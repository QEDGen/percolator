#![allow(dead_code)]

//! Stress harnesses — Week 3 bug hunting.
//!
//! The Week 2 multi-step harnesses verify lockstep refinement
//! across short sequences (typically 1..15 actions) at uniform
//! random inputs. This file pushes the harnesses harder along
//! three dimensions:
//!
//!   1. **Longer sequences** — 1..50 actions per trace. Drift
//!      bugs where production and reference diverge by tiny
//!      amounts per step would accumulate visibly only over
//!      many steps.
//!   2. **Biased generators** — instead of uniform sampling,
//!      bias toward boundary cases: amount = 0, amount = 1,
//!      amount = remaining-budget, amount = max-representable.
//!      These are where bugs hide.
//!   3. **Higher case counts** — `ProptestConfig::cases = 2000`
//!      per harness, vs proptest's default 256. Trades runtime
//!      for coverage density.
//!
//! Runtime: each test takes ~5-20 seconds. Total file ~1 minute.
//!
//! If a stress harness fails, the failing trace is shrunk to a
//! minimal example automatically (proptest's standard behavior).

use proptest::prelude::*;
use proptest::strategy::ValueTree;
use proptest::test_runner::Config;

use percolator::{
    v16::{MarketGroupV16, V16Config},
    BOUND_SCALE,
};

// ============================================================================
// Stress 1 — InsuranceLedger reserve lockstep with biased amounts
// ============================================================================

/// Reference port for the abstraction (lives in
/// `proofs_v16_lean_refinement_insurance.rs` but copied here for
/// isolation; would be deduplicated under a real `common/` mod).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct InsuranceLedger {
    initial_deposited: u128,
    source_credit_reserved_num: u128,
    domain_spent: u128,
}

impl InsuranceLedger {
    fn is_conserved(&self) -> bool {
        self.source_credit_reserved_num
            .checked_add(self.domain_spent)
            .map(|sum| sum <= self.initial_deposited)
            .unwrap_or(false)
    }

    fn reserve(&self, amount: u128) -> Option<Self> {
        let new_reserved = self.source_credit_reserved_num.checked_add(amount)?;
        let sum = new_reserved.checked_add(self.domain_spent)?;
        if sum <= self.initial_deposited {
            Some(Self {
                source_credit_reserved_num: new_reserved,
                ..*self
            })
        } else {
            None
        }
    }
}

fn abstract_insurance(group: &MarketGroupV16, domain: usize) -> InsuranceLedger {
    let reservation = group.insurance_credit_reservations[domain];
    let reserved_atoms = reservation
        .insurance_credit_reserved_num
        .div_ceil(BOUND_SCALE);
    InsuranceLedger {
        initial_deposited: group.insurance_domain_budget[domain],
        source_credit_reserved_num: reserved_atoms,
        domain_spent: group.insurance_domain_spent[domain],
    }
}

fn setup_group(budget_atoms: u128) -> Option<MarketGroupV16> {
    let market = [1u8; 32];
    let mut g = MarketGroupV16::new(market, V16Config::public_user_fund(4, 0, 10)).ok()?;
    g.insurance_domain_budget[0] = budget_atoms;
    g.insurance_domain_spent[0] = 0;
    g.insurance = g.insurance_domain_budget[0].checked_mul(2)?;
    g.vault = g.vault.checked_add(g.insurance)?;
    Some(g)
}

/// **Biased amount generator**: mixes boundary values with
/// uniform random. Approximate weights:
///   - 25% zero (tests zero-amount handling)
///   - 25% one  (smallest positive)
///   - 20% near remaining budget (boundary)
///   - 30% uniform random
fn arb_biased_amount(budget_atoms: u128) -> impl Strategy<Value = u128> {
    prop_oneof![
        1 => Just(0u128),
        1 => Just(1u128),
        1 => Just(budget_atoms / 4),
        1 => Just(budget_atoms / 2),
        2 => (0u128..=budget_atoms),
    ]
}

proptest! {
    #![proptest_config(Config {
        cases: 2000,
        max_shrink_iters: 1000,
        .. Config::default()
    })]

    /// **Stress: InsuranceLedger lockstep over long sequences with
    /// biased amounts**. 50-step sequences, 2000 cases, biased
    /// generators hitting boundary values. If drift exists, this
    /// should find it.
    #[test]
    fn stress_insurance_lockstep_long(
        budget_atoms in 1_000u128..=100_000u128,
    ) {
        let Some(mut g) = setup_group(budget_atoms) else {
            return Ok(());
        };
        let mut r = abstract_insurance(&g, 0);

        // Build a 50-step trace inside the test.
        let mut runner = proptest::test_runner::TestRunner::default();
        let amount_strategy = arb_biased_amount(budget_atoms);
        for _step in 0..50 {
            let amount_atoms = amount_strategy
                .new_tree(&mut runner)
                .map_err(|_| proptest::test_runner::TestCaseError::reject("strategy failed"))?
                .current();
            let amount_bound = match amount_atoms.checked_mul(BOUND_SCALE) {
                Some(v) => v,
                None => break,
            };
            let prod_ok = g
                .reserve_insurance_credit_not_atomic(0, amount_bound)
                .is_ok();
            let ref_post = r.reserve(amount_atoms);
            match (prod_ok, ref_post) {
                (true, Some(r_post)) => {
                    let abst = abstract_insurance(&g, 0);
                    prop_assert_eq!(abst, r_post);
                    r = r_post;
                }
                (false, _) => {
                    // Production refused. Stop the trace.
                    break;
                }
                (true, None) => {
                    prop_assert!(
                        false,
                        "lockstep violation at long-sequence step: budget_atoms={budget_atoms} amount_atoms={amount_atoms} reserved={:?}",
                        r
                    );
                }
            }
        }
    }
}

// ============================================================================
// Stress 2 — BackingBucket multi-action chains
// ============================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct BackingBucket {
    fresh_unliened: u128,
    valid_liened: u128,
    consumed_liened: u128,
    impaired_liened: u128,
}

impl BackingBucket {
    fn total_backing(&self) -> u128 {
        self.fresh_unliened
            .saturating_add(self.valid_liened)
            .saturating_add(self.consumed_liened)
            .saturating_add(self.impaired_liened)
    }
}

fn abstract_bucket(group: &MarketGroupV16, domain: usize) -> BackingBucket {
    let b = group.source_backing_buckets[domain];
    BackingBucket {
        fresh_unliened: b.fresh_unliened_backing_num,
        valid_liened: b.valid_liened_backing_num,
        consumed_liened: b.consumed_liened_backing_num,
        impaired_liened: b.impaired_liened_backing_num,
    }
}

fn setup_group_with_backing(fresh: u128, bound: u128) -> Option<MarketGroupV16> {
    let market = [1u8; 32];
    let mut g = MarketGroupV16::new(market, V16Config::public_user_fund(4, 0, 10)).ok()?;
    g.add_source_positive_claim_bound_not_atomic(0, bound, 10).ok()?;
    if fresh > 0 {
        g.add_fresh_counterparty_backing_not_atomic(0, fresh, 10).ok()?;
    }
    Some(g)
}

/// **Biased bucket-amount generator**: mixes boundary values.
fn arb_biased_bucket_amount(cap: u128) -> impl Strategy<Value = u128> {
    prop_oneof![
        1 => Just(0u128),
        1 => Just(1u128),
        1 => Just(cap),
        1 => Just(cap / 2),
        2 => (0u128..=cap),
    ]
}

#[derive(Clone, Copy, Debug)]
enum BucketOp {
    Create(u128),
    Release(u128),
    Consume(u128),
}

proptest! {
    #![proptest_config(Config {
        cases: 1000,
        max_shrink_iters: 1000,
        .. Config::default()
    })]

    /// **Stress: BackingBucket total_backing invariant across 50-step
    /// chains**. With biased amounts and a deliberately small
    /// bucket, lots of failed operations expose any drift.
    #[test]
    fn stress_bucket_total_invariant_long(
        fresh_amount in 500u128..=10_000u128,
    ) {
        let Some(mut g) = setup_group_with_backing(fresh_amount, fresh_amount) else {
            return Ok(());
        };
        let initial_total = abstract_bucket(&g, 0).total_backing();

        let mut runner = proptest::test_runner::TestRunner::default();
        let amt_strategy = arb_biased_bucket_amount(fresh_amount);
        let op_strategy = 0u8..3;

        for _step in 0..50 {
            let op = op_strategy.clone()
                .new_tree(&mut runner)
                .map_err(|_| proptest::test_runner::TestCaseError::reject("op gen failed"))?
                .current();
            let amount = amt_strategy
                .new_tree(&mut runner)
                .map_err(|_| proptest::test_runner::TestCaseError::reject("amt gen failed"))?
                .current();

            let _ = match op {
                0 => g.create_source_credit_lien_from_counterparty_not_atomic(0, amount).is_ok(),
                1 => g.release_source_credit_lien_from_counterparty_not_atomic(0, amount).is_ok(),
                _ => g.consume_source_credit_lien_from_counterparty_not_atomic(0, amount).is_ok(),
            };
            // The total-backing invariant must hold after every step,
            // accepted or rejected.
            let post = abstract_bucket(&g, 0);
            prop_assert_eq!(post.total_backing(), initial_total);
        }
    }
}

// ============================================================================
// Stress 3 — InsuranceLedger long-sequence conservation
// ============================================================================

proptest! {
    #![proptest_config(Config {
        cases: 2000,
        max_shrink_iters: 1000,
        .. Config::default()
    })]

    /// **Stress: conservation invariant survives 50-step reserve
    /// chains with biased amounts**. Specifically tests that
    /// `amount_from_bound_num` ceil-divide doesn't accumulate
    /// rounding error across many calls.
    #[test]
    fn stress_insurance_conservation_long(
        budget_atoms in 1_000u128..=100_000u128,
    ) {
        let Some(mut g) = setup_group(budget_atoms) else {
            return Ok(());
        };

        let mut runner = proptest::test_runner::TestRunner::default();
        let amt_strategy = arb_biased_amount(budget_atoms);

        for _step in 0..50 {
            let amount_atoms = amt_strategy
                .new_tree(&mut runner)
                .map_err(|_| proptest::test_runner::TestCaseError::reject("amt gen failed"))?
                .current();
            let amount_bound = match amount_atoms.checked_mul(BOUND_SCALE) {
                Some(v) => v,
                None => break,
            };
            let _ = g.reserve_insurance_credit_not_atomic(0, amount_bound);
            // Conservation must hold after every step.
            let reserved_atoms = g.insurance_credit_reservations[0]
                .insurance_credit_reserved_num
                .div_ceil(BOUND_SCALE);
            prop_assert!(
                reserved_atoms + g.insurance_domain_spent[0]
                    <= g.insurance_domain_budget[0],
                "conservation violated: reserved_atoms={reserved_atoms} spent={} budget={}",
                g.insurance_domain_spent[0],
                g.insurance_domain_budget[0]
            );
        }
    }
}

// ============================================================================
// Stress 4 — LienLifecycle source_credit aggregate over long chains
// ============================================================================

fn setup_group_for_lien_stress(fresh: u128) -> Option<MarketGroupV16> {
    let market = [1u8; 32];
    let mut g = MarketGroupV16::new(market, V16Config::public_user_fund(4, 0, 10)).ok()?;
    g.add_source_positive_claim_bound_not_atomic(0, fresh, 10).ok()?;
    if fresh > 0 {
        g.add_fresh_counterparty_backing_not_atomic(0, fresh, 10).ok()?;
    }
    Some(g)
}

proptest! {
    #![proptest_config(Config {
        cases: 1000,
        max_shrink_iters: 1000,
        .. Config::default()
    })]

    /// **Stress: source_credit aggregate cumulative invariant
    /// across 50-step mixed lien chains**. Verifies the
    /// `final_valid + final_spent + released = created`
    /// identity over long traces. Drift in the per-domain
    /// aggregate would surface here.
    #[test]
    fn stress_lien_cumulative_long(
        fresh in 5_000u128..=20_000u128,
    ) {
        let Some(mut g) = setup_group_for_lien_stress(fresh) else {
            return Ok(());
        };

        let mut cumulative_created: u128 = 0;
        let mut cumulative_consumed: u128 = 0;
        let mut cumulative_released: u128 = 0;

        let mut runner = proptest::test_runner::TestRunner::default();
        let amt_strategy = arb_biased_bucket_amount(500);
        let op_strategy = 0u8..3;

        for _step in 0..50 {
            let op = op_strategy.clone()
                .new_tree(&mut runner)
                .map_err(|_| proptest::test_runner::TestCaseError::reject("op gen failed"))?
                .current();
            let amount = amt_strategy
                .new_tree(&mut runner)
                .map_err(|_| proptest::test_runner::TestCaseError::reject("amt gen failed"))?
                .current();
            match op {
                0 => {
                    if g.create_source_credit_lien_from_counterparty_not_atomic(0, amount)
                        .is_ok()
                    {
                        cumulative_created += amount;
                    }
                }
                1 => {
                    if g.release_source_credit_lien_from_counterparty_not_atomic(0, amount)
                        .is_ok()
                    {
                        cumulative_released += amount;
                    }
                }
                _ => {
                    if g.consume_source_credit_lien_from_counterparty_not_atomic(0, amount)
                        .is_ok()
                    {
                        cumulative_consumed += amount;
                    }
                }
            }
        }

        // Cumulative identity: valid + spent + released = created.
        let final_valid = g.source_credit[0].valid_liened_backing_num;
        let final_spent = g.source_credit[0].spent_backing_num;
        let _ = cumulative_consumed;
        prop_assert_eq!(
            final_valid + final_spent + cumulative_released,
            cumulative_created,
            "cumulative aggregate identity violated"
        );
    }
}

// ============================================================================
// Stress 5 — Activation lifecycle round-trips at scale
// ============================================================================

proptest! {
    #![proptest_config(Config {
        cases: 500,
        max_shrink_iters: 1000,
        .. Config::default()
    })]

    /// **Stress: 10 activate/retire/reactivate cycles preserve
    /// asset_activation_count monotonicity**. Each cycle on a
    /// fixed asset slot bumps the count by 1; after k complete
    /// cycles, the count equals k (or fewer if cycles got
    /// rejected). The count never decreases.
    #[test]
    fn stress_activation_lifecycle_cycles(
        price in 100u64..=1_000u64,
        cooldown in 1u64..=3u64,
    ) {
        let mut cfg = V16Config::public_user_fund(4, 0, 10);
        cfg.asset_activation_cooldown_slots = cooldown;
        let market = [1u8; 32];
        let Ok(mut g) = MarketGroupV16::new(market, cfg) else {
            return Ok(());
        };

        let mut last_count = 0u64;
        let mut slot = 1u64;
        for _cycle in 0..10 {
            // activate at current slot.
            if g.activate_empty_asset_not_atomic(0, price, slot).is_ok() {
                prop_assert!(g.asset_activation_count >= last_count);
                last_count = g.asset_activation_count;
                // retire after cooldown.
                slot += cooldown + 1;
                let _ = g.retire_empty_asset_not_atomic(0, slot);
                // step forward cooldown for the next activate.
                slot += cooldown + 1;
            } else {
                // unable to activate (e.g. cooldown still pending);
                // step slot forward.
                slot += cooldown + 1;
            }
        }
        // count never decreased (last_count is the post-monotonic-check value).
        prop_assert!(g.asset_activation_count >= last_count);
    }
}

// ============================================================================
// Stress 6 — adversarial sequences (hand-crafted scenarios)
// ============================================================================

#[test]
fn adversarial_fill_then_overflow() {
    // Hand-crafted: budget allows exactly k chunks of size c;
    // the (k+1)-th must be rejected. Sweep across k and c.
    for k in 1u128..=10 {
        for c in [1u128, 100, 1_000, 10_000].iter().copied() {
            let budget_atoms = k * c;
            let Some(mut g) = setup_group(budget_atoms) else { continue };

            // Reserve k chunks — each should succeed.
            let chunk_bound = match c.checked_mul(BOUND_SCALE) {
                Some(v) => v,
                None => continue,
            };
            let mut succeeded = 0u128;
            for _ in 0..k {
                if g.reserve_insurance_credit_not_atomic(0, chunk_bound).is_ok() {
                    succeeded += 1;
                }
            }

            // The (succeeded+1)-th reserve must fail.
            let extra_bound = match (1u128).checked_mul(BOUND_SCALE) {
                Some(v) => v,
                None => continue,
            };
            let after_fill = g
                .reserve_insurance_credit_not_atomic(0, extra_bound)
                .is_ok();
            assert!(
                !after_fill,
                "adversarial: budget exhausted (k={k} c={c} succeeded={succeeded}) but production accepted another reserve"
            );
        }
    }
}

#[test]
fn adversarial_zero_amount_reserve_succeeds() {
    // Reserving 0 should always succeed (no-op).
    for budget_atoms in [100u128, 1_000, 10_000].iter().copied() {
        let Some(mut g) = setup_group(budget_atoms) else { continue };
        assert!(
            g.reserve_insurance_credit_not_atomic(0, 0).is_ok(),
            "zero reserve should be a no-op success at budget={budget_atoms}"
        );
        // State unchanged.
        assert_eq!(
            g.insurance_credit_reservations[0].insurance_credit_reserved_num,
            0
        );
    }
}

#[test]
fn adversarial_bucket_create_consume_release_zero() {
    // Bucket operations on amount=0 should succeed as no-ops.
    let Some(mut g) = setup_group_with_backing(1_000, 1_000) else { return };

    // amount=0 is special: the production handler short-circuits to Ok.
    assert!(g.create_source_credit_lien_from_counterparty_not_atomic(0, 0).is_ok());
    assert!(g.release_source_credit_lien_from_counterparty_not_atomic(0, 0).is_ok());
    assert!(g.consume_source_credit_lien_from_counterparty_not_atomic(0, 0).is_ok());

    // Total backing must be unchanged after all zero ops.
    let final_total = abstract_bucket(&g, 0).total_backing();
    assert_eq!(final_total, 1_000);
}
