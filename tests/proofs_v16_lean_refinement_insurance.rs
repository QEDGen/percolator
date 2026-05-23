//! State-machine refinement: `Percolator/InsuranceLedger.lean` ↔ Rust.
//!
//! Tier 2 of the verification stack. The pattern mirrors
//! `proofs_v16_lean_refinement.rs` but at the state-machine level:
//!
//!   - The Lean spec (`InsuranceLedger` + `reserve` / `release` /
//!     `consume` + `applyWrite`) defines the abstract behavior with
//!     a carried conservation invariant.
//!   - The Rust *reference port* below is a line-for-line port of
//!     the Lean definitions. It is **owned by the verification**
//!     (not used by production); it exists so the Lean spec is
//!     runnable in Rust.
//!   - The proptests verify the Lean theorems hold at runtime for
//!     the reference port. They do not yet bridge to v16.rs
//!     production state — that is a follow-up step that requires a
//!     `MarketGroupV16` fixture and an abstraction function
//!     projecting the production `InsuranceCreditReservationV16` to
//!     the abstract `InsuranceLedger`.
//!
//! The theorems verified at runtime:
//!
//!   - `consume_atomic_decrement_and_spend`: a successful consume
//!     decrements `sourceCreditReservedNum` and increments
//!     `domainSpent` by the same amount.
//!   - `applyWrite_preserves_initialDeposited`: no writer mutates
//!     the deposit anchor.
//!   - `conservation`: every reachable state satisfies the
//!     `reserved + staged + protocolStaged + spent ≤ deposited`
//!     invariant. Carried as a struct field on the Lean side; a
//!     runtime check on the Rust side.
//!
//! See `formal_verification/Percolator/InsuranceLedger.lean` for
//! the Lean statements and
//! `formal_verification/Percolator/SingleWriterInsurance.lean` for
//! the closed-sum `applyWrite` typed entry point.

use proptest::prelude::*;

// ============================================================================
// Reference port — Rust copy of `Percolator/InsuranceLedger.lean`
// ============================================================================

/// Insurance ledger, single-domain projection. Mirrors the Lean
/// `InsuranceLedger` structure.
///
/// The Lean structure carries the conservation invariant as a proof
/// field; in Rust we represent it as a runtime check (see
/// `is_conserved`). Construction is via `new` and the three
/// transitions; the conservation property is preserved by
/// construction (verified by the proptests below).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct InsuranceLedger {
    initial_deposited: u128,
    source_credit_reserved_num: u128,
    domain_spent: u128,
    staged_domain_debit: u128,
    global_protocol_staged: u128,
}

impl InsuranceLedger {
    /// The empty ledger — Lean's `InsuranceLedger.empty`.
    const EMPTY: Self = Self {
        initial_deposited: 0,
        source_credit_reserved_num: 0,
        domain_spent: 0,
        staged_domain_debit: 0,
        global_protocol_staged: 0,
    };

    /// Initialize a ledger with `deposit` units of capital. Mirrors
    /// `Percolator/InsuranceLedger.lean::InsuranceLedger.initial`.
    fn initial(deposit: u128) -> Self {
        Self {
            initial_deposited: deposit,
            ..Self::EMPTY
        }
    }

    /// The conservation invariant. Carried as a struct field
    /// (`conservation : ... ≤ initialDeposited`) in Lean; verified
    /// at construction time here.
    fn is_conserved(&self) -> bool {
        self.source_credit_reserved_num
            .checked_add(self.staged_domain_debit)
            .and_then(|x| x.checked_add(self.global_protocol_staged))
            .and_then(|x| x.checked_add(self.domain_spent))
            .map(|sum| sum <= self.initial_deposited)
            .unwrap_or(false)
    }

    /// **Reserve**: add `amount` to source-credit reservation.
    /// Returns `None` if the post-state would violate conservation.
    ///
    /// Mirrors Lean `InsuranceLedger.reserve`.
    fn reserve(&self, amount: u128) -> Option<Self> {
        let new_reserved = self.source_credit_reserved_num.checked_add(amount)?;
        let sum = new_reserved
            .checked_add(self.staged_domain_debit)?
            .checked_add(self.global_protocol_staged)?
            .checked_add(self.domain_spent)?;
        if sum <= self.initial_deposited {
            Some(Self {
                source_credit_reserved_num: new_reserved,
                ..*self
            })
        } else {
            None
        }
    }

    /// **Release**: remove `amount` from source-credit reservation
    /// without spending. Returns `None` if `amount` exceeds the
    /// current reservation.
    ///
    /// Mirrors Lean `InsuranceLedger.release`.
    fn release(&self, amount: u128) -> Option<Self> {
        if self.source_credit_reserved_num < amount {
            None
        } else {
            Some(Self {
                source_credit_reserved_num: self.source_credit_reserved_num - amount,
                ..*self
            })
        }
    }

    /// **Consume**: spend `amount`. Decrements
    /// `source_credit_reserved_num` and increments `domain_spent`
    /// atomically.
    ///
    /// Mirrors Lean `InsuranceLedger.consume`.
    fn consume(&self, amount: u128) -> Option<Self> {
        if self.source_credit_reserved_num < amount {
            return None;
        }
        Some(Self {
            source_credit_reserved_num: self.source_credit_reserved_num - amount,
            domain_spent: self.domain_spent.checked_add(amount)?,
            ..*self
        })
    }
}

/// Closed sum of canonical writers. Mirrors Lean
/// `SingleWriterInsurance.lean::InsuranceWrite`. By exhaustiveness,
/// there is no fourth constructor — every `InsuranceWrite` value
/// is provably one of these three.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum InsuranceWrite {
    Reserve(u128),
    Release(u128),
    Consume(u128),
}

impl InsuranceLedger {
    /// The single typed entry point. Routes by `InsuranceWrite`
    /// constructor to the corresponding named transition.
    ///
    /// Mirrors Lean `InsuranceLedger.applyWrite`.
    fn apply_write(&self, w: InsuranceWrite) -> Option<Self> {
        match w {
            InsuranceWrite::Reserve(a) => self.reserve(a),
            InsuranceWrite::Release(a) => self.release(a),
            InsuranceWrite::Consume(a) => self.consume(a),
        }
    }
}

// ============================================================================
// Generators
// ============================================================================

/// Generate a well-conserved random ledger. We start from a deposit
/// and apply a random reservation; this guarantees the post-state
/// satisfies the conservation invariant. Other fields stay zero
/// for simplicity in the first cut.
fn arb_ledger() -> impl Strategy<Value = InsuranceLedger> {
    (1u128..=1_000_000u128, 0u128..=1_000_000u128).prop_filter_map(
        "reservation must not exceed deposit",
        |(deposit, reserved)| {
            if reserved <= deposit {
                Some(InsuranceLedger {
                    initial_deposited: deposit,
                    source_credit_reserved_num: reserved,
                    domain_spent: 0,
                    staged_domain_debit: 0,
                    global_protocol_staged: 0,
                })
            } else {
                None
            }
        },
    )
}

/// Generate a random `InsuranceWrite` action.
fn arb_write() -> impl Strategy<Value = InsuranceWrite> {
    prop_oneof![
        (1u128..=1_000_000u128).prop_map(InsuranceWrite::Reserve),
        (0u128..=1_000_000u128).prop_map(InsuranceWrite::Release),
        (0u128..=1_000_000u128).prop_map(InsuranceWrite::Consume),
    ]
}

// ============================================================================
// Proptests — runtime verification of the Lean theorems
// ============================================================================

proptest! {
    /// **Lean `InsuranceLedger.empty_isReconciledZero` analog**: the
    /// empty ledger satisfies conservation. Sanity check on the
    /// constructor — not a proptest in the random-input sense, but
    /// included for completeness.
    #[test]
    fn empty_is_conserved(_x: u32) {
        prop_assert!(InsuranceLedger::EMPTY.is_conserved());
    }

    /// **Lean `InsuranceLedger.initial` is conserved**: a freshly-
    /// constructed ledger is always conserved.
    #[test]
    fn initial_is_conserved(deposit in 0u128..=u128::MAX) {
        prop_assert!(InsuranceLedger::initial(deposit).is_conserved());
    }

    /// **Conservation under reserve** (Lean
    /// `reserve_preserves_conservation`): every successful reserve
    /// produces a conserved post-state. The Lean theorem is by the
    /// `conservation` proof field; here it's a runtime check.
    #[test]
    fn reserve_preserves_conservation(l in arb_ledger(), amount in 0u128..=2_000_000u128) {
        if let Some(l_post) = l.reserve(amount) {
            prop_assert!(l_post.is_conserved());
        }
    }

    /// **Conservation under release** (Lean
    /// `release_preserves_conservation`). -/
    #[test]
    fn release_preserves_conservation(l in arb_ledger(), amount in 0u128..=2_000_000u128) {
        if let Some(l_post) = l.release(amount) {
            prop_assert!(l_post.is_conserved());
        }
    }

    /// **Conservation under consume** (Lean
    /// `consume_preserves_conservation`).
    #[test]
    fn consume_preserves_conservation(l in arb_ledger(), amount in 0u128..=2_000_000u128) {
        if let Some(l_post) = l.consume(amount) {
            prop_assert!(l_post.is_conserved());
        }
    }

    /// **Atomic decrement-and-spend** (Lean
    /// `consume_atomic_decrement_and_spend`): a successful consume
    /// decrements `source_credit_reserved_num` and increments
    /// `domain_spent` by exactly `amount` in the same step. The
    /// same atom cannot be both reserved and spent.
    #[test]
    fn consume_atomic_decrement_and_spend(l in arb_ledger(), amount in 0u128..=2_000_000u128) {
        if let Some(l_post) = l.consume(amount) {
            prop_assert_eq!(
                l_post.source_credit_reserved_num + amount,
                l.source_credit_reserved_num
            );
            prop_assert_eq!(l_post.domain_spent, l.domain_spent + amount);
        }
    }

    /// **Consume preserves deposit and staged** (Lean
    /// `consume_preserves_deposit_and_staged`): the consume
    /// transition reclassifies reserved → spent against the same
    /// `initial_deposited`; nothing else moves.
    #[test]
    fn consume_preserves_deposit_and_staged(l in arb_ledger(), amount in 0u128..=2_000_000u128) {
        if let Some(l_post) = l.consume(amount) {
            prop_assert_eq!(l_post.initial_deposited, l.initial_deposited);
            prop_assert_eq!(l_post.staged_domain_debit, l.staged_domain_debit);
            prop_assert_eq!(l_post.global_protocol_staged, l.global_protocol_staged);
        }
    }

    /// **Release preserves domain_spent** (Lean
    /// `release_preserves_domainSpent`): release returns reserved
    /// capacity to available without ever moving spend.
    #[test]
    fn release_preserves_domain_spent(l in arb_ledger(), amount in 0u128..=2_000_000u128) {
        if let Some(l_post) = l.release(amount) {
            prop_assert_eq!(l_post.domain_spent, l.domain_spent);
        }
    }

    /// **apply_write_preserves_initialDeposited** (Lean
    /// `applyWrite_preserves_initialDeposited`): no constructor of
    /// `InsuranceWrite` mutates the deposit anchor. Closed-sum
    /// exhaustiveness on the Lean side; per-constructor checks here.
    #[test]
    fn apply_write_preserves_initial_deposited(
        l in arb_ledger(),
        w in arb_write(),
    ) {
        if let Some(l_post) = l.apply_write(w) {
            prop_assert_eq!(l_post.initial_deposited, l.initial_deposited);
        }
    }

    /// **apply_write_preserves_globalProtocolStaged** (Lean
    /// `applyWrite_preserves_globalProtocolStaged`).
    #[test]
    fn apply_write_preserves_global_protocol_staged(
        l in arb_ledger(),
        w in arb_write(),
    ) {
        if let Some(l_post) = l.apply_write(w) {
            prop_assert_eq!(l_post.global_protocol_staged, l.global_protocol_staged);
        }
    }

    /// **apply_write routing equivalence** (Lean
    /// `applyWrite_Reserve` / `_Release` / `_Consume`):
    /// `apply_write(Reserve(a))` is definitionally `reserve(a)`,
    /// and likewise for the other two constructors.
    #[test]
    fn apply_write_routing_equivalence(
        l in arb_ledger(),
        a in 0u128..=1_000_000u128,
    ) {
        prop_assert_eq!(l.apply_write(InsuranceWrite::Reserve(a)), l.reserve(a));
        prop_assert_eq!(l.apply_write(InsuranceWrite::Release(a)), l.release(a));
        prop_assert_eq!(l.apply_write(InsuranceWrite::Consume(a)), l.consume(a));
    }

    /// **Sequences of writes preserve conservation**: a chain of
    /// arbitrary `InsuranceWrite` actions, each one applied if it
    /// succeeds, never breaks conservation. This is the
    /// integration-level claim — composition of the Lean
    /// transitions stays sound.
    #[test]
    fn sequence_of_writes_preserves_conservation(
        l0 in arb_ledger(),
        actions in prop::collection::vec(arb_write(), 0..20),
    ) {
        let mut l = l0;
        prop_assert!(l.is_conserved());
        for w in actions {
            if let Some(l_next) = l.apply_write(w) {
                l = l_next;
                prop_assert!(l.is_conserved());
            }
        }
    }
}

// ============================================================================
// Tier 2.5 — Production connector
//
// The reference port above is the Lean spec made executable. This section
// connects it to the actual `v16.rs::MarketGroupV16::reserve_insurance_credit_not_atomic`
// production handler and proptests that the production transition behaves
// like the reference port under an abstraction function.
//
// The setup mirrors `tests/v16_spec_tests.rs::v16_reserve_insurance_credit_*`
// patterns. We exercise small amounts in BOUND-units so the
// `amount_from_bound_num` conversion is exact (no rounding).
// ============================================================================

use percolator::{
    BOUND_SCALE,
    v16::{MarketGroupV16, V16Config},
};

/// Abstract a single-domain projection of the production engine to the
/// reference port. Everything is expressed in **atoms** in the
/// reference — the production's `insurance_credit_reserved_num` is in
/// BOUND-units (sub-atomic), but the *budget* constraint is enforced
/// against `amount_from_bound_num(reserved)` (the atom-rounded value).
/// To match this exactly, the abstraction:
///
///   - puts the budget in atoms (its native unit on production);
///   - converts the BOUND-unit reservation to atoms via the same
///     ceil-divide used by the production check;
///   - keeps spent in atoms.
fn abstract_insurance(group: &MarketGroupV16, domain: usize) -> InsuranceLedger {
    let reservation = group.insurance_credit_reservations[domain];
    let reserved_atoms = reservation
        .insurance_credit_reserved_num
        .div_ceil(BOUND_SCALE);
    InsuranceLedger {
        initial_deposited: group.insurance_domain_budget[domain],
        source_credit_reserved_num: reserved_atoms,
        domain_spent: group.insurance_domain_spent[domain],
        staged_domain_debit: 0,
        global_protocol_staged: 0,
    }
}

/// Build a `MarketGroupV16` with the insurance pool, domain budget, and
/// initial reservation set so the conservation invariant holds.
///
/// All input quantities are in **atoms**. The production
/// `insurance_credit_reserved_num` is stored in BOUND-units; the helper
/// converts `initial_reserved_atoms` to BOUND-units (× BOUND_SCALE) when
/// writing the production field. This keeps the conversion exact (no
/// ceil-divide rounding).
fn setup_group_for_insurance_reserve(
    budget_atoms: u128,
    initial_reserved_atoms: u128,
) -> Option<MarketGroupV16> {
    let market = [1u8; 32];
    let mut g = MarketGroupV16::new(market, V16Config::public_user_fund(4, 0, 10)).ok()?;
    g.insurance_domain_budget[0] = budget_atoms;
    g.insurance_domain_spent[0] = 0;
    g.insurance = g.insurance_domain_budget[0].checked_mul(2)?;
    g.vault = g.vault.checked_add(g.insurance)?;
    g.insurance_credit_reservations[0].insurance_credit_reserved_num =
        initial_reserved_atoms.checked_mul(BOUND_SCALE)?;
    Some(g)
}

proptest! {
    /// **Production refinement: reserve_insurance_credit_not_atomic matches
    /// the Lean reference**. All quantities expressed in atoms (the
    /// reference port's unit system); production's BOUND-unit field is
    /// scaled by BOUND_SCALE under the hood.
    #[test]
    fn production_reserve_matches_reference(
        budget_atoms in 100u128..=10_000u128,
        initial_reserved_atoms in 0u128..=5_000u128,
        amount_atoms in 0u128..=5_000u128,
    ) {
        prop_assume!(initial_reserved_atoms <= budget_atoms);

        let Some(mut g) = setup_group_for_insurance_reserve(budget_atoms, initial_reserved_atoms)
        else {
            return Ok(());
        };

        let ref_pre = abstract_insurance(&g, 0);
        prop_assert!(ref_pre.is_conserved());
        let ref_post = ref_pre.reserve(amount_atoms);

        // Production takes amount in BOUND-units.
        let amount_bound = match amount_atoms.checked_mul(BOUND_SCALE) {
            Some(v) => v,
            None => return Ok(()),
        };
        let prod_result = g.reserve_insurance_credit_not_atomic(0, amount_bound);

        match (prod_result, ref_post) {
            (Ok(()), Some(ref_post)) => {
                let prod_post = abstract_insurance(&g, 0);
                prop_assert_eq!(prod_post, ref_post);
            }
            (Err(_), None) => {}
            (Ok(()), None) => {
                prop_assert!(
                    false,
                    "production accepted reserve but reference rejected: budget={budget_atoms} reserved={initial_reserved_atoms} amount={amount_atoms}"
                );
            }
            (Err(_), Some(_)) => {
                // Production has stricter checks (e.g. global insurance
                // cap, encumbrance proofs); refusing what reference
                // accepts is OK in the refinement direction.
            }
        }
    }

    /// **Production-side conservation invariant**: a successful
    /// `reserve_insurance_credit_not_atomic` leaves the per-domain
    /// `reserved + spent ≤ budget` (in atoms) invariant intact.
    #[test]
    fn production_reserve_preserves_conservation(
        budget_atoms in 100u128..=10_000u128,
        initial_reserved_atoms in 0u128..=5_000u128,
        amount_atoms in 0u128..=5_000u128,
    ) {
        prop_assume!(initial_reserved_atoms <= budget_atoms);

        let Some(mut g) = setup_group_for_insurance_reserve(budget_atoms, initial_reserved_atoms)
        else {
            return Ok(());
        };
        let amount_bound = match amount_atoms.checked_mul(BOUND_SCALE) {
            Some(v) => v,
            None => return Ok(()),
        };

        if g.reserve_insurance_credit_not_atomic(0, amount_bound).is_ok() {
            let reserved_atoms = g.insurance_credit_reservations[0]
                .insurance_credit_reserved_num
                .div_ceil(BOUND_SCALE);
            let budget = g.insurance_domain_budget[0];
            prop_assert!(reserved_atoms + g.insurance_domain_spent[0] <= budget);
        }
    }

    /// **Production reserve increments BOUND-num by exactly amount**: the
    /// production field is in BOUND-units, so an `amount` of `N *
    /// BOUND_SCALE` increments `insurance_credit_reserved_num` by
    /// `N * BOUND_SCALE`.
    #[test]
    fn production_reserve_increments_by_amount(
        budget_atoms in 100u128..=10_000u128,
        initial_reserved_atoms in 0u128..=5_000u128,
        amount_atoms in 0u128..=5_000u128,
    ) {
        prop_assume!(initial_reserved_atoms <= budget_atoms);

        let Some(mut g) = setup_group_for_insurance_reserve(budget_atoms, initial_reserved_atoms)
        else {
            return Ok(());
        };
        let amount_bound = match amount_atoms.checked_mul(BOUND_SCALE) {
            Some(v) => v,
            None => return Ok(()),
        };

        let pre = g.insurance_credit_reservations[0].insurance_credit_reserved_num;
        if g.reserve_insurance_credit_not_atomic(0, amount_bound).is_ok() {
            let post = g.insurance_credit_reservations[0].insurance_credit_reserved_num;
            prop_assert_eq!(post, pre + amount_bound);
        }
    }
}

// ============================================================================
// Multi-step sequence bridges — Week 2 deepening
//
// The connector above proves single-step refinement: one production
// reserve call matches one reference-port reserve. This section
// extends the bridge to *sequences*: a chain of N reserve actions
// against the same domain must keep the production state in lock-
// step with the reference port after every step.
//
// Sequencing bugs that single-step tests miss include:
//   - Side effects between steps (e.g. refresh_source_credit_domain_after_mutation)
//     that alter cross-state in ways the abstraction doesn't capture.
//   - Order-dependent acceptance/rejection where production accepts
//     a step that violates a future invariant the reference would
//     catch.
//   - Drift over many steps where the abstraction and production
//     diverge by a tiny amount per step.
// ============================================================================

/// A scripted action for the multi-step harness.
#[derive(Clone, Copy, Debug)]
enum ProductionAction {
    /// Call `reserve_insurance_credit_not_atomic(0, amount_atoms * BOUND_SCALE)`.
    Reserve(u128),
}

fn arb_action() -> impl Strategy<Value = ProductionAction> {
    (0u128..=500u128).prop_map(ProductionAction::Reserve)
}

proptest! {
    /// **Multi-step refinement: production and reference stay in
    /// lockstep across N reserves**. After each successful step,
    /// the production state's abstraction equals the reference
    /// port's state. If at any step production accepts what the
    /// reference rejects (or post-states diverge), the test fails.
    #[test]
    fn multistep_reserve_lockstep(
        budget_atoms in 1_000u128..=50_000u128,
        actions in prop::collection::vec(arb_action(), 1..15),
    ) {
        let Some(mut g) = setup_group_for_insurance_reserve(budget_atoms, 0)
        else {
            return Ok(());
        };
        let mut r = abstract_insurance(&g, 0);
        prop_assert!(r.is_conserved());

        for action in actions {
            // Snapshot pre-step abstractions.
            let pre_abstract = abstract_insurance(&g, 0);
            prop_assert_eq!(pre_abstract, r);

            // Apply the action in lockstep.
            let amount_atoms = match action {
                ProductionAction::Reserve(a) => a,
            };
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
                    // Both accepted: post-state abstractions must match.
                    let post_abstract = abstract_insurance(&g, 0);
                    prop_assert_eq!(post_abstract, r_post);
                    r = r_post;
                }
                (false, _) => {
                    // Production refused — stop the trace (reference may
                    // or may not have accepted; production is stricter
                    // due to global cap / encumbrance checks).
                    break;
                }
                (true, None) => {
                    // Refinement violation: production accepted what
                    // reference rejected.
                    prop_assert!(
                        false,
                        "lockstep violation at step: production accepted but reference rejected"
                    );
                }
            }
        }
    }

    /// **Multi-step conservation invariant**: after any sequence of
    /// production reserves, the per-domain conservation invariant
    /// (reserved + spent ≤ budget) holds. The reference port carries
    /// this as a struct field; production maintains it as an
    /// engine-level invariant.
    #[test]
    fn multistep_reserve_preserves_conservation(
        budget_atoms in 1_000u128..=50_000u128,
        actions in prop::collection::vec(arb_action(), 1..20),
    ) {
        let Some(mut g) = setup_group_for_insurance_reserve(budget_atoms, 0)
        else {
            return Ok(());
        };
        let mut last_action_succeeded = true;

        for action in actions {
            let amount_atoms = match action {
                ProductionAction::Reserve(a) => a,
            };
            let amount_bound = match amount_atoms.checked_mul(BOUND_SCALE) {
                Some(v) => v,
                None => break,
            };
            last_action_succeeded = g
                .reserve_insurance_credit_not_atomic(0, amount_bound)
                .is_ok();
            // After any step (whether accepted or rejected), conservation
            // still holds on the production state.
            let reserved_atoms = g.insurance_credit_reservations[0]
                .insurance_credit_reserved_num
                .div_ceil(BOUND_SCALE);
            prop_assert!(
                reserved_atoms + g.insurance_domain_spent[0]
                    <= g.insurance_domain_budget[0]
            );
        }
        // Suppress unused-warning when traces succeed fully.
        let _ = last_action_succeeded;
    }

    /// **Sequence of N reserves up to budget then one over**: after
    /// reserving budget/k each time, k times, the (k+1)-th reserve
    /// should fail closed in both production and reference. This is
    /// an explicit boundary test of the sequencing bridge.
    #[test]
    fn sequence_exhausts_then_rejects(
        k in 2u128..=5u128,
        chunk_atoms in 100u128..=500u128,
    ) {
        let budget_atoms = k * chunk_atoms + chunk_atoms / 2; // not enough for k+1 chunks
        let Some(mut g) = setup_group_for_insurance_reserve(budget_atoms, 0)
        else {
            return Ok(());
        };
        let mut r = abstract_insurance(&g, 0);

        let amount_bound = match chunk_atoms.checked_mul(BOUND_SCALE) {
            Some(v) => v,
            None => return Ok(()),
        };

        // First k reserves should succeed in lockstep.
        for _ in 0..k {
            let prod_ok = g
                .reserve_insurance_credit_not_atomic(0, amount_bound)
                .is_ok();
            let ref_post = r.reserve(chunk_atoms);
            match (prod_ok, ref_post) {
                (true, Some(r_post)) => {
                    let abst = abstract_insurance(&g, 0);
                    prop_assert_eq!(abst, r_post);
                    r = r_post;
                }
                _ => {
                    // Production may reject earlier than reference due to
                    // stricter global checks. That's OK — break here.
                    return Ok(());
                }
            }
        }

        // (k+1)-th reserve: reference should reject (budget left <
        // chunk).
        let r_overflow = r.reserve(chunk_atoms);
        prop_assert!(r_overflow.is_none());

        // Production may accept (because of rounding via amount_from_bound_num
        // or because the BOUND-unit representation has some slack);
        // if it does, the abstraction must agree with the reference
        // (which rejected) — which would be a refinement violation.
        let prod_overflow_ok = g
            .reserve_insurance_credit_not_atomic(0, amount_bound)
            .is_ok();
        if prod_overflow_ok {
            // The reference rejects this; if production accepts, we
            // have a refinement violation.
            prop_assert!(
                false,
                "production accepted budget-overflow reserve that reference rejected: k={k} chunk_atoms={chunk_atoms} budget_atoms={budget_atoms}"
            );
        }
    }
}
