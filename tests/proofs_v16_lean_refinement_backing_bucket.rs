//! State-machine refinement: `Percolator/BackingBucket.lean` ↔ Rust.
//!
//! Tier 2 of the verification stack, second cluster bridge.
//!
//! Same pattern as the InsuranceLedger bridge:
//!
//!   - The Lean spec (`BackingBucket` + `openFresh` / `expire` /
//!     `markImpaired` / `lienAgainst` / `consumeLien` /
//!     `releaseLien` / `impairLien`) defines the bucket's
//!     per-partition behavior.
//!   - The Rust *reference port* below is a line-for-line port of
//!     the Lean definitions, owned by the verification.
//!   - Proptests verify the Lean theorems hold at runtime: every
//!     transition preserves `totalBacking` (the per-bucket
//!     conservation invariant), expire is status-only, etc.
//!
//! Theorems verified at runtime:
//!
//!   - `expire_preserves_available` (§14 #34): expire does not
//!     decrement `freshUnliened`.
//!   - `expire_preserves_amounts` (§14 #34/#35): expire is the
//!     identity on every backing partition; only status changes.
//!   - `available_after_lien_then_expire` (§14 #36): after a
//!     partial lien followed by expire, available backing is
//!     bounded by the pre-lien available.
//!   - `*_preserves_total_backing`: every transition preserves the
//!     four-partition sum.
//!
//! See `formal_verification/Percolator/BackingBucket.lean`.

#![allow(dead_code)] // reference port mirrors every Lean def; not all are exercised by proptests yet

use proptest::prelude::*;

// ============================================================================
// Reference port — Rust copy of `Percolator/BackingBucket.lean`
// ============================================================================

/// Backing-bucket lifecycle tag. Mirrors `Lifecycle.lean::BackingBucketStatus`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BucketStatus {
    Empty,
    Fresh,
    Expired,
    Impaired,
}

/// Backing bucket, single per-domain unit. Mirrors Lean
/// `BackingBucket`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct BackingBucket {
    market_id: u64,
    fresh_unliened: u128,
    valid_liened: u128,
    consumed_liened: u128,
    impaired_liened: u128,
    expiry_slot: u64,
    status: BucketStatus,
}

impl BackingBucket {
    /// Empty bucket for a given market. Lean `emptyForMarket`.
    fn empty_for_market(market_id: u64) -> Self {
        Self {
            market_id,
            fresh_unliened: 0,
            valid_liened: 0,
            consumed_liened: 0,
            impaired_liened: 0,
            expiry_slot: 0,
            status: BucketStatus::Empty,
        }
    }

    /// Total backing held in the bucket across all four partitions.
    /// Lean `totalBacking`.
    fn total_backing(&self) -> u128 {
        self.fresh_unliened
            .saturating_add(self.valid_liened)
            .saturating_add(self.consumed_liened)
            .saturating_add(self.impaired_liened)
    }

    /// Available (un-liened, un-consumed, un-impaired) backing.
    /// Lean `available`. -/
    fn available(&self) -> u128 {
        self.fresh_unliened
    }

    /// **Open**: Empty → Fresh, with `amount` freshly-deposited
    /// backing. Lean `openFresh`.
    fn open_fresh(&self, amount: u128, expiry_slot: u64) -> Option<Self> {
        if self.status != BucketStatus::Empty {
            return None;
        }
        Some(Self {
            fresh_unliened: amount,
            expiry_slot,
            status: BucketStatus::Fresh,
            ..*self
        })
    }

    /// **Expire**: Fresh → Expired. Status only; no amount field
    /// is touched. Lean `expire`.
    fn expire(&self) -> Option<Self> {
        if self.status != BucketStatus::Fresh {
            return None;
        }
        Some(Self {
            status: BucketStatus::Expired,
            ..*self
        })
    }

    /// **Mark impaired**: Fresh|Expired → Impaired. Status only.
    /// Lean `markImpaired`.
    fn mark_impaired(&self) -> Option<Self> {
        if self.status == BucketStatus::Empty {
            return None;
        }
        Some(Self {
            status: BucketStatus::Impaired,
            ..*self
        })
    }

    /// **Lien against**: move `amount` from fresh_unliened to
    /// valid_liened. Lean `lienAgainst`.
    fn lien_against(&self, amount: u128) -> Option<Self> {
        if self.fresh_unliened < amount {
            return None;
        }
        Some(Self {
            fresh_unliened: self.fresh_unliened - amount,
            valid_liened: self.valid_liened.checked_add(amount)?,
            ..*self
        })
    }

    /// **Consume a lien**: move `amount` from valid_liened to
    /// consumed_liened. The backing is gone (spent). Lean
    /// `consumeLien`.
    fn consume_lien(&self, amount: u128) -> Option<Self> {
        if self.valid_liened < amount {
            return None;
        }
        Some(Self {
            valid_liened: self.valid_liened - amount,
            consumed_liened: self.consumed_liened.checked_add(amount)?,
            ..*self
        })
    }

    /// **Release a lien**: move `amount` from valid_liened back to
    /// fresh_unliened. Lean `releaseLien`.
    fn release_lien(&self, amount: u128) -> Option<Self> {
        if self.valid_liened < amount {
            return None;
        }
        Some(Self {
            valid_liened: self.valid_liened - amount,
            fresh_unliened: self.fresh_unliened.checked_add(amount)?,
            ..*self
        })
    }

    /// **Impair a lien**: move `amount` from valid_liened to
    /// impaired_liened. Lean `impairLien`.
    fn impair_lien(&self, amount: u128) -> Option<Self> {
        if self.valid_liened < amount {
            return None;
        }
        Some(Self {
            valid_liened: self.valid_liened - amount,
            impaired_liened: self.impaired_liened.checked_add(amount)?,
            ..*self
        })
    }
}

// ============================================================================
// Generators
// ============================================================================

/// Generate a random bucket whose partition sum does not overflow
/// u128. Status is randomly one of the four.
fn arb_bucket() -> impl Strategy<Value = BackingBucket> {
    (
        any::<u64>(),
        0u128..=1_000_000u128,
        0u128..=1_000_000u128,
        0u128..=1_000_000u128,
        0u128..=1_000_000u128,
        any::<u64>(),
        0u8..4,
    )
        .prop_map(|(mid, f, v, c, i, exp, s)| BackingBucket {
            market_id: mid,
            fresh_unliened: f,
            valid_liened: v,
            consumed_liened: c,
            impaired_liened: i,
            expiry_slot: exp,
            status: match s {
                0 => BucketStatus::Empty,
                1 => BucketStatus::Fresh,
                2 => BucketStatus::Expired,
                _ => BucketStatus::Impaired,
            },
        })
}

/// Generate a Fresh bucket (so `expire` and `lien_against` can
/// fire). Useful for testing those transitions specifically.
fn arb_fresh_bucket() -> impl Strategy<Value = BackingBucket> {
    arb_bucket().prop_map(|b| BackingBucket {
        status: BucketStatus::Fresh,
        ..b
    })
}

// ============================================================================
// Proptests — runtime verification of the Lean theorems
// ============================================================================

proptest! {
    /// **`expire_preserves_available`** (Lean theorem of same name,
    /// §14 #34): expire does not decrement `fresh_unliened`. -/
    #[test]
    fn expire_preserves_available(b in arb_fresh_bucket()) {
        if let Some(b_post) = b.expire() {
            prop_assert_eq!(b_post.available(), b.available());
        }
    }

    /// **`expire_preserves_amounts`** (Lean §14 #34/#35): expire is
    /// the identity on every backing partition; only status
    /// changes.
    #[test]
    fn expire_preserves_amounts(b in arb_fresh_bucket()) {
        if let Some(b_post) = b.expire() {
            prop_assert_eq!(b_post.fresh_unliened, b.fresh_unliened);
            prop_assert_eq!(b_post.valid_liened, b.valid_liened);
            prop_assert_eq!(b_post.consumed_liened, b.consumed_liened);
            prop_assert_eq!(b_post.impaired_liened, b.impaired_liened);
            prop_assert_eq!(b_post.total_backing(), b.total_backing());
        }
    }

    /// **`expire_status`** (Lean): expire flips status Fresh →
    /// Expired.
    #[test]
    fn expire_status_transitions(b in arb_fresh_bucket()) {
        if let Some(b_post) = b.expire() {
            prop_assert_eq!(b.status, BucketStatus::Fresh);
            prop_assert_eq!(b_post.status, BucketStatus::Expired);
        }
    }

    /// **`available_after_lien_then_expire`** (Lean, §14 #36):
    /// after a partial lien followed by expire, available backing
    /// is bounded by the pre-lien available.
    #[test]
    fn available_after_lien_then_expire(
        b in arb_fresh_bucket(),
        amount in 0u128..=1_000_000u128,
    ) {
        if let Some(b1) = b.lien_against(amount) {
            if let Some(b2) = b1.expire() {
                prop_assert!(b2.available() <= b.available());
            }
        }
    }

    /// **lien_against preserves total_backing**: backing moves
    /// between partitions but stays in the bucket.
    #[test]
    fn lien_against_preserves_total(
        b in arb_bucket(),
        amount in 0u128..=1_000_000u128,
    ) {
        if let Some(b_post) = b.lien_against(amount) {
            prop_assert_eq!(b_post.total_backing(), b.total_backing());
        }
    }

    /// **consume_lien preserves total_backing**: valid → consumed
    /// move, both in the four-partition sum.
    #[test]
    fn consume_lien_preserves_total(
        b in arb_bucket(),
        amount in 0u128..=1_000_000u128,
    ) {
        if let Some(b_post) = b.consume_lien(amount) {
            prop_assert_eq!(b_post.total_backing(), b.total_backing());
        }
    }

    /// **release_lien preserves total_backing**.
    #[test]
    fn release_lien_preserves_total(
        b in arb_bucket(),
        amount in 0u128..=1_000_000u128,
    ) {
        if let Some(b_post) = b.release_lien(amount) {
            prop_assert_eq!(b_post.total_backing(), b.total_backing());
        }
    }

    /// **impair_lien preserves total_backing**.
    #[test]
    fn impair_lien_preserves_total(
        b in arb_bucket(),
        amount in 0u128..=1_000_000u128,
    ) {
        if let Some(b_post) = b.impair_lien(amount) {
            prop_assert_eq!(b_post.total_backing(), b.total_backing());
        }
    }

    /// **lien_against decrements available by exactly amount**:
    /// the bucket loses available backing equal to `amount`.
    #[test]
    fn lien_against_decrements_available(
        b in arb_bucket(),
        amount in 0u128..=1_000_000u128,
    ) {
        if let Some(b_post) = b.lien_against(amount) {
            prop_assert_eq!(b_post.available() + amount, b.available());
            prop_assert_eq!(b_post.valid_liened, b.valid_liened + amount);
        }
    }

    /// **release_lien increments available by exactly amount**:
    /// the dual of lien_against.
    #[test]
    fn release_lien_increments_available(
        b in arb_bucket(),
        amount in 0u128..=1_000_000u128,
    ) {
        if let Some(b_post) = b.release_lien(amount) {
            prop_assert_eq!(b_post.available(), b.available() + amount);
            prop_assert_eq!(b_post.valid_liened + amount, b.valid_liened);
        }
    }

    /// **open_fresh requires Empty status**: only an Empty bucket
    /// can be opened.
    #[test]
    fn open_fresh_requires_empty(
        b in arb_bucket(),
        amount in 0u128..=1_000_000u128,
        slot in any::<u64>(),
    ) {
        match b.status {
            BucketStatus::Empty => {
                let res = b.open_fresh(amount, slot);
                prop_assert!(res.is_some());
                let b_post = res.unwrap();
                prop_assert_eq!(b_post.status, BucketStatus::Fresh);
                prop_assert_eq!(b_post.fresh_unliened, amount);
                prop_assert_eq!(b_post.expiry_slot, slot);
            }
            _ => prop_assert!(b.open_fresh(amount, slot).is_none()),
        }
    }

    /// **expire requires Fresh status**: only a Fresh bucket can
    /// be expired.
    #[test]
    fn expire_requires_fresh(b in arb_bucket()) {
        match b.status {
            BucketStatus::Fresh => prop_assert!(b.expire().is_some()),
            _ => prop_assert!(b.expire().is_none()),
        }
    }

    /// **Sequence of lien transitions preserves total_backing**:
    /// composition of any number of `lien_against` / `consume_lien`
    /// / `release_lien` / `impair_lien` calls keeps the
    /// four-partition sum invariant.
    #[test]
    fn sequence_preserves_total_backing(
        b0 in arb_bucket(),
        steps in prop::collection::vec(
            (0u8..4, 0u128..=1_000u128),
            0..15,
        ),
    ) {
        let mut b = b0;
        let initial_total = b.total_backing();
        for (op, amt) in steps {
            let next = match op {
                0 => b.lien_against(amt),
                1 => b.consume_lien(amt),
                2 => b.release_lien(amt),
                _ => b.impair_lien(amt),
            };
            if let Some(b_next) = next {
                prop_assert_eq!(b_next.total_backing(), initial_total);
                b = b_next;
            }
        }
    }
}

// ============================================================================
// Tier 2.5 — Production connector
//
// Connects the BackingBucket reference port to `v16.rs::MarketGroupV16`'s
// per-domain `source_backing_buckets[d]` plus the production handlers
// `add_fresh_counterparty_backing_not_atomic` (open), the lien
// transitions, etc.
// ============================================================================

use percolator::v16::{
    BackingBucketStatusV16, BackingBucketV16, MarketGroupV16, V16Config,
};

/// Abstract the production bucket at a domain to the reference port.
/// The production struct and the reference port have field-by-field
/// alignment — this is essentially the identity map.
fn abstract_bucket(group: &MarketGroupV16, domain: usize) -> BackingBucket {
    let b = group.source_backing_buckets[domain];
    BackingBucket {
        market_id: b.market_id,
        fresh_unliened: b.fresh_unliened_backing_num,
        valid_liened: b.valid_liened_backing_num,
        consumed_liened: b.consumed_liened_backing_num,
        impaired_liened: b.impaired_liened_backing_num,
        expiry_slot: b.expiry_slot,
        status: match b.status {
            BackingBucketStatusV16::Empty => BucketStatus::Empty,
            BackingBucketStatusV16::Fresh => BucketStatus::Fresh,
            BackingBucketStatusV16::Expired => BucketStatus::Expired,
            BackingBucketStatusV16::Impaired => BucketStatus::Impaired,
        },
    }
}

/// Build a `MarketGroupV16` with a single-domain backing bucket
/// pre-populated via `add_fresh_counterparty_backing_not_atomic`.
/// Returns `None` if any setup step fails (e.g. config invalid).
fn setup_group_with_fresh_backing(
    fresh_amount: u128,
    claim_bound: u128,
) -> Option<MarketGroupV16> {
    let market = [1u8; 32];
    let mut g = MarketGroupV16::new(market, V16Config::public_user_fund(4, 0, 10)).ok()?;
    g.add_source_positive_claim_bound_not_atomic(0, claim_bound, 10)
        .ok()?;
    if fresh_amount == 0 {
        return Some(g);
    }
    // `add_fresh_counterparty_backing_not_atomic` requires
    // amount > 0 and expiry_slot > current_slot.
    g.add_fresh_counterparty_backing_not_atomic(0, fresh_amount, 10)
        .ok()?;
    Some(g)
}

proptest! {
    /// **Production-side total_backing conservation**: after any
    /// sequence of create / release / consume on the production
    /// lien handlers, the bucket's four-partition sum stays
    /// invariant (well — consume moves valid → consumed, both in
    /// the sum). The reference port's `*_preserves_total` family
    /// claims this directly; here we verify it holds for the real
    /// handlers.
    #[test]
    fn production_lien_transitions_preserve_total(
        fresh_amount in 1u128..=10_000u128,
        claim_bound in 1u128..=10_000u128,
        lien_amount in 1u128..=10_000u128,
    ) {
        prop_assume!(lien_amount <= fresh_amount);
        prop_assume!(lien_amount <= claim_bound);

        let Some(mut g) = setup_group_with_fresh_backing(fresh_amount, claim_bound) else {
            return Ok(());
        };

        let pre = abstract_bucket(&g, 0);
        let pre_total = pre.total_backing();

        // Create a lien (fresh_unliened → valid_liened).
        if g.create_source_credit_lien_from_counterparty_not_atomic(0, lien_amount)
            .is_ok()
        {
            let post = abstract_bucket(&g, 0);
            prop_assert_eq!(post.total_backing(), pre_total);
            prop_assert_eq!(post.fresh_unliened + lien_amount, pre.fresh_unliened);
            prop_assert_eq!(post.valid_liened, pre.valid_liened + lien_amount);
        }
    }

    /// **Production reference-equivalence for create_lien**: the
    /// production `create_source_credit_lien_from_counterparty_not_atomic`
    /// produces a post-state that matches the reference port's
    /// `lien_against`.
    #[test]
    fn production_create_lien_matches_reference(
        fresh_amount in 1u128..=10_000u128,
        claim_bound in 1u128..=10_000u128,
        lien_amount in 1u128..=10_000u128,
    ) {
        prop_assume!(lien_amount <= claim_bound);

        let Some(mut g) = setup_group_with_fresh_backing(fresh_amount, claim_bound) else {
            return Ok(());
        };

        let ref_pre = abstract_bucket(&g, 0);
        let ref_post = ref_pre.lien_against(lien_amount);

        let prod_ok = g
            .create_source_credit_lien_from_counterparty_not_atomic(0, lien_amount)
            .is_ok();
        let prod_post = abstract_bucket(&g, 0);

        if prod_ok {
            // Reference must also accept; post-states match on the four
            // backing fields.
            let ref_post = ref_post.expect("reference rejected what production accepted");
            prop_assert_eq!(prod_post.fresh_unliened, ref_post.fresh_unliened);
            prop_assert_eq!(prod_post.valid_liened, ref_post.valid_liened);
            prop_assert_eq!(prod_post.consumed_liened, ref_post.consumed_liened);
            prop_assert_eq!(prod_post.impaired_liened, ref_post.impaired_liened);
        }
    }

    /// **Production consume preserves total_backing**: valid →
    /// consumed move within the four-partition sum.
    #[test]
    fn production_consume_lien_preserves_total(
        (fresh_amount, lien_amount, consume_amount) in
            (1u128..=10_000u128).prop_flat_map(|fresh| {
                (1u128..=fresh).prop_flat_map(move |lien| {
                    (1u128..=lien).prop_map(move |consume| (fresh, lien, consume))
                })
            }),
    ) {
        let claim_bound = fresh_amount;  // claim ≥ lien is ensured

        let Some(mut g) = setup_group_with_fresh_backing(fresh_amount, claim_bound) else {
            return Ok(());
        };
        if g.create_source_credit_lien_from_counterparty_not_atomic(0, lien_amount)
            .is_err()
        {
            return Ok(());
        }

        let pre = abstract_bucket(&g, 0);
        let pre_total = pre.total_backing();

        if g.consume_source_credit_lien_from_counterparty_not_atomic(0, consume_amount)
            .is_ok()
        {
            let post = abstract_bucket(&g, 0);
            prop_assert_eq!(post.total_backing(), pre_total);
            prop_assert_eq!(post.valid_liened + consume_amount, pre.valid_liened);
            prop_assert_eq!(post.consumed_liened, pre.consumed_liened + consume_amount);
        }
    }

    /// **Production release preserves total_backing**: valid →
    /// fresh_unliened move (dual of create).
    #[test]
    fn production_release_lien_preserves_total(
        (fresh_amount, lien_amount, release_amount) in
            (1u128..=10_000u128).prop_flat_map(|fresh| {
                (1u128..=fresh).prop_flat_map(move |lien| {
                    (1u128..=lien).prop_map(move |release| (fresh, lien, release))
                })
            }),
    ) {
        let claim_bound = fresh_amount;

        let Some(mut g) = setup_group_with_fresh_backing(fresh_amount, claim_bound) else {
            return Ok(());
        };
        if g.create_source_credit_lien_from_counterparty_not_atomic(0, lien_amount)
            .is_err()
        {
            return Ok(());
        }

        let pre = abstract_bucket(&g, 0);
        let pre_total = pre.total_backing();

        if g.release_source_credit_lien_from_counterparty_not_atomic(0, release_amount)
            .is_ok()
        {
            let post = abstract_bucket(&g, 0);
            prop_assert_eq!(post.total_backing(), pre_total);
            prop_assert_eq!(post.valid_liened + release_amount, pre.valid_liened);
            prop_assert_eq!(post.fresh_unliened, pre.fresh_unliened + release_amount);
        }
    }
}

// silence unused-import lint in some configurations
#[allow(unused_imports)]
use BackingBucketV16 as _BackingBucketV16Used;

// ============================================================================
// Multi-step sequence bridges — Week 2 deepening
//
// Multi-step refinement harness for `BackingBucketV16` chains: a
// random sequence of `create_lien` / `release_lien` / `consume_lien`
// calls against the production engine, mirrored on the reference
// port. After each step, the production bucket's abstraction must
// equal the reference port's bucket.
//
// Sequencing scenarios that single-step tests miss:
//   - Composite invariants that hold only across multiple steps
//     (e.g. create-then-release returns to the prior state).
//   - Order-dependent state machines (consume after create_then_release
//     uses different reserves).
//   - Long chains where small per-step drift accumulates.
// ============================================================================

/// A scripted bucket action for the multi-step harness. Amounts are
/// constrained at sample time so the operations are likely to
/// succeed.
#[derive(Clone, Copy, Debug)]
enum BucketAction {
    CreateLien(u128),
    ReleaseLien(u128),
    ConsumeLien(u128),
}

fn arb_bucket_action() -> impl Strategy<Value = BucketAction> {
    (0u8..3, 1u128..=1_000u128).prop_map(|(op, amt)| match op {
        0 => BucketAction::CreateLien(amt),
        1 => BucketAction::ReleaseLien(amt),
        _ => BucketAction::ConsumeLien(amt),
    })
}

proptest! {
    /// **Multi-step lockstep: production and reference agree across
    /// N lien operations**. After each successful production call,
    /// the abstracted bucket equals the reference port's bucket.
    ///
    /// Crucially: any time production *accepts* a step, the
    /// reference port must also accept it, and the post-states
    /// must match field-by-field. This catches sequencing drift.
    #[test]
    fn multistep_bucket_lockstep(
        initial_fresh in 1_000u128..=10_000u128,
        claim_bound in 1_000u128..=10_000u128,
        actions in prop::collection::vec(arb_bucket_action(), 1..15),
    ) {
        let Some(mut g) = setup_group_with_fresh_backing(initial_fresh, claim_bound) else {
            return Ok(());
        };
        let mut r = abstract_bucket(&g, 0);

        for action in actions {
            // Snapshot pre-step (sanity).
            let pre_abstract = abstract_bucket(&g, 0);
            prop_assert_eq!(pre_abstract, r);

            // Apply in lockstep.
            let (prod_ok, ref_post) = match action {
                BucketAction::CreateLien(amount) => {
                    let prod = g
                        .create_source_credit_lien_from_counterparty_not_atomic(0, amount)
                        .is_ok();
                    (prod, r.lien_against(amount))
                }
                BucketAction::ReleaseLien(amount) => {
                    let prod = g
                        .release_source_credit_lien_from_counterparty_not_atomic(0, amount)
                        .is_ok();
                    (prod, r.release_lien(amount))
                }
                BucketAction::ConsumeLien(amount) => {
                    let prod = g
                        .consume_source_credit_lien_from_counterparty_not_atomic(0, amount)
                        .is_ok();
                    (prod, r.consume_lien(amount))
                }
            };

            match (prod_ok, ref_post) {
                (true, Some(r_post)) => {
                    let post_abstract = abstract_bucket(&g, 0);
                    // Match on the four backing partitions (other
                    // fields like market_id are anchors and don't
                    // change).
                    prop_assert_eq!(post_abstract.fresh_unliened, r_post.fresh_unliened);
                    prop_assert_eq!(post_abstract.valid_liened, r_post.valid_liened);
                    prop_assert_eq!(post_abstract.consumed_liened, r_post.consumed_liened);
                    prop_assert_eq!(post_abstract.impaired_liened, r_post.impaired_liened);
                    r = r_post;
                }
                (false, _) => {
                    // Production refused — stop the trace.
                    break;
                }
                (true, None) => {
                    prop_assert!(
                        false,
                        "lockstep violation: production accepted but reference rejected: {:?}",
                        action
                    );
                }
            }
        }
    }

    /// **Multi-step total_backing conservation**: across any sequence
    /// of create / release / consume / impair operations, the
    /// four-partition sum on the production side stays equal to
    /// the original total. The reference port carries this as a
    /// theorem; this test verifies production matches.
    #[test]
    fn multistep_total_backing_invariant(
        initial_fresh in 1_000u128..=10_000u128,
        actions in prop::collection::vec(arb_bucket_action(), 1..20),
    ) {
        let Some(mut g) = setup_group_with_fresh_backing(initial_fresh, initial_fresh) else {
            return Ok(());
        };
        let initial_total = abstract_bucket(&g, 0).total_backing();

        for action in actions {
            let _ok = match action {
                BucketAction::CreateLien(a) => {
                    g.create_source_credit_lien_from_counterparty_not_atomic(0, a).is_ok()
                }
                BucketAction::ReleaseLien(a) => {
                    g.release_source_credit_lien_from_counterparty_not_atomic(0, a).is_ok()
                }
                BucketAction::ConsumeLien(a) => {
                    g.consume_source_credit_lien_from_counterparty_not_atomic(0, a).is_ok()
                }
            };
            let post_total = abstract_bucket(&g, 0).total_backing();
            prop_assert_eq!(post_total, initial_total);
        }
    }

    /// **Round-trip: create N then release N restores original
    /// state**. A canonical sequencing test — if create_lien and
    /// release_lien are correctly paired, the bucket returns to
    /// its prior partition layout.
    #[test]
    fn create_then_release_round_trips(
        initial_fresh in 100u128..=5_000u128,
        amount in 1u128..=100u128,
    ) {
        prop_assume!(amount <= initial_fresh);

        let Some(mut g) = setup_group_with_fresh_backing(initial_fresh, initial_fresh) else {
            return Ok(());
        };
        let pre = abstract_bucket(&g, 0);

        if g.create_source_credit_lien_from_counterparty_not_atomic(0, amount).is_err() {
            return Ok(());
        }
        if g.release_source_credit_lien_from_counterparty_not_atomic(0, amount).is_err() {
            return Ok(());
        }

        let post = abstract_bucket(&g, 0);
        prop_assert_eq!(post.fresh_unliened, pre.fresh_unliened);
        prop_assert_eq!(post.valid_liened, pre.valid_liened);
        prop_assert_eq!(post.consumed_liened, pre.consumed_liened);
        prop_assert_eq!(post.impaired_liened, pre.impaired_liened);
    }

    /// **Sequence of consumes monotonically grows consumed_liened**:
    /// every successful consume strictly increases the consumed
    /// counter; sum of consumed amounts equals the total increment.
    #[test]
    fn multistep_consumes_grow_consumed_monotonically(
        initial_fresh in 1_000u128..=5_000u128,
        amounts in prop::collection::vec(1u128..=100u128, 1..10),
    ) {
        let Some(mut g) = setup_group_with_fresh_backing(initial_fresh, initial_fresh) else {
            return Ok(());
        };
        // First create one big lien.
        let total_to_lien: u128 = amounts.iter().sum();
        if total_to_lien > initial_fresh {
            return Ok(());
        }
        if g.create_source_credit_lien_from_counterparty_not_atomic(0, total_to_lien).is_err() {
            return Ok(());
        }

        let mut total_consumed_expected: u128 = 0;
        let pre_consumed = abstract_bucket(&g, 0).consumed_liened;

        for amount in amounts {
            let pre = abstract_bucket(&g, 0).consumed_liened;
            if g.consume_source_credit_lien_from_counterparty_not_atomic(0, amount).is_ok() {
                let post = abstract_bucket(&g, 0).consumed_liened;
                prop_assert_eq!(post, pre + amount);
                total_consumed_expected += amount;
            }
        }

        let final_consumed = abstract_bucket(&g, 0).consumed_liened;
        prop_assert_eq!(final_consumed, pre_consumed + total_consumed_expected);
    }
}
