#![allow(dead_code)] // reference port mirrors every Lean def; not all are exercised by proptests yet

//! State-machine refinement: `Percolator/LienLifecycle.lean` ↔ Rust.
//!
//! Tier 2 of the verification stack, third cluster bridge.
//!
//! Same pattern as the InsuranceLedger / BackingBucket bridges:
//! port the Lean spec as a self-contained Rust reference impl,
//! then proptest the Lean theorems hold at runtime.
//!
//! Lien is type-indexed by `BackingSource` (Counterparty or
//! Insurance) in Lean; in Rust we use a tagged sum `LienKey` and
//! a `SourceCreditLienAggregate` that holds one lien per source.
//! The "no cross-source mixup" §14 #23 property is by construction
//! at the type level on the Lean side; on the Rust side we make
//! it visible by giving each side a separately-named field.
//!
//! Theorems verified at runtime:
//!
//!   - §14 #32 (create_targets_named_source_only):
//!     create on counterparty doesn't touch insurance, and vv.
//!   - §14 #32 (create_*_increments): create increments
//!     faceClaim and backing by exactly the call arguments.
//!   - §14 #37 (consume_*_decrements): consume decrements both
//!     fields by exactly the call arguments.
//!   - §14 #19/#30 (impair_conserves_totalFace): impair moves
//!     face between valid and impaired buckets, conserving total.
//!   - §14 #19/#30 (consume_totalFace_decrement): consume reduces
//!     total face by exactly the consumed amount.
//!   - §14 #21/#31 (impair_preserves_backing): impair leaves
//!     backingReservedNum unchanged.
//!   - §14 #21/#31 (impair_grows_impaired): impair grows the
//!     impaired-face bucket by exactly the impaired amount.
//!   - release_eq_consume: release and consume have identical
//!     per-lien effects (the difference is in caller accounting).
//!
//! See `formal_verification/Percolator/LienLifecycle.lean`.

use proptest::prelude::*;

// ============================================================================
// Reference port — Rust copy of `Percolator/LienLifecycle.lean`
// ============================================================================

/// The two named backing sources. Lean's `BackingSource` enum.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BackingSource {
    Counterparty,
    Insurance,
}

/// A single lien against the named backing pool. Mirrors Lean
/// `Lien src` — but since Rust does not support type-indexed
/// structures here, we carry the `src` tag as a runtime field
/// and rely on `SourceCreditLienAggregate` to keep the two sides
/// in separately-named fields.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Lien {
    src: BackingSource,
    face_claim_locked_num: u128,
    backing_reserved_num: u128,
    effective_credit_reserved: u128,
    impaired_face_claim_num: u128,
    impaired_effective_credit_reserved: u128,
}

impl Lien {
    /// Empty lien for a given source. Lean `Lien.empty`.
    fn empty(src: BackingSource) -> Self {
        Self {
            src,
            face_claim_locked_num: 0,
            backing_reserved_num: 0,
            effective_credit_reserved: 0,
            impaired_face_claim_num: 0,
            impaired_effective_credit_reserved: 0,
        }
    }

    /// Total face claim — currently locked or impaired. Lean
    /// `totalFace`. This is the quantity conserved by `impair`
    /// and reduced by `consume` / `release`.
    fn total_face(&self) -> u128 {
        self.face_claim_locked_num
            .saturating_add(self.impaired_face_claim_num)
    }

    /// **Create**: add to face, backing, and effective. Lean
    /// `create`.
    fn create(&self, face: u128, backing: u128, effective: u128) -> Option<Self> {
        Some(Self {
            face_claim_locked_num: self.face_claim_locked_num.checked_add(face)?,
            backing_reserved_num: self.backing_reserved_num.checked_add(backing)?,
            effective_credit_reserved: self.effective_credit_reserved.checked_add(effective)?,
            ..*self
        })
    }

    /// **Consume**: subtract face, backing, effective. Backing is
    /// *spent* (gone from the system). Lean `consume`.
    fn consume(&self, face: u128, backing: u128, effective: u128) -> Option<Self> {
        if self.face_claim_locked_num < face
            || self.backing_reserved_num < backing
            || self.effective_credit_reserved < effective
        {
            return None;
        }
        Some(Self {
            face_claim_locked_num: self.face_claim_locked_num - face,
            backing_reserved_num: self.backing_reserved_num - backing,
            effective_credit_reserved: self.effective_credit_reserved - effective,
            ..*self
        })
    }

    /// **Release**: same per-lien shape as consume. The difference
    /// (backing returns to fresh pool vs is spent) is in caller
    /// accounting — see Lean `release_eq_consume`.
    fn release(&self, face: u128, backing: u128, effective: u128) -> Option<Self> {
        self.consume(face, backing, effective)
    }

    /// **Impair**: move face and effective from the valid bucket
    /// to the impaired bucket. `backingReservedNum` is NOT
    /// changed — the lien stays encumbered, just now bad. Lean
    /// `impair`.
    fn impair(&self, face: u128, effective: u128) -> Option<Self> {
        if self.face_claim_locked_num < face
            || self.effective_credit_reserved < effective
        {
            return None;
        }
        Some(Self {
            face_claim_locked_num: self.face_claim_locked_num - face,
            effective_credit_reserved: self.effective_credit_reserved - effective,
            impaired_face_claim_num: self
                .impaired_face_claim_num
                .checked_add(face)?,
            impaired_effective_credit_reserved: self
                .impaired_effective_credit_reserved
                .checked_add(effective)?,
            ..*self
        })
    }
}

/// Per-domain aggregate of liens with counterparty and insurance
/// in separately-named fields. Mirrors Lean
/// `SourceCreditLienAggregate`. The structural witness for §14
/// #23 is that the two sides live in separate fields — no single
/// expression can update both.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SourceCreditLienAggregate {
    domain: u32,
    source_claim_bound_num: u128,
    counterparty: Lien,
    insurance: Lien,
}

impl SourceCreditLienAggregate {
    fn empty_at(domain: u32) -> Self {
        Self {
            domain,
            source_claim_bound_num: 0,
            counterparty: Lien::empty(BackingSource::Counterparty),
            insurance: Lien::empty(BackingSource::Insurance),
        }
    }

    /// Total locked face claim (sum across sources). Lean
    /// `faceClaimLockedNum`.
    fn face_claim_locked_num(&self) -> u128 {
        self.counterparty
            .face_claim_locked_num
            .saturating_add(self.insurance.face_claim_locked_num)
    }

    /// Total impaired face claim. Lean `impairedFaceClaimNum`.
    fn impaired_face_claim_num(&self) -> u128 {
        self.counterparty
            .impaired_face_claim_num
            .saturating_add(self.insurance.impaired_face_claim_num)
    }

    /// Total backing reserved (across sources, BOUND-scaled).
    /// Lean `backingReservedNum`.
    fn backing_reserved_num(&self) -> u128 {
        self.counterparty
            .backing_reserved_num
            .saturating_add(self.insurance.backing_reserved_num)
    }

    /// Lookup the per-source lien by `BackingSource`. Lean
    /// `lienBySource`.
    fn lien_by_source(&self, src: BackingSource) -> Lien {
        match src {
            BackingSource::Counterparty => self.counterparty,
            BackingSource::Insurance => self.insurance,
        }
    }
}

// ============================================================================
// Generators
// ============================================================================

fn arb_lien(src: BackingSource) -> impl Strategy<Value = Lien> {
    (
        0u128..=1_000_000u128,
        0u128..=1_000_000u128,
        0u128..=1_000_000u128,
        0u128..=1_000_000u128,
        0u128..=1_000_000u128,
    )
        .prop_map(move |(face, backing, effective, imp_face, imp_eff)| Lien {
            src,
            face_claim_locked_num: face,
            backing_reserved_num: backing,
            effective_credit_reserved: effective,
            impaired_face_claim_num: imp_face,
            impaired_effective_credit_reserved: imp_eff,
        })
}

fn arb_counterparty_lien() -> impl Strategy<Value = Lien> {
    arb_lien(BackingSource::Counterparty)
}

fn arb_insurance_lien() -> impl Strategy<Value = Lien> {
    arb_lien(BackingSource::Insurance)
}

fn arb_aggregate() -> impl Strategy<Value = SourceCreditLienAggregate> {
    (any::<u32>(), 0u128..=1_000_000u128, arb_counterparty_lien(), arb_insurance_lien())
        .prop_map(|(dom, bound, cp, ins)| SourceCreditLienAggregate {
            domain: dom,
            source_claim_bound_num: bound,
            counterparty: cp,
            insurance: ins,
        })
}

// ============================================================================
// Proptests — runtime verification of the Lean theorems
// ============================================================================

proptest! {
    /// **`create_targets_named_source_only`** (Lean §14 #32):
    /// creating on the counterparty side leaves the insurance lien
    /// untouched.
    #[test]
    fn create_counterparty_leaves_insurance(
        a in arb_aggregate(),
        face in 0u128..=1_000_000u128,
        backing in 0u128..=1_000_000u128,
        effective in 0u128..=1_000_000u128,
    ) {
        if let Some(new_cp) = a.counterparty.create(face, backing, effective) {
            let a_new = SourceCreditLienAggregate { counterparty: new_cp, ..a };
            prop_assert_eq!(a_new.insurance, a.insurance);
        }
    }

    /// **`create_insurance_leaves_counterparty`** (Lean §14 #32):
    /// the symmetric statement for the insurance side.
    #[test]
    fn create_insurance_leaves_counterparty(
        a in arb_aggregate(),
        face in 0u128..=1_000_000u128,
        backing in 0u128..=1_000_000u128,
        effective in 0u128..=1_000_000u128,
    ) {
        if let Some(new_ins) = a.insurance.create(face, backing, effective) {
            let a_new = SourceCreditLienAggregate { insurance: new_ins, ..a };
            prop_assert_eq!(a_new.counterparty, a.counterparty);
        }
    }

    /// **`create_faceClaim_increments`** (Lean §14 #32): create
    /// increments faceClaimLockedNum by exactly `face`.
    #[test]
    fn create_face_claim_increments(
        l in arb_counterparty_lien(),
        face in 0u128..=1_000_000u128,
        backing in 0u128..=1_000_000u128,
        effective in 0u128..=1_000_000u128,
    ) {
        if let Some(l_post) = l.create(face, backing, effective) {
            prop_assert_eq!(
                l_post.face_claim_locked_num,
                l.face_claim_locked_num + face
            );
        }
    }

    /// **`create_backing_increments`** (Lean §14 #32): create
    /// increments backingReservedNum by exactly `backing`.
    #[test]
    fn create_backing_increments(
        l in arb_counterparty_lien(),
        face in 0u128..=1_000_000u128,
        backing in 0u128..=1_000_000u128,
        effective in 0u128..=1_000_000u128,
    ) {
        if let Some(l_post) = l.create(face, backing, effective) {
            prop_assert_eq!(
                l_post.backing_reserved_num,
                l.backing_reserved_num + backing
            );
        }
    }

    /// **`consume_faceClaim_decrements`** (Lean §14 #37): consume
    /// decrements faceClaimLockedNum by exactly `face`.
    #[test]
    fn consume_face_claim_decrements(
        l in arb_counterparty_lien(),
        face in 0u128..=1_000_000u128,
        backing in 0u128..=1_000_000u128,
        effective in 0u128..=1_000_000u128,
    ) {
        if let Some(l_post) = l.consume(face, backing, effective) {
            prop_assert_eq!(
                l_post.face_claim_locked_num + face,
                l.face_claim_locked_num
            );
        }
    }

    /// **`consume_backing_decrements`** (Lean §14 #37): consume
    /// decrements backingReservedNum by exactly `backing`.
    #[test]
    fn consume_backing_decrements(
        l in arb_counterparty_lien(),
        face in 0u128..=1_000_000u128,
        backing in 0u128..=1_000_000u128,
        effective in 0u128..=1_000_000u128,
    ) {
        if let Some(l_post) = l.consume(face, backing, effective) {
            prop_assert_eq!(
                l_post.backing_reserved_num + backing,
                l.backing_reserved_num
            );
        }
    }

    /// **`impair_conserves_totalFace`** (Lean §14 #19/#30): impair
    /// moves face between buckets without losing any. The total
    /// face quantity is preserved.
    #[test]
    fn impair_conserves_total_face(
        l in arb_counterparty_lien(),
        face in 0u128..=1_000_000u128,
        effective in 0u128..=1_000_000u128,
    ) {
        if let Some(l_post) = l.impair(face, effective) {
            prop_assert_eq!(l_post.total_face(), l.total_face());
        }
    }

    /// **`consume_totalFace_decrement`** (Lean §14 #19/#30):
    /// consume reduces total face by exactly the consumed amount
    /// (because the impaired bucket is untouched).
    #[test]
    fn consume_total_face_decrement(
        l in arb_counterparty_lien(),
        face in 0u128..=1_000_000u128,
        backing in 0u128..=1_000_000u128,
        effective in 0u128..=1_000_000u128,
    ) {
        if let Some(l_post) = l.consume(face, backing, effective) {
            prop_assert_eq!(l_post.total_face() + face, l.total_face());
        }
    }

    /// **`impair_grows_impaired`** (Lean §14 #21/#31): impair grows
    /// impairedFaceClaimNum by exactly `face`.
    #[test]
    fn impair_grows_impaired(
        l in arb_counterparty_lien(),
        face in 0u128..=1_000_000u128,
        effective in 0u128..=1_000_000u128,
    ) {
        if let Some(l_post) = l.impair(face, effective) {
            prop_assert_eq!(
                l_post.impaired_face_claim_num,
                l.impaired_face_claim_num + face
            );
        }
    }

    /// **`impair_preserves_backing`** (Lean §14 #21/#31): impair
    /// leaves backingReservedNum unchanged — the lien stays
    /// encumbered against the backing pool.
    #[test]
    fn impair_preserves_backing(
        l in arb_counterparty_lien(),
        face in 0u128..=1_000_000u128,
        effective in 0u128..=1_000_000u128,
    ) {
        if let Some(l_post) = l.impair(face, effective) {
            prop_assert_eq!(l_post.backing_reserved_num, l.backing_reserved_num);
        }
    }

    /// **`release_eq_consume`** (Lean): release and consume have
    /// identical per-lien effects. The difference (backing returns
    /// to fresh vs is spent) lives in caller accounting.
    #[test]
    fn release_eq_consume(
        l in arb_counterparty_lien(),
        face in 0u128..=1_000_000u128,
        backing in 0u128..=1_000_000u128,
        effective in 0u128..=1_000_000u128,
    ) {
        prop_assert_eq!(
            l.release(face, backing, effective),
            l.consume(face, backing, effective)
        );
    }

    /// **lien_by_source matches the named field**: dispatching by
    /// `BackingSource` returns exactly the field of that side.
    #[test]
    fn lien_by_source_dispatches_correctly(a in arb_aggregate()) {
        prop_assert_eq!(a.lien_by_source(BackingSource::Counterparty), a.counterparty);
        prop_assert_eq!(a.lien_by_source(BackingSource::Insurance), a.insurance);
    }

    /// **Sequence of consume/impair preserves total_face down**:
    /// each consume reduces total_face by exactly the consumed
    /// face; each impair preserves it. Composition is bounded.
    #[test]
    fn sequence_consume_impair_total_face_monotone(
        l0 in arb_counterparty_lien(),
        steps in prop::collection::vec(
            (any::<bool>(), 0u128..=1_000u128, 0u128..=1_000u128, 0u128..=1_000u128),
            0..15,
        ),
    ) {
        let mut l = l0;
        for (do_consume, face, backing, effective) in steps {
            let prev_total = l.total_face();
            let next = if do_consume {
                l.consume(face, backing, effective)
            } else {
                l.impair(face, effective)
            };
            if let Some(l_next) = next {
                // total_face either decreases by `face` (consume) or stays the same (impair).
                prop_assert!(l_next.total_face() <= prev_total);
                l = l_next;
            }
        }
    }
}

// ============================================================================
// Tier 2.5 — Production connector (backing-side per-domain aggregate)
//
// The production tracks lien data across multiple layers (bucket,
// source_credit aggregate, account). The reference port's `Lien` is a
// single record. The clean bridge is on the backing-side per-domain
// aggregate: `source_credit[d].valid_liened_backing_num` is updated
// by every `create / release / consume` and corresponds to the
// reference port's `Lien.backing_reserved_num`.
//
// This connector verifies the per-domain backing aggregate evolves as
// the reference port's Lien.backing transitions predict.
// ============================================================================

use percolator::v16::{MarketGroupV16, V16Config};

fn group_with_lien_setup(
    fresh_amount: u128,
    claim_bound: u128,
) -> Option<MarketGroupV16> {
    let market = [1u8; 32];
    let mut g = MarketGroupV16::new(market, V16Config::public_user_fund(4, 0, 10)).ok()?;
    g.add_source_positive_claim_bound_not_atomic(0, claim_bound, 10).ok()?;
    if fresh_amount > 0 {
        g.add_fresh_counterparty_backing_not_atomic(0, fresh_amount, 10).ok()?;
    }
    Some(g)
}

proptest! {
    /// **Production create_lien increments source_credit aggregate by
    /// exactly amount** (mirrors reference `Lien.create(0, amount, 0)`
    /// on the backing-side field).
    #[test]
    fn production_source_credit_aggregate_after_create(
        fresh in 1u128..=10_000u128,
        bound in 1u128..=10_000u128,
        lien_amount in 1u128..=10_000u128,
    ) {
        prop_assume!(lien_amount <= fresh);
        prop_assume!(lien_amount <= bound);

        let Some(mut g) = group_with_lien_setup(fresh, bound) else {
            return Ok(());
        };

        let pre_valid = g.source_credit[0].valid_liened_backing_num;
        if g.create_source_credit_lien_from_counterparty_not_atomic(0, lien_amount)
            .is_ok()
        {
            let post_valid = g.source_credit[0].valid_liened_backing_num;
            prop_assert_eq!(post_valid, pre_valid + lien_amount);
        }
    }

    /// **Production release_lien decrements source_credit aggregate
    /// by exactly amount** (mirrors reference `Lien.release(0,
    /// amount, 0)`).
    #[test]
    fn production_source_credit_aggregate_after_release(
        (fresh, lien_amount, release_amount) in
            (1u128..=10_000u128).prop_flat_map(|fresh| {
                (1u128..=fresh).prop_flat_map(move |lien| {
                    (1u128..=lien).prop_map(move |release| (fresh, lien, release))
                })
            }),
    ) {
        let Some(mut g) = group_with_lien_setup(fresh, fresh) else {
            return Ok(());
        };
        if g.create_source_credit_lien_from_counterparty_not_atomic(0, lien_amount)
            .is_err()
        {
            return Ok(());
        }

        let pre_valid = g.source_credit[0].valid_liened_backing_num;
        if g.release_source_credit_lien_from_counterparty_not_atomic(0, release_amount)
            .is_ok()
        {
            let post_valid = g.source_credit[0].valid_liened_backing_num;
            prop_assert_eq!(post_valid + release_amount, pre_valid);
        }
    }

    /// **Production consume_lien increments spent_backing_num and
    /// decrements valid_liened_backing_num by exactly amount**
    /// (mirrors reference `Lien.consume(0, amount, 0)` plus the
    /// atomic move-to-spent that BackingBucket models via
    /// consumed_liened).
    #[test]
    fn production_source_credit_aggregate_after_consume(
        (fresh, lien_amount, consume_amount) in
            (1u128..=10_000u128).prop_flat_map(|fresh| {
                (1u128..=fresh).prop_flat_map(move |lien| {
                    (1u128..=lien).prop_map(move |consume| (fresh, lien, consume))
                })
            }),
    ) {
        let Some(mut g) = group_with_lien_setup(fresh, fresh) else {
            return Ok(());
        };
        if g.create_source_credit_lien_from_counterparty_not_atomic(0, lien_amount)
            .is_err()
        {
            return Ok(());
        }

        let pre_valid = g.source_credit[0].valid_liened_backing_num;
        let pre_spent = g.source_credit[0].spent_backing_num;
        if g.consume_source_credit_lien_from_counterparty_not_atomic(0, consume_amount)
            .is_ok()
        {
            let post_valid = g.source_credit[0].valid_liened_backing_num;
            let post_spent = g.source_credit[0].spent_backing_num;
            prop_assert_eq!(post_valid + consume_amount, pre_valid);
            prop_assert_eq!(post_spent, pre_spent + consume_amount);
        }
    }

    // ========================================================================
    // Multi-step sequencing — Week 2 deepening
    // ========================================================================

    /// **Sum of valid_liened + spent_backing equals total created**:
    /// over any sequence of create / consume / release, the
    /// production aggregate `valid_liened_backing_num +
    /// spent_backing_num + (fresh_unliened released back)` tracks
    /// the cumulative create amount minus total released. This
    /// is the multi-step bookkeeping invariant.
    #[test]
    fn multistep_aggregate_tracking(
        fresh in 5_000u128..=10_000u128,
        actions in prop::collection::vec((0u8..3, 1u128..=200u128), 1..15),
    ) {
        let Some(mut g) = group_with_lien_setup(fresh, fresh) else {
            return Ok(());
        };
        let mut cumulative_created: u128 = 0;
        let mut cumulative_consumed: u128 = 0;
        let mut cumulative_released: u128 = 0;

        for (op, amount) in actions {
            let pre_valid = g.source_credit[0].valid_liened_backing_num;
            let pre_spent = g.source_credit[0].spent_backing_num;
            match op {
                0 => {
                    // create
                    if g.create_source_credit_lien_from_counterparty_not_atomic(0, amount)
                        .is_ok()
                    {
                        cumulative_created += amount;
                        let post_valid = g.source_credit[0].valid_liened_backing_num;
                        prop_assert_eq!(post_valid, pre_valid + amount);
                    }
                }
                1 => {
                    // release
                    if g.release_source_credit_lien_from_counterparty_not_atomic(0, amount)
                        .is_ok()
                    {
                        cumulative_released += amount;
                        let post_valid = g.source_credit[0].valid_liened_backing_num;
                        prop_assert_eq!(post_valid + amount, pre_valid);
                    }
                }
                _ => {
                    // consume
                    if g.consume_source_credit_lien_from_counterparty_not_atomic(0, amount)
                        .is_ok()
                    {
                        cumulative_consumed += amount;
                        let post_valid = g.source_credit[0].valid_liened_backing_num;
                        let post_spent = g.source_credit[0].spent_backing_num;
                        prop_assert_eq!(post_valid + amount, pre_valid);
                        prop_assert_eq!(post_spent, pre_spent + amount);
                    }
                }
            }
        }

        // Cumulative invariant:
        //   final_valid = created - released - consumed
        //   final_spent = consumed
        // Sum: final_valid + final_spent = created - released
        // ↔   final_valid + final_spent + released = created
        let final_valid = g.source_credit[0].valid_liened_backing_num;
        let final_spent = g.source_credit[0].spent_backing_num;
        let _ = cumulative_consumed;  // tracked but already captured by final_spent
        prop_assert_eq!(
            final_valid + final_spent + cumulative_released,
            cumulative_created
        );
    }

    /// **Create-then-release inverts at the source-credit
    /// aggregate**: creating amount A then releasing A leaves the
    /// source_credit[d].valid_liened_backing_num at its prior
    /// value.
    #[test]
    fn multistep_create_release_inverts_at_aggregate(
        fresh in 100u128..=5_000u128,
        amount in 1u128..=100u128,
    ) {
        prop_assume!(amount <= fresh);

        let Some(mut g) = group_with_lien_setup(fresh, fresh) else {
            return Ok(());
        };
        let pre_valid = g.source_credit[0].valid_liened_backing_num;

        if g.create_source_credit_lien_from_counterparty_not_atomic(0, amount).is_err() {
            return Ok(());
        }
        if g.release_source_credit_lien_from_counterparty_not_atomic(0, amount).is_err() {
            return Ok(());
        }

        let post_valid = g.source_credit[0].valid_liened_backing_num;
        prop_assert_eq!(post_valid, pre_valid);
    }
}
