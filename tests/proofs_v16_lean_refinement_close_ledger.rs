#![allow(dead_code)] // reference port mirrors every Lean def; not all are exercised by proptests yet

//! State-machine refinement: `Percolator/CloseLedger.lean` +
//! `Percolator/ClosePriority.lean` ↔ Rust.
//!
//! Tier 2 of the verification stack, eighth and final cluster
//! bridge. Covers the close-progress ledger and its booking
//! transitions, plus the four-component close priority with its
//! strict-total-order properties.
//!
//! Theorems verified at runtime:
//!
//!   - `empty_no_irreversible_progress`: a fresh ledger has no
//!     irreversible progress.
//!   - `book*_preserves_anchors`: every booking transition leaves
//!     the immutable close anchors (closeId, assetIndex, marketId,
//!     domainSide, grossLossAtCloseStart, driftReferenceSlot,
//!     maxCloseSlot) untouched.
//!   - `book*_decreases_residual` (or addDrift_increases_residual):
//!     residual moves by exactly the booked amount.
//!   - `book*_increments_*` (per booking counter).
//!   - `applyQuantityAdl_requires_zero_residual` (§10 spec invariant).
//!   - **ClosePriority**: §14 #92 strict-total-order (irreflexive,
//!     asymmetric, transitive, trichotomy by construction).
//!   - §14 #93 (`distinct_closeId_strictly_comparable`): two
//!     priorities with the same first three components but distinct
//!     closeIds are strictly comparable.
//!
//! See `formal_verification/Percolator/CloseLedger.lean` and
//! `Percolator/ClosePriority.lean`.

use proptest::prelude::*;

// ============================================================================
// Reference port — CloseLedger
// ============================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Side {
    Long,
    Short,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CloseLedger {
    active: bool,
    finalized: bool,
    canceled: bool,
    adl_applied: bool,
    close_id: u64,
    asset_index: u32,
    market_id: u64,
    domain_side: Side,
    gross_loss_at_close_start: u128,
    drift_reference_slot: u64,
    max_close_slot: u64,
    support_consumed: u128,
    junior_face_burned: u128,
    insurance_spent: u128,
    b_loss_booked: u128,
    explicit_loss_assigned: u128,
    quantity_adl_applied_q: u128,
    drift_consumed: u128,
    pending_obligation_credits: u128,
    residual_remaining: u128,
}

impl CloseLedger {
    fn empty(
        close_id: u64,
        asset: u32,
        market: u64,
        side: Side,
        gross: u128,
        drift_ref_slot: u64,
        max_slot: u64,
    ) -> Self {
        Self {
            active: true,
            finalized: false,
            canceled: false,
            adl_applied: false,
            close_id,
            asset_index: asset,
            market_id: market,
            domain_side: side,
            gross_loss_at_close_start: gross,
            drift_reference_slot: drift_ref_slot,
            max_close_slot: max_slot,
            support_consumed: 0,
            junior_face_burned: 0,
            insurance_spent: 0,
            b_loss_booked: 0,
            explicit_loss_assigned: 0,
            quantity_adl_applied_q: 0,
            drift_consumed: 0,
            pending_obligation_credits: 0,
            residual_remaining: gross,
        }
    }

    /// Mirror of `has_irreversible_progress`. Lean
    /// `hasIrreversibleProgress`.
    fn has_irreversible_progress(&self) -> bool {
        self.support_consumed != 0
            || self.junior_face_burned != 0
            || self.insurance_spent != 0
            || self.b_loss_booked != 0
            || self.explicit_loss_assigned != 0
            || self.quantity_adl_applied_q != 0
            || self.drift_consumed != 0
    }

    fn is_active_not_done(&self) -> bool {
        self.active && !self.finalized && !self.canceled
    }

    fn book_support(&self, amount: u128) -> Option<Self> {
        if !self.is_active_not_done() || self.residual_remaining < amount {
            return None;
        }
        Some(Self {
            support_consumed: self.support_consumed.checked_add(amount)?,
            residual_remaining: self.residual_remaining - amount,
            ..*self
        })
    }

    fn book_insurance(&self, amount: u128) -> Option<Self> {
        if !self.is_active_not_done() || self.residual_remaining < amount {
            return None;
        }
        Some(Self {
            insurance_spent: self.insurance_spent.checked_add(amount)?,
            residual_remaining: self.residual_remaining - amount,
            ..*self
        })
    }

    fn book_b(&self, chunk: u128) -> Option<Self> {
        if !self.is_active_not_done() || self.residual_remaining < chunk {
            return None;
        }
        Some(Self {
            b_loss_booked: self.b_loss_booked.checked_add(chunk)?,
            residual_remaining: self.residual_remaining - chunk,
            ..*self
        })
    }

    fn book_explicit(&self, amount: u128) -> Option<Self> {
        if !self.is_active_not_done() || self.residual_remaining < amount {
            return None;
        }
        Some(Self {
            explicit_loss_assigned: self.explicit_loss_assigned.checked_add(amount)?,
            residual_remaining: self.residual_remaining - amount,
            ..*self
        })
    }

    fn book_pending_obligation(&self, amount: u128) -> Option<Self> {
        if !self.is_active_not_done() || self.residual_remaining < amount {
            return None;
        }
        Some(Self {
            pending_obligation_credits: self
                .pending_obligation_credits
                .checked_add(amount)?,
            residual_remaining: self.residual_remaining - amount,
            ..*self
        })
    }

    fn add_drift(&self, delta: u128) -> Option<Self> {
        if !self.is_active_not_done() {
            return None;
        }
        Some(Self {
            drift_consumed: self.drift_consumed.checked_add(delta)?,
            residual_remaining: self.residual_remaining.checked_add(delta)?,
            ..*self
        })
    }

    fn apply_quantity_adl(&self, q: u128) -> Option<Self> {
        if !self.is_active_not_done()
            || self.residual_remaining != 0
            || self.adl_applied
        {
            return None;
        }
        Some(Self {
            quantity_adl_applied_q: q,
            adl_applied: true,
            ..*self
        })
    }

    fn finalize(&self) -> Option<Self> {
        if !self.is_active_not_done() {
            return None;
        }
        Some(Self {
            finalized: true,
            active: false,
            ..*self
        })
    }

    fn cure_and_cancel(&self) -> Option<Self> {
        if !self.is_active_not_done() || self.has_irreversible_progress() {
            return None;
        }
        Some(Self {
            canceled: true,
            active: false,
            ..*self
        })
    }
}

// ============================================================================
// Reference port — ClosePriority
// ============================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ClosePriority {
    certified_liq_deficit: u128,
    total_abs_risk_notional: u128,
    drift_reference_slot: u64,
    close_id: u64,
}

impl ClosePriority {
    /// Lex compare: (deficit DESC, notional DESC, drift_slot ASC,
    /// closeId ASC). Lean `lt`.
    fn lt(&self, other: &Self) -> bool {
        if self.certified_liq_deficit > other.certified_liq_deficit {
            return true;
        }
        if self.certified_liq_deficit < other.certified_liq_deficit {
            return false;
        }
        if self.total_abs_risk_notional > other.total_abs_risk_notional {
            return true;
        }
        if self.total_abs_risk_notional < other.total_abs_risk_notional {
            return false;
        }
        if self.drift_reference_slot < other.drift_reference_slot {
            return true;
        }
        if self.drift_reference_slot > other.drift_reference_slot {
            return false;
        }
        self.close_id < other.close_id
    }
}

// ============================================================================
// Anchor-equality predicate
// ============================================================================

fn anchors_eq(a: &CloseLedger, b: &CloseLedger) -> bool {
    a.close_id == b.close_id
        && a.asset_index == b.asset_index
        && a.market_id == b.market_id
        && a.domain_side == b.domain_side
        && a.gross_loss_at_close_start == b.gross_loss_at_close_start
        && a.drift_reference_slot == b.drift_reference_slot
        && a.max_close_slot == b.max_close_slot
}

// ============================================================================
// Generators
// ============================================================================

fn arb_side() -> impl Strategy<Value = Side> {
    prop_oneof![Just(Side::Long), Just(Side::Short)]
}

fn arb_ledger() -> impl Strategy<Value = CloseLedger> {
    (
        any::<u64>(),
        any::<u32>(),
        any::<u64>(),
        arb_side(),
        0u128..=1_000_000u128,
        any::<u64>(),
        any::<u64>(),
    )
        .prop_map(|(cid, ai, mid, side, gross, drs, mcs)| {
            CloseLedger::empty(cid, ai, mid, side, gross, drs, mcs)
        })
}

fn arb_priority() -> impl Strategy<Value = ClosePriority> {
    (
        0u128..=1_000u128,
        0u128..=1_000u128,
        0u64..=1_000u64,
        0u64..=1_000u64,
    )
        .prop_map(|(d, n, ds, c)| ClosePriority {
            certified_liq_deficit: d,
            total_abs_risk_notional: n,
            drift_reference_slot: ds,
            close_id: c,
        })
}

// ============================================================================
// Proptests
// ============================================================================

proptest! {
    /// **`empty_no_irreversible_progress`** (Lean): a fresh ledger
    /// has no irreversible progress flag set.
    #[test]
    fn empty_no_irreversible_progress(
        cid in any::<u64>(),
        ai in any::<u32>(),
        mid in any::<u64>(),
        side in arb_side(),
        gross in 0u128..=1_000_000u128,
        drs in any::<u64>(),
        mcs in any::<u64>(),
    ) {
        let l = CloseLedger::empty(cid, ai, mid, side, gross, drs, mcs);
        prop_assert!(!l.has_irreversible_progress());
    }

    /// **`bookSupport_preserves_anchors`** (Lean): bookSupport
    /// leaves the immutable close anchors untouched.
    #[test]
    fn book_support_preserves_anchors(
        l in arb_ledger(),
        amount in 0u128..=2_000_000u128,
    ) {
        if let Some(l_post) = l.book_support(amount) {
            prop_assert!(anchors_eq(&l, &l_post));
        }
    }

    /// **`bookSupport_decreases_residual`** (Lean): bookSupport
    /// decreases residual_remaining by exactly amount.
    #[test]
    fn book_support_decreases_residual(
        l in arb_ledger(),
        amount in 0u128..=2_000_000u128,
    ) {
        if let Some(l_post) = l.book_support(amount) {
            prop_assert_eq!(l_post.residual_remaining + amount, l.residual_remaining);
            prop_assert_eq!(l_post.support_consumed, l.support_consumed + amount);
        }
    }

    /// **`bookInsurance_decreases_residual`** (Lean).
    #[test]
    fn book_insurance_decreases_residual(
        l in arb_ledger(),
        amount in 0u128..=2_000_000u128,
    ) {
        if let Some(l_post) = l.book_insurance(amount) {
            prop_assert_eq!(l_post.residual_remaining + amount, l.residual_remaining);
            prop_assert_eq!(l_post.insurance_spent, l.insurance_spent + amount);
            prop_assert!(anchors_eq(&l, &l_post));
        }
    }

    /// **`bookB_decreases_residual`** (Lean).
    #[test]
    fn book_b_decreases_residual(
        l in arb_ledger(),
        chunk in 0u128..=2_000_000u128,
    ) {
        if let Some(l_post) = l.book_b(chunk) {
            prop_assert_eq!(l_post.residual_remaining + chunk, l.residual_remaining);
            prop_assert_eq!(l_post.b_loss_booked, l.b_loss_booked + chunk);
            prop_assert!(anchors_eq(&l, &l_post));
        }
    }

    /// **`bookExplicit_decreases_residual`** (Lean).
    #[test]
    fn book_explicit_decreases_residual(
        l in arb_ledger(),
        amount in 0u128..=2_000_000u128,
    ) {
        if let Some(l_post) = l.book_explicit(amount) {
            prop_assert_eq!(l_post.residual_remaining + amount, l.residual_remaining);
            prop_assert_eq!(l_post.explicit_loss_assigned, l.explicit_loss_assigned + amount);
            prop_assert!(anchors_eq(&l, &l_post));
        }
    }

    /// **`bookPendingObligation_decreases_residual`** (Lean §14 #47):
    /// the credit is applied atomically — both fields move
    /// in the same step.
    #[test]
    fn book_pending_obligation_atomic(
        l in arb_ledger(),
        amount in 0u128..=2_000_000u128,
    ) {
        if let Some(l_post) = l.book_pending_obligation(amount) {
            prop_assert_eq!(l_post.residual_remaining + amount, l.residual_remaining);
            prop_assert_eq!(
                l_post.pending_obligation_credits,
                l.pending_obligation_credits + amount
            );
            prop_assert!(anchors_eq(&l, &l_post));
        }
    }

    /// **`addDrift_increases_residual`** (Lean): drift increases
    /// residual.
    #[test]
    fn add_drift_increases_residual(
        l in arb_ledger(),
        delta in 0u128..=1_000u128,
    ) {
        if let Some(l_post) = l.add_drift(delta) {
            prop_assert_eq!(l_post.residual_remaining, l.residual_remaining + delta);
            prop_assert_eq!(l_post.drift_consumed, l.drift_consumed + delta);
            prop_assert!(anchors_eq(&l, &l_post));
        }
    }

    /// **`applyQuantityAdl_requires_zero_residual`** (Lean): ADL only
    /// applies when residual is fully booked.
    #[test]
    fn apply_quantity_adl_requires_zero_residual(
        l in arb_ledger(),
        q in 0u128..=1_000u128,
    ) {
        if let Some(_) = l.apply_quantity_adl(q) {
            prop_assert_eq!(l.residual_remaining, 0);
            prop_assert!(!l.adl_applied);
        }
    }

    /// **`cureAndCancel`** requires no irreversible progress (the
    /// spec rule: cancel only before any booking has fired).
    #[test]
    fn cure_and_cancel_requires_no_progress(l in arb_ledger()) {
        if let Some(_) = l.cure_and_cancel() {
            prop_assert!(!l.has_irreversible_progress());
        }
    }

    /// **`finalize_preserves_anchors`** (Lean).
    #[test]
    fn finalize_preserves_anchors(l in arb_ledger()) {
        if let Some(l_post) = l.finalize() {
            prop_assert!(anchors_eq(&l, &l_post));
            prop_assert!(l_post.finalized);
            prop_assert!(!l_post.active);
        }
    }

    // ========================================================================
    // ClosePriority §14 #92: strict total order
    // ========================================================================

    /// **`lt_irrefl`** (Lean §14 #92): no priority is strictly less
    /// than itself.
    #[test]
    fn priority_lt_irreflexive(a in arb_priority()) {
        prop_assert!(!a.lt(&a));
    }

    /// **`lt_asymm`** (Lean §14 #92): if a < b then not b < a.
    #[test]
    fn priority_lt_asymmetric(a in arb_priority(), b in arb_priority()) {
        if a.lt(&b) {
            prop_assert!(!b.lt(&a));
        }
    }

    /// **`lt_trans`** (Lean §14 #92): if a < b and b < c, then a < c.
    #[test]
    fn priority_lt_transitive(
        a in arb_priority(),
        b in arb_priority(),
        c in arb_priority(),
    ) {
        if a.lt(&b) && b.lt(&c) {
            prop_assert!(a.lt(&c));
        }
    }

    /// **`lt_trichotomy`** (Lean §14 #92): for any a, b: a < b OR
    /// b < a OR a == b (structurally).
    #[test]
    fn priority_lt_trichotomy(a in arb_priority(), b in arb_priority()) {
        prop_assert!(a.lt(&b) || b.lt(&a) || a == b);
    }

    /// **`distinct_closeId_strictly_comparable`** (Lean §14 #93):
    /// two priorities with the same first three components but
    /// distinct closeIds are strictly comparable.
    #[test]
    fn priority_distinct_close_id_comparable(
        deficit in 0u128..=1_000u128,
        notional in 0u128..=1_000u128,
        drift_slot in 0u64..=1_000u64,
        cid1 in 0u64..=500u64,
        cid2 in 501u64..=1_000u64,
    ) {
        let a = ClosePriority {
            certified_liq_deficit: deficit,
            total_abs_risk_notional: notional,
            drift_reference_slot: drift_slot,
            close_id: cid1,
        };
        let b = ClosePriority {
            certified_liq_deficit: deficit,
            total_abs_risk_notional: notional,
            drift_reference_slot: drift_slot,
            close_id: cid2,
        };
        // cid1 < cid2 so a < b lexicographically.
        prop_assert!(a.lt(&b));
        prop_assert!(!b.lt(&a));
    }
}
