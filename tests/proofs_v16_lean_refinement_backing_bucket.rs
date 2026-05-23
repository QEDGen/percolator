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
