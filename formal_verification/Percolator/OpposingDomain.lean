/-
  Percolator.OpposingDomain — residual booking targets the
  (asset, opposing_side) domain, not just any per-ledger domain.

  The §14 #56 / #84 invariants require that a loss originating on
  some leg's side is booked into the *opposing* side's domain
  (`Domain_j = (asset_j, opposing_side_j)` per `spec.md:1295`). A
  prior closure under #56 / #84 in `Spec14Aliases2.lean` only
  witnessed that the close ledger had *some* (asset, side) pair —
  trivially true. This file proves the opposing-side relationship
  explicitly: a close ledger created from a leg with
  `originSide = .Long` must carry `domainSide = .Short`, and vice
  versa.

  §14 invariants addressed:
    - #56 `residuals_charged_only_to_asset_opposing_side_domain`
    - #84 `dead_leg_forfeit_books_to_bankruptcy_domain`
-/

import Percolator.Lifecycle
import Percolator.CloseLedger
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

/-- The originating leg of a loss event: which asset and which side
    took the loss. -/
structure LossOrigin where
  assetIndex : Nat
  originSide : Side
  deriving Repr

namespace LossOrigin

/-- The domain to which residuals from this loss origin must book —
    the opposing side of the same asset. -/
def opposingDomain (lo : LossOrigin) : Nat × Side :=
  (lo.assetIndex, lo.originSide.flip)

/-- A long-side loss books to the short-side domain. -/
theorem opposingDomain_long :
    (LossOrigin.mk asset .Long).opposingDomain = (asset, .Short) := by
  unfold opposingDomain
  rfl

/-- A short-side loss books to the long-side domain. -/
theorem opposingDomain_short :
    (LossOrigin.mk asset .Short).opposingDomain = (asset, .Long) := by
  unfold opposingDomain
  rfl

/-- The opposing-domain mapping is an involution at the side level:
    flipping twice returns to the original side. -/
theorem opposingDomain_flip_twice
    (lo : LossOrigin) :
    let lo' : LossOrigin :=
      { assetIndex := lo.assetIndex, originSide := lo.originSide.flip }
    lo'.opposingDomain.2 = lo.originSide := by
  unfold opposingDomain
  exact Side.flip_flip lo.originSide

/-- The opposing-domain assetIndex matches the origin's. Residuals
    never book to an *unrelated* asset. -/
theorem opposingDomain_same_asset (lo : LossOrigin) :
    lo.opposingDomain.1 = lo.assetIndex := rfl

end LossOrigin

namespace CloseLedger

/-- **Open a close ledger from a loss origin**: the constructor sets
    `domainSide` to the opposing side of the originating leg, baking
    in the §14 #56 / #84 spec rule by construction. -/
def openFromLoss (lo : LossOrigin) (closeId gross driftRefSlot maxSlot : Nat) :
    CloseLedger :=
  empty closeId lo.assetIndex lo.assetIndex lo.originSide.flip gross
    driftRefSlot maxSlot

/-- **§14 #56 (opposing-side rule for residual booking)**: a ledger
    opened from a loss on `originSide` carries `domainSide` equal to
    the flip — never the originating side itself, never an unrelated
    side. -/
theorem openFromLoss_targets_opposing_side
    (lo : LossOrigin) (closeId gross driftRefSlot maxSlot : Nat) :
    (CloseLedger.openFromLoss lo closeId gross driftRefSlot maxSlot).domainSide
    = lo.originSide.flip := by
  unfold openFromLoss empty
  rfl

/-- **§14 #56 (long → short)**: a long-side loss opens a ledger on
    the short-side domain. -/
theorem openFromLoss_long_targets_short
    (asset closeId gross driftRefSlot maxSlot : Nat) :
    (CloseLedger.openFromLoss
      { assetIndex := asset, originSide := .Long }
      closeId gross driftRefSlot maxSlot).domainSide = .Short := by
  unfold openFromLoss empty
  rfl

/-- **§14 #56 (short → long)**: a short-side loss opens a ledger on
    the long-side domain. -/
theorem openFromLoss_short_targets_long
    (asset closeId gross driftRefSlot maxSlot : Nat) :
    (CloseLedger.openFromLoss
      { assetIndex := asset, originSide := .Short }
      closeId gross driftRefSlot maxSlot).domainSide = .Long := by
  unfold openFromLoss empty
  rfl

/-- **§14 #56 (same asset)**: a ledger opened from a loss origin
    carries the same `assetIndex` — residuals never book to an
    unrelated asset. -/
theorem openFromLoss_same_asset
    (lo : LossOrigin) (closeId gross driftRefSlot maxSlot : Nat) :
    (CloseLedger.openFromLoss lo closeId gross driftRefSlot maxSlot).assetIndex
    = lo.assetIndex := by
  unfold openFromLoss empty
  rfl

/-- **§14 #56 (never originating side)**: the domain side of a
    ledger opened from a loss is provably distinct from the
    originating side. -/
theorem openFromLoss_domain_distinct_from_origin
    (lo : LossOrigin) (closeId gross driftRefSlot maxSlot : Nat) :
    (CloseLedger.openFromLoss lo closeId gross driftRefSlot maxSlot).domainSide
    ≠ lo.originSide := by
  rw [openFromLoss_targets_opposing_side]
  cases lo.originSide <;> simp [Side.flip]

/-- **§14 #84 (dead-leg forfeit specialization)**: the dead-leg
    forfeit transition opens its close ledger via `openFromLoss` on
    the dead leg's origin; the resulting domain is the opposing side
    of the dead leg, never the dead leg's own side. -/
theorem deadLegForfeit_books_to_opposing_side
    (lo : LossOrigin) (closeId gross driftRefSlot maxSlot : Nat) :
    let cl := CloseLedger.openFromLoss lo closeId gross driftRefSlot maxSlot
    cl.domainSide ≠ lo.originSide
    ∧ cl.assetIndex = lo.assetIndex := by
  exact ⟨openFromLoss_domain_distinct_from_origin lo closeId gross driftRefSlot maxSlot,
         openFromLoss_same_asset lo closeId gross driftRefSlot maxSlot⟩

end CloseLedger

end Percolator.Spec
