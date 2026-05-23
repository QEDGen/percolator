/-
  Percolator.HedgeEnvelope — hedge credit reducing the maintenance
  requirement covers the combined-loss envelope.

  Mirrors the cross-margin hedge accounting in §§6-7 (`spec.md:1150`):
  for a hedge bucket of long + short positions on the same asset,
  the engine credits a hedge bonus equal to the smaller leg's absolute
  position size scaled by the price-deviation budget, reducing the
  maintenance requirement. The §14 #91 invariant is that the credit
  is bounded by the combined-loss envelope on the bucket.

  §14 invariants addressed:
    - #91 `hedge_credit_reduced_requirement_covers_combined_loss_envelope`
-/

import Percolator.Defs
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

/-- A hedge bucket of paired long and short positions on the same
    asset, plus the combined-loss envelope cap that the hedge credit
    cannot exceed.

    `longAbs` / `shortAbs` — absolute position size on each side.
    `envelopeCap` — the engine-computed combined-loss envelope for
    this hedge bucket (price + funding + liquidation-fee budget).
    Per the spec, this is the upper bound on the hedge credit. -/
structure HedgeBucket where
  longAbs     : Nat
  shortAbs    : Nat
  envelopeCap : Nat
  deriving Repr

namespace HedgeBucket

/-- The hedged portion = min(longAbs, shortAbs). The off-setting
    leg cancels out exactly this much exposure. -/
def hedgedSize (h : HedgeBucket) : Nat :=
  min h.longAbs h.shortAbs

/-- The hedge credit applied to the maintenance requirement. Per
    spec: the credit is at most the envelope cap, and never exceeds
    the hedged size. We model it as the minimum of the two. -/
def hedgeCredit (h : HedgeBucket) : Nat :=
  min h.hedgedSize h.envelopeCap

/-- **§14 #91 (credit is bounded by envelope)**: the hedge credit
    never exceeds the engine-computed combined-loss envelope cap. -/
theorem hedgeCredit_le_envelope (h : HedgeBucket) :
    h.hedgeCredit ≤ h.envelopeCap := by
  unfold hedgeCredit
  exact Nat.min_le_right _ _

/-- **§14 #91 (credit is bounded by hedged size)**: the hedge
    credit never exceeds the smaller leg's absolute position size.
    This is the structural bound that prevents over-crediting. -/
theorem hedgeCredit_le_hedgedSize (h : HedgeBucket) :
    h.hedgeCredit ≤ h.hedgedSize := by
  unfold hedgeCredit
  exact Nat.min_le_left _ _

/-- **§14 #91 (zero-leg degenerate)**: with no position on one side,
    the hedged size is zero and so is the credit. -/
theorem hedgeCredit_zero_when_no_short (h : HedgeBucket)
    (hs : h.shortAbs = 0) : h.hedgeCredit = 0 := by
  unfold hedgeCredit hedgedSize
  rw [hs]
  simp

theorem hedgeCredit_zero_when_no_long (h : HedgeBucket)
    (hl : h.longAbs = 0) : h.hedgeCredit = 0 := by
  unfold hedgeCredit hedgedSize
  rw [hl]
  simp

/-- **§14 #91 (envelope cap = 0 zeros the credit)**: a zero
    envelope cap forces zero hedge credit. -/
theorem hedgeCredit_zero_when_no_envelope (h : HedgeBucket)
    (he : h.envelopeCap = 0) : h.hedgeCredit = 0 := by
  unfold hedgeCredit
  rw [he]
  simp

/-- The maintenance requirement after hedge credit. -/
def reducedRequirement (h : HedgeBucket) (rawRequirement : Nat) : Nat :=
  rawRequirement - h.hedgeCredit

/-- **§14 #91 (reduction bounded by combined-loss envelope)**: the
    reduction in the maintenance requirement is at most the
    envelope cap. -/
theorem reducedRequirement_above_envelope
    (h : HedgeBucket) (rawRequirement : Nat)
    (hle : h.envelopeCap ≤ rawRequirement) :
    rawRequirement - h.envelopeCap ≤ h.reducedRequirement rawRequirement := by
  unfold reducedRequirement
  have := h.hedgeCredit_le_envelope
  omega

/-- **§14 #91 (monotonicity in raw requirement)**: a larger raw
    requirement produces a larger reduced requirement, holding the
    bucket fixed. -/
theorem reducedRequirement_mono
    (h : HedgeBucket) (r1 r2 : Nat) (hr : r1 ≤ r2) :
    h.reducedRequirement r1 ≤ h.reducedRequirement r2 := by
  unfold reducedRequirement
  exact Nat.sub_le_sub_right hr _

/-- **§14 #91 (no over-credit)**: a hedge credit of zero leaves the
    requirement unchanged. -/
theorem reducedRequirement_zero_credit
    (h : HedgeBucket) (rawRequirement : Nat) (h0 : h.hedgeCredit = 0) :
    h.reducedRequirement rawRequirement = rawRequirement := by
  unfold reducedRequirement
  rw [h0]
  simp

end HedgeBucket

end Percolator.Spec
