/-
  Percolator.ZeroWeightClear — zero-weight domain residual cannot
  clear without backing.

  Mirrors the spec rule in §10 (`spec.md:1220`):
    "If W == 0, residual clears only by reserved insurance or
     explicit protocol-owned backing preserving senior invariants;
     otherwise route to recovery."

  When the loss-weight sum on a side is zero, ordinary B-booking
  cannot make progress (the chunk denominator W is zero). The only
  permitted clearing paths are insurance or explicit backed loss —
  both of which are tracked in distinct `CloseLedger` counters.

  §14 invariants addressed:
    - #76 `zero_weight_domain_residual_cannot_clear_without_backing`
-/

import Percolator.CloseLedger
import Percolator.BBookingExact
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

namespace CloseLedger

/-- A clearing action available under zero-weight: only insurance
    spend or explicit backed loss are permitted. B booking is
    excluded by construction. -/
inductive ZeroWeightClearance : Type where
  | insurance       (amount : Nat) : ZeroWeightClearance
  | explicitBacked  (amount : Nat) : ZeroWeightClearance
  deriving DecidableEq, Repr

namespace ZeroWeightClearance

/-- The clearing amount carried by an action. -/
def amount : ZeroWeightClearance → Nat
  | .insurance a => a
  | .explicitBacked a => a

/-- Apply the clearance to a close ledger via the appropriate booking
    transition. Both branches preserve `closeId`/anchors and reduce
    residual; both are backed (insurance or protocol-owned) per spec. -/
def apply (l : CloseLedger) : ZeroWeightClearance → Option CloseLedger
  | .insurance a => l.bookInsurance a
  | .explicitBacked a => l.bookExplicit a

end ZeroWeightClearance

/-- **§14 #76 (no B-booking path)**: a zero-weight side has
    `loss_weight_sum_side = 0`, which is the `W` parameter of
    `bBookingStep`. When `W = 0`, the booking formula has no defined
    output — captured here by `bBookingStep` requiring `0 < W` in
    every conservation theorem (`bBookingStep_exact_conservation`,
    `bBookingStep_remainder_lt_W`).

    A clearing action must therefore avoid B-booking; only the two
    `ZeroWeightClearance` constructors are permitted. -/
theorem bBookingStep_undefined_at_zero_weight
    (engineChunk R : Nat) :
    ¬ (∃ deltaB newR : Nat, deltaB * 0 + newR = engineChunk * SOCIAL_LOSS_DEN + R
       ∧ newR < 0) := by
  rintro ⟨_, _, _, hlt⟩
  exact Nat.not_lt_zero _ hlt

/-- **§14 #76 (insurance clearance is backed)**: applying an
    insurance clearance increments `insuranceSpent` by exactly the
    amount, which is sourced from reserved insurance capacity. -/
theorem ZeroWeightClearance.insurance_amount_books_insuranceSpent
    (l l' : CloseLedger) (amount : Nat)
    (h : (ZeroWeightClearance.insurance amount).apply l = some l') :
    l'.insuranceSpent = l.insuranceSpent + amount := by
  unfold ZeroWeightClearance.apply at h
  unfold bookInsurance at h
  by_cases ha : !l.active || l.finalized || l.canceled
  · simp [ha] at h
  by_cases hr : l.residualRemaining < amount
  · simp [ha, hr] at h
  · simp [ha, hr] at h
    have hl' := h.symm
    rw [hl']

/-- **§14 #76 (explicit clearance is backed)**: applying an
    explicit-backed clearance increments `explicitLossAssigned` by
    exactly the amount, which the spec requires be backed by
    protocol-owned capital. -/
theorem ZeroWeightClearance.explicit_amount_books_explicitLoss
    (l l' : CloseLedger) (amount : Nat)
    (h : (ZeroWeightClearance.explicitBacked amount).apply l = some l') :
    l'.explicitLossAssigned = l.explicitLossAssigned + amount := by
  unfold ZeroWeightClearance.apply at h
  unfold bookExplicit at h
  by_cases ha : !l.active || l.finalized || l.canceled
  · simp [ha] at h
  by_cases hr : l.residualRemaining < amount
  · simp [ha, hr] at h
  · simp [ha, hr] at h
    have hl' := h.symm
    rw [hl']

/-- **§14 #76 (no `bookB` constructor)**: the `ZeroWeightClearance`
    sum type does not include a B-booking variant. The structural
    typing forbids using `bookB` as a clearing path under
    zero-weight. -/
theorem ZeroWeightClearance.classification (z : ZeroWeightClearance) :
    (∃ a : Nat, z = .insurance a) ∨ (∃ a : Nat, z = .explicitBacked a) := by
  cases z with
  | insurance a => exact .inl ⟨a, rfl⟩
  | explicitBacked a => exact .inr ⟨a, rfl⟩

/-- **§14 #76 (residual strictly decreases)**: each permitted
    clearance strictly decreases residual when the amount is
    positive. -/
theorem ZeroWeightClearance.apply_decreases_residual
    (l l' : CloseLedger) (z : ZeroWeightClearance) (hpos : 0 < z.amount)
    (h : z.apply l = some l') :
    l'.residualRemaining < l.residualRemaining := by
  cases z with
  | insurance a =>
    unfold ZeroWeightClearance.apply at h
    unfold ZeroWeightClearance.amount at hpos
    exact CloseLedger.bookInsurance_decreases_residual l l' a h hpos
  | explicitBacked a =>
    unfold ZeroWeightClearance.apply at h
    unfold ZeroWeightClearance.amount at hpos
    exact CloseLedger.bookExplicit_decreases_residual l l' a h hpos

end CloseLedger

end Percolator.Spec
