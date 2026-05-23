/-
  Percolator.KFSettlement — K/F (settlement-quality) credit consumes
  backing AND locks face claim in one atomic transition.

  Mirrors the spec rule in §6 (K/F lanes) and §10 (close
  consumption): when settlement-quality credit fires, the engine
  MUST atomically decrement backing-reserved and increment
  face-claim-locked by the same amount. The §14 #53 invariant is
  the per-step atomicity: there is no transition that does one
  without the other.

  We model `KFSettlementState` and `kfSettlementStep`. The
  one-output structure of the function makes the atomicity
  structural — there is no way to apply only half the step.

  §14 invariants addressed:
    - #53 `settlement_quality_credit_consumes_backing_and_locks_face_claim`
-/

import Percolator.Defs
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

/-- The K/F settlement state of a single (account, source) pair:
    backing reserved against the source, and face claim currently
    locked by a settlement-quality credit. -/
structure KFSettlementState where
  backingReservedNum : Nat
  faceClaimLockedNum : Nat
  deriving Repr

namespace KFSettlementState

/-- The empty K/F state — no backing, no locked face. -/
def empty : KFSettlementState where
  backingReservedNum := 0
  faceClaimLockedNum := 0

/-- **The atomic K/F settlement step**: consume `settle` units of
    backing and lock `settle` units of face claim in one atomic
    update.

    Returns `none` when there is insufficient backing. The
    one-result-tuple form is the §14 #53 structural witness: the
    transition either applies both effects or neither. -/
def kfSettlementStep (s : KFSettlementState) (settle : Nat) :
    Option KFSettlementState :=
  if s.backingReservedNum < settle then none
  else some {
    backingReservedNum := s.backingReservedNum - settle
    faceClaimLockedNum := s.faceClaimLockedNum + settle
  }

/-- **§14 #53 (backing decrement)**: a successful step decrements
    backing by exactly `settle`. -/
theorem kfSettlementStep_consumes_backing
    (s s' : KFSettlementState) (settle : Nat)
    (h : s.kfSettlementStep settle = some s') :
    s'.backingReservedNum + settle = s.backingReservedNum := by
  unfold kfSettlementStep at h
  by_cases hlt : s.backingReservedNum < settle
  · simp [hlt] at h
  · push_neg at hlt
    simp [hlt] at h
    have hs' := h.symm
    rw [hs']
    change s.backingReservedNum - settle + settle = s.backingReservedNum
    omega

/-- **§14 #53 (face-claim lock)**: a successful step increments
    `faceClaimLockedNum` by exactly `settle`. -/
theorem kfSettlementStep_locks_face_claim
    (s s' : KFSettlementState) (settle : Nat)
    (h : s.kfSettlementStep settle = some s') :
    s'.faceClaimLockedNum = s.faceClaimLockedNum + settle := by
  unfold kfSettlementStep at h
  by_cases hlt : s.backingReservedNum < settle
  · simp [hlt] at h
  · push_neg at hlt
    simp [hlt] at h
    have hs' := h.symm
    rw [hs']

/-- **§14 #53 (atomic: both effects from the same call)**: the same
    transition that consumes backing locks the face claim — the
    `some` result carries both new field values, and there is no
    branch that updates only one. -/
theorem kfSettlementStep_atomic
    (s s' : KFSettlementState) (settle : Nat)
    (h : s.kfSettlementStep settle = some s') :
    s'.backingReservedNum + settle = s.backingReservedNum
    ∧ s'.faceClaimLockedNum = s.faceClaimLockedNum + settle :=
  ⟨kfSettlementStep_consumes_backing s s' settle h,
   kfSettlementStep_locks_face_claim s s' settle h⟩

/-- **§14 #53 (precondition)**: a successful step requires sufficient
    backing — settle ≤ backingReservedNum. -/
theorem kfSettlementStep_requires_backing
    (s s' : KFSettlementState) (settle : Nat)
    (h : s.kfSettlementStep settle = some s') :
    settle ≤ s.backingReservedNum := by
  unfold kfSettlementStep at h
  by_cases hlt : s.backingReservedNum < settle
  · simp [hlt] at h
  · push_neg at hlt
    exact hlt

/-- **§14 #53 (under-backed fails closed)**: when backing is
    insufficient, the transition returns `none` — neither effect is
    applied. -/
theorem kfSettlementStep_fails_closed_underBacked
    (s : KFSettlementState) (settle : Nat)
    (h : s.backingReservedNum < settle) :
    s.kfSettlementStep settle = none := by
  unfold kfSettlementStep
  simp [h]

/-- **§14 #53 (total transfer conservation)**: the sum of
    `backingReservedNum` and `faceClaimLockedNum` is preserved by
    the step — backing is converted into locked face claim, no atom
    is created or destroyed. -/
theorem kfSettlementStep_preserves_total
    (s s' : KFSettlementState) (settle : Nat)
    (h : s.kfSettlementStep settle = some s') :
    s'.backingReservedNum + s'.faceClaimLockedNum
    = s.backingReservedNum + s.faceClaimLockedNum := by
  have hb := kfSettlementStep_consumes_backing s s' settle h
  have hf := kfSettlementStep_locks_face_claim s s' settle h
  omega

end KFSettlementState

end Percolator.Spec
