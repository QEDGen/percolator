/-
  Percolator.SoftCredit — soft maintenance credit formula with
  locked-face-claim exclusion.

  Mirrors the spec rule "open positive PnL may support health, but it
  MUST NOT cure a bankruptcy residual unless a source-domain backing
  lien is consumed and the supporting face claim is locked/burned"
  (`spec.md:48`). The arithmetic claim is that *locked* face claim
  (already encumbered by a lien) cannot contribute again to soft
  maintenance credit.

  §14 invariants addressed:
    - #44 `locked_face_claim_excluded_from_soft_credit`
-/

import Percolator.Defs
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

/-- The soft-credit formula: total face claim minus locked face claim.

    `faceClaim` is the gross face-claim amount. `lockedFaceClaim` is
    the portion already locked by an active source-credit lien.
    Soft maintenance credit may use only the unlocked residue.

    When `lockedFaceClaim > faceClaim` (degenerate; shouldn't occur
    given downstream invariants but typed at `Nat`), returns `0`. -/
def softCredit (faceClaim lockedFaceClaim : Nat) : Nat :=
  faceClaim - lockedFaceClaim

/-- **§14 #44 (exclusion identity)**: when `lockedFaceClaim ≤ faceClaim`
    — i.e. the lock budget is well-formed — soft credit plus locked
    face claim recovers the gross face claim. No double-counting:
    the locked portion is not also available as soft credit. -/
theorem softCredit_plus_locked_eq_face
    (faceClaim lockedFaceClaim : Nat) (h : lockedFaceClaim ≤ faceClaim) :
    softCredit faceClaim lockedFaceClaim + lockedFaceClaim = faceClaim := by
  unfold softCredit
  omega

/-- **§14 #44 (boundedness)**: soft credit never exceeds gross face
    claim. -/
theorem softCredit_le_faceClaim (faceClaim lockedFaceClaim : Nat) :
    softCredit faceClaim lockedFaceClaim ≤ faceClaim := by
  unfold softCredit
  exact Nat.sub_le _ _

/-- **§14 #44 (locked-only saturation)**: when *all* face claim is
    locked, soft credit is zero. -/
theorem softCredit_zero_when_fully_locked
    (faceClaim : Nat) :
    softCredit faceClaim faceClaim = 0 := by
  unfold softCredit
  simp

/-- **§14 #44 (anti-monotone in lock)**: a larger lock leaves at most
    the same soft credit. -/
theorem softCredit_anti_in_locked
    (faceClaim lock₁ lock₂ : Nat) (h : lock₁ ≤ lock₂) :
    softCredit faceClaim lock₂ ≤ softCredit faceClaim lock₁ := by
  unfold softCredit
  exact Nat.sub_le_sub_left h _

/-- **§14 #44 (zero-lock degenerate)**: with no lock, soft credit
    equals the gross face claim. -/
theorem softCredit_zero_lock (faceClaim : Nat) :
    softCredit faceClaim 0 = faceClaim := by
  unfold softCredit
  simp

/-- **§14 #44 (no double-count witness)**: a "double-count" attempt
    would compute `softCredit + lockedFaceClaim > faceClaim`, but the
    arithmetic forbids this — when the lock is well-formed, the sum
    equals exactly `faceClaim`; when not, soft credit is zero and the
    sum equals `lockedFaceClaim`. Either way, the sum never exceeds
    `max faceClaim lockedFaceClaim`. -/
theorem softCredit_plus_locked_bounded
    (faceClaim lockedFaceClaim : Nat) :
    softCredit faceClaim lockedFaceClaim + lockedFaceClaim
    ≤ max faceClaim lockedFaceClaim := by
  unfold softCredit
  by_cases h : lockedFaceClaim ≤ faceClaim
  · have : faceClaim - lockedFaceClaim + lockedFaceClaim = faceClaim := by omega
    rw [this]
    exact Nat.le_max_left _ _
  · push_neg at h
    have hzero : faceClaim - lockedFaceClaim = 0 := by omega
    rw [hzero, Nat.zero_add]
    exact Nat.le_max_right _ _

end Percolator.Spec
