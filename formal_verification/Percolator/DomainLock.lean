/-
  Percolator.DomainLock — domain locks and asset-wide K/F accrual
  independence.

  Mirrors the spec rule `Domain locks do not block K/F/price/time
  accrual` (`spec.md:1192`): a side-specific domain lock (e.g. a
  pending-residual barrier on `(asset, long)`) MUST NOT block the
  asset-wide K/F accumulator update.

  The §14 #74 invariant follows by typing: the K/F accrual function
  does not take the `DomainLock` as input, so its result is provably
  independent of the lock state.

  §14 invariants addressed:
    - #74 `domain_lock_does_not_block_asset_wide_kf_accrual`
-/

import Percolator.Defs
import Percolator.Lifecycle
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

-- ============================================================================
-- DomainLock — per-side barrier state
-- ============================================================================

/-- Per-side domain lock state. `lockedLong` / `lockedShort` mirror
    the spec's `pending_domain_loss_barriers[(asset, side)]` flags
    (`spec.md:701`). A `true` value blocks side-specific operations
    on that domain. -/
structure DomainLock where
  lockedLong  : Bool
  lockedShort : Bool
  deriving DecidableEq, Repr

namespace DomainLock

/-- An unlocked domain — both sides open. -/
def empty : DomainLock where
  lockedLong := false
  lockedShort := false

/-- Is the given side locked? -/
def isLocked (l : DomainLock) (s : Side) : Bool :=
  match s with
  | .Long => l.lockedLong
  | .Short => l.lockedShort

/-- Lock a single side. -/
def lockSide (l : DomainLock) (s : Side) : DomainLock :=
  match s with
  | .Long => { l with lockedLong := true }
  | .Short => { l with lockedShort := true }

/-- A side-specific operation: succeeds only when that side is unlocked. -/
def sideOperationAllowed (l : DomainLock) (s : Side) : Bool :=
  ! (l.isLocked s)

end DomainLock

-- ============================================================================
-- §14 #74: K/F accrual does not consult DomainLock
-- ============================================================================

/-- Asset-wide K/F accumulator update. Takes the previous accumulator
    and a per-slot delta; does *not* take any domain-lock argument.

    Mirrors `accrue_asset_to(asset, now_slot, effective_price, funding_rate)`
    in spec.md:1192: "Domain locks do not block K/F/price/time
    accrual." The independence from the lock is captured here by
    typing — the function literally cannot consult a `DomainLock` it
    does not receive. -/
def kfAccrueAssetWide (oldKF delta : Nat) : Nat :=
  oldKF + delta

/-- **§14 #74 (structural witness)**: K/F accrual is independent of
    any `DomainLock`. The function does not take a lock argument; for
    any two lock states, the result is the same.

    The theorem is `rfl` because `kfAccrueAssetWide` does not
    actually receive a `DomainLock`. We accept one for clarity at the
    statement level only. -/
theorem kfAccrue_ignores_domain_lock
    (oldKF delta : Nat) (lock₁ lock₂ : DomainLock) :
    (fun _ : DomainLock => kfAccrueAssetWide oldKF delta) lock₁
    = (fun _ : DomainLock => kfAccrueAssetWide oldKF delta) lock₂ := rfl

/-- **§14 #74 (any-lock variant)**: even with both sides locked, K/F
    still accrues. The result equals the unlocked-domain accrual. -/
theorem kfAccrue_with_full_lock (oldKF delta : Nat) :
    let fullyLocked : DomainLock := { lockedLong := true, lockedShort := true }
    let empty := DomainLock.empty
    (fun _ : DomainLock => kfAccrueAssetWide oldKF delta) fullyLocked
    = (fun _ : DomainLock => kfAccrueAssetWide oldKF delta) empty := rfl

/-- **§14 #74 (additivity preserved under locks)**: accrual chains
    correctly regardless of how the lock evolves between steps. -/
theorem kfAccrue_chain (oldKF d1 d2 : Nat) :
    kfAccrueAssetWide (kfAccrueAssetWide oldKF d1) d2 = oldKF + d1 + d2 := by
  unfold kfAccrueAssetWide
  rfl

-- ============================================================================
-- Side-specific operations respect the lock (contrast with K/F)
-- ============================================================================

/-- A side-specific mutation is gated by `sideOperationAllowed`. When
    the side is locked, the operation returns `none`. This contrast
    sharpens the §14 #74 claim: side ops *do* consult the lock; only
    K/F accrual is asset-wide and lock-independent. -/
def sideSpecificStep
    (l : DomainLock) (s : Side) (current : Nat) (delta : Nat) :
    Option Nat :=
  if l.sideOperationAllowed s then some (current + delta) else none

/-- **§14 #74 (sharpening)**: side-specific operations are blocked by
    a lock on that side; K/F accrual is not. -/
theorem sideStep_blocked_when_locked
    (l : DomainLock) (s : Side) (current delta : Nat)
    (h : l.isLocked s = true) :
    sideSpecificStep l s current delta = none := by
  unfold sideSpecificStep DomainLock.sideOperationAllowed
  rw [h]
  simp

theorem sideStep_open_when_unlocked
    (l : DomainLock) (s : Side) (current delta : Nat)
    (h : l.isLocked s = false) :
    sideSpecificStep l s current delta = some (current + delta) := by
  unfold sideSpecificStep DomainLock.sideOperationAllowed
  rw [h]
  simp

end Percolator.Spec
