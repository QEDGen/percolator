/-
  Percolator.HLock — Phase 3 port of `h_lock_lane` / `select_h_lock`.

  The h-lock lane chooses between two configured horizons (`hMin` and
  `hMax`) based on a fixed set of "force conservative" flags. This is a
  pure, flag-driven decision — no arithmetic, no state mutation.

  Mirror of `v16.rs::MarketGroupV16::h_lock_lane` (line 5058) and
  `select_h_lock` (line 5088).

  The Rust function reads several runtime flags off the `MarketGroupV16`
  and the (optional) `PortfolioAccountV16`. In Lean we abstract those
  as fields on a small `HLockContext` / `AccountHLockFlags` record, so
  the proof is over the logical content of the predicate rather than
  the in-tree struct layout.

  §14 items this contributes to: this is the prerequisite "small win"
  before tackling the harder pure-function ports. Demonstrates the
  Lean-spec ↔ Rust-impl pattern at minimum complexity.
-/

import Percolator.Lifecycle

namespace Percolator.Spec

-- ============================================================================
-- HLockContext — the market-group-side flags consumed by h_lock_lane
-- ============================================================================

/-- Market-group-wide flags read by `h_lock_lane`.

    Lifted from the in-line reads at `v16.rs:5076-5081`:
      - `self.threshold_stress_active`
      - `self.bankruptcy_hlock_active`
      - `self.mode == Recovery`  (encoded as MarketMode in the context)
      - `self.loss_stale_active`
    plus the per-call `instruction_bankruptcy_candidate` flag (a fifth
    way to force the conservative lane). -/
structure HLockContext where
  thresholdStressActive : Bool
  bankruptcyHLockActive : Bool
  mode                  : MarketMode
  lossStaleActive       : Bool
  deriving Repr

-- ============================================================================
-- AccountHLockFlags — the account-side flags consumed by h_lock_lane
-- ============================================================================

/-- Per-account flags read by `h_lock_lane` when an account is supplied.

    Lifted from `v16.rs:5063-5073`:
      - `account.stale_state`
      - `account.b_stale_state`
      - `account.close_progress.has_pending_residual()`
      - `self.account_touches_pending_domain_loss_barrier(account)`
    All four force `HMax`. -/
structure AccountHLockFlags where
  staleState                     : Bool
  bStaleState                    : Bool
  hasPendingResidual             : Bool
  touchesPendingDomainLossBarrier : Bool
  deriving Repr

namespace AccountHLockFlags

/-- Disjunction over the four account-side force-conservative flags. -/
def forcesHMax (a : AccountHLockFlags) : Bool :=
  a.staleState || a.bStaleState
  || a.hasPendingResidual
  || a.touchesPendingDomainLossBarrier

end AccountHLockFlags

namespace HLockContext

/-- Whether the mode is Recovery (Bool form). -/
def isRecovery (ctx : HLockContext) : Bool :=
  match ctx.mode with
  | .Recovery => true
  | _         => false

/-- Disjunction over the four market-group-side force-conservative flags
    plus the per-call instruction-bankruptcy flag. -/
def forcesHMax (ctx : HLockContext) (instructionBankruptcyCandidate : Bool) : Bool :=
  ctx.thresholdStressActive
  || ctx.bankruptcyHLockActive
  || ctx.isRecovery
  || instructionBankruptcyCandidate
  || ctx.lossStaleActive

end HLockContext

-- ============================================================================
-- h_lock_lane — pure decision function
-- ============================================================================

/-- Pulled out as a named function for proof-friendliness. -/
def accountForcesOf : Option AccountHLockFlags → Bool
  | none   => false
  | some a => a.forcesHMax

/-- Lean spec mirror of `v16.rs::MarketGroupV16::h_lock_lane`.

    Returns `HMax` if any of the nine force-conservative flags is true
    (four account-side + four group-side + the per-call bankruptcy
    candidate), otherwise `HMin`. -/
def hLockLane
    (ctx : HLockContext)
    (account : Option AccountHLockFlags)
    (instructionBankruptcyCandidate : Bool) : HLockLane :=
  if accountForcesOf account || ctx.forcesHMax instructionBankruptcyCandidate
  then .HMax
  else .HMin

-- ============================================================================
-- select_h_lock — wrapper that materializes the chosen horizon
-- ============================================================================

/-- Lean spec mirror of `v16.rs::MarketGroupV16::select_h_lock`.

    Maps `hLockLane`'s `HMin`/`HMax` choice to the configured `hMin` or
    `hMax` value. Pure — no state, no arithmetic. -/
def selectHLock
    (ctx : HLockContext) (hMin hMax : Nat)
    (account : Option AccountHLockFlags)
    (instructionBankruptcyCandidate : Bool) : Nat :=
  match hLockLane ctx account instructionBankruptcyCandidate with
  | .HMin => hMin
  | .HMax => hMax

-- ============================================================================
-- Correctness theorems
-- ============================================================================

/-- **HMax iff any force flag set**. The "→" direction is the
    conservatism guarantee: every force-conservative flag *actually*
    forces `HMax`. The "←" direction is the no-spurious-HMax
    guarantee. -/
theorem hLockLane_eq_HMax_iff
    (ctx : HLockContext)
    (account : Option AccountHLockFlags)
    (ibc : Bool) :
    hLockLane ctx account ibc = .HMax
    ↔ (accountForcesOf account || ctx.forcesHMax ibc) = true := by
  unfold hLockLane
  cases h : accountForcesOf account || ctx.forcesHMax ibc
  · -- false branch: hLockLane = HMin ≠ HMax; RHS false
    simp [h]
  · -- true branch: hLockLane = HMax; RHS true
    simp [h]

/-- **HMin iff no force flag set**. -/
theorem hLockLane_eq_HMin_iff
    (ctx : HLockContext)
    (account : Option AccountHLockFlags)
    (ibc : Bool) :
    hLockLane ctx account ibc = .HMin
    ↔ (accountForcesOf account || ctx.forcesHMax ibc) = false := by
  unfold hLockLane
  cases h : accountForcesOf account || ctx.forcesHMax ibc
  · simp [h]
  · simp [h]

/-- **`selectHLock` is `hMin` or `hMax`**: the output is always one of
    the configured horizons; no other value is possible. -/
theorem selectHLock_eq_hMin_or_hMax
    (ctx : HLockContext) (hMin hMax : Nat)
    (account : Option AccountHLockFlags) (ibc : Bool) :
    selectHLock ctx hMin hMax account ibc = hMin
    ∨ selectHLock ctx hMin hMax account ibc = hMax := by
  unfold selectHLock
  cases hLockLane ctx account ibc
  · left; rfl
  · right; rfl

/-- **`selectHLock` matches the lane**: returns `hMin` exactly when the
    lane is `HMin`, `hMax` exactly when the lane is `HMax`. -/
theorem selectHLock_eq_hMax_iff_lane_HMax
    (ctx : HLockContext) (hMin hMax : Nat)
    (account : Option AccountHLockFlags) (ibc : Bool)
    (hne : hMin ≠ hMax) :
    selectHLock ctx hMin hMax account ibc = hMax
    ↔ hLockLane ctx account ibc = .HMax := by
  unfold selectHLock
  cases h : hLockLane ctx account ibc
  · simp [h]; intro heq; exact hne heq
  · simp [h]

/-- **No-account, no-flags case**: with no account and all group-side
    flags false, the lane is `HMin`. Sanity check on the default path. -/
theorem hLockLane_default_HMin
    (ctx : HLockContext)
    (h_threshold : ctx.thresholdStressActive = false)
    (h_bankruptcy : ctx.bankruptcyHLockActive = false)
    (h_mode : ctx.mode ≠ .Recovery)
    (h_loss : ctx.lossStaleActive = false) :
    hLockLane ctx none false = .HMin := by
  unfold hLockLane
  have h_acc : accountForcesOf none = false := rfl
  have h_rec : ctx.isRecovery = false := by
    unfold HLockContext.isRecovery
    cases hm : ctx.mode
    · rfl
    · rfl
    · exfalso; rw [hm] at h_mode; exact h_mode rfl
  have h_grp : ctx.forcesHMax false = false := by
    unfold HLockContext.forcesHMax
    rw [h_threshold, h_bankruptcy, h_rec, h_loss]
    rfl
  rw [h_acc, h_grp]
  rfl

end Percolator.Spec
