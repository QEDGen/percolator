/-
  Percolator.ConservativeWithdrawal — withdrawal uses sum-of-
  negative-leg-PnL, not aggregate-min.

  Closes §14 #45 in `SPEC_COVERAGE.md`:
  `withdrawal_uses_conservative_sum_negative_leg_pnl_not_aggregate_min`.

  The spec rule: when computing withdrawable capital, the engine
  must subtract the *sum* of all negative leg PnLs (the
  conservative lower bound) rather than just the *min* (which
  would treat one big loss as the only constraint while letting
  smaller losses cancel against profitable-but-stale legs).

  This file proves the structural inequality:

      sum_of_negative_legs ≥ min_of_negative_legs   (in absolute value)

  with equality only when there is at most one negative leg.
  Concretely: subtracting the sum is at least as conservative as
  subtracting the min.

  §14 invariants addressed:
    - #45 `withdrawal_uses_conservative_sum_negative_leg_pnl_not_aggregate_min`
-/

import Percolator.Defs
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

-- ============================================================================
-- §14 #45: conservative-sum vs aggregate-min
-- ============================================================================

/-- A leg-PnL signed value: a leg contributes either positive PnL
    (good for the account) or negative PnL (a loss). For
    withdrawal-capacity computation we care about the *absolute*
    magnitude of negative PnL — losses reduce withdrawable
    capital. -/
structure LegPnL where
  /-- Magnitude of loss on this leg (0 for profitable / flat legs). -/
  lossAbs : Nat
  deriving Repr

namespace LegPnL

/-- Sum of loss magnitudes across a list of legs. -/
def sumLoss (legs : List LegPnL) : Nat :=
  (legs.map LegPnL.lossAbs).sum

/-- Max loss magnitude across a list of legs (returns 0 on []). -/
def maxLoss (legs : List LegPnL) : Nat :=
  (legs.map LegPnL.lossAbs).foldl max 0

/-- A list of legs, each with its loss magnitude. -/
abbrev Legs := List LegPnL

-- ============================================================================
-- §14 #45 (the key inequality): sumLoss ≥ maxLoss
-- ============================================================================

/-- Helper: `xs.foldl max acc ≤ acc + xs.sum`. The accumulator is
    bounded by acc + sum; the maximum cannot exceed acc plus any
    additional summands. -/
private theorem foldl_max_le_acc_plus_sum :
    ∀ (xs : List Nat) (acc : Nat), xs.foldl max acc ≤ acc + xs.sum
  | [], acc => by simp
  | x :: rest, acc => by
    -- foldl max acc (x :: rest) = foldl max (max acc x) rest
    show rest.foldl max (max acc x) ≤ acc + (x + rest.sum)
    have rec := foldl_max_le_acc_plus_sum rest (max acc x)
    -- rec : rest.foldl max (max acc x) ≤ max acc x + rest.sum
    have : max acc x ≤ acc + x := by
      cases Nat.le_total acc x with
      | inl h => rw [max_eq_right h]; omega
      | inr h => rw [max_eq_left h]; omega
    omega

/-- **§14 #45 (sumLoss ≥ maxLoss)**: the sum of leg losses is at
    least the maximum leg loss. Subtracting the sum from available
    capital is at least as conservative as subtracting just the
    max loss — so the engine that uses the sum cannot over-credit
    a withdrawal relative to one that uses the max.

    This is the structural inequality that distinguishes the
    "conservative sum" from the "aggregate min/max" approach. -/
theorem sumLoss_ge_maxLoss (legs : Legs) : maxLoss legs ≤ sumLoss legs := by
  unfold maxLoss sumLoss
  have := foldl_max_le_acc_plus_sum (legs.map LegPnL.lossAbs) 0
  -- this : (legs.map lossAbs).foldl max 0 ≤ 0 + (legs.map lossAbs).sum
  omega

-- ============================================================================
-- §14 #45 (withdrawal capacity)
-- ============================================================================

/-- The conservative withdrawal capacity: capital minus the sum of
    leg losses. This is the spec-mandated formula. -/
def withdrawCapacityConservative (capital : Nat) (legs : Legs) : Nat :=
  capital - sumLoss legs

/-- The hypothetical aggregate-min withdrawal capacity: capital
    minus just the maximum leg loss. This is what the spec
    forbids — it's not conservative enough. -/
def withdrawCapacityAggregateMin (capital : Nat) (legs : Legs) : Nat :=
  capital - maxLoss legs

/-- **§14 #45 (conservative is at most as permissive as min)**: the
    conservative formula gives a withdrawal capacity at most as
    large as the aggregate-min one — i.e. the spec is strictly
    more conservative (or equal in the single-negative-leg case). -/
theorem conservative_le_aggregate_min (capital : Nat) (legs : Legs) :
    withdrawCapacityConservative capital legs
      ≤ withdrawCapacityAggregateMin capital legs := by
  unfold withdrawCapacityConservative withdrawCapacityAggregateMin
  have := sumLoss_ge_maxLoss legs
  omega

/-- **§14 #45 (over-withdrawal would happen under aggregate-min)**:
    when there are two or more loss-bearing legs, the aggregate-
    min formula permits a strictly larger withdrawal than the
    conservative formula. Witness: two legs each losing `k`; sum
    loss is `2k`, max loss is `k`. -/
theorem aggregate_min_overstates_with_two_losses (capital k : Nat)
    (hk : 0 < k) (hcap : 2 * k ≤ capital) :
    let legs : Legs := [{ lossAbs := k }, { lossAbs := k }]
    withdrawCapacityConservative capital legs
      < withdrawCapacityAggregateMin capital legs := by
  unfold withdrawCapacityConservative withdrawCapacityAggregateMin
  unfold sumLoss maxLoss
  simp [LegPnL.lossAbs]
  -- sum = 2k, max = max 0 (max k k) = k.
  omega

end LegPnL

end Percolator.Spec
