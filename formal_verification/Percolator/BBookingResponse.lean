/-
  Percolator.BBookingResponse — B-booking triggers source-claim-
  bound and credit-rate recompute OR conservative lowering.

  Closes §14 #94 in `SPEC_COVERAGE.md`:
  `B_booking_triggers_source_claim_bound_and_credit_rate_recompute_or_conservative_lowering`.

  The spec rule: after a successful B-booking step, the engine
  must either (a) recompute the source-claim bound and credit
  rate based on the new state, or (b) conservatively *lower* the
  cached bound/rate. The cached values cannot drift upward
  silently.

  This file makes the dichotomy structural via a closed-sum
  `BBookingResponse`:

    - `recomputed` — bound and rate refreshed from current state.
    - `conservativelyLowered` — cached values reduced (never
      raised) to maintain the upper-bound invariant.

  The structural witness is exhaustiveness on the closed sum: no
  third path that could let the cache drift upward.

  §14 invariants addressed:
    - #94 `B_booking_triggers_source_claim_bound_and_credit_rate_recompute_or_conservative_lowering`
-/

import Percolator.Defs
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

-- ============================================================================
-- §14 #94: B-booking response dichotomy
-- ============================================================================

/-- The source-side cached values that B-booking interacts with. -/
structure SourceClaimCache where
  claimBoundNum   : Nat
  creditRateNum   : Nat
  deriving Repr

namespace SourceClaimCache

def empty : SourceClaimCache where
  claimBoundNum := 0
  creditRateNum := 0

end SourceClaimCache

/-- The dichotomous response of a B-booking step on the source
    cache. Closed sum — no third path. -/
inductive BBookingResponse : Type where
  /-- The bound and rate were freshly recomputed from the new state. -/
  | recomputed (cache : SourceClaimCache) : BBookingResponse
  /-- The cached values were conservatively lowered (≤ prior). -/
  | conservativelyLowered (cache : SourceClaimCache) : BBookingResponse
  deriving Repr

namespace BBookingResponse

/-- Extract the post-response cache. -/
def cache : BBookingResponse → SourceClaimCache
  | .recomputed c => c
  | .conservativelyLowered c => c

def isRecomputed : BBookingResponse → Bool
  | .recomputed _ => true
  | .conservativelyLowered _ => false

def isLowered : BBookingResponse → Bool
  | .recomputed _ => false
  | .conservativelyLowered _ => true

end BBookingResponse

/-- The B-booking step over the cache. Given the pre-step cache
    and a `recomputeFresh` flag indicating whether the engine
    chose to recompute from scratch, produce a `BBookingResponse`.
    The `recomputed` branch uses the supplied fresh values; the
    `conservativelyLowered` branch ensures the post values are at
    most the pre values. -/
def bBookingStepResponse
    (pre : SourceClaimCache) (recomputeFresh : Bool)
    (freshBound freshRate : Nat) : BBookingResponse :=
  if recomputeFresh then
    .recomputed { claimBoundNum := freshBound, creditRateNum := freshRate }
  else
    .conservativelyLowered {
      claimBoundNum := min pre.claimBoundNum freshBound
      creditRateNum := min pre.creditRateNum freshRate
    }

-- ============================================================================
-- §14 #94: Witness theorems
-- ============================================================================

namespace BBookingResponse

/-- **§14 #94 (closed-world dichotomy)**: every B-booking response
    is either `.recomputed` or `.conservativelyLowered`. The
    inductive's exhaustiveness rules out any third case. -/
theorem step_response_is_one_of_two
    (pre : SourceClaimCache) (b : Bool) (fb fr : Nat) :
    let r := bBookingStepResponse pre b fb fr
    r.isRecomputed = true ∨ r.isLowered = true := by
  unfold bBookingStepResponse
  by_cases h : b
  · simp [h, isRecomputed, isLowered]
  · simp [h, isRecomputed, isLowered]

/-- **§14 #94 (lowered branch never raises the cache)**: when the
    response is `conservativelyLowered`, the post-cache values
    are at most the pre-cache values. The cache cannot drift
    upward through this branch. -/
theorem lowered_never_raises_cache
    (pre : SourceClaimCache) (fb fr : Nat)
    (h : bBookingStepResponse pre false fb fr
         = .conservativelyLowered (bBookingStepResponse pre false fb fr).cache) :
    (bBookingStepResponse pre false fb fr).cache.claimBoundNum
      ≤ pre.claimBoundNum
    ∧ (bBookingStepResponse pre false fb fr).cache.creditRateNum
      ≤ pre.creditRateNum := by
  unfold bBookingStepResponse at *
  simp at *
  refine ⟨?_, ?_⟩
  · exact Nat.min_le_left _ _
  · exact Nat.min_le_left _ _

/-- **§14 #94 (recomputed branch uses fresh values)**: when the
    response is `recomputed`, the post-cache values come from the
    fresh inputs — they reflect the new state, not the stale
    cached values. -/
theorem recomputed_uses_fresh_values
    (pre : SourceClaimCache) (fb fr : Nat) :
    (bBookingStepResponse pre true fb fr).cache
    = { claimBoundNum := fb, creditRateNum := fr } := by
  unfold bBookingStepResponse cache
  simp

/-- **§14 #94 (no silent upward drift)**: regardless of branch,
    the credit rate is bounded above by the maximum of pre.rate
    and the fresh rate. There is no path where the cache silently
    exceeds both. -/
theorem no_silent_upward_drift
    (pre : SourceClaimCache) (b : Bool) (fb fr : Nat) :
    (bBookingStepResponse pre b fb fr).cache.creditRateNum
      ≤ max pre.creditRateNum fr := by
  unfold bBookingStepResponse cache
  by_cases h : b
  · simp [h]
  · simp [h]

end BBookingResponse

end Percolator.Spec
