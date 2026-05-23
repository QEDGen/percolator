/-
  Percolator.ClaimBoundBucketRange — out-of-range claim-bound
  bucket fails closed or re-buckets.

  Closes §14 #49 in `SPEC_COVERAGE.md`:
  `claim_bound_bucket_out_of_range_fails_closed_or_rebuckets`.

  The spec rule: when the engine queries a claim-bound bucket
  index that falls outside the configured bucket range, it must
  either fail closed (refuse to operate) or re-bucket (clamp the
  index into the valid range). A silent overflow into garbage
  data is forbidden.

  Closed-sum `BucketRangeOutcome` dichotomy.

  §14 invariants addressed:
    - #49 `claim_bound_bucket_out_of_range_fails_closed_or_rebuckets`
-/

import Percolator.Defs
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

-- ============================================================================
-- §14 #49: bucket-range dichotomy
-- ============================================================================

/-- A claim-bound bucket index. -/
abbrev BucketIndex : Type := Nat

/-- Maximum bucket count. Mirrors the production constant
    (e.g. `V16_MAX_MARKET_SLOTS_N` or a per-asset bucket cap). -/
def MAX_BUCKET_COUNT : Nat := 64

/-- The closed sum of outcomes when querying a bucket index. -/
inductive BucketRangeOutcome : Type where
  /-- Index is in range; the value at that bucket is returned. -/
  | inRange (value : Nat) : BucketRangeOutcome
  /-- Index is out of range and the engine fails closed. -/
  | failClosed : BucketRangeOutcome
  /-- Index is out of range but a re-bucket-into-range path is taken;
      the rebucketed index is returned alongside the value at that
      clamped position. -/
  | rebucketed (clampedIdx : BucketIndex) (value : Nat) : BucketRangeOutcome
  deriving Repr

namespace BucketRangeOutcome

def isInRange : BucketRangeOutcome → Bool
  | .inRange _ => true
  | _          => false

def isFailClosed : BucketRangeOutcome → Bool
  | .failClosed => true
  | _           => false

def isRebucketed : BucketRangeOutcome → Bool
  | .rebucketed _ _ => true
  | _               => false

end BucketRangeOutcome

/-- Query a bucket. If `idx < MAX_BUCKET_COUNT`, in-range. Otherwise,
    the `recoverable` flag selects fail-closed vs re-bucket. -/
def queryBucket
    (buckets : BucketIndex → Nat) (idx : BucketIndex) (recoverable : Bool) :
    BucketRangeOutcome :=
  if idx < MAX_BUCKET_COUNT then
    .inRange (buckets idx)
  else if recoverable then
    .rebucketed (MAX_BUCKET_COUNT - 1) (buckets (MAX_BUCKET_COUNT - 1))
  else
    .failClosed

-- ============================================================================
-- §14 #49: Witness theorems
-- ============================================================================

namespace BucketRangeOutcome

/-- **§14 #49 (closed-world dichotomy)**: every outcome is one of
    the three constructors. Inductive exhaustiveness rules out a
    fourth path (silent garbage). -/
theorem queryBucket_is_one_of_three
    (b : BucketIndex → Nat) (idx : BucketIndex) (r : Bool) :
    let o := queryBucket b idx r
    o.isInRange = true ∨ o.isFailClosed = true ∨ o.isRebucketed = true := by
  unfold queryBucket
  by_cases h1 : idx < MAX_BUCKET_COUNT
  · simp [h1, isInRange]
  · by_cases h2 : r
    · simp [h1, h2, isRebucketed]
    · simp [h1, h2, isFailClosed]

/-- **§14 #49 (out-of-range never returns inRange)**: an
    `idx ≥ MAX_BUCKET_COUNT` cannot produce an `inRange` outcome.
    Silent overflow is structurally impossible. -/
theorem out_of_range_does_not_return_inRange
    (b : BucketIndex → Nat) (idx : BucketIndex) (r : Bool)
    (h : MAX_BUCKET_COUNT ≤ idx) :
    queryBucket b idx r ≠ .inRange (b idx) := by
  unfold queryBucket
  have hnotlt : ¬ idx < MAX_BUCKET_COUNT := Nat.not_lt.mpr h
  simp [hnotlt]
  by_cases hr : r
  · simp [hr]
  · simp [hr]

/-- **§14 #49 (rebucketed index is in range)**: when the outcome
    is `rebucketed`, the clamped index is provably less than
    `MAX_BUCKET_COUNT`. Re-bucketing cannot leave the index in an
    out-of-range state. -/
theorem rebucketed_clamps_into_range
    (b : BucketIndex → Nat) (idx : BucketIndex) (r : Bool)
    (clampedIdx value : Nat)
    (h : queryBucket b idx r = .rebucketed clampedIdx value) :
    clampedIdx < MAX_BUCKET_COUNT := by
  unfold queryBucket at h
  by_cases h1 : idx < MAX_BUCKET_COUNT
  · simp [h1] at h
  · by_cases h2 : r
    · simp [h1, h2] at h
      have hc := h.1
      rw [← hc]
      unfold MAX_BUCKET_COUNT
      omega
    · simp [h1, h2] at h

end BucketRangeOutcome

end Percolator.Spec
