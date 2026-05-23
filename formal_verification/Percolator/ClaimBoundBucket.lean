/-
  Percolator.ClaimBoundBucket — Phase 3: §14 #48 closure.

  The "claim_bound_bucket formula" computes per-bucket atom counts via
  `amount_from_bound_num` (defined in `Percolator/BoundArith.lean`) and
  sums them across buckets to get the source-domain total.

  §14 #48: `claim_bound_bucket_formula_never_understates_source_domain_claims`.

  The Lean statement: `amount_from_bound_num` is *sub-additive over
  ceiling-division* — summing the per-bucket ceilings is always at least
  the ceiling of the sum:

      Σ amount_from_bound_num(bucket_num[i]) ≥ amount_from_bound_num(Σ bucket_num[i])

  This means the bucket-level formula's output is a conservative upper
  bound on what the source-domain formula would compute against the
  summed input. Conservative = doesn't understate.

  Proof rests on the basic ceiling arithmetic fact `ceil(a) + ceil(b) ≥
  ceil(a + b)` for division by a fixed positive integer.
-/

import Percolator.BoundArith
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

-- ============================================================================
-- Sub-additivity of amount_from_bound_num
-- ============================================================================

/-- **§14 #48 (pairwise)**: ceiling-division is sub-additive.

    `amountFromBoundNum (a + b) ≤ amountFromBoundNum a + amountFromBoundNum b`.

    The bucket-level formula doesn't understate the source-domain
    aggregate: summing the per-bucket ceilings is always at least the
    ceiling of the per-source sum.

    Proof: `amountFromBoundNum x · BOUND_SCALE ≥ x` (by
    `amountFromBoundNum_rounds_up`); sum that for x = a, b and use
    `amountFromBoundNum_minimal`. -/
theorem amountFromBoundNum_subadditive (a b : Nat) :
    amountFromBoundNum (a + b) ≤ amountFromBoundNum a + amountFromBoundNum b := by
  -- (amountFromBoundNum a + amountFromBoundNum b) · BOUND_SCALE
  --   = amountFromBoundNum a · BOUND_SCALE + amountFromBoundNum b · BOUND_SCALE
  --   ≥ a + b
  have hsum :
      (amountFromBoundNum a + amountFromBoundNum b) * BOUND_SCALE ≥ a + b := by
    have ha := amountFromBoundNum_rounds_up a
    have hb := amountFromBoundNum_rounds_up b
    have :
        (amountFromBoundNum a + amountFromBoundNum b) * BOUND_SCALE
        = amountFromBoundNum a * BOUND_SCALE + amountFromBoundNum b * BOUND_SCALE := by
      ring
    linarith
  exact amountFromBoundNum_minimal (a + b) _ hsum

-- ============================================================================
-- List-level (generalized) version
-- ============================================================================

/-- Sum of `amountFromBoundNum` applied to each list element. -/
def sumAmountFromBoundNum (xs : List Nat) : Nat :=
  (xs.map amountFromBoundNum).sum

/-- **§14 #48 (list form)**: `amountFromBoundNum` distributes
    sub-additively over a list of bucket nums.

    `amountFromBoundNum (Σ xs) ≤ Σ (amountFromBoundNum xs[i])`.

    Holds by induction on the list, with `amountFromBoundNum_subadditive`
    at each step. -/
theorem amountFromBoundNum_le_sumAmountFromBoundNum (xs : List Nat) :
    amountFromBoundNum xs.sum ≤ sumAmountFromBoundNum xs := by
  induction xs with
  | nil =>
    -- amountFromBoundNum 0 = 0; sum [] = 0
    unfold sumAmountFromBoundNum amountFromBoundNum
    simp
  | cons x rest ih =>
    -- xs.sum = x + rest.sum
    -- sumAmountFromBoundNum (x :: rest) = amountFromBoundNum x + sumAmountFromBoundNum rest
    show amountFromBoundNum (x + rest.sum)
       ≤ amountFromBoundNum x + (rest.map amountFromBoundNum).sum
    calc amountFromBoundNum (x + rest.sum)
        ≤ amountFromBoundNum x + amountFromBoundNum rest.sum :=
          amountFromBoundNum_subadditive x rest.sum
      _ ≤ amountFromBoundNum x + sumAmountFromBoundNum rest := by
          unfold sumAmountFromBoundNum at ih ⊢
          linarith

end Percolator.Spec
