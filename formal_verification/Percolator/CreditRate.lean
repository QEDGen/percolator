/-
  Percolator.CreditRate — Source-credit rate formula refinement.

  Mirror of `src/v16.rs::expected_source_credit_rate_num_for_state`
  (lines 7990-8002). The Rust impl computes:

      if state.positive_claim_bound_num == 0:
          return CREDIT_RATE_SCALE      -- full credit (1.0) when no claim
      let available = available_backing_num_for_source_credit_state(state)
      let rate = (available * CREDIT_RATE_SCALE) / state.positive_claim_bound_num
      min(rate, CREDIT_RATE_SCALE)

  The Rust uses U256 widening to avoid overflow in `available · CREDIT_RATE_SCALE`;
  Lean's `Nat` is unbounded, so we compute directly. The U256 widening correctness
  is proven separately in `Percolator/WideMath.lean` and bridged at the proptest
  level (`tests/proofs_v16_lean_refinement.rs`).

  §14 invariants this file closes:
    - #42 `credit_rate_num_bounded_below_and_above` (fully)
    - #1  `source_domain_positive_credit_capped_by_realizable_backing` (the
          formula half — the "realizable backing" predicate is a separate concern)
    - #50 `credit_rate_recomputation_is_bounded_by_domain_count_and_bucket_count`
          (the per-domain math half — the bounded-work claim is operational)
-/

import Percolator.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Percolator.Spec

-- ============================================================================
-- The credit-rate formula
-- ============================================================================

/-- The credit rate as computed by `expected_source_credit_rate_num_for_state`.

    When `claim = 0` (no positive claim against the source domain), credit rate
    is full (= `CREDIT_RATE_SCALE`, semantically 1.0). Otherwise it's the ratio
    `available · SCALE / claim`, capped at `SCALE`.

    `available` is the realizable backing num for the source-credit state; `claim`
    is `state.positive_claim_bound_num`. -/
def creditRateNum (available claim : Nat) : Nat :=
  if claim = 0 then CREDIT_RATE_SCALE
  else min ((available * CREDIT_RATE_SCALE) / claim) CREDIT_RATE_SCALE

-- ============================================================================
-- Bound theorems (§14 #42)
-- ============================================================================

/-- **Upper bound**: the credit rate never exceeds `CREDIT_RATE_SCALE`, which
    is the unit (1.0 in fixed-point). This is the load-bearing safety property:
    no account can claim more than its full backing-weighted share.

    Direct from `min`, regardless of how the cap branch is reached. -/
theorem creditRateNum_le_scale (available claim : Nat) :
    creditRateNum available claim ≤ CREDIT_RATE_SCALE := by
  unfold creditRateNum
  by_cases h : claim = 0
  · simp [h]
  · simp [h]

/-- **Lower bound**: rate is non-negative. Trivial in `Nat` (everything is ≥ 0);
    included for `§14 #42` traceability since the spec phrases the invariant as
    "bounded below and above." -/
theorem creditRateNum_nonneg (available claim : Nat) :
    0 ≤ creditRateNum available claim :=
  Nat.zero_le _

-- ============================================================================
-- Boundary behavior
-- ============================================================================

/-- **Zero claim ⇒ full credit**. When no positive claim has been booked against
    the source domain, the rate is exactly `CREDIT_RATE_SCALE` (the identity).
    Mirrors the early-return `if state.positive_claim_bound_num == 0` branch. -/
theorem creditRateNum_zero_claim (available : Nat) :
    creditRateNum available 0 = CREDIT_RATE_SCALE := by
  unfold creditRateNum
  simp

/-- **Zero backing ⇒ zero credit** (when there is a positive claim). This is the
    load-bearing fail-closed property: if the source domain has nothing realizable
    backing it, the engine MUST credit zero against any claim.

    Closes the "zero backing" lane of `proof_v16_account_source_claim_equity_zero_backing_gives_zero_credit`. -/
theorem creditRateNum_zero_backing (claim : Nat) (h : 0 < claim) :
    creditRateNum 0 claim = 0 := by
  unfold creditRateNum
  have hne : claim ≠ 0 := Nat.pos_iff_ne_zero.mp h
  simp [hne]

/-- **Full backing ⇒ rate caps at SCALE**. When `available ≥ claim`, the rate
    saturates at `CREDIT_RATE_SCALE` (i.e. 1.0 in fixed-point) — the engine
    does not over-credit.

    Closes the "full backing" lane of
    `proof_v16_account_source_claim_equity_full_backing_gives_full_credit`. -/
theorem creditRateNum_full_backing
    (available claim : Nat) (hc : 0 < claim) (h : claim ≤ available) :
    creditRateNum available claim = CREDIT_RATE_SCALE := by
  have hne : claim ≠ 0 := Nat.pos_iff_ne_zero.mp hc
  -- SCALE ≤ (available * SCALE) / claim
  have hge : CREDIT_RATE_SCALE ≤ (available * CREDIT_RATE_SCALE) / claim := by
    rw [Nat.le_div_iff_mul_le hc]
    calc CREDIT_RATE_SCALE * claim
        = claim * CREDIT_RATE_SCALE := by ring
      _ ≤ available * CREDIT_RATE_SCALE :=
          Nat.mul_le_mul_right CREDIT_RATE_SCALE h
  unfold creditRateNum
  rw [if_neg hne]
  exact min_eq_right hge

-- ============================================================================
-- Monotonicity (used downstream when refresh increases realizable backing)
-- ============================================================================

/-- **Monotone in available backing**. If realizable backing grows (e.g. after a
    full refresh adds a fresh bucket), the credit rate weakly grows. This is what
    lets `full_account_refresh` re-issue a higher health certificate without
    violating safety: any new credit is properly backed. -/
theorem creditRateNum_mono_in_backing
    (a1 a2 claim : Nat) (h : a1 ≤ a2) :
    creditRateNum a1 claim ≤ creditRateNum a2 claim := by
  unfold creditRateNum
  by_cases hc : claim = 0
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc]
    -- Goal: min ((a1 * S) / claim) S ≤ min ((a2 * S) / claim) S
    have hdiv : (a1 * CREDIT_RATE_SCALE) / claim ≤ (a2 * CREDIT_RATE_SCALE) / claim :=
      Nat.div_le_div_right (Nat.mul_le_mul_right _ h)
    exact le_min (le_trans (min_le_left _ _) hdiv) (min_le_right _ _)

/-- **Antitone in claim**. If the source-domain positive claim grows (more risk
    booked), the credit rate weakly shrinks at fixed backing — i.e. each unit
    of backing supports proportionally less. The discontinuity at `claim = 0`
    means this only holds for `0 < claim_1 ≤ claim_2`. -/
theorem creditRateNum_anti_in_claim
    (available c1 c2 : Nat) (h1 : 0 < c1) (h : c1 ≤ c2) :
    creditRateNum available c2 ≤ creditRateNum available c1 := by
  unfold creditRateNum
  have h2 : 0 < c2 := Nat.lt_of_lt_of_le h1 h
  have hne1 : c1 ≠ 0 := Nat.pos_iff_ne_zero.mp h1
  have hne2 : c2 ≠ 0 := Nat.pos_iff_ne_zero.mp h2
  rw [if_neg hne1, if_neg hne2]
  -- Goal: min ((available * S) / c2) S ≤ min ((available * S) / c1) S
  have hdiv : (available * CREDIT_RATE_SCALE) / c2
              ≤ (available * CREDIT_RATE_SCALE) / c1 :=
    Nat.div_le_div_left h h1
  exact le_min (le_trans (min_le_left _ _) hdiv) (min_le_right _ _)

end Percolator.Spec
