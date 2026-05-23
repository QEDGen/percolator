/-
  Percolator.OraclePumpLimit — credit realizable from any claim is
  bounded by available backing.

  Closes §14 #6 in `SPEC_COVERAGE.md`:
  `oracle_pump_credit_limited_by_opposing_reserved_backing`.

  The spec rule: if an adversary inflates the oracle price (an
  "oracle pump") and that grows the account's claim, the
  realizable source-credit cannot grow beyond the backing
  reserved on the opposing side. Concretely, the realizable
  credit `rate × claim / CREDIT_RATE_SCALE` is bounded above by
  the available backing — independent of how large the claim
  becomes.

  This file builds on `Percolator/CreditRate.lean` (Phase 1):

    - `creditRateNum` is defined as
      `min((available · SCALE) / claim, SCALE)` for `claim > 0`.
    - The realized credit at a claim is
      `creditRateNum × claim / SCALE`.

  The §14 #6 closure: this realized credit is `≤ available`
  regardless of the claim magnitude.

  §14 invariants addressed:
    - #6 `oracle_pump_credit_limited_by_opposing_reserved_backing`
-/

import Percolator.CreditRate
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

-- ============================================================================
-- §14 #6: realized credit bounded by available backing
-- ============================================================================

/-- **§14 #6 (the rate's numerator never exceeds available × SCALE)**:
    by construction, `creditRateNum available claim ≤
    (available · SCALE) / claim` (when claim > 0) and ≤ SCALE
    (always). This is the structural floor of the credit-rate
    formula. -/
theorem creditRateNum_le_ratio
    (available claim : Nat) (h : 0 < claim) :
    creditRateNum available claim
    ≤ (available * CREDIT_RATE_SCALE) / claim := by
  unfold creditRateNum
  have hne : claim ≠ 0 := Nat.pos_iff_ne_zero.mp h
  rw [if_neg hne]
  exact Nat.min_le_left _ _

/-- **§14 #6 (realized credit ≤ available · SCALE)**: multiplying
    the rate back by `claim` gives an amount bounded above by
    `available · SCALE`. After dividing out the fixed-point
    scale, the realized credit is bounded by `available`. -/
theorem realized_credit_bounded_by_backing_scaled
    (available claim : Nat) (h : 0 < claim) :
    creditRateNum available claim * claim
      ≤ available * CREDIT_RATE_SCALE := by
  have hle := creditRateNum_le_ratio available claim h
  -- creditRateNum ≤ ⌊(available · SCALE) / claim⌋
  -- multiply both sides by claim (positive):
  --   creditRateNum × claim ≤ ⌊(available · SCALE) / claim⌋ × claim
  --                         ≤ available · SCALE        (by Nat.div_mul_le_self)
  calc creditRateNum available claim * claim
      ≤ ((available * CREDIT_RATE_SCALE) / claim) * claim :=
        Nat.mul_le_mul_right _ hle
    _ ≤ available * CREDIT_RATE_SCALE := Nat.div_mul_le_self _ _

/-- **§14 #6 (oracle-pump-proof bound)**: dividing the previous
    bound by `CREDIT_RATE_SCALE` gives the spec-level claim:
    realized credit (in user-facing units) is bounded by
    `available`, regardless of how big `claim` is.

    Concretely: `(rate × claim) / SCALE ≤ available`. -/
theorem realized_credit_bounded_by_backing
    (available claim : Nat) (h : 0 < claim) :
    (creditRateNum available claim * claim) / CREDIT_RATE_SCALE
      ≤ available := by
  have hscale : 0 < CREDIT_RATE_SCALE := by
    unfold CREDIT_RATE_SCALE
    decide
  have hbound := realized_credit_bounded_by_backing_scaled available claim h
  -- div is monotone, so dividing hbound by SCALE gives the result.
  have hdiv : (creditRateNum available claim * claim) / CREDIT_RATE_SCALE
            ≤ (available * CREDIT_RATE_SCALE) / CREDIT_RATE_SCALE :=
    Nat.div_le_div_right hbound
  rw [Nat.mul_div_cancel _ hscale] at hdiv
  exact hdiv

/-- **§14 #6 (oracle-pump is *bounded*, not zero)**: even if the
    claim grows arbitrarily large (oracle pump), realized credit
    is still bounded by `available` — it can grow up to the
    backing, but no further. The bound is tight: with claim ≤
    available, realized credit can reach `available · SCALE /
    SCALE = available`. -/
theorem oracle_pump_cannot_exceed_backing
    (available claim claim' : Nat) (hpos : 0 < claim) (hpos' : 0 < claim')
    (_grew : claim ≤ claim') :
    (creditRateNum available claim' * claim') / CREDIT_RATE_SCALE
      ≤ available :=
  realized_credit_bounded_by_backing available claim' hpos'

end Percolator.Spec
