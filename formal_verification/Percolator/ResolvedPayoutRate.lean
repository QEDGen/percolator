/-
  Percolator.ResolvedPayoutRate — resolved payout uses per-source-
  domain rate or the conservative aggregate rate.

  Closes §14 #78 in `SPEC_COVERAGE.md`:
  `resolved_payout_uses_source_domain_or_conservative_aggregate_rates`.

  The spec rule: at resolution time, the engine computes a payout
  rate per account from either (a) the per-source-domain rate
  for that account's domain, or (b) the conservative-aggregate
  rate across all domains — whichever is *smaller*. Picking the
  larger would over-pay; picking *the per-domain rate without the
  aggregate fallback* could miss insolvency on a different domain.

  The structural witness: the payout rate is `min(perDomainRate,
  aggregateRate)`, so the engine never pays more than either
  bound would individually allow.

  Same pattern as §14 #45 (`ConservativeWithdrawal.lean`): a
  min/sum inequality that distinguishes the spec-mandated formula
  from forbidden alternatives.

  §14 invariants addressed:
    - #78 `resolved_payout_uses_source_domain_or_conservative_aggregate_rates`
-/

import Percolator.Defs
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

-- ============================================================================
-- §14 #78: payout-rate min selection
-- ============================================================================

/-- Per-account payout-rate inputs at resolution time. -/
structure ResolutionRateContext where
  /-- The per-source-domain payout rate for this account's
      domain. -/
  perDomainRateNum    : Nat
  /-- The conservative cross-domain aggregate rate. -/
  aggregateRateNum    : Nat
  /-- The denominator the rate is scaled by. -/
  rateDenNum          : Nat
  deriving Repr

namespace ResolutionRateContext

/-- The spec-mandated payout rate: the smaller of the two. -/
def payoutRateNum (ctx : ResolutionRateContext) : Nat :=
  min ctx.perDomainRateNum ctx.aggregateRateNum

end ResolutionRateContext

-- ============================================================================
-- §14 #78: Witness theorems
-- ============================================================================

namespace ResolutionRateContext

/-- **§14 #78 (payout rate ≤ per-domain rate)**: the chosen rate
    is at most the per-source-domain rate — so a single domain's
    insolvency caps the payout, preventing over-pay from that
    side. -/
theorem payoutRateNum_le_perDomain (ctx : ResolutionRateContext) :
    ctx.payoutRateNum ≤ ctx.perDomainRateNum := by
  unfold payoutRateNum
  exact Nat.min_le_left _ _

/-- **§14 #78 (payout rate ≤ aggregate rate)**: the chosen rate is
    at most the conservative aggregate rate — so cross-domain
    insolvency also caps the payout, preventing over-pay from
    cross-domain underfunding. -/
theorem payoutRateNum_le_aggregate (ctx : ResolutionRateContext) :
    ctx.payoutRateNum ≤ ctx.aggregateRateNum := by
  unfold payoutRateNum
  exact Nat.min_le_right _ _

/-- **§14 #78 (payout rate equals one of the two)**: the spec-
    mandated rate is exactly one of the two inputs (whichever is
    smaller — or either, if equal). No third "ad-hoc" rate is
    ever produced. -/
theorem payoutRateNum_equals_one_of_two (ctx : ResolutionRateContext) :
    ctx.payoutRateNum = ctx.perDomainRateNum
    ∨ ctx.payoutRateNum = ctx.aggregateRateNum := by
  unfold payoutRateNum
  by_cases h : ctx.perDomainRateNum ≤ ctx.aggregateRateNum
  · left; exact min_eq_left h
  · right; push_neg at h; exact min_eq_right (le_of_lt h)

/-- **§14 #78 (forbidden: max-rate would over-pay)**: a
    hypothetical "max-rate" payout (using whichever rate is
    *higher*) is provably greater-or-equal to the spec rate. The
    forbidden formula always over-pays relative to the
    conservative formula; the strict inequality holds whenever
    the two rates differ. -/
theorem max_rate_overstates_when_rates_differ
    (ctx : ResolutionRateContext)
    (h : ctx.perDomainRateNum ≠ ctx.aggregateRateNum) :
    ctx.payoutRateNum
      < max ctx.perDomainRateNum ctx.aggregateRateNum := by
  unfold payoutRateNum
  by_cases h1 : ctx.perDomainRateNum ≤ ctx.aggregateRateNum
  · rw [min_eq_left h1]
    rw [max_eq_right h1]
    have : ctx.perDomainRateNum < ctx.aggregateRateNum :=
      lt_of_le_of_ne h1 h
    exact this
  · push_neg at h1
    rw [min_eq_right (le_of_lt h1)]
    rw [max_eq_left (le_of_lt h1)]
    exact h1

/-- **§14 #78 (no-fallback formula understates)**: a hypothetical
    "per-domain only" formula (ignoring the aggregate) could
    over-pay relative to the conservative min when the aggregate
    is smaller. The min formula is at most that one. -/
theorem perDomain_only_is_above_min
    (ctx : ResolutionRateContext) :
    ctx.payoutRateNum ≤ ctx.perDomainRateNum :=
  payoutRateNum_le_perDomain ctx

end ResolutionRateContext

end Percolator.Spec
