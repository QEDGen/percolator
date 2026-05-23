/-
  Percolator.DeadLegForfeit — dead-leg forfeit/detach payout safety.

  Mirrors the spec rule in §12 (`spec.md:1389`):
    "Dead-leg forfeit/detach … values positive PnL at zero unless
    source-domain backing is consumed, values negative PnL at
    conservative fallback/recovery loss within the §1.3 recovery
    fallback envelope, books residual only to (asset, opposing_side),
    clears only after residual durability …"

  The §14 #83 invariant — "uses bounded fallback or zero positive
  payout" — is captured here as a *closed sum*: a `DeadLegOutcome` is
  either `zeroPositive` (no positive value transferred) or
  `boundedFallback` carrying a `FallbackPriceInput` whose `accepted`
  proof obligation is in the constructor. Every value of the type
  falls into one of the two safe categories; there is no
  out-of-envelope unbounded outcome.

  §14 invariants addressed:
    - #83 `dead_leg_forfeit_uses_bounded_fallback_or_zero_positive_payout`
-/

import Percolator.RecoveryFallback
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

/-- The two safe outcomes of a dead-leg forfeit/detach.

    `zeroPositive` — the dead leg's positive-PnL valuation is zero.
    No source-domain backing was consumed, and the safe path is to
    transfer no positive value at all.

    `boundedFallback` — a fallback-price valuation is used, with the
    `FallbackPriceInput.accepted` proof carried in the constructor.
    By §14 #80/#81/#82 (`RecoveryFallback.lean`), this is bounded by
    the configured deviation envelope.

    There is no third constructor for "unbounded payout under
    unverified or out-of-envelope price" — that case cannot be
    represented as a valid `DeadLegOutcome`. -/
inductive DeadLegOutcome : Type where
  | zeroPositive
    : DeadLegOutcome
  | boundedFallback
      (input : FallbackPriceInput)
      (accepted : input.accepted)
    : DeadLegOutcome
  deriving Repr

namespace DeadLegOutcome

/-- The positive payout produced by this outcome. -/
def positivePayout : DeadLegOutcome → Nat
  | .zeroPositive => 0
  | .boundedFallback _ _ => 0  -- positive PnL is zeroed under fallback per spec

/-- The negative-PnL valuation produced by this outcome. For
    `boundedFallback`, this is `legTransferBound` with the carried
    fallback input. -/
def negativeValuation : DeadLegOutcome → Nat → Nat
  | .zeroPositive, _ => 0
  | .boundedFallback input _, posQAbs =>
      legTransferBound posQAbs input.P_ref input.P_fb

/-- **§14 #83 (positive payout is zero)**: every safe outcome returns
    zero positive payout. The spec's "values positive PnL at zero
    unless backing is consumed" is captured by this being the only
    payout function — backing consumption is a separate side
    transition not modeled in this lemma. -/
theorem positivePayout_zero (o : DeadLegOutcome) :
    o.positivePayout = 0 := by
  cases o <;> rfl

/-- **§14 #83 (negative valuation bounded under fallback)**: when the
    outcome is `boundedFallback`, the negative-PnL valuation is the
    per-leg transfer bound — already proven to be bounded by the
    deviation envelope (`RecoveryFallback.lean`). -/
theorem boundedFallback_negativeValuation_eq
    (input : FallbackPriceInput) (accepted : input.accepted) (posQAbs : Nat) :
    (DeadLegOutcome.boundedFallback input accepted).negativeValuation posQAbs
    = legTransferBound posQAbs input.P_ref input.P_fb := rfl

/-- **§14 #83 (negative valuation zero on zeroPositive branch)**: the
    `zeroPositive` outcome carries no fallback price and so reports
    zero negative valuation as well. -/
theorem zeroPositive_negativeValuation
    (posQAbs : Nat) :
    DeadLegOutcome.zeroPositive.negativeValuation posQAbs = 0 := rfl

/-- **§14 #83 (no out-of-envelope path)**: there is no constructor for
    an `out-of-envelope` outcome. The type is closed at two
    constructors, both of which are safe by `positivePayout_zero`. -/
theorem no_unverified_constructor :
    ∀ o : DeadLegOutcome, o = .zeroPositive ∨
      ∃ input : FallbackPriceInput, ∃ h : input.accepted,
        o = .boundedFallback input h := by
  intro o
  cases o with
  | zeroPositive => exact .inl rfl
  | boundedFallback input accepted =>
    exact .inr ⟨input, accepted, rfl⟩

/-- **§14 #83 (envelope-bounded transfer)**: when the outcome is a
    `boundedFallback`, the per-leg transfer bound is bounded by the
    envelope-deviation cap, courtesy of `envelopeValid` carried in
    the `FallbackPriceInput.accepted` proof. -/
theorem boundedFallback_envelope_holds
    (input : FallbackPriceInput) (accepted : input.accepted) :
    envelopeValid input.P_ref input.P_fb input.devBps :=
  accepted.2

end DeadLegOutcome

end Percolator.Spec
