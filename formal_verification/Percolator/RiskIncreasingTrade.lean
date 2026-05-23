/-
  Percolator.RiskIncreasingTrade — trade-transition typing that
  requires a source-credit lien for risk-increasing operations that
  depend on positive PnL.

  Mirrors the spec rules in §§9 and 11 (`spec.md:42`, `spec.md:1108`):
    "withdrawals, conversions, fee payment from PnL, residual curing,
     and risk-increasing trades that depend on positive PnL MUST
     reserve or consume a source-domain credit lien."

  The §14 #8 invariant is closed by making the lien witness a
  required field of the risk-increasing constructor. No expression
  can build a `TradeStep.riskIncreasing` without supplying a
  `Lien BackingSource.Counterparty` whose backing field is positive.
  Code that "forgets" the lien fails to typecheck.

  §14 invariants addressed:
    - #8 `risk_increasing_trade_requires_source_credit_lien`
-/

import Percolator.Lien
import Percolator.Lifecycle
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

/-- A single trade step. Either:

      - `riskDecreasing`: no lien required. Reducing exposure cannot
        introduce new positive-PnL dependence.
      - `riskIncreasing`: requires a typed `Lien Counterparty` plus a
        proof that the lien carries positive backing. The
        `backingPositive` field forbids a stub lien with zero backing
        from satisfying the constructor.
      - `riskIncreasingInsurance`: insurance-backed variant —
        same shape with a `Lien Insurance`.

    The §14 #8 closure is structural: the risk-increasing
    constructors cannot be applied without producing a lien with
    positive backing. -/
inductive TradeStep : Type where
  | riskDecreasing : TradeStep
  | riskIncreasing
      (lien : Lien BackingSource.Counterparty)
      (backingPositive : 0 < lien.backingReservedNum) : TradeStep
  | riskIncreasingInsurance
      (lien : Lien BackingSource.Insurance)
      (backingPositive : 0 < lien.backingReservedNum) : TradeStep
  deriving Repr

namespace TradeStep

/-- **§14 #8 (counterparty witness)**: a `riskIncreasing` step always
    produces a lien with strictly positive backing. -/
theorem riskIncreasing_has_positive_backing
    (lien : Lien BackingSource.Counterparty)
    (backingPositive : 0 < lien.backingReservedNum) :
    0 < (TradeStep.riskIncreasing lien backingPositive
          |>.recOn (motive := fun _ => Nat)
             0
             (fun l _ => l.backingReservedNum)
             (fun l _ => l.backingReservedNum)) :=
  backingPositive

/-- **§14 #8 (insurance witness)**: symmetric statement for the
    insurance-backed risk-increasing constructor. -/
theorem riskIncreasingInsurance_has_positive_backing
    (lien : Lien BackingSource.Insurance)
    (backingPositive : 0 < lien.backingReservedNum) :
    0 < (TradeStep.riskIncreasingInsurance lien backingPositive
          |>.recOn (motive := fun _ => Nat)
             0
             (fun l _ => l.backingReservedNum)
             (fun l _ => l.backingReservedNum)) :=
  backingPositive

/-- Project a trade step to the backing it consumes (zero for the
    risk-decreasing constructor; the lien's backing otherwise). -/
def consumedBacking : TradeStep → Nat
  | .riskDecreasing => 0
  | .riskIncreasing lien _ => lien.backingReservedNum
  | .riskIncreasingInsurance lien _ => lien.backingReservedNum

/-- **§14 #8 (no risk-increasing without backing)**: every
    risk-increasing trade step consumes strictly positive backing.
    There is no constructor that takes a risk-increasing flag without
    a lien. -/
theorem riskIncreasing_consumedBacking_positive
    (lien : Lien BackingSource.Counterparty)
    (backingPositive : 0 < lien.backingReservedNum) :
    0 < (TradeStep.riskIncreasing lien backingPositive).consumedBacking :=
  backingPositive

theorem riskIncreasingInsurance_consumedBacking_positive
    (lien : Lien BackingSource.Insurance)
    (backingPositive : 0 < lien.backingReservedNum) :
    0 < (TradeStep.riskIncreasingInsurance lien backingPositive).consumedBacking :=
  backingPositive

/-- **§14 #8 (constructor classification)**: every trade step is
    exactly one of the three forms. No fourth "risk-increasing
    without lien" constructor exists. -/
theorem classification (t : TradeStep) :
    t = .riskDecreasing
    ∨ (∃ (lien : Lien BackingSource.Counterparty)
         (h : 0 < lien.backingReservedNum),
        t = .riskIncreasing lien h)
    ∨ (∃ (lien : Lien BackingSource.Insurance)
         (h : 0 < lien.backingReservedNum),
        t = .riskIncreasingInsurance lien h) := by
  cases t with
  | riskDecreasing => exact .inl rfl
  | riskIncreasing lien h =>
    exact .inr (.inl ⟨lien, h, rfl⟩)
  | riskIncreasingInsurance lien h =>
    exact .inr (.inr ⟨lien, h, rfl⟩)

/-- **§14 #8 (zero consumed only on risk-decreasing)**: a step with
    `consumedBacking = 0` must be the risk-decreasing constructor. A
    risk-increasing step cannot have zero backing. -/
theorem zero_consumed_implies_riskDecreasing (t : TradeStep)
    (h : t.consumedBacking = 0) : t = .riskDecreasing := by
  cases t with
  | riskDecreasing => rfl
  | riskIncreasing lien hp =>
    exfalso
    unfold consumedBacking at h
    exact absurd h (Nat.not_eq_zero_of_lt hp)
  | riskIncreasingInsurance lien hp =>
    exfalso
    unfold consumedBacking at h
    exact absurd h (Nat.not_eq_zero_of_lt hp)

end TradeStep

end Percolator.Spec
