/-
  Percolator.NoPayoutCredit — soft maintenance credit and uncollectible
  fees never reach payout or socialization.

  Mirrors two related spec rules:
    - "Open positive PnL may support health, but it MUST NOT cure a
      bankruptcy residual unless a source-domain backing lien is
      consumed" (`spec.md:48`).
    - "Rounding residue is always assigned to a non-user,
      non-backing stock class" (`spec.md:1556`); the analogous
      principle for uncollectible fees per §10 — they are forgiven,
      not socialized into senior pools.

  §14 invariants addressed:
    - #52 `soft_maintenance_credit_does_not_create_payout_or_residual_cure`
    - #77 `uncollectible_fees_forgiven_not_socialized`
-/

import Percolator.SoftCredit
import Percolator.StockReconciliation
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

-- ============================================================================
-- §14 #52: soft maintenance credit does not create payout or residual cure
-- ============================================================================

/-- A payout decision computed from soft credit. The constructor
    refuses to fire when the underlying credit is purely soft (i.e.
    the `lienBackedAmount` is zero).

    `softCreditAmount` — the soft maintenance credit, computed via
    `SoftCredit.softCredit`.
    `lienBackedAmount` — the portion actually backed by a consumed
    source-credit lien. Only this portion is eligible for payout. -/
structure PayoutFromCredit where
  softCreditAmount : Nat
  lienBackedAmount : Nat
  /-- Soft credit alone is *not* enough — the payout amount is
      determined by `lienBackedAmount`. Captured here as a structure
      invariant rather than a separate predicate. -/
  payoutAmount     : Nat
  payoutLe         : payoutAmount ≤ lienBackedAmount
  deriving Repr

namespace PayoutFromCredit

/-- **§14 #52**: the payout amount is bounded by the lien-backed
    portion of the credit, not by the soft credit. A soft-credit-only
    scenario (where `lienBackedAmount = 0`) forces `payoutAmount = 0`. -/
theorem soft_credit_only_yields_zero_payout
    (p : PayoutFromCredit) (h : p.lienBackedAmount = 0) :
    p.payoutAmount = 0 := by
  have := p.payoutLe
  omega

/-- **§14 #52 (no payout from soft credit)**: increasing
    `softCreditAmount` does not raise `payoutAmount`. The
    `payoutLe` field bounds payout by `lienBackedAmount` only. -/
theorem payout_independent_of_soft_credit (p : PayoutFromCredit) :
    p.payoutAmount ≤ p.lienBackedAmount := p.payoutLe

/-- **§14 #52 (no residual cure from soft credit)**: a "residual
    cure" amount drawn from `PayoutFromCredit` is also bounded by
    `lienBackedAmount`. Modeled as a derived projection. -/
def residualCureContribution (p : PayoutFromCredit) : Nat :=
  p.payoutAmount

theorem residualCureContribution_le_lien_backed (p : PayoutFromCredit) :
    p.residualCureContribution ≤ p.lienBackedAmount := p.payoutLe

theorem residualCureContribution_zero_when_only_soft
    (p : PayoutFromCredit) (h : p.lienBackedAmount = 0) :
    p.residualCureContribution = 0 :=
  soft_credit_only_yields_zero_payout p h

end PayoutFromCredit

-- ============================================================================
-- §14 #77: uncollectible fees forgiven, not socialized
-- ============================================================================

/-- A fee resolution. `assessed` is the fee charged; `collectible`
    is the portion the engine can actually withhold from available
    capital; `uncollectible = assessed - collectible` is the gap.

    The §14 #77 invariant is that the uncollectible portion is
    *forgiven* — it does not socialize into insurance, senior
    capital, or any user-claim pool. -/
structure FeeResolution where
  assessed     : Nat
  collectible  : Nat
  collLeAssess : collectible ≤ assessed
  deriving Repr

namespace FeeResolution

/-- Uncollectible portion of the fee. -/
def uncollectible (f : FeeResolution) : Nat :=
  f.assessed - f.collectible

theorem uncollectible_plus_collectible_eq_assessed (f : FeeResolution) :
    f.uncollectible + f.collectible = f.assessed := by
  unfold uncollectible
  have := f.collLeAssess
  omega

/-- **§14 #77 (forgiven amount target)**: the uncollectible portion
    is destined for a `forgiven` sink — a value that does not feed
    any user-facing or senior pool. We model the sink as a
    distinguished `ProtocolForgiveness` class outside the
    StockClasses partition.

    `applyForgiveness` simply discards the uncollectible amount; it
    does not credit insurance, surplus, or any escrow. -/
def applyForgiveness (sc : StockClasses) (_f : FeeResolution) : StockClasses := sc

/-- **§14 #77 (forgiveness does not touch insurance)**:
    `applyForgiveness` leaves `insurance` unchanged. -/
theorem applyForgiveness_preserves_insurance
    (sc : StockClasses) (f : FeeResolution) :
    (applyForgiveness sc f).insurance = sc.insurance := rfl

/-- **§14 #77 (forgiveness does not touch any user-claim class)**:
    every StockClasses field is preserved by `applyForgiveness`. -/
theorem applyForgiveness_preserves_cTot
    (sc : StockClasses) (f : FeeResolution) :
    (applyForgiveness sc f).cTot = sc.cTot := rfl

theorem applyForgiveness_preserves_cancelDepositEscrow
    (sc : StockClasses) (f : FeeResolution) :
    (applyForgiveness sc f).cancelDepositEscrow = sc.cancelDepositEscrow := rfl

theorem applyForgiveness_preserves_unallocatedProtocolSurplus
    (sc : StockClasses) (f : FeeResolution) :
    (applyForgiveness sc f).unallocatedProtocolSurplus
    = sc.unallocatedProtocolSurplus := rfl

theorem applyForgiveness_preserves_totalV
    (sc : StockClasses) (f : FeeResolution) :
    (applyForgiveness sc f).totalV = sc.totalV := rfl

/-- **The counterfactual socialization function** — what *would* happen
    if the spec rule were violated and uncollectible fees pushed into
    insurance. This is defined explicitly so the contrast with
    `applyForgiveness` is provable, not just asserted.

    The §14 #77 invariant says the engine MUST use `applyForgiveness`,
    NOT `socializeIntoInsurance`. Both functions are total and
    well-typed; the spec rule chooses one. -/
def socializeIntoInsurance (sc : StockClasses) (f : FeeResolution) :
    StockClasses :=
  { sc with insurance := sc.insurance + f.uncollectible }

/-- **§14 #77 (socialization grows insurance; forgiveness does not)**:
    when the uncollectible portion is positive, the would-be
    socialization strictly grows `insurance`, while `applyForgiveness`
    leaves it unchanged. Choosing `applyForgiveness` is a *real*
    choice, not a no-op. -/
theorem socializeIntoInsurance_grows_insurance
    (sc : StockClasses) (f : FeeResolution) (hpos : 0 < f.uncollectible) :
    sc.insurance < (socializeIntoInsurance sc f).insurance := by
  unfold socializeIntoInsurance
  show sc.insurance < sc.insurance + f.uncollectible
  omega

/-- **§14 #77 (socialization grows vault total; forgiveness does not)**:
    the spec preserves the vault by forgiveness; socialization would
    increase the totalV by `uncollectible`. The two functions are
    therefore *distinguishable* — `forgive` is the choice the spec
    mandates. -/
theorem socializeIntoInsurance_grows_totalV
    (sc : StockClasses) (f : FeeResolution) (hpos : 0 < f.uncollectible) :
    sc.totalV < (socializeIntoInsurance sc f).totalV := by
  unfold socializeIntoInsurance
  unfold StockClasses.totalV
  simp
  omega

/-- **§14 #77 (forgive ≠ socialize)**: the two functions produce
    different outputs whenever the uncollectible portion is positive.
    The spec rule "use forgive" is therefore a meaningful constraint:
    a non-compliant engine that used socialize would produce a
    different stock-class state. -/
theorem forgive_distinct_from_socialize
    (sc : StockClasses) (f : FeeResolution) (hpos : 0 < f.uncollectible) :
    applyForgiveness sc f ≠ socializeIntoInsurance sc f := by
  intro heq
  have hf := applyForgiveness_preserves_insurance sc f
  have hs := socializeIntoInsurance_grows_insurance sc f hpos
  rw [heq] at hf
  omega

/-- **§14 #77 (uncollectible vanishes under forgive)**: the
    uncollectible portion does not appear in any stock class after
    forgiveness. Total vault is preserved exactly. -/
theorem forgive_uncollectible_vanishes
    (sc : StockClasses) (f : FeeResolution) :
    (applyForgiveness sc f).totalV = sc.totalV := applyForgiveness_preserves_totalV sc f

end FeeResolution

end Percolator.Spec
