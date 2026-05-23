/-
  Percolator.YetMoreStrengthening — fourth round of strengthenings for
  audit-flagged partials from `AUDIT_2026-05-22.md`.

  §14 invariants strengthened in this file:
    - #60 `asset_cannot_activate_with_nonzero_or_unreconciled_state`
          (audit: zero-state captured; the *unreconciled-but-zero*
           distinction was absent. This file adds a `reconciled`
           flag on a paired `Reconciled` state, separate from the
           zero counts, and a strengthened activation transition
           that requires *both*. The counterfactual
           `unreconciledZero` witnesses that all-zero counts alone
           are not enough.)
    - #59 `mutable_asset_activation_requires_full_envelope_proofs`
          (audit: ActivationEnvelope was abstract Bool flags. This
           file binds each flag to a concrete derivation over
           numerical witnesses (fee, price age, margin, oi,
           bHeadroom, source credit, close progress, portfolio
           width, recovery backoff), mirroring the #88 pattern. A
           failing underlying condition forces the derived flag to
           `false`, which in turn provably blocks activation.)
    - #10 `source_credit_lien_impairment_forces_deleverage_liquidation_or_recovery`
          (audit: `normalStep` is blocked under impairment but
           "forces routing" lacked progress teeth. This file adds
           a progress-counter monoid; routes strictly advance it,
           `normalStep` is the identity on the counter, so any
           progress under impairment must have come from one of
           the three named routes.)
-/

import Percolator.Activation
import Percolator.MoreStrengthening
import Percolator.ImpairmentRouting
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

-- ============================================================================
-- §14 #60 (strengthened): reconciliation flag separate from zero counts
-- ============================================================================

namespace AssetSlotState

/-- A reconciliation flag, separate from the quantitative slot fields.

    The spec ("nonzero or unreconciled") names two *independent*
    conditions: a slot can have all-zero counts and still be
    unreconciled — e.g. mid-reorg, before a settlement attestation
    is processed, or while a side-effect queue is still draining. -/
structure Reconciliation where
  reconciled : Bool
  deriving Repr, DecidableEq

/-- A slot paired with its reconciliation flag. This is the unit
    of the strengthened activation transition. -/
structure Reconciled where
  slot           : AssetSlotState
  reconciliation : Reconciliation
  deriving Repr

namespace Reconciled

/-- Full reconciliation: zero counts AND the reconciliation flag set. -/
def fullyReconciled (r : Reconciled) : Prop :=
  r.slot.isReconciledZero ∧ r.reconciliation.reconciled = true

instance (r : Reconciled) : Decidable r.fullyReconciled := by
  unfold fullyReconciled; infer_instance

/-- An unreconciled-but-zero state: counts are zero but the flag
    is `false`. Demonstrates the distinction the audit asked for. -/
def unreconciledZero (epoch : Nat) : Reconciled where
  slot := AssetSlotState.empty epoch
  reconciliation := { reconciled := false }

/-- A fully-reconciled empty state. -/
def reconciledEmpty (epoch : Nat) : Reconciled where
  slot := AssetSlotState.empty epoch
  reconciliation := { reconciled := true }

/-- **§14 #60 (unreconciled-zero is structurally distinct)**: a slot
    with zero counts but `reconciled = false` does NOT satisfy
    `fullyReconciled`. The predicate distinguishes the two states. -/
theorem unreconciledZero_not_fullyReconciled (epoch : Nat) :
    ¬ (unreconciledZero epoch).fullyReconciled := by
  unfold unreconciledZero fullyReconciled
  intro ⟨_, h⟩
  cases h

/-- **§14 #60 (reconciled-zero is accepted)**: the fully-reconciled
    empty state satisfies the predicate — completing the picture
    that the two conditions are *separately* checked. -/
theorem reconciledEmpty_fullyReconciled (epoch : Nat) :
    (reconciledEmpty epoch).fullyReconciled := by
  unfold reconciledEmpty fullyReconciled
  refine ⟨AssetSlotState.empty_isReconciledZero epoch, rfl⟩

end Reconciled

end AssetSlotState

/-- The strengthened activation transition over the paired
    reconciled state. Requires a valid lifecycle step, full
    reconciliation (zero counts AND flag set), and every envelope
    check. Post-state bumps the slot epoch by 1 (§14 #61). -/
inductive ActivateFull :
    AssetSlotState.Reconciled → AssetLifecycle → ActivationEnvelope →
    AssetSlotState.Reconciled → AssetLifecycle → Prop where
  | step (r : AssetSlotState.Reconciled) (lBefore : AssetLifecycle)
         (env : ActivationEnvelope)
         (_hlife : AssetLifecycle.Step lBefore .Active)
         (_hrec : r.fullyReconciled)
         (_henv : env.allValid = true) :
      ActivateFull r lBefore env
        { r with slot := { r.slot with epoch := r.slot.epoch + 1 } }
        .Active

namespace ActivateFull

/-- **§14 #60 (strengthened — requires reconciliation flag)**:
    a successful `ActivateFull` proves the reconciliation flag was
    set, separately from the zero counts. -/
theorem requires_reconciliation_flag
    {r r' : AssetSlotState.Reconciled} {lBefore lAfter : AssetLifecycle}
    {env : ActivationEnvelope}
    (h : ActivateFull r lBefore env r' lAfter) :
    r.reconciliation.reconciled = true := by
  cases h with
  | step _ hrec _ => exact hrec.2

/-- **§14 #60 (strengthened — also requires zero counts)**: the
    quantitative side of the precondition. Conjoined with the flag
    requirement above. -/
theorem requires_zero_state
    {r r' : AssetSlotState.Reconciled} {lBefore lAfter : AssetLifecycle}
    {env : ActivationEnvelope}
    (h : ActivateFull r lBefore env r' lAfter) :
    r.slot.isReconciledZero := by
  cases h with
  | step _ hrec _ => exact hrec.1

/-- **§14 #60 (counterfactual: zero counts alone are insufficient)**:
    the `unreconciledZero` state (zero counts, `reconciled = false`)
    cannot be the pre-state of any `ActivateFull` transition. -/
theorem unreconciled_zero_rejects_activation
    {lBefore lAfter : AssetLifecycle} {env : ActivationEnvelope}
    {r' : AssetSlotState.Reconciled} (epoch : Nat)
    (h : ActivateFull (AssetSlotState.Reconciled.unreconciledZero epoch)
         lBefore env r' lAfter) : False := by
  have hflag := requires_reconciliation_flag h
  unfold AssetSlotState.Reconciled.unreconciledZero at hflag
  cases hflag

end ActivateFull

-- ============================================================================
-- §14 #59 (strengthened): per-envelope concrete predicates
-- ============================================================================

namespace ActivationEnvelope

/-- Concrete numerical witnesses underlying each envelope check.
    Each pair (actual, threshold) corresponds to one Bool flag on
    `ActivationEnvelope`. -/
structure Witness where
  feePaid                       : Nat
  feeRequired                   : Nat
  priceAgeBlocks                : Nat
  priceMaxAgeBlocks             : Nat
  fundingAccrued                : Nat
  fundingDue                    : Nat
  marginActual                  : Nat
  marginRequired                : Nat
  oiActual                      : Nat
  oiCap                         : Nat
  bHeadroomActual               : Nat
  bHeadroomRequired             : Nat
  sourceCreditUsed              : Nat
  sourceCreditCap               : Nat
  closeProgressDone             : Nat
  closeProgressTarget           : Nat
  portfolioWidthN               : Nat
  recoveryFallbackBackoffBlocks : Nat
  recoveryFallbackBackoffMin    : Nat
  deriving Repr

/-- Derive a complete `ActivationEnvelope` from a numerical witness.
    Each flag is `true` exactly when its underlying inequality holds.
    `portfolioOK` is delegated to `portfolioOKFromN` from the #88
    strengthening to keep the two derivations in lock-step. -/
def fromWitness (w : Witness) : ActivationEnvelope where
  feeOK              := decide (w.feeRequired ≤ w.feePaid)
  priceOK            := decide (w.priceAgeBlocks ≤ w.priceMaxAgeBlocks)
  fundingOK          := decide (w.fundingDue ≤ w.fundingAccrued)
  marginOK           := decide (w.marginRequired ≤ w.marginActual)
  oiOK               := decide (w.oiActual ≤ w.oiCap)
  bHeadroomOK        := decide (w.bHeadroomRequired ≤ w.bHeadroomActual)
  sourceCreditOK     := decide (w.sourceCreditUsed ≤ w.sourceCreditCap)
  closeProgressOK    := decide (w.closeProgressTarget ≤ w.closeProgressDone)
  portfolioOK        := portfolioOKFromN w.portfolioWidthN
  recoveryFallbackOK := decide (w.recoveryFallbackBackoffMin
                                ≤ w.recoveryFallbackBackoffBlocks)

/-- **§14 #59 (feeOK derivation)**: when the witness shows under-paid
    fee, the derived `feeOK` flag is `false`. -/
theorem fromWitness_feeOK_false_when_underpaid (w : Witness)
    (h : w.feePaid < w.feeRequired) :
    (fromWitness w).feeOK = false := by
  unfold fromWitness
  have hnot : ¬ w.feeRequired ≤ w.feePaid := by omega
  simp [hnot]

/-- **§14 #59 (priceOK derivation)**: stale price (age exceeds max)
    forces `priceOK = false`. -/
theorem fromWitness_priceOK_false_when_stale (w : Witness)
    (h : w.priceMaxAgeBlocks < w.priceAgeBlocks) :
    (fromWitness w).priceOK = false := by
  unfold fromWitness
  have hnot : ¬ w.priceAgeBlocks ≤ w.priceMaxAgeBlocks := by omega
  simp [hnot]

/-- **§14 #59 (fundingOK derivation)**: funding owed beyond accrued
    forces `fundingOK = false`. -/
theorem fromWitness_fundingOK_false_when_short (w : Witness)
    (h : w.fundingAccrued < w.fundingDue) :
    (fromWitness w).fundingOK = false := by
  unfold fromWitness
  have hnot : ¬ w.fundingDue ≤ w.fundingAccrued := by omega
  simp [hnot]

/-- **§14 #59 (marginOK derivation)**: under-margin forces flag false. -/
theorem fromWitness_marginOK_false_when_undermargined (w : Witness)
    (h : w.marginActual < w.marginRequired) :
    (fromWitness w).marginOK = false := by
  unfold fromWitness
  have hnot : ¬ w.marginRequired ≤ w.marginActual := by omega
  simp [hnot]

/-- **§14 #59 (oiOK derivation)**: OI over cap forces flag false. -/
theorem fromWitness_oiOK_false_when_over (w : Witness)
    (h : w.oiCap < w.oiActual) :
    (fromWitness w).oiOK = false := by
  unfold fromWitness
  have hnot : ¬ w.oiActual ≤ w.oiCap := by omega
  simp [hnot]

/-- **§14 #59 (bHeadroomOK derivation)**: insufficient B-headroom
    forces flag false. -/
theorem fromWitness_bHeadroomOK_false_when_short (w : Witness)
    (h : w.bHeadroomActual < w.bHeadroomRequired) :
    (fromWitness w).bHeadroomOK = false := by
  unfold fromWitness
  have hnot : ¬ w.bHeadroomRequired ≤ w.bHeadroomActual := by omega
  simp [hnot]

/-- **§14 #59 (sourceCreditOK derivation)**: source credit over cap
    forces flag false. -/
theorem fromWitness_sourceCreditOK_false_when_over (w : Witness)
    (h : w.sourceCreditCap < w.sourceCreditUsed) :
    (fromWitness w).sourceCreditOK = false := by
  unfold fromWitness
  have hnot : ¬ w.sourceCreditUsed ≤ w.sourceCreditCap := by omega
  simp [hnot]

/-- **§14 #59 (closeProgressOK derivation)**: close progress short
    of target forces flag false. -/
theorem fromWitness_closeProgressOK_false_when_short (w : Witness)
    (h : w.closeProgressDone < w.closeProgressTarget) :
    (fromWitness w).closeProgressOK = false := by
  unfold fromWitness
  have hnot : ¬ w.closeProgressTarget ≤ w.closeProgressDone := by omega
  simp [hnot]

/-- **§14 #59 (portfolioOK derivation)**: delegates to the #88
    `portfolioOKFromN` link; over-bound `N` forces flag false. -/
theorem fromWitness_portfolioOK_false_when_N_too_large (w : Witness)
    (h : MAX_PORTFOLIO_ASSETS_N < w.portfolioWidthN) :
    (fromWitness w).portfolioOK = false := by
  unfold fromWitness
  exact portfolioOKFromN_false_when_too_large w.portfolioWidthN h

/-- **§14 #59 (recoveryFallbackOK derivation)**: backoff too short
    forces flag false. -/
theorem fromWitness_recoveryFallbackOK_false_when_short (w : Witness)
    (h : w.recoveryFallbackBackoffBlocks < w.recoveryFallbackBackoffMin) :
    (fromWitness w).recoveryFallbackOK = false := by
  unfold fromWitness
  have hnot : ¬ w.recoveryFallbackBackoffMin
                ≤ w.recoveryFallbackBackoffBlocks := by omega
  simp [hnot]

/-- **§14 #59 (per-envelope soundness — fee side)**: if a witness-
    derived envelope is fully valid, the witness's fee condition
    holds. Demonstrates per-envelope decoding from `allValid`. -/
theorem fromWitness_allValid_implies_fee_paid (w : Witness)
    (h : (fromWitness w).allValid = true) :
    w.feeRequired ≤ w.feePaid := by
  have hcomp := (allValid_iff (fromWitness w)).mp h
  have hfee := hcomp.1
  unfold fromWitness at hfee
  simp at hfee
  exact hfee

/-- **§14 #59 (per-envelope soundness — margin side)**. -/
theorem fromWitness_allValid_implies_margin_satisfied (w : Witness)
    (h : (fromWitness w).allValid = true) :
    w.marginRequired ≤ w.marginActual := by
  have hcomp := (allValid_iff (fromWitness w)).mp h
  have hm := hcomp.2.2.2.1
  unfold fromWitness at hm
  simp at hm
  exact hm

/-- **§14 #59 (per-envelope soundness — source-credit side)**. -/
theorem fromWitness_allValid_implies_sourceCredit_under_cap (w : Witness)
    (h : (fromWitness w).allValid = true) :
    w.sourceCreditUsed ≤ w.sourceCreditCap := by
  have hcomp := (allValid_iff (fromWitness w)).mp h
  have hsc := hcomp.2.2.2.2.2.2.1
  unfold fromWitness at hsc
  simp at hsc
  exact hsc

/-- **§14 #59 (per-envelope soundness — recovery fallback side)**. -/
theorem fromWitness_allValid_implies_recoveryFallback_sufficient
    (w : Witness) (h : (fromWitness w).allValid = true) :
    w.recoveryFallbackBackoffMin ≤ w.recoveryFallbackBackoffBlocks := by
  have hcomp := (allValid_iff (fromWitness w)).mp h
  have hr := hcomp.2.2.2.2.2.2.2.2.2
  unfold fromWitness at hr
  simp at hr
  exact hr

end ActivationEnvelope

-- ============================================================================
-- §14 #10 (strengthened): progress monoid forces routing
-- ============================================================================

namespace AccountWithLiens

/-- The progress monoid: an account plus a non-decreasing counter
    tracking how many resolution steps have been taken. Routes
    strictly advance the counter; `normalStep` is the identity on
    it. This is the structural witness for "forces routing": any
    progress from an impaired-unresolved state must come from one
    of the three named routes. -/
structure WithProgress where
  account  : AccountWithLiens
  progress : Nat
  deriving Repr

namespace WithProgress

/-- A fresh state at zero progress. -/
def fresh : WithProgress where
  account  := AccountWithLiens.fresh
  progress := 0

/-- Lift `normalStep` to the progress-pair: identity on the counter. -/
def normalStep (wp : WithProgress) : Option WithProgress :=
  match wp.account.normalStep with
  | none   => none
  | some a => some { account := a, progress := wp.progress }

/-- Lift `routeDeleverage`: strictly advances the counter by 1. -/
def routeDeleverage (wp : WithProgress) : Option WithProgress :=
  match wp.account.routeDeleverage with
  | none   => none
  | some a => some { account := a, progress := wp.progress + 1 }

/-- Lift `routeLiquidation`: strictly advances the counter by 1. -/
def routeLiquidation (wp : WithProgress) : Option WithProgress :=
  match wp.account.routeLiquidation with
  | none   => none
  | some a => some { account := a, progress := wp.progress + 1 }

/-- Lift `routeRecovery`: strictly advances the counter by 1. -/
def routeRecovery (wp : WithProgress) : Option WithProgress :=
  match wp.account.routeRecovery with
  | none   => none
  | some a => some { account := a, progress := wp.progress + 1 }

/-- **§14 #10 (normal step is identity on progress)**: a successful
    `normalStep` leaves the progress counter unchanged. -/
theorem normalStep_progress_unchanged
    (wp wp' : WithProgress) (h : wp.normalStep = some wp') :
    wp'.progress = wp.progress := by
  unfold normalStep at h
  cases hns : wp.account.normalStep with
  | none => rw [hns] at h; cases h
  | some a =>
    rw [hns] at h
    injection h with heq
    subst heq
    rfl

/-- **§14 #10 (deleverage route strictly advances progress)**. -/
theorem routeDeleverage_progress_advances
    (wp wp' : WithProgress) (h : wp.routeDeleverage = some wp') :
    wp'.progress = wp.progress + 1 := by
  unfold routeDeleverage at h
  cases hns : wp.account.routeDeleverage with
  | none => rw [hns] at h; cases h
  | some a =>
    rw [hns] at h
    injection h with heq
    subst heq
    rfl

/-- **§14 #10 (liquidation route strictly advances progress)**. -/
theorem routeLiquidation_progress_advances
    (wp wp' : WithProgress) (h : wp.routeLiquidation = some wp') :
    wp'.progress = wp.progress + 1 := by
  unfold routeLiquidation at h
  cases hns : wp.account.routeLiquidation with
  | none => rw [hns] at h; cases h
  | some a =>
    rw [hns] at h
    injection h with heq
    subst heq
    rfl

/-- **§14 #10 (recovery route strictly advances progress)**. -/
theorem routeRecovery_progress_advances
    (wp wp' : WithProgress) (h : wp.routeRecovery = some wp') :
    wp'.progress = wp.progress + 1 := by
  unfold routeRecovery at h
  cases hns : wp.account.routeRecovery with
  | none => rw [hns] at h; cases h
  | some a =>
    rw [hns] at h
    injection h with heq
    subst heq
    rfl

/-- **§14 #10 (normal step blocked under impairment, lifted)**. -/
theorem normalStep_blocked_under_impairment
    (wp : WithProgress) (himp : wp.account.hasImpairedLien = true)
    (hres : wp.account.resolved = false) :
    wp.normalStep = none := by
  unfold normalStep
  rw [normalStep_blocked_when_impaired wp.account himp hres]

/-- **§14 #10 (closed-world: under impairment, only routes can
    produce strict progress)**. From an impaired-unresolved state,
    if any of the four candidate transitions takes us to a state
    with strictly greater progress, then the transition was one of
    the three routes — `normalStep` cannot have fired, because it
    is blocked under impairment. -/
theorem strict_progress_from_impairment_implies_route
    (wp wp' : WithProgress)
    (himp : wp.account.hasImpairedLien = true)
    (hres : wp.account.resolved = false)
    (h : wp.normalStep = some wp' ∨
         wp.routeDeleverage = some wp' ∨
         wp.routeLiquidation = some wp' ∨
         wp.routeRecovery = some wp') :
    wp.routeDeleverage = some wp' ∨
    wp.routeLiquidation = some wp' ∨
    wp.routeRecovery = some wp' := by
  rcases h with hns | hrest
  · have hblock := normalStep_blocked_under_impairment wp himp hres
    rw [hblock] at hns
    cases hns
  · exact hrest

end WithProgress

end AccountWithLiens

end Percolator.Spec
