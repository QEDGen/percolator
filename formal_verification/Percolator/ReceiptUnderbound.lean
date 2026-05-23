/-
  Percolator.ReceiptUnderbound — an under-bound resolved receipt
  halts payout or routes to recovery.

  Closes §14 #79 in `SPEC_COVERAGE.md`:
  `resolved_receipt_underbound_halts_payout_or_recovers`.

  The spec rule: a `ResolvedReceipt` carries a paid-effective
  amount and a bound (the cap). When the receipt is *under-bound*
  (paid < bound), the payout cannot proceed — either it waits for
  a top-up, or it routes to permissionless recovery. The receipt
  cannot be silently treated as paid in full.

  This file makes the dichotomy structural via a closed-sum
  `ReceiptOutcome`:

    - `paid` — the receipt cleared (paid ≥ bound).
    - `haltedPendingTopup` — under-bound; payout halts waiting for
      a top-up from the account.
    - `routedToRecovery` — under-bound and account-level recovery
      conditions triggered; permissionless-recovery flow takes over.

  The structural witness is the type's exhaustiveness: every
  outcome is one of the three, so no path lets an under-bound
  receipt produce `paid`.

  §14 invariants addressed:
    - #79 `resolved_receipt_underbound_halts_payout_or_recovers`
-/

import Percolator.Defs
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

-- ============================================================================
-- §14 #79: ResolvedReceipt + closed outcome sum
-- ============================================================================

/-- A resolved payout receipt. Mirrors the relevant fields of
    `v16.rs::ResolvedReceiptV16`:
      - `paidEffectiveNum`: how much has been paid so far.
      - `boundNum`: the cap the receipt is entitled to.
      - `recoveryEligible`: whether account-level recovery
        conditions are tripped. -/
structure ResolvedReceipt where
  paidEffectiveNum  : Nat
  boundNum          : Nat
  recoveryEligible  : Bool
  deriving Repr

namespace ResolvedReceipt

/-- Predicate: is this receipt fully paid (paid ≥ bound)? -/
def isFullyPaid (r : ResolvedReceipt) : Bool :=
  decide (r.boundNum ≤ r.paidEffectiveNum)

/-- Predicate: is this receipt under-bound (paid < bound)? -/
def isUnderbound (r : ResolvedReceipt) : Bool :=
  decide (r.paidEffectiveNum < r.boundNum)

theorem fullyPaid_iff (r : ResolvedReceipt) :
    r.isFullyPaid = true ↔ r.boundNum ≤ r.paidEffectiveNum := by
  unfold isFullyPaid; simp

theorem underbound_iff (r : ResolvedReceipt) :
    r.isUnderbound = true ↔ r.paidEffectiveNum < r.boundNum := by
  unfold isUnderbound; simp

end ResolvedReceipt

/-- The closed sum of payout outcomes. Every receipt resolves to
    one of these three; no other path exists. -/
inductive ReceiptOutcome : Type where
  | paid               : ReceiptOutcome
  | haltedPendingTopup : ReceiptOutcome
  | routedToRecovery   : ReceiptOutcome
  deriving DecidableEq, Repr

namespace ReceiptOutcome

def isPaid : ReceiptOutcome → Bool
  | .paid => true
  | _     => false

def isHalted : ReceiptOutcome → Bool
  | .haltedPendingTopup => true
  | _                   => false

def isRecovery : ReceiptOutcome → Bool
  | .routedToRecovery => true
  | _                 => false

end ReceiptOutcome

namespace ResolvedReceipt

/-- The receipt-processing function. Returns the outcome based on
    the receipt's payment state and recovery eligibility. -/
def process (r : ResolvedReceipt) : ReceiptOutcome :=
  if r.isFullyPaid then
    .paid
  else if r.recoveryEligible then
    .routedToRecovery
  else
    .haltedPendingTopup

end ResolvedReceipt

-- ============================================================================
-- §14 #79: Witness theorems
-- ============================================================================

namespace ResolvedReceipt

/-- **§14 #79 (under-bound cannot produce .paid)**: when the
    receipt is under-bound (paid < bound), `process` returns
    either `haltedPendingTopup` or `routedToRecovery` — never
    `paid`. -/
theorem underbound_does_not_pay
    (r : ResolvedReceipt) (h : r.paidEffectiveNum < r.boundNum) :
    r.process ≠ .paid := by
  unfold process
  have hnf : r.isFullyPaid = false := by
    unfold isFullyPaid
    have : ¬ r.boundNum ≤ r.paidEffectiveNum := by omega
    simp [this]
  rw [hnf]
  simp
  split <;> intro hp <;> cases hp

/-- **§14 #79 (under-bound produces halted-or-recovery)**: the
    explicit positive form — under-bound implies the outcome is
    one of the two non-paying constructors. -/
theorem underbound_halts_or_recovers
    (r : ResolvedReceipt) (h : r.paidEffectiveNum < r.boundNum) :
    r.process = .haltedPendingTopup ∨ r.process = .routedToRecovery := by
  unfold process
  have hnf : r.isFullyPaid = false := by
    unfold isFullyPaid
    have : ¬ r.boundNum ≤ r.paidEffectiveNum := by omega
    simp [this]
  rw [hnf]
  by_cases hr : r.recoveryEligible
  · simp [hr]
  · simp [hr]

/-- **§14 #79 (.paid implies fully paid)**: contrapositive of
    `underbound_does_not_pay`. If the outcome is `.paid`, then the
    paid amount reaches the bound. -/
theorem paid_implies_fully_paid
    (r : ResolvedReceipt) (h : r.process = .paid) :
    r.boundNum ≤ r.paidEffectiveNum := by
  unfold process at h
  by_cases hp : r.isFullyPaid
  · exact (fullyPaid_iff r).mp hp
  · simp [hp] at h
    split at h <;> cases h

/-- **§14 #79 (closed-world dichotomy)**: every receipt outcome is
    one of the three named constructors. The closed-sum structure
    of `ReceiptOutcome` guarantees this by exhaustiveness. -/
theorem process_is_one_of_three (r : ResolvedReceipt) :
    r.process = .paid
    ∨ r.process = .haltedPendingTopup
    ∨ r.process = .routedToRecovery := by
  unfold process
  by_cases hp : r.isFullyPaid
  · simp [hp]
  by_cases hr : r.recoveryEligible
  · simp [hp, hr]
  · simp [hp, hr]

/-- **§14 #79 (recovery branch requires under-bound)**: a receipt
    that routes to recovery must have been under-bound. The
    structural witness ruling out "recovery from a fully-paid
    receipt." -/
theorem recovery_branch_requires_underbound
    (r : ResolvedReceipt) (h : r.process = .routedToRecovery) :
    r.paidEffectiveNum < r.boundNum := by
  unfold process at h
  by_cases hp : r.isFullyPaid
  · simp [hp] at h
  · push_neg at hp
    have hnotle : ¬ r.boundNum ≤ r.paidEffectiveNum := by
      intro hle
      have : r.isFullyPaid = true := by
        unfold isFullyPaid; simp [hle]
      exact hp this
    omega

/-- **§14 #79 (halted branch requires under-bound and no recovery)**:
    a receipt that halts pending top-up must have been under-bound
    and *not* recovery-eligible. -/
theorem halted_branch_requires_underbound_and_no_recovery
    (r : ResolvedReceipt) (h : r.process = .haltedPendingTopup) :
    r.paidEffectiveNum < r.boundNum ∧ r.recoveryEligible = false := by
  unfold process at h
  by_cases hp : r.isFullyPaid
  · simp [hp] at h
  by_cases hrc : r.recoveryEligible
  · simp [hp, hrc] at h
  · push_neg at hp
    have hnotle : ¬ r.boundNum ≤ r.paidEffectiveNum := by
      intro hle
      have : r.isFullyPaid = true := by
        unfold isFullyPaid; simp [hle]
      exact hp this
    refine ⟨by omega, ?_⟩
    cases hb : r.recoveryEligible
    · rfl
    · exact absurd hb hrc

end ResolvedReceipt

end Percolator.Spec
