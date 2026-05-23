/-
  Percolator.EvenMoreStrengthening — third round of strengthenings
  for audit-flagged partials from `AUDIT_2026-05-22.md`.

  §14 invariants strengthened in this file:
    - #46 `close_drift_reserve_has_backed_loss_capacity_or_recovers`
          (audit: predicate defined but no handler binding;
           this file adds `continueOrRecover` that types every
           continuation as either backed-continue or routed-to-
           recovery, no third path)
    - #52 `soft_maintenance_credit_does_not_create_payout_or_residual_cure`
          (audit: PayoutFromCredit existed but no engine binding;
           this file adds `attemptPayout` over AccountCapital that
           consumes only the lien-backed portion)
    - #55 `backing_consumption_reduces_loser_capital_and_preserves_senior_invariants`
          (audit: senior invariant at simplified 3-class vault, not
           full 10-class StockClasses; this file embeds
           VaultSnapshot into StockClasses so the 3-class invariant
           lifts to a totalV-conservation statement)
-/

import Percolator.CloseLedger
import Percolator.NoPayoutCredit
import Percolator.ActualBacking
import Percolator.BackingConsumption
import Percolator.StockReconciliation
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

-- ============================================================================
-- §14 #46 (strengthened): typed continuation outcome with no third path
-- ============================================================================

namespace CloseLedger

/-- The outcome of a close-progress continuation attempt: either a
    successful step under backed drift reserve, or an explicit
    routing to recovery when the reserve is unbacked. The closed sum
    forbids a "continue without backing" path. -/
inductive ContinuationOutcome : Type where
  | continued       (l : CloseLedger) : ContinuationOutcome
  | routedToRecovery (reason : String) : ContinuationOutcome
  deriving Repr

namespace ContinuationOutcome

/-- Is this outcome a continuation (i.e. drift-backed step)? -/
def isContinued : ContinuationOutcome → Bool
  | .continued _ => true
  | .routedToRecovery _ => false

/-- Is this outcome a recovery routing? -/
def isRecovery : ContinuationOutcome → Bool
  | .continued _ => false
  | .routedToRecovery _ => true

end ContinuationOutcome

/-- **Gated continuation**: a close-progress booking that fires only
    when the drift reserve is provably backed. Otherwise routes to
    recovery via the spec-mandated path.

    Per `spec.md:1252-1262`: "If [the drift reserve] cannot be
    backed, ordinary close continuation MUST route to recovery." -/
def continueOrRecover
    (l : CloseLedger) (driftReserve : Nat) (backing : DriftBacking)
    (amount : Nat) : ContinuationOutcome :=
  if closeDriftReserveBacked driftReserve backing then
    match l.bookSupport amount with
    | some l' => .continued l'
    | none    => .routedToRecovery "bookSupport precondition failed"
  else
    .routedToRecovery "drift reserve not backed"

/-- **§14 #46 (no continuation without backing)**: if the outcome is
    `continued`, the drift-reserve backing predicate must have
    held. There is no path that produces `continued` without backing. -/
theorem continueOrRecover_continued_implies_backed
    (l l' : CloseLedger) (driftReserve : Nat) (backing : DriftBacking)
    (amount : Nat)
    (h : continueOrRecover l driftReserve backing amount = .continued l') :
    closeDriftReserveBacked driftReserve backing := by
  unfold continueOrRecover at h
  by_cases hbacked : closeDriftReserveBacked driftReserve backing
  · exact hbacked
  · simp [hbacked] at h

/-- **§14 #46 (unbacked routes to recovery)**: when the backing
    predicate fails, the outcome is provably `routedToRecovery` —
    never `continued`. -/
theorem continueOrRecover_unbacked_routes_recovery
    (l : CloseLedger) (driftReserve : Nat) (backing : DriftBacking)
    (amount : Nat)
    (h : ¬ closeDriftReserveBacked driftReserve backing) :
    (continueOrRecover l driftReserve backing amount).isRecovery = true := by
  unfold continueOrRecover ContinuationOutcome.isRecovery
  simp [h]

/-- **§14 #46 (closed-world dichotomy)**: every outcome is either a
    continuation or a recovery routing — no third "continue without
    routing" case. -/
theorem continueOrRecover_dichotomy
    (l : CloseLedger) (driftReserve : Nat) (backing : DriftBacking)
    (amount : Nat) :
    let outcome := continueOrRecover l driftReserve backing amount
    outcome.isContinued = true ∨ outcome.isRecovery = true := by
  unfold continueOrRecover
  by_cases hbacked : closeDriftReserveBacked driftReserve backing
  · simp [hbacked]
    cases hb : l.bookSupport amount with
    | none => simp [ContinuationOutcome.isContinued, ContinuationOutcome.isRecovery]
    | some _ => simp [ContinuationOutcome.isContinued, ContinuationOutcome.isRecovery]
  · simp [hbacked]
    simp [ContinuationOutcome.isContinued, ContinuationOutcome.isRecovery]

end CloseLedger

-- ============================================================================
-- §14 #52 (strengthened): PayoutFromCredit bound to AccountCapital action
-- ============================================================================

namespace AccountCapital

/-- **Attempt a payout** from a `PayoutFromCredit` decision against an
    `AccountCapital`. The action consumes the `payoutAmount` from
    capital — but `payoutAmount` is structurally bounded by
    `lienBackedAmount` (per the `payoutLe` field on `PayoutFromCredit`),
    so a soft-credit-only decision (lien-backed = 0) yields zero
    payout. -/
def attemptPayout (a : AccountCapital) (p : PayoutFromCredit) :
    Option (AccountCapital × Nat) :=
  if p.payoutAmount = 0 then none
  else if a.amount < p.payoutAmount then none
  else some ({ amount := a.amount - p.payoutAmount }, p.payoutAmount)

/-- **§14 #52 (soft-credit-only yields no payout)**: when the
    `PayoutFromCredit` has zero lien-backed amount, `payoutAmount` is
    forced to zero (by `payoutLe`), and `attemptPayout` returns
    `none` — the engine action does nothing.

    This is the binding the audit asked for: the engine path
    consumes `payoutAmount`, not `softCreditAmount`, and zero
    lien-backed implies zero payout. -/
theorem attemptPayout_none_when_only_soft_credit
    (a : AccountCapital) (p : PayoutFromCredit) (h : p.lienBackedAmount = 0) :
    a.attemptPayout p = none := by
  unfold attemptPayout
  have hzero : p.payoutAmount = 0 :=
    PayoutFromCredit.soft_credit_only_yields_zero_payout p h
  simp [hzero]

/-- **§14 #52 (positive payout requires lien backing)**: a successful
    `attemptPayout` proves `p.lienBackedAmount > 0`. The
    contrapositive of the no-soft-credit-payout theorem. -/
theorem attemptPayout_some_implies_lien_backed
    (a a' : AccountCapital) (p : PayoutFromCredit) (paid : Nat)
    (h : a.attemptPayout p = some (a', paid)) :
    0 < p.lienBackedAmount := by
  by_contra hnot
  push_neg at hnot
  have hzero : p.lienBackedAmount = 0 := Nat.le_zero.mp hnot
  have := attemptPayout_none_when_only_soft_credit a p hzero
  rw [this] at h
  cases h

/-- **§14 #52 (payout decrements capital by lien-backed quantum)**:
    a successful `attemptPayout` decrements capital by exactly
    `payoutAmount`, which is bounded by `lienBackedAmount`. Capital
    cannot be reduced by `softCreditAmount` — only by what the lien
    backs. -/
theorem attemptPayout_capital_decrement
    (a a' : AccountCapital) (p : PayoutFromCredit) (paid : Nat)
    (h : a.attemptPayout p = some (a', paid)) :
    a'.amount + paid = a.amount ∧ paid ≤ p.lienBackedAmount := by
  unfold attemptPayout at h
  by_cases hz : p.payoutAmount = 0
  · simp [hz] at h
  by_cases hlt : a.amount < p.payoutAmount
  · simp [hz, hlt] at h
  · simp [hz, hlt] at h
    obtain ⟨ha', hpaid⟩ := h
    push_neg at hlt
    refine ⟨?_, ?_⟩
    · rw [← ha', ← hpaid]
      change a.amount - p.payoutAmount + p.payoutAmount = a.amount
      omega
    · rw [← hpaid]
      exact p.payoutLe

end AccountCapital

-- ============================================================================
-- §14 #55 (strengthened): VaultSnapshot embeds into StockClasses
-- ============================================================================

namespace VaultSnapshot

/-- Embed a `VaultSnapshot` into a 10-class `StockClasses` partition.

    `loserCapital` and `winnerCapital` fold into `cTot` (the per-
    account capital aggregate). `bookedLoss` lands in
    `settlementRoundingResidue` (protocol-owned residue from the
    booking — the spec-aligned target for unallocated loss). The
    other eight classes are zero in the simplified vault snapshot. -/
def embed (s : VaultSnapshot) : StockClasses where
  cTot                       := s.loserCapital + s.winnerCapital
  insurance                  := 0
  cancelDepositEscrow        := 0
  pendingObligationEscrow    := 0
  closeStagedQuoteReserve    := 0
  resolvedPayoutEscrow       := 0
  explicitBackedLossReserve  := 0
  settlementRoundingResidue  := s.bookedLoss
  protocolFeePayable         := 0
  unallocatedProtocolSurplus := 0

/-- **§14 #55 (embed preserves senior invariant in 10-class form)**:
    when the source snapshot satisfies the 3-class senior invariant
    `vault = loserCapital + winnerCapital + bookedLoss`, the embedded
    `StockClasses` satisfies the 10-class reconciliation
    `vault = totalV`. -/
theorem embed_totalV_eq_vault (s : VaultSnapshot) (h : s.seniorInvariant) :
    s.embed.totalV = s.vault := by
  unfold seniorInvariant at h
  unfold embed StockClasses.totalV
  simp
  omega

/-- **§14 #55 (embed preserves reconciliation)**: if the snapshot's
    senior invariant holds, the embedded stock classes reconcile to
    the snapshot's vault — `StockClasses.reconciled` is satisfied. -/
theorem embed_reconciled (s : VaultSnapshot) (h : s.seniorInvariant) :
    s.embed.reconciled s.vault := by
  unfold StockClasses.reconciled
  exact (embed_totalV_eq_vault s h).symm

/-- **§14 #55 (consumeBacking lifts to embedded form)**: a
    backing-consumption transition preserves the embedded
    StockClasses's reconciliation. Combining
    `consumeBacking_preserves_seniorInvariant` (the 3-class proof)
    with `embed_reconciled` gives the 10-class statement. -/
theorem consumeBacking_embed_preserves_reconciled
    (s s' : VaultSnapshot) (amount : Nat)
    (hpre : s.seniorInvariant) (h : s.consumeBacking amount = some s') :
    s'.embed.reconciled s'.vault :=
  embed_reconciled s' (consumeBacking_preserves_seniorInvariant s s' amount hpre h)

/-- **§14 #55 (consumeBacking preserves vault in 10-class form)**:
    the embedded vault total is unchanged across the transition. -/
theorem consumeBacking_embed_preserves_totalV
    (s s' : VaultSnapshot) (amount : Nat)
    (hpre : s.seniorInvariant) (h : s.consumeBacking amount = some s') :
    s'.embed.totalV = s.embed.totalV := by
  have hvpre := embed_totalV_eq_vault s hpre
  have hvpost := embed_totalV_eq_vault s'
    (consumeBacking_preserves_seniorInvariant s s' amount hpre h)
  have hvault := consumeBacking_preserves_vault s s' amount h
  omega

end VaultSnapshot

end Percolator.Spec
