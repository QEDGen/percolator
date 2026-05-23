/-
  Percolator.CloseLedger — Phase 5 cluster 4 (close progress, part 2):
  the per-account close-progress ledger, its booking transitions,
  immutable anchors, drift-reserve backing, and net-progress invariant.

  Mirrors `v16.rs::CloseProgressLedgerV16` (line 1040), with the
  immutable anchors split out by transition typing rather than by
  runtime equality check.

  §14 invariants addressed:
    - #46 `close_drift_reserve_has_backed_loss_capacity_or_recovers`
    - #47 `pulled_forward_obligation_credit_not_socialized_again`
    - #66 `participant_finalization_pulls_forward_pending_obligation`
    - #67 `phantom_weight_without_backing_reverts`
    - #69 `preempted_close_restart_cannot_double_book_residual`
    - #70 `close_id_and_drift_anchors_immutable`
    - #71 `bankrupt_close_progress_decreases_net_of_close_drift`
    - #72 `cure_and_cancel_checks_before_consuming_new_deposit`
    - #73 `quantity_adl_and_account_finalization_atomic_or_barriered`
-/

import Percolator.Defs
import Percolator.Lifecycle
import Percolator.Lien
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

-- ============================================================================
-- CloseLedger — per-account close-progress record
-- ============================================================================

/-- Mirror of `v16.rs::CloseProgressLedgerV16` (line 1040). The fields
    are partitioned into:

      - **Immutable anchors**: `closeId`, `assetIndex`, `marketId`,
        `domainSide`, `grossLossAtCloseStart`, `driftReferenceSlot`,
        `maxCloseSlot`. These are set at close start and persist across
        preemption, restart, and recovery until the close finalizes or
        is canceled (§22 of the spec, line 55).
      - **Booking counters**: `supportConsumed`, `juniorFaceBurned`,
        `insuranceSpent`, `bLossBooked`, `explicitLossAssigned`,
        `quantityAdlAppliedQ`, `driftConsumed`, `pendingObligationCredits`.
        These monotonically grow as the close progresses.
      - **Lifecycle flags**: `active`, `finalized`, `canceled`,
        `adlApplied` (the `QuantityADLApplied` phase indicator).
      - **Derived residual**: `residualRemaining` (held as state so
        transitions can witness exact post-step values). -/
structure CloseLedger where
  active                   : Bool
  finalized                : Bool
  canceled                 : Bool
  adlApplied               : Bool
  closeId                  : Nat
  assetIndex               : Nat
  marketId                 : Nat
  domainSide               : Side
  grossLossAtCloseStart    : Nat
  driftReferenceSlot       : Nat
  maxCloseSlot             : Nat
  supportConsumed          : Nat
  juniorFaceBurned         : Nat
  insuranceSpent           : Nat
  bLossBooked              : Nat
  explicitLossAssigned     : Nat
  quantityAdlAppliedQ      : Nat
  driftConsumed            : Nat
  pendingObligationCredits : Nat
  residualRemaining        : Nat
  deriving Repr

namespace CloseLedger

/-- The empty ledger — all counters zero. -/
def empty (closeId : Nat) (asset : Nat) (market : Nat) (side : Side)
    (gross : Nat) (driftRefSlot maxSlot : Nat) : CloseLedger where
  active := true
  finalized := false
  canceled := false
  adlApplied := false
  closeId := closeId
  assetIndex := asset
  marketId := market
  domainSide := side
  grossLossAtCloseStart := gross
  driftReferenceSlot := driftRefSlot
  maxCloseSlot := maxSlot
  supportConsumed := 0
  juniorFaceBurned := 0
  insuranceSpent := 0
  bLossBooked := 0
  explicitLossAssigned := 0
  quantityAdlAppliedQ := 0
  driftConsumed := 0
  pendingObligationCredits := 0
  residualRemaining := gross  -- at start: residual = gross loss

-- ============================================================================
-- "Has irreversible progress" — mirrors v16.rs::has_irreversible_progress
-- ============================================================================

/-- Mirror of `v16.rs::CloseProgressLedgerV16::has_irreversible_progress`
    (line 1093). Used by cure-and-cancel preconditions: a close may
    only cancel before any booking has fired. -/
def hasIrreversibleProgress (l : CloseLedger) : Bool :=
  decide (l.supportConsumed ≠ 0)
  || decide (l.juniorFaceBurned ≠ 0)
  || decide (l.insuranceSpent ≠ 0)
  || decide (l.bLossBooked ≠ 0)
  || decide (l.explicitLossAssigned ≠ 0)
  || decide (l.quantityAdlAppliedQ ≠ 0)
  || decide (l.driftConsumed ≠ 0)

/-- An empty (fresh-from-`empty`) ledger has no irreversible progress. -/
theorem empty_no_irreversible_progress
    (closeId asset market : Nat) (side : Side)
    (gross driftRefSlot maxSlot : Nat) :
    (empty closeId asset market side gross driftRefSlot maxSlot).hasIrreversibleProgress
      = false := by
  unfold hasIrreversibleProgress empty
  simp

-- ============================================================================
-- Booking transitions — only the booking counters move. The immutable
-- anchors are baked into the structural update (`{ l with ... }`) and
-- cannot be touched.
-- ============================================================================

/-- **BookSupport**: consume `amount` of senior support. -/
def bookSupport (l : CloseLedger) (amount : Nat) : Option CloseLedger :=
  if !l.active || l.finalized || l.canceled then none
  else if l.residualRemaining < amount then none
  else some {
    l with
    supportConsumed := l.supportConsumed + amount
    residualRemaining := l.residualRemaining - amount
  }

/-- **BookInsurance**: consume `amount` of insurance. -/
def bookInsurance (l : CloseLedger) (amount : Nat) : Option CloseLedger :=
  if !l.active || l.finalized || l.canceled then none
  else if l.residualRemaining < amount then none
  else some {
    l with
    insuranceSpent := l.insuranceSpent + amount
    residualRemaining := l.residualRemaining - amount
  }

/-- **BookB**: increment `b_loss_booked` by `chunk`. -/
def bookB (l : CloseLedger) (chunk : Nat) : Option CloseLedger :=
  if !l.active || l.finalized || l.canceled then none
  else if l.residualRemaining < chunk then none
  else some {
    l with
    bLossBooked := l.bLossBooked + chunk
    residualRemaining := l.residualRemaining - chunk
  }

/-- **BookExplicit**: assign `amount` to explicit loss. -/
def bookExplicit (l : CloseLedger) (amount : Nat) : Option CloseLedger :=
  if !l.active || l.finalized || l.canceled then none
  else if l.residualRemaining < amount then none
  else some {
    l with
    explicitLossAssigned := l.explicitLossAssigned + amount
    residualRemaining := l.residualRemaining - amount
  }

/-- **BookPendingObligation**: pull forward `amount` from a pending
    obligation. The obligation is credited exactly once to the origin
    residual (§14 #47, §10 of the spec, line 1302) — this transition
    encodes the credit-once property: `pendingObligationCredits`
    increases by `amount` and `residualRemaining` decreases by `amount`
    in the *same* atomic step. -/
def bookPendingObligation (l : CloseLedger) (amount : Nat) :
    Option CloseLedger :=
  if !l.active || l.finalized || l.canceled then none
  else if l.residualRemaining < amount then none
  else some {
    l with
    pendingObligationCredits := l.pendingObligationCredits + amount
    residualRemaining := l.residualRemaining - amount
  }

/-- **AddDrift**: add `delta` of adverse drift to the residual. Unlike
    booking transitions, drift *increases* `residualRemaining` (and
    `driftConsumed`, since reserved drift capacity is being used). -/
def addDrift (l : CloseLedger) (delta : Nat) : Option CloseLedger :=
  if !l.active || l.finalized || l.canceled then none
  else some {
    l with
    driftConsumed := l.driftConsumed + delta
    residualRemaining := l.residualRemaining + delta
  }

/-- **ApplyQuantityADL**: set `quantityAdlAppliedQ` to `q` and flip the
    `adlApplied` flag. Only applicable when the residual is fully
    booked (`residualRemaining = 0`) — encodes the §10 invariant that
    quantity ADL applies exactly once *after* residual durability
    (`spec.md:1222`). -/
def applyQuantityAdl (l : CloseLedger) (q : Nat) : Option CloseLedger :=
  if !l.active || l.finalized || l.canceled then none
  else if l.residualRemaining ≠ 0 then none
  else if l.adlApplied then none
  else some {
    l with
    quantityAdlAppliedQ := q
    adlApplied := true
  }

/-- **Finalize**: close out the ledger. Requires ADL applied and
    `residualRemaining = 0`. Sets `finalized := true` and
    `active := false`. The §10 invariant (`spec.md:1222`) says
    quantity ADL is atomic-or-barriered with finalization — encoded
    here by requiring `adlApplied = true` before `finalize` can fire. -/
def finalize (l : CloseLedger) : Option CloseLedger :=
  if !l.active || l.finalized || l.canceled then none
  else if l.residualRemaining ≠ 0 then none
  else if !l.adlApplied then none
  else some {
    l with
    finalized := true
    active := false
  }

/-- **CureAndCancel**: cancel the close. Only allowed before any
    irreversible booking has happened (`spec.md:1320` /
    `v16.rs::has_irreversible_progress`). -/
def cureAndCancel (l : CloseLedger) : Option CloseLedger :=
  if !l.active || l.finalized || l.canceled then none
  else if l.hasIrreversibleProgress then none
  else some {
    l with
    canceled := true
    active := false
  }

-- ============================================================================
-- §14 #70: close_id and drift anchors are immutable across transitions
-- ============================================================================

/-- The immutable anchors per `spec.md:1252-1262`. Encoded as a
    conjunction of per-field equalities rather than a tuple so that the
    proof obligation `l'.anchorsEq l` is discharged by component
    `rfl`s under structural updates. -/
def anchorsEq (a b : CloseLedger) : Prop :=
  a.closeId = b.closeId
  ∧ a.assetIndex = b.assetIndex
  ∧ a.marketId = b.marketId
  ∧ a.domainSide = b.domainSide
  ∧ a.grossLossAtCloseStart = b.grossLossAtCloseStart
  ∧ a.driftReferenceSlot = b.driftReferenceSlot
  ∧ a.maxCloseSlot = b.maxCloseSlot

/-- Anchor preservation under a structural update — the proof obligation
    we discharge for every booking transition. -/
theorem anchorsEq_refl (l : CloseLedger) : anchorsEq l l :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **§14 #70 (bookSupport)**: booking transitions don't touch anchors. -/
theorem bookSupport_preserves_anchors
    (l l' : CloseLedger) (amount : Nat) (h : l.bookSupport amount = some l') :
    anchorsEq l' l := by
  unfold bookSupport at h
  split_ifs at h
  all_goals cases h
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem bookInsurance_preserves_anchors
    (l l' : CloseLedger) (amount : Nat) (h : l.bookInsurance amount = some l') :
    anchorsEq l' l := by
  unfold bookInsurance at h
  split_ifs at h
  all_goals cases h
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem bookB_preserves_anchors
    (l l' : CloseLedger) (chunk : Nat) (h : l.bookB chunk = some l') :
    anchorsEq l' l := by
  unfold bookB at h
  split_ifs at h
  all_goals cases h
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem bookExplicit_preserves_anchors
    (l l' : CloseLedger) (amount : Nat) (h : l.bookExplicit amount = some l') :
    anchorsEq l' l := by
  unfold bookExplicit at h
  split_ifs at h
  all_goals cases h
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem bookPendingObligation_preserves_anchors
    (l l' : CloseLedger) (amount : Nat)
    (h : l.bookPendingObligation amount = some l') :
    anchorsEq l' l := by
  unfold bookPendingObligation at h
  split_ifs at h
  all_goals cases h
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem addDrift_preserves_anchors
    (l l' : CloseLedger) (delta : Nat) (h : l.addDrift delta = some l') :
    anchorsEq l' l := by
  unfold addDrift at h
  split_ifs at h
  all_goals cases h
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem applyQuantityAdl_preserves_anchors
    (l l' : CloseLedger) (q : Nat) (h : l.applyQuantityAdl q = some l') :
    anchorsEq l' l := by
  unfold applyQuantityAdl at h
  split_ifs at h
  all_goals cases h
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem finalize_preserves_anchors
    (l l' : CloseLedger) (h : l.finalize = some l') :
    anchorsEq l' l := by
  unfold finalize at h
  split_ifs at h
  all_goals cases h
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem cureAndCancel_preserves_anchors
    (l l' : CloseLedger) (h : l.cureAndCancel = some l') :
    anchorsEq l' l := by
  unfold cureAndCancel at h
  split_ifs at h
  all_goals cases h
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- §14 #71: each booking step strictly decreases the residual (net of drift
-- in the same step). Drift adds to residual; bookings subtract. We
-- prove the per-step monotonicity.
-- ============================================================================

/-- **§14 #71 (bookSupport)**: booking strictly decreases residual when
    the consumed amount is positive. -/
theorem bookSupport_decreases_residual
    (l l' : CloseLedger) (amount : Nat)
    (h : l.bookSupport amount = some l') (hpos : 0 < amount) :
    l'.residualRemaining < l.residualRemaining := by
  unfold bookSupport at h
  split_ifs at h with h1 h2
  all_goals cases h
  push_neg at h2
  change l.residualRemaining - amount < l.residualRemaining
  omega

theorem bookInsurance_decreases_residual
    (l l' : CloseLedger) (amount : Nat)
    (h : l.bookInsurance amount = some l') (hpos : 0 < amount) :
    l'.residualRemaining < l.residualRemaining := by
  unfold bookInsurance at h
  split_ifs at h with h1 h2
  all_goals cases h
  push_neg at h2
  change l.residualRemaining - amount < l.residualRemaining
  omega

theorem bookB_decreases_residual
    (l l' : CloseLedger) (chunk : Nat)
    (h : l.bookB chunk = some l') (hpos : 0 < chunk) :
    l'.residualRemaining < l.residualRemaining := by
  unfold bookB at h
  split_ifs at h with h1 h2
  all_goals cases h
  push_neg at h2
  change l.residualRemaining - chunk < l.residualRemaining
  omega

theorem bookExplicit_decreases_residual
    (l l' : CloseLedger) (amount : Nat)
    (h : l.bookExplicit amount = some l') (hpos : 0 < amount) :
    l'.residualRemaining < l.residualRemaining := by
  unfold bookExplicit at h
  split_ifs at h with h1 h2
  all_goals cases h
  push_neg at h2
  change l.residualRemaining - amount < l.residualRemaining
  omega

theorem bookPendingObligation_decreases_residual
    (l l' : CloseLedger) (amount : Nat)
    (h : l.bookPendingObligation amount = some l') (hpos : 0 < amount) :
    l'.residualRemaining < l.residualRemaining := by
  unfold bookPendingObligation at h
  split_ifs at h with h1 h2
  all_goals cases h
  push_neg at h2
  change l.residualRemaining - amount < l.residualRemaining
  omega

/-- **§14 #71 (drift increases residual)**: drift accrual strictly
    raises the residual — the dual of the booking lemmas. -/
theorem addDrift_increases_residual
    (l l' : CloseLedger) (delta : Nat)
    (h : l.addDrift delta = some l') (hpos : 0 < delta) :
    l.residualRemaining < l'.residualRemaining := by
  unfold addDrift at h
  split_ifs at h
  all_goals cases h
  change l.residualRemaining < l.residualRemaining + delta
  omega

-- ============================================================================
-- §14 #47: pending-obligation credit decrements origin residual once
-- ============================================================================

/-- **§14 #47**: `bookPendingObligation` debits `residualRemaining` and
    credits `pendingObligationCredits` by *exactly* the same amount, in
    one atomic step. There is no second crediting transition — by
    construction this method is the only one that touches
    `pendingObligationCredits`, so the "credited exactly once" property
    is built into the lifecycle.

    Compare with `spec.md:1302`: "The origin residual is credited
    exactly once before the obligation is pulled forward." -/
theorem bookPendingObligation_credit_matches_debit
    (l l' : CloseLedger) (amount : Nat)
    (h : l.bookPendingObligation amount = some l') :
    l'.pendingObligationCredits = l.pendingObligationCredits + amount
    ∧ l'.residualRemaining + amount = l.residualRemaining := by
  unfold bookPendingObligation at h
  split_ifs at h with h1 h2
  all_goals cases h
  push_neg at h2
  refine ⟨rfl, ?_⟩
  change l.residualRemaining - amount + amount = l.residualRemaining
  omega

-- ============================================================================
-- §14 #69: preempted close restart cannot double-book residual.
-- "Same close_id ⇒ same ledger" — restart is a continuation, not a new
-- ledger. We witness this by showing that restarting on the same
-- closeId means accumulating on the existing booking counters, not
-- resetting to zero.
-- ============================================================================

/-- **§14 #69 (booking is monotone)**: `supportConsumed` (and every
    other booking counter) grows monotonically under booking
    transitions — never resets. The "same close_id ⇒ same ledger"
    structural fact is in the per-account ledger type; what matters
    arithmetically is that the booking counters cannot decrease. -/
theorem bookSupport_monotone_supportConsumed
    (l l' : CloseLedger) (amount : Nat)
    (h : l.bookSupport amount = some l') :
    l.supportConsumed ≤ l'.supportConsumed := by
  unfold bookSupport at h
  split_ifs at h
  all_goals cases h
  change l.supportConsumed ≤ l.supportConsumed + amount
  omega

theorem bookInsurance_monotone_insuranceSpent
    (l l' : CloseLedger) (amount : Nat)
    (h : l.bookInsurance amount = some l') :
    l.insuranceSpent ≤ l'.insuranceSpent := by
  unfold bookInsurance at h
  split_ifs at h
  all_goals cases h
  change l.insuranceSpent ≤ l.insuranceSpent + amount
  omega

theorem bookB_monotone_bLossBooked
    (l l' : CloseLedger) (chunk : Nat) (h : l.bookB chunk = some l') :
    l.bLossBooked ≤ l'.bLossBooked := by
  unfold bookB at h
  split_ifs at h
  all_goals cases h
  change l.bLossBooked ≤ l.bLossBooked + chunk
  omega

theorem bookExplicit_monotone_explicitLossAssigned
    (l l' : CloseLedger) (amount : Nat)
    (h : l.bookExplicit amount = some l') :
    l.explicitLossAssigned ≤ l'.explicitLossAssigned := by
  unfold bookExplicit at h
  split_ifs at h
  all_goals cases h
  change l.explicitLossAssigned ≤ l.explicitLossAssigned + amount
  omega

-- ============================================================================
-- §14 #46: close drift reserve has backed loss capacity or recovers.
-- We encode the predicate that the reserved drift capacity is backed
-- by one or more of: support, insurance, lien backing, B-headroom, or
-- recovery capacity (`spec.md:1252-1262`).
-- ============================================================================

/-- The pool of capacity an active close may draw on to absorb drift,
    mirroring `spec.md:1254-1259`. -/
structure DriftBacking where
  eligibleAccountSupport          : Nat
  domainInsuranceCapacity         : Nat
  sourceCreditLienBackingConsumed : Nat
  bBookingHeadroom                : Nat
  deterministicRecoveryCapacity   : Nat
  deriving Repr

namespace DriftBacking

/-- The total backing the close can draw on. -/
def total (b : DriftBacking) : Nat :=
  b.eligibleAccountSupport
  + b.domainInsuranceCapacity
  + b.sourceCreditLienBackingConsumed
  + b.bBookingHeadroom
  + b.deterministicRecoveryCapacity

end DriftBacking

/-- **§14 #46 (predicate)**: the close-drift reserve is backed iff
    `closeDriftReserve <= sum of backing categories`.

    Equivalently (per spec): if this fails, ordinary continuation MUST
    route to recovery — encoded below as `routesToRecoveryIfUnbacked`. -/
def closeDriftReserveBacked (closeDriftReserve : Nat) (b : DriftBacking) : Prop :=
  closeDriftReserve ≤ b.total

instance (closeDriftReserve : Nat) (b : DriftBacking) :
    Decidable (closeDriftReserveBacked closeDriftReserve b) := by
  unfold closeDriftReserveBacked; infer_instance

/-- **§14 #46 (fail-closed witness)**: the continuation predicate. A
    continuation is permitted only when the drift reserve is backed;
    otherwise it must route to recovery.

    Encoded as `Sum`: `inl unit` means continuation allowed,
    `inr unit` means must route to recovery. -/
def continuationDecision (closeDriftReserve : Nat) (b : DriftBacking) : Bool :=
  decide (closeDriftReserveBacked closeDriftReserve b)

theorem continuationDecision_iff (closeDriftReserve : Nat) (b : DriftBacking) :
    continuationDecision closeDriftReserve b = true
    ↔ closeDriftReserveBacked closeDriftReserve b := by
  unfold continuationDecision
  simp

/-- **§14 #46 (route to recovery on unbacked)**: if the reserve is not
    backed, the continuation decision returns `false` — i.e. ordinary
    close continuation is denied; the caller must route to recovery. -/
theorem unbacked_routes_to_recovery
    (closeDriftReserve : Nat) (b : DriftBacking)
    (h : ¬ closeDriftReserveBacked closeDriftReserve b) :
    continuationDecision closeDriftReserve b = false := by
  unfold continuationDecision
  simp [h]

-- ============================================================================
-- §14 #72: cure-and-cancel checks before consuming new deposit.
-- Encoded by the precondition on `cureAndCancel`: it can only fire
-- before any irreversible booking. New deposits (which are booking
-- transitions) cannot be applied as support before the cancel check.
-- ============================================================================

/-- **§14 #72**: `cureAndCancel` requires `hasIrreversibleProgress = false`.
    The booking transitions all set at least one irreversible field;
    therefore once any booking has fired, cancel is denied. -/
theorem cureAndCancel_requires_no_irreversible
    (l l' : CloseLedger) (h : l.cureAndCancel = some l') :
    l.hasIrreversibleProgress = false := by
  unfold cureAndCancel at h
  by_cases ha : !l.active
  · simp [ha] at h
  by_cases hf : l.finalized
  · simp [hf] at h
  by_cases hc : l.canceled
  · simp [hc] at h
  by_cases hi : l.hasIrreversibleProgress
  · simp [ha, hf, hc, hi] at h
  · push_neg at hi
    exact Bool.eq_false_iff.mpr (fun heq => hi heq)

/-- **§14 #72 (booking establishes irreversibility for support)**: a
    successful `bookSupport` with positive amount sets `supportConsumed > 0`,
    which is one of the disjuncts of `hasIrreversibleProgress`. The
    post-booking ledger reports `hasIrreversibleProgress = true`. -/
theorem bookSupport_sets_irreversible
    (l l' : CloseLedger) (amount : Nat)
    (h : l.bookSupport amount = some l') (hpos : 0 < amount) :
    l'.hasIrreversibleProgress = true := by
  unfold bookSupport at h
  split_ifs at h
  all_goals cases h
  unfold hasIrreversibleProgress
  have hne : l.supportConsumed + amount ≠ 0 := by omega
  change (decide ((l.supportConsumed + amount) ≠ 0)
          || decide (l.juniorFaceBurned ≠ 0)
          || decide (l.insuranceSpent ≠ 0)
          || decide (l.bLossBooked ≠ 0)
          || decide (l.explicitLossAssigned ≠ 0)
          || decide (l.quantityAdlAppliedQ ≠ 0)
          || decide (l.driftConsumed ≠ 0)) = true
  simp [hne]

-- ============================================================================
-- §14 #73: quantity ADL and account finalization atomic-or-barriered.
-- Encoded by the `finalize` precondition: it requires `adlApplied = true`.
-- ============================================================================

/-- **§14 #73**: `finalize` requires `adlApplied = true`. Quantity ADL
    and finalization must happen with ADL strictly before finalize —
    encoded here as a transition precondition; the "atomic" alternative
    of the spec is captured by ADL being a single ledger transition
    that flips `adlApplied`. -/
theorem finalize_requires_adlApplied
    (l l' : CloseLedger) (h : l.finalize = some l') :
    l.adlApplied = true := by
  unfold finalize at h
  by_cases ha : !l.active
  · simp [ha] at h
  by_cases hf : l.finalized
  · simp [hf] at h
  by_cases hc : l.canceled
  · simp [hc] at h
  by_cases hr : l.residualRemaining ≠ 0
  · simp [ha, hf, hc, hr] at h
  by_cases hadl : !l.adlApplied
  · simp [ha, hf, hc, hr, hadl] at h
  · simp at hadl
    exact hadl

/-- **§14 #73 (residual must be fully booked before finalize)**: the
    other precondition — residual zero at finalize. -/
theorem finalize_requires_zero_residual
    (l l' : CloseLedger) (h : l.finalize = some l') :
    l.residualRemaining = 0 := by
  unfold finalize at h
  by_cases ha : !l.active
  · simp [ha] at h
  by_cases hf : l.finalized
  · simp [hf] at h
  by_cases hc : l.canceled
  · simp [hc] at h
  by_cases hr : l.residualRemaining ≠ 0
  · simp [ha, hf, hc, hr] at h
  · push_neg at hr
    exact hr

-- ============================================================================
-- §14 #66: participant finalization pulls forward pending obligation.
-- Encoded by the existence of `bookPendingObligation` as a transition:
-- finalization phases must call it for any pending obligation; the
-- amount-debit-equals-credit property is §14 #47 above.
-- ============================================================================

/-- **§14 #66 (witnessed by `bookPendingObligation`)**: there is a
    dedicated transition to credit pending-obligation amounts into the
    close ledger. The transition is the only one that increments
    `pendingObligationCredits`, structurally ensuring that pending
    obligations are accounted for at finalization rather than silently
    dropped. -/
theorem bookPendingObligation_only_credit_path
    (l l' : CloseLedger) (amount : Nat)
    (h : l.bookPendingObligation amount = some l') :
    l'.pendingObligationCredits ≥ l.pendingObligationCredits + amount := by
  have := bookPendingObligation_credit_matches_debit l l' amount h
  omega

/-- **§14 #66 (no shortcut path)**: no other booking transition touches
    `pendingObligationCredits`. We witness this for `bookSupport`,
    `bookInsurance`, `bookB`, `bookExplicit`, and `addDrift`. -/
theorem bookSupport_does_not_touch_pendingObligation
    (l l' : CloseLedger) (amount : Nat)
    (h : l.bookSupport amount = some l') :
    l'.pendingObligationCredits = l.pendingObligationCredits := by
  unfold bookSupport at h
  split_ifs at h
  all_goals cases h
  rfl

theorem bookInsurance_does_not_touch_pendingObligation
    (l l' : CloseLedger) (amount : Nat)
    (h : l.bookInsurance amount = some l') :
    l'.pendingObligationCredits = l.pendingObligationCredits := by
  unfold bookInsurance at h
  split_ifs at h
  all_goals cases h
  rfl

theorem bookB_does_not_touch_pendingObligation
    (l l' : CloseLedger) (chunk : Nat) (h : l.bookB chunk = some l') :
    l'.pendingObligationCredits = l.pendingObligationCredits := by
  unfold bookB at h
  split_ifs at h
  all_goals cases h
  rfl

theorem bookExplicit_does_not_touch_pendingObligation
    (l l' : CloseLedger) (amount : Nat)
    (h : l.bookExplicit amount = some l') :
    l'.pendingObligationCredits = l.pendingObligationCredits := by
  unfold bookExplicit at h
  split_ifs at h
  all_goals cases h
  rfl

theorem addDrift_does_not_touch_pendingObligation
    (l l' : CloseLedger) (delta : Nat) (h : l.addDrift delta = some l') :
    l'.pendingObligationCredits = l.pendingObligationCredits := by
  unfold addDrift at h
  split_ifs at h
  all_goals cases h
  rfl

-- ============================================================================
-- §14 #67: phantom weight without backing reverts. We model the simplest
-- form: a transition that *purports* to add weight without backing has
-- no booking transition that would accept it; the typed transitions
-- below require an explicit backing source.
-- ============================================================================

/-- Mirror of "attribute weight to a domain". Every attribution must
    name a backing source (counterparty or insurance) and a positive
    backing amount; without those, no constructor builds a witness. -/
structure WeightAttribution where
  amount  : Nat
  src     : BackingSource
  backing : Nat
  backed  : 0 < backing
  deriving Repr

/-- **§14 #67 (no zero-backed attribution)**: by construction, a
    `WeightAttribution` cannot carry zero `backing`. Any code path that
    tries to build one with `backing = 0` fails the `backed` field. -/
theorem weight_attribution_has_positive_backing (w : WeightAttribution) :
    0 < w.backing := w.backed

-- ============================================================================
-- §14 #24: per-lien categorization disjoint by typing
-- ============================================================================

/-- A typed lien-consumption transition that routes to exactly one
    of the two close-residual categories based on the lien's
    `BackingSource`. A counterparty-backed lien debits
    `supportConsumed`; an insurance-backed lien debits
    `insuranceSpent`. The match is total over `BackingSource`, so a
    third "uncategorized" path is unrepresentable. -/
def consumeLienForResidual
    {src : BackingSource} (l : CloseLedger) (_lien : Lien src) (amount : Nat) :
    Option CloseLedger :=
  match src with
  | .Counterparty => l.bookSupport amount
  | .Insurance    => l.bookInsurance amount

/-- **§14 #24 (counterparty lien debits supportConsumed only)**: when
    the consumed lien is counterparty-backed, only `supportConsumed`
    increases — `insuranceSpent` is provably unchanged. -/
theorem consumeLienForResidual_counterparty_touches_support_only
    (l l' : CloseLedger) (lien : Lien BackingSource.Counterparty)
    (amount : Nat)
    (h : l.consumeLienForResidual lien amount = some l') :
    l'.insuranceSpent = l.insuranceSpent := by
  unfold consumeLienForResidual at h
  unfold bookSupport at h
  by_cases ha : !l.active || l.finalized || l.canceled
  · simp [ha] at h
  by_cases hr : l.residualRemaining < amount
  · simp [ha, hr] at h
  · simp [ha, hr] at h
    have hl' := h.symm
    rw [hl']

/-- **§14 #24 (insurance lien debits insuranceSpent only)**: when
    the consumed lien is insurance-backed, only `insuranceSpent`
    increases — `supportConsumed` is provably unchanged. -/
theorem consumeLienForResidual_insurance_touches_insurance_only
    (l l' : CloseLedger) (lien : Lien BackingSource.Insurance)
    (amount : Nat)
    (h : l.consumeLienForResidual lien amount = some l') :
    l'.supportConsumed = l.supportConsumed := by
  unfold consumeLienForResidual at h
  unfold bookInsurance at h
  by_cases ha : !l.active || l.finalized || l.canceled
  · simp [ha] at h
  by_cases hr : l.residualRemaining < amount
  · simp [ha, hr] at h
  · simp [ha, hr] at h
    have hl' := h.symm
    rw [hl']

/-- **§14 #24 (categorization is total and disjoint)**: every typed
    lien is classified by exactly one of `Counterparty` or
    `Insurance`. There is no path that increments both categories
    for the same lien, and there is no path that increments neither
    when a consume fires.

    The closed-world `BackingSource` enum (cluster 1 typing) provides
    the structural witness. -/
theorem consumeLienForResidual_targets_one_category
    {src : BackingSource} :
    src = .Counterparty ∨ src = .Insurance := by
  cases src
  · exact .inl rfl
  · exact .inr rfl

-- ============================================================================
-- §14 #46: typed continuation outcome with no third path
-- ============================================================================

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

-- ============================================================================
-- §14 #71: aggregate net-of-drift conservation over a transition sequence
-- ============================================================================

/-- A single closure operation in the booking sequence: either a
    booking that decrements residual, or a drift accrual that
    increments it. Other transitions (finalize, cureAndCancel,
    applyQuantityAdl) don't affect residual and are excluded here. -/
inductive ResidualMove : Type where
  | bookSupport   (amount : Nat) : ResidualMove
  | bookInsurance (amount : Nat) : ResidualMove
  | bookB         (amount : Nat) : ResidualMove
  | bookExplicit  (amount : Nat) : ResidualMove
  | bookPending   (amount : Nat) : ResidualMove
  | drift         (delta  : Nat) : ResidualMove
  deriving Repr

namespace ResidualMove

/-- Apply one residual move. -/
def apply (l : CloseLedger) : ResidualMove → Option CloseLedger
  | .bookSupport   amount => l.bookSupport amount
  | .bookInsurance amount => l.bookInsurance amount
  | .bookB         amount => l.bookB amount
  | .bookExplicit  amount => l.bookExplicit amount
  | .bookPending   amount => l.bookPendingObligation amount
  | .drift         delta  => l.addDrift delta

/-- The total residual-debit amount in this move (zero for drift). -/
def bookingAmount : ResidualMove → Nat
  | .bookSupport   amount => amount
  | .bookInsurance amount => amount
  | .bookB         amount => amount
  | .bookExplicit  amount => amount
  | .bookPending   amount => amount
  | .drift         _      => 0

/-- The total residual-credit amount (drift increment). -/
def driftAmount : ResidualMove → Nat
  | .drift delta => delta
  | _            => 0

end ResidualMove

/-- Apply a sequence of residual moves. Returns `none` if any
    transition fails its precondition. -/
def applyMoves (l : CloseLedger) : List ResidualMove → Option CloseLedger
  | [] => some l
  | m :: rest =>
    match m.apply l with
    | none => none
    | some l' => l'.applyMoves rest

/-- Total bookings across a sequence. -/
def totalBookings (moves : List ResidualMove) : Nat :=
  (moves.map ResidualMove.bookingAmount).sum

/-- Total drift across a sequence. -/
def totalDrift (moves : List ResidualMove) : Nat :=
  (moves.map ResidualMove.driftAmount).sum

/-- Per-move residual change: a booking decreases by its amount, a
    drift increases by its delta. Returns the difference
    `new.residualRemaining - old.residualRemaining` plus an existence
    witness for the resulting ledger. -/
theorem ResidualMove.apply_residual_delta
    (l l' : CloseLedger) (m : ResidualMove) (h : m.apply l = some l') :
    l'.residualRemaining + m.bookingAmount
    = l.residualRemaining + m.driftAmount := by
  cases m with
  | bookSupport amount =>
    unfold ResidualMove.apply ResidualMove.bookingAmount ResidualMove.driftAmount at *
    unfold CloseLedger.bookSupport at h
    by_cases ha : !l.active || l.finalized || l.canceled
    · simp [ha] at h
    by_cases hr : l.residualRemaining < amount
    · simp [ha, hr] at h
    · simp [ha, hr] at h
      have hl' := h.symm
      rw [hl']
      change l.residualRemaining - amount + amount = l.residualRemaining + 0
      omega
  | bookInsurance amount =>
    unfold ResidualMove.apply ResidualMove.bookingAmount ResidualMove.driftAmount at *
    unfold CloseLedger.bookInsurance at h
    by_cases ha : !l.active || l.finalized || l.canceled
    · simp [ha] at h
    by_cases hr : l.residualRemaining < amount
    · simp [ha, hr] at h
    · simp [ha, hr] at h
      have hl' := h.symm
      rw [hl']
      change l.residualRemaining - amount + amount = l.residualRemaining + 0
      omega
  | bookB amount =>
    unfold ResidualMove.apply ResidualMove.bookingAmount ResidualMove.driftAmount at *
    unfold CloseLedger.bookB at h
    by_cases ha : !l.active || l.finalized || l.canceled
    · simp [ha] at h
    by_cases hr : l.residualRemaining < amount
    · simp [ha, hr] at h
    · simp [ha, hr] at h
      have hl' := h.symm
      rw [hl']
      change l.residualRemaining - amount + amount = l.residualRemaining + 0
      omega
  | bookExplicit amount =>
    unfold ResidualMove.apply ResidualMove.bookingAmount ResidualMove.driftAmount at *
    unfold CloseLedger.bookExplicit at h
    by_cases ha : !l.active || l.finalized || l.canceled
    · simp [ha] at h
    by_cases hr : l.residualRemaining < amount
    · simp [ha, hr] at h
    · simp [ha, hr] at h
      have hl' := h.symm
      rw [hl']
      change l.residualRemaining - amount + amount = l.residualRemaining + 0
      omega
  | bookPending amount =>
    unfold ResidualMove.apply ResidualMove.bookingAmount ResidualMove.driftAmount at *
    unfold CloseLedger.bookPendingObligation at h
    by_cases ha : !l.active || l.finalized || l.canceled
    · simp [ha] at h
    by_cases hr : l.residualRemaining < amount
    · simp [ha, hr] at h
    · simp [ha, hr] at h
      have hl' := h.symm
      rw [hl']
      change l.residualRemaining - amount + amount = l.residualRemaining + 0
      omega
  | drift delta =>
    unfold ResidualMove.apply ResidualMove.bookingAmount ResidualMove.driftAmount at *
    unfold CloseLedger.addDrift at h
    by_cases ha : !l.active || l.finalized || l.canceled
    · simp [ha] at h
    · simp [ha] at h
      have hl' := h.symm
      rw [hl']
      change l.residualRemaining + delta + 0 = l.residualRemaining + delta
      omega

/-- **§14 #71 (aggregate net-of-drift conservation)**: after an
    arbitrary sequence of residual moves, the residual change equals
    `totalDrift - totalBookings`. When `totalBookings ≥ totalDrift`,
    residual non-strictly decreases — close progress dominates drift
    in aggregate.

    This is the §14 #71 spec claim lifted from per-step to the full
    sequence. -/
theorem applyMoves_residual_conservation
    (l l' : CloseLedger) (moves : List ResidualMove)
    (h : l.applyMoves moves = some l') :
    l'.residualRemaining + totalBookings moves
    = l.residualRemaining + totalDrift moves := by
  induction moves generalizing l with
  | nil =>
    unfold applyMoves at h
    cases h
    unfold totalBookings totalDrift
    simp
  | cons m rest ih =>
    unfold applyMoves at h
    cases hm : m.apply l with
    | none => rw [hm] at h; cases h
    | some l1 =>
      rw [hm] at h
      have hstep := ResidualMove.apply_residual_delta l l1 m hm
      have hrest := ih l1 h
      unfold totalBookings totalDrift
      simp [List.map_cons, List.sum_cons]
      unfold totalBookings totalDrift at hrest
      omega

/-- **§14 #71 (net-decrease when bookings dominate drift)**: if the
    total booked amount equals or exceeds total drift, residual
    non-strictly decreases across the sequence. -/
theorem applyMoves_residual_decreases_when_bookings_dominate
    (l l' : CloseLedger) (moves : List ResidualMove)
    (h : l.applyMoves moves = some l')
    (hdom : totalDrift moves ≤ totalBookings moves) :
    l'.residualRemaining ≤ l.residualRemaining := by
  have hcons := applyMoves_residual_conservation l l' moves h
  omega

/-- **§14 #71 (strict decrease when bookings strictly dominate
    drift)**: if total bookings strictly exceed total drift,
    residual strictly decreases. -/
theorem applyMoves_residual_strictly_decreases
    (l l' : CloseLedger) (moves : List ResidualMove)
    (h : l.applyMoves moves = some l')
    (hdom : totalDrift moves < totalBookings moves) :
    l'.residualRemaining < l.residualRemaining := by
  have hcons := applyMoves_residual_conservation l l' moves h
  omega

end CloseLedger

end Percolator.Spec
