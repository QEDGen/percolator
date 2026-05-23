/-
  Percolator.StrengthenedClosures — second pass on three audit-flagged
  partials from `AUDIT_2026-05-22.md`.

  §14 invariants strengthened in this file:
    - #38 `lien_consumption_removes_backing_from_fresh_reserved_and_claim_bound`
          (audit: prior closure covered fresh_reserved drop only;
           this file adds the claim_bound drop and a joint theorem)
    - #71 `bankrupt_close_progress_decreases_net_of_close_drift`
          (audit: prior closure was per-step; this file adds the
           aggregate sequence theorem showing total booked net of
           drift across an arbitrary transition sequence)
    - #90 `equity_side_penalties_disjoint_from_requirement_side_penalties`
          (audit: prior closure was field-level disjointness; this
           file adds a PenaltySource enum with category tags so
           each source provably maps to exactly one category)
-/

import Percolator.LienLifecycle
import Percolator.BackingBucket
import Percolator.CloseLedger
import Percolator.HealthTest
import Percolator.Spec14Aliases2
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

-- ============================================================================
-- §14 #38 (strengthened): joint fresh_reserved + claim_bound drop
-- ============================================================================

/-- **§14 #38 (joint statement)**: a lien consumption that targets
    both the bucket-level `validLiened` partition and the lien-level
    `faceClaimLockedNum` simultaneously decrements both by exactly
    the consumed amount.

    The prior closure proved only the bucket side
    (`consumeLien_removes_from_validLiened`). This strengthens by
    pairing it with the lien-side decrement
    (`Lien.consume_faceClaim_decrements` from cluster 1). -/
theorem lien_consumption_removes_fresh_reserved_and_claim_bound
    {src : BackingSource}
    (b b' : BackingBucket) (l l' : Lien src)
    (amount face : Nat) (effective : Nat)
    (hbucket : b.consumeLien amount = some b')
    (hlien   : l.consume face amount effective = some l') :
    b'.validLiened + amount = b.validLiened
    ∧ l'.faceClaimLockedNum + face = l.faceClaimLockedNum
    ∧ l'.backingReservedNum + amount = l.backingReservedNum := by
  refine ⟨?_, ?_, ?_⟩
  · exact (BackingBucket.consumeLien_removes_from_validLiened
            b b' amount hbucket).1
  · exact Lien.consume_faceClaim_decrements l face amount effective l' hlien
  · exact Lien.consume_backing_decrements l face amount effective l' hlien

/-- **§14 #38 (combined fresh-reserved sum drop)**: the bucket's
    `freshUnliened + validLiened` (the spec's "fresh_reserved_backing_num"
    for that bucket) decreases by `amount` when a consume fires —
    `freshUnliened` is untouched and `validLiened` drops by `amount`. -/
theorem BackingBucket.consumeLien_decreases_fresh_reserved_total
    (b b' : BackingBucket) (amount : Nat)
    (h : b.consumeLien amount = some b') :
    b'.freshUnliened + b'.validLiened + amount
    = b.freshUnliened + b.validLiened := by
  unfold consumeLien at h
  by_cases hlt : b.validLiened < amount
  · simp [hlt] at h
  · push_neg at hlt
    simp [hlt] at h
    have hb' := h.symm
    rw [hb']
    change b.freshUnliened + (b.validLiened - amount) + amount
         = b.freshUnliened + b.validLiened
    omega

-- ============================================================================
-- §14 #71 (strengthened): aggregate net-decrease over a transition sequence
-- ============================================================================

namespace CloseLedger

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

-- ============================================================================
-- §14 #90 (strengthened): PenaltySource enum with category tags
-- ============================================================================

/-- The classification of a penalty: does it deduct from equity or
    add to the maintenance requirement? Per spec these are disjoint
    sides of the health test. -/
inductive PenaltyCategory : Type where
  | equity      : PenaltyCategory
  | requirement : PenaltyCategory
  deriving DecidableEq, Repr

/-- A specific penalty source. Each source maps to exactly one
    `PenaltyCategory` and one `HealthInputs` field — the disjointness
    is established by definition. -/
inductive PenaltySource : Type where
  | lossExposure              : PenaltySource
  | lockedFaceClaim           : PenaltySource
  | pendingObligationExposure : PenaltySource
  | maintenanceRequirement    : PenaltySource
  deriving DecidableEq, Repr

namespace PenaltySource

/-- The category each source belongs to. -/
def category : PenaltySource → PenaltyCategory
  | .lossExposure              => .equity
  | .lockedFaceClaim           => .equity
  | .pendingObligationExposure => .equity
  | .maintenanceRequirement    => .requirement

/-- The contribution of each source to the health inputs. -/
def contributionOf (h : HealthInputs) : PenaltySource → Nat
  | .lossExposure              => h.lossExposure
  | .lockedFaceClaim           => h.lockedFaceClaim
  | .pendingObligationExposure => h.pendingObligationExposure
  | .maintenanceRequirement    => h.maintenanceRequirement

end PenaltySource

/-- The sum of contributions across a list of sources. -/
def HealthInputs.sumContributions
    (h : HealthInputs) (sources : List PenaltySource) : Nat :=
  (sources.map (PenaltySource.contributionOf h)).sum

/-- **§14 #90 (each source has exactly one category)**: the category
    function is total and deterministic — no source spans both equity
    and requirement sides. -/
theorem PenaltySource.category_total (s : PenaltySource) :
    s.category = .equity ∨ s.category = .requirement := by
  cases s
  all_goals (first | exact .inl rfl | exact .inr rfl)

/-- **§14 #90 (no source has both categories)**: the category function
    is a function (not a relation), so no source can simultaneously
    be equity and requirement. -/
theorem PenaltySource.category_unique
    (s : PenaltySource) (c1 c2 : PenaltyCategory)
    (h1 : s.category = c1) (h2 : s.category = c2) :
    c1 = c2 := by
  rw [← h1, ← h2]

/-- **§14 #90 (sum decomposition by category)**: the negative-equity
    formula equals the sum over the three equity-category sources
    plus the maintenance-requirement source. Each source contributes
    via `contributionOf` exactly once. -/
theorem HealthInputs.negativeEquity_eq_sum_by_category (h : HealthInputs) :
    h.negativeEquity
    = h.sumContributions [.lossExposure, .lockedFaceClaim, .pendingObligationExposure]
      + h.sumContributions [.maintenanceRequirement] := by
  unfold negativeEquity sumContributions
  simp [PenaltySource.contributionOf]
  omega

/-- **§14 #90 (equity-side sources have equity category)**: the three
    sources in the equity decomposition all map to `.equity`. -/
theorem PenaltySource.equity_sources_have_equity_category :
    PenaltySource.lossExposure.category = .equity
    ∧ PenaltySource.lockedFaceClaim.category = .equity
    ∧ PenaltySource.pendingObligationExposure.category = .equity := by
  refine ⟨rfl, rfl, rfl⟩

/-- **§14 #90 (requirement-side source has requirement category)**: the
    sole requirement-side source maps to `.requirement`. -/
theorem PenaltySource.requirement_source_has_requirement_category :
    PenaltySource.maintenanceRequirement.category = .requirement := rfl

/-- **§14 #90 (disjointness via category mismatch)**: an equity-side
    source's category is provably not equal to a requirement-side
    source's category. -/
theorem PenaltySource.equity_distinct_from_requirement
    (s : PenaltySource) (h : s.category = .equity) :
    s.category ≠ .requirement := by
  rw [h]
  intro contra
  cases contra

end Percolator.Spec
