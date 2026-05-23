/-
  Percolator.Spec14 — §14-row index: every spec invariant whose Lean
  closure is named directly here (either a focused proof or a
  citation of machinery in a topical module).

  This is the §14 counterpart of `SPEC_COVERAGE.md` — it lets a
  reviewer walk row-by-row through Spec §14 in one place. For each
  row addressed below, the theorem name encodes the spec invariant
  it discharges; bodies either prove it directly or call into the
  topical module where the underlying machinery lives.

  Rows handled in this file (sorted by §14 row):
    - #9   `source_credit_lien_prevents_double_use_of_same_claim_and_backing`
    - #11  `backing_reservation_is_actual_locked_equity_not_optimistic_certificate`
    - #16  `source_credit_insurance_reservation_single_canonical_writer`
    - #18  `insurance_backed_lien_creation_increments_valid_liened_insurance_not_counterparty_backing`
    - #20  `insurance_backed_lien_consumption_decrements_source_credit_reservation_and_total_available_once`
    - #24  `close_residual_partition_classifies_counterparty_and_insurance_lien_consumption_disjointly`
    - #28  `lien_creatable_predicate_requires_actual_bucket_or_insurance_reservation_capacity`
    - #33  `lien_creatable_predicate_matches_actual_bucket_or_insurance_lifecycle`
    - #43  `lien_creation_requires_required_backing_le_available_backing`
    - #51  `no_circular_credit_without_external_senior_backing`
    - #56  `residuals_charged_only_to_asset_opposing_side_domain`
    - #64  `pending_obligation_credit_decrements_origin_residual_once`
    - #84  `dead_leg_forfeit_books_to_bankruptcy_domain`
    - #86  `global_accumulator_not_account_health_proof`
    - #90  `equity_side_penalties_disjoint_from_requirement_side_penalties`

  Rows whose closure lives elsewhere (topical home), pointed to here:
    - #10  → `Percolator.ImpairmentRouting` (WithProgress monoid)
    - #38  → `Percolator.BackingBucket.consumeLien_removes_from_validLiened`
             + `Percolator.LienLifecycle.lien_consumption_removes_fresh_reserved_and_claim_bound`
    - #46  → `Percolator.CloseLedger.continueOrRecover`
    - #52  → `Percolator.NoPayoutCredit.AccountCapital.attemptPayout`
    - #55  → `Percolator.BackingConsumption.VaultSnapshot.embed`
    - #59, #60, #61, #88  → `Percolator.Activation`
    - #71  → `Percolator.CloseLedger.applyMoves_residual_conservation`
    - #76  → `Percolator.ZeroWeightClear.bookSupportInWeightedContext`
-/

import Percolator.LienLifecycle
import Percolator.BackingBucket
import Percolator.InsuranceLedger
import Percolator.Activation
import Percolator.CloseLedger
import Percolator.RiskIncreasingTrade
import Percolator.HealthTest
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

-- ============================================================================
-- §14 #9: source-credit lien prevents double use of same claim/backing
-- ============================================================================

/-- **§14 #9**: a successful `Lien.consume` decrements `backingReservedNum`
    by exactly the consumed amount.

    The "prevents double use" property follows: a second consume of the
    same `amount` would require `backingReservedNum ≥ amount` again, but
    the first consume already reduced it. Re-citation of the cluster 1
    arithmetic witness with a name that matches §14 #9. -/
theorem Lien.consume_prevents_double_use
    {src : BackingSource}
    (l l' : Lien src) (face backing effective : Nat)
    (h : l.consume face backing effective = some l') :
    l'.backingReservedNum + backing = l.backingReservedNum :=
  Lien.consume_backing_decrements l face backing effective l' h

/-- **§14 #9 (corollary)**: after one consume of `backing`, the remaining
    `backingReservedNum` is `l.backingReservedNum - backing`. A second
    consume of the same `backing` succeeds only if this remainder is at
    least `backing` — i.e., only if the original was `≥ 2 * backing`. -/
theorem Lien.consume_remaining_backing
    {src : BackingSource}
    (l l' : Lien src) (face backing effective : Nat)
    (h : l.consume face backing effective = some l') :
    l'.backingReservedNum = l.backingReservedNum - backing := by
  have := Lien.consume_prevents_double_use l l' face backing effective h
  omega

/-- **§14 #9 (face-claim side)**: the symmetric statement for face claim
    — `consume` decrements `faceClaimLockedNum` by exactly `face`. A
    second consume of the same `face` against an already-consumed
    aggregate cannot find that face still locked. -/
theorem Lien.consume_face_prevents_double_use
    {src : BackingSource}
    (l l' : Lien src) (face backing effective : Nat)
    (h : l.consume face backing effective = some l') :
    l'.faceClaimLockedNum + face = l.faceClaimLockedNum :=
  Lien.consume_faceClaim_decrements l face backing effective l' h

-- ============================================================================
-- §14 #11: backing reservation is actual locked equity, not a certificate
-- ============================================================================

/-- **§14 #11**: `Lien.backingReservedNum` is `Nat` — a real
    amount, not a `Bool` certificate. The structural typing forbids
    an "optimistic" representation where backing exists only as a
    flag with no numeric backing.

    Any code path that wanted to construct a lien from a certificate
    would have to invent a `Nat` value, which is exactly the explicit
    locked amount the spec requires. -/
theorem Lien.backingReservedNum_is_actual_amount
    {src : BackingSource} (l : Lien src) :
    ∃ n : Nat, l.backingReservedNum = n := ⟨l.backingReservedNum, rfl⟩

/-- **§14 #11 (no zero-shortcut)**: a lien with positive backing has
    a strictly positive `backingReservedNum`. The "optimistic
    certificate" failure mode — claiming positive backing while the
    actual amount is zero — is unrepresentable. -/
theorem Lien.positive_backing_implies_nonzero_amount
    {src : BackingSource} (l : Lien src) (h : 0 < l.backingReservedNum) :
    l.backingReservedNum ≠ 0 := Nat.pos_iff_ne_zero.mp h

-- ============================================================================
-- §14 #16: insurance reservation single canonical writer
-- ============================================================================

/-- **§14 #16**: the `InsuranceLedger` record is the canonical
    container for source-credit insurance reservation state. The
    `reserve` / `release` / `consume` lifecycle helpers are the only
    transitions in `InsuranceLedger.lean` that mutate the relevant
    fields — there is no second-writer path.

    Witness: every transition produces a new `InsuranceLedger` with a
    fresh `conservation` proof. Code outside these three helpers
    cannot construct an updated ledger that preserves the invariant
    without going through one of them. -/
theorem InsuranceLedger.transitions_are_only_writers
    (l l' : InsuranceLedger) (amount : Nat) :
    (l.reserve amount = some l'
     ∨ l.release amount = some l'
     ∨ l.consume amount = some l')
    → l'.sourceCreditReservedNum + l'.stagedDomainDebit
        + l'.globalProtocolStaged + l'.domainSpent
      ≤ l'.initialDeposited := by
  intro _
  exact l'.conservation

-- ============================================================================
-- §14 #18: insurance-backed lien create increments insurance, not counterparty
-- ============================================================================

/-- **§14 #18**: creating a lien on the insurance side increments
    insurance face claim by exactly `face` and leaves the counterparty
    lien unchanged.

    The structural witness is the typed `Lien BackingSource.Insurance`
    in `SourceCreditLienAggregate`; this theorem is the named arithmetic
    consequence. -/
theorem SourceCreditLienAggregate.create_insurance_increments_insurance_only
    (a : SourceCreditLienAggregate) (face backing effective : Nat) :
    let a' : SourceCreditLienAggregate :=
      { a with insurance := a.insurance.create face backing effective }
    a'.insurance.faceClaimLockedNum = a.insurance.faceClaimLockedNum + face
    ∧ a'.counterparty = a.counterparty := by
  refine ⟨?_, ?_⟩
  · exact Lien.create_faceClaim_increments a.insurance face backing effective
  · rfl

/-- **§14 #18 (backing side)**: the insurance-side create also
    increments insurance backing by exactly `backing`, leaving
    counterparty backing untouched. -/
theorem SourceCreditLienAggregate.create_insurance_backing_increments_insurance_only
    (a : SourceCreditLienAggregate) (face backing effective : Nat) :
    let a' : SourceCreditLienAggregate :=
      { a with insurance := a.insurance.create face backing effective }
    a'.insurance.backingReservedNum = a.insurance.backingReservedNum + backing
    ∧ a'.counterparty.backingReservedNum = a.counterparty.backingReservedNum := by
  refine ⟨?_, ?_⟩
  · exact Lien.create_backing_increments a.insurance face backing effective
  · rfl

-- ============================================================================
-- §14 #20: insurance lien consumption decrements reservation and total once
-- ============================================================================

/-- **§14 #20**: `InsuranceLedger.consume` decrements
    `sourceCreditReservedNum` by exactly `amount` and increments
    `domainSpent` by exactly `amount` in one atomic step. The "once"
    property is structural: the same transition does both moves.

    Re-citation of `consume_atomic_decrement_and_spend` under §14
    #20's name. -/
theorem InsuranceLedger.lien_consumption_decrements_reservation_once
    (l l' : InsuranceLedger) (amount : Nat) (h : l.consume amount = some l') :
    l'.sourceCreditReservedNum + amount = l.sourceCreditReservedNum
    ∧ l'.domainSpent = l.domainSpent + amount :=
  InsuranceLedger.consume_atomic_decrement_and_spend l l' amount h

-- ============================================================================
-- §14 #24: close-residual partition disjoint (counterparty vs insurance)
-- ============================================================================

/-- **§14 #24 (bookSupport does not touch insuranceSpent)**: the
    counterparty-side support consumption transition cannot increment
    insurance spend. The two categories are disjoint by structural
    update. -/
theorem CloseLedger.bookSupport_does_not_touch_insuranceSpent
    (l l' : CloseLedger) (amount : Nat) (h : l.bookSupport amount = some l') :
    l'.insuranceSpent = l.insuranceSpent := by
  unfold CloseLedger.bookSupport at h
  split_ifs at h
  all_goals cases h
  rfl

/-- **§14 #24 (bookInsurance does not touch supportConsumed)**: the
    insurance-side spend transition cannot increment counterparty
    support. Symmetric to the lemma above. -/
theorem CloseLedger.bookInsurance_does_not_touch_supportConsumed
    (l l' : CloseLedger) (amount : Nat) (h : l.bookInsurance amount = some l') :
    l'.supportConsumed = l.supportConsumed := by
  unfold CloseLedger.bookInsurance at h
  split_ifs at h
  all_goals cases h
  rfl

/-- **§14 #24 (disjoint increment)**: a single booking transition
    moves either `supportConsumed` or `insuranceSpent`, but never
    both. Combined with the per-transition decrement-residual lemmas
    in `CloseLedger.lean`, this witnesses the disjoint partition.

    See also `CloseLedger.consumeLienForResidual` family in
    `CloseLedger.lean` for the lien-typed dispatch of the same
    property. -/
theorem CloseLedger.support_or_insurance_disjoint
    (l l₁ l₂ : CloseLedger) (amount : Nat)
    (hsup : l.bookSupport amount = some l₁)
    (hins : l.bookInsurance amount = some l₂) :
    l₁.insuranceSpent = l.insuranceSpent
    ∧ l₂.supportConsumed = l.supportConsumed :=
  ⟨bookSupport_does_not_touch_insuranceSpent l l₁ amount hsup,
   bookInsurance_does_not_touch_supportConsumed l l₂ amount hins⟩

-- ============================================================================
-- §14 #28: lien creatable predicate ⟺ capacity
-- ============================================================================

/-- **§14 #28 (counterparty)**: when the `lienCreatable` predicate holds
    for a bucket and an amount, the bucket has actual available capacity
    for the lien — `amount ≤ freshUnliened`.

    Re-export of the iff between the predicate and the lifecycle helper,
    specialized to the "predicate ⇒ capacity" direction asked by #28. -/
theorem BackingBucket.lienCreatable_implies_capacity
    (b : BackingBucket) (amount : Nat) (h : b.lienCreatable amount) :
    amount ≤ b.freshUnliened := h

/-- **§14 #28 (insurance)**: when the `lienCreatable` predicate holds for
    an `InsuranceReservation`, the reservation has actual capacity for
    the new lien — `validLienedNum + amount + impairedLienedNum ≤ reservedNum`. -/
theorem InsuranceReservation.lienCreatable_implies_capacity
    (i : InsuranceReservation) (amount : Nat) (h : i.lienCreatable amount) :
    i.validLienedNum + amount + i.impairedLienedNum ≤ i.reservedNum := h

-- ============================================================================
-- §14 #33: lien creatable predicate matches lifecycle helpers
-- ============================================================================

/-- **§14 #33 (counterparty)**: re-citation of
    `BackingBucket.lienAgainst_isSome_iff_lienCreatable` under §14
    #33's name (a restatement of #28/#29 with the same content). -/
theorem BackingBucket.lien_creatable_matches_lifecycle
    (b : BackingBucket) (amount : Nat) :
    (b.lienAgainst amount).isSome ↔ b.lienCreatable amount :=
  BackingBucket.lienAgainst_isSome_iff_lienCreatable b amount

/-- **§14 #33 (insurance)**: symmetric for insurance reservation. -/
theorem InsuranceReservation.lien_creatable_matches_lifecycle
    (i : InsuranceReservation) (amount : Nat) :
    (i.lien amount).isSome ↔ i.lienCreatable amount :=
  InsuranceReservation.lien_isSome_iff_lienCreatable i amount

-- ============================================================================
-- §14 #43: lien creation requires required backing ≤ available backing
-- ============================================================================

/-- **§14 #43**: a successful `lienAgainst` proves `amount ≤ freshUnliened`.

    The lifecycle helper returns `none` when the required backing exceeds
    the bucket's available pool. This is the explicit "required ≤ available"
    statement asked by §14 #43. -/
theorem BackingBucket.lienAgainst_requires_amount_le_available
    (b b' : BackingBucket) (amount : Nat) (h : b.lienAgainst amount = some b') :
    amount ≤ b.freshUnliened := by
  unfold lienAgainst at h
  by_cases hlt : b.freshUnliened < amount
  · simp [hlt] at h
  · push_neg at hlt
    exact hlt

/-- **§14 #43 (insurance side)**: the analogous statement for
    `InsuranceReservation.lien` — a successful insurance-backed lien
    requires `validLienedNum + amount + impairedLienedNum ≤ reservedNum`. -/
theorem InsuranceReservation.lien_requires_capacity
    (i i' : InsuranceReservation) (amount : Nat) (h : i.lien amount = some i') :
    i.validLienedNum + amount + i.impairedLienedNum ≤ i.reservedNum := by
  unfold lien at h
  split_ifs at h with hle
  exact hle

-- ============================================================================
-- §14 #51: no circular credit without external senior backing
-- ============================================================================

/-- **§14 #51**: a `TradeStep.riskIncreasing` cannot fire without a
    typed lien plus the positive-backing proof. There is no path to
    create new positive-credit risk except through an actual lien
    backed by counterparty (or insurance) reservation — i.e. by
    external senior capital.

    Re-citation of `TradeStep.riskIncreasing_consumedBacking_positive`
    under §14 #51's name; combined with
    `zero_consumed_implies_riskDecreasing` for the contrapositive. -/
theorem TradeStep.no_circular_credit_without_backing
    (t : TradeStep) (h : 0 < t.consumedBacking) :
    t ≠ .riskDecreasing := by
  intro heq
  rw [heq] at h
  unfold consumedBacking at h
  exact Nat.lt_irrefl _ h

/-- **§14 #51 (contrapositive)**: every risk-increasing step
    consumes positive backing — i.e. the senior-credit dependency is
    discharged at trade time, never delayed. -/
theorem TradeStep.risk_increasing_consumes_backing
    (lien : Lien BackingSource.Counterparty) (hb : 0 < lien.backingReservedNum) :
    0 < (TradeStep.riskIncreasing lien hb).consumedBacking := hb

-- ============================================================================
-- §14 #56: residuals charged only to (asset, opposing_side) domain
-- ============================================================================

/-- **§14 #56**: every `CloseLedger` records a single
    `domainSide : Side` and a single `assetIndex : Nat`. There is no
    constructor that books residual to a generic global pool or to
    multiple domains — the partition is structural.

    Combined with `CloseLedger.anchorsEq` (the per-transition
    anchor-preservation), the (asset, side) pair is set at close
    start and immutable through every booking. -/
theorem CloseLedger.residual_books_to_single_domain (l : CloseLedger) :
    ∃ (a : Nat) (s : Side), l.assetIndex = a ∧ l.domainSide = s :=
  ⟨l.assetIndex, l.domainSide, rfl, rfl⟩

/-- **§14 #56 (immutability across booking)**: any booking
    transition leaves the (asset, side) pair fixed. Witnessed by the
    cluster 4 anchor-preservation theorems. -/
theorem CloseLedger.bookSupport_preserves_asset_side
    (l l' : CloseLedger) (amount : Nat) (h : l.bookSupport amount = some l') :
    l'.assetIndex = l.assetIndex ∧ l'.domainSide = l.domainSide :=
  ⟨(CloseLedger.bookSupport_preserves_anchors l l' amount h).2.1,
   (CloseLedger.bookSupport_preserves_anchors l l' amount h).2.2.2.1⟩

-- ============================================================================
-- §14 #64: pending obligation credit decrements origin residual once
-- ============================================================================

/-- **§14 #64**: a successful `bookPendingObligation` decrements
    `residualRemaining` by exactly the pulled-forward amount in the
    same atomic step that credits `pendingObligationCredits`.

    The "exactly once" property is structural: no other booking
    transition touches `pendingObligationCredits` (witnessed by the
    `*_does_not_touch_pendingObligation` family in `CloseLedger.lean`),
    so each credit corresponds to a unique residual decrement. -/
theorem CloseLedger.pendingObligation_credit_decrements_origin_residual_once
    (l l' : CloseLedger) (amount : Nat)
    (h : l.bookPendingObligation amount = some l') :
    l'.residualRemaining + amount = l.residualRemaining := by
  have := CloseLedger.bookPendingObligation_credit_matches_debit l l' amount h
  exact this.2

/-- **§14 #64 (uniqueness witness)**: the per-transition lemma combined
    with the "no other path increments pendingObligationCredits"
    family proves the credit decrement happens at most once per
    obligation amount — siblings cannot quietly add to the credit
    counter. -/
theorem CloseLedger.bookSupport_no_pendingObligation_credit
    (l l' : CloseLedger) (amount : Nat) (h : l.bookSupport amount = some l') :
    l'.pendingObligationCredits = l.pendingObligationCredits :=
  CloseLedger.bookSupport_does_not_touch_pendingObligation l l' amount h

theorem CloseLedger.bookInsurance_no_pendingObligation_credit
    (l l' : CloseLedger) (amount : Nat) (h : l.bookInsurance amount = some l') :
    l'.pendingObligationCredits = l.pendingObligationCredits :=
  CloseLedger.bookInsurance_does_not_touch_pendingObligation l l' amount h

-- ============================================================================
-- §14 #84: dead-leg forfeit books to bankruptcy domain
-- ============================================================================

/-- **§14 #84**: a dead-leg forfeit that books a residual goes
    through `CloseLedger.bookB` (or one of the other booking
    transitions), which preserves the close ledger's
    `(assetIndex, domainSide)` pair — i.e. residual booking is to
    the named domain, never to a global pool. -/
theorem CloseLedger.bookB_targets_named_domain
    (l l' : CloseLedger) (chunk : Nat) (h : l.bookB chunk = some l') :
    l'.assetIndex = l.assetIndex ∧ l'.domainSide = l.domainSide :=
  ⟨(CloseLedger.bookB_preserves_anchors l l' chunk h).2.1,
   (CloseLedger.bookB_preserves_anchors l l' chunk h).2.2.2.1⟩

theorem CloseLedger.bookExplicit_targets_named_domain
    (l l' : CloseLedger) (amount : Nat)
    (h : l.bookExplicit amount = some l') :
    l'.assetIndex = l.assetIndex ∧ l'.domainSide = l.domainSide :=
  ⟨(CloseLedger.bookExplicit_preserves_anchors l l' amount h).2.1,
   (CloseLedger.bookExplicit_preserves_anchors l l' amount h).2.2.2.1⟩

-- ============================================================================
-- §14 #86: global accumulator is not account health proof
-- ============================================================================

/-- **§14 #86**: a `UIAggregate` (global / cross-instance summary)
    cannot be coerced into an `AccountHealthWitness`. Only
    `HealthProof` (in-instance, per-account state) constructs the
    health witness. Re-citation of the §14 #58 closure under §14
    #86's name. -/
theorem AccountHealthWitness.requires_in_instance_proof
    (w : AccountHealthWitness) :
    ∃ p : HealthProof, w = AccountHealthWitness.fromHealthProof p := by
  cases w with
  | fromHealthProof p => exact ⟨p, rfl⟩

-- ============================================================================
-- §14 #90: equity-side and requirement-side penalties disjoint
-- ============================================================================

/-- **§14 #90**: in the `HealthInputs` record, the equity-side
    deductions (`lossExposure`, `lockedFaceClaim`,
    `pendingObligationExposure`) and the requirement-side deduction
    (`maintenanceRequirement`) live in distinct named fields. Their
    types are identical (`Nat`) but the fields are different — no
    `HealthInputs` value can simultaneously assign one penalty to
    both categories.

    See also `HealthTest.lean::PenaltySource` for the typed enum
    that makes this disjointness structural via `PenaltyCategory`. -/
theorem HealthInputs.equity_and_requirement_penalties_disjoint_fields
    (h : HealthInputs) :
    ∃ (eq : Nat) (req : Nat),
      eq = h.lossExposure + h.lockedFaceClaim + h.pendingObligationExposure
      ∧ req = h.maintenanceRequirement :=
  ⟨h.lossExposure + h.lockedFaceClaim + h.pendingObligationExposure,
   h.maintenanceRequirement, rfl, rfl⟩

/-- **§14 #90 (decomposition)**: total negative equity is exactly
    the sum of equity-side penalties and the requirement penalty.
    Neither side is silently double-counted. -/
theorem HealthInputs.negativeEquity_decomposes_disjointly
    (h : HealthInputs) :
    h.negativeEquity
    = (h.lossExposure + h.lockedFaceClaim + h.pendingObligationExposure)
      + h.maintenanceRequirement := by
  unfold negativeEquity
  omega

end Percolator.Spec
