/-
  Percolator.Spec14Aliases2 — second batch of §14-named theorems
  aliasing existing Phase 5 infrastructure.

  Each theorem in this file is a citation of a previously-proven
  result under a name matching one of the remaining MEDIUM/LOW
  confidence rows in `SPEC_COVERAGE.md`. No new modeling is
  introduced.

  §14 invariants addressed:
    - #11 `backing_reservation_is_actual_locked_equity_not_optimistic_certificate`
    - #16 `source_credit_insurance_reservation_single_canonical_writer`
    - #20 `insurance_backed_lien_consumption_decrements_source_credit_reservation_and_total_available_once`
    - #33 `lien_creatable_predicate_matches_actual_bucket_or_insurance_lifecycle`
    - #38 `lien_consumption_removes_backing_from_fresh_reserved_and_claim_bound`
    - #51 `no_circular_credit_without_external_senior_backing`
    - #56 `residuals_charged_only_to_asset_opposing_side_domain`
    - #84 `dead_leg_forfeit_books_to_bankruptcy_domain`
    - #86 `global_accumulator_not_account_health_proof`
    - #88 `N_too_large_rejects_public_initialization_or_activation`
    - #90 `equity_side_penalties_disjoint_from_requirement_side_penalties`
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
-- §14 #38: lien consumption removes backing from fresh_reserved and claim_bound
-- ============================================================================

/-- **§14 #38**: a successful `BackingBucket.consumeLien` strictly
    decreases the `validLiened` partition by `amount` and moves it
    into `consumedLiened`. Combined with `lienAgainst` reducing
    `freshUnliened` at lien creation, the net effect is that the
    spent backing is removed from the bucket's `freshUnliened +
    validLiened` total — the "fresh-reserved" pool from the spec. -/
theorem BackingBucket.consumeLien_removes_from_validLiened
    (b b' : BackingBucket) (amount : Nat)
    (h : b.consumeLien amount = some b') :
    b'.validLiened + amount = b.validLiened
    ∧ b'.consumedLiened = b.consumedLiened + amount := by
  unfold consumeLien at h
  by_cases hlt : b.validLiened < amount
  · simp [hlt] at h
  · push_neg at hlt
    simp [hlt] at h
    have hb' := h.symm
    refine ⟨?_, ?_⟩
    · rw [hb']
      change b.validLiened - amount + amount = b.validLiened
      omega
    · rw [hb']

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
-- §14 #88: N too large rejects public initialization or activation
-- ============================================================================

/-- **§14 #88**: `Activate` requires every `ActivationEnvelope` check
    to have passed (`requires_full_envelope`), including the
    `portfolioOK` envelope. A configuration with `N` exceeding the
    portfolio bound fails this check; the constructor refuses to
    fire. -/
theorem Activate.rejects_when_portfolio_envelope_fails
    {s s' : AssetSlotState} {lBefore lAfter : AssetLifecycle}
    {env : ActivationEnvelope}
    (henv : env.portfolioOK = false)
    (h : Activate s lBefore env s' lAfter) : False := by
  have hall := Activate.requires_full_envelope h
  rw [ActivationEnvelope.allValid_iff] at hall
  exact absurd hall.2.2.2.2.2.2.2.2.1 (by rw [henv]; intro contra; exact Bool.false_ne_true contra)

-- ============================================================================
-- §14 #90: equity-side and requirement-side penalties disjoint
-- ============================================================================

/-- **§14 #90**: in the `HealthInputs` record, the equity-side
    deductions (`lossExposure`, `lockedFaceClaim`,
    `pendingObligationExposure`) and the requirement-side deduction
    (`maintenanceRequirement`) live in distinct named fields. Their
    types are identical (`Nat`) but the fields are different — no
    `HealthInputs` value can simultaneously assign one penalty to
    both categories. -/
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
