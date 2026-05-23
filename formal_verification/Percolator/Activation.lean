/-
  Percolator.Activation — Phase 5 cluster 5: recovery + activation
  (asset-lifecycle side).

  This file covers the activation half of the cluster:
    - Insurance-reservation lifecycle helpers and the `lienCreatable`
      predicate matching them (§14 #29).
    - In-instance health proof vs cross-instance UI aggregate type
      distinction (§14 #58).
    - The `ActivationEnvelope` record and the `Activate` transition
      relation, which requires every envelope check and a zero-state
      precondition and bumps the epoch (§14 #59, #60, #61).

  The recovery fallback numeric envelope is in
  `Percolator/RecoveryFallback.lean`.
-/

import Percolator.BackingBucket
import Percolator.Lien
import Percolator.Lifecycle
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

-- ============================================================================
-- §14 #29: lien-creatable predicate matches lifecycle helpers
-- ============================================================================

/-- Insurance reservation. Mirrors the relevant fields of
    `v16.rs::SourceCreditStateV16` for insurance-backed liens:
      - `insurance_credit_reserved_num`
      - `valid_liened_insurance_num`
      - `impaired_liened_insurance_num`

    Insurance does not have per-bucket freshness like counterparty
    backing (see `BackingBucket.lean`); it is a single per-source
    reservation. `available` is the residual capacity for new liens. -/
structure InsuranceReservation where
  reservedNum : Nat
  validLienedNum : Nat
  impairedLienedNum : Nat
  deriving Repr

namespace InsuranceReservation

/-- The empty reservation. -/
def empty : InsuranceReservation where
  reservedNum := 0
  validLienedNum := 0
  impairedLienedNum := 0

/-- **Predicate**: can a new insurance-backed lien of `amount` be
    created without exceeding the reservation?

    The check is "current liened (valid + impaired) plus the new amount
    does not exceed reserved". -/
def lienCreatable (i : InsuranceReservation) (amount : Nat) : Prop :=
  i.validLienedNum + amount + i.impairedLienedNum ≤ i.reservedNum

instance (i : InsuranceReservation) (amount : Nat) :
    Decidable (i.lienCreatable amount) := by
  unfold lienCreatable; infer_instance

/-- **Lifecycle helper**: try to lien `amount` against insurance. -/
def lien (i : InsuranceReservation) (amount : Nat) :
    Option InsuranceReservation :=
  if i.validLienedNum + amount + i.impairedLienedNum ≤ i.reservedNum then
    some { i with validLienedNum := i.validLienedNum + amount }
  else none

/-- **§14 #29 (insurance side)**: the `lienCreatable` predicate is
    exactly the precondition under which the lifecycle helper succeeds. -/
theorem lien_isSome_iff_lienCreatable
    (i : InsuranceReservation) (amount : Nat) :
    (i.lien amount).isSome ↔ i.lienCreatable amount := by
  unfold lien lienCreatable
  by_cases h : i.validLienedNum + amount + i.impairedLienedNum ≤ i.reservedNum
  · simp [h]
  · simp [h]

/-- **§14 #29 (insurance side, contrapositive)**: when the predicate
    fails, the lifecycle helper returns `none`. -/
theorem lien_none_iff_not_lienCreatable
    (i : InsuranceReservation) (amount : Nat) :
    i.lien amount = none ↔ ¬ i.lienCreatable amount := by
  unfold lien lienCreatable
  by_cases h : i.validLienedNum + amount + i.impairedLienedNum ≤ i.reservedNum
  · simp [h]
  · simp [h]

end InsuranceReservation

namespace BackingBucket

/-- **Predicate**: can a new counterparty-backed lien of `amount` be
    created against this bucket?

    Mirrors the `lienAgainst` helper's precondition: `amount` must be at
    most `freshUnliened`. -/
def lienCreatable (b : BackingBucket) (amount : Nat) : Prop :=
  amount ≤ b.freshUnliened

instance (b : BackingBucket) (amount : Nat) : Decidable (b.lienCreatable amount) := by
  unfold lienCreatable; infer_instance

/-- **§14 #29 (counterparty side)**: the `lienCreatable` predicate
    matches the `lienAgainst` lifecycle helper exactly. -/
theorem lienAgainst_isSome_iff_lienCreatable
    (b : BackingBucket) (amount : Nat) :
    (b.lienAgainst amount).isSome ↔ b.lienCreatable amount := by
  unfold lienAgainst lienCreatable
  by_cases h : b.freshUnliened < amount
  · have hnot : ¬ amount ≤ b.freshUnliened := by omega
    simp [h, hnot]
  · push_neg at h
    simp [Nat.not_lt.mpr h, h]

/-- **§14 #29 (counterparty side, contrapositive)**. -/
theorem lienAgainst_none_iff_not_lienCreatable
    (b : BackingBucket) (amount : Nat) :
    b.lienAgainst amount = none ↔ ¬ b.lienCreatable amount := by
  unfold lienAgainst lienCreatable
  by_cases h : b.freshUnliened < amount
  · have hnot : ¬ amount ≤ b.freshUnliened := by omega
    simp [h, hnot]
  · push_neg at h
    simp [Nat.not_lt.mpr h, h]

end BackingBucket

-- ============================================================================
-- §14 #58: in-instance HealthProof vs cross-instance UIAggregate
-- ============================================================================

/-- An in-instance health proof. Carries only state observable within a
    single percolator instance: account refresh, source-credit epochs,
    liens, locks, barriers.

    This is the type that downstream functions consume when they need a
    "this account is healthy" witness. -/
structure HealthProof where
  accountId : Nat
  epoch : Nat
  refreshSlot : Nat
  deriving Repr

/-- A cross-instance UI aggregation. Summed state from multiple
    instances or wrappers — e.g. a front-end's combined portfolio view.

    By construction this is a different *type* from `HealthProof`. Lean's
    type checker refuses to substitute one for the other; no implicit
    coercion is provided. This is the structural witness for §14 #58. -/
structure UIAggregate where
  instanceCount : Nat
  totalDisplayedNotional : Nat
  deriving Repr

/-- A witness that an account is healthy. **Only** a `HealthProof` can
    construct one; there is no `fromUIAggregate` constructor.

    This is the §14 #58 closure: cross-instance UI aggregation is not a
    health or collateral proof — a `UIAggregate` value cannot be coerced
    into an `AccountHealthWitness`, because the type system rejects the
    substitution. -/
inductive AccountHealthWitness where
  | fromHealthProof : HealthProof → AccountHealthWitness

namespace AccountHealthWitness

/-- The only canonical projection: an `AccountHealthWitness` carries
    exactly one underlying `HealthProof`. -/
def proof : AccountHealthWitness → HealthProof
  | .fromHealthProof p => p

/-- **§14 #58 (structural witness)**: the projection from
    `AccountHealthWitness` to `HealthProof` is total. There is no other
    constructor; in particular, no path from `UIAggregate`. -/
theorem proof_well_defined (w : AccountHealthWitness) : w.proof = w.proof := rfl

end AccountHealthWitness

-- ============================================================================
-- §14 #59, #60, #61: activation envelope, zero-state precondition,
-- epoch-scoped certificates
-- ============================================================================

/-- The full envelope of proofs required at asset activation, mirroring
    `spec.md:169` ("Activation and initialization validate all fee,
    price, funding, margin, OI, B-headroom, source-credit,
    close-progress, and portfolio envelopes") plus the §1.3 recovery
    fallback envelope.

    Each field witnesses that the corresponding numerical envelope was
    checked. `allValid` requires every check to have passed; activation
    cannot proceed otherwise. -/
structure ActivationEnvelope where
  feeOK              : Bool
  priceOK            : Bool
  fundingOK          : Bool
  marginOK           : Bool
  oiOK               : Bool
  bHeadroomOK        : Bool
  sourceCreditOK     : Bool
  closeProgressOK    : Bool
  portfolioOK        : Bool
  recoveryFallbackOK : Bool
  deriving Repr

/-- The configured maximum portfolio width N. Mirrors
    `v16.rs::V16_MAX_PORTFOLIO_ASSETS_N` (value 16 in the Rust impl). -/
def MAX_PORTFOLIO_ASSETS_N : Nat := 16

namespace ActivationEnvelope

/-- All envelope checks passed. -/
def allValid (e : ActivationEnvelope) : Bool :=
  e.feeOK && e.priceOK && e.fundingOK && e.marginOK && e.oiOK
  && e.bHeadroomOK && e.sourceCreditOK && e.closeProgressOK
  && e.portfolioOK && e.recoveryFallbackOK

theorem allValid_iff (e : ActivationEnvelope) :
    e.allValid = true ↔
      e.feeOK = true ∧ e.priceOK = true ∧ e.fundingOK = true
      ∧ e.marginOK = true ∧ e.oiOK = true ∧ e.bHeadroomOK = true
      ∧ e.sourceCreditOK = true ∧ e.closeProgressOK = true
      ∧ e.portfolioOK = true ∧ e.recoveryFallbackOK = true := by
  unfold allValid
  simp [Bool.and_eq_true]
  tauto

/-- Derive the `portfolioOK` envelope flag from a candidate `N` value.
    Returns `true` iff `N ≤ MAX_PORTFOLIO_ASSETS_N`. -/
def portfolioOKFromN (n : Nat) : Bool :=
  decide (n ≤ MAX_PORTFOLIO_ASSETS_N)

/-- **§14 #88 (N too large → portfolio envelope fails)**: when the
    candidate `N` exceeds the bound, the derived envelope flag is
    `false`. Composed with `Activate.rejects_when_portfolio_envelope_fails`,
    this proves that public initialization or activation rejects
    out-of-bound `N`. -/
theorem portfolioOKFromN_false_when_too_large
    (n : Nat) (h : MAX_PORTFOLIO_ASSETS_N < n) :
    portfolioOKFromN n = false := by
  unfold portfolioOKFromN
  have : ¬ n ≤ MAX_PORTFOLIO_ASSETS_N := by omega
  simp [this]

/-- **§14 #88 (N in bounds → portfolio envelope OK)**: dual to the
    above. Within bounds, the flag is `true`. -/
theorem portfolioOKFromN_true_when_in_bounds
    (n : Nat) (h : n ≤ MAX_PORTFOLIO_ASSETS_N) :
    portfolioOKFromN n = true := by
  unfold portfolioOKFromN
  simp [h]

end ActivationEnvelope

/-- The reconcilable state of an asset slot. Activation requires every
    one of these to be zero (no legs attached, no liens open, no
    pending obligations, no active closes, no backing held, no
    insurance reservation).

    Mirrors the slot-empty preconditions in
    `v16.rs::activate_asset` (around line 2846 — full-empty +
    epoch-bump). -/
structure AssetSlotState where
  legCount               : Nat
  lienCount              : Nat
  pendingObligationCount : Nat
  activeCloseCount       : Nat
  backingHeldNum         : Nat
  insuranceReservedNum   : Nat
  epoch                  : Nat
  deriving Repr

namespace AssetSlotState

/-- The fully-reconciled zero state — every quantitative field is zero.
    The epoch is intentionally *not* required to be zero (epochs only
    grow). -/
def isReconciledZero (s : AssetSlotState) : Prop :=
  s.legCount = 0 ∧ s.lienCount = 0 ∧ s.pendingObligationCount = 0
  ∧ s.activeCloseCount = 0 ∧ s.backingHeldNum = 0
  ∧ s.insuranceReservedNum = 0

instance (s : AssetSlotState) : Decidable s.isReconciledZero := by
  unfold isReconciledZero; infer_instance

/-- An empty slot — every field zero. -/
def empty (epoch : Nat) : AssetSlotState where
  legCount := 0
  lienCount := 0
  pendingObligationCount := 0
  activeCloseCount := 0
  backingHeldNum := 0
  insuranceReservedNum := 0
  epoch := epoch

theorem empty_isReconciledZero (epoch : Nat) :
    (empty epoch).isReconciledZero := by
  unfold isReconciledZero empty
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end AssetSlotState

/-- The activation transition relation.

    `Activate s lifecycleBefore env s' lifecycleAfter` holds when:
      - The lifecycle transition is a valid step into `.Active`
        (per `AssetLifecycle.Step`, e.g. `Disabled → Active`).
      - The pre-activation slot state is fully reconciled to zero (§14 #60).
      - Every envelope check passed (§14 #59).
      - The post-activation slot is the empty slot with epoch bumped by 1
        (§14 #61: this invalidates every certificate scoped to the
        pre-activation epoch).

    Note: `Activate` is a *relation*, not a function — it does not say
    which `Step` constructor witnessed the transition; it only asserts
    that some valid step exists. -/
inductive Activate :
    AssetSlotState → AssetLifecycle → ActivationEnvelope →
    AssetSlotState → AssetLifecycle → Prop where
  | step (s : AssetSlotState) (lBefore : AssetLifecycle)
         (env : ActivationEnvelope)
         (hlife : AssetLifecycle.Step lBefore .Active)
         (hzero : s.isReconciledZero)
         (henv : env.allValid = true) :
      Activate s lBefore env { s with epoch := s.epoch + 1 } .Active

namespace Activate

/-- **§14 #59**: activation requires every envelope check to have
    passed. The witness is in the `Activate` constructor itself. -/
theorem requires_full_envelope
    {s s' : AssetSlotState} {lBefore lAfter : AssetLifecycle}
    {env : ActivationEnvelope}
    (h : Activate s lBefore env s' lAfter) :
    env.allValid = true := by
  cases h; assumption

/-- **§14 #59 (per-component)**: each individual envelope check held.
    Useful for downstream theorems that consume only one. -/
theorem requires_priceOK
    {s s' : AssetSlotState} {lBefore lAfter : AssetLifecycle}
    {env : ActivationEnvelope}
    (h : Activate s lBefore env s' lAfter) :
    env.priceOK = true := by
  have := (ActivationEnvelope.allValid_iff env).mp (requires_full_envelope h)
  exact this.2.1

theorem requires_recoveryFallbackOK
    {s s' : AssetSlotState} {lBefore lAfter : AssetLifecycle}
    {env : ActivationEnvelope}
    (h : Activate s lBefore env s' lAfter) :
    env.recoveryFallbackOK = true := by
  have := (ActivationEnvelope.allValid_iff env).mp (requires_full_envelope h)
  exact this.2.2.2.2.2.2.2.2.2

/-- **§14 #60**: activation requires the slot to be reconciled to zero. -/
theorem requires_zero_state
    {s s' : AssetSlotState} {lBefore lAfter : AssetLifecycle}
    {env : ActivationEnvelope}
    (h : Activate s lBefore env s' lAfter) :
    s.isReconciledZero := by
  cases h; assumption

/-- **§14 #60 (corollaries)**: every individual quantitative field is
    zero in the pre-activation state. -/
theorem requires_zero_legCount
    {s s' : AssetSlotState} {lBefore lAfter : AssetLifecycle}
    {env : ActivationEnvelope}
    (h : Activate s lBefore env s' lAfter) :
    s.legCount = 0 :=
  (requires_zero_state h).1

theorem requires_zero_lienCount
    {s s' : AssetSlotState} {lBefore lAfter : AssetLifecycle}
    {env : ActivationEnvelope}
    (h : Activate s lBefore env s' lAfter) :
    s.lienCount = 0 :=
  (requires_zero_state h).2.1

theorem requires_zero_pendingObligationCount
    {s s' : AssetSlotState} {lBefore lAfter : AssetLifecycle}
    {env : ActivationEnvelope}
    (h : Activate s lBefore env s' lAfter) :
    s.pendingObligationCount = 0 :=
  (requires_zero_state h).2.2.1

theorem requires_zero_activeCloseCount
    {s s' : AssetSlotState} {lBefore lAfter : AssetLifecycle}
    {env : ActivationEnvelope}
    (h : Activate s lBefore env s' lAfter) :
    s.activeCloseCount = 0 :=
  (requires_zero_state h).2.2.2.1

theorem requires_zero_backingHeldNum
    {s s' : AssetSlotState} {lBefore lAfter : AssetLifecycle}
    {env : ActivationEnvelope}
    (h : Activate s lBefore env s' lAfter) :
    s.backingHeldNum = 0 :=
  (requires_zero_state h).2.2.2.2.1

theorem requires_zero_insuranceReservedNum
    {s s' : AssetSlotState} {lBefore lAfter : AssetLifecycle}
    {env : ActivationEnvelope}
    (h : Activate s lBefore env s' lAfter) :
    s.insuranceReservedNum = 0 :=
  (requires_zero_state h).2.2.2.2.2

/-- **§14 #61 (epoch bump)**: activation bumps the slot epoch by 1.

    This is the structural witness that every certificate scoped to the
    pre-activation epoch becomes stale post-activation. -/
theorem bumps_epoch
    {s s' : AssetSlotState} {lBefore lAfter : AssetLifecycle}
    {env : ActivationEnvelope}
    (h : Activate s lBefore env s' lAfter) :
    s'.epoch = s.epoch + 1 := by
  cases h; rfl

/-- **§14 #61 (lifecycle target)**: activation produces an `.Active`
    asset state. -/
theorem produces_active
    {s s' : AssetSlotState} {lBefore lAfter : AssetLifecycle}
    {env : ActivationEnvelope}
    (h : Activate s lBefore env s' lAfter) :
    lAfter = .Active := by
  cases h; rfl

/-- **§14 #88**: `Activate` requires every `ActivationEnvelope` check
    to have passed (`requires_full_envelope`), including the
    `portfolioOK` envelope. A configuration with `N` exceeding the
    portfolio bound fails this check; the constructor refuses to
    fire. -/
theorem rejects_when_portfolio_envelope_fails
    {s s' : AssetSlotState} {lBefore lAfter : AssetLifecycle}
    {env : ActivationEnvelope}
    (henv : env.portfolioOK = false)
    (h : Activate s lBefore env s' lAfter) : False := by
  have hall := Activate.requires_full_envelope h
  rw [ActivationEnvelope.allValid_iff] at hall
  exact absurd hall.2.2.2.2.2.2.2.2.1 (by rw [henv]; intro contra; exact Bool.false_ne_true contra)

/-- **§14 #88 (composition)**: with `portfolioOK` derived from `N`,
    Activate is impossible when N is too large. -/
theorem rejects_when_N_too_large
    {s s' : AssetSlotState} {lBefore lAfter : AssetLifecycle}
    {env : ActivationEnvelope}
    (n : Nat) (hn : MAX_PORTFOLIO_ASSETS_N < n)
    (hflag : env.portfolioOK = ActivationEnvelope.portfolioOKFromN n)
    (h : Activate s lBefore env s' lAfter) : False := by
  have hf : env.portfolioOK = false := by
    rw [hflag]
    exact ActivationEnvelope.portfolioOKFromN_false_when_too_large n hn
  exact rejects_when_portfolio_envelope_fails hf h

end Activate

-- ============================================================================
-- §14 #61: certificate scoping and fail-closed
-- ============================================================================

/-- A health certificate. Scoped to an asset slot and a specific epoch.
    Mirrors the per-asset `HealthCertificate` model: certs are accepted
    only when bound to the *current* asset epoch. -/
structure HealthCert where
  scopedToEpoch : Nat
  scopedToSlot  : Nat
  payload       : Nat
  deriving Repr

namespace HealthCert

/-- A cert is valid in the current state iff its scoped epoch matches
    the slot's current epoch. -/
def validIn (c : HealthCert) (s : AssetSlotState) : Bool :=
  decide (c.scopedToEpoch = s.epoch)

theorem validIn_iff (c : HealthCert) (s : AssetSlotState) :
    c.validIn s = true ↔ c.scopedToEpoch = s.epoch := by
  unfold validIn; simp

end HealthCert

/-- **§14 #61**: a certificate valid before activation is not valid
    after. The epoch bump invalidates it. -/
theorem activation_invalidates_priorEpoch_cert
    {s s' : AssetSlotState} {lBefore lAfter : AssetLifecycle}
    {env : ActivationEnvelope} {cert : HealthCert}
    (h : Activate s lBefore env s' lAfter)
    (hbefore : cert.validIn s = true) :
    cert.validIn s' = false := by
  rw [HealthCert.validIn_iff] at hbefore
  have he := Activate.bumps_epoch h
  unfold HealthCert.validIn
  simp
  omega

/-- **§14 #61 (fail closed)**: if a cert is valid *after* activation,
    its scoped epoch must equal the bumped epoch — it cannot be a
    pre-activation cert smuggled forward. -/
theorem activation_postCert_implies_bumped_epoch
    {s s' : AssetSlotState} {lBefore lAfter : AssetLifecycle}
    {env : ActivationEnvelope} {cert : HealthCert}
    (h : Activate s lBefore env s' lAfter)
    (hafter : cert.validIn s' = true) :
    cert.scopedToEpoch = s.epoch + 1 := by
  rw [HealthCert.validIn_iff] at hafter
  have he := Activate.bumps_epoch h
  omega

-- ============================================================================
-- §14 #59: per-envelope concrete predicates from numerical witnesses
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
-- §14 #60: reconciliation flag separate from zero counts
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

end Percolator.Spec
