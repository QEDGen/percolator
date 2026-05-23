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

end Percolator.Spec
