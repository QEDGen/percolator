/-
  Percolator.RecoveryFallback — Phase 5 cluster 5: recovery fallback
  numeric envelope.

  Models the spec's §1.3 / §12 recovery fallback envelope, the per-leg
  and per-account value-transfer bounds, and the fail-closed rejection
  of out-of-envelope reference prices.

  §14 invariants addressed:
    - #80 `recovery_fallback_price_within_configured_deviation_envelope`
    - #81 `recovery_fallback_value_transfer_bound_computed_per_account_and_domain`
    - #82 `fallback_recovery_rejects_unverified_or_out_of_envelope_reference_price`
-/

import Percolator.Defs
import Percolator.BoundArith
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Percolator.Spec

-- ============================================================================
-- Absolute difference on Nat
-- ============================================================================

/-- Absolute difference on `Nat`. `a` and `b` are unsigned; returns the
    larger minus the smaller. -/
def absDiff (a b : Nat) : Nat := if a ≥ b then a - b else b - a

theorem absDiff_self (a : Nat) : absDiff a a = 0 := by
  unfold absDiff
  simp

theorem absDiff_comm (a b : Nat) : absDiff a b = absDiff b a := by
  unfold absDiff
  by_cases h : a ≥ b
  · by_cases h' : b ≥ a
    · have heq : a = b := by omega
      subst heq; simp
    · simp [h, h']
  · push_neg at h
    have h' : b ≥ a := Nat.le_of_lt h
    have hnot : ¬ a ≥ b := Nat.not_le.mpr h
    simp [h', hnot]

theorem absDiff_le_left (a b : Nat) (h : a ≥ b) : absDiff a b = a - b := by
  unfold absDiff
  simp [h]

theorem absDiff_le_right (a b : Nat) (h : b ≥ a) : absDiff a b = b - a := by
  unfold absDiff
  by_cases h' : a ≥ b
  · have heq : a = b := by omega
    subst heq; simp
  · simp [h']

-- ============================================================================
-- §14 #80: deviation envelope predicate
-- ============================================================================

/-- **The §1.3 envelope predicate** (`spec.md:213-215`).

    The fallback price must be within `devBps / 10_000` of the reference
    price:
    ```
    abs(FallbackRecoveryPrice - RecoveryReferencePrice) * 10_000
       <= cfg_max_recovery_fallback_deviation_bps * RecoveryReferencePrice
    ```
    The cap `devBps` is the configured `cfg_max_recovery_fallback_deviation_bps`,
    which is itself bounded by `MAX_RECOVERY_FALLBACK_DEVIATION_BPS = 10000`
    (see `Defs.lean::MAX_RECOVERY_FALLBACK_DEVIATION_BPS`). -/
def envelopeValid (P_ref P_fb devBps : Nat) : Prop :=
  absDiff P_fb P_ref * 10000 ≤ devBps * P_ref

instance (P_ref P_fb devBps : Nat) : Decidable (envelopeValid P_ref P_fb devBps) := by
  unfold envelopeValid; infer_instance

/-- **§14 #80 (zero-deviation)**: equal prices always satisfy the
    envelope. -/
theorem envelopeValid_self (P devBps : Nat) :
    envelopeValid P P devBps := by
  unfold envelopeValid
  rw [absDiff_self]
  simp

/-- **§14 #80 (zero cap)**: with `devBps = 0`, the envelope holds iff
    the prices are equal. -/
theorem envelopeValid_zeroBps_iff_eq (P_ref P_fb : Nat) :
    envelopeValid P_ref P_fb 0 ↔ P_fb = P_ref := by
  unfold envelopeValid
  simp
  constructor
  · intro h
    unfold absDiff at h
    by_cases hle : P_fb ≥ P_ref
    · simp [hle] at h; omega
    · push_neg at hle
      have : ¬ P_fb ≥ P_ref := Nat.not_le.mpr hle
      simp [this] at h; omega
  · intro h; subst h; rw [absDiff_self]

/-- **§14 #80 (monotone in cap)**: a looser cap accepts every price the
    tighter cap would accept. -/
theorem envelopeValid_mono_in_devBps
    (P_ref P_fb devBps devBps' : Nat) (h : devBps ≤ devBps')
    (hvalid : envelopeValid P_ref P_fb devBps) :
    envelopeValid P_ref P_fb devBps' := by
  unfold envelopeValid at hvalid ⊢
  have : devBps * P_ref ≤ devBps' * P_ref := Nat.mul_le_mul_right _ h
  omega

/-- **§14 #80 (envelope explicit form)**: the validity predicate is
    exactly the spec's inequality. Provided as a named equivalence for
    downstream consumers. -/
theorem envelopeValid_iff (P_ref P_fb devBps : Nat) :
    envelopeValid P_ref P_fb devBps ↔
    absDiff P_fb P_ref * 10000 ≤ devBps * P_ref := by
  unfold envelopeValid; rfl

-- ============================================================================
-- §14 #81: per-leg and per-account value-transfer bound
-- ============================================================================

/-- Per-leg recovery value-transfer bound (`spec.md:222-224`):
    ```
    recovery_value_transfer_leg =
      ceil(|pos_q_leg| * |P_fb - P_ref| / POS_SCALE)
    ```
    where `POS_SCALE = 10^6` (`Defs.lean::POS_SCALE`). -/
def legTransferBound (posQAbs P_ref P_fb : Nat) : Nat :=
  let prod := posQAbs * absDiff P_fb P_ref
  (prod + POS_SCALE - 1) / POS_SCALE

/-- **§14 #81 (zero-position has zero transfer)**: a leg with no
    position contributes zero to the bound. -/
theorem legTransferBound_zero_posQ (P_ref P_fb : Nat) :
    legTransferBound 0 P_ref P_fb = 0 := by
  unfold legTransferBound
  simp
  unfold POS_SCALE
  norm_num

/-- **§14 #81 (zero-deviation has zero transfer)**: with `P_fb = P_ref`,
    every leg's bound is zero. -/
theorem legTransferBound_zero_deviation (posQAbs P : Nat) :
    legTransferBound posQAbs P P = 0 := by
  unfold legTransferBound
  rw [absDiff_self]
  simp
  unfold POS_SCALE
  norm_num

/-- **§14 #81 (monotone in posQ)**: a larger position contributes a
    larger (or equal) per-leg bound. -/
theorem legTransferBound_mono_in_posQ
    (posQAbs posQAbs' P_ref P_fb : Nat) (h : posQAbs ≤ posQAbs') :
    legTransferBound posQAbs P_ref P_fb ≤ legTransferBound posQAbs' P_ref P_fb := by
  unfold legTransferBound
  apply Nat.div_le_div_right
  have : posQAbs * absDiff P_fb P_ref ≤ posQAbs' * absDiff P_fb P_ref :=
    Nat.mul_le_mul_right _ h
  omega

/-- Per-account recovery value-transfer bound (`spec.md:218-225`):
    ```
    recovery_value_transfer_bound(account) =
      sum_over_legs ceil(|pos_q_leg| * |P_fb - P_ref| / POS_SCALE)
    ```
    `legs` is a list of per-leg absolute position quantities. -/
def accountTransferBound (legs : List Nat) (P_ref P_fb : Nat) : Nat :=
  (legs.map (fun q => legTransferBound q P_ref P_fb)).sum

/-- **§14 #81 (zero account)**: an account with no legs has zero
    transfer bound. -/
theorem accountTransferBound_nil (P_ref P_fb : Nat) :
    accountTransferBound [] P_ref P_fb = 0 := by
  unfold accountTransferBound
  simp

/-- **§14 #81 (cons additivity)**: adding a leg adds its bound to the
    account total. -/
theorem accountTransferBound_cons
    (q : Nat) (rest : List Nat) (P_ref P_fb : Nat) :
    accountTransferBound (q :: rest) P_ref P_fb
    = legTransferBound q P_ref P_fb + accountTransferBound rest P_ref P_fb := by
  unfold accountTransferBound
  simp

/-- **§14 #81 (zero deviation has zero account bound)**: with equal
    prices the account bound is zero. -/
theorem accountTransferBound_zero_deviation (legs : List Nat) (P : Nat) :
    accountTransferBound legs P P = 0 := by
  induction legs with
  | nil => rw [accountTransferBound_nil]
  | cons q rest ih =>
    rw [accountTransferBound_cons, legTransferBound_zero_deviation, ih]

/-- **§14 #81 (per-leg ceiling bound)**: each leg's contribution is at
    most `ceil(posQAbs * |P_fb - P_ref| / POS_SCALE)`. The definition
    *is* this bound; we expose it as a named theorem. -/
theorem legTransferBound_eq_ceilDiv (posQAbs P_ref P_fb : Nat) :
    legTransferBound posQAbs P_ref P_fb
    = (posQAbs * absDiff P_fb P_ref + POS_SCALE - 1) / POS_SCALE := by
  rfl

/-- **§14 #81 (monotone in leg list)**: a superset of legs (cons more)
    yields an at-least-as-large bound. -/
theorem accountTransferBound_le_cons
    (q : Nat) (rest : List Nat) (P_ref P_fb : Nat) :
    accountTransferBound rest P_ref P_fb
    ≤ accountTransferBound (q :: rest) P_ref P_fb := by
  rw [accountTransferBound_cons]
  exact Nat.le_add_left _ _

-- ============================================================================
-- §14 #82: fail-closed on out-of-envelope or unverified reference
-- ============================================================================

/-- A fallback recovery price input. Combines the reference price, the
    fallback price, an "is the reference verified" flag, and the
    deviation cap. -/
structure FallbackPriceInput where
  P_ref     : Nat
  P_fb      : Nat
  verified  : Bool
  devBps    : Nat
  deriving Repr

namespace FallbackPriceInput

/-- The acceptance predicate: a fallback recovery is allowed iff the
    reference is verified AND the envelope is valid. -/
def accepted (i : FallbackPriceInput) : Prop :=
  i.verified = true ∧ envelopeValid i.P_ref i.P_fb i.devBps

instance (i : FallbackPriceInput) : Decidable i.accepted := by
  unfold accepted; infer_instance

end FallbackPriceInput

/-- **§14 #82 (fail closed on unverified)**: an unverified reference
    price is never accepted, regardless of envelope. -/
theorem unverified_rejected (i : FallbackPriceInput) (h : i.verified = false) :
    ¬ i.accepted := by
  unfold FallbackPriceInput.accepted
  intro hacc
  rw [h] at hacc
  exact Bool.false_ne_true hacc.1

/-- **§14 #82 (fail closed on out-of-envelope)**: an out-of-envelope
    fallback is never accepted, regardless of verification. -/
theorem outOfEnvelope_rejected
    (i : FallbackPriceInput) (h : ¬ envelopeValid i.P_ref i.P_fb i.devBps) :
    ¬ i.accepted := by
  unfold FallbackPriceInput.accepted
  intro hacc
  exact h hacc.2

/-- **§14 #82 (acceptance equivalence)**: a fallback is accepted iff
    both conditions hold. -/
theorem accepted_iff (i : FallbackPriceInput) :
    i.accepted ↔ (i.verified = true ∧ envelopeValid i.P_ref i.P_fb i.devBps) := by
  unfold FallbackPriceInput.accepted; rfl

/-- **§14 #82 (zero positive payout under rejection)**: a rejected
    fallback contributes zero to any payout. Modeled here as: if
    `i` is not accepted, the "payout under this fallback" — represented
    abstractly as some Nat that is conditionally zeroed — must be zero.

    Encoded as a function that returns `0` unless accepted; the theorem
    is by definition. -/
def conditionalPayout (i : FallbackPriceInput) (positive : Nat) : Nat :=
  if i.accepted then positive else 0

theorem conditionalPayout_zero_when_rejected
    (i : FallbackPriceInput) (positive : Nat) (h : ¬ i.accepted) :
    conditionalPayout i positive = 0 := by
  unfold conditionalPayout
  simp [h]

theorem conditionalPayout_eq_when_accepted
    (i : FallbackPriceInput) (positive : Nat) (h : i.accepted) :
    conditionalPayout i positive = positive := by
  unfold conditionalPayout
  simp [h]

end Percolator.Spec
