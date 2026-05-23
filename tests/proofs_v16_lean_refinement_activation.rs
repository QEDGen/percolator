#![allow(dead_code)] // reference port mirrors every Lean def; not all are exercised by proptests yet

//! State-machine refinement: `Percolator/Activation.lean` (+
//! `YetMoreStrengthening.lean`, `MoreStrengthening.lean`) ↔ Rust.
//!
//! Tier 2 of the verification stack, fourth cluster bridge. Covers:
//!
//!   - `ActivationEnvelope` (10 Bool flags) + `all_valid`.
//!   - `AssetSlotState` + `is_reconciled_zero` + `epoch_bump`.
//!   - `EnvelopeWitness` (concrete numerical inputs, from #59
//!     strengthening) + `from_witness` + per-envelope soundness.
//!   - `HealthCert` + `valid_in` (epoch-scoped certs).
//!   - Activation transition: requires lifecycle step into
//!     `.Active`, full envelope, reconciliation, and bumps the
//!     epoch.
//!
//! Theorems verified at runtime:
//!
//!   - `all_valid_iff`: envelope `all_valid` iff every flag true.
//!   - `from_witness_*_false_when_*`: each per-envelope flag is
//!     false when its underlying numerical condition fails.
//!   - `from_witness_all_valid_implies_*`: `all_valid` decodes
//!     to each underlying constraint.
//!   - `requires_full_envelope` / `requires_zero_state`: the
//!     activation transition's gates.
//!   - `activation_invalidates_priorEpoch_cert` (§14 #61): the
//!     epoch bump invalidates pre-activation certs.
//!   - N_too_large_rejects_via_portfolioOK (§14 #88, from the
//!     #88 strengthening): activation is impossible when the
//!     candidate N exceeds the bound.
//!
//! See `formal_verification/Percolator/Activation.lean`,
//! `MoreStrengthening.lean::ActivationEnvelope.portfolioOKFromN`,
//! `YetMoreStrengthening.lean::ActivationEnvelope.fromWitness`.

use proptest::prelude::*;

// ============================================================================
// Reference port
// ============================================================================

/// Allowed lifecycle transitions into `.Active`. Mirrors the Lean
/// `AssetLifecycle.Step` predicate (only the cases reaching
/// `.Active` matter here).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AssetLifecycle {
    Disabled,
    PendingActivation,
    Active,
    DrainOnly,
    Retired,
}

/// Predicate: is this a valid step into `.Active`? Lean
/// `AssetLifecycle.Step _ .Active`.
fn lifecycle_step_into_active(from: AssetLifecycle) -> bool {
    matches!(
        from,
        AssetLifecycle::Disabled | AssetLifecycle::PendingActivation
    )
}

/// The full activation-envelope set. Mirrors Lean
/// `ActivationEnvelope`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ActivationEnvelope {
    fee_ok: bool,
    price_ok: bool,
    funding_ok: bool,
    margin_ok: bool,
    oi_ok: bool,
    b_headroom_ok: bool,
    source_credit_ok: bool,
    close_progress_ok: bool,
    portfolio_ok: bool,
    recovery_fallback_ok: bool,
}

impl ActivationEnvelope {
    /// All flags true. Lean `allValid`.
    fn all_valid(&self) -> bool {
        self.fee_ok
            && self.price_ok
            && self.funding_ok
            && self.margin_ok
            && self.oi_ok
            && self.b_headroom_ok
            && self.source_credit_ok
            && self.close_progress_ok
            && self.portfolio_ok
            && self.recovery_fallback_ok
    }
}

/// Maximum portfolio width N. Lean
/// `MoreStrengthening.lean::MAX_PORTFOLIO_ASSETS_N`.
const MAX_PORTFOLIO_ASSETS_N: u32 = 16;

/// `portfolio_ok` derived from candidate N. Lean
/// `portfolioOKFromN`.
fn portfolio_ok_from_n(n: u32) -> bool {
    n <= MAX_PORTFOLIO_ASSETS_N
}

/// Concrete numerical inputs for each envelope check. Lean
/// `YetMoreStrengthening.lean::ActivationEnvelope.Witness`.
#[derive(Clone, Copy, Debug)]
struct EnvelopeWitness {
    fee_paid: u128,
    fee_required: u128,
    price_age_blocks: u64,
    price_max_age_blocks: u64,
    funding_accrued: u128,
    funding_due: u128,
    margin_actual: u128,
    margin_required: u128,
    oi_actual: u128,
    oi_cap: u128,
    b_headroom_actual: u128,
    b_headroom_required: u128,
    source_credit_used: u128,
    source_credit_cap: u128,
    close_progress_done: u128,
    close_progress_target: u128,
    portfolio_width_n: u32,
    recovery_fallback_backoff_blocks: u64,
    recovery_fallback_backoff_min: u64,
}

impl EnvelopeWitness {
    /// Derive a complete `ActivationEnvelope`. Each flag is `true`
    /// exactly when its underlying inequality holds. Lean
    /// `fromWitness`.
    fn to_envelope(&self) -> ActivationEnvelope {
        ActivationEnvelope {
            fee_ok: self.fee_required <= self.fee_paid,
            price_ok: self.price_age_blocks <= self.price_max_age_blocks,
            funding_ok: self.funding_due <= self.funding_accrued,
            margin_ok: self.margin_required <= self.margin_actual,
            oi_ok: self.oi_actual <= self.oi_cap,
            b_headroom_ok: self.b_headroom_required <= self.b_headroom_actual,
            source_credit_ok: self.source_credit_used <= self.source_credit_cap,
            close_progress_ok: self.close_progress_target <= self.close_progress_done,
            portfolio_ok: portfolio_ok_from_n(self.portfolio_width_n),
            recovery_fallback_ok: self.recovery_fallback_backoff_min
                <= self.recovery_fallback_backoff_blocks,
        }
    }
}

/// The reconcilable state of an asset slot. Lean `AssetSlotState`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct AssetSlotState {
    leg_count: u32,
    lien_count: u32,
    pending_obligation_count: u32,
    active_close_count: u32,
    backing_held_num: u128,
    insurance_reserved_num: u128,
    epoch: u64,
}

impl AssetSlotState {
    fn empty(epoch: u64) -> Self {
        Self {
            leg_count: 0,
            lien_count: 0,
            pending_obligation_count: 0,
            active_close_count: 0,
            backing_held_num: 0,
            insurance_reserved_num: 0,
            epoch,
        }
    }

    /// Lean `isReconciledZero`.
    fn is_reconciled_zero(&self) -> bool {
        self.leg_count == 0
            && self.lien_count == 0
            && self.pending_obligation_count == 0
            && self.active_close_count == 0
            && self.backing_held_num == 0
            && self.insurance_reserved_num == 0
    }
}

/// The post-state of a successful activation. Lean's `Activate`
/// is a relation; here we model it as a function returning the
/// post-state when the gates hold, else `None`.
fn activate(
    s: &AssetSlotState,
    l_before: AssetLifecycle,
    env: &ActivationEnvelope,
) -> Option<(AssetSlotState, AssetLifecycle)> {
    if !lifecycle_step_into_active(l_before) {
        return None;
    }
    if !s.is_reconciled_zero() {
        return None;
    }
    if !env.all_valid() {
        return None;
    }
    let post = AssetSlotState {
        epoch: s.epoch.checked_add(1)?,
        ..*s
    };
    Some((post, AssetLifecycle::Active))
}

/// A health certificate scoped to a slot epoch. Lean `HealthCert`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct HealthCert {
    scoped_to_epoch: u64,
    scoped_to_slot: u32,
    payload: u128,
}

impl HealthCert {
    /// Valid iff the cert's scoped epoch matches the current slot
    /// epoch. Lean `validIn`.
    fn valid_in(&self, s: &AssetSlotState) -> bool {
        self.scoped_to_epoch == s.epoch
    }
}

// ============================================================================
// Generators
// ============================================================================

fn arb_envelope() -> impl Strategy<Value = ActivationEnvelope> {
    (
        any::<bool>(),
        any::<bool>(),
        any::<bool>(),
        any::<bool>(),
        any::<bool>(),
        any::<bool>(),
        any::<bool>(),
        any::<bool>(),
        any::<bool>(),
        any::<bool>(),
    )
        .prop_map(|(a, b, c, d, e, f, g, h, i, j)| ActivationEnvelope {
            fee_ok: a,
            price_ok: b,
            funding_ok: c,
            margin_ok: d,
            oi_ok: e,
            b_headroom_ok: f,
            source_credit_ok: g,
            close_progress_ok: h,
            portfolio_ok: i,
            recovery_fallback_ok: j,
        })
}

fn arb_witness() -> impl Strategy<Value = EnvelopeWitness> {
    (
        (0u128..=1_000_000u128, 0u128..=1_000_000u128),
        (0u64..=10_000u64, 0u64..=10_000u64),
        (0u128..=1_000_000u128, 0u128..=1_000_000u128),
        (0u128..=1_000_000u128, 0u128..=1_000_000u128),
        (0u128..=1_000_000u128, 0u128..=1_000_000u128),
        (0u128..=1_000_000u128, 0u128..=1_000_000u128),
        (0u128..=1_000_000u128, 0u128..=1_000_000u128),
        (0u128..=1_000_000u128, 0u128..=1_000_000u128),
        0u32..=32u32,
        (0u64..=10_000u64, 0u64..=10_000u64),
    )
        .prop_map(
            |(
                (fp, fr),
                (pa, pma),
                (fa, fd),
                (ma, mr),
                (oa, oc),
                (ba, br),
                (su, sc),
                (cd, ct),
                n,
                (rbb, rbm),
            )| EnvelopeWitness {
                fee_paid: fp,
                fee_required: fr,
                price_age_blocks: pa,
                price_max_age_blocks: pma,
                funding_accrued: fa,
                funding_due: fd,
                margin_actual: ma,
                margin_required: mr,
                oi_actual: oa,
                oi_cap: oc,
                b_headroom_actual: ba,
                b_headroom_required: br,
                source_credit_used: su,
                source_credit_cap: sc,
                close_progress_done: cd,
                close_progress_target: ct,
                portfolio_width_n: n,
                recovery_fallback_backoff_blocks: rbb,
                recovery_fallback_backoff_min: rbm,
            },
        )
}

fn arb_slot_state() -> impl Strategy<Value = AssetSlotState> {
    (0u32..=10u32, 0u32..=10u32, 0u32..=10u32, 0u32..=10u32, 0u128..=1000u128, 0u128..=1000u128, 0u64..=1000u64)
        .prop_map(|(lc, lic, po, ac, bh, ir, e)| AssetSlotState {
            leg_count: lc,
            lien_count: lic,
            pending_obligation_count: po,
            active_close_count: ac,
            backing_held_num: bh,
            insurance_reserved_num: ir,
            epoch: e,
        })
}

fn arb_zero_slot_state() -> impl Strategy<Value = AssetSlotState> {
    (0u64..=1000u64).prop_map(AssetSlotState::empty)
}

fn arb_lifecycle() -> impl Strategy<Value = AssetLifecycle> {
    prop_oneof![
        Just(AssetLifecycle::Disabled),
        Just(AssetLifecycle::PendingActivation),
        Just(AssetLifecycle::Active),
        Just(AssetLifecycle::DrainOnly),
        Just(AssetLifecycle::Retired),
    ]
}

// ============================================================================
// Proptests
// ============================================================================

proptest! {
    /// **`allValid_iff`** (Lean): `all_valid` is equivalent to all
    /// flags being true.
    #[test]
    fn all_valid_iff_all_flags(env in arb_envelope()) {
        let conjunction = env.fee_ok && env.price_ok && env.funding_ok
            && env.margin_ok && env.oi_ok && env.b_headroom_ok
            && env.source_credit_ok && env.close_progress_ok
            && env.portfolio_ok && env.recovery_fallback_ok;
        prop_assert_eq!(env.all_valid(), conjunction);
    }

    /// **`fromWitness_feeOK_false_when_underpaid`** (Lean §14 #59):
    /// when feePaid < feeRequired, the derived fee_ok flag is false.
    #[test]
    fn from_witness_fee_ok_false_when_underpaid(mut w in arb_witness()) {
        w.fee_paid = 5;
        w.fee_required = 100;
        prop_assert!(!w.to_envelope().fee_ok);
    }

    /// **`fromWitness_priceOK_false_when_stale`** (Lean §14 #59).
    #[test]
    fn from_witness_price_ok_false_when_stale(mut w in arb_witness()) {
        w.price_age_blocks = 100;
        w.price_max_age_blocks = 5;
        prop_assert!(!w.to_envelope().price_ok);
    }

    /// **`fromWitness_marginOK_false_when_undermargined`** (Lean §14 #59).
    #[test]
    fn from_witness_margin_ok_false_when_under(mut w in arb_witness()) {
        w.margin_actual = 5;
        w.margin_required = 100;
        prop_assert!(!w.to_envelope().margin_ok);
    }

    /// **`fromWitness_portfolioOK_false_when_N_too_large`** (Lean
    /// §14 #88): N > MAX_PORTFOLIO_ASSETS_N forces flag false.
    #[test]
    fn from_witness_portfolio_ok_false_when_too_large(mut w in arb_witness()) {
        w.portfolio_width_n = MAX_PORTFOLIO_ASSETS_N + 1;
        prop_assert!(!w.to_envelope().portfolio_ok);
    }

    /// **`fromWitness_allValid_implies_fee_paid`** (Lean §14 #59):
    /// `allValid → feeRequired ≤ feePaid`. Decoding direction.
    #[test]
    fn from_witness_all_valid_implies_fee_paid(w in arb_witness()) {
        let env = w.to_envelope();
        if env.all_valid() {
            prop_assert!(w.fee_required <= w.fee_paid);
        }
    }

    /// **`fromWitness_allValid_implies_margin_satisfied`** (Lean §14 #59).
    #[test]
    fn from_witness_all_valid_implies_margin(w in arb_witness()) {
        let env = w.to_envelope();
        if env.all_valid() {
            prop_assert!(w.margin_required <= w.margin_actual);
        }
    }

    /// **`fromWitness_allValid_implies_sourceCredit_under_cap`** (Lean §14 #59).
    #[test]
    fn from_witness_all_valid_implies_source_credit(w in arb_witness()) {
        let env = w.to_envelope();
        if env.all_valid() {
            prop_assert!(w.source_credit_used <= w.source_credit_cap);
        }
    }

    /// **`empty_isReconciledZero`** (Lean): the empty slot is
    /// reconciled-zero.
    #[test]
    fn empty_is_reconciled_zero(epoch in 0u64..=1000u64) {
        prop_assert!(AssetSlotState::empty(epoch).is_reconciled_zero());
    }

    /// **`requires_full_envelope`** (Lean §14 #59): activation
    /// requires all envelope flags. -/
    #[test]
    fn activation_requires_full_envelope(
        s in arb_zero_slot_state(),
        l_before in arb_lifecycle(),
        env in arb_envelope(),
    ) {
        if let Some((post, l_after)) = activate(&s, l_before, &env) {
            prop_assert!(env.all_valid());
            prop_assert_eq!(l_after, AssetLifecycle::Active);
            prop_assert_eq!(post.epoch, s.epoch + 1);
        }
    }

    /// **`requires_zero_state`** (Lean §14 #60): activation
    /// requires the pre-state to be reconciled-zero.
    #[test]
    fn activation_requires_reconciled_zero(
        s in arb_slot_state(),
        l_before in arb_lifecycle(),
        env in arb_envelope(),
    ) {
        if let Some(_) = activate(&s, l_before, &env) {
            prop_assert!(s.is_reconciled_zero());
        }
    }

    /// **`bumps_epoch`** (Lean §14 #61): a successful activation
    /// bumps the slot epoch by 1.
    #[test]
    fn activation_bumps_epoch(
        s in arb_zero_slot_state(),
        l_before in arb_lifecycle(),
        env in arb_envelope(),
    ) {
        if let Some((post, _)) = activate(&s, l_before, &env) {
            prop_assert_eq!(post.epoch, s.epoch + 1);
        }
    }

    /// **`produces_active`** (Lean §14 #61): post-state lifecycle
    /// is `.Active`.
    #[test]
    fn activation_produces_active(
        s in arb_zero_slot_state(),
        l_before in arb_lifecycle(),
        env in arb_envelope(),
    ) {
        if let Some((_, l_after)) = activate(&s, l_before, &env) {
            prop_assert_eq!(l_after, AssetLifecycle::Active);
        }
    }

    /// **`activation_invalidates_priorEpoch_cert`** (Lean §14 #61):
    /// a cert valid pre-activation is not valid post-activation.
    #[test]
    fn activation_invalidates_prior_epoch_cert(
        s in arb_zero_slot_state(),
        l_before in arb_lifecycle(),
        env in arb_envelope(),
        cert_slot in any::<u32>(),
        cert_payload in any::<u128>(),
    ) {
        let cert = HealthCert {
            scoped_to_epoch: s.epoch,
            scoped_to_slot: cert_slot,
            payload: cert_payload,
        };
        prop_assert!(cert.valid_in(&s));
        if let Some((post, _)) = activate(&s, l_before, &env) {
            prop_assert!(!cert.valid_in(&post));
        }
    }

    /// **N too large rejects activation** (Lean §14 #88, via
    /// `portfolioOKFromN_false_when_too_large` composed with
    /// `rejects_when_portfolio_envelope_fails`).
    #[test]
    fn n_too_large_rejects_via_portfolio_ok(
        s in arb_zero_slot_state(),
        l_before in arb_lifecycle(),
        mut w in arb_witness(),
    ) {
        w.portfolio_width_n = MAX_PORTFOLIO_ASSETS_N + 1;
        let env = w.to_envelope();
        prop_assert!(!env.portfolio_ok);
        prop_assert!(activate(&s, l_before, &env).is_none());
    }

    /// **Activation rejects non-step lifecycles**: e.g. Active →
    /// Active or DrainOnly → Active is not a valid step.
    #[test]
    fn activation_rejects_invalid_lifecycle(
        s in arb_zero_slot_state(),
        env in arb_envelope(),
    ) {
        // Active → Active is not a valid step
        prop_assert!(activate(&s, AssetLifecycle::Active, &env).is_none());
        // Retired → Active is not a valid step
        prop_assert!(activate(&s, AssetLifecycle::Retired, &env).is_none());
    }
}
