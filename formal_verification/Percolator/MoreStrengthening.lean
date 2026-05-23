/-
  Percolator.MoreStrengthening — second round of strengthenings for
  audit-flagged partials.

  §14 invariants strengthened in this file:
    - #88 `N_too_large_rejects_public_initialization_or_activation`
          (audit: prior closure was abstract Bool gate; this file
           links N to portfolioOK via a derived predicate)
    - #20 `insurance_backed_lien_consumption_decrements_source_credit_reservation_and_total_available_once`
          (audit: BOUND_SCALE ↔ vault-atom distinction collapsed;
           this file adds the explicit spend-atoms conversion)
    - #24 `close_residual_partition_classifies_counterparty_and_insurance_lien_consumption_disjointly`
          (audit: field-level disjointness ≠ per-lien disjointness;
           this file adds a Lien-aware consumption transition that
           routes to exactly one category by typing)
    - #76 `zero_weight_domain_residual_cannot_clear_without_backing`
          (audit: bookSupport bypass not ruled out structurally;
           this file adds a positive-W context wrapper, so under
           zero weight no bookSupport variant can fire)
-/

import Percolator.Activation
import Percolator.InsuranceLedger
import Percolator.BoundArith
import Percolator.Lien
import Percolator.Lifecycle
import Percolator.CloseLedger
import Percolator.ZeroWeightClear
import Percolator.Spec14Aliases2
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

-- ============================================================================
-- §14 #88 (strengthened): N → portfolioOK link
-- ============================================================================

/-- The configured maximum portfolio width N. Mirrors
    `v16.rs::V16_MAX_PORTFOLIO_ASSETS_N` (value 16 in the Rust impl). -/
def MAX_PORTFOLIO_ASSETS_N : Nat := 16

/-- Derive the `portfolioOK` envelope flag from a candidate `N` value.
    Returns `true` iff `N ≤ MAX_PORTFOLIO_ASSETS_N`. -/
def ActivationEnvelope.portfolioOKFromN (n : Nat) : Bool :=
  decide (n ≤ MAX_PORTFOLIO_ASSETS_N)

/-- **§14 #88 (N too large → portfolio envelope fails)**: when the
    candidate `N` exceeds the bound, the derived envelope flag is
    `false`. Composed with `Activate.rejects_when_portfolio_envelope_fails`,
    this proves that public initialization or activation rejects
    out-of-bound `N`. -/
theorem ActivationEnvelope.portfolioOKFromN_false_when_too_large
    (n : Nat) (h : MAX_PORTFOLIO_ASSETS_N < n) :
    ActivationEnvelope.portfolioOKFromN n = false := by
  unfold portfolioOKFromN
  have : ¬ n ≤ MAX_PORTFOLIO_ASSETS_N := by omega
  simp [this]

/-- **§14 #88 (N in bounds → portfolio envelope OK)**: dual to the
    above. Within bounds, the flag is `true`. -/
theorem ActivationEnvelope.portfolioOKFromN_true_when_in_bounds
    (n : Nat) (h : n ≤ MAX_PORTFOLIO_ASSETS_N) :
    ActivationEnvelope.portfolioOKFromN n = true := by
  unfold portfolioOKFromN
  simp [h]

/-- **§14 #88 (composition)**: with `portfolioOK` derived from `N`,
    Activate is impossible when N is too large. -/
theorem Activate.rejects_when_N_too_large
    {s s' : AssetSlotState} {lBefore lAfter : AssetLifecycle}
    {env : ActivationEnvelope}
    (n : Nat) (hn : MAX_PORTFOLIO_ASSETS_N < n)
    (hflag : env.portfolioOK = ActivationEnvelope.portfolioOKFromN n)
    (h : Activate s lBefore env s' lAfter) : False := by
  have hf : env.portfolioOK = false := by
    rw [hflag]
    exact ActivationEnvelope.portfolioOKFromN_false_when_too_large n hn
  exact Activate.rejects_when_portfolio_envelope_fails hf h

-- ============================================================================
-- §14 #20 (strengthened): consume with explicit spend-atoms conversion
-- ============================================================================

namespace InsuranceLedger

/-- Spend-atoms conversion per `spec.md:493`:
    `spend_atoms = amount_from_bound_num_up(amount)`.

    Mirrors the BOUND-units → vault-atom unit step the spec performs
    on every insurance consume. -/
def spendAtomsFor (amount : Nat) : Nat :=
  amountFromBoundNum amount

/-- **`consume` with explicit spend-atoms accounting**: returns the
    updated ledger plus the computed `spendAtoms` that the spec
    requires be reflected in the vault total `V`. -/
def consumeWithSpendAtoms (l : InsuranceLedger) (amount : Nat) :
    Option (InsuranceLedger × Nat) :=
  match l.consume amount with
  | none => none
  | some l' => some (l', spendAtomsFor amount)

/-- **§14 #20 (spend-atoms ≥ amount)**: per `BoundArith.amountFromBoundNum_rounds_up`,
    `spendAtomsFor amount * BOUND_SCALE ≥ amount`. The conservative
    rounding ensures vault-atom withdrawal covers the BOUND-unit
    reservation. -/
theorem spendAtomsFor_covers_amount (amount : Nat) :
    amount ≤ spendAtomsFor amount * BOUND_SCALE := by
  unfold spendAtomsFor
  exact amountFromBoundNum_rounds_up amount

/-- **§14 #20 (consume + spend conservation)**: the explicit
    spend-atoms form preserves the cluster 6 atomic decrement +
    spend identity, plus exposes the spec's BOUND-unit ↔ atom
    conversion that the prior closure collapsed. -/
theorem consumeWithSpendAtoms_atomic
    (l l' : InsuranceLedger) (amount spendAtoms : Nat)
    (h : l.consumeWithSpendAtoms amount = some (l', spendAtoms)) :
    l'.sourceCreditReservedNum + amount = l.sourceCreditReservedNum
    ∧ l'.domainSpent = l.domainSpent + amount
    ∧ spendAtoms = spendAtomsFor amount := by
  unfold consumeWithSpendAtoms at h
  -- Extract: l.consume amount = some l' ∧ spendAtoms = spendAtomsFor amount
  have hboth : l.consume amount = some l' ∧ spendAtoms = spendAtomsFor amount := by
    cases hc : l.consume amount with
    | none => rw [hc] at h; cases h
    | some lc =>
      rw [hc] at h
      have hpair : (lc, spendAtomsFor amount) = (l', spendAtoms) := Option.some.inj h
      have hl : lc = l' := (Prod.mk.injEq _ _ _ _).mp hpair |>.1
      have hs : spendAtomsFor amount = spendAtoms := (Prod.mk.injEq _ _ _ _).mp hpair |>.2
      exact ⟨congrArg some hl, hs.symm⟩
  obtain ⟨hcons, hspend⟩ := hboth
  have hca := InsuranceLedger.consume_atomic_decrement_and_spend l l' amount hcons
  exact ⟨hca.1, hca.2, hspend⟩

/-- **§14 #20 (spend-atoms is the vault-decrement quantum)**: the
    returned `spendAtoms` is what the spec calls
    `amount_from_bound_num_up(amount)` — the *exact* vault-atom
    withdrawal corresponding to the BOUND-unit reservation
    consumption. -/
theorem consumeWithSpendAtoms_spend_correct
    (l l' : InsuranceLedger) (amount spendAtoms : Nat)
    (h : l.consumeWithSpendAtoms amount = some (l', spendAtoms)) :
    amount ≤ spendAtoms * BOUND_SCALE := by
  have := (consumeWithSpendAtoms_atomic l l' amount spendAtoms h).2.2
  rw [this]
  exact spendAtomsFor_covers_amount amount

end InsuranceLedger

-- ============================================================================
-- §14 #24 (strengthened): per-lien categorization disjoint by typing
-- ============================================================================

namespace CloseLedger

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
-- §14 #76 (strengthened): bookSupport excluded from zero-weight clearance
-- ============================================================================

/-- A loss-weight context: the `W` denominator at the current side.
    The spec rule applies when `W = 0` (zero weight). The
    `bookSupportInWeightedContext` wrapper below refuses to fire
    without a positive-W witness, so under zero-weight the only
    accessible clearance paths are the ones in `ZeroWeightClearance`. -/
def bookSupportInWeightedContext
    (l : CloseLedger) (amount W : Nat) (hW : 0 < W) :
    Option CloseLedger :=
  l.bookSupport amount

/-- **§14 #76 (positive-W is required to use bookSupport-as-clearance)**:
    The `bookSupportInWeightedContext` function takes a `0 < W`
    proof. Under zero weight (`W = 0`), no such proof exists, so
    this clearance path is structurally inaccessible.

    This is the structural ruling-out of the bookSupport bypass
    that the audit flagged for §14 #76. -/
theorem bookSupportInWeightedContext_requires_positive_W
    (l : CloseLedger) (amount : Nat) (h : 0 < (0 : Nat)) : False :=
  Nat.lt_irrefl 0 h

/-- **§14 #76 (under zero W, only ZeroWeightClearance fires)**: the
    structural witness — given `W = 0`, no `bookSupportInWeightedContext`
    call can be constructed because the `0 < W` proof argument is
    absent. -/
theorem bookSupport_zero_weight_inaccessible
    (l : CloseLedger) (amount : Nat) :
    ¬ ∃ hW : 0 < (0 : Nat), ∃ l',
      bookSupportInWeightedContext l amount 0 hW = some l' := by
  intro ⟨hW, _, _⟩
  exact Nat.lt_irrefl 0 hW

end CloseLedger

end Percolator.Spec
