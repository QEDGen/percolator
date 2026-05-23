/-
  Percolator.ClosePriority — Phase 5 cluster 4 (close progress, part 1):
  cross-close priority ordering.

  Models the strict-total-order priority comparator from
  `spec.md:1238-1244`:

      ClosePriority = (
          higher certified_liq_deficit first,
          then higher total_abs_risk_notional,
          then older drift_reference_slot or close_start_slot,
          then lower immutable close_id
      )

  Closes the §14 invariants that depend on the ordering being
  irreflexive, asymmetric, transitive, and trichotomous over distinct
  `close_id`.

  §14 invariants addressed:
    - #68 `preemptive_close_priority_prevents_hold_and_wait_deadlock`
    - #92 `cross_close_priority_is_strict_total_order`
    - #93 `equal_priority_livelock_impossible`
-/

import Percolator.Defs
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

-- ============================================================================
-- ClosePriority — the four-component priority record
-- ============================================================================

/-- Mirror of the priority tuple in `spec.md:1239-1244`. `closeId`
    is the immutable tie-breaker; distinct closes have distinct
    `closeId` by construction (cf. §22 of the spec). -/
structure ClosePriority where
  certifiedLiqDeficit  : Nat
  totalAbsRiskNotional : Nat
  driftReferenceSlot   : Nat
  closeId              : Nat
  deriving DecidableEq, Repr

namespace ClosePriority

/-- **Strict less-than** = "higher priority than". Lex-compares on
    (deficit DESC, notional DESC, drift_slot ASC, closeId ASC). -/
def lt (a b : ClosePriority) : Prop :=
  a.certifiedLiqDeficit > b.certifiedLiqDeficit
  ∨ (a.certifiedLiqDeficit = b.certifiedLiqDeficit ∧
      a.totalAbsRiskNotional > b.totalAbsRiskNotional)
  ∨ (a.certifiedLiqDeficit = b.certifiedLiqDeficit ∧
      a.totalAbsRiskNotional = b.totalAbsRiskNotional ∧
      a.driftReferenceSlot < b.driftReferenceSlot)
  ∨ (a.certifiedLiqDeficit = b.certifiedLiqDeficit ∧
      a.totalAbsRiskNotional = b.totalAbsRiskNotional ∧
      a.driftReferenceSlot = b.driftReferenceSlot ∧
      a.closeId < b.closeId)

instance : Decidable (lt a b) := by unfold lt; infer_instance

instance : LT ClosePriority := ⟨lt⟩

theorem lt_def (a b : ClosePriority) :
    a < b ↔
      a.certifiedLiqDeficit > b.certifiedLiqDeficit
      ∨ (a.certifiedLiqDeficit = b.certifiedLiqDeficit ∧
          a.totalAbsRiskNotional > b.totalAbsRiskNotional)
      ∨ (a.certifiedLiqDeficit = b.certifiedLiqDeficit ∧
          a.totalAbsRiskNotional = b.totalAbsRiskNotional ∧
          a.driftReferenceSlot < b.driftReferenceSlot)
      ∨ (a.certifiedLiqDeficit = b.certifiedLiqDeficit ∧
          a.totalAbsRiskNotional = b.totalAbsRiskNotional ∧
          a.driftReferenceSlot = b.driftReferenceSlot ∧
          a.closeId < b.closeId) := by
  rfl

-- ============================================================================
-- §14 #92 (strict total order): irreflexivity, asymmetry, transitivity,
-- trichotomy (modulo equal-by-construction).
-- ============================================================================

/-- **§14 #92 (irreflexive)**: no priority is strictly less than itself. -/
theorem lt_irrefl (a : ClosePriority) : ¬ a < a := by
  rw [lt_def]
  intro h
  rcases h with h | h | h | h
  · exact Nat.lt_irrefl _ h
  · exact Nat.lt_irrefl _ h.2
  · exact Nat.lt_irrefl _ h.2.2
  · exact Nat.lt_irrefl _ h.2.2.2

/-- **§14 #92 (asymmetric)**: if A < B, then not B < A. -/
theorem lt_asymm (a b : ClosePriority) (h : a < b) : ¬ b < a := by
  rw [lt_def] at h ⊢
  intro h'
  rcases h with h | h | h | h <;> rcases h' with h' | h' | h' | h' <;> omega

/-- **§14 #92 (transitive)**: if A < B and B < C, then A < C. -/
theorem lt_trans (a b c : ClosePriority) (hab : a < b) (hbc : b < c) :
    a < c := by
  rw [lt_def] at hab hbc ⊢
  rcases hab with hab | hab | hab | hab <;> rcases hbc with hbc | hbc | hbc | hbc
  -- 16 cases; each reduces to nat-arithmetic chain
  all_goals first
    | (left; omega)
    | (right; left; omega)
    | (right; right; left; omega)
    | (right; right; right; omega)

/-- **§14 #93 (trichotomy modulo equality)**: any two ClosePriorities
    are comparable — either A < B, A = B, or B < A. -/
theorem lt_trichotomy (a b : ClosePriority) :
    a < b ∨ a = b ∨ b < a := by
  by_cases hd : a.certifiedLiqDeficit = b.certifiedLiqDeficit
  · by_cases hn : a.totalAbsRiskNotional = b.totalAbsRiskNotional
    · by_cases hs : a.driftReferenceSlot = b.driftReferenceSlot
      · by_cases hi : a.closeId = b.closeId
        · right; left
          cases a; cases b
          congr
        · rcases Nat.lt_or_gt_of_ne hi with hlt | hlt
          · left
            rw [lt_def]; right; right; right
            exact ⟨hd, hn, hs, hlt⟩
          · right; right
            rw [lt_def]; right; right; right
            exact ⟨hd.symm, hn.symm, hs.symm, hlt⟩
      · rcases Nat.lt_or_gt_of_ne hs with hlt | hlt
        · left
          rw [lt_def]; right; right; left
          exact ⟨hd, hn, hlt⟩
        · right; right
          rw [lt_def]; right; right; left
          exact ⟨hd.symm, hn.symm, hlt⟩
    · rcases Nat.lt_or_gt_of_ne hn with hlt | hlt
      · right; right
        rw [lt_def]; right; left
        exact ⟨hd.symm, hlt⟩
      · left
        rw [lt_def]; right; left
        exact ⟨hd, hlt⟩
  · rcases Nat.lt_or_gt_of_ne hd with hlt | hlt
    · right; right
      rw [lt_def]; left
      exact hlt
    · left
      rw [lt_def]; left
      exact hlt

-- ============================================================================
-- §14 #93 (equal-priority livelock impossible): distinct closeIds ⇒
-- comparable priorities (i.e., never equal).
-- ============================================================================

/-- **§14 #93**: two closes with distinct `closeId` are always
    comparable — neither can stall waiting on the other.

    The closeId is the final tiebreaker in `lt`; if every prior
    component is equal, the closeId discrimination kicks in. If any
    prior component differs, that resolves the order. -/
theorem distinct_closeId_strictly_comparable
    (a b : ClosePriority) (h : a.closeId ≠ b.closeId) :
    a < b ∨ b < a := by
  rcases lt_trichotomy a b with hab | heq | hba
  · exact .inl hab
  · -- a = b would imply a.closeId = b.closeId, contradicting h
    have : a.closeId = b.closeId := by rw [heq]
    exact absurd this h
  · exact .inr hba

-- ============================================================================
-- §14 #68 (no hold-and-wait deadlock): a strict total order has no
-- cycles. We witness this for the smallest interesting case (2- and
-- 3-cycles) which is what "hold-and-wait" requires.
-- ============================================================================

/-- **§14 #68 (no 2-cycle)**: A cannot hold and wait on B while B
    holds and waits on A.

    "A holds and waits on B" means A < B in priority (B must yield to
    A, but A is waiting on B). For a deadlock to form, B would also
    need to be waiting on A, i.e., B < A. Asymmetry forbids this. -/
theorem no_two_cycle (a b : ClosePriority) (hab : a < b) (hba : b < a) :
    False := lt_asymm a b hab hba

/-- **§14 #68 (no 3-cycle)**: A < B < C < A is impossible. -/
theorem no_three_cycle
    (a b c : ClosePriority) (hab : a < b) (hbc : b < c) (hca : c < a) :
    False :=
  no_two_cycle a c (lt_trans a b c hab hbc) hca

end ClosePriority

end Percolator.Spec
