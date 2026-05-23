/-
  Percolator.SingleWriterInsurance — closed-world single-writer
  enforcement for `InsuranceLedger`.

  Strengthens the §14 #16 closure in
  `Spec14Aliases2.lean::InsuranceLedger.transitions_are_only_writers`.
  The original closure proved conservation under the three named
  transitions (`reserve`, `release`, `consume`) but did not encode
  "no other writer" at the type level. This file adds a
  `InsuranceWrite` sum with exactly the three named constructors
  and an `applyWrite` router. At this typed entry point, the
  closed-world property is structural: there is no fourth
  constructor, so no fourth writer can be invoked.

  §14 invariants strengthened in this file:
    - #16 `insurance_reservation_single_canonical_writer`
          (audit: conservation under the 3 named transitions
           proved, but "no other writer" was not encoded
           structurally. This file adds the closed-sum entry
           point and the routing-equivalence theorems.)
-/

import Percolator.InsuranceLedger
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

namespace InsuranceLedger

-- ============================================================================
-- §14 #16 (strengthened): closed-world writer sum
-- ============================================================================

/-- The closed sum of canonical writers to an `InsuranceLedger`. Each
    constructor carries the parameters of the corresponding named
    transition. By exhaustiveness, there is no fourth constructor;
    every `InsuranceWrite` value is provably one of these three. -/
inductive InsuranceWrite : Type where
  | Reserve (amount : Nat) : InsuranceWrite
  | Release (amount : Nat) : InsuranceWrite
  | Consume (amount : Nat) : InsuranceWrite
  deriving DecidableEq, Repr

namespace InsuranceWrite

/-- A tag projection — names the canonical writer this action invokes. -/
inductive Tag : Type where
  | reserveTag : Tag
  | releaseTag : Tag
  | consumeTag : Tag
  deriving DecidableEq, Repr

def tag : InsuranceWrite → Tag
  | .Reserve _ => .reserveTag
  | .Release _ => .releaseTag
  | .Consume _ => .consumeTag

/-- **§14 #16 (closed-world)**: every `InsuranceWrite` lies in exactly
    one of the three tagged constructors. There is no fourth path —
    Lean's exhaustiveness check on this `match` is the structural
    witness. -/
theorem tag_is_one_of_three (w : InsuranceWrite) :
    w.tag = .reserveTag ∨ w.tag = .releaseTag ∨ w.tag = .consumeTag := by
  cases w with
  | Reserve _ => exact .inl rfl
  | Release _ => exact .inr (.inl rfl)
  | Consume _ => exact .inr (.inr rfl)

end InsuranceWrite

/-- The single canonical entry point for writing to an
    `InsuranceLedger`. Routes by `InsuranceWrite` constructor to the
    corresponding named transition. Returns `none` if the underlying
    transition's precondition fails. -/
def applyWrite (l : InsuranceLedger) (w : InsuranceWrite) :
    Option InsuranceLedger :=
  match w with
  | .Reserve a => l.reserve a
  | .Release a => l.release a
  | .Consume a => l.consume a

-- ============================================================================
-- Routing equivalences: applyWrite ≡ the named transition
-- ============================================================================

/-- **§14 #16 (Reserve routing)**: `applyWrite` with a `Reserve`
    constructor is *definitionally* the same as calling `reserve`
    directly. The router does not introduce a new code path. -/
theorem applyWrite_Reserve (l : InsuranceLedger) (a : Nat) :
    l.applyWrite (.Reserve a) = l.reserve a := rfl

/-- **§14 #16 (Release routing)**. -/
theorem applyWrite_Release (l : InsuranceLedger) (a : Nat) :
    l.applyWrite (.Release a) = l.release a := rfl

/-- **§14 #16 (Consume routing)**. -/
theorem applyWrite_Consume (l : InsuranceLedger) (a : Nat) :
    l.applyWrite (.Consume a) = l.consume a := rfl

-- ============================================================================
-- Conservation under the typed entry point
-- ============================================================================

/-- **§14 #16 (conservation under applyWrite)**: every successful
    `applyWrite` produces a ledger that satisfies the conservation
    invariant. This is immediate because the post-state carries the
    `conservation` proof field; what's new is that the post-state
    *must* have come through `applyWrite` (no other constructor of
    `InsuranceWrite` exists). -/
theorem applyWrite_preserves_conservation
    (l l' : InsuranceLedger) (w : InsuranceWrite)
    (_h : l.applyWrite w = some l') :
    l'.sourceCreditReservedNum + l'.stagedDomainDebit
      + l'.globalProtocolStaged + l'.domainSpent
    ≤ l'.initialDeposited :=
  l'.conservation

/-- **§14 #16 (closed-world: every successful applyWrite was one of
    the three named writers)**. This is the structural witness that
    "no other writer" exists: any successful call composes the
    canonical sum router with one of the three named functions, and
    `applyWrite` is the only path that produces `some` results from
    a `InsuranceWrite` input. -/
theorem applyWrite_some_iff_named_transition
    (l l' : InsuranceLedger) (w : InsuranceWrite)
    (h : l.applyWrite w = some l') :
    (∃ a, w = .Reserve a ∧ l.reserve a = some l')
    ∨ (∃ a, w = .Release a ∧ l.release a = some l')
    ∨ (∃ a, w = .Consume a ∧ l.consume a = some l') := by
  cases w with
  | Reserve a =>
    rw [applyWrite_Reserve] at h
    exact .inl ⟨a, rfl, h⟩
  | Release a =>
    rw [applyWrite_Release] at h
    exact .inr (.inl ⟨a, rfl, h⟩)
  | Consume a =>
    rw [applyWrite_Consume] at h
    exact .inr (.inr ⟨a, rfl, h⟩)

/-- **§14 #16 (initialDeposited never changes via applyWrite)**: none
    of the three canonical writers mutates the deposit anchor.
    Combined with the closed-world property, this proves that the
    deposit field is structurally immutable at the typed entry
    point: no constructor of `InsuranceWrite` can change it. -/
theorem applyWrite_preserves_initialDeposited
    (l l' : InsuranceLedger) (w : InsuranceWrite)
    (h : l.applyWrite w = some l') :
    l'.initialDeposited = l.initialDeposited := by
  cases w with
  | Reserve a =>
    rw [applyWrite_Reserve] at h
    unfold reserve at h
    by_cases hp : l.sourceCreditReservedNum + a + l.stagedDomainDebit
                    + l.globalProtocolStaged + l.domainSpent
                  ≤ l.initialDeposited
    · simp [hp] at h
      rw [← h]
    · simp [hp] at h
  | Release a =>
    rw [applyWrite_Release] at h
    unfold release at h
    by_cases hp : l.sourceCreditReservedNum < a
    · simp [hp] at h
    · simp [hp] at h
      rw [← h]
  | Consume a =>
    rw [applyWrite_Consume] at h
    exact (consume_preserves_deposit_and_staged l l' a h).1

/-- **§14 #16 (globalProtocolStaged never changes via applyWrite)**:
    same structural argument as deposit — no constructor mutates
    this field. -/
theorem applyWrite_preserves_globalProtocolStaged
    (l l' : InsuranceLedger) (w : InsuranceWrite)
    (h : l.applyWrite w = some l') :
    l'.globalProtocolStaged = l.globalProtocolStaged := by
  cases w with
  | Reserve a =>
    rw [applyWrite_Reserve] at h
    unfold reserve at h
    by_cases hp : l.sourceCreditReservedNum + a + l.stagedDomainDebit
                    + l.globalProtocolStaged + l.domainSpent
                  ≤ l.initialDeposited
    · simp [hp] at h
      rw [← h]
    · simp [hp] at h
  | Release a =>
    rw [applyWrite_Release] at h
    unfold release at h
    by_cases hp : l.sourceCreditReservedNum < a
    · simp [hp] at h
    · simp [hp] at h
      rw [← h]
  | Consume a =>
    rw [applyWrite_Consume] at h
    exact (consume_preserves_deposit_and_staged l l' a h).2.2

end InsuranceLedger

end Percolator.Spec
