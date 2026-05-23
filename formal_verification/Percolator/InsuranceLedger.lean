/-
  Percolator.InsuranceLedger — Phase 5 cluster 6 (part 3):
  insurance ledger conservation and no-double-counting.

  Closes the §14 invariants deferred from cluster 2 (token-value-flow
  soundness) that required a stateful, sequence-of-flows model rather
  than per-flow row reasoning.

  Mirrors `spec.md:711-735` (`InsuranceLedger`) plus the conservation
  invariants in `spec.md:725-735`:

      live_source_credit_insurance + live_domain_staged
        + global_protocol_staged_debits
      <= total_available

  §14 invariants addressed:
    - #13 `insurance_credit_reservation_globally_conserved`
    - #14 `insurance_spend_not_double_counted_as_live_encumbrance`
-/

import Percolator.Defs
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

-- ============================================================================
-- InsuranceLedger — minimal single-domain model
-- ============================================================================

/-- Insurance ledger, single-domain projection. Mirrors the fields of
    `v16.rs::InsuranceLedger` (spec.md:711) most relevant to §14 #13/#14:

      - `initialDeposited`  — cumulative deposits (invariant anchor)
      - `sourceCreditReservedNum` — canonical live source-credit reservation
      - `domainSpent`       — cumulative spent for cap/audit
      - `stagedDomainDebit` — committed-but-not-yet-applied debit

    `totalAvailable = initialDeposited - domainSpent` is derivable from
    the conservation invariant rather than stored. -/
structure InsuranceLedger where
  initialDeposited        : Nat
  sourceCreditReservedNum : Nat
  domainSpent             : Nat
  stagedDomainDebit       : Nat
  globalProtocolStaged    : Nat
  /-- The §14 #13 conservation invariant carried as a structure
      proof. Reservation + staged ≤ available capital. -/
  conservation :
    sourceCreditReservedNum + stagedDomainDebit + globalProtocolStaged
      + domainSpent
    ≤ initialDeposited

namespace InsuranceLedger

/-- The empty ledger — no deposits, no reservations, no spend. -/
def empty : InsuranceLedger where
  initialDeposited        := 0
  sourceCreditReservedNum := 0
  domainSpent             := 0
  stagedDomainDebit       := 0
  globalProtocolStaged    := 0
  conservation := by simp

/-- Initialize a ledger with `deposit` units of capital. -/
def initial (deposit : Nat) : InsuranceLedger where
  initialDeposited        := deposit
  sourceCreditReservedNum := 0
  domainSpent             := 0
  stagedDomainDebit       := 0
  globalProtocolStaged    := 0
  conservation := by simp

/-- Current available capital: deposit minus spent. -/
def totalAvailable (l : InsuranceLedger) : Nat :=
  l.initialDeposited - l.domainSpent

-- ============================================================================
-- Transitions: reserve, release, consume
-- ============================================================================

/-- **Reserve**: add `amount` to source-credit reservation. Fails if
    the new total would violate conservation. -/
def reserve (l : InsuranceLedger) (amount : Nat) : Option InsuranceLedger :=
  if h : l.sourceCreditReservedNum + amount + l.stagedDomainDebit
          + l.globalProtocolStaged + l.domainSpent
        ≤ l.initialDeposited then
    some {
      l with
      sourceCreditReservedNum := l.sourceCreditReservedNum + amount
      conservation := by
        have := l.conservation
        linarith
    }
  else none

/-- **Release**: remove `amount` from source-credit reservation
    (without spending). -/
def release (l : InsuranceLedger) (amount : Nat) : Option InsuranceLedger :=
  if hlt : l.sourceCreditReservedNum < amount then none
  else
    some {
      l with
      sourceCreditReservedNum := l.sourceCreditReservedNum - amount
      conservation := by
        have hc := l.conservation
        have hle : amount ≤ l.sourceCreditReservedNum := Nat.not_lt.mp hlt
        omega
    }

/-- **Consume**: spend `amount`. Decrements `sourceCreditReservedNum`
    and increments `domainSpent` in one atomic step — the §14 #14
    "not double-counted" property is structural here: the same
    `amount` cannot remain reserved after spending, because the same
    transition does both. -/
def consume (l : InsuranceLedger) (amount : Nat) : Option InsuranceLedger :=
  if hlt : l.sourceCreditReservedNum < amount then none
  else
    some {
      l with
      sourceCreditReservedNum := l.sourceCreditReservedNum - amount
      domainSpent             := l.domainSpent + amount
      conservation := by
        have hc := l.conservation
        have hle : amount ≤ l.sourceCreditReservedNum := Nat.not_lt.mp hlt
        omega
    }

-- ============================================================================
-- §14 #13: global conservation across all transitions
-- ============================================================================

/-- **§14 #13**: the conservation invariant holds at every state —
    immediate from the `conservation` field carried by the structure. -/
theorem conservation_holds (l : InsuranceLedger) :
    l.sourceCreditReservedNum + l.stagedDomainDebit
      + l.globalProtocolStaged + l.domainSpent
    ≤ l.initialDeposited :=
  l.conservation

/-- **§14 #13 (reserve preserves conservation)**: any successful
    reserve transition produces a ledger that still satisfies
    conservation. Carried by the `conservation` proof field in the
    new structure. -/
theorem reserve_preserves_conservation
    (l l' : InsuranceLedger) (amount : Nat) (h : l.reserve amount = some l') :
    l'.sourceCreditReservedNum + l'.stagedDomainDebit
      + l'.globalProtocolStaged + l'.domainSpent
    ≤ l'.initialDeposited :=
  l'.conservation

theorem release_preserves_conservation
    (l l' : InsuranceLedger) (amount : Nat) (h : l.release amount = some l') :
    l'.sourceCreditReservedNum + l'.stagedDomainDebit
      + l'.globalProtocolStaged + l'.domainSpent
    ≤ l'.initialDeposited :=
  l'.conservation

theorem consume_preserves_conservation
    (l l' : InsuranceLedger) (amount : Nat) (h : l.consume amount = some l') :
    l'.sourceCreditReservedNum + l'.stagedDomainDebit
      + l'.globalProtocolStaged + l'.domainSpent
    ≤ l'.initialDeposited :=
  l'.conservation

-- ============================================================================
-- §14 #14: spend not double-counted as live encumbrance
-- ============================================================================

/-- **§14 #14 (consume is atomic decrement+spend)**: when `consume`
    succeeds, the reservation decreases by `amount` and `domainSpent`
    increases by `amount` in the same step. The same atom cannot be
    both reserved and spent. -/
theorem consume_atomic_decrement_and_spend
    (l l' : InsuranceLedger) (amount : Nat) (h : l.consume amount = some l') :
    l'.sourceCreditReservedNum + amount = l.sourceCreditReservedNum
    ∧ l'.domainSpent = l.domainSpent + amount := by
  unfold consume at h
  by_cases hlt : l.sourceCreditReservedNum < amount
  · simp [hlt] at h
  · push_neg at hlt
    simp [hlt] at h
    have hl' := h.symm
    constructor
    · have : l'.sourceCreditReservedNum = l.sourceCreditReservedNum - amount := by
        rw [hl']
      omega
    · have : l'.domainSpent = l.domainSpent + amount := by
        rw [hl']
      exact this

/-- **§14 #14 (initial deposit and staged unchanged)**: consume does
    not move money — it reclassifies reserved into spent against the
    same `initialDeposited` total. -/
theorem consume_preserves_deposit_and_staged
    (l l' : InsuranceLedger) (amount : Nat) (h : l.consume amount = some l') :
    l'.initialDeposited = l.initialDeposited
    ∧ l'.stagedDomainDebit = l.stagedDomainDebit
    ∧ l'.globalProtocolStaged = l.globalProtocolStaged := by
  unfold consume at h
  by_cases hlt : l.sourceCreditReservedNum < amount
  · simp [hlt] at h
  · push_neg at hlt
    simp [hlt] at h
    have hl' := h.symm
    refine ⟨?_, ?_, ?_⟩
    all_goals (rw [hl'])

/-- **§14 #14 (release does not increment spend)**: a release returns
    reserved capacity to available without ever incrementing
    `domainSpent`. The reservation and spend counters cannot drift. -/
theorem release_preserves_domainSpent
    (l l' : InsuranceLedger) (amount : Nat) (h : l.release amount = some l') :
    l'.domainSpent = l.domainSpent := by
  unfold release at h
  by_cases hlt : l.sourceCreditReservedNum < amount
  · simp [hlt] at h
  · simp [hlt] at h
    rw [h.symm]

/-- **§14 #14 (reserve does not increment spend)**: reserving capacity
    leaves the spend counter untouched. -/
theorem reserve_preserves_domainSpent
    (l l' : InsuranceLedger) (amount : Nat) (h : l.reserve amount = some l') :
    l'.domainSpent = l.domainSpent := by
  unfold reserve at h
  split_ifs at h
  all_goals cases h
  rfl

/-- **§14 #14 (total reservation+spend bounded by deposit)**: a direct
    corollary of conservation — the sum of currently reserved and
    cumulatively spent capital is bounded by what was ever deposited. -/
theorem reservedPlusSpent_le_deposit (l : InsuranceLedger) :
    l.sourceCreditReservedNum + l.domainSpent ≤ l.initialDeposited := by
  have := l.conservation
  omega

end InsuranceLedger

-- ============================================================================
-- Sequence-of-flows model: a list of transitions applied in order
-- ============================================================================

/-- A single insurance-ledger transition — exactly the shape of the
    three lifecycle helpers above. The sequence-of-flows model below
    walks a list of these to witness invariants across an entire
    history. -/
inductive InsuranceTxn : Type where
  | reserve (amount : Nat)
  | release (amount : Nat)
  | consume (amount : Nat)
  deriving Repr

namespace InsuranceTxn

/-- Apply one transition to a ledger, returning `none` if the
    precondition fails. -/
def apply (t : InsuranceTxn) (l : InsuranceLedger) : Option InsuranceLedger :=
  match t with
  | .reserve amount => l.reserve amount
  | .release amount => l.release amount
  | .consume amount => l.consume amount

end InsuranceTxn

namespace InsuranceLedger

/-- Apply a sequence of transitions. Returns `some` only if every
    transition's precondition was satisfied. -/
def applySeq (l : InsuranceLedger) : List InsuranceTxn → Option InsuranceLedger
  | [] => some l
  | t :: rest =>
    match t.apply l with
    | none => none
    | some l' => l'.applySeq rest

/-- **§14 #13 (sequence-of-flows conservation)**: conservation holds
    after every prefix of an arbitrary transition sequence. -/
theorem applySeq_preserves_conservation
    (l l' : InsuranceLedger) (ts : List InsuranceTxn)
    (h : l.applySeq ts = some l') :
    l'.sourceCreditReservedNum + l'.stagedDomainDebit
      + l'.globalProtocolStaged + l'.domainSpent
    ≤ l'.initialDeposited :=
  l'.conservation

/-- **§14 #13 (sequence-of-flows: spend never exceeds deposit)**: the
    cumulative `domainSpent` after any history is bounded by
    `initialDeposited`. -/
theorem applySeq_spend_bounded
    (l l' : InsuranceLedger) (ts : List InsuranceTxn)
    (h : l.applySeq ts = some l') :
    l'.domainSpent ≤ l'.initialDeposited :=
  Nat.le_trans (Nat.le_add_left _ _) (reservedPlusSpent_le_deposit l')

end InsuranceLedger

end Percolator.Spec
