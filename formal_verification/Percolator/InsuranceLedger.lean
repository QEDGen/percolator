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
import Percolator.BoundArith
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

-- ============================================================================
-- §14 #20: consume with explicit BOUND-unit ↔ vault-atom conversion
-- ============================================================================

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
