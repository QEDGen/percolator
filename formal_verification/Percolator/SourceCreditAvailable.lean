/-
  Percolator.SourceCreditAvailable — Phase 3 port of
  `available_backing_num_for_source_credit_state`.

  Computes the available source-credit backing for a single domain.
  Per `v16.rs::MarketGroupV16::available_backing_num_for_source_credit_state`
  (line 7969):

      counterparty_available = fresh_reserved_backing − valid_liened_backing
      insurance_encumbered    = valid_liened_insurance + impaired_liened_insurance
      insurance_available     = insurance_credit_reserved − insurance_encumbered
      available_backing       = counterparty_available + insurance_available

  Preconditions (Rust errors if violated):
      fresh_reserved_backing ≥ valid_liened_backing
      insurance_credit_reserved ≥ insurance_encumbered

  Lean port returns `Option Nat`: `none` when a precondition fails,
  `some n` with the available-backing value otherwise.

  §14 contribution: this is the "available backing" half of #1
  (`source_domain_positive_credit_capped_by_realizable_backing`) and
  feeds the credit-rate formula in `Percolator/CreditRate.lean`
  (#50, `credit_rate_recomputation_bounded`).
-/

import Percolator.State
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

namespace SourceCreditState

-- ============================================================================
-- available_backing_num — pure ledger query
-- ============================================================================

/-- Insurance encumbrance: valid + impaired insurance liens. -/
def insuranceEncumbered (s : SourceCreditState) : Nat :=
  s.lienedAmounts.amount .Insurance .Valid
  + s.lienedAmounts.amount .Insurance .Impaired

/-- Lean spec mirror of `v16.rs::MarketGroupV16::available_backing_num_for_source_credit_state`
    (line 7969).

    Returns the per-domain available backing if both preconditions hold;
    `none` otherwise. Mirrors the Rust `Result<u128, V16Error>` shape:
    the two error cases in Rust correspond to the two `none` returns
    here. -/
def availableBackingNum (s : SourceCreditState) : Option Nat :=
  let cpValid := s.lienedAmounts.amount .Counterparty .Valid
  let insEnc := s.insuranceEncumbered
  if s.freshReservedBackingNum < cpValid then none
  else if s.insuranceCreditReservedNum < insEnc then none
  else some ((s.freshReservedBackingNum - cpValid) + (s.insuranceCreditReservedNum - insEnc))

/-- **Soundness — when `some`, the value matches the textbook formula**:
    `available = (fresh − valid_cp) + (insurance_reserved − insurance_encumbered)`. -/
theorem availableBackingNum_some_eq
    (s : SourceCreditState) (v : Nat) (h : s.availableBackingNum = some v) :
    v = (s.freshReservedBackingNum - s.lienedAmounts.amount .Counterparty .Valid)
        + (s.insuranceCreditReservedNum - s.insuranceEncumbered) := by
  unfold availableBackingNum at h
  by_cases h1 : s.freshReservedBackingNum < s.lienedAmounts.amount .Counterparty .Valid
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : s.insuranceCreditReservedNum < s.insuranceEncumbered
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  exact (Option.some.inj h).symm

/-- **Completeness — `some` returned iff both preconditions hold**. -/
theorem availableBackingNum_isSome_iff
    (s : SourceCreditState) :
    s.availableBackingNum.isSome
    ↔ s.lienedAmounts.amount .Counterparty .Valid ≤ s.freshReservedBackingNum
      ∧ s.insuranceEncumbered ≤ s.insuranceCreditReservedNum := by
  unfold availableBackingNum
  constructor
  · intro hsome
    by_cases h1 : s.freshReservedBackingNum < s.lienedAmounts.amount .Counterparty .Valid
    · rw [if_pos h1] at hsome; cases hsome
    rw [if_neg h1] at hsome
    by_cases h2 : s.insuranceCreditReservedNum < s.insuranceEncumbered
    · rw [if_pos h2] at hsome; cases hsome
    push_neg at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have hn1 : ¬ s.freshReservedBackingNum < s.lienedAmounts.amount .Counterparty .Valid := by omega
    have hn2 : ¬ s.insuranceCreditReservedNum < s.insuranceEncumbered := by omega
    rw [if_neg hn1, if_neg hn2]
    rfl

/-- **Direct value formula** under both preconditions. -/
theorem availableBackingNum_eq_of_preconditions
    (s : SourceCreditState)
    (h1 : s.lienedAmounts.amount .Counterparty .Valid ≤ s.freshReservedBackingNum)
    (h2 : s.insuranceEncumbered ≤ s.insuranceCreditReservedNum) :
    s.availableBackingNum
    = some ((s.freshReservedBackingNum - s.lienedAmounts.amount .Counterparty .Valid)
            + (s.insuranceCreditReservedNum - s.insuranceEncumbered)) := by
  unfold availableBackingNum
  have hn1 : ¬ s.freshReservedBackingNum < s.lienedAmounts.amount .Counterparty .Valid := by omega
  have hn2 : ¬ s.insuranceCreditReservedNum < s.insuranceEncumbered := by omega
  rw [if_neg hn1, if_neg hn2]

/-- **Bounded above by total reserves**: available backing never exceeds
    fresh_reserved_backing + insurance_credit_reserved. -/
theorem availableBackingNum_le_total_reserves
    (s : SourceCreditState) (v : Nat) (h : s.availableBackingNum = some v) :
    v ≤ s.freshReservedBackingNum + s.insuranceCreditReservedNum := by
  rw [availableBackingNum_some_eq s v h]
  have h1 : s.freshReservedBackingNum - s.lienedAmounts.amount .Counterparty .Valid
          ≤ s.freshReservedBackingNum := Nat.sub_le _ _
  have h2 : s.insuranceCreditReservedNum - s.insuranceEncumbered
          ≤ s.insuranceCreditReservedNum := Nat.sub_le _ _
  omega

/-- **Empty state has zero available backing** (and no preconditions
    violated). Sanity check. -/
theorem availableBackingNum_empty :
    SourceCreditState.empty.availableBackingNum = some 0 := by
  unfold availableBackingNum SourceCreditState.empty insuranceEncumbered
  simp [LienedAmountsBySource.empty]

end SourceCreditState

end Percolator.Spec
