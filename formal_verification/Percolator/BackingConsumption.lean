/-
  Percolator.BackingConsumption — loser-capital decrement preserving
  senior-vault invariants.

  Mirrors the spec rule (§10) that backing consumption against a
  liquidating counterparty reduces *that* account's capital while
  preserving the system-level senior accounting:

      vault = sum_i C_i + I + escrows + residue + …  (per §5.1.1)

  The §14 #55 invariant is that backing consumption decrements the
  loser's `C_i` and increments a senior-accounted destination
  category (booked loss, support consumed, or insurance committed)
  by the same amount — the vault total never moves.

  §14 invariants addressed:
    - #55 `backing_consumption_reduces_loser_capital_and_preserves_senior_invariants`
-/

import Percolator.Defs
import Percolator.StockReconciliation
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

/-- Two-account vault snapshot for the backing-consumption transition.

    `loserCapital` — the losing counterparty's capital. Will be
    decremented by a successful consumption.

    `winnerCapital` — the profitable counterparty's capital, opposite
    side. Untouched by the consumption (the credit flows to a
    booked-loss class, not to the winner's `C_i`).

    `bookedLoss` — the senior destination for consumed backing. The
    spec partitions this further (support_consumed,
    consumed_counterparty_credit_lien_backing, etc.); here we collapse
    them into a single "booked loss" category to focus on vault
    conservation.

    `vault` — the protocol vault. The §14 #55 senior invariant is
    `vault = loserCapital + winnerCapital + bookedLoss` (in the
    abstracted partition). -/
structure VaultSnapshot where
  loserCapital  : Nat
  winnerCapital : Nat
  bookedLoss    : Nat
  vault         : Nat
  deriving Repr

namespace VaultSnapshot

/-- The senior invariant: `vault = loserCapital + winnerCapital + bookedLoss`. -/
def seniorInvariant (s : VaultSnapshot) : Prop :=
  s.vault = s.loserCapital + s.winnerCapital + s.bookedLoss

instance (s : VaultSnapshot) : Decidable s.seniorInvariant := by
  unfold seniorInvariant; infer_instance

/-- **The atomic backing-consumption transition**: subtract `amount`
    from `loserCapital` and add the same `amount` to `bookedLoss`.
    `winnerCapital` and `vault` are unchanged.

    Returns `none` when the loser cannot cover the amount. The
    one-result form makes the §14 #55 atomicity structural. -/
def consumeBacking (s : VaultSnapshot) (amount : Nat) : Option VaultSnapshot :=
  if s.loserCapital < amount then none
  else some {
    s with
    loserCapital := s.loserCapital - amount
    bookedLoss   := s.bookedLoss + amount
  }

/-- **§14 #55 (loser capital strictly decreases)**: a successful
    consume of `amount > 0` strictly reduces `loserCapital`. -/
theorem consumeBacking_decreases_loser
    (s s' : VaultSnapshot) (amount : Nat) (hpos : 0 < amount)
    (h : s.consumeBacking amount = some s') :
    s'.loserCapital < s.loserCapital := by
  unfold consumeBacking at h
  by_cases hlt : s.loserCapital < amount
  · simp [hlt] at h
  · push_neg at hlt
    simp [hlt] at h
    have hs' := h.symm
    rw [hs']
    change s.loserCapital - amount < s.loserCapital
    omega

/-- **§14 #55 (loser capital exact decrement)**: the decrement is
    exactly `amount`. -/
theorem consumeBacking_loser_decrement
    (s s' : VaultSnapshot) (amount : Nat)
    (h : s.consumeBacking amount = some s') :
    s'.loserCapital + amount = s.loserCapital := by
  unfold consumeBacking at h
  by_cases hlt : s.loserCapital < amount
  · simp [hlt] at h
  · push_neg at hlt
    simp [hlt] at h
    have hs' := h.symm
    rw [hs']
    change s.loserCapital - amount + amount = s.loserCapital
    omega

/-- **§14 #55 (booked loss exact increment)**: the booked-loss
    category receives the consumed amount. -/
theorem consumeBacking_booked_increment
    (s s' : VaultSnapshot) (amount : Nat)
    (h : s.consumeBacking amount = some s') :
    s'.bookedLoss = s.bookedLoss + amount := by
  unfold consumeBacking at h
  by_cases hlt : s.loserCapital < amount
  · simp [hlt] at h
  · push_neg at hlt
    simp [hlt] at h
    have hs' := h.symm
    rw [hs']

/-- **§14 #55 (winner capital untouched)**: the winner's capital is
    not affected by backing consumption from the loser. -/
theorem consumeBacking_preserves_winner
    (s s' : VaultSnapshot) (amount : Nat)
    (h : s.consumeBacking amount = some s') :
    s'.winnerCapital = s.winnerCapital := by
  unfold consumeBacking at h
  by_cases hlt : s.loserCapital < amount
  · simp [hlt] at h
  · push_neg at hlt
    simp [hlt] at h
    have hs' := h.symm
    rw [hs']

/-- **§14 #55 (vault preserved)**: the protocol vault is unchanged
    by the consumption — the transition is internal accounting. -/
theorem consumeBacking_preserves_vault
    (s s' : VaultSnapshot) (amount : Nat)
    (h : s.consumeBacking amount = some s') :
    s'.vault = s.vault := by
  unfold consumeBacking at h
  by_cases hlt : s.loserCapital < amount
  · simp [hlt] at h
  · push_neg at hlt
    simp [hlt] at h
    have hs' := h.symm
    rw [hs']

/-- **§14 #55 (senior invariant preserved)**: if the pre-state
    satisfies the senior invariant, so does the post-state. The vault
    total never moves, and the loser-capital decrement is mirrored
    one-for-one by the booked-loss increment. -/
theorem consumeBacking_preserves_seniorInvariant
    (s s' : VaultSnapshot) (amount : Nat)
    (hpre : s.seniorInvariant) (h : s.consumeBacking amount = some s') :
    s'.seniorInvariant := by
  unfold seniorInvariant at hpre ⊢
  have hl := consumeBacking_loser_decrement s s' amount h
  have hb := consumeBacking_booked_increment s s' amount h
  have hw := consumeBacking_preserves_winner s s' amount h
  have hv := consumeBacking_preserves_vault s s' amount h
  omega

/-- **§14 #55 (fail-closed)**: when the loser cannot cover the
    amount, the transition is rejected entirely — no partial
    capital decrement, no booked-loss change. -/
theorem consumeBacking_fails_when_underbacked
    (s : VaultSnapshot) (amount : Nat) (h : s.loserCapital < amount) :
    s.consumeBacking amount = none := by
  unfold consumeBacking
  simp [h]

-- ============================================================================
-- §14 #55: VaultSnapshot embeds into 10-class StockClasses
-- ============================================================================

/-- Embed a `VaultSnapshot` into a 10-class `StockClasses` partition.

    `loserCapital` and `winnerCapital` fold into `cTot` (the per-
    account capital aggregate). `bookedLoss` lands in
    `settlementRoundingResidue` (protocol-owned residue from the
    booking — the spec-aligned target for unallocated loss). The
    other eight classes are zero in the simplified vault snapshot. -/
def embed (s : VaultSnapshot) : StockClasses where
  cTot                       := s.loserCapital + s.winnerCapital
  insurance                  := 0
  cancelDepositEscrow        := 0
  pendingObligationEscrow    := 0
  closeStagedQuoteReserve    := 0
  resolvedPayoutEscrow       := 0
  explicitBackedLossReserve  := 0
  settlementRoundingResidue  := s.bookedLoss
  protocolFeePayable         := 0
  unallocatedProtocolSurplus := 0

/-- **§14 #55 (embed preserves senior invariant in 10-class form)**:
    when the source snapshot satisfies the 3-class senior invariant
    `vault = loserCapital + winnerCapital + bookedLoss`, the embedded
    `StockClasses` satisfies the 10-class reconciliation
    `vault = totalV`. -/
theorem embed_totalV_eq_vault (s : VaultSnapshot) (h : s.seniorInvariant) :
    s.embed.totalV = s.vault := by
  unfold seniorInvariant at h
  unfold embed StockClasses.totalV
  simp
  omega

/-- **§14 #55 (embed preserves reconciliation)**: if the snapshot's
    senior invariant holds, the embedded stock classes reconcile to
    the snapshot's vault — `StockClasses.reconciled` is satisfied. -/
theorem embed_reconciled (s : VaultSnapshot) (h : s.seniorInvariant) :
    s.embed.reconciled s.vault := by
  unfold StockClasses.reconciled
  exact (embed_totalV_eq_vault s h).symm

/-- **§14 #55 (consumeBacking lifts to embedded form)**: a
    backing-consumption transition preserves the embedded
    StockClasses's reconciliation. Combining
    `consumeBacking_preserves_seniorInvariant` (the 3-class proof)
    with `embed_reconciled` gives the 10-class statement. -/
theorem consumeBacking_embed_preserves_reconciled
    (s s' : VaultSnapshot) (amount : Nat)
    (hpre : s.seniorInvariant) (h : s.consumeBacking amount = some s') :
    s'.embed.reconciled s'.vault :=
  embed_reconciled s' (consumeBacking_preserves_seniorInvariant s s' amount hpre h)

/-- **§14 #55 (consumeBacking preserves vault in 10-class form)**:
    the embedded vault total is unchanged across the transition. -/
theorem consumeBacking_embed_preserves_totalV
    (s s' : VaultSnapshot) (amount : Nat)
    (hpre : s.seniorInvariant) (h : s.consumeBacking amount = some s') :
    s'.embed.totalV = s.embed.totalV := by
  have hvpre := embed_totalV_eq_vault s hpre
  have hvpost := embed_totalV_eq_vault s'
    (consumeBacking_preserves_seniorInvariant s s' amount hpre h)
  have hvault := consumeBacking_preserves_vault s s' amount h
  omega

end VaultSnapshot

end Percolator.Spec
