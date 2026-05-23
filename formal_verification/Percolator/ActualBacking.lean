/-
  Percolator.ActualBacking — backing reservation is actual locked
  equity sourced from an account, not an unverified certificate.

  The §14 #11 invariant requires that a non-zero `backingReservedNum`
  on a lien correspond to a *real* capital decrement on the account
  that locked it. A "certificate" failure mode would let a lien claim
  positive backing while no equity was ever moved.

  This file replaces the prior (tautological) §14 #11 closure in
  `Spec14Aliases2.lean` with a substantive model: a `lockEquity`
  transition that takes pre-capital and produces (postCapital,
  Lien) such that `postCapital + lien.backingReservedNum =
  preCapital` exactly.

  §14 invariants addressed:
    - #11 `backing_reservation_is_actual_locked_equity_not_optimistic_certificate`
-/

import Percolator.Lien
import Percolator.Lifecycle
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

/-- An account's loss-bearing capital — the pool from which backing
    is drawn. Mirrors the `C_i` per-account capital in `spec.md §5`. -/
structure AccountCapital where
  amount : Nat
  deriving Repr

namespace AccountCapital

/-- **The atomic lock-equity transition**: move `amount` units of
    capital from the account into a counterparty-backed lien. The
    one-result-tuple shape makes the move atomic — the lien cannot be
    constructed with `backingReservedNum > 0` without a matching
    capital decrement.

    Returns `none` when the account lacks sufficient capital. -/
def lockEquity (a : AccountCapital) (amount : Nat) :
    Option (AccountCapital × Lien BackingSource.Counterparty) :=
  if a.amount < amount then none
  else some (
    { amount := a.amount - amount },
    { faceClaimLockedNum := 0
      backingReservedNum := amount
      effectiveCreditReserved := 0
      impairedFaceClaimNum := 0
      impairedEffectiveCreditReserved := 0 }
  )

/-- **§14 #11 (capital conservation)**: a successful `lockEquity`
    moves exactly `amount` units from `AccountCapital` into the lien's
    `backingReservedNum`. The post-lock capital plus the lien's
    backing equals the pre-lock capital — no atoms are created or
    destroyed. -/
theorem lockEquity_conservation
    (a a' : AccountCapital) (l : Lien BackingSource.Counterparty)
    (amount : Nat) (h : a.lockEquity amount = some (a', l)) :
    a'.amount + l.backingReservedNum = a.amount := by
  unfold lockEquity at h
  by_cases hlt : a.amount < amount
  · simp [hlt] at h
  · push_neg at hlt
    simp [hlt] at h
    obtain ⟨ha', hl⟩ := h
    rw [← ha', ← hl]
    change a.amount - amount + amount = a.amount
    omega

/-- **§14 #11 (lien backing = locked amount)**: the resulting lien's
    `backingReservedNum` equals exactly the `amount` requested. There
    is no path that produces a lien with `backingReservedNum > 0` but
    a smaller capital decrement (the "optimistic certificate" case). -/
theorem lockEquity_lien_backing_eq_amount
    (a a' : AccountCapital) (l : Lien BackingSource.Counterparty)
    (amount : Nat) (h : a.lockEquity amount = some (a', l)) :
    l.backingReservedNum = amount := by
  unfold lockEquity at h
  by_cases hlt : a.amount < amount
  · simp [hlt] at h
  · push_neg at hlt
    simp [hlt] at h
    obtain ⟨_, hl⟩ := h
    rw [← hl]

/-- **§14 #11 (capital strictly decreases on positive lock)**: a
    positive-amount lock strictly reduces the account's capital.
    Combined with `lien_backing_eq_amount`, the lien's positive
    backing is provably sourced from real capital. -/
theorem lockEquity_decreases_capital
    (a a' : AccountCapital) (l : Lien BackingSource.Counterparty)
    (amount : Nat) (hpos : 0 < amount)
    (h : a.lockEquity amount = some (a', l)) :
    a'.amount < a.amount := by
  have hcons := lockEquity_conservation a a' l amount h
  have hbk := lockEquity_lien_backing_eq_amount a a' l amount h
  omega

/-- **§14 #11 (fail-closed on under-capital)**: if the account
    lacks sufficient capital, `lockEquity` returns `none` — no
    "optimistic" lien is produced. -/
theorem lockEquity_fails_when_undercapital
    (a : AccountCapital) (amount : Nat) (h : a.amount < amount) :
    a.lockEquity amount = none := by
  unfold lockEquity
  simp [h]

/-- **§14 #11 (precondition extraction)**: a successful `lockEquity`
    proves the account had at least `amount` of capital. -/
theorem lockEquity_requires_capital
    (a a' : AccountCapital) (l : Lien BackingSource.Counterparty)
    (amount : Nat) (h : a.lockEquity amount = some (a', l)) :
    amount ≤ a.amount := by
  unfold lockEquity at h
  by_cases hlt : a.amount < amount
  · simp [hlt] at h
  · push_neg at hlt
    exact hlt

/-- **§14 #11 (contrapositive: any positive-backing lien is
    capital-sourced)**: if a lien has positive `backingReservedNum`
    and was produced by `lockEquity`, the originating account's
    capital was strictly higher than the post-lock state. There is
    no path through `lockEquity` that creates positive backing
    without consuming capital. -/
theorem positive_lien_implies_capital_decrement
    (a a' : AccountCapital) (l : Lien BackingSource.Counterparty)
    (amount : Nat) (h : a.lockEquity amount = some (a', l))
    (hpos : 0 < l.backingReservedNum) :
    a'.amount < a.amount := by
  have heq := lockEquity_lien_backing_eq_amount a a' l amount h
  rw [heq] at hpos
  exact lockEquity_decreases_capital a a' l amount hpos h

end AccountCapital

end Percolator.Spec
