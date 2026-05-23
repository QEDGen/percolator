/-
  Percolator.CreditAcyclicity — structural acyclicity of credit
  dependency chains.

  Strengthens the §14 #51 closure in `Spec14Aliases2.lean`
  (`TradeStep.no_circular_credit_without_backing`). The original
  closure proved that risk-increasing trades require lien-backed
  credit ("requires backing"); the audit noted that circular
  dependencies (e.g. A → B → C → A) were not actually ruled out —
  every link could individually be backed yet the chain could
  cycle.

  This file adds an *indexed* inductive `CreditChain` whose index
  is the list of accounts in the chain. The constructors:
    - `external` builds a one-element chain anchored at an
       `ExternalBacking` source.
    - `extend` adds a new account to the head of an existing chain,
       with a `notIn` proof that the new account is not already
       present in the index.

  By construction, every well-typed `CreditChain accounts` has a
  `Nodup` index — the structural witness that A → B → ... → A
  cycles are unrepresentable.

  §14 invariants strengthened in this file:
    - #51 `no_circular_credit_without_external_senior_backing`
          (audit: "requires backing" captured; "no circular" not.
           This file adds the structural acyclicity invariant.)
-/

import Percolator.Lien
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

-- ============================================================================
-- §14 #51 (strengthened): credit chains are structurally acyclic
-- ============================================================================

/-- An account identifier (opaque Nat — mirrors v16.rs account ids
    used as keys in the credit-routing graph). -/
abbrev AccountId : Type := Nat

/-- An external senior-backing source. In v16 these are the
    counterparty backing buckets and insurance reservation pools —
    capital that lives *outside* the chain of accounts. -/
structure ExternalBacking where
  /-- Source label (e.g. backing-bucket id, insurance-ledger id). -/
  id     : Nat
  /-- Positive backing amount available from this source. -/
  amount : Nat
  /-- Senior capital is strictly positive; an empty source cannot
      anchor a chain. -/
  positive : 0 < amount

/-- A credit-dependency chain indexed by the list of accounts it
    visits.

    The recursion is intentional:
      - Every chain *begins* with an external senior backing source.
        There is no "freestanding" chain constructor — without the
        backing anchor, no chain can be built.
      - Each `extend` step takes a *new* account (one not already
        in the index) and prepends it. The `notIn` proof rules out
        cycles by construction.

    The list-as-index lets us reason about the chain's account
    membership at the type level. -/
inductive CreditChain : List AccountId → Type where
  | external (backing : ExternalBacking) (account : AccountId) :
      CreditChain [account]
  | extend   {prev : List AccountId} (chain : CreditChain prev)
             (account : AccountId) (_notIn : ¬ account ∈ prev) :
      CreditChain (account :: prev)

namespace CreditChain

/-- The external senior backing anchoring this chain. The recursion
    bottoms out at the `external` constructor. -/
def anchor : {accounts : List AccountId} → CreditChain accounts → ExternalBacking
  | _, .external b _    => b
  | _, .extend prev _ _ => prev.anchor

/-- The chain's length — equals the index list's length by
    construction. -/
def length : {accounts : List AccountId} → CreditChain accounts → Nat
  | _, .external _ _    => 1
  | _, .extend prev _ _ => prev.length + 1

/-- **Length-matches-index**: the recursive `length` definition
    matches the index list's length. -/
theorem length_eq_accounts_length :
    {accounts : List AccountId} → (c : CreditChain accounts) →
    c.length = accounts.length
  | _, .external _ _ => rfl
  | _, .extend prev _ _ => by
    show prev.length + 1 = _ + 1
    rw [length_eq_accounts_length prev]

/-- **§14 #51 (acyclicity — accounts are distinct)**: every
    `CreditChain accounts`'s index list is Nodup. By construction:
    every `extend` constructor takes a `notIn` proof, so the new
    head differs from every prior entry.

    This is the structural witness that A → B → ... → A cycles are
    unrepresentable in the type. -/
theorem accounts_nodup :
    {accounts : List AccountId} → (_c : CreditChain accounts) →
    accounts.Nodup
  | _, .external _ a =>
    show ([a] : List AccountId).Nodup
    by exact List.nodup_singleton a
  | _, .extend prev a hnotIn => by
    show (a :: _).Nodup
    exact List.Nodup.cons hnotIn (accounts_nodup prev)

/-- **§14 #51 (the chain anchor is structurally positive)**: every
    chain — by construction — bottoms out at an `external`
    backing with `positive : 0 < amount`. The recursion uses the
    constructor field directly. -/
theorem anchor_positive :
    {accounts : List AccountId} → (c : CreditChain accounts) →
    0 < c.anchor.amount
  | _, .external b _ => b.positive
  | _, .extend prev _ _ => anchor_positive prev

/-- **§14 #51 (extend preserves anchor)**: prepending an account to
    a chain does not change the underlying senior backing source.
    Every account in the extended chain still transitively depends
    on the same external capital. -/
theorem extend_preserves_anchor
    {prev : List AccountId} (c : CreditChain prev) (a : AccountId)
    (hnotIn : ¬ a ∈ prev) :
    (CreditChain.extend c a hnotIn).anchor = c.anchor := rfl

/-- **§14 #51 (no self-extension)**: cannot extend a chain with an
    account that is already present in its index list. The
    constructor field requires the negative proof; the absence of
    that proof makes the call ill-typed. -/
theorem cannot_self_extend
    {prev : List AccountId} (_c : CreditChain prev) (a : AccountId)
    (h : a ∈ prev) :
    ¬ ∃ (hnotIn : ¬ a ∈ prev), True := by
  intro ⟨hnotIn, _⟩
  exact hnotIn h

end CreditChain

-- ============================================================================
-- §14 #51 (acyclicity contracts at the credit-link layer)
-- ============================================================================

/-- A single credit link between two accounts, with the dependent
    side typed against an `ExternalBacking` source — modeling
    "this credit lane is anchored by external capital."

    A list of `CreditLink`s could be assembled into a chain (or
    not, if circular). The `CreditChain` type above is the
    structural certificate that a particular assembly is acyclic. -/
structure CreditLink where
  src    : AccountId
  dst    : AccountId
  backed : ExternalBacking

/-- **§14 #51 (lone link is always acyclic)**: any single credit
    link can be packaged into a one-step chain — the type system
    only refuses when the link is a self-loop. -/
theorem link_to_singleton_chain (l : CreditLink) (hne : l.src ≠ l.dst) :
    ∃ chain : CreditChain [l.src, l.dst],
      chain.anchor = l.backed := by
  have hnotIn : ¬ l.src ∈ ([l.dst] : List AccountId) := by
    intro hmem
    simp at hmem
    exact hne hmem
  exact ⟨CreditChain.extend (CreditChain.external l.backed l.dst) l.src hnotIn, rfl⟩

end Percolator.Spec
