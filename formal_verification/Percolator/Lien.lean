/-
  Percolator.Lien — Liens parameterized by their backing source.

  This file is the Phase 2 win for §14 #23 ("lien_never_both_support_and_insurance"):
  a `Lien` is a *type* indexed by `BackingSource`, so a counterparty-backed
  lien and an insurance-backed lien are different types. No expression
  can accidentally classify a lien as both — the type system refuses to
  unify them.

  This converts a runtime invariant (which Kani harnesses currently
  defend by case analysis) into a structural type-level fact: any code
  that wants to operate on "all liens regardless of source" must either
  destructure both flavours or sum over the `BackingSource` index, which
  makes the dual classification visible.

  The Rust counterpart lives in `src/v16.rs`:
    - `SourceCreditBackingSourceV16` (line 190) — the runtime enum.
    - `SourceCreditStateV16` (line 837) — has parallel
      `valid_liened_backing_num` / `valid_liened_insurance_num` pairs.
    - `SourceCreditLienAggregateProofV16` (line 1647) — has parallel
      `counterparty_face_claim_locked_num` / `insurance_face_claim_locked_num`.

  In the Lean model these pairs become a single function indexed by
  `BackingSource`, so adding a new source variant in the future will
  trigger a totality error at every consumer rather than silently zero
  out an unhandled case.
-/

import Percolator.Defs
import Percolator.Lifecycle

namespace Percolator.Spec

-- ============================================================================
-- Lien — indexed by backing source
-- ============================================================================

/-- A single lien against the named backing pool.

    The `src : BackingSource` parameter is part of the type. `Lien
    .Counterparty` and `Lien .Insurance` are distinct types — there is
    no function that takes a generic `Lien` without first specifying or
    abstracting over the source. This makes §14 #23 unrepresentable
    rather than merely false at runtime.

    Fields mirror the per-source amounts that `SourceCreditLienAggregateProofV16`
    splits into parallel pairs. -/
structure Lien (src : BackingSource) where
  /-- Locked face-claim quantity (units of POS_SCALE-scaled claim). -/
  faceClaimLockedNum : Nat
  /-- Reserved backing (units of BOUND_SCALE-scaled backing). -/
  backingReservedNum : Nat
  /-- Effective credit reserved against this lien. -/
  effectiveCreditReserved : Nat
  /-- Face claim that has been impaired (loss-bearing). -/
  impairedFaceClaimNum : Nat
  /-- Effective credit reserved against the impaired portion. -/
  impairedEffectiveCreditReserved : Nat
  deriving Repr

namespace Lien

/-- Empty lien (no claim, no backing). The constructor inherits the
    `src` type parameter — so `Lien.empty (src := .Counterparty)` is
    not interchangeable with `Lien.empty (src := .Insurance)`. -/
def empty (src : BackingSource) : Lien src where
  faceClaimLockedNum := 0
  backingReservedNum := 0
  effectiveCreditReserved := 0
  impairedFaceClaimNum := 0
  impairedEffectiveCreditReserved := 0

end Lien

-- ============================================================================
-- SourceCreditLienAggregate — per-domain aggregate split by source
-- ============================================================================

/-- Per-domain aggregate of liens, with the two sources held in
    separately-typed fields.

    Mirrors `v16.rs::SourceCreditLienAggregateProofV16` but with the
    counterparty/insurance split living at the type level. In Rust the
    invariant `counterparty_face_claim_locked_num + insurance_face_claim_locked_num
    = face_claim_locked_num` is checked at runtime in
    `SourceCreditLienAggregateProofV16::validate`; in Lean the totals
    are derived from the per-source fields by construction, so the
    invariant is structural. -/
structure SourceCreditLienAggregate where
  /-- Source domain index (mirrors `v16.rs::SourceCreditBackingSourceV16`'s
      enclosing context — the domain is whichever credit lane this
      aggregate covers). -/
  domain : Nat
  /-- Per-domain bound on aggregate face-claim that can be locked. -/
  sourceClaimBoundNum : Nat
  /-- The counterparty-backed lien — typed `Lien .Counterparty`. -/
  counterparty : Lien BackingSource.Counterparty
  /-- The insurance-backed lien — typed `Lien .Insurance`. Distinct type
      from `counterparty`, so no operation can confuse them. -/
  insurance : Lien BackingSource.Insurance
  deriving Repr

namespace SourceCreditLienAggregate

/-- Total locked face claim — derived, not stored. The Rust struct
    stores `face_claim_locked_num` and *validates* it equals the sum
    of the per-source amounts at runtime; the Lean model derives it,
    making the conservation automatic. -/
def faceClaimLockedNum (a : SourceCreditLienAggregate) : Nat :=
  a.counterparty.faceClaimLockedNum + a.insurance.faceClaimLockedNum

/-- Total impaired face claim — derived. -/
def impairedFaceClaimNum (a : SourceCreditLienAggregate) : Nat :=
  a.counterparty.impairedFaceClaimNum + a.insurance.impairedFaceClaimNum

/-- Total effective credit reserved (across both sources). -/
def effectiveCreditReserved (a : SourceCreditLienAggregate) : Nat :=
  a.counterparty.effectiveCreditReserved + a.insurance.effectiveCreditReserved

/-- Total backing reserved (across both sources, in BOUND_SCALE units). -/
def backingReservedNum (a : SourceCreditLienAggregate) : Nat :=
  a.counterparty.backingReservedNum + a.insurance.backingReservedNum

/-- Look up a single per-source lien by `BackingSource`. Total function:
    extending `BackingSource` with a new variant in the future will
    trigger a non-exhaustive-match error here, surfacing every
    downstream consumer that needs to handle the new source. -/
def lienBySource (a : SourceCreditLienAggregate) : (src : BackingSource) → Lien src
  | .Counterparty => a.counterparty
  | .Insurance    => a.insurance

/-- **Structural decomposition**: every lien in the aggregate is
    classified by exactly one `BackingSource`. The type guarantees this;
    the function below witnesses that the two named fields exhaust the
    classification. -/
theorem lien_either (a : SourceCreditLienAggregate) (src : BackingSource) :
    a.lienBySource src
    = (match src with
       | .Counterparty => a.counterparty
       | .Insurance    => a.insurance) := by
  cases src <;> rfl

/-- The empty aggregate at a given domain — all per-source liens zero. -/
def emptyAt (domain : Nat) : SourceCreditLienAggregate where
  domain := domain
  sourceClaimBoundNum := 0
  counterparty := Lien.empty .Counterparty
  insurance := Lien.empty .Insurance

end SourceCreditLienAggregate

-- ============================================================================
-- Per-source per-validity liened amounts (mirrors SourceCreditStateV16
-- fields valid_liened_backing/insurance_num × impaired_liened_*)
-- ============================================================================

/-- A 2×2 lien classification: `(BackingSource × Validity) → Nat`.

    Mirrors the four parallel fields in `v16.rs::SourceCreditStateV16`:
      - `valid_liened_backing_num`     ↔  validity=Valid,    src=Counterparty
      - `valid_liened_insurance_num`   ↔  validity=Valid,    src=Insurance
      - `impaired_liened_backing_num`  ↔  validity=Impaired, src=Counterparty
      - `impaired_liened_insurance_num`↔  validity=Impaired, src=Insurance

    By expressing these as functions over `BackingSource` and a 2-valued
    validity tag, the §14 #23 constraint that no lien straddles both
    sources is structural: every cell is classified by exactly one
    `(src, validity)` pair. -/
inductive Validity : Type where
  | Valid    : Validity
  | Impaired : Validity
  deriving DecidableEq, Repr

structure LienedAmountsBySource where
  amount : BackingSource → Validity → Nat

namespace LienedAmountsBySource

/-- Total liened across all (source, validity) combinations. -/
def total (l : LienedAmountsBySource) : Nat :=
  l.amount .Counterparty .Valid + l.amount .Counterparty .Impaired
  + l.amount .Insurance .Valid + l.amount .Insurance .Impaired

/-- Counterparty total. -/
def counterpartyTotal (l : LienedAmountsBySource) : Nat :=
  l.amount .Counterparty .Valid + l.amount .Counterparty .Impaired

/-- Insurance total. -/
def insuranceTotal (l : LienedAmountsBySource) : Nat :=
  l.amount .Insurance .Valid + l.amount .Insurance .Impaired

/-- **Structural conservation**: total equals counterparty + insurance.
    This is what §14 #23 asserts at runtime via parallel fields; here it's
    a `by rfl` consequence of the definitions. -/
theorem total_eq_counterparty_plus_insurance (l : LienedAmountsBySource) :
    l.total = l.counterpartyTotal + l.insuranceTotal := by
  unfold total counterpartyTotal insuranceTotal; omega

/-- The empty lien-amount table. -/
def empty : LienedAmountsBySource where
  amount := fun _ _ => 0

end LienedAmountsBySource

end Percolator.Spec
