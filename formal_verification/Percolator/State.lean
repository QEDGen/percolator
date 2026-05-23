/-
  Percolator.State — Core state structures with type-level invariants.

  Phase 2 deliverable per `VERIFICATION_PLAN.md:107`. Models the Rust
  state structures from `src/v16.rs` as Lean records / dependent types
  to make several §14 invariants *structural* (true by typing) rather
  than runtime-checked.

  Structural §14 closures here:
    - #57 (no_global_B_index): the only fields named `bLongNum` /
      `bShortNum` live inside `AssetState`. There is no `MarketGroup`-
      or `PortfolioAccount`-level B-index field, so the invariant is
      a structural absence.
    - #87 (canonical_single_leg_per_asset): `PortfolioAccount.legs` is
      a finite map keyed by `AssetSlot` index. By construction at most
      one leg lives at each slot.
    - Parts of #2 (token value flow conservation): see
      `Percolator/ValueFlow.lean`.
    - Parts of #23 (lien dual classification): see `Percolator/Lien.lean`.

  Scope: this file models the *shape* of the state machine, not every
  field. Operational fields (oracle prices, funding, fee credits, etc.)
  are present where needed for §14 reasoning; redundant fields the Rust
  code stores for caching are not modeled.
-/

import Percolator.Defs
import Percolator.Lifecycle
import Percolator.Lien

namespace Percolator.Spec

-- ============================================================================
-- Per-side fields — small helper for "long / short" mapped quantities
-- ============================================================================

/-- A pair of values, one per `Side`. Generalizes the `*_long` / `*_short`
    field-pair pattern used throughout `v16.rs::AssetStateV16`. Indexing
    by `Side` rather than parallel fields makes "the long and short
    sides are symmetric" structural — there is no way to forget the
    short side when writing a per-side function. -/
structure PerSide (α : Type) where
  long  : α
  short : α
  deriving Repr

namespace PerSide

/-- Look up a side. Total — a future addition to `Side` would force
    every consumer to handle the new constructor (typechecking event). -/
def get {α : Type} (p : PerSide α) : Side → α
  | .Long  => p.long
  | .Short => p.short

/-- Apply a function to both sides. -/
def map {α β : Type} (f : α → β) (p : PerSide α) : PerSide β where
  long  := f p.long
  short := f p.short

/-- All-zero PerSide for any type with a zero. -/
def replicate {α : Type} (v : α) : PerSide α where
  long  := v
  short := v

end PerSide

-- ============================================================================
-- AssetState — per-asset slot in a market group
-- ============================================================================

/-- Lean mirror of the relevant fields of `v16.rs::AssetStateV16`.

    Per-asset state for a single market slot. The B-index fields
    (`bNum`, `bEpochStartNum`) live here and *only* here — closing
    §14 #57 ("no global B index") structurally.

    Numeric fields are modeled as Nat / Int with explicit precision via
    the constants in `Percolator/Defs.lean` (POS_SCALE etc.). -/
structure AssetState where
  /-- Externally-visible market id; mirrors `market_id`. -/
  marketId : Nat
  /-- Current lifecycle phase (Disabled/PendingActivation/Active/...). -/
  lifecycle : AssetLifecycle
  /-- The slot at which a retired asset was retired (0 if not retired). -/
  retiredSlot : Nat
  /-- Per-side total face exposure (POS_SCALE units). -/
  a : PerSide Nat
  /-- Per-side cumulative price-index (i128 in Rust, modeled as Int). -/
  k : PerSide Int
  /-- Per-side cumulative funding-index numerator. -/
  fNum : PerSide Int
  /-- Per-side current B-index numerator (BOUND_SCALE units). The fact
      that this field exists *only* inside `AssetState` is what closes
      §14 #57: no enclosing type has a B-index field. -/
  bNum : PerSide Nat
  /-- Per-side B-index numerator at epoch start. -/
  bEpochStartNum : PerSide Nat
  /-- Per-side open interest in quote-quantity units. -/
  oiEffQ : PerSide Nat
  /-- Per-side epoch counter. -/
  epoch : PerSide Nat
  /-- Per-side current SideMode (Normal/DrainOnly/ResetPending). -/
  mode : PerSide SideMode
  deriving Repr

namespace AssetState

/-- An asset state empties out at given market id, with all per-side
    quantities zero and lifecycle `Disabled`. -/
def empty (marketId : Nat) : AssetState where
  marketId       := marketId
  lifecycle      := .Disabled
  retiredSlot    := 0
  a              := PerSide.replicate 0
  k              := PerSide.replicate 0
  fNum           := PerSide.replicate 0
  bNum           := PerSide.replicate 0
  bEpochStartNum := PerSide.replicate 0
  oiEffQ         := PerSide.replicate 0
  epoch          := PerSide.replicate 0
  mode           := PerSide.replicate .Normal

end AssetState

-- ============================================================================
-- PortfolioLeg — single leg in a portfolio account
-- ============================================================================

/-- Lean mirror of `v16.rs::PortfolioLegV16`.

    A single leg of a portfolio account: a long or short position on a
    single asset, with cached snapshot fields for funding/B accrual.

    The `assetSlot` field identifies *which* asset this leg references.
    Combined with `PortfolioAccount.legs` being a finite map keyed by
    `AssetSlot`, §14 #87 ("one canonical leg per asset") is structural:
    there can be at most one entry per slot in the map. -/
structure PortfolioLeg where
  /-- The asset slot this leg references in the enclosing market group. -/
  assetSlot : Nat
  /-- Cached market id at the time of leg creation. -/
  marketId : Nat
  /-- Long or short. -/
  side : Side
  /-- Position size in quote-quantity (i128 in Rust). -/
  basisPosQ : Int
  /-- Position basis (POS_SCALE units). -/
  aBasis : Nat
  /-- Snapshot of asset k at last accrual. -/
  kSnap : Int
  /-- Snapshot of asset f. -/
  fSnap : Int
  /-- Snapshot of asset epoch. -/
  epochSnap : Nat
  /-- Loss-weight share. -/
  lossWeight : Nat
  /-- Snapshot of asset B numerator. -/
  bSnap : Nat
  /-- Remaining B share. -/
  bRem : Nat
  /-- Snapshot of asset b_epoch. -/
  bEpochSnap : Nat
  /-- Flag: B-side is stale. -/
  bStale : Bool
  /-- Flag: leg state is stale. -/
  stale : Bool
  deriving Repr

namespace PortfolioLeg

/-- Empty leg at a given slot. The slot is supplied so that even the
    "empty" leg has correct provenance — there is no leg with an
    unspecified slot. -/
def empty (assetSlot : Nat) : PortfolioLeg where
  assetSlot  := assetSlot
  marketId   := 0
  side       := .Long
  basisPosQ  := 0
  aBasis     := ADL_ONE
  kSnap      := 0
  fSnap      := 0
  epochSnap  := 0
  lossWeight := 0
  bSnap      := 0
  bRem       := 0
  bEpochSnap := 0
  bStale     := false
  stale      := false

end PortfolioLeg

-- ============================================================================
-- PortfolioAccount — single user's state
-- ============================================================================

/-- A per-account source-credit state, indexed elsewhere by domain. -/
structure SourceCreditState where
  positiveClaimBoundNum     : Nat
  exactPositiveClaimNum     : Nat
  freshReservedBackingNum   : Nat
  spentBackingNum           : Nat
  /-- Per-source per-validity liened amounts. Mirror of the four
      parallel fields `valid_liened_backing_num` /
      `valid_liened_insurance_num` /
      `impaired_liened_backing_num` /
      `impaired_liened_insurance_num` in `SourceCreditStateV16`.
      The `LienedAmountsBySource` shape enforces §14 #23 — see
      `Percolator/Lien.lean`. -/
  lienedAmounts             : LienedAmountsBySource
  insuranceCreditReservedNum : Nat
  creditRateNum             : Nat
  creditEpoch               : Nat

namespace SourceCreditState

/-- Empty source-credit state (matches `SourceCreditStateV16::EMPTY`). -/
def empty : SourceCreditState where
  positiveClaimBoundNum      := 0
  exactPositiveClaimNum      := 0
  freshReservedBackingNum    := 0
  spentBackingNum            := 0
  lienedAmounts              := LienedAmountsBySource.empty
  insuranceCreditReservedNum := 0
  creditRateNum              := CREDIT_RATE_SCALE
  creditEpoch                := 0

end SourceCreditState

/-- Lean mirror of `v16.rs::PortfolioAccountV16`.

    A user's portfolio account: capital, PnL, per-domain source-credit
    state, and a *finite map* of asset-slot → leg.

    **§14 #87 (canonical_single_leg_per_asset)** closure: `legs` is
    `Nat → Option PortfolioLeg` — at most one leg per slot by typing.
    The slot index is the function argument; the function returns the
    leg if one exists. -/
structure PortfolioAccount where
  /-- Capital deposited by the account holder. -/
  capital : Nat
  /-- Realized PnL (signed). -/
  pnl : Int
  /-- Reserved PnL pending settlement. -/
  reservedPnl : Nat
  /-- Per-domain source-credit state. Indexed by domain (Nat). The Rust
      array is `[SourceCreditStateV16; V16_DOMAIN_COUNT]`; the Lean
      model uses a total function over Nat with default `empty`. -/
  sourceCredit : Nat → SourceCreditState
  /-- The legs map. By construction at most one leg per asset slot —
      this is the §14 #87 structural closure. `none` means "no leg in
      this slot"; `some leg` means there's exactly one leg there. -/
  legs : Nat → Option PortfolioLeg
  /-- Fee credits (signed; negative = owed fees). -/
  feeCredits : Int
  /-- Cancel-deposit escrow. -/
  cancelDepositEscrow : Nat
  /-- Recovery / lock flags. -/
  staleState : Bool
  bStaleState : Bool
  rebalanceLock : Bool
  liquidationLock : Bool

namespace PortfolioAccount

/-- Empty account — no capital, no legs anywhere, default per-domain
    source-credit state. -/
def empty : PortfolioAccount where
  capital             := 0
  pnl                 := 0
  reservedPnl         := 0
  sourceCredit        := fun _ => SourceCreditState.empty
  legs                := fun _ => none
  feeCredits          := 0
  cancelDepositEscrow := 0
  staleState          := false
  bStaleState         := false
  rebalanceLock       := false
  liquidationLock     := false

/-- **Legs are uniquely keyed**: there is no expressible "two legs at
    the same slot" since `legs` is a function. The §14 #87 closure is
    the type itself. This theorem just witnesses the trivial fact. -/
theorem leg_unique_per_slot (a : PortfolioAccount) (slot : Nat) :
    ∀ l1 l2 : PortfolioLeg,
      a.legs slot = some l1 → a.legs slot = some l2 → l1 = l2 := by
  intro l1 l2 h1 h2
  have := h1.symm.trans h2
  exact Option.some.inj this

end PortfolioAccount

-- ============================================================================
-- MarketGroup — top-level market state
-- ============================================================================

/-- Lean mirror of `v16.rs::MarketGroupV16`'s shape (the load-bearing
    fields).

    Contains the vault, insurance pool, and a finite map of asset slots
    to `AssetState`. Notably: there is no `bLong` / `bShort` /
    `bIndex` field at this level — all B-index data is per-asset inside
    `AssetState`. This is the structural closure of §14 #57. -/
structure MarketGroup where
  /-- Vault holding aggregate quote-token capital. -/
  vault : Nat
  /-- Insurance pool. -/
  insurance : Nat
  /-- Total senior capital (sum across accounts; cached). -/
  cTot : Nat
  /-- Per-asset-slot state. Like `PortfolioAccount.legs`, this is a
      total function; "no asset at this slot" is `AssetState.empty
      marketId` with lifecycle `.Disabled`. -/
  assets : Nat → AssetState
  /-- Market-group-wide operating mode (Live/Resolved/Recovery). -/
  mode : MarketMode

namespace MarketGroup

/-- Empty market group. -/
def empty : MarketGroup where
  vault     := 0
  insurance := 0
  cTot      := 0
  assets    := fun slot => AssetState.empty slot
  mode      := .Live

/-- **§14 #57 (no_global_B_index) — structural**: the only way to read
    a B-index value is through an `AssetState.bNum`. The market group
    itself has no `bNum` field. This is witnessed not by a theorem but
    by the absence of a field; the lemma below just documents that the
    only B-index accessor goes through `assets`. -/
def bNum (g : MarketGroup) (slot : Nat) (side : Side) : Nat :=
  ((g.assets slot).bNum).get side

end MarketGroup

end Percolator.Spec
