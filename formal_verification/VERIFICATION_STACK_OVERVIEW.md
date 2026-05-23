# Verification stack — top-level overview

This document explains the percolator-v16 verification approach
end-to-end. It is the orientation document for anyone trying to
understand what's been built, why, and where to look.

## The shape of the stack

The verification stack has four tiers. Each tier verifies a
different layer of the system against a different abstraction.

```
                    spec.md §14 (99 invariants)
                          │
                          ▼ formal expression
                ┌─────────────────────┐
        Lean    │   Phase 1–5 specs   │   ←  Tier 1: arithmetic + state-machine
                │   + post-audit      │      99/99 §14 invariants Lean-closed
                │   strengthenings    │
                └─────────────────────┘
                          │
                          ▼ executable port
                ┌─────────────────────┐
        Rust    │  Reference ports    │   ←  Tier 2: spec is executable
                │  in tests/          │      102 proptests verify Lean theorems
                │  proofs_v16_lean_   │      at runtime
                │  refinement_*.rs    │
                └─────────────────────┘
                          │
                          ▼ abstraction function
                ┌─────────────────────┐
        Rust    │ Production connector │  ←  Tier 2.5: refinement to v16.rs
                │  (same file, lower   │      28 proptests verify production
                │  half + stress file) │      transitions match reference
                └─────────────────────┘
                          │
                          ▼ executes
                ┌─────────────────────┐
                │     v16.rs          │   ←  the actual production engine
                │  (MarketGroupV16)   │      ~10,000 lines of Rust
                └─────────────────────┘

  Plus the existing Kani BMC harnesses (proofs_v16.rs, 50 proofs)
  that verify bounded properties of v16.rs symbolically.
```

## The four tiers

### Tier 1 — Arithmetic kernel

**Location**: `formal_verification/Percolator/{U256,I256,WideMath,
BoundArith,CreditRate}.lean` (Phase 1) plus
`tests/proofs_v16_lean_refinement.rs`.

**What it proves**: `src/wide_math.rs`'s widening multiplication,
mul/div, two's-complement signed arithmetic, and fixed-point
scaling identities are correct over the full u128/u256/i128
domain.

**How**: Lean theorems prove the math via Mathlib's `omega`,
`linarith`, and `ring`. A `num-bigint` reference impl in Rust is
the spec made executable; 10 proptests diff the production
operations against the reference at randomly-sampled u128/u256
inputs.

**Status**: complete. The arithmetic layer is fully bridged.

### Tier 2 — State-machine spec layer

**Location**: `formal_verification/Percolator/*.lean` (Phase 2–5
modules plus session strengthenings) and
`tests/proofs_v16_lean_refinement_{insurance,backing_bucket,
lien_lifecycle,activation,stock_reconciliation,b_booking,
value_flow,close_ledger}.rs`.

**What it proves**: every Phase 5 cluster — lien lifecycle,
backing bucket, activation envelope, close ledger, close
priority, B-booking arithmetic, value-flow soundness, stock
reconciliation, insurance ledger — has both a Lean spec (state
+ transitions + theorems) and a Rust reference port that mirrors
it line-by-line. The reference port is the spec made executable.

102 proptests verify the Lean theorems hold at runtime: every
named theorem on the spec side has a matching proptest on the
reference-port side. The reference ports are owned by the
verification (not used by production).

**Status**: complete. All 8 clusters have ports + proptests.

### Tier 2.5 — Production connector

**Location**: bottom halves of the Tier 2 test files, plus
`tests/proofs_v16_lean_refinement_stress.rs`.

**What it proves**: the production engine (`v16.rs::MarketGroupV16`
and its handlers) refines the Lean spec. For each cluster, an
*abstraction function* projects production state to the reference
port; proptests then exercise real production handlers and
verify the projected post-state matches the reference port's
post-state.

The connector landed in three rounds:

1. **Single-step refinement** (28 proptests across 8 clusters):
   one production call ↔ one reference call, post-states agree
   under abstraction.
2. **Multi-step lockstep** (16 proptests across 6 clusters):
   sequences of 1–20 production calls; the abstraction tracks
   the reference port after every step. Catches sequencing bugs
   that single-step tests miss.
3. **Stress** (8 harnesses): 50-step sequences with biased
   generators (boundary values weighted heavily) and 1000–2000
   cases per harness. ~500,000+ production-call operations.
   Plus hand-crafted adversarial sequences.

**Status**: all 8 clusters have multi-step coverage. The final
two (BBookingExact and CloseLedger) used alternative paths
that sidestep the bankrupt-close fixture: BBookingExact uses
a 3-line `production_inline_step` helper to chain the inline
arithmetic; CloseLedger mutates `CloseProgressLedgerV16`'s pub
fields directly and verifies method-level lockstep.

### Tier 3 — Kani symbolic verification

**Location**: `tests/proofs_v16.rs` (existing, ~50 proofs).

**What it proves**: bounded properties of v16.rs at small input
ranges (typically ≤ 40 atoms). Verifies the engine's behavior
symbolically — exhaustive over the bounded input space, not
random.

The Tier 1–2.5 bridges are random-input refinement; Tier 3 is
exhaustive at small bounds. The two are complementary.

**Status**: pre-existing. Not modified by this verification
session.

## What the bridge has caught

The verification stack has surfaced exactly one real refinement-
direction discrepancy across all the work:

**InsuranceLedger unit-conversion bug** (Week 1 of the
production connector). The initial abstraction kept the
production's `insurance_credit_reserved_num` in BOUND-units
when the reference port's constraint was in atoms. A budget
of 100 atoms allowed a reserve of 101 BOUND-units (= ~1 atom
after `amount_from_bound_num` ceil-divide) — production
accepted, reference rejected. Fixed by aligning units to atoms
throughout the abstraction (commit `37a2152`).

After Week 1's audit-strengthening, Week 2's lockstep deepening,
and Week 3's adversarial stress, no further discrepancies have
surfaced. This is a meaningful negative result: the production
engine refines the Lean spec at the modeled subset.

## How §14 coverage was achieved

The 99 §14 invariants from `spec.md` were closed across two
sessions:

- **Original Phase 5** (May 2026): 84 invariants via the Phase
  1–5 modules.
- **This 2026-05-22 session**: 15 more across 11 dedicated
  modules covering invariants that were previously
  "Kani-only" or "no Lean coverage" rows.

A self-audit on 2026-05-23 classified all 15 new closures as
SOLID after strengthening (the 6 initial partials were each
upgraded with production-aligned witnesses).

Across both audits (the original 2026-05-22 + the 2026-05-23
audit), 50 closures were classified; after strengthenings,
**50/50 are SOLID, 0 PARTIAL, 0 OVERCLAIM**.

## File map

```
formal_verification/
├── HANDOFF.md                    — session-by-session resumption notes
├── SPEC_COVERAGE.md              — per-§14-invariant coverage matrix
├── VERIFICATION_PLAN.md          — original multi-month plan (Phases 1–6)
├── REASSESSMENT_PHASE4.md        — Phase 4 decision point
├── AUDIT_2026-05-22.md           — first audit (35 closures)
├── AUDIT_2026-05-23.md           — this session's audit (15 closures)
├── VERIFICATION_STACK_OVERVIEW.md — this document
└── Percolator/
    ├── (Phase 1–5 modules, see SPEC_COVERAGE.md for the matrix)
    └── (2026-05-23 modules: ReservationEncumbrance, NoDoubleSpend,
         FavorableActions, ConservativeWithdrawal, ReceiptUnderbound,
         BBookingResponse, ResidualCureOnce, OraclePumpLimit,
         BoundedExpiryScan, AggregateDriftCredit, NoFullMarketScan,
         ClaimBoundBucketRange, CrossAssetIsolation, VerifiedMaker,
         ResolvedPayoutRate)

tests/
├── proofs_v16.rs                 — Kani BMC proofs (Tier 3)
├── proofs_v16_arithmetic.rs      — small-reference Kani harnesses
├── proofs_v16_lean_refinement.rs — Tier 1 arithmetic bridge
└── proofs_v16_lean_refinement_{cluster}.rs — Tier 2 + 2.5 per cluster
    plus tests/proofs_v16_lean_refinement_stress.rs (Week 3 stress)
```

## How to verify locally

```bash
# Tier 1–2 (Lean side): build all spec proofs
cd formal_verification
lake build

# Tier 2.5 (production connectors + stress)
cd ..
cargo test --tests       # all 440+ tests
cargo test --test proofs_v16_lean_refinement_stress  # stress only

# Tier 3 (Kani): per the existing proofs_v16.rs harness setup
```

Total build time: ~30 seconds for incremental `lake build`,
~10 seconds for the cargo test suite (the stress file adds ~4s).

## What this stack does NOT do

Honest scope limits:

- **It does not verify Solana-level execution.** The Lean spec
  abstracts away the Solana account model, PDA derivations, and
  account-data layouts. Production-side these are handled by
  separate harnesses (the `v16_*` Kani proofs).
- **It does not verify cross-instruction composition.** Each
  Tier 2.5 proptest exercises one instruction at a time (or a
  sequence within one transaction); the multi-step harnesses
  run inside a single test thread without simulating
  inter-instruction state churn from external callers.
- **It does not catch bugs in code paths the proptests miss.**
  Biased generators help, but coverage of the production
  state space is incomplete by construction. The Tier 3 Kani
  harnesses complement this by exhaustive checking at small
  bounds.
- **It does not verify cryptographic primitives.** Signature
  verification is modeled as an opaque predicate (#63).

## When to update

When v16.rs gains a new public handler or changes a field's
unit:

1. **Lean spec**: add or update the corresponding `Percolator/
   *.lean` module. Run `lake build` to type-check.
2. **Reference port**: update the corresponding
   `tests/proofs_v16_lean_refinement_{cluster}.rs` reference
   port to match.
3. **Production connector**: update the abstraction function and
   any single-step / multi-step proptests in the same file. The
   Week 1 unit-conversion bug surfaced precisely because the
   abstraction was wrong; this is exactly the kind of issue the
   connector catches.
4. **Stress harness**: usually no change needed, but if the
   transition is sensitive to a new boundary, add a hand-crafted
   adversarial case to `tests/proofs_v16_lean_refinement_stress.rs`.
5. **SPEC_COVERAGE.md**: if a §14 invariant's coverage shifts,
   update the per-row description.

A working pattern: change v16.rs → run `cargo test --tests` →
if a connector test fails, investigate whether it's a real
production bug or a stale reference port. The bridge is
designed to fail loudly on the difference.
