# Verification Plan — percolator-v16 Risk Engine

This plan covers moving percolator-v16 from "230 Kani harnesses with no traceability
to §14" to "Lean spec is the source of truth for engine semantics." The strategy is
**incremental, lowest-hanging-fruit first**: start with pure arithmetic and structural
work that pure Lean + Mathlib handles natively, then decide whether state-machine
verification (Velvet or alternative) is needed based on what's left.

Written 2026-05-20 against the state captured in `SPEC_COVERAGE.md`.

## Goals

1. **Every §14 invariant lives in the same artifact that defines the state it
   constrains.** No external prose, no implicit harness mapping, no drift surface.
2. **Compress §14 from 99 to ~60 invariants via the Lean spec itself.** Many of the
   conservation and lien-lifecycle mirror invariants become structurally true once
   the data model is in dependent types, or are subsumed when the spec designates
   one ledger as canonical. This is a *consequence* of writing the spec correctly,
   not a separate effort.
3. **Executable reference implementation and test vectors as byproducts.**

## Non-goals

- **Refactor the Rust impl.** The Rust code stays as-is. If the Lean spec reveals
  the data model wants to be different, that's a separate decision later.
- **Commit to Velvet (or any state-machine verification tool) upfront.** The plan
  starts with work that pure Lean handles, and defers the state-machine tooling
  decision until Phase 4, when we know what's actually left.
- Performance verification. Only safety / conservation / liveness.
- Verify external wrappers (consumer programs). Their responsibility.

## Current state (2026-05-20, from SPEC_COVERAGE.md)

```
Confidence × Strength matrix over 99 §14 invariants:

           STRONG  MEDIUM  WEAK  N/A
HIGH          4     30     14     0    48
MEDIUM        9     14      9     0    32
LOW           2      9      3     0    14
NONE          0      0      0     5     5
```

Lean-side:

- `Percolator/WideMath.lean` — `wideningMulU128_correct` and corollaries proved
  (~770 LoC of Lean). `Percolator/U256.lean` has `toNat_mul`, `toNat_lt`, and
  `checkedMul_both_hi_zero`. The arithmetic foundation is solid.
- 2 proptests bridge Rust `wide_math.rs` to Lean model (`proofs_v16_lean_refinement.rs`).
- Open items in `WideMath.lean` comments: `u256CheckedMul_correct` (full
  schoolbook), `divRemU256_correct`, `i256Abs/Neg/Mul_correct` (signed
  two's-complement).

## Strategy: tier the §14 invariants by what they actually need

Not every invariant needs the same machinery. Tiering them by required technique
gives a natural work order:

| Tier | Technique | Approximate §14 count | Tools |
|---|---|---|---|
| **T1 — Arithmetic** | Theorems over Nat/Int with `ring`/`linarith`/`omega` | ~10–15 | Pure Lean + Mathlib |
| **T2 — Structural** | Dependent types that make violations impossible | ~20–30 | Pure Lean (no proofs needed — type-check) |
| **T3 — Pure-function** | Theorems about stateless computations on the data model | ~15–20 | Pure Lean theorems |
| **T4 — State-machine** | Conservation across mutating operations, liveness, lifecycle | ~30–40 | Velvet / F\* / pure Lean transition relations |

T1+T2+T3 ≈ 45–65 invariants closable without state-machine tooling. **That's the
lowest-hanging fruit.** Whether to tackle T4 — and with what tooling — is a
separate decision the plan defers until Phase 4.

## Phase 1 — Finish the arithmetic layer (4–8 weeks)

**Scope:** complete the remaining arithmetic theorems in `Percolator/`, plus the
percolator-specific bound/rate arithmetic.

**Deliverables:**

- `WideMath.lean`: close the `Future` items already drafted as comments:
  - `u256CheckedMul_correct` — full schoolbook for U256 × U256 → U256 with
    explicit overflow.
  - `divRemU256_correct` — `num = quotient · den + remainder ∧ remainder < den`.
  - `i256AbsU256_correct`, `i256CheckedNeg_correct`, `i256CheckedMul_correct`.
- `Percolator/CreditRate.lean` (new): theorems for the credit-rate formula
  (`min(available_backing · CREDIT_RATE_SCALE / claim, CREDIT_RATE_SCALE)`),
  proving it's bounded above by CREDIT_RATE_SCALE, zero when backing is zero,
  monotone in available_backing.
- `Percolator/BoundArith.lean` (new): theorems for `amount_from_bound_num_up`,
  `amount_from_bound_num_down`, the `POS_SCALE` / `BOUND_SCALE` / `ADL_ONE`
  identities.
- Extend the existing `proofs_v16_lean_refinement.rs` proptest file with new
  refinement properties for each theorem proved.

**§14 items this closes or partially closes:**

- T1: #15 (amount_from_bound_num_up rounds up), #42 (credit_rate_num bounded),
  parts of #1 (source_domain credit capped by backing — the formula half),
  parts of #50 (credit_rate_recomputation bounded — the per-domain math).

**Exit criterion:** all "Future" theorems in `WideMath.lean` are proven (no
`sorry`). Credit-rate and bound-arithmetic theorems exist with no `sorry`.
SPEC_COVERAGE.md updated to reference Lean theorem identifiers for these items.

**Why this first:** the existing `wideningMulU128_correct` proof closed cleanly,
so the team already knows the toolchain works. Extending it is the lowest-risk
path to closing real §14 items. Everything in this phase is pure-function math —
no state, no Velvet, no exotic Lean machinery.

## Phase 2 — Structural invariants via dependent types (3–5 weeks)

**Scope:** define the percolator data model in Lean with dependent constraints
that make violation impossible. No proofs — just type definitions that compile
or don't.

**Deliverables:**

- `Percolator/State.lean`: `MarketGroup`, `PortfolioAccount`, `AssetState`,
  `PortfolioLeg`, plus supporting structs as Lean records/inductives.
- `Percolator/Lifecycle.lean`: the 8 lifecycle enums (`AssetLifecycle`,
  `MarketMode`, `BackingBucketStatus`, etc.) as Lean inductives, plus
  allowed-transition relations.
- `Percolator/Lien.lean`: `Lien` parameterized by `BackingSource` so dual
  classification is a type error.
- `Percolator/ValueFlow.lean`: `TokenValueFlow` indexed by balance conservation
  so an unbalanced proof doesn't typecheck.
- `Percolator/CompactLeg.lean`: enforce "one leg per asset per account" at the
  type level if practical.

**§14 items this closes structurally:**

- T2: #23 (lien_never_both_support_and_insurance — dependent type on
  BackingSource), #57 (no_global_B_index — type forces per-asset only), #87
  (canonical_single_leg_per_asset — same), parts of #2 and #25
  (ValueFlow constructors require balance), parts of #24
  (close_residual_partition disjoint by type tag), and several more depending
  on how aggressive the typing is.

Target: 15–25 invariants discharged by typing alone.

**Exit criterion:** SPEC_COVERAGE.md identifies which §14 items are now
"structural via type T at file:line" — these never need proofs.

**Risk to watch:** Lean 4 dependent-typing can get syntactically heavy when a
field has 5+ constraints. If a constraint feels forced, leave it for Phase 3 as
a theorem. Don't over-engineer.

## Phase 3 — Pure-function ports (4–8 weeks)

**Scope:** port stateless engine functions to Lean and prove their properties as
theorems. No mutable state, no transitions — just functions on the data model
defined in Phase 2.

Target functions, smallest first:

- `select_h_lock` (5 lines of branch logic): trivial property — output is
  hmin or hmax depending on a 6-flag predicate.
- `risk_score` formula: stateless computation on portfolio + prices.
- `source_credit_available_backing_num`: stateless ledger query.
- `claim_bound_bucket_formula`: bucket selection logic.
- `flat_account_equity`: capital + pnl − fee_debt.
- `h_lock_lane` selection.
- `validate_account_shape` predicate (pure assertion on account state).

**§14 items this closes:**

- T3: full #1 (source credit cap), full #50 (credit rate bounded by domain/bucket
  count), #44 (locked_face_claim_excluded), #45 (withdrawal uses conservative
  sum), #48 (claim_bound_bucket_formula doesn't understate), parts of #65, #90,
  others depending on what gets ported.

Target: 15–20 more invariants discharged.

**Exit criterion:** every §14 item that's a property of a stateless computation
has a Lean theorem.

## Phase 4 — Reassessment + state-machine decision (1 week)

**This is the key gate.** After Phases 1–3, count what's left and decide.

**Tally to make:**

- How many §14 invariants are discharged (T1+T2+T3 closed)?
- How many remain that genuinely require state-machine reasoning?
- Among the remaining ones, how complex are they? Is it 30 conservation
  theorems (each ~10 lines of Lean) or 30 multi-step liveness arguments
  (each ~100 lines)?
- Has the work in Phases 1–3 surfaced data-model issues that we should fix in
  the spec before continuing?

**Decision tree:**

| State after Phase 3 | Next move |
|---|---|
| ≥75 of 99 closed; remaining ones are simple conservation theorems | Try pure Lean transition relations — no Velvet needed. Estimate 2–3 months. |
| 50–75 closed; remaining are mix of conservation + lifecycle | **Velvet spike (2 weeks)** as originally planned. Then full state-machine phase if green. |
| <50 closed; data model itself feels unstable | Stop. Iterate on the data model in Lean first; re-spec.md if needed. |
| ≥90 closed; remaining ones are intractable or low-value | Declare victory. Document the gap in SPEC_COVERAGE.md and ship. |

The point of this gate: **Velvet is a tool we commit to only if we need it.**
After 3–6 months of Phase 1–3 work, the team knows Lean, knows the data model,
and can make the tooling decision with much better information than now.

## Phase 5 (conditional) — State-machine layer (4–8 months)

**Only execute if Phase 4 says we need state-machine verification AND we have
the time/people for it.**

If the chosen tool is **Velvet:**
- 2-week spike on lien lifecycle to validate the toolchain (the original Phase 1
  from the previous plan).
- ~30 collapsed engine verbs, organized in 7 clusters (source credit + lien,
  bucket lifecycle, account I/O, trade + accrual, close + B-booking, recovery,
  activation). Each becomes a Velvet `method` block.
- Per-cluster gate: SMT discharges ≥50% of `ensures`. If not, decompose or
  switch tools.

If the chosen tool is **pure Lean transition relations:**
- Define each verb as `state → state` function plus a separate
  `transition_invariant` theorem proved by hand.
- More verbose than Velvet but no external dependency.
- Mathlib `omega` / `linarith` / `ring` handle most obligations; the rest are
  manual.

If the chosen tool is **F\* or other:**
- Out-of-scope details — decide at Phase 4 based on what's left.

**Exit criterion:** every §14 item that survived Phase 3 has either a Lean
theorem or an explicit "not verified, accepted gap" entry in SPEC_COVERAGE.md.

## Phase 6 — Extraction & test vectors (2–4 weeks)

**Scope:**

- Extract the Lean spec to a runnable reference (OCaml or via `derive_tester_for`
  for property-based testing).
- Generate `formal_verification/test_vectors/*.json` corpus.
- Update `spec.md §14` to reference Lean theorem identifiers (e.g. `#1` →
  `Percolator.CreditRate.credit_capped_by_backing`).
- Final SPEC_COVERAGE.md showing per-invariant: which file, which theorem name,
  which technique tier.

## Decision tree (overall)

```
                Phase 1 (arithmetic)
                       ↓
                Phase 2 (structural types)
                       ↓
                Phase 3 (pure functions)
                       ↓
                Phase 4 — reassess
                       │
       ┌───────────────┼───────────────┬──────────────┐
       ▼               ▼               ▼              ▼
  ≥90 closed       50–75 closed    <50 closed     ≥75 closed
  STOP             Velvet spike    fix data        try pure
  (declare         (2 weeks)       model first      Lean state
  victory)            ↓                              relations
                  Phase 5 (Velvet                       ↓
                  state-machine)                    Phase 5 lite
                       ↓                              ↓
                  Phase 6 ← ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ┘
                  (extraction +
                  test vectors)
```

## Risks

1. **SMT struggles on the percolator-specific arithmetic.** cvc5/z3 are weak on
   nonlinear math like the credit-rate formula. Mitigation: Phase 1 proves these
   as named Mathlib theorems with `ring`/`linarith`, then any later state-machine
   work cites them as lemmas. Don't ask SMT to re-prove arithmetic.

2. **Mathlib has limited state-machine / separation-logic infrastructure.** If
   Phase 4 decides on pure-Lean transition relations, expect to build some
   tactics for "this operation conserves quantity Q." Mitigation: budget 1–2
   extra weeks in Phase 5 for tactic infrastructure.

3. **Phase 2 dependent-type design lock-in.** Bad type choices in Phase 2 make
   Phases 3+ harder. Mitigation: review Phase 2 output against a few sample §14
   items from each category before declaring Phase 2 done. Iterate the types if
   they don't compose.

4. **Lean port reveals a data-model issue.** A constraint that's true in Rust
   may not survive the spec. Mitigation: this is the *point* of the exercise —
   surface it, fix it in the Lean spec, document the divergence in
   SPEC_COVERAGE.md. Rust catches up later (or not).

5. **One engineer bottleneck.** 4–8 months single-person for Phases 1–3 is
   sequential. Mitigation: after Phase 2 lands, Phases 3 and (later) 5 are
   parallelizable by cluster.

## Success metrics

Tracked in `SPEC_COVERAGE.md`:

- **End of Phase 1:** all "Future" theorems in `WideMath.lean` proven; ~10
  §14 items annotated with their Lean theorem identifier.
- **End of Phase 2:** 15–25 §14 items annotated as "structural via type T."
- **End of Phase 3:** 30–45 §14 items closed (T1+T2+T3 cumulative).
- **End of Phase 4:** decision recorded — proceed with which tool, or stop.
- **End of Phase 5 (if executed):** ≥90 of 99 §14 items closed.
- **End of Phase 6:** spec.md §14 entries point at Lean theorem identifiers.

## What stays the same

- `tests/proofs_v16.rs` (the 230 Kani harnesses): untouched. Defends the Rust
  impl independently.
- `tests/v16_spec_tests.rs`: untouched.
- `src/wide_math.rs`, `src/v16.rs`: untouched by this plan. Rust may or may not
  eventually track the Lean spec — separate decision.

## Time and resources

- **Phase 1:** 4–8 weeks, one engineer with Lean familiarity.
- **Phase 2:** 3–5 weeks.
- **Phase 3:** 4–8 weeks.
- **Phase 4:** 1 week of reassessment work.
- **Phase 5 (conditional):** 4–8 months single-person, or 2–3 months with
  parallelization. May be skipped entirely.
- **Phase 6:** 2–4 weeks.

**Through Phase 4** (everything before the state-machine commitment): 3–5
months single-person.

**Through Phase 5** (if executed): 7–13 months single-person.

The team only commits to Phase 1 now (~6 weeks). Everything else is decided
based on what's actually left to do at each gate. Worst case — if the team
stops after Phase 3 — they still have ~40 §14 items closed, a tiered map of
the rest, and a working Lean spec foundation. That's a meaningful artifact
on its own.
