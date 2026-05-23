# Hand-off — Phase 5 verification effort

Last touched: 2026-05-21. Last commit: Phase 5 cluster 6 (conservation
and reconciliation).

## Where we are

**53 of 99 §14 invariants closed by Lean. Phase 5 is complete.**

Phases done:
- **Phase 1** — arithmetic refinements (U256 schoolbook, divRem, I256
  two's-complement). Closed with no `sorry`. Six Rust proptests bridge
  the Lean theorems to `wide_math.rs` via num-bigint.
- **Phase 2** — structural types. `Lifecycle`, `Lien` (indexed by
  `BackingSource`), `ValueFlow` (row-balanced), `State` (legs as
  function-typed map).
- **Phase 3** — pure-function ports. `HLock`, `FlatAccountEquity`,
  `SourceCreditAvailable`, `ClaimBoundBucket` sub-additivity,
  `ValidateAccountShape` predicate.
- **Phase 4** — reassessment gate. Decision: proceed to Phase 5 with
  pure Lean transition relations (not Velvet). See
  `REASSESSMENT_PHASE4.md`.
- **Phase 5 cluster 1** — lien lifecycle (`LienLifecycle.lean`).
- **Phase 5 cluster 2** — token-value-flow soundness
  (`ValueFlowSoundness.lean`).
- **Phase 5 cluster 3** — backing bucket lifecycle
  (`BackingBucket.lean`).
- **Phase 5 cluster 5** — recovery + activation
  (`Activation.lean`, `RecoveryFallback.lean`).
- **Phase 5 cluster 4** — close progress and priority
  (`ClosePriority.lean`, `CloseLedger.lean`).
- **Phase 5 cluster 6** — conservation and reconciliation
  (`BBookingExact.lean`, `StockReconciliation.lean`,
  `InsuranceLedger.lean`). The deferred §14 #13 and #14 are also
  closed here.

Per-cluster §14 closures are documented in `SPEC_COVERAGE.md`'s
"Phase X §14 closures" sections.

## What's next

Phase 5 is complete. Remaining work falls into three categories:

1. **The 46 §14 invariants still without Lean coverage.** Most are
   either operationally satisfied by Kani harnesses (see
   `SPEC_COVERAGE.md` rows tagged HIGH/MEDIUM Confidence) or
   require concrete account/ledger snapshots that the Lean spec
   abstracts away. Any new Lean coverage should target the
   HIGH+WEAK rows in the "Overclaim risk" section of
   `SPEC_COVERAGE.md` — those have a Kani harness whose name fits
   but only at concrete inputs.

2. **Hardening: bridge Lean transitions to the Rust impl.** The
   Phase 5 transition relations (lien, value-flow, bucket, ledger,
   close, activation, recovery) are spec-side. Add proptests under
   `tests/proofs_v16_lean_refinement.rs` that diff each Rust handler
   against its Lean transition. Same pattern as the six existing
   arithmetic bridges.

3. **Phase 6 (extraction).** Per `VERIFICATION_PLAN.md`. Generate a
   reference Rust kernel from the Lean specs so the bridge is
   automatic rather than per-handler. This is the multi-month
   commitment that was conditional on Phases 1–5 succeeding.

## Gotchas learned in this codebase

- **`open` is a reserved keyword in Lean 4.** I renamed
  `BackingBucket.open` → `openFresh`. If you write more lifecycle
  modules with constructors, watch for `open`, `let`, `match`, etc.
- **`Repr` cannot derive on function-typed fields.** `State.lean`'s
  `LienedAmountsBySource` and `PortfolioAccount.legs` (which uses
  `Nat → Option PortfolioLeg`) deliberately omit `deriving Repr`.
- **Bool tactic combinations are brittle.** `by_cases h : (a || b) =
  true; rw [if_pos h] / [if_neg h]` is fragile. The cleaner pattern is
  `cases h : a || b` and then `simp [h]` in both branches. See
  `HLock.lean::hLockLane_eq_HMax_iff` for the working pattern.
- **Operator precedence on `Bool || Bool = Bool`**: write
  `(a || b) = true` not `a || b = true` — Lean parses the second as
  `a || (b = true)`, coercing via `decide`.
- **`linarith` won't see Nat non-negativity automatically.** When
  proving `TWO_256 ≤ X + Y` from `TWO_256 ≤ Y`, use `omega` instead —
  it knows `Nat`. Trying `linarith` works only after explicit
  `Nat.zero_le` hypotheses.
- **`Int.natAbs_of_nonpos` doesn't exist in this Mathlib version.**
  Use `rw [Int.natCast_natAbs, abs_of_nonpos hle]` instead. The
  `Int.natCast_natAbs` lemma converts `(x.natAbs : Int) = |x|`, then
  `abs_of_nonpos` rewrites `|x| = -x` under `x ≤ 0`.
- **Existence-uniqueness statements on partial functions are dicey.**
  If you write `∃! c, ∀ cls, P cls = (if cls = c then ... else 0)`,
  the uniqueness usually fails in degenerate cases (e.g. when
  `amount = 0`). Prefer the cleaner row-level statement
  `creditFor own_class = amount ∧ creditFor other = 0`. See
  `ValueFlowSoundness.lean::TokenValueRow.creditFor_own_class`.
- **The Phase 1 arithmetic theorems are foundational. Cite them — do
  not re-prove.** `U256.checkedMul_correct`,
  `BoundArith.amountFromBoundNum_rounds_up`, etc. are stable.

## Workflow notes

- **One commit per cluster** with a descriptive message. Use the
  HEREDOC pattern. **Don't** reference `VERIFICATION_PLAN.md` or
  `REASSESSMENT_PHASE4.md` in commit messages — they're meta-docs
  that may evolve. Describe what the code does. (See
  [commit-message-style memory].)
- **Update `SPEC_COVERAGE.md`** at the end of each cluster: add a
  "Phase 5 cluster N §14 closures" subsection listing each invariant
  with its closing theorem identifier.
- **`lake build` from `/Users/abishek/code/percolator-v16/formal_verification`** —
  Lake's project root is one level down from the repo root. Running
  `lake build` from the repo root fails with "no configuration file".
- **Mathlib is heavy.** The first build after `lake build` takes
  several minutes. Incremental rebuilds are fast (~10s for a single
  file change). Don't run `lake clean` unless you really need to.

## File-by-file inventory (Phase 5)

| File | Closes | Approx lines |
|---|---|---:|
| `Percolator/LienLifecycle.lean`       | #19, #21, #30, #31, #32, #37, #39 | 325 |
| `Percolator/ValueFlowSoundness.lean`  | #4, #25, #26, #27 | 201 |
| `Percolator/BackingBucket.lean`       | #34, #35, #36, #40 | 297 |
| `Percolator/Activation.lean`          | #29, #58, #59, #60, #61 | 457 |
| `Percolator/RecoveryFallback.lean`    | #80, #81, #82 | 287 |
| `Percolator/ClosePriority.lean`       | #68, #92, #93 | 195 |
| `Percolator/CloseLedger.lean`         | #46, #47, #66, #67, #69, #70, #71, #72, #73 | 734 |
| `Percolator/BBookingExact.lean`       | #75 | 161 |
| `Percolator/StockReconciliation.lean` | #5, #95, #96, #97, #98, #99 | 426 |
| `Percolator/InsuranceLedger.lean`     | #13, #14 | 298 |

Plus 9 invariants closed by Phase 1–3 (`U256`, `I256`, `WideMath`,
`BoundArith`, `CreditRate`, `Lifecycle`, `Lien`, `ValueFlow`,
`State`, `HLock`, `FlatAccountEquity`, `SourceCreditAvailable`,
`ClaimBoundBucket`, `ValidateAccountShape`):
#1, #2, #15, #23, #42, #48, #50, #57, #87.

## Additional gotchas from clusters 4-5

- **Record literal projection doesn't reduce under `rfl` automatically.**
  After `cases h` on `some {…} = some l'`, the goal becomes
  `{…}.field op …`, which `rfl` will *not* close even when the field
  is unchanged by the update. Use `change <explicit form> ; omega` (or
  whatever closes the explicit form). The `unfold anchors` /
  `simp [anchors]` patterns also fail to peel the projection. The
  reliable pattern is to define helpers as conjunctions of
  field-equalities (`anchorsEq`) and discharge with `⟨rfl, …, rfl⟩`,
  one per field.
- **`split_ifs at h` already discards trivially-false branches.** When
  the if-then-else returns `none` in some branch and `h : … = some l'`,
  those branches collapse automatically — you don't get separate
  bullets for them. The reliable pattern is `split_ifs at h with h1 h2`
  followed by `all_goals cases h` and then a single proof for the
  surviving branch.
- **`split_ifs` hypothesis order**: when you bind `with h1 h2`, you get
  the *negated* conditions in the surviving (else-else) branch as
  hypotheses; `push_neg at h2` is usually needed before `omega`.

## Suggested order for next session

Phase 5 is complete. The next session should pick from the "What's
next" list above — most likely starting with item 2 (Rust↔Lean
refinement bridges via proptests) since that's the lowest-cost
hardening of what's already proven. The bridge pattern is in
`tests/proofs_v16_lean_refinement.rs` (six existing examples for
the Phase 1 arithmetic theorems).

If extending Lean coverage instead, prioritize the HIGH+WEAK
overclaim-risk invariants in `SPEC_COVERAGE.md` — those advertise
coverage but rely on concrete-input Kani harnesses with no symbolic
∀ guarantee.
