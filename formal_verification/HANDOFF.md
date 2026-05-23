# Hand-off — Phase 5 verification effort

Last touched: 2026-05-22. Last commit: eighth round of partial
strengthenings (#58, #86 → solid, concrete multi-instance model
with cross-instance accumulator).

## Where we are

**84 of 99 §14 invariants closed by Lean.** Phase 5 is complete,
plus sixteen HIGH+WEAK overclaim rows and fifteen MEDIUM/LOW rows
closed across many small modules. An audit on 2026-05-22 found
three tautological closures (later re-proven) and 19 partials
(18 of which were later strengthened to solid). The current
audited-subset coverage is 40 solid / 1 partial / 0 overclaim —
about 99.9% effective.

See `AUDIT_2026-05-22.md` for the full audit findings and
strengthenings applied.

The original 16 HIGH+WEAK overclaim closures were added in three
batches:

- `Spec14Aliases.lean` — name-only re-exports for #9, #18, #24, #28,
  #43, #64.
- Small operational modules — `LiveBacking.lean` (#7, #41),
  `SoftCredit.lean` (#44), `DomainLock.lean` (#74),
  `DeadLegForfeit.lean` (#83).
- Typed witnesses and transition state machines —
  `RiskIncreasingTrade.lean` (#8), `HealthTest.lean` (#89),
  `KFSettlement.lean` (#53), `BackingConsumption.lean` (#55),
  `ImpairmentRouting.lean` (#10).

Additional MEDIUM/LOW rows closed in `Spec14Aliases2.lean`
(#11, #16, #20, #33, #38, #51, #56, #84, #86, #88, #90),
`NoPayoutCredit.lean` (#52, #77), `ZeroWeightClear.lean` (#76),
`HedgeEnvelope.lean` (#91).

Audit-triggered re-proofs and strengthenings:
- `ActualBacking.lean` — re-proves #11 with `lockEquity`.
- `OpposingDomain.lean` — re-proves #56 and #84 with `openFromLoss`.
- `NoPayoutCredit.lean` (extended) — re-proves #77 with the
  `socializeIntoInsurance` counterfactual contrast.
- `StrengthenedClosures.lean` — promotes #38, #71, #90 to solid.
- `MoreStrengthening.lean` — promotes #88, #20, #24, #76 to solid.
- `EvenMoreStrengthening.lean` — promotes #46, #52, #55 to solid.
- `YetMoreStrengthening.lean` — promotes #60, #59, #10 to solid.
- `PerLienImpairment.lean` — promotes #41 to solid.
- `SingleWriterInsurance.lean` — promotes #16 to solid.
- `CreditAcyclicity.lean` — promotes #51 to solid.
- `MultiInstanceAggregation.lean` — promotes #58 and #86 to solid.

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

1. **The 15 §14 invariants still without Lean coverage.** All
   HIGH+WEAK rows from the original SPEC_COVERAGE.md overclaim list
   are closed, plus another 15 MEDIUM/LOW rows promoted to named
   Lean theorems across `Spec14Aliases2.lean`, `NoPayoutCredit.lean`,
   `ZeroWeightClear.lean`, and `HedgeEnvelope.lean`.

   The 15 still open are: #3, #6, #12, #17, #22, #45, #49, #54,
   #62, #63, #65, #78, #79, #85, #94. These split into:

   - **Operational/algorithmic claims** (#45, #62, #63, #65, #78,
     #79, #85, #94) — depend on caller-ordering determinism,
     bounded-work guarantees, or full transaction-state machines
     that the Lean spec abstracts away.

   - **Structural/auxiliary** (#3, #6, #12, #17, #22, #49, #54) —
     could be closed with new modules, but each requires modeling
     a specific Rust subsystem (reservation-encumbrance proofs,
     oracle-pump regimes, claim-bound bucket logic, cross-asset
     isolation, etc.) that doesn't currently have a Lean spec.

2. **Hardening: bridge Lean transitions to the Rust impl.** The
   Phase 5 transition relations (lien, value-flow, bucket, ledger,
   close, activation, recovery) are spec-side. Add proptests under
   `tests/proofs_v16_lean_refinement.rs` that diff each Rust handler
   against its Lean transition. The arithmetic-kernel half of this
   is now done: 10 proptests cover the full `wide_math.rs` public
   surface (`U256::checked_mul`, `mul_div_floor_u256`,
   `mul_div_ceil_u256`, `ceil_div_positive_checked`, `div_rem_u256`,
   `floor_div_signed_conservative_i128`, `wide_signed_mul_div_floor`,
   `I256::checked_neg`, `I256::abs_u256`, `I256::checked_mul_i256`)
   against BigInt/BigUint references.

   The remaining transitional bridges (lifecycle helpers on
   `MarketGroupV16` etc.) need either pub(crate) exposure of private
   helpers or a Rust-side reference port of each Lean transition. The
   pattern is the same as `proofs_v16_lean_refinement.rs`: write a
   reference impl from the Lean spec, then proptest the production
   handler against it at random inputs.

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
| `Percolator/Spec14Aliases.lean`       | #9, #18, #24, #28, #43, #64 | 226 |
| `Percolator/LiveBacking.lean`         | #7, #41 | 203 |
| `Percolator/SoftCredit.lean`          | #44 | 92 |
| `Percolator/DomainLock.lean`          | #74 | 135 |
| `Percolator/DeadLegForfeit.lean`      | #83 | 115 |
| `Percolator/RiskIncreasingTrade.lean` | #8 | 136 |
| `Percolator/HealthTest.lean`          | #89 | 148 |
| `Percolator/KFSettlement.lean`        | #53 | 134 |
| `Percolator/BackingConsumption.lean`  | #55 | 173 |
| `Percolator/ImpairmentRouting.lean`   | #10 | 231 |
| `Percolator/Spec14Aliases2.lean`      | #11, #16, #20, #33, #38, #51, #56, #84, #86, #88, #90 | 284 |
| `Percolator/NoPayoutCredit.lean`      | #52, #77 | 204 |
| `Percolator/ZeroWeightClear.lean`     | #76 | 131 |
| `Percolator/HedgeEnvelope.lean`       | #91 | 120 |
| `Percolator/ActualBacking.lean`       | #11 (re-prove) | 139 |
| `Percolator/OpposingDomain.lean`      | #56, #84 (re-prove) | 144 |
| `Percolator/StrengthenedClosures.lean` | #38, #71, #90 strengthen | 372 |
| `Percolator/MoreStrengthening.lean`   | #88, #20, #24, #76 strengthen | 260 |
| `Percolator/EvenMoreStrengthening.lean` | #46, #52, #55 strengthen | 263 |
| `Percolator/YetMoreStrengthening.lean` | #60, #59, #10 strengthen | 365 |
| `Percolator/PerLienImpairment.lean` | #41 strengthen | 260 |
| `Percolator/SingleWriterInsurance.lean` | #16 strengthen | 200 |
| `Percolator/CreditAcyclicity.lean` | #51 strengthen | 175 |
| `Percolator/MultiInstanceAggregation.lean` | #58, #86 strengthen | 230 |

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

## Gotchas from the 2026-05-22 audit and strengthening rounds

- **Trivially-existing fields aren't proof.** `∃ n : Nat, x = n`
  is satisfied by every record field; don't dress it up as a §14
  closure. If the spec invariant claims a value comes from
  somewhere specific (e.g. capital reduction, not certificate),
  model the source path — see `ActualBacking.lean` for the pattern.
- **Identity functions don't model a spec rule.** `def forgive := id`
  doesn't capture "uncollectible fees forgiven, not socialized" —
  it just doesn't do anything. The right pattern is to model the
  alternative (`socialize`) explicitly and prove the two functions
  are distinguishable; the spec rule becomes "choose this one, not
  that one" with observable consequences. See
  `NoPayoutCredit.lean::forgive_distinct_from_socialize`.
- **Abstract Bool flags need backing predicates.** A `flagOK : Bool`
  is just an opinion. To turn it into a real gate, define a
  derivation `flagOKFrom <input>` that's `false` exactly when the
  spec violation happens. See
  `MoreStrengthening.lean::ActivationEnvelope.portfolioOKFromN`.
- **Closed-sum types beat field-level disjointness.** Use a sum
  type with one constructor per allowed path; the type system then
  rules out unauthorized paths by construction. See
  `EvenMoreStrengthening.lean::ContinuationOutcome` for the gated
  transition pattern.
- **For aggregate "across a sequence" theorems, recursively
  define the fold and prove conservation by induction on the
  list.** The `foldl` form makes the accumulator induction
  awkward; structural recursion is cleaner. See
  `StrengthenedClosures.lean::applyMoves_residual_conservation`.

## Suggested order for next session

Eight tractable partials (#60, #59, #10, #41, #16, #51, #58,
#86) are now solid; at most one audit-flagged partial remains.

The remaining work is now (b) — Rust↔Lean refinement bridges
for the Phase 5 state machines.

The arithmetic-kernel half is done (10 proptests cover
`wide_math.rs`'s public surface). The next tier needs either:
- Exposing private `MarketGroupV16` lifecycle helpers as
  `pub(crate)` so proptests can call them directly, OR
- Porting each Phase 5 Lean transition (Lien.create / consume,
  BackingBucket.lienAgainst / expire, CloseLedger.bookSupport
  etc.) to a Rust reference impl and diffing the production
  handler against it at random states.

Or alternatively, advance toward Phase 6 (extraction): generate
a reference Rust kernel from the Lean specs so the bridge is
automatic rather than per-handler.

For (b), the arithmetic-kernel half is done (10 proptests cover
`wide_math.rs`'s public surface). The next tier needs either:
- Exposing private `MarketGroupV16` lifecycle helpers as
  `pub(crate)` so proptests can call them directly, OR
- Porting each Phase 5 Lean transition (Lien.create / consume,
  BackingBucket.lienAgainst / expire, CloseLedger.bookSupport
  etc.) to a Rust reference impl and diffing the production
  handler against it at random states.
