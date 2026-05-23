# Phase 4 — Reassessment Gate

Written 2026-05-21 against the state captured in `SPEC_COVERAGE.md`
after the Phase 3 commit (`2ae3069`).

Per `VERIFICATION_PLAN.md:174`, this is the one-week reassessment gate
between the data-model / pure-function work and the (conditional)
state-machine layer.

## Tally — §14 invariants discharged

### Fully closed by Lean (7)

| #  | Invariant | Closure |
|---:|---|---|
| 2  | `token_value_flow_proof_every_quote_atom_has_one_debit_and_one_credit` | Structural — `ValueFlow.lean::TokenValueFlow.total_debit_eq_total_credit` is `rfl`. |
| 15 | `amount_from_bound_num_up_rounds_up_for_insurance_credit` | `BoundArith.lean::amountFromBoundNum_rounds_up`. |
| 23 | `insurance_backed_lien_never_counts_as_both_support_and_insurance` | Structural — `Lien.lean::Lien` is indexed by `BackingSource`. |
| 42 | `credit_rate_num_bounded_below_and_above` | `CreditRate.lean::creditRateNum_le_scale`. |
| 48 | `claim_bound_bucket_formula_never_understates_source_domain_claims` | `ClaimBoundBucket.lean::amountFromBoundNum_subadditive` + list form. |
| 57 | `no_global_B_index` | Structural — `State.lean`: `bNum` fields exist only in `AssetState`. |
| 87 | `canonical_single_leg_per_asset` | Structural — `State.lean::PortfolioAccount.legs : Nat → Option PortfolioLeg`. |

### Partially closed by Lean (2)

| #  | Invariant | Closure | Remaining |
|---:|---|---|---|
| 1  | `source_domain_positive_credit_capped_by_realizable_backing` | Formula half in `CreditRate.lean` + `SourceCreditAvailable.lean`. | The "realizable backing aggregation" half requires per-bucket state-machine reasoning. |
| 50 | `credit_rate_recomputation_is_bounded_by_domain_count_and_bucket_count` | Per-domain math in `CreditRate.lean`. | The "bounded by domain count" half is an iteration-bound argument (Phase 5). |

### Score

**7 fully closed + 2 partially = effectively 8 of 99** (rounding the
partial closures down to 0.5 each).

The plan's optimistic projection at the end of Phase 3 was 30–45 (T1+T2+T3
cumulative). We're at ~8. The gap is **not** due to data-model
instability or tooling failure; it's that **most §14 invariants in this
spec are state-machine-flavored** rather than pure-function statements.

## What's actually left, by required technique

Counting the 91 remaining invariants by what they need:

| Required technique | Approximate count | Examples |
|---|---:|---|
| **Operational state-machine reasoning** (preservation across transitions) | 50+ | #3-13, #16-30, #32-41, #43-47, #51-56, #58-86, #88-99 — most of the spec. |
| **More pure-function ports** (could be Phase 3+ extensions) | 10-15 | #34-36 (bucket expiry), #38-40 (lien consumption arithmetic), #44-45 (locked face / withdrawal sums), #65 (drift credit), #75 (B booking remainder). |
| **More structural type wins** (could be Phase 2+ extensions) | 3-5 | #3 (reservation encumbrance separated from value flow — already done via separate type), #14 (insurance spend disjointness — could be encoded), #20-22 (insurance lien lifecycle). |

The dominant work is state-machine, by a 4:1 margin.

## Decision

Re-reading the plan's decision tree (`VERIFICATION_PLAN.md:190`):

> | State after Phase 3 | Next move |
> |---|---|
> | ≥75 of 99 closed; remaining ones are simple conservation theorems | Pure Lean transition relations. |
> | 50–75 closed; remaining are mix of conservation + lifecycle | Velvet spike (2 weeks). |
> | <50 closed; **data model itself feels unstable** | Stop. Iterate on the data model. |
> | ≥90 closed; remaining are intractable or low-value | Declare victory. |

We're at <50, but the data model is **not** unstable. The plan's
"<50" branch presupposes data-model trouble; ours is solid.

**Recommendation: proceed to Phase 5 (state-machine layer) with pure
Lean transition relations.** Velvet is not a good fit because:

1. Lean + Mathlib has carried the arithmetic and structural work
   cleanly. Adding a second prover (Velvet/F\*) doubles the surface
   area without obvious gain.
2. The remaining invariants are mostly **conservation across
   mutations** — a class Lean handles well via inductive transition
   relations and `simp` / `linarith` automation.
3. The 9 closures so far prove the data model and arithmetic
   foundations are correct. Building transition relations on top is
   incremental, not exploratory.

The plan's Phase 5 lite ("pure Lean transition relations") matches
this. Expect each invariant to be ~10–50 lines of Lean depending on
how many sub-properties it composes.

### Suggested Phase 5 ordering

Tackle clusters together so the supporting transition lemmas amortize:

1. **Lien lifecycle** (#11, #18-22, #30-33, #37-39) — ~10 invariants,
   shared `lienCreate`/`lienConsume`/`lienRelease`/`lienImpair`
   transition relations.
2. **Token-value-flow soundness** (#4, #13, #14, #25-27) — ~6
   invariants on top of the structurally-balanced `TokenValueFlow`.
3. **Backing bucket lifecycle** (#34-36, #40-41) — ~5 invariants,
   shared `bucketExpire` / `bucketImpair` transitions.
4. **Close progress** (#46-47, #66-73, #92-93) — ~10 invariants,
   close-state machine.
5. **Recovery + activation** (#29-31, #58-61, #80-82) — ~8
   invariants.
6. **Conservation / reconciliation** (#5, #75, #95-99) — ~7
   invariants on top of the value-flow conservation.

Total Phase 5 budget: ~3 months single-person, parallelizable across
clusters.

## What this commit notes for the next agent

- **The data model in `Percolator/State.lean` is stable.** Don't
  rewrite it. Add operational transition functions that take the
  existing structures.
- **Use the existing `Lien` type indexing on `BackingSource`.** The
  lifecycle lemmas should preserve the per-source split.
- **Don't try to encode every Rust validator field-by-field.** The
  Lean spec is the source of truth; the Rust impl tracks it
  approximately, with Kani harnesses defending the bit-level details.
- **The Phase 1 arithmetic refinements (`U256`, `I256`, `WideMath`,
  `BoundArith`, `CreditRate`) are all closed; cite them as lemmas in
  transition proofs rather than re-proving.**

## Status: Phase 4 complete. Recommend proceeding to Phase 5 with pure Lean transition relations.
