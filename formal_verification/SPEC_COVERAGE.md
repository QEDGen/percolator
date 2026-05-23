# SPEC_COVERAGE — Mapping spec.md §14 Invariants to Kani Harnesses

This document traces the 99 numbered "Required proof and TDD coverage" invariants from
`spec.md:1431-1529` to the 230 Kani proof harnesses in `tests/proofs_v16.rs` (plus 7 in
`tests/proofs_v16_arithmetic.rs` and the 2 Lean refinement proptests in
`tests/proofs_v16_lean_refinement.rs`). It was generated on 2026-05-20 by walking each
invariant and grepping for harness names whose semantics match. Harness function bodies
were spot-read where the name alone was ambiguous. There are no `///` doc comments on
the Kani harnesses, so confidence rests on function names and inspected bodies.

## Confidence levels

- **HIGH** — One or more harnesses plainly prove the invariant: a reader inspecting
  the code would agree the claim is established.
- **MEDIUM** — A harness covers part of the claim, or covers a related claim that
  implies the invariant under reasonable bounded assumptions (e.g. the proof works
  only for the closed-leg direction, only for `n=1` domain, or only for one of two
  symmetric sides).
- **LOW** — Only keyword overlap or partial structural alignment; the connection is
  plausible but not directly verified. Treat as effectively uncovered for audit.
- **NONE** — No plausible harness found.

## Strength tiers

Each cited harness is also tagged with one of:

- **`[SYM]`** — Genuinely symbolic. Uses `kani::any` over wide types (u64/u128/i128)
  or has ≥3 symbolic inputs that meaningfully explore the input space. Real bounded
  ∀ verification within the unwind bound. **19 of 237 harnesses.**
- **`[SEMI]`** — Semi-symbolic. Uses 1–2 small `kani::any` inputs (typically `bool` or
  `u8` case selectors picking among hardcoded regimes). Verifies a handful of
  representative branches symbolically. **80 of 237.**
- **`[CON]`** — Concrete. Zero `kani::any`, fixed-input fixture. Equivalent to a
  `#[test]` run through Kani's harness machinery — valid as a test of behavior at
  that specific input, but provides no symbolic ∀ guarantee. **138 of 237.**

The Strength field for each invariant rolls these up: STRONG if ≥1 cited harness is
SYM, MEDIUM if ≥1 is SEMI but none are SYM, WEAK if all are CON.

## Summary

```
Confidence (does any harness cover this invariant?):
  HIGH:   48 invariants
  MEDIUM: 32 invariants
  LOW:    14 invariants
  NONE:    5 invariants

Strength (is the coverage symbolic ∀ or concrete-input?):
  STRONG: 18 invariants (≥1 cited harness is genuinely symbolic — kani::any over wide
                         types or ≥3 symbolic inputs — OR has a Lean ∀-theorem)
  MEDIUM: 50 invariants (only semi-symbolic harnesses — small boolean/u8 case selectors)
  WEAK:   26 invariants (all cited harnesses are concrete-input — fixed fixtures, no symbolic state)
  N/A:    5 invariants (no harnesses to grade — see Confidence: NONE)

Lean coverage (Phases 1–3 of VERIFICATION_PLAN.md complete; Phase 5 cluster 1 (lien lifecycle) in progress):

Phase 1 — arithmetic refinements:
  Percolator/WideMath.lean   — wideningMulU128_correct + 4 corollaries
  Percolator/U256.lean       — toNat_lt, toNat_mul, both_hi_nonzero_overflows,
                               checkedMul_both_hi_zero, checkedMul_correct,
                               divRemU256_correct (+ quotient/remainder bounds)
  Percolator/I256.lean       — rawNat_lt_TWO_256, sign_iff_raw, negLimbs_raw,
                               checkedNeg_correct, absU256_correct,
                               checkedMulInt_some / _none / _eq_mul
  Percolator/CreditRate.lean — 7 theorems closing §14 #42, parts of #1 and #50
  Percolator/BoundArith.lean — 8 theorems closing §14 #15

Phase 2 — structural invariants via dependent types:
  Percolator/Lifecycle.lean  — Side, SideMode, AssetLifecycle, MarketMode,
                               BackingBucketStatus, BackingSource enums +
                               inductive .Step transition relations
  Percolator/Lien.lean       — Lien indexed by BackingSource (closes §14 #23
                               structurally); LienedAmountsBySource with
                               counterparty+insurance partition
  Percolator/ValueFlow.lean  — TokenValueFlow as list of TokenValueRow, each
                               row carries one debit/credit/amount triple, so
                               §14 #2 (total_debit = total_credit) is `rfl`
  Percolator/State.lean      — AssetState (B-index lives here only — §14 #57),
                               PortfolioLeg, PortfolioAccount.legs as
                               AssetSlot→Option PortfolioLeg (closes §14 #87),
                               MarketGroup; PerSide for long/short symmetry

Phase 3 — pure-function ports:
  Percolator/HLock.lean              — hLockLane / selectHLock + correctness
                                       (HMax-iff-force-flag, HMin-iff-no-force,
                                       output is hMin-or-hMax, default-HMin case)
  Percolator/FlatAccountEquity.lean  — accountEquity = capital + pnl − feeDebt
                                       (with closed form, monotonicity in
                                       capital/pnl/feeCredits)
  Percolator/SourceCreditAvailable.lean — availableBackingNum stateless ledger
                                       query; soundness/completeness against
                                       the precondition; bounded-by-reserves.
                                       Closes the "available backing" half of
                                       §14 #1 / feeds §14 #50.
  Percolator/ClaimBoundBucket.lean   — amountFromBoundNum sub-additivity
                                       (pairwise + list form). Closes §14 #48
                                       (claim_bound_bucket_formula never
                                       understates source-domain claims).
  Percolator/ValidateAccountShape.lean — ValidShape predicate aggregating
                                       fee-credit / reserved-PnL / leg-asset
                                       uniqueness / leg-lifecycle conditions.

Phase 5 cluster 1 — lien lifecycle (transition relations):
  Percolator/LienLifecycle.lean      — Lien.create / .consume / .release / .impair
                                       transition functions; per-transition
                                       arithmetic theorems closing §14 #32,
                                       #37, #39, #21/#31, and #19/#30 (the
                                       single-lien conservation half).

Phase 5 cluster 3 — backing bucket lifecycle:
  Percolator/BackingBucket.lean      — BackingBucket model + openFresh /
                                       expire / markImpaired / lienAgainst /
                                       consumeLien / releaseLien / impairLien
                                       transitions; aggregation lemmas
                                       (sumAvailable / sumFreshUnliened).
                                       Closes §14 #34, #35, #36, #40.

Spec14.lean + focused modules — additional MEDIUM/LOW rows
closed by citing existing infrastructure or small new structures:
  Percolator/Spec14.lean              — §14-row index file: named
                                       theorems citing Phase 5
                                       infrastructure for §14 #9
                                       (no double use of lien
                                       claim/backing), #11 (backing
                                       is Nat amount not
                                       certificate), #16 (single
                                       canonical writer via
                                       InsuranceLedger transitions),
                                       #18 (insurance create touches
                                       insurance only), #20 (consume
                                       atomic decrement + spend),
                                       #24 (close residual partition
                                       disjoint), #28, #33 (lien
                                       creatable predicate matches
                                       capacity / lifecycle), #43
                                       (lien creation requires
                                       backing ≤ available), #51
                                       (no circular credit), #56
                                       (residual to single domain),
                                       #64 (pending obligation
                                       credit once), #84 (dead-leg
                                       books to named domain), #86
                                       (UIAggregate can't witness
                                       health), #90 (penalty fields
                                       disjoint by typing). The
                                       #38, #46, #52, #55, #59, #60,
                                       #71, #76, #88 closures live
                                       in their topical modules
                                       (BackingBucket, CloseLedger,
                                       NoPayoutCredit,
                                       BackingConsumption,
                                       Activation, ZeroWeightClear,
                                       LienLifecycle) and are
                                       cross-referenced from the
                                       Spec14.lean header.
  Percolator/NoPayoutCredit.lean      — PayoutFromCredit structure
                                       whose payoutAmount is bounded
                                       by lienBackedAmount only;
                                       soft credit yields zero
                                       payout when there is no lien.
                                       FeeResolution with
                                       uncollectible portion routed
                                       through applyForgiveness
                                       (no-op on StockClasses) —
                                       uncollectible fees forgiven,
                                       never socialized. Closes §14
                                       #52, #77.
  Percolator/ZeroWeightClear.lean     — ZeroWeightClearance closed
                                       sum (insurance or
                                       explicitBacked only); no
                                       bBookB constructor. apply
                                       routes through bookInsurance
                                       or bookExplicit, both of
                                       which require backing. Closes
                                       §14 #76.
  Percolator/HedgeEnvelope.lean       — HedgeBucket with hedgeCredit
                                       = min(hedgedSize,
                                       envelopeCap); structural
                                       bounds in both directions;
                                       monotonicity in raw
                                       requirement. Closes §14 #91.

Heavy overclaim hardening — HIGH+WEAK rows needing typed witnesses
or transition state machines:
  Percolator/RiskIncreasingTrade.lean — TradeStep closed sum with
                                       riskDecreasing, riskIncreasing
                                       (carrying Lien Counterparty
                                       with 0 < backing proof field),
                                       riskIncreasingInsurance
                                       symmetric. Risk-increasing
                                       trade cannot be constructed
                                       without backing — structural
                                       witness. consumedBacking +
                                       zero_consumed_implies_riskDecreasing
                                       give the precise classification.
                                       Closes §14 #8.
  Percolator/HealthTest.lean          — HealthInputs record splitting
                                       positive vs negative equity;
                                       pendingObligationExposure
                                       appears in negativeEquity once.
                                       equity_decreases_by_pending_increment
                                       (linear with coefficient one);
                                       positiveEquity_independent_of_pending
                                       (no appearance elsewhere);
                                       double_counted_strict_increase
                                       contrast lemma. Closes §14 #89.
  Percolator/KFSettlement.lean        — kfSettlementStep atomic
                                       transition consuming backing
                                       and locking face claim in a
                                       single return; the atomic
                                       theorem combines both
                                       per-field witnesses; total
                                       conserved (backing + locked).
                                       Closes §14 #53.
  Percolator/BackingConsumption.lean  — VaultSnapshot with senior
                                       invariant vault = loserCapital
                                       + winnerCapital + bookedLoss;
                                       consumeBacking transition
                                       moves loser capital into
                                       bookedLoss one-for-one with
                                       vault preserved; the senior
                                       invariant is preserved by
                                       construction. Closes §14 #55.
  Percolator/ImpairmentRouting.lean   — AccountWithLiens record with
                                       hasImpairedLien flag; normalStep
                                       refuses to fire when impaired
                                       and unresolved; routeDeleverage
                                       / routeLiquidation /
                                       routeRecovery are the only
                                       three paths that clear the
                                       flag, each recording its
                                       resolution tag. closed-world
                                       routing witness shows every
                                       resolved account names one
                                       of the three routes. Closes
                                       §14 #10.

Operational overclaim hardening — HIGH+WEAK rows requiring new
structures rather than name-only re-exports:
  Percolator/LiveBacking.lean         — BackingBucket.liveAvailable
                                       (Fresh-only contribution) plus
                                       sumLiveAvailable aggregation
                                       with all-non-Fresh-implies-zero;
                                       creditRate_zero_when_no_fresh;
                                       expireAndImpairAll atomic
                                       transition draining
                                       validLiened into impairedLiened
                                       with totalBacking preserved.
                                       Closes §14 #7, #41.
  Percolator/SoftCredit.lean          — softCredit = faceClaim −
                                       lockedFaceClaim; the no-double-
                                       count identity
                                       softCredit_plus_locked_eq_face
                                       under well-formed lock budget;
                                       monotonicity in lock; bounded
                                       sum even in the degenerate
                                       over-lock case. Closes §14 #44.
  Percolator/DomainLock.lean          — DomainLock with per-side
                                       blocking; kfAccrueAssetWide
                                       takes no DomainLock argument
                                       (independence by typing); the
                                       sharpening lemma
                                       sideStep_blocked_when_locked
                                       contrasts side-specific ops.
                                       Closes §14 #74.
  Percolator/DeadLegForfeit.lean      — DeadLegOutcome closed sum
                                       (zeroPositive vs
                                       boundedFallback with carried
                                       FallbackPriceInput.accepted
                                       proof); positivePayout_zero
                                       on both constructors;
                                       no_unverified_constructor
                                       witness; envelope deviation
                                       relayed through
                                       boundedFallback_envelope_holds.
                                       Closes §14 #83.

Phase 5 cluster 6 — conservation and reconciliation:
  Percolator/BBookingExact.lean      — bBookingStep (single-step
                                       residual booking arithmetic);
                                       exact-conservation theorem
                                       (delta_B * W + new_R =
                                       chunk * SOCIAL_LOSS_DEN + R);
                                       remainder-< W bound; explicit
                                       delta/remainder forms;
                                       monotone-in-chunk; zero-chunk
                                       degenerate; bBookingRec
                                       (multi-chunk recursion) + the
                                       conservation lemma across an
                                       arbitrary chunk sequence.
                                       Closes §14 #75.
  Percolator/StockReconciliation.lean — StockClasses 10-tuple +
                                       totalV; reconciled predicate
                                       at any vault V; ClassLedgers
                                       O(1) source-of-truth bridge
                                       with matchesLedgers and
                                       per-class projections;
                                       DriftReserveBackingClass
                                       inductive forcing single-class
                                       mapping; RoundingSplit with
                                       residue/flow-balances theorem
                                       (sum(A_j) + residue = X);
                                       ResidueSink with applyResidue
                                       to settlement-residue or
                                       protocol-surplus class;
                                       HealthBackingPayoutWitness
                                       only constructible from
                                       userClaim role — protocolOwned
                                       (residue/surplus) refused.
                                       Closes §14 #5, #95, #96, #97,
                                       #98, #99.
  Percolator/InsuranceLedger.lean    — InsuranceLedger with embedded
                                       conservation proof field;
                                       reserve / release / consume
                                       lifecycle helpers each
                                       preserving conservation in
                                       their construction;
                                       consume_atomic_decrement_and_spend
                                       (reservation -= amount and
                                       domainSpent += amount in one
                                       step); InsuranceTxn +
                                       applySeq sequence-of-flows
                                       model with conservation
                                       holding after any prefix.
                                       Closes the deferred §14 #13
                                       and #14 from cluster 2.

Phase 5 cluster 4 — close progress and priority:
  Percolator/ClosePriority.lean      — ClosePriority record (4-tuple),
                                       lex strict-less-than over
                                       (deficit DESC, notional DESC,
                                       drift_slot ASC, closeId ASC);
                                       lt_irrefl / lt_asymm / lt_trans /
                                       lt_trichotomy; no_two_cycle /
                                       no_three_cycle from asymmetry +
                                       transitivity;
                                       distinct_closeId_strictly_comparable.
                                       Closes §14 #68, #92, #93.
  Percolator/CloseLedger.lean        — CloseLedger record mirroring
                                       v16.rs::CloseProgressLedgerV16;
                                       transition methods (bookSupport,
                                       bookInsurance, bookB,
                                       bookExplicit,
                                       bookPendingObligation, addDrift,
                                       applyQuantityAdl, finalize,
                                       cureAndCancel); anchorsEq +
                                       per-transition preservation
                                       theorems; per-transition residual
                                       strict-decrease (+ drift dual);
                                       bookPendingObligation atomic
                                       credit-debit match;
                                       per-transition monotonicity of
                                       booking counters;
                                       DriftBacking + closeDriftReserveBacked
                                       predicate + fail-closed
                                       continuationDecision; cure-and-cancel
                                       irreversibility precondition;
                                       finalize requires adlApplied and
                                       zero residual; WeightAttribution
                                       enforces 0 < backing by typing;
                                       does_not_touch_pendingObligation
                                       lemmas for every non-credit
                                       transition. Closes §14 #46, #47,
                                       #66, #67, #69, #70, #71, #72, #73.

Phase 5 cluster 5 — recovery + activation:
  Percolator/Activation.lean         — InsuranceReservation + lien helper
                                       with matching lienCreatable predicate;
                                       BackingBucket.lienCreatable bridge to
                                       lienAgainst; HealthProof / UIAggregate /
                                       AccountHealthWitness type split;
                                       ActivationEnvelope record;
                                       AssetSlotState + isReconciledZero;
                                       Activate transition relation with
                                       envelope/zero-state/epoch-bump witness;
                                       HealthCert.validIn with epoch-bump
                                       invalidation. Closes §14 #29, #58, #59,
                                       #60, #61.
  Percolator/RecoveryFallback.lean   — envelopeValid predicate
                                       (abs(P_fb - P_ref)*10000 ≤ devBps*P_ref);
                                       per-leg + per-account
                                       legTransferBound / accountTransferBound
                                       ceiling-divs; FallbackPriceInput with
                                       accepted predicate and fail-closed
                                       conditionalPayout. Closes §14 #80,
                                       #81, #82.

Phase 5 cluster 2 — token-value-flow soundness (named constructors):
  Percolator/ValueFlowSoundness.lean — lienCreateFlow (empty),
                                       internalTransferFlow, insuranceToCloseSpentFlow,
                                       recoveryInsurancePayoutFlow.
                                       Closes §14 #4, #25, #26 (structural row form),
                                       #27. The conservation-over-history
                                       §14 #13 and #14 require a sequence-of-flows
                                       model — deferred to a future cluster.

Refinement proptests (tests/proofs_v16_lean_refinement.rs) bridge each Phase 1
Lean theorem to the production Rust impl:
  u256_checked_mul_matches_biguint_spec
  mul_div_floor_u256_matches_biguint_spec_u128_inputs
  div_rem_u256_matches_biguint_spec
  i256_checked_neg_matches_bigint_spec
  i256_abs_u256_matches_bigint_spec
  i256_checked_mul_matches_bigint_spec
```

Phase 2 §14 closures by structural typing (no proofs — violations don't
typecheck or aren't expressible):

  #2  token_value_flow_proof_every_quote_atom_has_one_debit_and_one_credit
      Closed by `Percolator/ValueFlow.lean`: `TokenValueRow` carries a single
      amount that is both debited and credited; `totalDebit = totalCredit` is
      definitional equality.
  #23 lien_never_both_support_and_insurance
      Closed by `Percolator/Lien.lean`: `Lien` is indexed by `BackingSource`,
      so `Lien Counterparty` and `Lien Insurance` are distinct types. Aggregate
      `SourceCreditLienAggregate` holds them in separately-typed fields. No
      expression can construct a lien that is both.
  #57 no_global_B_index
      Closed by `Percolator/State.lean`: `bNum` fields live exclusively inside
      `AssetState`. `MarketGroup` exposes `bNum slot side` only as a
      derivation through `assets`, structurally per-asset.
  #87 canonical_single_leg_per_asset
      Closed by `Percolator/State.lean`: `PortfolioAccount.legs : Nat →
      Option PortfolioLeg` is a finite map; at most one leg per slot is the
      function-type signature. `leg_unique_per_slot` witnesses the trivial
      Option uniqueness.

Phase 3 §14 closures by pure-function theorems:

  #1  source_domain_positive_credit_capped_by_realizable_backing
      Strengthened by `Percolator/SourceCreditAvailable.lean`. The "available
      backing" half of #1 is now a Lean theorem (`availableBackingNum_le_total_reserves`).
      The full §14 #1 (combining this with `CreditRate.lean`'s rate cap) is
      thus discharged by composition.
  #48 claim_bound_bucket_formula_never_understates_source_domain_claims
      Closed by `Percolator/ClaimBoundBucket.lean`:
      `amountFromBoundNum_subadditive` (pairwise) and
      `amountFromBoundNum_le_sumAmountFromBoundNum` (list form). The
      bucket-level formula always returns at least the source-level
      ceiling — never understates.
  #50 source_credit_rate_recomputation_bounded
      The per-domain arithmetic (CreditRate.lean) plus the ledger query
      (SourceCreditAvailable.lean) together fully discharge the formula
      half of this invariant.

Phase 5 cluster 1 §14 closures (lien lifecycle):

  #19 insurance_backed_lien_consume_release_impair_conserves_canonical_ledger
  #30 insurance_backed_lien_create_consume_release_impair_conserves_canonical_ledger
      Closed (single-lien half) by `LienLifecycle.lean::impair_conserves_totalFace`
      and `consume_totalFace_decrement`. Aggregate-level conservation
      (across multiple liens) is a sum of per-lien instances.
  #21 impaired_insurance_lien_remains_reserved_and_unavailable_until_reconciled
  #31 insurance_impaired_lien_remains_encumbered_until_release_or_consume
      Closed by `impair_preserves_backing` and `impair_grows_impaired`:
      `backingReservedNum` is unchanged by impair (the lien stays
      encumbered) and `impairedFaceClaimNum` strictly grows.
  #32 lien_creation_increments_correct_aggregate_for_backing_source
      Closed by `create_targets_named_source_only` + `_insurance_leaves_counterparty`
      (structural type-level witness) and `create_faceClaim_increments` +
      `create_backing_increments` (arithmetic witness).
  #37 lien_consumption_decrements_bucket_valid_liened_and_source_valid_liened_once
      Closed by `consume_faceClaim_decrements` and `consume_backing_decrements`
      — the "once per side" property follows from each being a `Lien src`
      field, with `src` fixed at the call site.
  #39 lien_release_moves_valid_liened_to_fresh_unliened_without_changing_fresh_reserved
      Closed by `release_eq_consume` + `release_does_not_impair`: the
      per-lien field updates match consume; the impaired bucket is
      untouched (the released face truly leaves the system rather than
      being marked impaired).

Phase 5 cluster 2 §14 closures (token-value-flow soundness):

  #4  source_credit_lien_creation_moves_no_quote_value
      Closed by `ValueFlowSoundness.lean::lienCreateFlow_no_value`:
      `lienCreateFlow` is `TokenValueFlow.empty` — zero rows, zero
      debits, zero credits.
  #25 token_value_flow_proof_balances_internal_insurance_transfers
      Closed by `internalTransferFlow_balanced` + specialized
      `insuranceToCloseSpentFlow_balanced`: total_debit = total_credit,
      both external-quote counters zero, vault unchanged.
  #26 internal_insurance_transfer_requires_exactly_one_credit_entry
      Closed by `TokenValueRow.creditFor_own_class` /
      `creditFor_other_class`: each row's `creditFor` is `amount` for
      `r.creditClass` and `0` for every other class — structural by row
      typing.
  #27 recovery_consumed_insurance_lien_decrements_v_on_external_payout
      Closed by `recoveryInsurancePayoutFlow_vault_decrements` +
      `_shape` + `_balanced`: vault decreases by exactly the payout
      amount, the row debits InsuranceCapital and credits ExternalQuote,
      and the flow is structurally balanced.

Final batch §14 closures (MEDIUM/LOW rows):

  #11 backing_reservation_is_actual_locked_equity_not_optimistic_certificate
      Closed by `ActualBacking.lean::AccountCapital.lockEquity` plus
      `lockEquity_conservation` (post-capital + lien.backing =
      pre-capital exactly), `lockEquity_lien_backing_eq_amount`,
      `lockEquity_decreases_capital`, and
      `positive_lien_implies_capital_decrement`. A positive-backed
      lien provably corresponds to a capital decrement of the same
      amount — no "optimistic certificate" path can produce backing
      without consuming equity. *(Supersedes the prior tautological
      `Spec14.lean::Lien.backingReservedNum_is_actual_amount`
      — see AUDIT_2026-05-22.md.)*
  #16 source_credit_insurance_reservation_single_canonical_writer
      Closed by `Spec14.lean::InsuranceLedger.transitions_are_only_writers`:
      the three lifecycle helpers are the only paths that produce a
      valid `InsuranceLedger` with the conservation proof.
      Strengthened by
      `SingleWriterInsurance.lean::InsuranceLedger.InsuranceWrite`,
      a closed sum with exactly three constructors (Reserve /
      Release / Consume), plus `applyWrite` as the typed single
      entry point. `tag_is_one_of_three` is the closed-world
      witness — every `InsuranceWrite` value provably maps to one
      of the three named writers. The routing-equivalence theorems
      `applyWrite_Reserve` / `_Release` / `_Consume` show
      `applyWrite` is *definitionally* the named transition (no
      hidden path). `applyWrite_some_iff_named_transition` proves
      every successful call factors through one of the three.
      `applyWrite_preserves_initialDeposited` and
      `applyWrite_preserves_globalProtocolStaged` use the
      closed-sum exhaustiveness to prove that no constructor can
      mutate these anchor fields — "no other writer" is now
      structural at the typed entry point. *(Strengthened from
      "the three conserve" to "the three are the only writers" —
      see AUDIT_2026-05-22.md.)*
  #20 insurance_backed_lien_consumption_decrements_source_credit_reservation_and_total_available_once
      Strengthened by `InsuranceLedger.lean::InsuranceLedger.consumeWithSpendAtoms`
      and its `consumeWithSpendAtoms_atomic` /
      `_spend_correct` theorems. The `spendAtomsFor` helper exposes
      the spec's BOUND-unit ↔ vault-atom conversion
      (`amount_from_bound_num_up`) that was collapsed in the prior
      closure. The total-available decrement in vault atoms is now
      explicit: `amount ≤ spendAtoms * BOUND_SCALE`, conservative
      per `BoundArith.amountFromBoundNum_rounds_up`. The
      `Spec14.lean` direct re-citation remains for the BOUND-only
      half. *(Strengthened to add the spec's two-scale distinction —
      see AUDIT_2026-05-22.md.)*
  #33 lien_creatable_predicate_matches_actual_bucket_or_insurance_lifecycle
      Closed by `Spec14.lean::BackingBucket.lien_creatable_matches_lifecycle`
      and `InsuranceReservation.lien_creatable_matches_lifecycle`,
      re-citing the cluster 5 iff theorems.
  #38 lien_consumption_removes_backing_from_fresh_reserved_and_claim_bound
      Closed by `LienLifecycle.lean::lien_consumption_removes_fresh_reserved_and_claim_bound`:
      the joint theorem witnesses both halves —
      `b'.validLiened + amount = b.validLiened` (fresh-reserved
      side) and `l'.faceClaimLockedNum + face = l.faceClaimLockedNum`
      (claim-bound side). The supporting
      `BackingBucket.consumeLien_decreases_fresh_reserved_total`
      explicitly handles the bucket's `freshUnliened + validLiened`
      sum. *(Strengthened from
      `Spec14.lean::BackingBucket.consumeLien_removes_from_validLiened`
      which only proved the bucket side — see AUDIT_2026-05-22.md.)*
  #51 no_circular_credit_without_external_senior_backing
      Closed by `Spec14.lean::TradeStep.no_circular_credit_without_backing`
      and `risk_increasing_consumes_backing` — by typing, a risk-
      increasing trade cannot fire without consuming positive
      backing. Strengthened by
      `CreditAcyclicity.lean::CreditChain`, an *indexed* inductive
      whose index is the list of accounts in the chain. Two
      constructors: `external` anchors a chain at an
      `ExternalBacking` (with `positive : 0 < amount`); `extend`
      prepends a new account with a `notIn : ¬ a ∈ prev` proof
      field. The proof field rules out A → B → ... → A cycles at
      the type level — no `CreditChain` whose index has a
      duplicate can be constructed. `accounts_nodup` is the
      Nodup witness; `anchor_positive` proves every chain
      bottoms out at a strictly-positive external source;
      `extend_preserves_anchor` shows the senior backing is
      stable across extensions. *(Strengthened from "requires
      backing at each step" to "no cycle is representable" —
      see AUDIT_2026-05-22.md.)*
  #52 soft_maintenance_credit_does_not_create_payout_or_residual_cure
      Closed by `NoPayoutCredit.lean::AccountCapital.attemptPayout`
      — the engine-action binding the audit asked for. Theorems:
      `attemptPayout_none_when_only_soft_credit` (lien-backed = 0
      → no payout), `attemptPayout_some_implies_lien_backed`
      (successful payout proves lien-backed > 0), and
      `attemptPayout_capital_decrement` (capital decrement bounded
      by lien-backed, never by softCreditAmount). Plus the prior
      `NoPayoutCredit.lean::PayoutFromCredit` structural invariant
      bounding payoutAmount ≤ lienBackedAmount. *(Strengthened with
      an engine action so the bound has observable consequences —
      see AUDIT_2026-05-22.md.)*
  #56 residuals_charged_only_to_asset_opposing_side_domain
      Closed by `OpposingDomain.lean::CloseLedger.openFromLoss` plus
      `openFromLoss_targets_opposing_side` (domainSide = originSide.flip),
      `openFromLoss_long_targets_short` / `_short_targets_long` (the
      two concrete directions), `openFromLoss_domain_distinct_from_origin`
      (provably *not* the originating side), and
      `openFromLoss_same_asset` (no unrelated-asset booking). The
      cluster 4 anchor-preservation theorems guarantee these
      properties survive every booking transition. *(Supersedes the
      prior trivial `Spec14.lean::CloseLedger.residual_books_to_single_domain`
      — see AUDIT_2026-05-22.md.)*
  #76 zero_weight_domain_residual_cannot_clear_without_backing
      Closed by `ZeroWeightClear.lean::ZeroWeightClearance` (closed
      sum: only `insurance` and `explicitBacked` constructors)
      plus `ZeroWeightClear.lean::CloseLedger.bookSupportInWeightedContext`,
      which wraps `bookSupport` with a `0 < W` proof argument. Under
      zero weight (W = 0), no such proof exists, so the bookSupport
      path is structurally inaccessible —
      `bookSupport_zero_weight_inaccessible` is the explicit
      witness. `bBookingStep_undefined_at_zero_weight` rules out
      the B-booking shortcut symmetrically. *(Strengthened to close
      the bookSupport bypass — see AUDIT_2026-05-22.md.)*
  #77 uncollectible_fees_forgiven_not_socialized
      Closed by `NoPayoutCredit.lean::FeeResolution` plus the
      contrast pair: `applyForgiveness` (the spec-mandated path)
      preserves every StockClasses field including `insurance` and
      `totalV`, while the counterfactual `socializeIntoInsurance`
      strictly grows both. The distinguishability theorem
      `forgive_distinct_from_socialize` proves the two functions
      produce different outputs whenever the uncollectible portion
      is positive — `applyForgiveness` is therefore a *real* choice
      with observable consequences, not a no-op stub. *(Strengthened
      from the prior identity-only model — see AUDIT_2026-05-22.md.)*
  #84 dead_leg_forfeit_books_to_bankruptcy_domain
      Closed by `OpposingDomain.lean::CloseLedger.deadLegForfeit_books_to_opposing_side`:
      a close ledger opened via `openFromLoss` on a dead-leg
      origin carries `domainSide ≠ originSide` and the same
      `assetIndex` — i.e., residuals land in the bankruptcy
      domain (opposing side of the same asset). The cluster 4
      anchor-preservation theorems carry this through every
      subsequent booking transition. *(Supersedes the prior weaker
      `Spec14.lean::CloseLedger.bookB_targets_named_domain`
      / `_bookExplicit_targets_named_domain`, which only proved
      preservation of the anchor not its semantic correctness —
      see AUDIT_2026-05-22.md.)*
  #86 global_accumulator_not_account_health_proof
      Closed by `Spec14.lean::AccountHealthWitness.requires_in_instance_proof`,
      re-citing the §14 #58 closure: a health witness can only be
      constructed from a `HealthProof`, not a `UIAggregate`.
      Strengthened by `MultiInstanceAggregation.lean::GlobalAccumulator`,
      which gives the "global accumulator" explicit multi-instance
      content (`instances` list, `totalNotional` Nat) distinct
      from a per-account proof. `fromSnapshots_instances` and
      `fromSnapshots_totalNotional` are the structural-content
      witnesses. `MultiInstanceView.builtFrom` is the proof field
      tying the aggregator to the snapshots it summed over. *(Strengthened
      from re-cite to a typed object with multi-instance content —
      see AUDIT_2026-05-22.md.)*
  #88 N_too_large_rejects_public_initialization_or_activation
      Closed by `Activation.lean::Activate.rejects_when_N_too_large`,
      which composes `ActivationEnvelope.portfolioOKFromN_false_when_too_large`
      (N > MAX_PORTFOLIO_ASSETS_N → portfolioOK = false) with the
      `Activation.lean::Activate.rejects_when_portfolio_envelope_fails`
      rejection witness. The link between the candidate `N` and the
      envelope flag is now explicit, not abstract. *(Strengthened
      from the abstract-flag closure — see AUDIT_2026-05-22.md.)*
  #90 equity_side_penalties_disjoint_from_requirement_side_penalties
      Closed by `HealthTest.lean::PenaltySource` (a closed
      sum of four named sources, each tagged with `category` mapping
      to `equity` or `requirement`). The disjointness witnesses are
      `category_total` (every source has *exactly one* category),
      `category_unique` (no source has two), and
      `equity_distinct_from_requirement` (the categories themselves
      are distinct). `negativeEquity_eq_sum_by_category`
      decomposes the formula by category — equity-side contributions
      and the requirement contribution sum separately without
      overlap. *(Strengthened from field-level disjointness to
      source-level categorization — see AUDIT_2026-05-22.md.)*
  #91 hedge_credit_reduced_requirement_covers_combined_loss_envelope
      Closed by `HedgeEnvelope.lean::HedgeBucket.hedgeCredit_le_envelope`
      (credit bounded by envelope cap) plus
      `hedgeCredit_le_hedgedSize` (bounded by min-leg). The
      `reducedRequirement_above_envelope` lemma shows the
      reduction respects the combined-loss envelope.

Heavy overclaim hardening §14 closures:

  #8  risk_increasing_trade_requires_source_credit_lien
      Closed by `RiskIncreasingTrade.lean::TradeStep`: the
      `riskIncreasing` and `riskIncreasingInsurance` constructors
      require a typed `Lien` plus a structural proof that the
      lien's `backingReservedNum` is positive. There is no fourth
      constructor for "risk-increasing without lien", and
      `zero_consumed_implies_riskDecreasing` proves that any step
      consuming zero backing must be the riskDecreasing constructor.
  #10 source_credit_lien_impairment_forces_deleverage_liquidation_or_recovery
      Closed by `ImpairmentRouting.lean`. `normalStep` returns `none`
      whenever the account has an unresolved impaired lien
      (`normalStep_blocked_when_impaired`); only `routeDeleverage`,
      `routeLiquidation`, or `routeRecovery` can clear the flag
      (each `_clears_impaired` / `_records_resolution` /
      `_requires_impaired`). The `resolution_is_one_of_three`
      closed-world lemma confirms there is no fourth resolution
      path. Strengthened by
      `ImpairmentRouting.lean::AccountWithLiens.WithProgress`,
      which pairs the account with a progress-counter monoid. Routes
      strictly advance the counter by 1
      (`route*_progress_advances`); `normalStep` is the identity on
      it (`normalStep_progress_unchanged`); under impairment,
      `normalStep` is blocked
      (`normalStep_blocked_under_impairment`). The closed-world
      `strict_progress_from_impairment_implies_route` shows any
      progress from an impaired-unresolved state must come from one
      of the three named routes. *(Strengthened from
      "blocks normal step" to a positive "forces progress only via
      routes" — see AUDIT_2026-05-22.md.)*
  #53 settlement_quality_credit_consumes_backing_and_locks_face_claim
      Closed by `KFSettlement.lean::kfSettlementStep_atomic`: a
      successful K/F settlement returns a state with backing
      decremented and face claim locked by the same amount in one
      atomic call. The `_preserves_total` lemma is the conservation
      witness; `_fails_closed_underBacked` is the negative form.
  #55 backing_consumption_reduces_loser_capital_and_preserves_senior_invariants
      Closed by `BackingConsumption.lean` (3-class vault model) plus
      `BackingConsumption.lean::VaultSnapshot.embed` lifting to
      the full 10-class StockClasses. The senior invariant
      `vault = loserCapital + winnerCapital + bookedLoss` is
      preserved by `consumeBacking`
      (`consumeBacking_preserves_seniorInvariant`); the embedding
      preserves `totalV` (`embed_totalV_eq_vault`) and
      reconciliation (`embed_reconciled`). The composite
      `consumeBacking_embed_preserves_reconciled` lifts the
      transition's 3-class proof to a 10-class statement.
      *(Strengthened with the StockClasses embedding the audit
      asked for — see AUDIT_2026-05-22.md.)*
  #89 pending_obligation_exposure_counted_exactly_once_in_health_test
      Closed by `HealthTest.lean::equity_decreases_by_pending_increment`:
      raising `pendingObligationExposure` by `d` reduces equity by
      exactly `d`, not `2d`. `positiveEquity_independent_of_pending`
      shows the term appears only on the negative side, and
      `double_counted_strict_increase` is the explicit witness that
      double-counting strictly inflates negative equity beyond the
      spec formula.

Operational overclaim hardening §14 closures:

  #7  source_credit_rate_zero_when_backing_stale_or_exhausted
      Closed by `LiveBacking.lean::creditRate_zero_when_no_fresh`:
      when every backing bucket has status ≠ Fresh (i.e. all are
      Empty/Expired/Impaired, covering "stale" and "exhausted"),
      sumLiveAvailable is zero, and the Phase 1
      `creditRateNum_zero_backing` lemma forces the resulting rate
      to zero for any positive claim.
      `creditRate_zero_when_single_stale` is the convenience
      one-bucket form.
  #41 expired_liened_bucket_marks_liens_impaired_in_bounded_work
      Closed by `LiveBacking.lean::expireAndImpairAll`: the single
      transition flips the bucket status from Fresh to Impaired,
      drains validLiened into impairedLiened
      (`expireAndImpairAll_clears_validLiened` /
      `_grows_impaired`), and preserves totalBacking
      (`_preserves_totalBacking`). The "bounded work" claim is
      structural: this is one function call, not a loop. The bridge
      to #7 is `expireAndImpairAll_excluded_from_live`: the
      post-transition bucket is no longer counted in
      `sumLiveAvailable`. Strengthened by
      `PerLienImpairment.lean`, which adds a `BucketLien` per-lien
      record (id, amount, status). `expireLiens` flips every Valid
      lien to Impaired; `expireLiens_all_impaired` is the per-lien
      witness that no Valid lien survives. The aggregate-bridge
      theorems `expireLiens_valid_sum_zero` and
      `expireLiens_impaired_sum_eq` connect the per-lien transition
      to the bucket-aggregate counts: `validSum` drops to 0;
      `impairedSum` gains the prior `validSum`.
      `BucketWithLiens.expireWithLiens` is the lifted pair
      transition; `_preserves_consistency` proves the per-lien
      sums and bucket aggregates remain coherent;
      `_all_liens_impaired` lifts the per-lien witness to the
      paired state. *(Strengthened from bucket-aggregate-only to
      per-lien status updates that the audit asked for — see
      AUDIT_2026-05-22.md.)*
  #44 locked_face_claim_excluded_from_soft_credit
      Closed by `SoftCredit.lean::softCredit_plus_locked_eq_face`:
      under a well-formed lock (`lockedFaceClaim ≤ faceClaim`), the
      sum of soft-credit and locked-face-claim equals faceClaim
      exactly. No double-counting is possible. Boundedness and
      anti-monotonicity (`softCredit_le_faceClaim`,
      `softCredit_anti_in_locked`) give the supporting
      structure. Even in the degenerate over-lock case,
      `softCredit_plus_locked_bounded` holds.
  #74 domain_lock_does_not_block_asset_wide_kf_accrual
      Closed by `DomainLock.lean::kfAccrue_ignores_domain_lock`:
      `kfAccrueAssetWide` literally does not take a `DomainLock`
      as input, so its result is provably independent of the lock
      state. `kfAccrue_with_full_lock` is the explicit witness for
      the maximally-locked case. The contrast lemma
      `sideStep_blocked_when_locked` shows side-specific ops *are*
      gated — so this is not a trivial "function never reads input"
      claim but a deliberate signature design.
  #83 dead_leg_forfeit_uses_bounded_fallback_or_zero_positive_payout
      Closed by `DeadLegForfeit.lean::DeadLegOutcome` (a closed
      sum with two constructors: `zeroPositive` and
      `boundedFallback input accepted`, the second carrying the
      `FallbackPriceInput.accepted` proof). Every value of the
      type falls into one of these two safe categories;
      `no_unverified_constructor` is the explicit witness. The
      payout safety is in `positivePayout_zero` (every constructor
      reports zero positive payout) and
      `boundedFallback_envelope_holds` (the carried envelope
      proof relays §14 #80 / #81 / #82).

Overclaim hardening §14 closures:

  #9  source_credit_lien_prevents_double_use_of_same_claim_and_backing
      Closed by `Spec14.lean::Lien.consume_prevents_double_use`
      (consume strictly decrements `backingReservedNum` by the
      consumed amount) and `consume_remaining_backing` (explicit
      post-consume remainder = pre − amount). A second consume of
      the same `amount` requires `backingReservedNum ≥ amount` again,
      which only holds if the original was `≥ 2 · amount`. The
      symmetric face-claim version is
      `consume_face_prevents_double_use`.
  #18 insurance_backed_lien_creation_increments_valid_liened_insurance_not_counterparty_backing
      Closed by
      `Spec14.lean::SourceCreditLienAggregate.create_insurance_increments_insurance_only`
      (insurance face-claim += face, counterparty unchanged) plus
      `create_insurance_backing_increments_insurance_only` (insurance
      backing += backing, counterparty backing unchanged). Both ride
      on the cluster 1 type-typed `Lien BackingSource.Insurance`.
  #24 close_residual_partition_classifies_counterparty_and_insurance_lien_consumption_disjointly
      Closed by `CloseLedger.lean::CloseLedger.consumeLienForResidual`
      (typed routing on `BackingSource`: counterparty →
      bookSupport, insurance → bookInsurance) plus
      `consumeLienForResidual_counterparty_touches_support_only` /
      `_insurance_touches_insurance_only` (per-side cross-category
      preservation) and `consumeLienForResidual_targets_one_category`
      (closed-world `BackingSource` enum: every typed lien hits
      exactly one branch). The
      `Spec14.lean::CloseLedger.bookSupport_does_not_touch_insuranceSpent`
      family handles the field-level direction. *(Strengthened from
      field-level to per-lien typed disjointness — see
      AUDIT_2026-05-22.md.)*
  #28 lien_creatable_predicate_requires_actual_bucket_or_insurance_reservation_capacity
      Closed by `Spec14.lean::BackingBucket.lienCreatable_implies_capacity`
      and `InsuranceReservation.lienCreatable_implies_capacity`.
      These are the "predicate ⇒ capacity" direction of the cluster
      5 iff theorems, named to match §14 #28's invariant.
  #43 lien_creation_requires_required_backing_le_available_backing
      Closed by
      `Spec14.lean::BackingBucket.lienAgainst_requires_amount_le_available`
      and `InsuranceReservation.lien_requires_capacity`. Extracts
      the precondition of the lifecycle helpers as an explicit named
      theorem.
  #64 pending_obligation_credit_decrements_origin_residual_once
      Closed by
      `Spec14.lean::CloseLedger.pendingObligation_credit_decrements_origin_residual_once`
      (the residual half of the atomic credit-debit pair) combined
      with `bookSupport_no_pendingObligation_credit` and
      `bookInsurance_no_pendingObligation_credit` showing no
      sibling transition adds to the credit counter. Each credit is
      therefore paired with exactly one residual decrement.

Phase 5 cluster 6 §14 closures (conservation and reconciliation):

  #5  stock_reconciliation_holds_at_genesis_activation_mode_transition_and_recovery
      Closed by `StockReconciliation.lean::reconciled` predicate
      (V = totalV) and `empty_reconciled` (genesis case). The
      reconciliation check is decidable at any state; downstream
      transitions just need to preserve the equality.
  #13 insurance_credit_reservation_globally_conserved
      Closed by `InsuranceLedger.lean::conservation_holds` plus the
      `*_preserves_conservation` triple for reserve/release/consume,
      together with `applySeq_preserves_conservation` for arbitrary
      transition sequences. The structural `conservation` field on
      the `InsuranceLedger` record carries the proof through every
      transition by construction.
  #14 insurance_spend_not_double_counted_as_live_encumbrance
      Closed by `InsuranceLedger.lean::consume_atomic_decrement_and_spend`
      (consume reduces reservation by the same amount it adds to
      spent in one atomic step) plus `release_preserves_domainSpent`
      and `reserve_preserves_domainSpent` (the other transitions
      never touch the spend counter). The same atom cannot be both
      live-reserved and spent.
  #75 B_booking_exact_remainder_conservation
      Closed by `BBookingExact.lean::bBookingStep_exact_conservation`
      (delta_B * W + new_R = chunk * SOCIAL_LOSS_DEN + R) and
      `bBookingStep_remainder_lt_W` (new_R < W).
      `bBookingRec_conservation` lifts the per-step identity to an
      arbitrary chunk sequence: total booked + final remainder =
      initial remainder + sum of scaled chunks. No social-loss atom
      is silently created or destroyed across any number of chunks.
  #95 settlement_rounding_residue_credits_unallocated_surplus_and_flow_proof_balances
      Closed by `StockReconciliation.lean::RoundingSplit` with the
      `conservative : allocations.sum ≤ exactAmount` proof field and
      the `flow_balances` theorem (residue + allocations.sum =
      exactAmount). The `ResidueSink` choice (settlementRoundingResidue
      vs unallocatedProtocolSurplus) plus `applyResidue` route the
      residue into one of the two protocol-owned classes.
  #96 rounding_residue_never_used_for_health_backing_insurance_or_payout
      Closed by `StockReconciliation.lean::HealthBackingPayoutWitness`:
      the `fromUserClaim` constructor requires a role proof
      `h : role = .userClaim`. The residue and surplus classes are
      tagged `.protocolOwned`, and `residue_role_not_userClaim` /
      `surplus_role_not_userClaim` prove these tags are not equal —
      so no `HealthBackingPayoutWitness` value can be constructed
      from a residue or surplus amount. The §14 #96 exception (an
      explicit balanced transition) is modeled by the
      `ExplicitResidueTransfer` structure.
  #97 stock_reconciliation_includes_settlement_rounding_residue_total
      Closed by `StockReconciliation.lean::reconciled_includes_residue`
      (residue ≤ V whenever the partition reconciles) plus
      `residue_from_V` (explicit decomposition with the residue
      called out). `settlementRoundingResidue` is one of the 10
      classes summed by `totalV`.
  #98 funded_close_drift_reserve_maps_to_one_stock_or_reservation_class
      Closed by `StockReconciliation.lean::DriftReserveMapping`: the
      `cls` field is a single `DriftReserveBackingClass` enum value,
      so a mapping cannot carry two classes. `single_class` is the
      explicit ∃! witness. `tokenStockContribution` returns the
      mapping amount only for `.quoteEscrow`; the other four backing
      classes return zero token-stock contribution
      (`tokenStockContribution_nonQuote`), preventing double-counting
      between reservation/capacity ledgers and stock classes.
  #99 per_class_stock_reconciliation_matches_o1_ledgers_where_available
      Closed by `StockReconciliation.lean::matchesLedgers` predicate
      and the per-class projection lemmas
      (`matchesLedgers_insurance`, `_cancelDepositEscrow`,
      `_roundingResidue`). `empty_matchesLedgers` covers the genesis
      case.

Phase 5 cluster 4 §14 closures (close progress and priority):

  #46 close_drift_reserve_has_backed_loss_capacity_or_recovers
      Closed by `CloseLedger.lean::CloseLedger.continueOrRecover`
      — a typed continuation outcome (`continued` or
      `routedToRecovery`, no third path) bound to the
      `closeDriftReserveBacked` predicate. Theorems:
      `continueOrRecover_continued_implies_backed` (continuation
      requires backing), `_unbacked_routes_recovery` (unbacked
      routes), `_dichotomy` (closed-world). The predicate +
      decision plumbing remain in `CloseLedger.lean`. *(Strengthened
      from "predicate + abstract decision" to gated transition that
      structurally types the dichotomy — see AUDIT_2026-05-22.md.)*
  #47 pulled_forward_obligation_credit_not_socialized_again
      Closed by `CloseLedger.lean::bookPendingObligation_credit_matches_debit`
      (atomic debit-equals-credit) plus the
      `bookX_does_not_touch_pendingObligation` family showing no
      other transition path increments the credit counter. The same
      credit cannot be added twice because exactly one transition
      touches the field.
  #66 participant_finalization_pulls_forward_pending_obligation
      Closed by `CloseLedger.lean::bookPendingObligation_only_credit_path`
      (the only path that credits pending obligations) together with
      the `does_not_touch_pendingObligation` family for `bookSupport`,
      `bookInsurance`, `bookB`, `bookExplicit`, and `addDrift`.
      Pending obligations must be pulled forward through the dedicated
      transition — there is no shortcut.
  #67 phantom_weight_without_backing_reverts
      Closed by `CloseLedger.lean::WeightAttribution`. The structure
      requires `0 < backing` as a typed field; any expression that
      tries to construct an attribution with `backing = 0` fails to
      typecheck (`weight_attribution_has_positive_backing` is the
      explicit witness).
  #69 preempted_close_restart_cannot_double_book_residual
      Closed by `CloseLedger.lean::bookSupport_monotone_supportConsumed`
      and siblings for `insuranceSpent`, `bLossBooked`,
      `explicitLossAssigned`. Booking counters are monotonically
      non-decreasing across all transitions; restart cannot reset
      them to zero, so prior bookings cannot be silently repeated.
  #70 close_id_and_drift_anchors_immutable
      Closed by `CloseLedger.lean::anchorsEq` plus the
      `_preserves_anchors` theorems for every transition
      (bookSupport, bookInsurance, bookB, bookExplicit,
      bookPendingObligation, addDrift, applyQuantityAdl, finalize,
      cureAndCancel). The 7-field anchor block — closeId, assetIndex,
      marketId, domainSide, grossLossAtCloseStart,
      driftReferenceSlot, maxCloseSlot — is preserved by every
      lifecycle step.
  #71 bankrupt_close_progress_decreases_net_of_close_drift
      Closed by `CloseLedger.lean::CloseLedger.applyMoves_residual_conservation`
      (aggregate identity: `l'.residual + totalBookings = l.residual
      + totalDrift` across an arbitrary sequence) plus
      `applyMoves_residual_decreases_when_bookings_dominate` (net
      non-strict decrease when bookings ≥ drift) and
      `applyMoves_residual_strictly_decreases` (strict decrease when
      bookings strictly exceed drift). The per-step
      `CloseLedger.lean::bookSupport_decreases_residual` family is
      the building block. *(Strengthened from per-step to aggregate
      sequence — see AUDIT_2026-05-22.md.)*
  #72 cure_and_cancel_checks_before_consuming_new_deposit
      Closed by `CloseLedger.lean::cureAndCancel_requires_no_irreversible`
      (cure-and-cancel demands `hasIrreversibleProgress = false`)
      together with `bookSupport_sets_irreversible` (a successful
      positive booking sets `hasIrreversibleProgress = true`). After
      any booking, cancel is denied; new deposits cannot be consumed
      as support before the cancel check.
  #73 quantity_adl_and_account_finalization_atomic_or_barriered
      Closed by `CloseLedger.lean::finalize_requires_adlApplied`
      (finalize requires `adlApplied = true`) and
      `finalize_requires_zero_residual` (finalize requires residual
      booked to zero). ADL is its own one-shot transition
      (`applyQuantityAdl`) that flips the flag; finalize cannot fire
      before ADL has applied.
  #68 preemptive_close_priority_prevents_hold_and_wait_deadlock
      Closed by `ClosePriority.lean::no_two_cycle` and
      `no_three_cycle`, derived from `lt_asymm` and `lt_trans`. A
      strict total order has no cycles; no two closes can hold and
      wait on each other.
  #92 cross_close_priority_is_strict_total_order
      Closed by `ClosePriority.lean::lt_irrefl` + `lt_asymm` +
      `lt_trans` + `lt_trichotomy`. The priority comparator is a
      strict total order: irreflexive, asymmetric, transitive, and
      every pair of priorities is comparable (or equal as tuples).
  #93 equal_priority_livelock_impossible
      Closed by `ClosePriority.lean::distinct_closeId_strictly_comparable`:
      two closes with distinct `closeId` always have comparable
      priority (one strictly precedes the other). Combined with the
      spec rule that distinct closes have distinct closeIds,
      equal-priority livelock is impossible by construction.

Phase 5 cluster 5 §14 closures (recovery + activation):

  #29 lien_creatable_matches_actual_bucket_and_insurance_lifecycle_helpers
      Closed by `Activation.lean::InsuranceReservation.lien_isSome_iff_lienCreatable`
      and `BackingBucket.lienAgainst_isSome_iff_lienCreatable`: the
      "is a new lien creatable?" predicate is exactly the precondition
      under which the per-source lifecycle helper succeeds.
  #58 cross_instance_ui_aggregation_not_health_or_collateral_proof
      Closed by `Activation.lean::AccountHealthWitness`: a witness of
      account health can only be constructed from a `HealthProof` (the
      in-instance proof type). `UIAggregate` is a separate, distinct
      type with no path into `AccountHealthWitness`. The §14 #58
      structural distinction is closed at the type level — analogous to
      the §14 #87 closure pattern. Strengthened by
      `MultiInstanceAggregation.lean`, which adds the concrete
      multi-instance state the audit asked for: `InstanceSnapshot`
      is the per-instance projection (instId, accountId, notional,
      in-instance `healthProof`); `GlobalAccumulator.fromSnapshots`
      sums across instances and *discards* per-account
      `healthProof`s by design. The
      `no_canonical_extractor_from_accumulator` theorem proves that
      no total function `GlobalAccumulator → HealthProof` can
      exist: two snapshots with distinct accountIds can produce
      identical accumulators (`aggregator_collapses_distinct_accounts`),
      so any extractor would have to equal two distinct
      HealthProofs simultaneously — a contradiction.
      *(Strengthened from abstract type-distinction to concrete
      multi-instance state — see AUDIT_2026-05-22.md.)*
  #59 mutable_asset_activation_requires_full_envelope_proofs
      Closed by `Activation.lean::Activate.requires_full_envelope` plus
      the per-component witnesses `requires_priceOK` and
      `requires_recoveryFallbackOK`. The `ActivationEnvelope` record
      tags every envelope check (fee, price, funding, margin, OI,
      B-headroom, source-credit, close-progress, portfolio, recovery
      fallback); `Activate` cannot fire without `env.allValid = true`.
      Strengthened by
      `Activation.lean::ActivationEnvelope.fromWitness`: each
      flag is now derived from a concrete numerical `Witness` record
      (fee paid/required, price age, funding accrued/due, margin
      actual/required, OI cap, B-headroom, source-credit cap, close
      progress, portfolio width, recovery backoff). The per-envelope
      `fromWitness_*_false_when_*` lemmas show each flag is `false`
      exactly when the underlying inequality is violated; the
      `fromWitness_allValid_implies_*` lemmas decode `allValid` back
      into the witness predicates. *(Strengthened from the abstract-
      Bool closure that the audit flagged — see AUDIT_2026-05-22.md.)*
  #60 asset_cannot_activate_with_nonzero_or_unreconciled_state
      Closed by `Activation.lean::Activate.requires_zero_state` plus
      per-field corollaries (`requires_zero_legCount` /
      `_lienCount` / `_pendingObligationCount` /
      `_activeCloseCount` / `_backingHeldNum` /
      `_insuranceReservedNum`). The `Activate` constructor refuses to
      step from a non-`isReconciledZero` state. Strengthened by
      `Activation.lean::AssetSlotState.Reconciled`, which
      pairs the slot with an independent `reconciliation` flag.
      `Reconciled.fullyReconciled` requires *both* the zero counts
      and the flag; `ActivateFull` is the activation transition over
      the paired state. The counterfactual `unreconciledZero` (zero
      counts, `reconciled = false`) is provably rejected
      (`ActivateFull.unreconciled_zero_rejects_activation`), and
      `reconciledEmpty` is the dual accepting witness. *(Strengthened
      from a zero-only check to the "unreconciled-but-zero"
      distinction the audit flagged — see AUDIT_2026-05-22.md.)*
  #61 activation_invalidates_or_scopes_certs_fail_closed
      Closed by `Activation.lean::activation_invalidates_priorEpoch_cert`
      and `activation_postCert_implies_bumped_epoch`. Certs are scoped
      to `(slot, epoch)`. Activation bumps the slot's epoch by 1
      (`Activate.bumps_epoch`); a pre-activation cert can no longer
      validate, and a post-activation cert must have been bound to the
      bumped epoch.

Phase 5 cluster 5 §14 closures (recovery fallback envelope):

  #80 recovery_fallback_price_within_configured_deviation_envelope
      Closed by `RecoveryFallback.lean::envelopeValid` plus
      `envelopeValid_iff` (explicit-form witness),
      `envelopeValid_self` (zero-deviation boundary),
      `envelopeValid_zeroBps_iff_eq` (zero-cap forces price equality),
      `envelopeValid_mono_in_devBps` (a looser cap accepts strictly
      more prices). The predicate is exactly
      `abs(P_fb - P_ref) * 10000 ≤ devBps * P_ref` per `spec.md:213-215`.
  #81 recovery_fallback_value_transfer_bound_computed_per_account_and_domain
      Closed by `RecoveryFallback.lean::legTransferBound` (per-leg
      ceiling-div bound, mirroring `spec.md:222`) plus
      `accountTransferBound` (sum across legs) and the supporting
      lemmas `legTransferBound_zero_posQ`,
      `legTransferBound_zero_deviation`,
      `legTransferBound_mono_in_posQ`,
      `accountTransferBound_nil`, `accountTransferBound_cons`,
      `accountTransferBound_zero_deviation`,
      `accountTransferBound_le_cons` (monotone in leg list). The
      per-account bound is the structural sum the engine MUST compute
      per `spec.md:218-225`.
  #82 fallback_recovery_rejects_unverified_or_out_of_envelope_reference_price
      Closed by `RecoveryFallback.lean::unverified_rejected`
      (unverified reference always rejected),
      `outOfEnvelope_rejected` (out-of-envelope always rejected), and
      `conditionalPayout_zero_when_rejected` (rejection forces zero
      positive payout). Acceptance is the conjunction of verification
      and envelope-validity; failing either yields no positive junior
      value.

Phase 5 cluster 3 §14 closures (backing bucket lifecycle):

  #34 backing_bucket_expiry_does_not_underflow_available_backing
      Closed by `BackingBucket.lean::expire_preserves_available`: the
      `expire` transition is status-only, so `freshUnliened` (which is
      `available`) is unchanged.
  #35 backing_bucket_expiry_does_not_increase_available_backing_or_credit_rate
      Closed by `expire_does_not_increase_available` (and the stronger
      `expire_preserves_amounts`). Since `expire` leaves all four amount
      partitions equal to their pre-transition values, neither the
      bucket's available nor any downstream rate can increase.
  #36 backing_bucket_expiry_after_partial_lien_consumption_does_not_inflate_available
      Closed by `available_after_lien_then_expire`: `lienAgainst`
      strictly decreases `available`, and the subsequent `expire`
      preserves it — so the post-expire available is `≤` pre-lien
      available, never inflated.
  #40 source_available_backing_recomputes_from_bucket_sums
      Closed by `sumAvailable_eq_sumFreshUnliened` +
      `sumAvailable_cons`: the source-level aggregate is structurally
      the sum of per-bucket `available` values. Transition-side
      witnesses (`expire_preserves_sumAvailable`,
      `lienAgainst_decreases_sumAvailable`) show the aggregate tracks
      per-bucket transitions correctly.

The two axes answer different questions. **Confidence** says whether a harness exists that
*claims* to prove the invariant. **Strength** says whether the harness is doing symbolic
verification (real bounded ∀), running a concrete fixture through Kani's machinery, or
backed by a Lean theorem proven over arbitrary Nat. HIGH+WEAK is the danger zone:
the spec invariant looks covered, but the coverage is only at hand-picked inputs.
## Per-invariant rows

### #1. `source_domain_positive_credit_capped_by_realizable_backing`
**Confidence:** HIGH
**Strength:** STRONG (formula half via Lean ∀ Nat; realizable-backing predicate remains operational)
**Lean theorems** (`Percolator/CreditRate.lean`) — proves the formula `min(available · SCALE / claim, SCALE)` is correctly capped:
- `creditRateNum_le_scale`, `creditRateNum_zero_backing`, `creditRateNum_full_backing`, `creditRateNum_mono_in_backing`.
**Note:** the "realizable backing" half of this invariant — that `available_backing_num_for_source_credit_state` correctly aggregates only realizable buckets — is operational, not arithmetic, and stays in Kani harnesses for now.
**Kani harnesses (concrete sanity):**
- `proof_v16_source_credit_rate_is_bounded_by_available_backing` `[SEMI]` — Rust impl at three backing regimes.
- `proof_v16_source_domain_realizable_support_zero_backing_gives_zero_credit` `[CON]` — zero-backing fixture.
- `proof_v16_source_domain_realizable_support_full_backing_gives_full_credit` `[CON]` — full-backing fixture.
- `proof_v16_source_domain_realizable_support_uses_source_credit_rate` `[CON]` — account-level equity scales by the rate.

### #2. `token_value_flow_proof_every_quote_atom_has_one_debit_and_one_credit`
**Confidence:** HIGH
**Strength:** STRONG
**Harnesses:**
- `proof_v16_deposit_and_withdraw_value_flow_preserves_vault_capital_totals` `[CON]` — deposit/withdraw token-value flow balances vault and c_tot.
- `proof_v16_loss_and_fee_value_flow_preserves_vault_and_senior_totals` `[SEMI]` — loss-and-fee paths conserve vault, c_tot, and insurance under the flow proof.
- `proof_v16_stock_reconciliation_decomposes_vault_without_aliasing` `[SYM]` — `vault = c_tot + insurance + residual` decomposition without double-counting.

### #3. `reservation_encumbrance_proof_excludes_non_value_labels_from_token_flow`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_source_lien_creation_has_valid_reservation_encumbrance_proof` `[CON]` — emits validated reservation encumbrance proof distinct from value flow.
- `proof_v16_counterparty_lien_consume_preserves_backing_encumbrance` + `proof_v16_counterparty_lien_impair_preserves_backing_encumbrance` `[SEMI]` — backing encumbrance moves on lien lifecycle without touching value totals.
- **Lean closure**: `ReservationEncumbrance.lean::ReservationEncumbranceProof`
  is a record carrying *only* reservation/backing counters (no
  `debits` / `credits` / `externalQuote*` fields). The structural
  distinction from `TokenValueFlow` is at the type level —
  `encumbrance_has_no_value_flow_content` witnesses the absence
  of value-flow content; `empty_encumbrance_corresponds_to_empty_flow`
  shows that an empty encumbrance state has no value to extract.
  `createCounterpartyLien` is the encumbrance-only transition
  whose codomain is `ReservationEncumbranceProof`, not
  `TokenValueFlow` — value-flow content is structurally absent
  from the lien-creation path. Closes §14 #3.

### #4. `source_credit_lien_creation_moves_no_quote_value`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_counterparty_lien_consume_preserves_backing_encumbrance` + `proof_v16_counterparty_lien_impair_preserves_backing_encumbrance` `[SEMI]` — lien create/consume/impair holds `vault` constant; only reservation counters move.
- `proof_v16_public_withdraw_locks_claim_and_backing_when_positive_credit_is_required` `[CON]` — lien creation via withdraw does not move quote.

### #5. `stock_reconciliation_holds_at_genesis_activation_mode_transition_and_recovery`
**Confidence:** MEDIUM
**Strength:** STRONG
**Harnesses:**
- `proof_v16_stock_reconciliation_decomposes_vault_without_aliasing` `[SYM]` — `vault = c_tot + insurance + residual` invariant.
- `proof_v16_asset_activation_requires_empty_slot_and_bumps_epochs` `[SEMI]` — activation preserves ledger shape.
- `proof_v16_terminal_recovery_reason_and_mode_are_immutable` `[SEMI]` — recovery mode transition immutability.
**Note:** The full envelope (genesis + activation + mode transition + recovery as a single proof) is not asserted in one harness; individual phases are covered separately.

### #6. `oracle_pump_credit_limited_by_opposing_reserved_backing`
**Confidence:** MEDIUM
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_source_credit_rate_is_bounded_by_available_backing` `[SEMI]` — credit is bounded by available backing irrespective of claim magnitude.
- `proof_v16_expired_fresh_backing_stale_cert_blocks_source_credit_conversion` `[CON]` — stale backing blocks oracle-driven credit growth.
**Note:** No harness directly stress-tests an oracle pump producing claim growth without matching backing, but the rate cap rules it out.
- **Lean closure**: `OraclePumpLimit.lean::realized_credit_bounded_by_backing`
  proves `(creditRateNum × claim) / CREDIT_RATE_SCALE ≤ available`
  for any `claim > 0` — regardless of how big the claim grows
  (oracle-pump scenario), the realizable credit cannot exceed
  the available backing. `oracle_pump_cannot_exceed_backing` is
  the direct corollary on a growing-claim sequence. Builds on
  Phase 1's `creditRateNum_le_scale`, `_zero_backing`,
  `_mono_in_backing`, and `_anti_in_claim`. Closes §14 #6.

### #7. `source_credit_rate_zero_when_backing_stale_or_exhausted`
**Confidence:** HIGH
**Strength:** WEAK
**Harnesses:**
- `proof_v16_expired_fresh_backing_stale_cert_blocks_source_credit_conversion` `[CON]` — stale fresh backing forces `Err(Stale)` on conversion.
- `proof_v16_source_domain_realizable_support_zero_backing_gives_zero_credit` `[CON]` — exhausted backing produces zero credit rate.

### #8. `risk_increasing_trade_requires_source_credit_lien`
**Confidence:** HIGH
**Strength:** WEAK
**Harnesses:**
- `proof_v16_risk_increasing_trade_requires_initial_health_before_mutation` `[CON]` — risk-increasing path requires healthy refresh.
- `proof_v16_hlock_risk_increasing_trade_rejects_positive_credit_dependency_without_mutation` `[CON]` — risk-increasing trade relying on uncovered positive credit is rejected before mutation.
- `proof_v16_unbacked_attributed_conversion_rejects_without_mutation` `[CON]` — unbacked attributed credit rejected.

### #9. `source_credit_lien_prevents_double_use_of_same_claim_and_backing`
**Confidence:** HIGH
**Strength:** WEAK
**Harnesses:**
- `proof_v16_counterparty_source_credit_lien_aggregate_tracks_account_backing_split` `[CON]` — counterparty-backed liens reflect aggregate without aliasing.
- `proof_v16_insurance_source_credit_lien_aggregate_tracks_account_backing_split` `[CON]` — insurance-backed equivalent.
- `proof_v16_public_withdraw_counts_existing_lien_before_incremental_credit` `[CON]` — incremental credit must subtract existing lien.

### #10. `source_credit_lien_impairment_forces_deleverage_liquidation_or_recovery`
**Confidence:** HIGH
**Strength:** WEAK
**Harnesses:**
- `proof_v16_full_refresh_impairs_expired_counterparty_lien_before_equity_credit` `[CON]` — expired counterparty lien is impaired before equity credit.
- `proof_v16_insurance_lien_impairment_removes_account_health_credit` `[CON]` — insurance-backed impairment removes the credit from health.

### #11. `backing_reservation_is_actual_locked_equity_not_optimistic_certificate`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_full_refresh_reserves_counterparty_backing_from_new_capital_backed_loss` `[CON]` — backing reservation comes from real loss-bearing capital, not a certificate.
- `proof_v16_counterparty_lien_consume_preserves_backing_encumbrance` + `proof_v16_counterparty_lien_impair_preserves_backing_encumbrance` `[SEMI]` — `fresh_reserved_backing_num` mirrors true locked equity through lifecycle.

### #12. `backing_expiry_buckets_exclude_stale_contributions_without_full_scan`
**Confidence:** MEDIUM
**Strength:** STRONG
**Harnesses:**
- `proof_v16_expired_fresh_backing_stale_cert_blocks_source_credit_conversion` `[CON]` — expired backing excluded from credit conversion.
- `proof_v16_permissionless_crank_does_not_require_full_market_scan` `[SYM]` — bounded-work crank does not scan all accounts.
**Note:** No direct harness on `backing_expiry_buckets` data structure; coverage is by observable effect.
- **Lean closure**: `BoundedExpiryScan.lean::stale_excluded_by_local_check`
  shows the per-bucket stale check (`isStale`) reads only the
  `status` field of a single bucket — never any other bucket,
  account, or market. `liveAvailable_local` proves
  `liveAvailable`'s body is `if status = .Fresh then
  freshUnliened else 0`, a one-bucket function by signature.
  `sumLiveAvailable_signature_bounds_work` /
  `_input_is_buckets_only` express the structural bounded-work
  witness: the function type `List BackingBucket → Nat` rules
  out scanning accounts or markets (which would need
  `List Account → Nat` or `List Market → Nat`).
  `sumLiveAvailable_zero_when_all_stale` is the full closure:
  the aggregate excludes stale contributions by a per-bucket
  local check; `sumLiveAvailable_eq_sum_over_fresh` exhibits the
  partial-exclusion form for mixed lists. Closes §14 #12.

### #13. `insurance_credit_reservation_globally_conserved`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_insurance_reservation_lifecycle_preserves_encumbrance` `[SEMI]` — reserve/lien/consume/impair conserves insurance counters.
- `proof_v16_insurance_source_credit_lien_aggregate_tracks_account_backing_split` `[CON]` — aggregate equals account-level sum.

### #14. `insurance_spend_not_double_counted_as_live_encumbrance`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_insurance_reservation_lifecycle_preserves_encumbrance` `[SEMI]` — on consume, encumbrance is replaced by `consumed_insurance_num`, not duplicated.
- `proof_v16_bankrupt_liquidation_spends_one_insurance_atom_once` `[CON]` — atomic spend counted exactly once.
- `proof_v16_bankrupt_liquidation_spends_two_insurance_atoms_once` `[CON]` — same with two atoms.

### #15. `amount_from_bound_num_up_rounds_up_for_insurance_credit`
**Confidence:** HIGH (Lean theorem directly mirrors the function being claimed)
**Strength:** STRONG (∀ Nat via Lean)
**Lean theorems** (`Percolator/BoundArith.lean`):
- `amountFromBoundNum_rounds_up` — for all `bn`, `amountFromBoundNum bn · BOUND_SCALE ≥ bn`. **Direct discharge of #15.**
- `amountFromBoundNum_minimal` — the result is the smallest such amount (full ceiling characterization).
- `amountFromBoundNum_exact` — no rounding when `bn % BOUND_SCALE = 0`.
- `amount_bound_roundtrip` — `amountFromBoundNum (amount · BOUND_SCALE) = amount`.
- `amountFromBoundNum_mono` — bigger `bn` ⇒ at-least-as-big amount.
**Kani harnesses (concrete sanity):**
- `proof_v16_scaled_junior_bound_remainder_ceil_controls_resolved_payout` `[SEMI]` — scaled-bound remainder ceiling enforced in Rust.
**Note:** primitive ceil-div / wide mul-div-ceil sanity checks (formerly cited as dedicated Kani proofs) were retired upstream; their content survives implicitly through the higher-level proofs that use them, and is covered ∀ Nat by `amountFromBoundNum_rounds_up` / `_minimal` / `_exact` above.

### #16. `source_credit_insurance_reservation_single_canonical_writer`
**Confidence:** LOW
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_insurance_reservation_lifecycle_preserves_encumbrance` `[SEMI]` — only the lifecycle helpers touch the reservation counters.
**Note:** "Single canonical writer" is a structural property — no Kani harness directly asserts it; the absence of cross-writer pathways is inferred.

### #17. `source_credit_insurance_cannot_be_double_reserved_or_double_spent`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_insurance_reservation_lifecycle_preserves_encumbrance` `[SEMI]` — reserved counter never exceeds `reserve` and consume reduces it by exactly `lien`.
- `proof_v16_insurance_source_credit_lien_aggregate_tracks_account_backing_split` `[CON]` — proof aggregate sums account splits without overlap.
- **Lean closure**: `NoDoubleSpend.lean::cannot_reserve_twice_beyond_capacity`
  proves that two consecutive `reserve amount` calls require
  `2 * amount` against the same deposit — if deposit = amount,
  the second reserve fails closed.
  `cannot_consume_twice_beyond_reservation` proves that after a
  successful `reserve amount` + `consume amount`, the reservation
  is empty (= 0) and a second `consume amount` fails closed.
  `cumulative_reservation_bounded_by_deposit` is the structural
  conservation invariant (reservation + spent ≤ deposit) carried
  by the ledger; `consume_atom_either_reserved_or_spent` is the
  atomic decrement witness — the same atom cannot be both
  reserved and spent simultaneously. Closes §14 #17.

### #18. `insurance_backed_lien_creation_increments_valid_liened_insurance_not_counterparty_backing`
**Confidence:** HIGH
**Strength:** WEAK
**Harnesses:**
- `proof_v16_insurance_source_credit_lien_aggregate_tracks_account_backing_split` `[CON]` — proof shows `valid_liened_insurance_num` increments while counterparty backing is zero.
- `proof_v16_release_account_source_lien_restores_insurance_backing_when_unneeded` `[CON]` — release symmetric.

### #19. `insurance_backed_lien_consume_release_impair_conserves_canonical_ledger`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_insurance_reservation_lifecycle_preserves_encumbrance` `[SEMI]` — covers consume and impair branches and asserts `assert_public_invariants` holds.
- `proof_v16_release_account_source_lien_restores_insurance_backing_when_unneeded` `[CON]` — release branch.

### #20. `insurance_backed_lien_consumption_decrements_source_credit_reservation_and_total_available_once`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_insurance_reservation_lifecycle_preserves_encumbrance` `[SEMI]` — consume decrements `valid_liened_insurance_num`, sets `consumed_insurance_num`, and `available_backing_num` updates exactly once.

### #21. `impaired_insurance_lien_remains_reserved_and_unavailable_until_reconciled`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_insurance_reservation_lifecycle_preserves_encumbrance` `[SEMI]` — impair branch keeps `available_backing = reserve - lien` and `impaired_liened_insurance_num = lien`.
- `proof_v16_insurance_lien_impairment_removes_account_health_credit` `[CON]` — impaired insurance lien removes account health credit.

### #22. `insurance_backed_residual_cure_lien_counts_exactly_once_as_insurance_spent`
**Confidence:** LOW
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_insurance_reservation_lifecycle_preserves_encumbrance` `[SEMI]` — consume increments `consumed_insurance_num` exactly once.
**Note:** No harness specific to "residual cure" path on insurance-backed liens.
- **Lean closure**: `ResidualCureOnce.lean::cureFromInsurance` is
  a single atomic transition decrementing
  `insuranceLienReserved`, incrementing `insuranceSpent`, and
  decrementing `closeResidualRemaining` — all by the same
  `amount`. `cureFromInsurance_charges_exactly_once` proves
  spent increments by exactly amount;
  `_decrements_lien_once` proves the lien drops by the same
  amount; `_decrements_residual` proves the residual drops
  similarly;
  `cureFromInsurance_lien_drop_matches_spent_increment` is the
  composed identity — the same atom is consumed from the lien
  and recorded once on spent, never both undercharged or
  doublecharged. Closes §14 #22.

### #23. `insurance_backed_lien_never_counts_as_both_support_and_insurance`
**Confidence:** MEDIUM
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_insurance_source_credit_lien_aggregate_tracks_account_backing_split` `[CON]` — aggregate proof partitions face-claim locked between counterparty and insurance categories.
- `proof_v16_dead_leg_forfeit_books_one_loss_atom_to_opposing_domain_only` + `proof_v16_dead_leg_forfeit_books_four_loss_atoms_to_opposing_domain_only` `[SEMI]` — loss attribution is disjoint.
**Note:** The dual-counting prohibition is shown structurally by the partitioned aggregate; no harness exhibits a specific double-classification attempt.

### #24. `close_residual_partition_classifies_counterparty_and_insurance_lien_consumption_disjointly`
**Confidence:** MEDIUM
**Strength:** WEAK
**Harnesses:**
- `proof_v16_bankrupt_liquidation_consumes_insurance_before_social_loss` `[CON]` — partitions `insurance_used`, `residual_booked`, `explicit_loss`.
- `proof_v16_long_liquidation_residual_charges_short_domain` `[CON]` — residual classification by side.

### #25. `token_value_flow_proof_balances_internal_insurance_transfers`
**Confidence:** MEDIUM
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_loss_and_fee_value_flow_preserves_vault_and_senior_totals` `[SEMI]` — fee-to-insurance internal transfer preserves vault.
- `proof_v16_bankrupt_liquidation_consumes_insurance_before_social_loss` `[CON]` — insurance→loss internal transfer balances.

### #26. `internal_insurance_transfer_requires_exactly_one_credit_entry`
**Confidence:** LOW
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_loss_and_fee_value_flow_preserves_vault_and_senior_totals` `[SEMI]` — implies single credit by total preservation.
**Note:** No harness enforces "exactly one credit entry" as a counted property; the conservation harness implies it.

### #27. `recovery_consumed_insurance_lien_decrements_v_on_external_payout`
**Confidence:** LOW
**Strength:** WEAK
**Harnesses:**
- `proof_v16_permissionless_recovery_enables_dead_leg_forfeit_without_value_escape` `[CON]` — recovery does not escape value.
**Note:** External-payout decrement of `v` on recovery insurance consumption is not directly observable in current proofs.

### #28. `lien_creatable_predicate_requires_actual_bucket_or_insurance_reservation_capacity`
**Confidence:** HIGH
**Strength:** WEAK
**Harnesses:**
- `proof_v16_public_withdraw_locks_claim_and_backing_when_positive_credit_is_required` `[CON]` — withdraw demanding credit succeeds only when backing or reservation present.
- `proof_v16_unbacked_attributed_conversion_rejects_without_mutation` `[CON]` — unbacked path returns `LockActive` without mutation.

### #29. `lien_creatable_matches_actual_bucket_and_insurance_lifecycle_helpers`
**Confidence:** MEDIUM
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_counterparty_lien_consume_preserves_backing_encumbrance` + `proof_v16_counterparty_lien_impair_preserves_backing_encumbrance` `[SEMI]` — bucket helper invariants hold.
- `proof_v16_insurance_reservation_lifecycle_preserves_encumbrance` `[SEMI]` — insurance helper invariants hold.

### #30. `insurance_backed_lien_create_consume_release_impair_conserves_canonical_ledger`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_insurance_reservation_lifecycle_preserves_encumbrance` `[SEMI]` — full lifecycle harness checks public invariants throughout.

### #31. `insurance_impaired_lien_remains_encumbered_until_release_or_consume`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_insurance_reservation_lifecycle_preserves_encumbrance` `[SEMI]` — impair branch keeps `available = reserve - lien`.
- `proof_v16_insurance_lien_impairment_removes_account_health_credit` `[CON]` — impaired lien removes its credit.

### #32. `lien_creation_increments_correct_aggregate_for_backing_source`
**Confidence:** HIGH
**Strength:** WEAK
**Harnesses:**
- `proof_v16_counterparty_source_credit_lien_aggregate_tracks_account_backing_split` `[CON]` — counterparty path.
- `proof_v16_insurance_source_credit_lien_aggregate_tracks_account_backing_split` `[CON]` — insurance path.

### #33. `lien_creatable_predicate_matches_actual_bucket_or_insurance_lifecycle`
**Confidence:** MEDIUM
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_counterparty_lien_consume_preserves_backing_encumbrance` + `proof_v16_counterparty_lien_impair_preserves_backing_encumbrance` `[SEMI]` — counterparty lifecycle matches predicate.
- `proof_v16_insurance_reservation_lifecycle_preserves_encumbrance` `[SEMI]` — insurance lifecycle matches predicate.
**Note:** Mostly a restatement of #29; same harnesses apply.

### #34. `backing_bucket_expiry_does_not_underflow_available_backing`
**Confidence:** LOW
**Strength:** WEAK
**Harnesses:**
- `proof_v16_expired_fresh_backing_stale_cert_blocks_source_credit_conversion` `[CON]` — expiry path is observed without underflow.
**Note:** No harness directly exercises the `expire_backing_bucket` helper edge cases.

### #35. `backing_bucket_expiry_does_not_increase_available_backing_or_credit_rate`
**Confidence:** LOW
**Strength:** WEAK
**Harnesses:**
- `proof_v16_expired_fresh_backing_stale_cert_blocks_source_credit_conversion` `[CON]` — credit rate after expiry does not exceed pre-expiry rate.
**Note:** Same caveat as #34.

### #36. `backing_bucket_expiry_after_partial_lien_consumption_does_not_inflate_available`
**Confidence:** NONE
**Strength:** N/A
**Harnesses:** _No matching harness found._
**Note:** A targeted harness would set up a partially-consumed lien, expire the underlying bucket, and assert `available_backing` does not increase.

### #37. `lien_consumption_decrements_bucket_valid_liened_and_source_valid_liened_once`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_counterparty_lien_consume_preserves_backing_encumbrance` `[SEMI]` — consume branch decrements `valid_liened_backing_num` exactly once.

### #38. `lien_consumption_removes_backing_from_fresh_reserved_and_claim_bound`
**Confidence:** MEDIUM
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_counterparty_lien_consume_preserves_backing_encumbrance` `[SEMI]` — consume reduces `fresh_reserved_backing_num` by `lien` and sets `spent_backing_num = lien`.
- `proof_v16_passive_backing_consumption_preserves_senior_accounting_without_wrapper_injection` `[CON]` — consumption deducts from claim bound.

### #39. `lien_release_moves_valid_liened_to_fresh_unliened_without_changing_fresh_reserved`
**Confidence:** HIGH
**Strength:** WEAK
**Harnesses:**
- `proof_v16_release_account_source_lien_restores_counterparty_backing_when_unneeded` `[CON]` — release restores counterparty backing without changing fresh_reserved totals.
- `proof_v16_release_account_source_lien_restores_insurance_backing_when_unneeded` `[CON]` — insurance equivalent.

### #40. `source_available_backing_recomputes_from_bucket_sums`
**Confidence:** MEDIUM
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_source_credit_rate_is_bounded_by_available_backing` `[SEMI]` — uses `source_credit_available_backing_num(0)` which is recomputed.
- `proof_v16_counterparty_lien_consume_preserves_backing_encumbrance` + `proof_v16_counterparty_lien_impair_preserves_backing_encumbrance` `[SEMI]` — bucket-sum recomputation observed.

### #41. `expired_liened_bucket_marks_liens_impaired_in_bounded_work`
**Confidence:** MEDIUM
**Strength:** WEAK
**Harnesses:**
- `proof_v16_full_refresh_impairs_expired_counterparty_lien_before_equity_credit` `[CON]` — expired counterparty lien is impaired during the refresh.
**Note:** The "bounded work" upper-bound is implicit (Kani enforces unwind bounds) but not explicitly stated.

### #42. `credit_rate_num_bounded_below_and_above`
**Confidence:** HIGH
**Strength:** STRONG (via Lean — ∀ over Nat)
**Lean theorems** (`Percolator/CreditRate.lean`):
- `creditRateNum_le_scale` — upper bound: rate ≤ CREDIT_RATE_SCALE for all inputs.
- `creditRateNum_nonneg` — lower bound: rate ≥ 0 (structural in Nat).
- `creditRateNum_zero_backing` — boundary: zero backing ⇒ zero rate.
- `creditRateNum_full_backing` — boundary: full backing ⇒ rate caps at SCALE.
- `creditRateNum_zero_claim` — boundary: zero claim ⇒ full credit.
**Kani harnesses (concrete sanity):**
- `proof_v16_source_credit_rate_is_bounded_by_available_backing` `[SEMI]` — concrete-input sanity check that the Rust impl matches the Lean spec at three regimes.
- `proof_v16_source_domain_realizable_support_zero_backing_gives_zero_credit` `[CON]` — Rust impl at the zero-backing fixture.

### #43. `lien_creation_requires_required_backing_le_available_backing`
**Confidence:** HIGH
**Strength:** WEAK
**Harnesses:**
- `proof_v16_public_withdraw_locks_claim_and_backing_when_positive_credit_is_required` `[CON]` — lien creation requires backing.
- `proof_v16_unbacked_attributed_conversion_rejects_without_mutation` `[CON]` — fails when required > available.

### #44. `locked_face_claim_excluded_from_soft_credit`
**Confidence:** HIGH
**Strength:** WEAK
**Harnesses:**
- `proof_v16_public_withdraw_counts_existing_lien_before_incremental_credit` `[CON]` — existing locked face claim subtracted before computing incremental credit.

### #45. `withdrawal_uses_conservative_sum_negative_leg_pnl_not_aggregate_min`
**Confidence:** MEDIUM
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_stale_profitable_leg_cannot_withdraw_using_pre_refresh_positive_pnl` `[CON]` — disallows over-withdraw on profitable but stale leg.
- `proof_v16_loss_stale_blocks_nonflat_withdrawal` `[CON]` — loss-stale state blocks withdrawal.
- `proof_v16_partial_withdraw_can_leave_small_remainder` `[SEMI]` — partial-withdraw conservative path.
- **Lean closure**: `ConservativeWithdrawal.lean::sumLoss_ge_maxLoss`
  proves `maxLoss ≤ sumLoss` over arbitrary lists of leg losses
  — the structural inequality that distinguishes the conservative
  formula (subtract sum of all losses) from the aggregate-min
  formula (subtract just the max). `conservative_le_aggregate_min`
  is the corollary on withdrawal capacity: the conservative
  formula never permits a strictly larger withdrawal.
  `aggregate_min_overstates_with_two_losses` is the counterexample:
  with two legs each losing k, the sum is 2k but the max is k,
  so the aggregate-min formula would over-credit a withdrawal
  by k. Closes §14 #45.

### #46. `close_drift_reserve_has_backed_loss_capacity_or_recovers`
**Confidence:** MEDIUM
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_expired_close_progress_routes_recovery_before_durable_mutation` `[SEMI]` — expired drift reserve routes to recovery.
- `proof_v16_zero_weight_domain_residual_routes_to_recovery_without_mutation` `[SEMI]` — no capacity → recovery.

### #47. `pulled_forward_obligation_credit_not_socialized_again`
**Confidence:** MEDIUM
**Strength:** WEAK
**Harnesses:**
- `proof_v16_pending_domain_barrier_blocks_participants_until_residual_finalized` `[CON]` — pending obligation blocks re-socialization.
- `proof_v16_flat_pending_obligation_cannot_clear_before_b_settlement` `[CON]` — pulled-forward obligation cannot clear early.

### #48. `claim_bound_bucket_formula_never_understates_source_domain_claims`
**Confidence:** LOW
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_source_domain_realizable_support_uses_source_credit_rate` `[CON]` — formula applied at account level.
- `proof_v16_public_invariants_reject_scaled_junior_bound_cache_mismatch` `[SEMI]` — cached scaled bound must match formula.
**Note:** No harness targets the bucket-formula's lower-bound property directly.

### #49. `claim_bound_bucket_out_of_range_fails_closed_or_rebuckets`
**Confidence:** LOW
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_public_invariants_reject_scaled_junior_bound_cache_mismatch` `[SEMI]` — cache desync rejected.
**Note:** No targeted harness on out-of-range bucket re-bucketing.
- **Lean closure**: `ClaimBoundBucketRange.lean::BucketRangeOutcome`
  is a closed sum (inRange | failClosed | rebucketed).
  `queryBucket_is_one_of_three` proves exhaustiveness;
  `out_of_range_does_not_return_inRange` rules out silent
  overflow; `rebucketed_clamps_into_range` proves a re-bucketed
  index is provably in range. Closes §14 #49.

### #50. `credit_rate_recomputation_is_bounded_by_domain_count_and_bucket_count`
**Confidence:** LOW
**Strength:** MEDIUM (per-domain math via Lean; bounded-work claim remains operational)
**Lean theorems** (`Percolator/CreditRate.lean`) — proves the per-domain formula is well-defined and bounded:
- `creditRateNum_le_scale` — per-domain output bounded.
- `creditRateNum_mono_in_backing`, `creditRateNum_anti_in_claim` — well-defined behavior as backing/claim shift.
**Note:** the "bounded by domain count and bucket count" claim is a compute-cost/total-work bound, not an arithmetic identity. It stays in Kani harness coverage.
**Kani harnesses (concrete sanity):**
- `proof_v16_source_credit_rate_is_bounded_by_available_backing` `[SEMI]` — single-domain bounded recomputation.
**Note:** No explicit harness on the recomputation cost bound across multiple domains/buckets.

### #51. `no_circular_credit_without_external_senior_backing`
**Confidence:** MEDIUM
**Strength:** STRONG
**Harnesses:**
- `proof_v16_unbacked_attributed_conversion_rejects_without_mutation` `[CON]` — unbacked credit fails closed.
- `proof_v16_full_refresh_reserves_counterparty_backing_from_new_capital_backed_loss` `[CON]` — senior backing must come from real capital.
- `proof_v16_public_invariants_reject_broken_senior_claim_conservation` `[SYM]` — senior conservation rejected when violated.

### #52. `soft_maintenance_credit_does_not_create_payout_or_residual_cure`
**Confidence:** MEDIUM
**Strength:** STRONG
**Harnesses:**
- `proof_v16_ordinary_positive_conversion_disabled_outside_live_payout_lane` `[SEMI]` — soft credit cannot pay out.
- `proof_v16_non_deficit_public_paths_do_not_decrease_insurance` `[SYM]` — soft credit does not draw insurance.

### #53. `settlement_quality_credit_consumes_backing_and_locks_face_claim`
**Confidence:** HIGH
**Strength:** WEAK
**Harnesses:**
- `proof_v16_negative_kf_settlement_consumes_realizable_source_credit_before_principal` `[CON]` — K/F settlement consumes source credit.
- `proof_v16_positive_kf_settlement_consumes_source_credit_to_cure_prior_loss` `[CON]` — positive K/F equivalent.
- `proof_v16_source_backed_conversion_waits_only_for_contributing_source_exposure` `[CON]` — face-claim lock honored.

### #54. `fake_asset_profit_cannot_buy_unbacked_other_asset_risk`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_trade_hint_cannot_hide_toxic_portfolio_leg_on_other_asset` `[CON]` — toxic other-asset leg cannot be hidden by hint.
- `proof_v16_bad_asset_cannot_spend_unrelated_domain_insurance_budget` `[SEMI]` — cross-domain insurance theft blocked.
- **Lean closure**: `CrossAssetIsolation.lean::AssetExposure` is
  type-indexed by `AssetTag` (a phantom Nat); two exposures on
  different assets have different types. `AssetExposure.realize`
  is the only path that produces fungible `Capital` from a typed
  exposure; the realization runs on a single tag — there is no
  cross-tag combinator. `takeRisk` requires `Capital` (not a
  different-tag exposure) — `takeRisk_requires_capital` and
  `_success_decrements_capital` witness the strict-capital
  consumption. The type system rules out functions that combine
  `AssetExposure tagA` and `AssetExposure tagB` directly.
  Closes §14 #54.

### #55. `backing_consumption_reduces_loser_capital_and_preserves_senior_invariants`
**Confidence:** HIGH
**Strength:** WEAK
**Harnesses:**
- `proof_v16_passive_backing_consumption_preserves_senior_accounting_without_wrapper_injection` `[CON]` — backing consumption deducts loser capital while preserving senior accounting.

### #56. `residuals_charged_only_to_asset_opposing_side_domain`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_long_liquidation_residual_charges_short_domain` `[CON]` — long-side residual charges short domain.
- `proof_v16_short_liquidation_residual_charges_long_domain` `[CON]` — short-side residual charges long domain.
- `proof_v16_dead_leg_forfeit_books_one_loss_atom_to_opposing_domain_only` + `proof_v16_dead_leg_forfeit_books_four_loss_atoms_to_opposing_domain_only` `[SEMI]` — dead-leg equivalent.

### #57. `no_global_B_index`
**Confidence:** MEDIUM
**Strength:** STRONG
**Harnesses:**
- `proof_v16_per_asset_slot_last_prevents_cross_asset_accrual_aliasing` `[CON]` — per-asset slot last (no cross-asset global slot).
- `proof_v16_permissionless_crank_does_not_require_full_market_scan` `[SYM]` — hinted progress is O(1) per call.

### #58. `cross_instance_ui_aggregation_not_health_or_collateral_proof`
**Confidence:** MEDIUM
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_global_residual_is_not_account_health_proof` `[SEMI]` — global residual cannot prove account health (analogous in-instance claim).
**Note:** "Cross-instance UI aggregation" itself is not modeled; only the in-instance analog (global residual not used for per-account health) is covered.

### #59. `mutable_asset_activation_requires_full_envelope_proofs`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_asset_activation_requires_empty_slot_and_bumps_epochs` `[SEMI]` — activation requires empty slot and bumps all relevant epochs.
- `proof_v16_dynamic_header_activation_binds_backing_to_new_market_id` `[SEMI]` — backing-binding portion of envelope.
- `proof_v16_backing_bucket_market_id_must_match_asset_slot` `[SEMI]` — backing/market-id binding enforced.

### #60. `asset_cannot_activate_with_nonzero_or_unreconciled_state`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_asset_activation_requires_empty_slot_and_bumps_epochs` `[SEMI]` — empty-slot precondition.
- `proof_v16_retired_asset_idempotence_requires_empty_state` `[SEMI]` — retired state empty before re-activation.

### #61. `activation_invalidates_or_scopes_certs_fail_closed`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_b_stale_invalidates_prior_health_certificate` + `proof_v16_same_epoch_full_refresh_is_idempotent_after_price_down_settlement` + `proof_v16_same_epoch_full_refresh_is_idempotent_after_price_up_settlement` `[SEMI]` — certs scoped to epochs and prices; b-stale invalidates prior cert (mismatch fails closed); same-epoch refresh idempotence binds cert to price settlements.
- `proof_v16_favorable_action_accepts_current_full_refresh_certificate` + `proof_v16_favorable_action_rejects_stale_full_refresh_certificate` + `proof_v16_stale_clear_plus_current_certificate_restores_favorable_action_lane` `[CON]` — full refresh required (accept current / reject stale / stale-clear + current cert restores favorable-action lane).

### #62. `full_account_refresh_required_for_favorable_actions`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_favorable_action_accepts_current_full_refresh_certificate` + `proof_v16_favorable_action_rejects_stale_full_refresh_certificate` `[CON]` — direct claim (accept current / reject stale).
- `proof_v16_b_stale_invalidates_prior_health_certificate` `[SEMI]` — cert binding (b-stale invalidates prior cert).
- `proof_v16_favorable_locks_block_released_pnl_conversion_before_mutation` `[SEMI]` — locks block favorable actions.
- **Lean closure**: `FavorableActions.lean::FavorableActionKind.tryExecute`
  matches on the snapshot's `refresh : RefreshStatus` field and
  refuses to fire on `.Stale`. `tryExecute_blocked_when_stale`
  proves all three favorable-action kinds (Withdraw,
  IncreaseLeverage, UnlockCollateral) fail closed on stale
  snapshots; `tryExecute_some_implies_fresh` is the
  contrapositive: a successful action proves the snapshot was
  `.Fresh`. The closed-sum `RefreshStatus` guarantees the only
  path to `.Fresh` is via `markRefreshed` (corresponding to the
  production engine's full-refresh routine). Closes §14 #62.

### #63. `verified_maker_exemption_requires_engine_verified_post_trade_health_cert`
**Confidence:** NONE
**Strength:** N/A
**Harnesses:** _No matching harness found._
**Note:** No proof targeting a "verified maker" exemption path; if implemented, would assert that the exemption requires engine-verified post-trade cert.
- **Lean closure**: `VerifiedMaker.lean::PostTradeHealthCert`
  carries an origin tag from the closed-sum `CertOrigin`
  (engineVerified | userSupplied). `tryVerifiedMakerExemption`
  pattern-matches on origin and refuses to fire on
  `.userSupplied`.
  `tryVerifiedMakerExemption_blocked_when_user_supplied` and
  `_some_implies_engine_verified` are the contrapositive pair;
  `_engine_verified_fires` is the positive direction. Same
  pattern as §14 #62. Closes §14 #63.

### #64. `pending_obligation_credit_decrements_origin_residual_once`
**Confidence:** MEDIUM
**Strength:** WEAK
**Harnesses:**
- `proof_v16_pending_domain_barrier_blocks_participants_until_residual_finalized` `[CON]` — origin residual cleared exactly once on finalization.
- `proof_v16_flat_pending_obligation_cannot_clear_before_b_settlement` `[CON]` — single-decrement ordering.

### #65. `aggregate_due_drift_credit_is_O_1_before_b_booking`
**Confidence:** LOW
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_b_residual_booking_positive_makes_durable_progress` + `proof_v16_b_residual_booking_zero_noops` `[SEMI]` — booking is bounded and durable.
**Note:** Big-O complexity is not explicitly modeled; Kani's `unwind` bound implies boundedness.
- **Lean closure**: `AggregateDriftCredit.lean::DriftCreditAggregate`
  is a single-Nat record. `read : DriftCreditAggregate → Nat` is
  a direct field projection; the function's signature rules out
  any list traversal. `credit` and `debit` are incremental
  updates that operate on the aggregate alone (no per-account
  scan). `hasDriftCapacity` is the typed B-booking precondition
  with signature `DriftCreditAggregate → Nat → Bool` — a single
  comparison against a single field. Closes §14 #65 with the
  structural-locality pattern (same as #12 and #85).

### #66. `participant_finalization_pulls_forward_pending_obligation`
**Confidence:** MEDIUM
**Strength:** WEAK
**Harnesses:**
- `proof_v16_pending_domain_barrier_allows_full_trade_exit_as_flat_weight_obligation` `[CON]` — exit converts to flat obligation.
- `proof_v16_pending_domain_barrier_allows_rebalance_full_exit_as_flat_weight_obligation` `[CON]` — rebalance variant.
- `proof_v16_pending_obligation_blocks_side_reset_until_clear` `[CON]` — obligation pulled forward blocks reset.

### #67. `phantom_weight_without_backing_reverts`
**Confidence:** HIGH
**Strength:** STRONG
**Harnesses:**
- `proof_v16_unbacked_attributed_conversion_rejects_without_mutation` `[CON]` — unbacked attributed credit reverts.
- `proof_v16_public_invariants_reject_broken_senior_claim_conservation` `[SYM]` — phantom senior weight rejected by invariants.
- `proof_v16_risk_increasing_trade_requires_initial_health_before_mutation` `[CON]` — phantom-weight risk increase blocked.

### #68. `preemptive_close_priority_prevents_hold_and_wait_deadlock`
**Confidence:** MEDIUM
**Strength:** WEAK
**Harnesses:**
- `proof_v16_single_domain_close_lock_rejects_second_origin_until_first_finalized` `[CON]` — strict close ordering.
- `proof_v16_new_close_cannot_overwrite_active_finalized_close_ledger` `[CON]` — preemption rules.

### #69. `preempted_close_restart_cannot_double_book_residual`
**Confidence:** MEDIUM
**Strength:** WEAK
**Harnesses:**
- `proof_v16_new_close_cannot_overwrite_active_finalized_close_ledger` `[CON]` — restart blocked while ledger active.
- `proof_v16_single_domain_close_lock_rejects_second_origin_until_first_finalized` `[CON]` — second origin blocked.

### #70. `close_id_and_drift_anchors_immutable`
**Confidence:** MEDIUM
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_new_close_cannot_overwrite_active_finalized_close_ledger` `[CON]` — close_id preserved.
- `proof_v16_close_lifetime_uses_configured_bound_and_is_not_refreshed` `[SEMI]` — drift anchors not refreshed.
- `proof_v16_account_shape_rejects_close_progress_domain_mismatch_for_open_leg` `[SEMI]` — anchor consistency.

### #71. `bankrupt_close_progress_decreases_net_of_close_drift`
**Confidence:** MEDIUM
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_account_b_booking_advances_close_progress_or_fails_closed` `[SEMI]` — progress strictly advances or fails.
- `proof_v16_b_residual_booking_positive_makes_durable_progress` + `proof_v16_b_residual_booking_zero_noops` `[SEMI]` — durable progress invariant.

### #72. `cure_and_cancel_checks_before_consuming_new_deposit`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_cure_and_cancel_close_deposits_fresh_escrow_before_irreversible_progress` + `proof_v16_cure_and_cancel_close_releases_existing_escrow_before_irreversible_progress` `[SEMI]` — happy path (fresh-deposit and release-existing variants).
- `proof_v16_cure_and_cancel_rejects_b_progress_before_deposit_mutation` + `proof_v16_cure_and_cancel_rejects_drift_progress_before_deposit_mutation` + `proof_v16_cure_and_cancel_rejects_explicit_loss_progress_before_deposit_mutation` + `proof_v16_cure_and_cancel_rejects_insurance_progress_before_deposit_mutation` + `proof_v16_cure_and_cancel_rejects_quantity_adl_progress_before_deposit_mutation` + `proof_v16_cure_and_cancel_rejects_support_progress_before_deposit_mutation` `[SEMI]` — rejection path leaves deposit untouched for any in-flight progress type (b/drift/explicit-loss/insurance/quantity-adl/support).

### #73. `quantity_adl_and_account_finalization_atomic_or_barriered`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_quantity_adl_preserves_oi_symmetry_after_close` `[SEMI]` — qADL preserves OI symmetry.
- `proof_v16_quantity_adl_monotonically_shrinks_opposing_a_or_resets` `[SEMI]` — bounded shrink.
- `proof_v16_expired_close_progress_routes_recovery_before_durable_mutation` `[SEMI]` — barrier when expired.

### #74. `domain_lock_does_not_block_asset_wide_kf_accrual`
**Confidence:** MEDIUM
**Strength:** WEAK
**Harnesses:**
- `proof_v16_pending_domain_loss_barrier_does_not_freeze_asset_accrual` `[CON]` — barrier allows K/F accrual to continue.

### #75. `B_booking_exact_remainder_conservation`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_account_b_chunk_current_noops` + `proof_v16_account_b_chunk_positive_budget_advances` + `proof_v16_account_b_chunk_zero_budget_fails_closed` `[SEMI]` — exact conservation per chunk (noop / advance / fail-closed cases).
- `proof_v16_repeated_account_b_chunks_complete_bounded_small_residual` `[SEMI]` — repeated chunks complete with bounded remainder.
- `proof_v16_b_residual_booking_positive_makes_durable_progress` + `proof_v16_b_residual_booking_zero_noops` `[SEMI]` — B residual booking exactness.

### #76. `zero_weight_domain_residual_cannot_clear_without_backing`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_zero_weight_domain_residual_routes_to_recovery_without_mutation` `[SEMI]` — direct match.

### #77. `uncollectible_fees_forgiven_not_socialized`
**Confidence:** HIGH
**Strength:** STRONG
**Harnesses:**
- `proof_v16_fee_sync_uses_wide_product_and_drops_uncollectible_tail` `[SEMI]` — uncollectible tail dropped.
- `proof_v16_liquidation_fee_floor_shortfall_charges_available_capital_only` `[SEMI]` — shortfall charges only available capital.
- `proof_v16_non_deficit_public_paths_do_not_decrease_insurance` `[SYM]` — fees never reduce insurance.

### #78. `resolved_payout_uses_source_domain_or_conservative_aggregate_rates`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_resolved_payout_uses_positive_bound_denominator` `[CON]` — conservative bound denominator.
- `proof_v16_resolved_positive_payout_snapshot_is_order_stable` `[CON]` — snapshot order-stable.
- `proof_v16_resolved_payout_readiness_uses_exact_counters_and_bounds` `[SEMI]` — uses exact counters.
- **Lean closure**: `ResolvedPayoutRate.lean::ResolutionRateContext`
  carries the per-domain and aggregate rates; `payoutRateNum :=
  min(perDomainRateNum, aggregateRateNum)` is the spec formula.
  `payoutRateNum_le_perDomain` and `_le_aggregate` prove the
  chosen rate is bounded above by *both* inputs — so neither
  domain-level nor cross-domain insolvency can be silently
  over-paid. `payoutRateNum_equals_one_of_two` is the closed-
  world: the rate is exactly one of the two, never an ad-hoc
  third value. `max_rate_overstates_when_rates_differ` is the
  strict counterexample showing the forbidden "max-rate"
  formula always over-pays. Same pattern as §14 #45. Closes
  §14 #78.

### #79. `resolved_receipt_underbound_halts_payout_or_recovers`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_unfinalized_resolved_receipt_blocks_account_close_until_topup` `[SEMI]` — under-bound receipt blocks close until top-up.
- `proof_v16_resolved_receipt_tracks_paid_effective_and_bound_refinement_topup` `[SEMI]` — top-up refinement path.
- `proof_v16_pnl_pos_bound_tot_prevents_lazy_positive_pnl_first_mover_overpay` `[CON]` — under-bound first-mover overpay prevented.
- **Lean closure**: `ReceiptUnderbound.lean::ReceiptOutcome`
  is a closed sum of three constructors (`paid` /
  `haltedPendingTopup` / `routedToRecovery`).
  `ResolvedReceipt.process` returns one of the three based on
  payment state and recovery eligibility.
  `underbound_does_not_pay` proves under-bound receipts can't
  return `.paid`; `underbound_halts_or_recovers` is the positive
  form. `paid_implies_fully_paid` is the contrapositive. The
  closed-world `process_is_one_of_three` dichotomy plus
  `recovery_branch_requires_underbound` /
  `halted_branch_requires_underbound_and_no_recovery` rule out
  spurious routing. Closes §14 #79.

### #80. `recovery_fallback_price_within_configured_deviation_envelope`
**Confidence:** NONE
**Strength:** N/A
**Harnesses:** _No matching harness found._
**Note:** Spec §15 `[FIXED]` claims a `cfg_max_recovery_fallback_deviation_bps` envelope is checked at activation; no Kani harness covers the deviation-cap predicate directly.

### #81. `recovery_fallback_value_transfer_bound_computed_per_account_and_domain`
**Confidence:** NONE
**Strength:** N/A
**Harnesses:** _No matching harness found._
**Note:** A targeted harness would compute the per-account, per-domain transfer bound under a fallback price and assert it bounds the actual transfer.

### #82. `fallback_recovery_rejects_unverified_or_out_of_envelope_reference_price`
**Confidence:** NONE
**Strength:** N/A
**Harnesses:** _No matching harness found._
**Note:** Closely related to #80; no Kani harness rejects an out-of-envelope fallback recovery price.

### #83. `dead_leg_forfeit_uses_bounded_fallback_or_zero_positive_payout`
**Confidence:** HIGH
**Strength:** WEAK
**Harnesses:**
- `proof_v16_dead_leg_forfeit_does_not_credit_positive_kf_delta` `[CON]` — positive K/F payout zeroed.
- `proof_v16_dead_leg_forfeit_haircuts_positive_support_when_junior_impaired` `[CON]` — bounded haircut on positive support.

### #84. `dead_leg_forfeit_books_to_bankruptcy_domain`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_dead_leg_forfeit_books_one_loss_atom_to_opposing_domain_only` + `proof_v16_dead_leg_forfeit_books_four_loss_atoms_to_opposing_domain_only` `[SEMI]` — loss booked to opposing (bankruptcy) domain only.
- `proof_v16_dead_leg_forfeit_partial_b_progress_does_not_detach` `[CON]` — partial progress remains on the same domain.

### #85. `no_single_instruction_full_market_scan_required`
**Confidence:** HIGH
**Strength:** STRONG
**Harnesses:**
- `proof_v16_permissionless_crank_does_not_require_full_market_scan` `[SYM]` — direct match.
- `proof_v16_worst_case_hinted_progress_actions_are_total_and_bounded` `[SEMI]` — worst-case hinted progress bounded.
- **Lean closure**: `NoFullMarketScan.lean::MarketState` models
  the asset array as an indexed function `assetAt : AssetIndex →
  AssetSlot`; `lookup` is a direct application — by Lean's
  evaluation model, an O(1) lookup. `PerAssetOp.apply` has
  signature `AssetIndex → AssetSlot → AssetSlot` — the operation
  reads exactly one slot. `applyAtIndex_preserves_other_slots`
  proves a single per-asset operation leaves every non-targeted
  slot unchanged — the structural no-scan witness. The
  composition `PerAssetOp.compose` also stays per-slot; the type
  system rules out a full-market scan inside a per-asset
  operation's body. Closes §14 #85 with the structural-locality
  pattern (same as #12 and #65).

### #86. `global_accumulator_not_account_health_proof`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_global_residual_is_not_account_health_proof` `[SEMI]` — global residual (the "accumulator") rejected as account-level health input.
- `proof_v16_global_cross_margin_positive_leg_supports_other_leg_maintenance_without_b_domain` `[CON]` — cross-margin uses local proof, not a global accumulator.

### #87. `canonical_single_leg_per_asset`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_same_asset_duplicate_leg_cannot_double_count_support` `[SEMI]` — duplicate attach rejected.
- `proof_v16_compact_leg_slots_preserve_asset_identity` `[CON]` — slot/asset binding.
- `proof_v16_validate_account_shape_binds_compact_leg_slot_to_asset_identity` `[SEMI]` — shape validation.

### #88. `N_too_large_rejects_public_initialization_or_activation`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_configured_portfolio_width_rejects_out_of_range_leg` `[SEMI]` — out-of-range N rejected.
- `proof_v16_config_separates_active_leg_and_market_slot_caps` `[CON]` — separate caps enforced.
- `proof_v16_market_slot_can_exceed_active_leg_cap` `[CON]` — capacity bounds verified.

### #89. `pending_obligation_exposure_counted_exactly_once_in_health_test`
**Confidence:** MEDIUM
**Strength:** WEAK
**Harnesses:**
- `proof_v16_pending_domain_barrier_does_not_freeze_unrelated_positive_credit` `[CON]` — exposure does not over-count unrelated accounts.
- `proof_v16_pending_domain_barrier_allows_rebalance_reduction_with_weight_obligation_preserved` `[CON]` — weight obligation preserved during reduction.

### #90. `equity_side_penalties_disjoint_from_requirement_side_penalties`
**Confidence:** MEDIUM
**Strength:** STRONG
**Harnesses:**
- `proof_v16_cross_margin_equity_counts_collateral_once_and_score_uses_full_envelope` `[SYM]` — equity counted once; score envelope separate.
- `proof_v16_global_cross_margin_positive_leg_supports_other_leg_maintenance_without_b_domain` `[CON]` — penalty channels distinct.

### #91. `hedge_credit_reduced_requirement_covers_combined_loss_envelope`
**Confidence:** MEDIUM
**Strength:** STRONG
**Harnesses:**
- `proof_v16_cross_margin_equity_counts_collateral_once_and_score_uses_full_envelope` `[SYM]` — hedge-aware score envelope.
- `proof_v16_global_cross_margin_positive_leg_supports_other_leg_maintenance_without_b_domain` `[CON]` — positive leg credit reducing requirement.

### #92. `cross_close_priority_is_strict_total_order`
**Confidence:** HIGH
**Strength:** WEAK
**Harnesses:**
- `proof_v16_single_domain_close_lock_rejects_second_origin_until_first_finalized` `[CON]` — strict order on second origin.
- `proof_v16_public_invariants_reject_multiple_pending_barriers_per_domain` `[CON]` — barrier count ≤ 1 per domain.

### #93. `equal_priority_livelock_impossible`
**Confidence:** LOW
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_worst_case_hinted_progress_actions_are_total_and_bounded` `[SEMI]` — every hinted action makes bounded progress.
**Note:** "Equal priority livelock impossible" is a liveness property partially observed via boundedness; not explicitly stated.

### #94. `B_booking_triggers_source_claim_bound_and_credit_rate_recompute_or_conservative_lowering`
**Confidence:** MEDIUM
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_b_residual_booking_positive_makes_durable_progress` + `proof_v16_b_residual_booking_zero_noops` `[SEMI]` — booking triggers recompute or close.
- `proof_v16_passive_backing_consumption_preserves_senior_accounting_without_wrapper_injection` `[CON]` — claim bound recomputed conservatively.
- **Lean closure**: `BBookingResponse.lean::BBookingResponse`
  is a closed sum (recomputed | conservativelyLowered).
  `bBookingStepResponse` returns one of the two based on the
  engine's recompute flag.
  `step_response_is_one_of_two` is the closed-world dichotomy.
  `lowered_never_raises_cache` proves the conservative-lowering
  branch never increases cached claim_bound or credit_rate.
  `recomputed_uses_fresh_values` proves the recompute branch
  produces the fresh inputs verbatim.
  `no_silent_upward_drift` bounds the post-state credit_rate
  by `max(pre.rate, fresh)` regardless of branch — no path
  silently exceeds both. Closes §14 #94.

### #95. `settlement_rounding_residue_credits_unallocated_surplus_and_flow_proof_balances`
**Confidence:** MEDIUM
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_loss_and_fee_value_flow_preserves_vault_and_senior_totals` `[SEMI]` — flow balances under fee/loss settlement.
- `proof_v16_scaled_junior_bound_remainder_ceil_controls_resolved_payout` `[SEMI]` — rounding residue handled.

### #96. `rounding_residue_never_used_for_health_backing_insurance_or_payout`
**Confidence:** LOW
**Strength:** STRONG
**Harnesses:**
- `proof_v16_global_residual_is_not_account_health_proof` `[SEMI]` — residual not health.
- `proof_v16_non_deficit_public_paths_do_not_decrease_insurance` `[SYM]` — residue not drained into insurance.
**Note:** No harness specifically segregates "rounding residue" from health/backing/insurance/payout pools.

### #97. `stock_reconciliation_includes_settlement_rounding_residue_total`
**Confidence:** LOW
**Strength:** STRONG
**Harnesses:**
- `proof_v16_stock_reconciliation_decomposes_vault_without_aliasing` `[SYM]` — reconciliation covers the unallocated tail.
**Note:** Reconciliation harness checks `vault = c_tot + insurance + residual`; the "residue total" is implicit in `residual`.

### #98. `funded_close_drift_reserve_maps_to_one_stock_or_reservation_class`
**Confidence:** LOW
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_close_lifetime_uses_configured_bound_and_is_not_refreshed` `[SEMI]` — drift reserve scoped to a single close.
**Note:** No harness directly proves the 1-to-1 mapping between drift reserve and stock class.

### #99. `per_class_stock_reconciliation_matches_o1_ledgers_where_available`
**Confidence:** MEDIUM
**Strength:** STRONG
**Harnesses:**
- `proof_v16_stock_reconciliation_decomposes_vault_without_aliasing` `[SYM]` — per-class decomposition without aliasing.
- `proof_v16_public_invariants_reject_hard_global_bounds` `[SEMI]` — global ledger bounds enforced.


## Overclaim risk: HIGH/MEDIUM confidence but WEAK strength

These invariants are marked covered (the listed harnesses are semantically the right ones)
but every cited harness is concrete-input — no symbolic exploration. A reader scanning
the doc would think these are proved; in fact they're only checked at the specific fixture
values the harness picks. For each, either (a) accept that this is what coverage actually
means here, or (b) extend the harness with `kani::any` inputs to make it a real symbolic proof.

- **#7** `source_credit_rate_zero_when_backing_stale_or_exhausted` (confidence: HIGH)
- **#8** `risk_increasing_trade_requires_source_credit_lien` (confidence: HIGH)
- **#9** `source_credit_lien_prevents_double_use_of_same_claim_and_backing` (confidence: HIGH)
- **#10** `source_credit_lien_impairment_forces_deleverage_liquidation_or_recovery` (confidence: HIGH)
- **#18** `insurance_backed_lien_creation_increments_valid_liened_insurance_not_counterparty_backing` (confidence: HIGH)
- **#24** `close_residual_partition_classifies_counterparty_and_insurance_lien_consumption_disjointly` (confidence: MEDIUM)
- **#28** `lien_creatable_predicate_requires_actual_bucket_or_insurance_reservation_capacity` (confidence: HIGH)
- **#32** `lien_creation_increments_correct_aggregate_for_backing_source` (confidence: HIGH)
- **#39** `lien_release_moves_valid_liened_to_fresh_unliened_without_changing_fresh_reserved` (confidence: HIGH)
- **#41** `expired_liened_bucket_marks_liens_impaired_in_bounded_work` (confidence: MEDIUM)
- **#43** `lien_creation_requires_required_backing_le_available_backing` (confidence: HIGH)
- **#44** `locked_face_claim_excluded_from_soft_credit` (confidence: HIGH)
- **#47** `pulled_forward_obligation_credit_not_socialized_again` (confidence: MEDIUM)
- **#53** `settlement_quality_credit_consumes_backing_and_locks_face_claim` (confidence: HIGH)
- **#55** `backing_consumption_reduces_loser_capital_and_preserves_senior_invariants` (confidence: HIGH)
- **#64** `pending_obligation_credit_decrements_origin_residual_once` (confidence: MEDIUM)
- **#66** `participant_finalization_pulls_forward_pending_obligation` (confidence: MEDIUM)
- **#68** `preemptive_close_priority_prevents_hold_and_wait_deadlock` (confidence: MEDIUM)
- **#69** `preempted_close_restart_cannot_double_book_residual` (confidence: MEDIUM)
- **#74** `domain_lock_does_not_block_asset_wide_kf_accrual` (confidence: MEDIUM)
- **#83** `dead_leg_forfeit_uses_bounded_fallback_or_zero_positive_payout` (confidence: HIGH)
- **#89** `pending_obligation_exposure_counted_exactly_once_in_health_test` (confidence: MEDIUM)
- **#92** `cross_close_priority_is_strict_total_order` (confidence: HIGH)

## Gaps and follow-ups

The following invariants have no Kani coverage:

- **#36** `backing_bucket_expiry_after_partial_lien_consumption_does_not_inflate_available` — load-bearing; partial-consumption + expiry interaction is a classic source of accounting drift.
- **#63** `verified_maker_exemption_requires_engine_verified_post_trade_health_cert` — load-bearing if verified-maker is a real lane; the exemption is exactly the kind of policy a Kani harness should pin down.
- **#80** `recovery_fallback_price_within_configured_deviation_envelope` — load-bearing; spec §15 explicitly calls this a fix from v16.8 but no proof anchors it.
- **#81** `recovery_fallback_value_transfer_bound_computed_per_account_and_domain` — load-bearing; same v16.8 fix.
- **#82** `fallback_recovery_rejects_unverified_or_out_of_envelope_reference_price` — load-bearing; closes the loop on #80/#81.

The following LOW-confidence invariants look structurally important and would benefit from dedicated harnesses:

- **#16** `source_credit_insurance_reservation_single_canonical_writer` — structural property that should be witnessed by a "no other writer" harness.
- **#22** `insurance_backed_residual_cure_lien_counts_exactly_once_as_insurance_spent` — cure-path counting is exactly the kind of off-by-one Kani should catch.
- **#26** `internal_insurance_transfer_requires_exactly_one_credit_entry` — flow-proof leg currently implied by totals only.
- **#27** `recovery_consumed_insurance_lien_decrements_v_on_external_payout` — recovery payout decrement is not directly observed.
- **#34, #35** `backing_bucket_expiry_does_not_underflow_available_backing` / `does_not_increase_available_backing_or_credit_rate` — direct expiry-helper edge cases lack dedicated proofs.
- **#48** `claim_bound_bucket_formula_never_understates_source_domain_claims` — bucket-formula lower-bound is foundational for soundness of the credit rate.
- **#49** `claim_bound_bucket_out_of_range_fails_closed_or_rebuckets` — out-of-range bucket handling lacks an explicit fail-closed harness.
- **#50** `credit_rate_recomputation_is_bounded_by_domain_count_and_bucket_count` — bound is implicit in Kani unwinds; no harness ties it to domain/bucket counts.
- **#93** `equal_priority_livelock_impossible` — liveness property; might be out of scope for Kani but worth flagging.
- **#96** `rounding_residue_never_used_for_health_backing_insurance_or_payout` — covered only by indirect insurance-conservation harnesses; deserves a targeted negative proof.
- **#98** `funded_close_drift_reserve_maps_to_one_stock_or_reservation_class` — 1-to-1 mapping is exactly the structural property Kani can pin down.
