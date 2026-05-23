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

Lean coverage (Phase 1 of VERIFICATION_PLAN.md, complete):
  Percolator/WideMath.lean   — wideningMulU128_correct + 4 corollaries
  Percolator/U256.lean       — toNat_lt, toNat_mul, both_hi_nonzero_overflows,
                               checkedMul_both_hi_zero, checkedMul_correct,
                               divRemU256_correct (+ quotient/remainder bounds)
  Percolator/I256.lean       — rawNat_lt_TWO_256, sign_iff_raw, negLimbs_raw,
                               checkedNeg_correct, absU256_correct,
                               checkedMulInt_some / _none / _eq_mul
  Percolator/CreditRate.lean — 7 theorems closing §14 #42, parts of #1 and #50
  Percolator/BoundArith.lean — 8 theorems closing §14 #15

Refinement proptests (tests/proofs_v16_lean_refinement.rs) bridge each Lean
theorem to the production Rust impl:
  u256_checked_mul_matches_biguint_spec
  mul_div_floor_u256_matches_biguint_spec_u128_inputs
  div_rem_u256_matches_biguint_spec
  i256_checked_neg_matches_bigint_spec
  i256_abs_u256_matches_bigint_spec
  i256_checked_mul_matches_bigint_spec
```

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
- `proof_v16_account_source_claim_equity_zero_backing_gives_zero_credit` `[CON]` — zero-backing fixture.
- `proof_v16_account_source_claim_equity_full_backing_gives_full_credit` `[CON]` — full-backing fixture.
- `proof_v16_account_source_claim_equity_uses_source_credit_rate` `[CON]` — account-level equity scales by the rate.

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
- `proof_v16_counterparty_lien_lifecycle_preserves_backing_encumbrance` `[SEMI]` — backing encumbrance moves on lien lifecycle without touching value totals.

### #4. `source_credit_lien_creation_moves_no_quote_value`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_counterparty_lien_lifecycle_preserves_backing_encumbrance` `[SEMI]` — lien create/consume/impair holds `vault` constant; only reservation counters move.
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
- `proof_v16_expired_fresh_backing_requires_refresh_before_source_credit_conversion` `[CON]` — stale backing blocks oracle-driven credit growth.
**Note:** No harness directly stress-tests an oracle pump producing claim growth without matching backing, but the rate cap rules it out.

### #7. `source_credit_rate_zero_when_backing_stale_or_exhausted`
**Confidence:** HIGH
**Strength:** WEAK
**Harnesses:**
- `proof_v16_expired_fresh_backing_requires_refresh_before_source_credit_conversion` `[CON]` — stale fresh backing forces `Err(Stale)` on conversion.
- `proof_v16_account_source_claim_equity_zero_backing_gives_zero_credit` `[CON]` — exhausted backing produces zero credit rate.

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
- `proof_v16_counterparty_lien_lifecycle_preserves_backing_encumbrance` `[SEMI]` — `fresh_reserved_backing_num` mirrors true locked equity through lifecycle.

### #12. `backing_expiry_buckets_exclude_stale_contributions_without_full_scan`
**Confidence:** MEDIUM
**Strength:** STRONG
**Harnesses:**
- `proof_v16_expired_fresh_backing_requires_refresh_before_source_credit_conversion` `[CON]` — expired backing excluded from credit conversion.
- `proof_v16_permissionless_crank_does_not_require_full_market_scan` `[SYM]` — bounded-work crank does not scan all accounts.
**Note:** No direct harness on `backing_expiry_buckets` data structure; coverage is by observable effect.

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
- `proof_v16_ceil_div_positive_checked_matches_small_reference` (arithmetic) — ceil-div primitive matches reference.
- `proof_v16_mul_div_ceil_u256_is_floor_plus_remainder_indicator` (arithmetic) — wide mul-div ceil correctness.

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

### #23. `insurance_backed_lien_never_counts_as_both_support_and_insurance`
**Confidence:** MEDIUM
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_insurance_source_credit_lien_aggregate_tracks_account_backing_split` `[CON]` — aggregate proof partitions face-claim locked between counterparty and insurance categories.
- `proof_v16_dead_leg_forfeit_books_loss_to_opposing_domain_only` `[SEMI]` — loss attribution is disjoint.
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
- `proof_v16_counterparty_lien_lifecycle_preserves_backing_encumbrance` `[SEMI]` — bucket helper invariants hold.
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
- `proof_v16_counterparty_lien_lifecycle_preserves_backing_encumbrance` `[SEMI]` — counterparty lifecycle matches predicate.
- `proof_v16_insurance_reservation_lifecycle_preserves_encumbrance` `[SEMI]` — insurance lifecycle matches predicate.
**Note:** Mostly a restatement of #29; same harnesses apply.

### #34. `backing_bucket_expiry_does_not_underflow_available_backing`
**Confidence:** LOW
**Strength:** WEAK
**Harnesses:**
- `proof_v16_expired_fresh_backing_requires_refresh_before_source_credit_conversion` `[CON]` — expiry path is observed without underflow.
**Note:** No harness directly exercises the `expire_backing_bucket` helper edge cases.

### #35. `backing_bucket_expiry_does_not_increase_available_backing_or_credit_rate`
**Confidence:** LOW
**Strength:** WEAK
**Harnesses:**
- `proof_v16_expired_fresh_backing_requires_refresh_before_source_credit_conversion` `[CON]` — credit rate after expiry does not exceed pre-expiry rate.
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
- `proof_v16_counterparty_lien_lifecycle_preserves_backing_encumbrance` `[SEMI]` — consume branch decrements `valid_liened_backing_num` exactly once.

### #38. `lien_consumption_removes_backing_from_fresh_reserved_and_claim_bound`
**Confidence:** MEDIUM
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_counterparty_lien_lifecycle_preserves_backing_encumbrance` `[SEMI]` — consume reduces `fresh_reserved_backing_num` by `lien` and sets `spent_backing_num = lien`.
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
- `proof_v16_counterparty_lien_lifecycle_preserves_backing_encumbrance` `[SEMI]` — bucket-sum recomputation observed.

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
- `proof_v16_account_source_claim_equity_zero_backing_gives_zero_credit` `[CON]` — Rust impl at the zero-backing fixture.

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
- `proof_v16_account_source_claim_equity_uses_source_credit_rate` `[CON]` — formula applied at account level.
- `proof_v16_public_invariants_reject_scaled_junior_bound_cache_mismatch` `[SEMI]` — cached scaled bound must match formula.
**Note:** No harness targets the bucket-formula's lower-bound property directly.

### #49. `claim_bound_bucket_out_of_range_fails_closed_or_rebuckets`
**Confidence:** LOW
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_public_invariants_reject_scaled_junior_bound_cache_mismatch` `[SEMI]` — cache desync rejected.
**Note:** No targeted harness on out-of-range bucket re-bucketing.

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
- `proof_v16_dead_leg_forfeit_books_loss_to_opposing_domain_only` `[SEMI]` — dead-leg equivalent.

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
- `proof_v16_health_certificate_bound_to_market_epochs_and_prices` `[SEMI]` — certs scoped to epochs; mismatch fails closed.
- `proof_v16_full_refresh_clears_stale_certificate` `[CON]` — full refresh required.

### #62. `full_account_refresh_required_for_favorable_actions`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_favorable_action_requires_current_full_refresh` `[CON]` — direct claim.
- `proof_v16_health_certificate_bound_to_market_epochs_and_prices` `[SEMI]` — cert binding.
- `proof_v16_favorable_locks_block_released_pnl_conversion_before_mutation` `[SEMI]` — locks block favorable actions.

### #63. `verified_maker_exemption_requires_engine_verified_post_trade_health_cert`
**Confidence:** NONE
**Strength:** N/A
**Harnesses:** _No matching harness found._
**Note:** No proof targeting a "verified maker" exemption path; if implemented, would assert that the exemption requires engine-verified post-trade cert.

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
- `proof_v16_b_residual_booking_makes_durable_progress_or_fails_closed` `[SEMI]` — booking is bounded and durable.
**Note:** Big-O complexity is not explicitly modeled; Kani's `unwind` bound implies boundedness.

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
- `proof_v16_b_residual_booking_makes_durable_progress_or_fails_closed` `[SEMI]` — durable progress invariant.

### #72. `cure_and_cancel_checks_before_consuming_new_deposit`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_cure_and_cancel_close_releases_barrier_and_escrow_before_irreversible_progress` `[SEMI]` — happy path.
- `proof_v16_cure_and_cancel_rejects_irreversible_progress_before_deposit_mutation` `[SEMI]` — rejection path leaves deposit untouched.

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
- `proof_v16_account_b_chunk_either_advances_or_fails_closed` `[SEMI]` — exact conservation per chunk.
- `proof_v16_repeated_account_b_chunks_complete_bounded_small_residual` `[SEMI]` — repeated chunks complete with bounded remainder.
- `proof_v16_b_residual_booking_makes_durable_progress_or_fails_closed` `[SEMI]` — B residual booking exactness.

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

### #79. `resolved_receipt_underbound_halts_payout_or_recovers`
**Confidence:** HIGH
**Strength:** MEDIUM
**Harnesses:**
- `proof_v16_unfinalized_resolved_receipt_blocks_account_close_until_topup` `[SEMI]` — under-bound receipt blocks close until top-up.
- `proof_v16_resolved_receipt_tracks_paid_effective_and_bound_refinement_topup` `[SEMI]` — top-up refinement path.
- `proof_v16_pnl_pos_bound_tot_prevents_lazy_positive_pnl_first_mover_overpay` `[CON]` — under-bound first-mover overpay prevented.

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
- `proof_v16_dead_leg_forfeit_books_loss_to_opposing_domain_only` `[SEMI]` — loss booked to opposing (bankruptcy) domain only.
- `proof_v16_dead_leg_forfeit_partial_b_progress_does_not_detach` `[CON]` — partial progress remains on the same domain.

### #85. `no_single_instruction_full_market_scan_required`
**Confidence:** HIGH
**Strength:** STRONG
**Harnesses:**
- `proof_v16_permissionless_crank_does_not_require_full_market_scan` `[SYM]` — direct match.
- `proof_v16_worst_case_hinted_progress_actions_are_total_and_bounded` `[SEMI]` — worst-case hinted progress bounded.

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
- `proof_v16_b_residual_booking_makes_durable_progress_or_fails_closed` `[SEMI]` — booking triggers recompute or close.
- `proof_v16_passive_backing_consumption_preserves_senior_accounting_without_wrapper_injection` `[CON]` — claim bound recomputed conservatively.

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
