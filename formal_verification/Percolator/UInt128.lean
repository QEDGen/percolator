/-
  Percolator.UInt128 — Nat-based model of `u128` arithmetic.

  Lean's stdlib has `BitVec 128` but the production Rust code (`wide_math.rs`)
  is written in terms of u128 wrapping arithmetic plus explicit shifts and
  truncations between u64 / u128. The cleanest Lean model treats u128 as
  `Nat` with explicit `% TWO_128` reductions that mirror the wrapping
  behavior at well-defined boundaries.

  Why not `BitVec 128`?
  - Schoolbook decomposition is more natural over `Nat` (the spec is "split
    into u64 halves then sum", which is `a = (a / 2^64) * 2^64 + a % 2^64`).
  - Mathlib's `ring` / `omega` / `nlinarith` tactics target `Nat`/`Int`
    directly; `BitVec` proofs route through `BitVec.toNat` anyway.
  - The price: every operation that *could* overflow gets an explicit
    `% TWO_128`. The reader sees exactly where wrapping happens.

  Why not `Fin (2^128)`?
  - `Fin n` makes the bound a precondition of the type but every operation
    has to discharge the bound; lots of `Fin.mk` plumbing.
  - `Nat` plus a per-theorem `a < TWO_128` hypothesis is cheaper.

  This file defines the width constants and the u128↔u64 chunking ops
  used by `wide_math.rs::widening_mul_u128`. Operations that wrap (add,
  mul) are spelled inline in `Percolator.WideMath` rather than abstracted
  here, so each `% TWO_128` is visible at the use site.
-/

namespace Percolator.Spec

-- ============================================================================
-- Width constants
-- ============================================================================

/-- 2^64 — the chunk boundary for splitting u128 into two u64 halves. -/
def TWO_64 : Nat := 2^64

/-- 2^128 — the wrap point for u128 arithmetic. -/
def TWO_128 : Nat := 2^128

/-- 2^256 — the wrap point for u256 arithmetic. -/
def TWO_256 : Nat := 2^256

-- ============================================================================
-- u128 ↔ u64 chunking
-- ============================================================================

/-- Low 64 bits of a value (mirrors Rust `a as u64 as u128`). -/
def u64Lo (a : Nat) : Nat := a % TWO_64

/-- High 64 bits of a u128 value (mirrors Rust `(a >> 64) as u64 as u128`).
    Under `a < TWO_128`, the result is in `[0, TWO_64)`. -/
def u64Hi (a : Nat) : Nat := (a / TWO_64) % TWO_64

/-- Reconstruct a u128 from its (lo64, hi64) chunks. -/
def fromChunks (lo hi : Nat) : Nat := lo % TWO_64 + (hi % TWO_64) * TWO_64

-- ============================================================================
-- Predicates
-- ============================================================================

/-- Predicate: value fits in a u128. -/
def isU128 (a : Nat) : Prop := a < TWO_128

/-- Predicate: value fits in a u64. -/
def isU64 (a : Nat) : Prop := a < TWO_64

end Percolator.Spec
