/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Basic

/-!
# Specification: counting arithmetic operations

The arithmetic (algebraic) cost model, as definitions only; the lemmas about them are in
`WordRAM/Algebraic.lean`, which imports this file. It imports only Mathlib.

An algorithm over a ring `R` is written in the writer monad `Counted`: a value together with the
number of ring operations spent computing it. The only operations that charge anything are the
primitives `Op.add`, `Op.sub`, `Op.neg` (one additive operation each) and `Op.mul` (one
multiplication); `Counted.pi` runs a family of independent computations and adds up their costs,
and `Mat.add`, `Mat.sub` are entrywise matrix operations, one additive operation per entry.
Moving, copying and reindexing data is free. A cost statement is therefore about one explicit
algorithm, and it is meaningful only as far as that algorithm performs its ring operations
through these primitives, which is checked by reading its definition.
-/

@[expose] public section

namespace WordRAM.Algebraic

/-! ### Operation counts -/

/-- A count of arithmetic operations: `adds` counts additions, subtractions and negations,
`muls` counts multiplications. -/
structure OpCount where
  /-- Number of additive operations (additions, subtractions, negations). -/
  adds : ℕ
  /-- Number of multiplications. -/
  muls : ℕ

namespace OpCount

instance : Zero OpCount := ⟨⟨0, 0⟩⟩

instance : Add OpCount := ⟨fun a b => ⟨a.adds + b.adds, a.muls + b.muls⟩⟩

instance : AddCommMonoid OpCount where
  add_assoc a b c :=
    congrArg₂ OpCount.mk (Nat.add_assoc a.adds b.adds c.adds) (Nat.add_assoc a.muls b.muls c.muls)
  zero_add a := congrArg₂ OpCount.mk (Nat.zero_add a.adds) (Nat.zero_add a.muls)
  add_zero a := congrArg₂ OpCount.mk (Nat.add_zero a.adds) (Nat.add_zero a.muls)
  add_comm a b := congrArg₂ OpCount.mk (Nat.add_comm a.adds b.adds) (Nat.add_comm a.muls b.muls)
  nsmul := nsmulRec

/-- Total number of arithmetic operations. -/
def total (c : OpCount) : ℕ := c.adds + c.muls

/-- One additive operation. -/
abbrev oneAdd : OpCount := ⟨1, 0⟩

/-- One multiplication. -/
abbrev oneMul : OpCount := ⟨0, 1⟩

end OpCount

/-! ### The counting monad -/

universe u v

/-- A computation in the arithmetic cost model: a result `val` together with the number of
ring operations `cost` performed to obtain it (the writer monad over `OpCount`). -/
structure Counted (α : Type u) where
  /-- The computed value. -/
  val : α
  /-- The number of operations spent. -/
  cost : OpCount

namespace Counted

instance : Monad Counted where
  pure a := ⟨a, 0⟩
  bind x f := ⟨(f x.val).val, x.cost + (f x.val).cost⟩

/-- Run a family of independent counted computations indexed by a finite type: the value is
the family of values, the cost is the sum of the costs. -/
def pi {ι : Type v} [Fintype ι] {α : ι → Type u} (f : (i : ι) → Counted (α i)) :
    Counted ((i : ι) → α i) :=
  ⟨fun i => (f i).val, ∑ i, (f i).cost⟩

end Counted

/-! ### Primitive ring operations -/

namespace Op

variable {R : Type u}

/-- Addition, charged one additive operation. -/
def add [Add R] (a b : R) : Counted R := ⟨a + b, OpCount.oneAdd⟩

/-- Subtraction, charged one additive operation. -/
def sub [Sub R] (a b : R) : Counted R := ⟨a - b, OpCount.oneAdd⟩

/-- Negation, charged one additive operation. -/
def neg [Neg R] (a : R) : Counted R := ⟨-a, OpCount.oneAdd⟩

/-- Multiplication, charged one multiplication. -/
def mul [Mul R] (a b : R) : Counted R := ⟨a * b, OpCount.oneMul⟩

end Op

/-! ### Entrywise matrix operations -/

/-- Square matrices of size `n` over `R`. -/
abbrev SqMat (n : ℕ) (R : Type u) : Type u := Matrix (Fin n) (Fin n) R

namespace Mat

variable {R : Type u} {m : Type v} {n : Type v} [Fintype m] [Fintype n]

/-- Entrywise matrix addition, one additive operation per entry. -/
def add [Add R] (A B : Matrix m n R) : Counted (Matrix m n R) :=
  Counted.pi fun i => Counted.pi fun j => Op.add (A i j) (B i j)

/-- Entrywise matrix subtraction, one additive operation per entry. -/
def sub [Sub R] (A B : Matrix m n R) : Counted (Matrix m n R) :=
  Counted.pi fun i => Counted.pi fun j => Op.sub (A i j) (B i j)

end Mat

end WordRAM.Algebraic

end
