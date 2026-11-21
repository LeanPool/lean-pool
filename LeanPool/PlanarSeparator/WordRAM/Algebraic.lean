/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.WordRAM.AlgebraicSpec

/-!
# Counting arithmetic operations

The definitions are in `WordRAM/AlgebraicSpec.lean`; this file proves the lemmas about them.

The cost model of this library is the classical *arithmetic* (algebraic) model: an
algorithm over a ring `R` is charged one unit for every ring operation it performs on
elements of `R`; moving, copying and reindexing data is free.

* `OpCount` records the number of additive operations (additions, subtractions,
  negations) and the number of multiplications separately; `OpCount.total` is their sum.
* `Counted α` is the writer monad over `OpCount`: a value of type `α` together with the
  number of operations spent computing it.  Algorithms are written in this monad, so the
  operation count is a by-product of the algorithm itself and not a separate recurrence.
* `Op.add`, `Op.sub`, `Op.neg`, `Op.mul` are the primitive charged ring operations.
* `Counted.pi` evaluates a family of independent counted computations indexed by a finite
  type, summing their costs.
* `SqMat n R` abbreviates the square matrices `Matrix (Fin n) (Fin n) R`.
* `Mat.add`, `Mat.sub` are entrywise matrix addition and subtraction, charged one
  operation per entry.
-/

namespace WordRAM.Algebraic

@[expose] public section

/-! ### Operation counts -/

deriving instance DecidableEq, Repr for OpCount

attribute [ext] OpCount

namespace OpCount

@[simp] theorem adds_zero : (0 : OpCount).adds = 0 := rfl
@[simp] theorem muls_zero : (0 : OpCount).muls = 0 := rfl
@[simp] theorem adds_add (a b : OpCount) : (a + b).adds = a.adds + b.adds := rfl
@[simp] theorem muls_add (a b : OpCount) : (a + b).muls = a.muls + b.muls := rfl
@[simp] theorem adds_mk (a m : ℕ) : (OpCount.mk a m).adds = a := rfl
@[simp] theorem muls_mk (a m : ℕ) : (OpCount.mk a m).muls = m := rfl

/-- The additive-operation count as an additive monoid homomorphism. -/
def addsHom : OpCount →+ ℕ where
  toFun := adds
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The multiplication count as an additive monoid homomorphism. -/
def mulsHom : OpCount →+ ℕ where
  toFun := muls
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem adds_nsmul (k : ℕ) (a : OpCount) : (k • a).adds = k * a.adds := by
  change addsHom (k • a) = k * addsHom a
  rw [map_nsmul, smul_eq_mul]

@[simp] theorem muls_nsmul (k : ℕ) (a : OpCount) : (k • a).muls = k * a.muls := by
  change mulsHom (k • a) = k * mulsHom a
  rw [map_nsmul, smul_eq_mul]

@[simp] theorem adds_sum {ι : Type*} (s : Finset ι) (f : ι → OpCount) :
    (∑ i ∈ s, f i).adds = ∑ i ∈ s, (f i).adds :=
  map_sum addsHom f s

@[simp] theorem muls_sum {ι : Type*} (s : Finset ι) (f : ι → OpCount) :
    (∑ i ∈ s, f i).muls = ∑ i ∈ s, (f i).muls :=
  map_sum mulsHom f s

@[simp] theorem total_mk (a m : ℕ) : (OpCount.mk a m).total = a + m := rfl

@[simp] theorem total_zero : (0 : OpCount).total = 0 := rfl

@[simp] theorem total_add (a b : OpCount) : (a + b).total = a.total + b.total := by
  simp only [total, adds_add, muls_add]; omega

end OpCount

/-! ### The counting monad -/

universe u v

namespace Counted

@[simp] theorem val_pure {α : Type u} (a : α) : (pure a : Counted α).val = a := rfl
@[simp] theorem cost_pure {α : Type u} (a : α) : (pure a : Counted α).cost = 0 := rfl

@[simp] theorem val_bind {α β : Type u} (x : Counted α) (f : α → Counted β) :
    (x >>= f).val = (f x.val).val := rfl

@[simp] theorem cost_bind {α β : Type u} (x : Counted α) (f : α → Counted β) :
    (x >>= f).cost = x.cost + (f x.val).cost := rfl

@[simp] theorem val_map {α β : Type u} (f : α → β) (x : Counted α) :
    (f <$> x).val = f x.val := rfl

@[simp] theorem cost_map {α β : Type u} (f : α → β) (x : Counted α) :
    (f <$> x).cost = x.cost := by
  change x.cost + 0 = x.cost
  exact add_zero _

@[ext]
theorem ext' {α : Type u} {x y : Counted α} (h₁ : x.val = y.val) (h₂ : x.cost = y.cost) :
    x = y := by
  cases x; cases y; cases h₁; cases h₂; rfl

instance : LawfulMonad Counted := LawfulMonad.mk'
  (id_map := fun x => by ext <;> simp)
  (pure_bind := fun x f => by ext <;> simp)
  (bind_assoc := fun x f g => by ext <;> simp [add_assoc])

/-- Charge `c` operations without computing anything. -/
def tick (c : OpCount) : Counted PUnit := ⟨PUnit.unit, c⟩

@[simp] theorem val_tick (c : OpCount) : (tick c).val = PUnit.unit := rfl
@[simp] theorem cost_tick (c : OpCount) : (tick c).cost = c := rfl

@[simp] theorem val_pi {ι : Type v} [Fintype ι] {α : ι → Type u} (f : (i : ι) → Counted (α i)) :
    (pi f).val = fun i => (f i).val := rfl

@[simp] theorem cost_pi {ι : Type v} [Fintype ι] {α : ι → Type u}
    (f : (i : ι) → Counted (α i)) : (pi f).cost = ∑ i, (f i).cost := rfl

/-- `pi` of a family whose members all cost the same `c`. -/
theorem cost_pi_const {ι : Type v} [Fintype ι] {α : ι → Type u}
    (f : (i : ι) → Counted (α i)) (c : OpCount) (h : ∀ i, (f i).cost = c) :
    (pi f).cost = Fintype.card ι • c := by
  simp [h, Finset.card_univ]

end Counted

/-! ### Primitive ring operations -/

namespace Op

variable {R : Type u}

@[simp] theorem val_add [Add R] (a b : R) : (add a b).val = a + b := rfl
@[simp] theorem cost_add [Add R] (a b : R) : (add a b).cost = ⟨1, 0⟩ := rfl
@[simp] theorem val_sub [Sub R] (a b : R) : (sub a b).val = a - b := rfl
@[simp] theorem cost_sub [Sub R] (a b : R) : (sub a b).cost = ⟨1, 0⟩ := rfl
@[simp] theorem val_neg [Neg R] (a : R) : (neg a).val = -a := rfl
@[simp] theorem cost_neg [Neg R] (a : R) : (neg a).cost = ⟨1, 0⟩ := rfl
@[simp] theorem val_mul [Mul R] (a b : R) : (mul a b).val = a * b := rfl
@[simp] theorem cost_mul [Mul R] (a b : R) : (mul a b).cost = ⟨0, 1⟩ := rfl

end Op

/-! ### Entrywise matrix operations -/

namespace Mat

variable {R : Type u} {m : Type v} {n : Type v} [Fintype m] [Fintype n]

@[simp] theorem val_add [Add R] (A B : Matrix m n R) : (add A B).val = A + B := rfl

@[simp] theorem val_sub [Sub R] (A B : Matrix m n R) : (sub A B).val = A - B := rfl

@[simp] theorem cost_add [Add R] (A B : Matrix m n R) :
    (add A B).cost = ⟨Fintype.card m * Fintype.card n, 0⟩ := by
  ext <;> simp [add, Finset.card_univ]

@[simp] theorem cost_sub [Sub R] (A B : Matrix m n R) :
    (sub A B).cost = ⟨Fintype.card m * Fintype.card n, 0⟩ := by
  ext <;> simp [sub, Finset.card_univ]

end Mat

end

end WordRAM.Algebraic
