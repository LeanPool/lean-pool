/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

import Mathlib.Analysis.SpecialFunctions.Bernstein

public import LeanPool.Monlib4.RepTheory.AutMat

/-!
# Algebra of two matrix blocks

Product equivalences, swaps, and inner automorphisms used by two-block quantum graphs.
-/

@[expose] public section


/-- The algebra equivalence between a two-block product of matrix algebras and the matching
  `PiMat`. -/
def MatProdAlgEquivPiMat (n' : Fin 2 → Type*) [Π i, Fintype (n' i)] [Π i, DecidableEq (n' i)] :
  (Matrix (n' 0) (n' 0) ℂ × Matrix (n' 1) (n' 1) ℂ)
    ≃ₐ[ℂ]
  PiMat ℂ (Fin 2) n' :=
matrixPiFinTwoAlgEquivProd.symm

/-- Swap the two types in a `Fin 2`-indexed family. -/
abbrev PiFinTwo.swap (n' : Fin 2 → Type*) :
  Fin 2 → Type _ :=
fun i => if i = 0 then (n' 1) else (n' 0)

instance {n' : Fin 2 → Type*} [Π i, Fintype (n' i)] :
  Π i, Fintype ((PiFinTwo.swap n') i) :=
fun i => by
  unfold PiFinTwo.swap
  split_ifs <;> infer_instance
instance {n' : Fin 2 → Type*} [Π i, DecidableEq (n' i)] :
  Π i, DecidableEq ((PiFinTwo.swap n') i) :=
fun i => by
  unfold PiFinTwo.swap
  split_ifs <;> infer_instance

/-- The swapped product-to-`PiMat` equivalence for two matrix blocks. -/
def MatProdAlgEquivPiMatSwap (n' : Fin 2 → Type*) [Π i, Fintype (n' i)] [Π i,
  DecidableEq (n' i)] :
  (Matrix (n' 1) (n' 1) ℂ × Matrix (n' 0) (n' 0) ℂ)
    ≃ₐ[ℂ]
  PiMat ℂ (Fin 2) (PiFinTwo.swap n') :=
MatProdAlgEquivPiMat (PiFinTwo.swap n')

/-- Swap the two factors of a product as an algebra equivalence. -/
@[simps]
def Prod.swapAlgEquiv
  (α β : Type*) [Semiring α] [Semiring β] [Algebra ℂ α] [Algebra ℂ β] :
    (α × β) ≃ₐ[ℂ] (β × α) where
  toFun x := x.swap
  invFun x := x.swap
  left_inv _ := by simp
  right_inv _ := by simp
  map_add' _ _ := by simp
  map_mul' _ _ := by simp
  commutes' _ := by simp

/-- Swap the two blocks of a `PiMat` indexed by `Fin 2`. -/
def PiMatFinTwoSwapAlgEquiv
  {n' : Fin 2 → Type*} [Π i, Fintype (n' i)] [Π i, DecidableEq (n' i)] :
    PiMat ℂ (Fin 2) n' ≃ₐ[ℂ] PiMat ℂ (Fin 2) (PiFinTwo.swap n') :=
(MatProdAlgEquivPiMat n').symm.trans ((Prod.swapAlgEquiv _ _).trans
  (MatProdAlgEquivPiMatSwap n'))

/-- The constant `Fin 2`-indexed family with value `n`. -/
abbrev PiFinTwoSame (n : Type*) :
  Fin 2 → Type _ :=
fun i => let _ := i; n

instance {n : Type*} [Fintype n] :
  Π i, Fintype ((PiFinTwoSame n) i) :=
fun i => by infer_instance
instance {n : Type*} [DecidableEq n] :
  Π i, DecidableEq ((PiFinTwoSame n) i) :=
fun i => by infer_instance

theorem PiMatFinTwoSwapAlgEquiv_apply {n' : Fin 2 → Type*} [Π i, Fintype (n' i)] [Π i,
  DecidableEq (n' i)]
  (x : Matrix (n' 0) (n' 0) ℂ) (y : Matrix (n' 1) (n' 1) ℂ) :
  PiMatFinTwoSwapAlgEquiv (MatProdAlgEquivPiMat n' (x, y))
    = MatProdAlgEquivPiMat _ (y, x) :=
rfl

lemma PiFinTwoSame_swap {n : Type*} :
  PiFinTwo.swap (PiFinTwoSame n) = PiFinTwoSame n :=
by ext; simp only [ite_self, Fin.isValue]

/-- Swap the two identical matrix blocks of a `PiMat` indexed by `Fin 2`. -/
def PiMatFinTwoSameSwapAlgEquiv
  {n : Type*} [Fintype n] [DecidableEq n] :
    PiMat ℂ (Fin 2) (PiFinTwoSame n) ≃ₐ[ℂ] PiMat ℂ (Fin 2) (PiFinTwoSame n) :=
(MatProdAlgEquivPiMat (PiFinTwoSame n)).symm.trans ((Prod.swapAlgEquiv _ _).trans
  (MatProdAlgEquivPiMat (PiFinTwoSame n)))


theorem PiMatFinTwoSameSwapAlgEquiv_apply {n : Type*} [Fintype n] [DecidableEq n]
  (x : Matrix n n ℂ) (y : Matrix n n ℂ) :
  PiMatFinTwoSameSwapAlgEquiv (MatProdAlgEquivPiMat (PiFinTwoSame n) (x, y))
    = MatProdAlgEquivPiMat _ (y, x) :=
rfl

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem AlgEquiv.prodMap_inner_of {K R₁ R₂ : Type*} [CommSemiring K]
  [Semiring R₁] [Semiring R₂] [Algebra K R₁] [Algebra K R₂]
  {f : R₁ ≃ₐ[K] R₁} (hf : f.IsInner) {g : R₂ ≃ₐ[K] R₂} (hg : g.IsInner) :
  (f.prodMap g).IsInner := by
  rw [AlgEquiv.prod_isInner_iff_prodMap]
  obtain ⟨U, hU, rfl⟩ := hf
  obtain ⟨V, hV, rfl⟩ := hg
  exact ⟨U, hU, V, hV, rfl⟩

/-- Invertibility is preserved by the product-to-`PiMat` equivalence in the same-block case. -/
@[reducible]
def MatProdAlgEquivPiMatSameInvertibleOf {U : Matrix n n ℂ × Matrix n n ℂ}
  (hU : Invertible U) :
  Invertible ((MatProdAlgEquivPiMat (PiFinTwoSame n)) U) := by
  use (MatProdAlgEquivPiMat _ ⅟U) <;>
  simp only [← map_mul, invOf_mul_self, mul_invOf_self, map_one]
