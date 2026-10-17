/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite coefficient tensors and their algebraic transformations. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K X Y Z U V W : Type*} [CommSemiring K]

def cyclic (T : Tensor K X Y Z) : Tensor K Y Z X :=
  fun y z x => T x y z

theorem RankAtMost.cyclic {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) : RankAtMost (Tensor.cyclic T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨b, c, a, ?_⟩
  funext y z x
  simp only [Tensor.cyclic, rankOne]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def directSumProductEquiv (ι κ X U : Type*) :
    ((ι × κ) × (X × U)) ≃ ((ι × X) × (κ × U)) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem directSum_product {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (T : ι → Tensor K X Y Z) (S : κ → Tensor K U V W) :
    pullback (directSumProductEquiv ι κ X U)
      (directSumProductEquiv ι κ Y V) (directSumProductEquiv ι κ Z W)
      (product (directSum T) (directSum S)) =
      directSum (fun i : ι × κ => product (T i.1) (S i.2)) := by
  funext x y z
  change
    (if x.1.1 = y.1.1 ∧ x.1.1 = z.1.1 then
      T x.1.1 x.2.1 y.2.1 z.2.1 else 0) *
    (if x.1.2 = y.1.2 ∧ x.1.2 = z.1.2 then
      S x.1.2 x.2.2 y.2.2 z.2.2 else 0) =
    if x.1 = y.1 ∧ x.1 = z.1 then
      T x.1.1 x.2.1 y.2.1 z.2.1 * S x.1.2 x.2.2 y.2.2 z.2.2 else 0
  have hguard : (x.1 = y.1 ∧ x.1 = z.1) ↔
      (x.1.1 = y.1.1 ∧ x.1.1 = z.1.1) ∧
      (x.1.2 = y.1.2 ∧ x.1.2 = z.1.2) := by
    constructor
    · intro h
      exact ⟨⟨congrArg Prod.fst h.1, congrArg Prod.fst h.2⟩,
        ⟨congrArg Prod.snd h.1, congrArg Prod.snd h.2⟩⟩
    · intro h
      exact ⟨Prod.ext h.1.1 h.2.1, Prod.ext h.1.2 h.2.2⟩
  by_cases hi : x.1.1 = y.1.1 ∧ x.1.1 = z.1.1
  · by_cases hk : x.1.2 = y.1.2 ∧ x.1.2 = z.1.2
    · simp only [ite_eq_left hi, ite_eq_left hk, ite_eq_left (hguard.mpr ⟨hi, hk⟩)]
    · have hfull : ¬ (x.1 = y.1 ∧ x.1 = z.1) := fun h => hk (hguard.mp h).2
      simp only [ite_eq_left hi, ite_eq_right hk, ite_eq_right hfull, mul_zero]
  · have hfull : ¬ (x.1 = y.1 ∧ x.1 = z.1) := fun h => hi (hguard.mp h).1
    simp only [ite_eq_right hi, ite_eq_right hfull, zero_mul]

theorem RankAtMost.directSum_product {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {T : ι → Tensor K X Y Z} {S : κ → Tensor K U V W} {r s : ℕ}
    (hT : RankAtMost (directSum T) r) (hS : RankAtMost (directSum S) s) :
    RankAtMost (directSum (fun i : ι × κ => Tensor.product (T i.1) (S i.2))) (r * s) := by
  have h := (hT.product hS).pullback (directSumProductEquiv ι κ X U)
    (directSumProductEquiv ι κ Y V) (directSumProductEquiv ι κ Z W)
  rw [Tensor.directSum_product] at h
  exact h

theorem directSum_pullback {ι X' Y' Z' : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    pullback (fun x : ι × X' => (x.1, fx x.2))
      (fun y : ι × Y' => (y.1, fy y.2)) (fun z : ι × Z' => (z.1, fz z.2))
      (directSum T) = directSum (fun i => pullback fx fy fz (T i)) := rfl

theorem RankAtMost.directSum_pullback {ι X' Y' Z' : Type*} [DecidableEq ι]
    {T : ι → Tensor K X Y Z} {r : ℕ} (h : RankAtMost (directSum T) r)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    RankAtMost (directSum (fun i => Tensor.pullback fx fy fz (T i))) r :=
  h.pullback (fun x : ι × X' => (x.1, fx x.2))
    (fun y : ι × Y' => (y.1, fy y.2)) (fun z : ι × Z' => (z.1, fz z.2))

theorem cyclic_directSum {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) :
    cyclic (directSum T) = directSum (fun i => cyclic (T i)) := by
  funext x y z
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  rcases z with ⟨k, z⟩
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      simp [cyclic, directSum]
    · simp [cyclic, directSum, hik, Ne.symm hik]
  · by_cases hki : k = i
    · subst k
      simp [cyclic, directSum, hij]
    · simp [cyclic, directSum, hij, hki]

theorem RankAtMost.directSum_cyclic {ι : Type*} [DecidableEq ι]
    {T : ι → Tensor K X Y Z} {r : ℕ} (h : RankAtMost (directSum T) r) :
    RankAtMost (directSum (fun i => Tensor.cyclic (T i))) r := by
  rw [← Tensor.cyclic_directSum]
  exact h.cyclic

def directSumPowerEquiv (ι X : Type*) (n : ℕ) :
    ((Fin n → ι) × (Fin n → X)) ≃ (Fin n → ι × X) where
  toFun x i := (x.1 i, x.2 i)
  invFun x := (fun i => (x i).1, fun i => (x i).2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem directSum_power {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) (n : ℕ) :
    pullback (directSumPowerEquiv ι X n) (directSumPowerEquiv ι Y n)
      (directSumPowerEquiv ι Z n) (power (directSum T) n) =
      directSum (fun f : Fin n → ι =>
        fun x y z => ∏ i, T (f i) (x i) (y i) (z i)) := by
  funext x y z
  change (∏ i, if x.1 i = y.1 i ∧ x.1 i = z.1 i then
      T (x.1 i) (x.2 i) (y.2 i) (z.2 i) else 0) =
    if x.1 = y.1 ∧ x.1 = z.1 then
      ∏ i, T (x.1 i) (x.2 i) (y.2 i) (z.2 i) else 0
  simp only [Fintype.prod_ite_zero, forall_and, ← funext_iff]

theorem directSum_const_power {ι : Type*} [DecidableEq ι]
    (T : Tensor K X Y Z) (n : ℕ) :
    pullback (directSumPowerEquiv ι X n) (directSumPowerEquiv ι Y n)
      (directSumPowerEquiv ι Z n) (power (directSum (fun _ : ι => T)) n) =
      directSum (fun _ : Fin n → ι => power T n) :=
  directSum_power (fun _ : ι => T) n

theorem RankAtMost.directSum_const_of_power {ι : Type*} [DecidableEq ι]
    {T : Tensor K X Y Z} {n R : ℕ}
    (h : RankAtMost (Tensor.power (directSum (fun _ : ι => T)) n) R) :
    RankAtMost (directSum (fun _ : Fin n → ι => Tensor.power T n)) R := by
  have h' := h.pullback (directSumPowerEquiv ι X n)
    (directSumPowerEquiv ι Y n) (directSumPowerEquiv ι Z n)
  rw [Tensor.directSum_const_power] at h'
  exact h'

theorem RankAtMost.directSum_const_power {ι : Type*} [DecidableEq ι]
    {T : Tensor K X Y Z} {r : ℕ} (h : RankAtMost (directSum (fun _ : ι => T)) r)
    (n : ℕ) : RankAtMost (directSum (fun _ : Fin n → ι => Tensor.power T n)) (r ^ n) :=
  (h.power n).directSum_const_of_power

section Rectangular

variable {A B C : Type*}

def rectangularSquareX (A B C : Type*) :
    ((A × B × C) × (A × B × C)) ≃ (((A × B) × (B × C)) × (C × A)) where
  toFun x := (((x.1.1, x.2.2.1), (x.1.2.1, x.2.2.2)), (x.1.2.2, x.2.1))
  invFun x := ((x.1.1.1, x.1.2.1, x.2.1), (x.2.2, x.1.1.2, x.1.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def rectangularSquareY (A B C : Type*) :
    ((A × B × C) × (A × B × C)) ≃ (((B × C) × (C × A)) × (A × B)) where
  toFun y := (((y.1.2.1, y.2.2.2), (y.1.2.2, y.2.1)), (y.1.1, y.2.2.1))
  invFun y := ((y.2.1, y.1.1.1, y.1.2.1), (y.1.2.2, y.2.2, y.1.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

def rectangularSquareZ (A B C : Type*) :
    ((A × B × C) × (A × B × C)) ≃ (((C × A) × (A × B)) × (B × C)) where
  toFun z := (((z.1.2.2, z.2.1), (z.1.1, z.2.2.1)), (z.1.2.1, z.2.2.2))
  invFun z := ((z.1.2.1, z.2.1, z.1.1.1), (z.1.1.2, z.1.2.2, z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem matrixCoefficients_directSum_rank_of_power
    {ι : Type*} [DecidableEq ι] {n R : ℕ}
    (h : RankAtMost
      (power (directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) n) R) :
    RankAtMost (directSum (fun _ : Fin n → ι =>
      matrixCoefficients (K := K) (Fin n → A) (Fin n → B) (Fin n → C))) R := by
  have h' := h.directSum_const_of_power.directSum_pullback
    (fun x : (Fin n → A) × (Fin n → B) => fun i => (x.1 i, x.2 i))
    (fun y : (Fin n → B) × (Fin n → C) => fun i => (y.1 i, y.2 i))
    (fun z : (Fin n → C) × (Fin n → A) => fun i => (z.1 i, z.2 i))
  have heq : pullback
      (fun x : (Fin n → A) × (Fin n → B) => fun i => (x.1 i, x.2 i))
      (fun y : (Fin n → B) × (Fin n → C) => fun i => (y.1 i, y.2 i))
      (fun z : (Fin n → C) × (Fin n → A) => fun i => (z.1 i, z.2 i))
      (power (matrixCoefficients (K := K) A B C) n) =
      matrixCoefficients (Fin n → A) (Fin n → B) (Fin n → C) := by
    funext x y z
    exact matrixCoefficients_power n x y z
  simpa only [heq] using h'

theorem matrixCoefficients_cyclic_product_square :
    pullback (rectangularSquareX A B C) (rectangularSquareY A B C)
      (rectangularSquareZ A B C)
      (product (product (matrixCoefficients (K := K) A B C)
        (matrixCoefficients B C A)) (matrixCoefficients C A B)) =
      matrixCoefficients (A × B × C) (A × B × C) (A × B × C) := by
  funext x y z
  change
    ((if x.2.2.1 = y.1.2.1 ∧ y.2.2.2 = z.1.2.2 ∧ z.2.1 = x.1.1 then
        (1 : K) else 0) *
      (if x.2.2.2 = y.1.2.2 ∧ y.2.1 = z.1.1 ∧ z.2.2.1 = x.1.2.1 then
        1 else 0)) *
      (if x.2.1 = y.1.1 ∧ y.2.2.1 = z.1.2.1 ∧ z.2.2.2 = x.1.2.2 then
        1 else 0) =
      if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0
  simp only [Prod.ext_iff]
  have hguard :
      (((x.2.2.1 = y.1.2.1 ∧ y.2.2.2 = z.1.2.2 ∧ z.2.1 = x.1.1) ∧
        (x.2.2.2 = y.1.2.2 ∧ y.2.1 = z.1.1 ∧ z.2.2.1 = x.1.2.1)) ∧
        (x.2.1 = y.1.1 ∧ y.2.2.1 = z.1.2.1 ∧ z.2.2.2 = x.1.2.2)) ↔
      ((x.2.1 = y.1.1 ∧ x.2.2.1 = y.1.2.1 ∧ x.2.2.2 = y.1.2.2) ∧
        (y.2.1 = z.1.1 ∧ y.2.2.1 = z.1.2.1 ∧ y.2.2.2 = z.1.2.2) ∧
        z.2.1 = x.1.1 ∧ z.2.2.1 = x.1.2.1 ∧ z.2.2.2 = x.1.2.2) := by
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩
      exact ⟨⟨h₃.1, h₁.1, h₂.1⟩, ⟨h₂.2.1, h₃.2.1, h₁.2.1⟩,
        h₁.2.2, h₂.2.2, h₃.2.2⟩
    · intro h
      exact ⟨⟨⟨h.1.2.1, h.2.1.2.2, h.2.2.1⟩,
        ⟨h.1.2.2, h.2.1.1, h.2.2.2.1⟩⟩, ⟨h.1.1, h.2.1.2.1, h.2.2.2.2⟩⟩
  simp only [ite_zero_mul_ite_zero, one_mul, hguard]

theorem cyclic_matrixCoefficients :
    cyclic (matrixCoefficients (K := K) A B C) = matrixCoefficients B C A := by
  funext x y z
  exact matrixCoefficients_cyclic x y z

theorem matrixCoefficients_symmetrized_rank {r : ℕ}
    (h : RankAtMost (matrixCoefficients (K := K) A B C) r) :
    RankAtMost (matrixCoefficients (K := K)
      (A × B × C) (A × B × C) (A × B × C)) (r ^ 3) := by
  have h' := ((h.product (matrixCoefficients_cyclic_rank h)).product
    (matrixCoefficients_cyclic_rank (matrixCoefficients_cyclic_rank h))).pullback
    (rectangularSquareX A B C) (rectangularSquareY A B C) (rectangularSquareZ A B C)
  rw [matrixCoefficients_cyclic_product_square] at h'
  simpa only [pow_succ, pow_zero, one_mul] using h'

theorem matrixCoefficients_directSum_symmetrized_rank
    {ι : Type*} [DecidableEq ι] {r : ℕ}
    (h : RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) r) :
    RankAtMost (directSum (fun _ : (ι × ι) × ι =>
      matrixCoefficients (K := K) (A × B × C) (A × B × C) (A × B × C))) (r ^ 3) := by
  have h₁ : RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) B C A)) r := by
    simpa only [cyclic_matrixCoefficients] using h.directSum_cyclic
  have h₂ : RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) C A B)) r := by
    simpa only [cyclic_matrixCoefficients] using h₁.directSum_cyclic
  have h₃ := ((h.directSum_product h₁).directSum_product h₂).directSum_pullback
    (rectangularSquareX A B C) (rectangularSquareY A B C) (rectangularSquareZ A B C)
  simpa only [matrixCoefficients_cyclic_product_square, pow_succ, pow_zero, one_mul] using h₃

theorem symmetrized_tag_card (ι : Type*) [Fintype ι] :
    Fintype.card ((ι × ι) × ι) = Fintype.card ι ^ 3 := by
  simp [Fintype.card_prod, pow_succ]

omit [DecidableEq A] [DecidableEq B] [DecidableEq C] in
theorem symmetrized_index_card [Fintype A] [Fintype B] [Fintype C] :
    Fintype.card (A × B × C) = Fintype.card A * Fintype.card B * Fintype.card C := by
  simp [Fintype.card_prod, mul_assoc]

end Rectangular

end Tensor
end MatrixMultiplication.Foundation

end MatrixMultiplicationAllFields
