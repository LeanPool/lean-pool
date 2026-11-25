/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorClassRankOrder

/-!
# The three auxiliary pairings as actual tensor classes

The singleton leg is named in each pairing. Dimension comparisons select
coordinates, multiplication pairs coordinates, and the product of the three
orientations is the square matrix multiplication tensor.
-/

@[expose] public section

noncomputable section

open scoped BigOperators NNReal
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation.Tensor

namespace MatrixMultiplicationAllFields.TensorSpectrum

variable {K : Type*} [CommSemiring K]
namespace CoefficientTensor

/-- Evaluates `if y = z then 1 else 0` at the input `_ y z`. -/
def dotXCoeff (n : ℕ) : Tensor K Unit (Fin n) (Fin n) :=
  fun _ y z => if y = z then 1 else 0

/-- Evaluates `if x = z then 1 else 0` at the input `x _ z`. -/
def dotYCoeff (n : ℕ) : Tensor K (Fin n) Unit (Fin n) :=
  fun x _ z => if x = z then 1 else 0

/-- Evaluates `if x = y then 1 else 0` at the input `x y _`. -/
def dotZCoeff (n : ℕ) : Tensor K (Fin n) (Fin n) Unit :=
  fun x y _ => if x = y then 1 else 0

theorem dotX_restricts_of_le {m n : ℕ} (h : m ≤ n) :
    Restricts (dotXCoeff (K := K) n) (dotXCoeff m) := by
  have hp := Restricts.pullback (dotXCoeff (K := K) n) id (Fin.castLE h) (Fin.castLE h)
  have heq : Tensor.pullback id (Fin.castLE h) (Fin.castLE h) (dotXCoeff (K := K) n) =
      dotXCoeff m := by
    funext x y z
    simp [Tensor.pullback, dotXCoeff, Fin.ext_iff]
  rwa [heq] at hp

theorem dotY_restricts_of_le {m n : ℕ} (h : m ≤ n) :
    Restricts (dotYCoeff (K := K) n) (dotYCoeff m) := by
  have hp := Restricts.pullback (dotYCoeff (K := K) n) (Fin.castLE h) id (Fin.castLE h)
  have heq : Tensor.pullback (Fin.castLE h) id (Fin.castLE h) (dotYCoeff (K := K) n) =
      dotYCoeff m := by
    funext x y z
    simp [Tensor.pullback, dotYCoeff, Fin.ext_iff]
  rwa [heq] at hp

theorem dotZ_restricts_of_le {m n : ℕ} (h : m ≤ n) :
    Restricts (dotZCoeff (K := K) n) (dotZCoeff m) := by
  have hp := Restricts.pullback (dotZCoeff (K := K) n) (Fin.castLE h) (Fin.castLE h) id
  have heq : Tensor.pullback (Fin.castLE h) (Fin.castLE h) id (dotZCoeff (K := K) n) =
      dotZCoeff m := by
    funext x y z
    simp [Tensor.pullback, dotZCoeff, Fin.ext_iff]
  rwa [heq] at hp

theorem dotX_rankAtMost (n : ℕ) : Tensor.RankAtMost (dotXCoeff (K := K) n) n := by
  refine ⟨fun _ _ => 1, fun i y => if i = y then 1 else 0,
    fun i z => if i = z then 1 else 0, ?_⟩
  funext x y z
  simp [dotXCoeff, Tensor.rankOne, mul_ite, eq_comm]

theorem dotY_rankAtMost (n : ℕ) : Tensor.RankAtMost (dotYCoeff (K := K) n) n := by
  refine ⟨fun i x => if i = x then 1 else 0, fun _ _ => 1,
    fun i z => if i = z then 1 else 0, ?_⟩
  funext x y z
  simp [dotYCoeff, Tensor.rankOne, mul_ite, eq_comm]

theorem dotZ_rankAtMost (n : ℕ) : Tensor.RankAtMost (dotZCoeff (K := K) n) n := by
  refine ⟨fun i x => if i = x then 1 else 0,
    fun i y => if i = y then 1 else 0, fun _ _ => 1, ?_⟩
  funext x y z
  simp [dotZCoeff, Tensor.rankOne, mul_ite, eq_comm]

/-- Reindexes `(Unit × Unit)` and `Unit where toFun _` by an equivalence. -/
def dotUnitProduct : (Unit × Unit) ≃ Unit where
  toFun _ := ()
  invFun _ := ((), ())
  left_inv x := by rcases x with ⟨⟨⟩, ⟨⟩⟩; rfl
  right_inv x := by cases x; rfl

theorem dotX_product_pullback (m n : ℕ) :
    Tensor.pullback dotUnitProduct
      (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)) finProdFinEquiv
      (dotXCoeff (K := K) (m * n)) = Tensor.product (dotXCoeff m) (dotXCoeff n) := by
  funext x y z
  rcases y with ⟨y₁, y₂⟩
  rcases z with ⟨z₁, z₂⟩
  by_cases h₁ : y₁ = z₁ <;> by_cases h₂ : y₂ = z₂ <;>
    simp [Tensor.pullback, dotXCoeff, Tensor.product, Prod.mk.injEq, h₁, h₂]

theorem dotY_product_pullback (m n : ℕ) :
    Tensor.pullback (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))
      dotUnitProduct finProdFinEquiv (dotYCoeff (K := K) (m * n)) =
      Tensor.product (dotYCoeff m) (dotYCoeff n) := by
  funext x y z
  rcases x with ⟨x₁, x₂⟩
  rcases z with ⟨z₁, z₂⟩
  by_cases h₁ : x₁ = z₁ <;> by_cases h₂ : x₂ = z₂ <;>
    simp [Tensor.pullback, dotYCoeff, Tensor.product, Prod.mk.injEq, h₁, h₂]

theorem dotZ_product_pullback (m n : ℕ) :
    Tensor.pullback (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))
      finProdFinEquiv dotUnitProduct (dotZCoeff (K := K) (m * n)) =
      Tensor.product (dotZCoeff m) (dotZCoeff n) := by
  funext x y z
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  by_cases h₁ : x₁ = y₁ <;> by_cases h₂ : x₂ = y₂ <;>
    simp [Tensor.pullback, dotZCoeff, Tensor.product, Prod.mk.injEq, h₁, h₂]

/-- The two nonsingleton coordinates on the first leg become row and column. -/
def dotTripleX (n : ℕ) : ((Unit × Fin n) × Fin n) ≃ (Fin n × Fin n) where
  toFun x := (x.1.2, x.2)
  invFun x := (((), x.1), x.2)
  left_inv x := by rcases x with ⟨⟨⟨⟩, i⟩, j⟩; rfl
  right_inv x := by cases x; rfl

/-- The middle leg pairs the second index with the third. -/
def dotTripleY (n : ℕ) : ((Fin n × Unit) × Fin n) ≃ (Fin n × Fin n) where
  toFun y := (y.2, y.1.1)
  invFun y := ((y.2, ()), y.1)
  left_inv y := by rcases y with ⟨⟨i, ⟨⟩⟩, j⟩; rfl
  right_inv y := by cases y; rfl

/-- The final leg pairs the third index with the first. -/
def dotTripleZ (n : ℕ) : ((Fin n × Fin n) × Unit) ≃ (Fin n × Fin n) where
  toFun z := z.1
  invFun z := (z, ())
  left_inv z := by rcases z with ⟨⟨i, j⟩, ⟨⟩⟩; rfl
  right_inv z := rfl

theorem dotTriple_pullback (n : ℕ) :
    Tensor.pullback (dotTripleX n) (dotTripleY n) (dotTripleZ n)
      (squareMatrixTensor (K := K) n) =
      Tensor.product (Tensor.product (dotXCoeff n) (dotYCoeff n)) (dotZCoeff n) := by
  funext x y z
  by_cases hx : x.1.2 = z.1.2 <;>
    by_cases hy : y.1.1 = z.1.1 <;>
    by_cases hz : x.2 = y.2 <;>
    simp [Tensor.pullback, Tensor.matrixCoefficients, Tensor.product,
      dotTripleX, dotTripleY, dotTripleZ, dotXCoeff, dotYCoeff, dotZCoeff,
      hx, hy, hz, eq_comm]

end CoefficientTensor

namespace TensorClass

/-- The tensor class of multiplying two square matrices. -/
noncomputable def square (n : ℕ) : TensorClass K :=
  ofTensor (CoefficientTensor.squareMatrixTensor n)

/-- Computes the dot x by the application `ofTensor (CoefficientTensor.dotXCoeff n)`. -/
noncomputable def dotX (n : ℕ) : TensorClass K := ofTensor (CoefficientTensor.dotXCoeff n)
/-- Computes the dot y by the application `ofTensor (CoefficientTensor.dotYCoeff n)`. -/
noncomputable def dotY (n : ℕ) : TensorClass K := ofTensor (CoefficientTensor.dotYCoeff n)
/-- Computes the dot z by the application `ofTensor (CoefficientTensor.dotZCoeff n)`. -/
noncomputable def dotZ (n : ℕ) : TensorClass K := ofTensor (CoefficientTensor.dotZCoeff n)

theorem dotX_mono {m n : ℕ} (h : m ≤ n) : dotX (K := K) m ≤ dotX n :=
  ofTensor_le (CoefficientTensor.dotX_restricts_of_le h)

theorem dotY_mono {m n : ℕ} (h : m ≤ n) : dotY (K := K) m ≤ dotY n :=
  ofTensor_le (CoefficientTensor.dotY_restricts_of_le h)

theorem dotZ_mono {m n : ℕ} (h : m ≤ n) : dotZ (K := K) m ≤ dotZ n :=
  ofTensor_le (CoefficientTensor.dotZ_restricts_of_le h)

theorem rank_dotX_le (n : ℕ) : rank (dotX (K := K) n) ≤ n := by
  rw [dotX, rank_ofTensor]
  exact (CoefficientTensor.rank_le_iff _ _).mpr (CoefficientTensor.dotX_rankAtMost n)

theorem rank_dotY_le (n : ℕ) : rank (dotY (K := K) n) ≤ n := by
  rw [dotY, rank_ofTensor]
  exact (CoefficientTensor.rank_le_iff _ _).mpr (CoefficientTensor.dotY_rankAtMost n)

theorem rank_dotZ_le (n : ℕ) : rank (dotZ (K := K) n) ≤ n := by
  rw [dotZ, rank_ofTensor]
  exact (CoefficientTensor.rank_le_iff _ _).mpr (CoefficientTensor.dotZ_rankAtMost n)

theorem dotX_mul (m n : ℕ) : dotX (K := K) m * dotX n = dotX (m * n) := by
  unfold dotX
  rw [ofTensor_mul, ← CoefficientTensor.dotX_product_pullback]
  exact ofTensor_pullback_equiv _ _ _ _

theorem dotY_mul (m n : ℕ) : dotY (K := K) m * dotY n = dotY (m * n) := by
  unfold dotY
  rw [ofTensor_mul, ← CoefficientTensor.dotY_product_pullback]
  exact ofTensor_pullback_equiv _ _ _ _

theorem dotZ_mul (m n : ℕ) : dotZ (K := K) m * dotZ n = dotZ (m * n) := by
  unfold dotZ
  rw [ofTensor_mul, ← CoefficientTensor.dotZ_product_pullback]
  exact ofTensor_pullback_equiv _ _ _ _

@[simp] theorem dotX_one : dotX (K := K) 1 = 1 := by
  let u : Unit ≃ PUnit := Equiv.ofUnique _ _
  let e : Fin 1 ≃ PUnit := Equiv.ofUnique _ _
  have heq : Tensor.pullback u e e unitTensor = CoefficientTensor.dotXCoeff (K := K) 1 := by
    funext x y z
    simp [Tensor.pullback, TensorClass.unitTensor,
      CoefficientTensor.dotXCoeff, Subsingleton.elim y z]
  change ofTensor (CoefficientTensor.dotXCoeff 1) = ofTensor unitTensor
  rw [← heq]
  exact ofTensor_pullback_equiv _ u e e

@[simp] theorem dotY_one : dotY (K := K) 1 = 1 := by
  let u : Unit ≃ PUnit := Equiv.ofUnique _ _
  let e : Fin 1 ≃ PUnit := Equiv.ofUnique _ _
  have heq : Tensor.pullback e u e unitTensor = CoefficientTensor.dotYCoeff (K := K) 1 := by
    funext x y z
    simp [Tensor.pullback, TensorClass.unitTensor,
      CoefficientTensor.dotYCoeff, Subsingleton.elim x z]
  change ofTensor (CoefficientTensor.dotYCoeff 1) = ofTensor unitTensor
  rw [← heq]
  exact ofTensor_pullback_equiv _ e u e

@[simp] theorem dotZ_one : dotZ (K := K) 1 = 1 := by
  let u : Unit ≃ PUnit := Equiv.ofUnique _ _
  let e : Fin 1 ≃ PUnit := Equiv.ofUnique _ _
  have heq : Tensor.pullback e e u unitTensor = CoefficientTensor.dotZCoeff (K := K) 1 := by
    funext x y z
    simp [Tensor.pullback, TensorClass.unitTensor,
      CoefficientTensor.dotZCoeff, Subsingleton.elim x y]
  change ofTensor (CoefficientTensor.dotZCoeff 1) = ofTensor unitTensor
  rw [← heq]
  exact ofTensor_pullback_equiv _ e e u

theorem one_le_dotX {n : ℕ} (hn : 0 < n) : 1 ≤ dotX (K := K) n := by
  simpa only [dotX_one] using dotX_mono (Nat.succ_le_iff.mpr hn)

theorem one_le_dotY {n : ℕ} (hn : 0 < n) : 1 ≤ dotY (K := K) n := by
  simpa only [dotY_one] using dotY_mono (Nat.succ_le_iff.mpr hn)

theorem one_le_dotZ {n : ℕ} (hn : 0 < n) : 1 ≤ dotZ (K := K) n := by
  simpa only [dotZ_one] using dotZ_mono (Nat.succ_le_iff.mpr hn)

theorem dotX_mul_dotY_mul_dotZ (n : ℕ) : dotX (K := K) n * dotY n * dotZ n = square n := by
  unfold dotX dotY dotZ square
  rw [ofTensor_mul, ofTensor_mul, ← CoefficientTensor.dotTriple_pullback]
  exact ofTensor_pullback_equiv _ _ _ _

namespace Character

theorem dotX_le (f : Character K) (n : ℕ) : f (dotX n) ≤ n :=
  (f.le_rank _).trans (Nat.cast_le.mpr (rank_dotX_le n))

theorem dotY_le (f : Character K) (n : ℕ) : f (dotY n) ≤ n :=
  (f.le_rank _).trans (Nat.cast_le.mpr (rank_dotY_le n))

theorem dotZ_le (f : Character K) (n : ℕ) : f (dotZ n) ≤ n :=
  (f.le_rank _).trans (Nat.cast_le.mpr (rank_dotZ_le n))

theorem one_le_dotX (f : Character K) {n : ℕ} (hn : 0 < n) : 1 ≤ f (dotX n) := by
  simpa only [map_one] using f.monotone' (TensorClass.one_le_dotX hn)

theorem one_le_dotY (f : Character K) {n : ℕ} (hn : 0 < n) : 1 ≤ f (dotY n) := by
  simpa only [map_one] using f.monotone' (TensorClass.one_le_dotY hn)

theorem one_le_dotZ (f : Character K) {n : ℕ} (hn : 0 < n) : 1 ≤ f (dotZ n) := by
  simpa only [map_one] using f.monotone' (TensorClass.one_le_dotZ hn)

/-- Computes the dot xvalue by the application `f (dotX n)`. -/
noncomputable def dotXValue (f : Character K) (n : ℕ) : ℝ := f (dotX n)
/-- Computes the dot yvalue by the application `f (dotY n)`. -/
noncomputable def dotYValue (f : Character K) (n : ℕ) : ℝ := f (dotY n)
/-- Computes the dot zvalue by the application `f (dotZ n)`. -/
noncomputable def dotZValue (f : Character K) (n : ℕ) : ℝ := f (dotZ n)

theorem dotXValue_nonneg (f : Character K) (n : ℕ) : 0 ≤ f.dotXValue n :=
  (f (dotX n)).coe_nonneg

theorem dotYValue_nonneg (f : Character K) (n : ℕ) : 0 ≤ f.dotYValue n :=
  (f (dotY n)).coe_nonneg

theorem dotZValue_nonneg (f : Character K) (n : ℕ) : 0 ≤ f.dotZValue n :=
  (f (dotZ n)).coe_nonneg

theorem dotXValue_le (f : Character K) (n : ℕ) : f.dotXValue n ≤ n := by
  exact_mod_cast f.dotX_le n

theorem dotYValue_le (f : Character K) (n : ℕ) : f.dotYValue n ≤ n := by
  exact_mod_cast f.dotY_le n

theorem dotZValue_le (f : Character K) (n : ℕ) : f.dotZValue n ≤ n := by
  exact_mod_cast f.dotZ_le n

theorem one_le_dotXValue (f : Character K) {n : ℕ} (hn : 0 < n) : 1 ≤ f.dotXValue n := by
  exact_mod_cast f.one_le_dotX hn

theorem one_le_dotYValue (f : Character K) {n : ℕ} (hn : 0 < n) : 1 ≤ f.dotYValue n := by
  exact_mod_cast f.one_le_dotY hn

theorem one_le_dotZValue (f : Character K) {n : ℕ} (hn : 0 < n) : 1 ≤ f.dotZValue n := by
  exact_mod_cast f.one_le_dotZ hn

theorem dotXValue_mono (f : Character K) : Monotone f.dotXValue := by
  intro m n h
  exact_mod_cast f.monotone' (TensorClass.dotX_mono h)

theorem dotYValue_mono (f : Character K) : Monotone f.dotYValue := by
  intro m n h
  exact_mod_cast f.monotone' (TensorClass.dotY_mono h)

theorem dotZValue_mono (f : Character K) : Monotone f.dotZValue := by
  intro m n h
  exact_mod_cast f.monotone' (TensorClass.dotZ_mono h)

theorem dotXValue_mul (f : Character K) (m n : ℕ) :
    f.dotXValue (m * n) = f.dotXValue m * f.dotXValue n := by
  simp only [dotXValue, ← dotX_mul, map_mul, NNReal.coe_mul]

theorem dotYValue_mul (f : Character K) (m n : ℕ) :
    f.dotYValue (m * n) = f.dotYValue m * f.dotYValue n := by
  simp only [dotYValue, ← dotY_mul, map_mul, NNReal.coe_mul]

theorem dotZValue_mul (f : Character K) (m n : ℕ) :
    f.dotZValue (m * n) = f.dotZValue m * f.dotZValue n := by
  simp only [dotZValue, ← dotZ_mul, map_mul, NNReal.coe_mul]

@[simp] theorem dotXValue_one (f : Character K) : f.dotXValue 1 = 1 := by
  simp [dotXValue]

@[simp] theorem dotYValue_one (f : Character K) : f.dotYValue 1 = 1 := by
  simp [dotYValue]

@[simp] theorem dotZValue_one (f : Character K) : f.dotZValue 1 = 1 := by
  simp [dotZValue]

theorem dotValues_product (f : Character K) (n : ℕ) :
    f.dotXValue n * f.dotYValue n * f.dotZValue n = f (square n) := by
  simp only [dotXValue, dotYValue, dotZValue, ← NNReal.coe_mul, ← map_mul,
    dotX_mul_dotY_mul_dotZ]

end Character

end TensorClass
end MatrixMultiplicationAllFields.TensorSpectrum
