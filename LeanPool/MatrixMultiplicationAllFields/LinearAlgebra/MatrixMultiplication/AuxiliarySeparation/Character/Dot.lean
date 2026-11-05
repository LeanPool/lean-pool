/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Character/Dot.lean`, by Jeroen
Zuiddam, 2026: `ℂ` replaced by a field `K`; no declaration here needs `K` algebraically closed.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Basic
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.MultiplicativePower
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexPairingMatrixTensor
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.MatMul
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Dot-product exponents of tensor characters

The power laws here follow from restriction monotonicity and tensor products.
They are not additional assumptions on a character. The three exponents refer
to the leg on which the corresponding dot product has dimension one.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation.Character

variable (χ : Character K)

theorem value_pos {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor K X Y Z} (hT : T ≠ 0) : 0 < χ.value T :=
  lt_of_lt_of_le zero_lt_one (χ.one_le_value hT)

/-- Precomposing a character with a cyclic permutation gives a character. -/
def cyclicCharacter : Character K where
  value T := χ.value (Tensor.cyclic T)
  nonneg T := χ.nonneg (Tensor.cyclic T)
  map_zero := χ.map_zero
  map_one := χ.map_one
  map_directSum T := by
    rw [Tensor.cyclic_directSum, χ.map_directSum]
  map_product T S := χ.map_product (Tensor.cyclic T) (Tensor.cyclic S)
  monotone T A B C := by
    have heq : Tensor.cyclic (Tensor.restrict A B C T) =
        Tensor.restrict B C A (Tensor.cyclic T) := by
      funext y z x
      simp only [Tensor.cyclic, Tensor.restrict]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [heq]
    exact χ.monotone (Tensor.cyclic T) B C A

@[simp] theorem cyclicCharacter_value {X Y Z : Type}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor K X Y Z) :
    χ.cyclicCharacter.value T = χ.value (Tensor.cyclic T) := rfl

private theorem dotPairing_ne_zero {m : ℕ} (hm : 0 < m) :
    Tensor.dotPairing (K := K) (Fin m) ≠ 0 := by
  intro h
  have hv := congrFun (congrFun (congrFun h ⟨0, hm⟩) ⟨0, hm⟩) ()
  simp [Tensor.dotPairing] at hv

private theorem dotPairing_rank (m : ℕ) :
    Tensor.RankAtMost (Tensor.dotPairing (K := K) (Fin m)) m := by
  let a : Fin m → Fin m → K := fun i j => if i = j then 1 else 0
  have heq : Tensor.dotPairing (K := K) (Fin m) =
      fun x y z => ∑ i, Tensor.rankOne (a i) (a i) (fun _ : Unit => 1) x y z := by
    funext x y z
    simp [Tensor.dotPairing, Tensor.rankOne, a, mul_ite, eq_comm]
  rw [heq]
  simpa using Tensor.rankAtMost_sum_rankOne a a (fun (_ : Fin m) (_ : Unit) => (1 : K))

theorem value_dotPairing_pos {m : ℕ} (hm : 0 < m) :
    0 < χ.value (Tensor.dotPairing (K := K) (Fin m)) :=
  χ.value_pos (dotPairing_ne_zero hm)

theorem value_dotPairing_le (m : ℕ) :
    χ.value (Tensor.dotPairing (K := K) (Fin m)) ≤ m :=
  χ.value_le_rank (dotPairing_rank m)

theorem value_dotPairing_mono {m n : ℕ} (hmn : m ≤ n) :
    χ.value (Tensor.dotPairing (K := K) (Fin m)) ≤
      χ.value (Tensor.dotPairing (K := K) (Fin n)) := by
  have heq : Tensor.pullback (Fin.castLE hmn) (Fin.castLE hmn) id
      (Tensor.dotPairing (K := K) (Fin n)) = Tensor.dotPairing (K := K) (Fin m) := by
    funext x y z
    simp [Tensor.pullback, Tensor.dotPairing]
  rw [← heq]
  exact χ.value_pullback_le _ _ _ _

theorem value_dotPairing_mul (m n : ℕ) :
    χ.value (Tensor.dotPairing (K := K) (Fin (m * n))) =
      χ.value (Tensor.dotPairing (K := K) (Fin m)) *
        χ.value (Tensor.dotPairing (K := K) (Fin n)) := by
  have heq : Tensor.pullback finProdFinEquiv.symm finProdFinEquiv.symm
      (Equiv.prodUnique Unit Unit).symm
      (Tensor.product (Tensor.dotPairing (K := K) (Fin m))
        (Tensor.dotPairing (K := K) (Fin n))) =
      Tensor.dotPairing (K := K) (Fin (m * n)) := by
    funext x y z
    simp only [Tensor.pullback, Tensor.product, Tensor.dotPairing,
      ite_zero_mul_ite_zero, one_mul, ← Prod.ext_iff, Equiv.apply_eq_iff_eq]
  rw [← heq, χ.value_reindex, χ.map_product]

/-- The exponent on dot products whose third leg has dimension one. -/
def pZ : ℝ :=
  Real.log (χ.value (Tensor.dotPairing (K := K) (Fin 2))) / Real.log 2

/-- The exponent on dot products whose second leg has dimension one. -/
def pY : ℝ := χ.cyclicCharacter.pZ

/-- The exponent on dot products whose first leg has dimension one. -/
def pX : ℝ := χ.cyclicCharacter.cyclicCharacter.pZ

theorem pZ_nonneg : 0 ≤ χ.pZ := by
  apply div_nonneg _ (Real.log_nonneg (by norm_num))
  exact Real.log_nonneg (χ.one_le_value (dotPairing_ne_zero (by norm_num)))

theorem pZ_le_one : χ.pZ ≤ 1 := by
  apply (div_le_one (Real.log_pos (by norm_num))).2
  exact Real.log_le_log (χ.value_dotPairing_pos (by norm_num)) (χ.value_dotPairing_le 2)

theorem pY_nonneg : 0 ≤ χ.pY := χ.cyclicCharacter.pZ_nonneg
theorem pY_le_one : χ.pY ≤ 1 := χ.cyclicCharacter.pZ_le_one
theorem pX_nonneg : 0 ≤ χ.pX := χ.cyclicCharacter.cyclicCharacter.pZ_nonneg
theorem pX_le_one : χ.pX ≤ 1 := χ.cyclicCharacter.cyclicCharacter.pZ_le_one

theorem value_dotPairing {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.dotPairing (K := K) (Fin m)) = (m : ℝ) ^ χ.pZ := by
  apply positiveMultiplicative_eq_rpow
    (f := fun m => χ.value (Tensor.dotPairing (K := K) (Fin m)))
    (fun n hn => χ.value_dotPairing_pos hn)
    (fun m n _ _ => χ.value_dotPairing_mul m n)
    (fun _ _ _ _ hmn => χ.value_dotPairing_mono hmn) hm

theorem value_cyclic_dotPairing {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin m))) =
      (m : ℝ) ^ χ.pY :=
  χ.cyclicCharacter.value_dotPairing hm

theorem value_cyclic_cyclic_dotPairing {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin m)))) =
      (m : ℝ) ^ χ.pX :=
  χ.cyclicCharacter.cyclicCharacter.value_dotPairing hm

/-- Exact factorization through the three oriented dot products. -/
theorem value_matrixCoefficients {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    χ.value (Tensor.matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c)) =
      (b : ℝ) ^ χ.pZ * (a : ℝ) ^ χ.pY * (c : ℝ) ^ χ.pX := by
  rw [← Tensor.pairingTriple_matrixCoefficients, χ.value_reindex]
  simp only [Tensor.pairingTriple, χ.map_product, χ.value_dotPairing hb,
    χ.value_cyclic_dotPairing ha, χ.value_cyclic_cyclic_dotPairing hc]

/-- The character of square matrix multiplication has exponent `pX + pY + pZ`. -/
theorem value_matrixCoefficients_square {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.matrixCoefficients (K := K) (Fin m) (Fin m) (Fin m)) =
      (m : ℝ) ^ (χ.pX + χ.pY + χ.pZ) := by
  rw [χ.value_matrixCoefficients hm hm hm]
  have hm' : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  rw [Real.rpow_add hm', Real.rpow_add hm']
  ring

/-- The same power law in the matrix-tensor notation used for exact rank. -/
theorem value_matrixMultiplication {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.matMul K m m m) =
      (m : ℝ) ^ (χ.pX + χ.pY + χ.pZ) := by
  simpa only [Tensor.matMul_eq_matrixCoefficients] using
    χ.value_matrixCoefficients_square hm

end MatrixMultiplication.AuxiliarySeparation.Character

end

end MatrixMultiplicationAllFields
