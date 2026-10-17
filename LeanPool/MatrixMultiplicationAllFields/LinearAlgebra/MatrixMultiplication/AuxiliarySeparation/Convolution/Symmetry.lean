/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Convolution/Symmetry.lean`, by
Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; `[IsAlgClosed K]` is assumed by the
declarations that use it.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Symmetrization
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.Rank
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Dot
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.NormalizedProfile
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Character identities for polynomial convolution

The boundary convolution tensors are dot products. In the sixfold character
product, each possible singleton leg appears exactly twice. Consequently the
normalization by the average dot-product exponent gives the boundary values
of the polynomial profile from Section 5.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation
namespace Character

open MatrixMultiplication.Foundation

variable (χ : Character K)

/-- A symmetric dot product occurs twice in each of its three leg positions. -/
theorem sixfoldProduct_dotPairing (n : ℕ) :
    χ.sixfoldProduct (Tensor.dotPairing (K := K) (Fin n)) =
      (χ.value (Tensor.dotPairing (K := K) (Fin n)) *
        χ.value (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin n))) *
        χ.value (Tensor.cyclic (Tensor.cyclic
          (Tensor.dotPairing (K := K) (Fin n))))) ^ 2 := by
  let D := Tensor.dotPairing (K := K) (Fin n)
  have h3 : (fun (i : Fin n) (_ : Unit) (j : Fin n) => D i j ()) =
      Tensor.cyclic D := by
    funext i u j
    simp [D, Tensor.cyclic, Tensor.dotPairing, eq_comm]
  have h4 : (fun (_ : Unit) (j i : Fin n) => D i j ()) =
      Tensor.cyclic (Tensor.cyclic D) := by
    funext u j i
    simp [D, Tensor.cyclic, Tensor.dotPairing, eq_comm]
  have h5 : (fun (j i : Fin n) (_ : Unit) => D i j ()) = D := by
    funext j i u
    simp [D, Tensor.dotPairing, eq_comm]
  change χ.sixfoldProduct D = _
  unfold sixfoldProduct
  change χ.value D * χ.value (Tensor.cyclic D) *
      χ.value (Tensor.cyclic (Tensor.cyclic D)) *
      χ.value (fun (i : Fin n) (_ : Unit) (j : Fin n) => D i j ()) *
      χ.value (fun (_ : Unit) (j i : Fin n) => D i j ()) *
      χ.value (fun (j i : Fin n) (_ : Unit) => D i j ()) = _
  rw [h3, h4, h5]
  ring

/-- The boundary `C(1,b)` has the sixfold product of a dot product. -/
theorem sixfoldProduct_convolution_one_left (b : ℕ) :
    χ.sixfoldProduct (convolution K 1 b) =
      χ.sixfoldProduct (Tensor.dotPairing (K := K) (Fin b)) := by
  have h := χ.sixfoldProduct_reindex (convolution K 1 b)
    convolutionOneInputEquiv (Equiv.refl (Fin b)) (convolutionOneOutputEquiv b)
  rw [convolution_one_left_dotPairing] at h
  calc
    _ = χ.sixfoldProduct (Tensor.cyclic (Tensor.cyclic
        (Tensor.dotPairing (K := K) (Fin b)))) := h.symm
    _ = χ.sixfoldProduct (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin b))) :=
      χ.sixfoldProduct_cyclic _
    _ = _ := χ.sixfoldProduct_cyclic _

/-- The boundary `C(a,1)` has the same dot-product product. -/
theorem sixfoldProduct_convolution_one_right (a : ℕ) :
    χ.sixfoldProduct (convolution K a 1) =
      χ.sixfoldProduct (Tensor.dotPairing (K := K) (Fin a)) := by
  rw [χ.sixfoldProduct_convolution_comm, χ.sixfoldProduct_convolution_one_left]

/-- The mean of the character's three singleton-leg exponents. -/
def meanExponent : ℝ := (χ.pX + χ.pY + χ.pZ) / 3

theorem meanExponent_nonneg : 0 ≤ χ.meanExponent := by
  exact div_nonneg (add_nonneg (add_nonneg χ.pX_nonneg χ.pY_nonneg) χ.pZ_nonneg)
    (by norm_num)

theorem meanExponent_le_one : χ.meanExponent ≤ 1 := by
  unfold meanExponent
  have hx := χ.pX_le_one
  have hy := χ.pY_le_one
  have hz := χ.pZ_le_one
  linarith

/-- The three exponents occur twice in the sixfold boundary product. -/
theorem sixfoldProduct_dotPairing_eq_rpow {n : ℕ} (hn : 0 < n) :
    χ.sixfoldProduct (Tensor.dotPairing (K := K) (Fin n)) =
      (n : ℝ) ^ (6 * χ.meanExponent) := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [χ.sixfoldProduct_dotPairing, χ.value_dotPairing hn,
    χ.value_cyclic_dotPairing hn, χ.value_cyclic_cyclic_dotPairing hn,
    ← Real.rpow_add hn', ← Real.rpow_add hn']
  calc
    ((n : ℝ) ^ (χ.pZ + χ.pY + χ.pX)) ^ 2 =
        (n : ℝ) ^ ((χ.pZ + χ.pY + χ.pX) * (2 : ℕ)) :=
      (Real.rpow_mul_natCast hn'.le _ 2).symm
    _ = _ := by congr 1; unfold meanExponent; ring

/-- The positive-size boundary product has its exact normalized power. -/
theorem sixfoldProduct_convolution_one_left_eq_rpow {b : ℕ} (hb : 0 < b) :
    χ.sixfoldProduct (convolution K 1 b) = (b : ℝ) ^ (6 * χ.meanExponent) := by
  rw [χ.sixfoldProduct_convolution_one_left, χ.sixfoldProduct_dotPairing_eq_rpow hb]

/-- The polynomial profile `P(a,b)` normalized by the actual mean exponent. -/
def convolutionProfile (a b : ℕ) : ℝ :=
  χ.symmetrizedProfile χ.meanExponent (convolution K a b)

/-- Swapping the two polynomial inputs preserves the normalized profile. -/
theorem convolutionProfile_comm (a b : ℕ) :
    χ.convolutionProfile a b = χ.convolutionProfile b a := by
  exact congrArg (fun s : ℝ => s ^ (1 / (6 * χ.meanExponent)))
    (χ.sixfoldProduct_convolution_comm a b)

theorem convolutionProfile_nonneg (a b : ℕ) : 0 ≤ χ.convolutionProfile a b :=
  χ.symmetrizedProfile_nonneg _ _

/-- Nonzero polynomial multiplication gives a positive normalized profile. -/
theorem convolutionProfile_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    0 < χ.convolutionProfile a b :=
  χ.symmetrizedProfile_pos _ (convolution_nonzero ha hb)

/-- The evaluation/interpolation algorithm bounds the normalized profile. -/
theorem convolutionProfile_le [IsAlgClosed K] {a b : ℕ} (ht : 0 < χ.meanExponent) :
    χ.convolutionProfile a b ≤ (a + b - 1 : ℕ) ^ (1 / χ.meanExponent) :=
  χ.symmetrizedProfile_le_rank ht (convolution_rankAtMost a b)

/-- The normalization gives the exact initial value `P(1,b) = b`. -/
theorem convolutionProfile_one_left {b : ℕ} (ht : 0 < χ.meanExponent) (hb : 0 < b) :
    χ.convolutionProfile 1 b = b := by
  have hb' : 0 < (b : ℝ) := Nat.cast_pos.mpr hb
  unfold convolutionProfile symmetrizedProfile
  rw [χ.sixfoldProduct_convolution_one_left_eq_rpow hb, ← Real.rpow_mul hb'.le]
  rw [show (6 * χ.meanExponent) * (1 / (6 * χ.meanExponent)) = 1 by
    field_simp [ne_of_gt ht]]
  exact Real.rpow_one _

/-- Input symmetry gives the other exact initial value `P(a,1) = a`. -/
theorem convolutionProfile_one_right {a : ℕ} (ht : 0 < χ.meanExponent) (ha : 0 < a) :
    χ.convolutionProfile a 1 = a := by
  rw [χ.convolutionProfile_comm, χ.convolutionProfile_one_left ht ha]

/-- Interpolation bounds an individual character on polynomial convolution. -/
theorem value_convolution_le [IsAlgClosed K] (a b : ℕ) :
    χ.value (convolution K a b) ≤ (a + b - 1 : ℕ) :=
  χ.value_le_rank (convolution_rankAtMost a b)

/-- Positive input sizes give a positive individual character value. -/
theorem value_convolution_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    0 < χ.value (convolution K a b) :=
  zero_lt_one.trans_le (χ.one_le_value (convolution_nonzero ha hb))

end Character
end MatrixMultiplication.AuxiliarySeparation

end

end MatrixMultiplicationAllFields
