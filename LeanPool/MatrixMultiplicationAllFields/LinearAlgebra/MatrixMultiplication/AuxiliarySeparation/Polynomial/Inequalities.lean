/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Polynomial/Inequalities.lean`,
by Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; `[IsAlgClosed K]` is assumed by the
declarations that use it.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.Symmetry
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Permutation
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Polynomial.Laws
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Determinant.Character
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Sector.Character
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Polynomial.ProductBounds
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.Profile
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# The inequalities for the polynomial profile

The six character values are combined before the common probability law is
optimized. Each first-leg exponent occurs twice, so the total entropy exponent
is exactly six times the mean exponent used to normalize the profile.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation.Character

variable (χ : Character K)

/-- All six permuted characters have the same mean singleton-leg exponent. -/
theorem permutedCharacter_meanExponent (i : Fin 6) :
    (χ.permutedCharacter i).meanExponent = χ.meanExponent := by
  fin_cases i <;> simp [permutedCharacter, meanExponent] <;> ring

/-- The exponents of the six permuted characters have the normalization total. -/
theorem sum_permutedCharacter_pX_mean :
    (∑ i : Fin 6, (χ.permutedCharacter i).pX) = 6 * χ.meanExponent := by
  rw [χ.sum_permutedCharacter_pX]
  unfold meanExponent
  ring

/-- All six factors associated to a positive-size polynomial tensor are positive. -/
theorem permutedCharacter_convolution_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (i : Fin 6) : 0 < (χ.permutedCharacter i).value (convolution K a b) :=
  (χ.permutedCharacter i).value_convolution_pos ha hb

/-- Exchanging the two output-side positions reorders the six convolution factors. -/
theorem prod_permutedCharacter_swapped_convolution (a b : ℕ) :
    (∏ i : Fin 6, (χ.permutedCharacter i).value
      (fun x z y => convolution K a b x y z)) =
    ∏ i : Fin 6, (χ.permutedCharacter i).value (convolution K a b) := by
  rw [χ.prod_permutedCharacter_value, χ.prod_permutedCharacter_value]
  exact χ.sixfoldProduct_swap23 _

/-- The actual polynomial profile is concave in its second positive index. -/
theorem convolutionProfile_concave [IsAlgClosed K] {a b : ℕ} (ht : 0 < χ.meanExponent)
    (ha : 0 < a) (hb : 2 ≤ b) :
    χ.convolutionProfile a (b - 1) + χ.convolutionProfile a (b + 1) ≤
      2 * χ.convolutionProfile a b := by
  have h := finite_product_concavity
    (fun i : Fin 6 => (χ.permutedCharacter i).value (convolution K a b))
    (fun i : Fin 6 => (χ.permutedCharacter i).value (convolution K a (b + 1)))
    (fun i : Fin 6 => (χ.permutedCharacter i).value (convolution K a (b - 1)))
    (fun i : Fin 6 => (χ.permutedCharacter i).pX)
    (mul_pos (by norm_num : (0 : ℝ) < 6) ht) χ.sum_permutedCharacter_pX_mean
    (fun i => χ.permutedCharacter_convolution_pos ha (by omega) i)
    (fun i => χ.permutedCharacter_convolution_pos ha (by omega) i)
    (fun i => χ.permutedCharacter_convolution_pos ha (by omega) i)
    (fun i q hq₀ hq₁ =>
      (χ.permutedCharacter i).convolution_concavity_tag a b ha hb q hq₀ hq₁)
  simp only [χ.prod_permutedCharacter_value] at h
  change χ.convolutionProfile a (b + 1) + χ.convolutionProfile a (b - 1) ≤
    2 * χ.convolutionProfile a b at h
  simpa only [add_comm] using h

/-- The actual three-sector degeneration triples the normalized profile. -/
theorem convolutionProfile_tripling [IsAlgClosed K] {a h : ℕ} (ht : 0 < χ.meanExponent)
    (ha : 0 < a) (hh : 0 < h) :
    3 * χ.convolutionProfile a h ≤ χ.convolutionProfile a (3 * h + a - 1) := by
  have hsw : (fun i s r => convolution K a h i r s) ≠ 0 := by
    intro hz
    apply convolution_nonzero (K := K) ha hh
    exact congrArg
      (fun T : Tensor K (Fin a) (Fin (a + h - 1)) (Fin h) => fun i j k => T i k j) hz
  have h := finite_product_tripling
    (fun i : Fin 6 => (χ.permutedCharacter i).value (convolution K a (3 * h + a - 1)))
    (fun i : Fin 6 => (χ.permutedCharacter i).value (convolution K a h))
    (fun i : Fin 6 => (χ.permutedCharacter i).value (fun x z y => convolution K a h x y z))
    (fun i : Fin 6 => (χ.permutedCharacter i).pX)
    (mul_pos (by norm_num : (0 : ℝ) < 6) ht) χ.sum_permutedCharacter_pX_mean
    (fun i => χ.permutedCharacter_convolution_pos ha (by omega) i)
    (fun i => χ.permutedCharacter_convolution_pos ha hh i)
    (fun i => (χ.permutedCharacter i).value_pos hsw)
    (fun i => Sector.convolution_tripling_tag (χ.permutedCharacter i) a h ha hh)
    (χ.prod_permutedCharacter_swapped_convolution a h)
  simpa only [χ.prod_permutedCharacter_value, convolutionProfile, symmetrizedProfile] using h

/-- The polynomial profile satisfies every hypothesis of the scalar growth theorem. -/
def toScalarProfile [IsAlgClosed K] (ht : 0 < χ.meanExponent) : ScalarProfile χ.meanExponent where
  value := χ.convolutionProfile
  positive a b ha hb := χ.convolutionProfile_pos (by omega) (by omega)
  symmetric a b _ _ := χ.convolutionProfile_comm a b
  boundary b hb := χ.convolutionProfile_one_left ht (by omega)
  concave a b ha hb := χ.convolutionProfile_concave ht (by omega) hb
  tripling a h ha hh := χ.convolutionProfile_tripling ht (by omega) (by omega)
  rank_bound a b ha hb := by
    have h := χ.convolutionProfile_le (a := a) (b := b) ht
    have hab : 1 ≤ a + b := by omega
    simpa only [Nat.cast_sub hab, Nat.cast_add, Nat.cast_one] using h

/-- Every actual tensor character has mean singleton-leg exponent at most `3/4`. -/
theorem meanExponent_le_three_quarters [IsAlgClosed K] : χ.meanExponent ≤ 3 / 4 := by
  by_cases ht : 0 < χ.meanExponent
  · exact (χ.toScalarProfile ht).exponent_le_three_quarters ht
  · have hle : χ.meanExponent ≤ 0 := le_of_not_gt ht
    linarith

/-- The three dot-product exponents of an actual character sum to at most `9/4`. -/
theorem exponent_sum_le_nine_quarters [IsAlgClosed K] : χ.pX + χ.pY + χ.pZ ≤ 9 / 4 := by
  have h := χ.meanExponent_le_three_quarters
  unfold meanExponent at h
  linarith

end MatrixMultiplication.AuxiliarySeparation.Character

end

end MatrixMultiplicationAllFields
