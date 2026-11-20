/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.SliceQuadraturePositivity
public import LeanPool.NoncommutativeAMGM.MatrixOrder

/-! # Applying the positive slice quadrature to matrix sums of squares -/

@[expose] public section
namespace NoncommutativeAMGM
open scoped BigOperators
open Matrix

/-- The root-grid slice quadrature, bundled as a real linear functional. -/
noncomputable def rootSliceLinearMap (n m : ℕ) (ξ ζ : ℂ) : BooleanPolynomial n →ₗ[ℝ] ℝ where
  toFun := rootSliceFunctional n m ξ ζ
  map_add' f g := by
    simp only [rootSliceFunctional, rootRealAverage, map_add, Finset.sum_add_distrib]
    ring
  map_smul' a f := by
    simp only [rootSliceFunctional, rootRealAverage, map_smul, smul_eq_mul, RingHom.id_apply]
    rw [← Finset.mul_sum]
    ring

/-- Apply a scalar Boolean linear functional to every entry of a matrix. -/
noncomputable def booleanMatrixImage {n : ℕ} {ι κ : Type*}
    (L : BooleanPolynomial n →ₗ[ℝ] ℝ) (M : Matrix ι κ (BooleanPolynomial n)) :
    Matrix ι κ ℝ := fun i j ↦ L (M i j)

/-- A rectangular Boolean matrix times its transpose. -/
noncomputable def booleanGram {n : ℕ} {ι κ : Type*} [Fintype κ]
    (F : Matrix ι κ (BooleanPolynomial n)) : Matrix ι ι (BooleanPolynomial n) :=
  fun i j ↦ ∑ a, F i a * F j a

theorem linear_square_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (L : BooleanPolynomial n →ₗ[ℝ] ℝ) (x : ι → ℝ) (f : ι → BooleanPolynomial n) :
    L ((∑ i, x i • f i) ^ 2) = ∑ i, ∑ j, x i * x j * L (f i * f j) := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_assoc, mul_comm (f j) (f i)]

theorem booleanGram_quadratic {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : BooleanPolynomial n →ₗ[ℝ] ℝ) (F : Matrix ι κ (BooleanPolynomial n)) (x : ι → ℝ) :
    star x ⬝ᵥ (booleanMatrixImage L (booleanGram F) *ᵥ x) =
      ∑ a, L ((∑ i, x i • F i a) ^ 2) := by
  classical
  simp only [dotProduct, Matrix.mulVec, booleanMatrixImage, booleanGram,
    Pi.star_apply, star_trivial, map_sum, Finset.mul_sum, Finset.sum_mul, linear_square_sum]
  calc
    (∑ i, ∑ j, ∑ a, x i * (L (F i a * F j a) * x j)) =
        ∑ i, ∑ a, ∑ j, x i * x j * L (F i a * F j a) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := Finset.sum_comm

/-- Positivity on scalar squares implies positivity on matrix Gram sums of the same degree. -/
theorem booleanMatrixImage_gram_posSemidef {n d : ℕ} {ι κ : Type*} [Finite ι] [Fintype κ]
    (L : BooleanPolynomial n →ₗ[ℝ] ℝ)
    (hL : ∀ f : BooleanPolynomial n, BooleanDegreeLE f d → 0 ≤ L (f ^ 2))
    (F : Matrix ι κ (BooleanPolynomial n)) (hF : ∀ i a, BooleanDegreeLE (F i a) d) :
    (booleanMatrixImage L (booleanGram F)).PosSemidef := by
  let : Fintype ι := Fintype.ofFinite ι
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, booleanMatrixImage, booleanGram]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    exact mul_comm _ _
  · intro x
    rw [booleanGram_quadratic]
    apply Finset.sum_nonneg
    intro a _
    apply hL
    apply booleanDegreeLE_sum
    intro i _
    exact booleanDegreeLE_smul (x i) (hF i a)

/-- The quadratic-threshold quadrature maps each actual Boolean matrix Gram sum to a PSD matrix. -/
theorem rootSlice_gram_posSemidef {ξ ζ : ℂ} {η : ℝ} {n m d : ℕ}
    {ι κ : Type*} [Finite ι] [Fintype κ]
    (F : Matrix ι κ (BooleanPolynomial n)) (hn : 0 < n) (hm : 2 ≤ m)
    (hζ : IsPrimitiveRoot ζ m) (hξ : ξ ^ m = (η : ℂ)) (hη : η = 1 ∨ η = -1)
    (hF : ∀ i a, BooleanDegreeLE (F i a) d) (hdn : 2 * d ≤ n)
    (hdm : 2 * d ≤ m + 1) (hnd : 2 * d ^ 2 ≤ n) :
    (booleanMatrixImage (rootSliceLinearMap n m ξ ζ) (booleanGram F)).PosSemidef := by
  apply booleanMatrixImage_gram_posSemidef _ _ F hF
  intro f hf
  exact rootSliceFunctional_square_nonneg f hn hm hζ hξ hη hf hdn hdm hnd

end NoncommutativeAMGM
