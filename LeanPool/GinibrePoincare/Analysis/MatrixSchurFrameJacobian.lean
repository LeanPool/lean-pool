/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurFrameJacobian.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurFrameDerivative
public import LeanPool.GinibrePoincare.Analysis.MatrixUnitaryVolume

/-!
# Matrix Schur frame jacobian

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixSchurFrame_entry_fderiv_abs_det`.
-/

@[expose] public section

open Matrix Filter
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section

/-- The actual derivative, read in matrix entry coordinates and in the moving unitary frame. -/
def matrixSchurFrameNormalizedDerivative {n : ℕ}
    (Q : (SchurLowerIndex n → ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin n) ℂ) (x : SchurLowerIndex n → ℂ)
    (y : SchurUpperIndex n → ℂ) : SchurCoordinates n →ₗ[ℝ] SchurCoordinates n :=
  schurEntryCoordinates.comp
    ((matrixUnitaryConjugation (Q x)ᴴ).comp
      (fderiv ℝ (matrixSchurFrameChart Q T) (x, y))).toLinearMap

theorem matrixSchurFrameNormalizedDerivative_eq {n : ℕ}
    (Q : (SchurLowerIndex n → ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin n) ℂ) (x : SchurLowerIndex n → ℂ)
    (y : SchurUpperIndex n → ℂ)
    (D : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (hQ : HasFDerivAt Q D x) (hunit : ∀ᶠ z in 𝓝 x, Q z ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    matrixSchurFrameNormalizedDerivative Q T x y =
      schurMovingJacobian (T + schurUpperCombination y) (matrixUnitaryConnection (Q x) D) := by
  apply LinearMap.ext
  intro p
  simp only [matrixSchurFrameNormalizedDerivative, schurMovingJacobian,
    LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  erw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
  erw [matrixUnitaryConjugation_apply]
  rw [Matrix.conjTranspose_conjTranspose]
  change schurEntryCoordinates ((Q x)ᴴ *
    fderiv ℝ (matrixSchurFrameChart Q T) (x, y) p * Q x) =
    schurEntryCoordinates (schurMovingTangent (T + schurUpperCombination y)
      (matrixUnitaryConnection (Q x) D) p)
  rw [matrixSchurFrameChart_normalized_fderiv Q T x p.1 y p.2 D hQ hunit]

theorem matrixSchurFrameNormalizedDerivative_det {n : ℕ}
    (Q : (SchurLowerIndex n → ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ i j, j < i → T i j = 0)
    (x : SchurLowerIndex n → ℂ) (y : SchurUpperIndex n → ℂ)
    (D : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (hQ : HasFDerivAt Q D x) (hunit : ∀ᶠ z in 𝓝 x, Q z ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (matrixSchurFrameNormalizedDerivative Q T x y).det =
      vandermondeWeight (fun i => (T + schurUpperCombination y) i i) *
        (((matrixLowerRead n).comp (matrixUnitaryConnection (Q x) D)).toLinearMap).det := by
  rw [matrixSchurFrameNormalizedDerivative_eq Q T x y D hQ hunit]
  apply schurMovingJacobian_det
  · intro i j hij
    rw [Matrix.add_apply, hT i j hij, schurUpperCombination_lower_zero y i j hij, add_zero]
  · intro v
    exact matrixUnitary_left_derivative_skew hQ hunit v

/-- In fixed entry coordinates the absolute Jacobian has the same Vandermonde factor;
unitary conjugation contributes determinant of absolute value one. -/
theorem matrixSchurFrame_entry_fderiv_abs_det {n : ℕ}
    (Q : (SchurLowerIndex n → ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ i j, j < i → T i j = 0)
    (x : SchurLowerIndex n → ℂ) (y : SchurUpperIndex n → ℂ)
    (D : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (hQ : HasFDerivAt Q D x) (hunit : ∀ᶠ z in 𝓝 x, Q z ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    |(schurEntryCoordinates.comp
        (fderiv ℝ (matrixSchurFrameChart Q T) (x, y)).toLinearMap).det| =
      vandermondeWeight (fun i => (T + schurUpperCombination y) i i) *
        |(((matrixLowerRead n).comp (matrixUnitaryConnection (Q x) D)).toLinearMap).det| := by
  let E := schurEntryCoordinatesEquiv n
  let C : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    (matrixUnitaryConjugation (Q x)ᴴ).toLinearMap
  let J := schurEntryCoordinates.comp
    (fderiv ℝ (matrixSchurFrameChart Q T) (x, y)).toLinearMap
  let B := E.toLinearMap.comp (C.comp E.symm.toLinearMap)
  have hux : (Q x)ᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    have hh := hunit.self_of_nhds
    have hx : Q x * (Q x)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hh
    apply Matrix.mem_unitaryGroup_iff'.mpr
    change ((Q x)ᴴ)ᴴ * (Q x)ᴴ = 1
    rw [Matrix.conjTranspose_conjTranspose]
    exact hx
  have hB : |B.det| = 1 := by
    have he : B.det = C.det := LinearMap.det_conj C E
    rw [he]
    exact matrixUnitaryConjugation_abs_det (Q x)ᴴ hux
  have heq : matrixSchurFrameNormalizedDerivative Q T x y = B.comp J := by
    have hE : ∀ z, E.symm (schurEntryCoordinates z) = z := fun z => E.symm_apply_apply z
    have hE2 : ∀ z, E z = schurEntryCoordinates z := fun _ => rfl
    have hC : ∀ z : Matrix (Fin n) (Fin n) ℂ, C z = (Q x)ᴴ * z * Q x := fun z =>
      (matrixUnitaryConjugation_apply (Q x)ᴴ z).trans (by
        rw [Matrix.conjTranspose_conjTranspose]
        rfl)
    rw [matrixSchurFrameNormalizedDerivative_eq Q T x y D hQ hunit]
    apply LinearMap.ext
    intro p
    rw [LinearMap.comp_apply]
    simp only [B, J, LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe, hE,
      hE2, hC]
    rw [matrixSchurFrameChart_normalized_fderiv Q T x p.1 y p.2 D hQ hunit]
    rfl
  have he : |(matrixSchurFrameNormalizedDerivative Q T x y).det| = |J.det| := by
    rw [heq, LinearMap.det_comp, abs_mul, hB, one_mul]
  rw [matrixSchurFrameNormalizedDerivative_det Q T hT x y D hQ hunit,
    abs_mul, abs_of_nonneg (vandermondeWeight_nonneg _)] at he
  exact he.symm

end
end GinibrePoincare
