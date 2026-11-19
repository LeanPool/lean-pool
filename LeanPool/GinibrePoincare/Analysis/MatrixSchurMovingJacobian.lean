/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurMovingJacobian.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurUniqueness
public import LeanPool.GinibrePoincare.Analysis.MatrixUnitaryLowerChart

/-!
# Matrix Schur moving jacobian

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `schurMovingJacobian_det`.
-/

@[expose] public section

open Matrix
open scoped Matrix Matrix.Norms.Operator
namespace GinibrePoincare
noncomputable section

theorem matrixLowerRead_skew_commutator {n : ℕ} (T K : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) (hK : Kᴴ = -K) :
    matrixLowerRead n (K * T - T * K) = schurLowerJacobian T *ᵥ matrixLowerRead n K := by
  let c := matrixSkewReadCoordinates n K
  let D := Matrix.diagonal (fun i => (c.2 i : ℂ) * Complex.I)
  have hrec : schurSkewCombination c.1 + D = K := by
    simpa only [matrixSkewCoordinateMap_apply, c, D] using matrixSkewCoordinateMap_reconstruct n K
        hK
  have hD : ∀ i j, j < i → D i j = 0 := by
    intro i j hij
    exact Matrix.diagonal_apply_ne _ (ne_of_gt hij)
  have hDT := matrix_upper_product D T hD hT
  have hTD := matrix_upper_product T D hT hD
  funext p
  have he : K * T - T * K =
      (schurSkewCombination c.1 * T - T * schurSkewCombination c.1) + (D * T - T * D) := by
    rw [← hrec]
    noncomm_ring
  change (K * T - T * K) (schurLowerRow p) (schurLowerCol p) = _
  have h1 : (D * T) (schurLowerRow p) (schurLowerCol p) = 0 := hDT _ _ p.property
  have h2 : (T * D) (schurLowerRow p) (schurLowerCol p) = 0 := hTD _ _ p.property
  rw [he]
  simp only [Matrix.add_apply, Matrix.sub_apply, h1, h2, sub_self, add_zero]
  exact (schurLowerJacobian_skew_commutator T hT c.1 p).symm

/-- The tangent map `(x, y) ↦ W x * T - T * W x + Y` for a general lower-coordinate direction
map `W`, with `Y` the upper-triangular matrix built from `y`. -/
def schurMovingTangent {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (W : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
    SchurCoordinates n →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  let S : SchurCoordinates n →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    W.comp (ContinuousLinearMap.fst ℝ _ _)
  ((ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ)).flip T).comp S -
    ((ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ)) T).comp S +
      ((schurUpperCLM n).restrictScalars ℝ).comp (ContinuousLinearMap.snd ℝ _ _)

theorem schurMovingTangent_apply {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (W : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (p : SchurCoordinates n) :
    schurMovingTangent T W p = W p.1 * T - T * W p.1 + schurUpperCombination p.2 := by
  change W p.1 * T - T * W p.1 + schurUpperCLM n p.2 = _
  rw [schurUpperCLM_apply]

/-- `schurMovingTangent T W` read in entry coordinates. -/
def schurMovingJacobian {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (W : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
    SchurCoordinates n →ₗ[ℝ] SchurCoordinates n :=
  schurEntryCoordinates.comp (schurMovingTangent T W).toLinearMap

/-- The upper-entry component of `schurMovingJacobian T W`, restricted to lower coordinates. -/
def schurMovingUpperTangent {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (W : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
    (SchurLowerIndex n → ℂ) →ₗ[ℝ] (SchurUpperIndex n → ℂ) :=
  (LinearMap.snd ℝ _ _).comp ((schurMovingJacobian T W).comp (LinearMap.inl ℝ _ _))

theorem schurMovingJacobian_block {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0)
    (W : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (hW : ∀ x, (W x)ᴴ = -W x) :
    schurMovingJacobian T W =
      ((((Matrix.toLin' (schurLowerJacobian T)).restrictScalars ℝ).comp
        ((matrixLowerRead n).comp W).toLinearMap).comp (LinearMap.fst ℝ _ _)).prod
        ((schurMovingUpperTangent T W).comp (LinearMap.fst ℝ _ _) + LinearMap.snd ℝ _ _) := by
  apply LinearMap.ext
  intro p
  apply Prod.ext
  · change matrixLowerRead n (schurMovingTangent T W p) = _
    rw [schurMovingTangent_apply, map_add]
    have hz : matrixLowerRead n (schurUpperCombination p.2) = 0 := by
      funext q
      exact schurUpperCombination_lower_zero _ _ _ q.property
    rw [hz, add_zero, matrixLowerRead_skew_commutator T _ hT (hW p.1)]
    rfl
  · funext q
    change schurMovingTangent T W p q.val.1 q.val.2 =
      schurMovingTangent T W (p.1, 0) q.val.1 q.val.2 + p.2 q
    rw [schurMovingTangent_apply, schurMovingTangent_apply]
    have hz : schurUpperCombination (0 : SchurUpperIndex n → ℂ) = 0 := by
      rw [← schurUpperCLM_apply, map_zero]
    simp [schurUpperCombination_entry, hz]

/-- In a moving unitary frame, the spectral Jacobian is the Vandermonde weight times
an actual real determinant depending only on the unitary frame coordinates. -/
theorem schurMovingJacobian_det {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0)
    (W : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (hW : ∀ x, (W x)ᴴ = -W x) :
    (schurMovingJacobian T W).det = vandermondeWeight (fun i => T i i) *
      (((matrixLowerRead n).comp W).toLinearMap).det := by
  rw [schurMovingJacobian_block T hT W hW, real_triangular_prod_det,
    LinearMap.det_comp, schurLowerJacobian_real_det T hT]

end
end GinibrePoincare
