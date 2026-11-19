/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurFullJacobian.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurLocalChart
public import LeanPool.GinibrePoincare.Analysis.MatrixSchurRealJacobian

/-! # Full Schur differential in matrix entry coordinates

Split the matrix entries into strict lower and upper coordinates and construct
the explicit inverse reassembly map. In these coordinates the Schur tangent
map has blocks `(lowerJacobian, 0; upperTangent, identity)`. The determinant
of this triangular block map is therefore the lower-block determinant, whose
real value is the Vandermonde weight. Composing the actual chart derivative
with the entry equivalence identifies this algebraic determinant with the
Jacobian of the genuine Schur chart.
-/

@[expose] public section

open Matrix
open scoped Matrix Matrix.Norms.Operator
namespace GinibrePoincare
noncomputable section

/-- Entry coordinates, with the strict lower entries followed by the upper entries. -/
def schurEntryCoordinates {n : ℕ} : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] SchurCoordinates n where
  toFun A := (fun p => A (schurLowerRow p) (schurLowerCol p), fun p => A p.val.1 p.val.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The matrix with prescribed strictly lower entries `x` and upper entries `y`; inverse of
`schurEntryCoordinates`. -/
def schurEntryCoordinatesInverse (n : ℕ) : SchurCoordinates n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (((schurLowerCLM n).restrictScalars ℝ).comp (ContinuousLinearMap.fst ℝ _ _)).toLinearMap +
    (((schurUpperCLM n).restrictScalars ℝ).comp (ContinuousLinearMap.snd ℝ _ _)).toLinearMap

theorem schurEntryCoordinatesInverse_apply (n : ℕ) (p : SchurCoordinates n) :
    schurEntryCoordinatesInverse n p = schurLowerCombination p.1 + schurUpperCombination p.2 := by
  simp [schurEntryCoordinatesInverse, schurLowerCLM_apply, schurUpperCLM_apply]

theorem schurEntryCoordinates_left_inv (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    schurEntryCoordinatesInverse n (schurEntryCoordinates A) = A := by
  rw [schurEntryCoordinatesInverse_apply]
  ext i j
  rw [Matrix.add_apply]
  by_cases hij : j < i
  · let p : SchurLowerIndex n := ⟨toLex (j, OrderDual.toDual i), hij⟩
    have hh : schurLowerCombination (schurEntryCoordinates A).1 i j = A i j :=
      by simpa [p, schurLowerRow, schurLowerCol, schurEntryCoordinates] using
        schurLowerCombination_lowerEntry (schurEntryCoordinates A).1 p
    rw [hh, schurUpperCombination_lower_zero _ i j hij, add_zero]
  · have hh : schurUpperCombination (schurEntryCoordinates A).2 i j = A i j :=
      schurUpperCombination_entry _ ⟨(i, j), le_of_not_gt hij⟩
    rw [schurLowerCombination_upperEntries_zero _ i j (le_of_not_gt hij), hh, zero_add]

theorem schurEntryCoordinates_right_inv (n : ℕ) (p : SchurCoordinates n) :
    schurEntryCoordinates (schurEntryCoordinatesInverse n p) = p := by
  rw [schurEntryCoordinatesInverse_apply]
  apply Prod.ext
  · funext q
    change (schurLowerCombination p.1 + schurUpperCombination p.2)
      (schurLowerRow q) (schurLowerCol q) = p.1 q
    have hz : schurUpperCombination p.2 (schurLowerRow q) (schurLowerCol q) = 0 :=
      schurUpperCombination_lower_zero _ _ _ q.property
    rw [Matrix.add_apply, schurLowerCombination_lowerEntry, hz, add_zero]
  · funext q
    change (schurLowerCombination p.1 + schurUpperCombination p.2) q.val.1 q.val.2 = p.2 q
    rw [Matrix.add_apply, schurLowerCombination_upperEntries_zero _ _ _ q.property,
      schurUpperCombination_entry, zero_add]

/-- Entry coordinates (strictly lower entries, upper entries) as a real-linear equivalence. -/
def schurEntryCoordinatesEquiv (n : ℕ) : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℝ] SchurCoordinates n :=
  { schurEntryCoordinates with
    invFun := schurEntryCoordinatesInverse n
    left_inv := schurEntryCoordinates_left_inv n
    right_inv := schurEntryCoordinates_right_inv n }

/-- The Schur tangent map expressed in entry coordinates in its codomain. -/
def schurCoordinateJacobian {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) :
    SchurCoordinates n →ₗ[ℝ] SchurCoordinates n :=
  schurEntryCoordinates.comp (schurCoordinateTangentCLM T).toLinearMap

theorem real_triangular_prod_det {E F : Type*} [AddCommGroup E] [AddCommGroup F]
    [Module ℝ E] [Module ℝ F] [Module.Free ℝ E] [Module.Free ℝ F]
    [Module.Finite ℝ E] [Module.Finite ℝ F] (A : E →ₗ[ℝ] E) (C : E →ₗ[ℝ] F) :
    ((A.comp (LinearMap.fst ℝ E F)).prod
      (C.comp (LinearMap.fst ℝ E F) + LinearMap.snd ℝ E F)).det = A.det := by
  classical
  let b := Module.Free.chooseBasis ℝ E
  let c := Module.Free.chooseBasis ℝ F
  have hm : LinearMap.toMatrix (b.prod c) (b.prod c)
      ((A.comp (LinearMap.fst ℝ E F)).prod
        (C.comp (LinearMap.fst ℝ E F) + LinearMap.snd ℝ E F)) =
      Matrix.fromBlocks (LinearMap.toMatrix b b A) 0 (LinearMap.toMatrix b c C) 1 := by
    ext (i | i) (j | j) <;> simp [LinearMap.toMatrix, Matrix.one_apply, Finsupp.single_apply,
        eq_comm]
  rw [← LinearMap.det_toMatrix (b.prod c), hm, Matrix.det_fromBlocks_zero₁₂]
  simp [LinearMap.det_toMatrix]

/-- The upper-entry component of the Schur coordinate Jacobian at `T`, restricted to lower
(skew) coordinates. -/
def schurUpperTangent {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) :
    (SchurLowerIndex n → ℂ) →ₗ[ℝ] (SchurUpperIndex n → ℂ) :=
  (LinearMap.snd ℝ _ _).comp
    ((schurCoordinateJacobian T).comp (LinearMap.inl ℝ _ _))

theorem schurCoordinateJacobian_block {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) :
    schurCoordinateJacobian T =
      (((Matrix.toLin' (schurLowerJacobian T)).restrictScalars ℝ).comp
        (LinearMap.fst ℝ _ _)).prod
        ((schurUpperTangent T).comp (LinearMap.fst ℝ _ _) + LinearMap.snd ℝ _ _) := by
  apply LinearMap.ext
  intro p
  apply Prod.ext
  · funext q
    change schurCoordinateTangentCLM T p (schurLowerRow q) (schurLowerCol q) = _
    rw [schurCoordinateTangentCLM_apply]
    change (schurSkewCombination p.1 * T - T * schurSkewCombination p.1 +
      schurUpperCombination p.2) (schurLowerRow q) (schurLowerCol q) = _
    have hz : schurUpperCombination p.2 (schurLowerRow q) (schurLowerCol q) = 0 :=
      schurUpperCombination_lower_zero _ _ _ q.property
    rw [Matrix.add_apply, hz, add_zero]
    change (schurSkewCombination p.1 * T - T * schurSkewCombination p.1)
      (schurLowerRow q) (schurLowerCol q) = (schurLowerJacobian T *ᵥ p.1) q
    exact (schurLowerJacobian_skew_commutator T hT p.1 q).symm
  · funext q
    change schurCoordinateTangentCLM T p q.val.1 q.val.2 =
      schurCoordinateTangentCLM T (p.1, 0) q.val.1 q.val.2 + p.2 q
    rw [schurCoordinateTangentCLM_apply, schurCoordinateTangentCLM_apply]
    have hz : schurUpperCombination (0 : SchurUpperIndex n → ℂ) = 0 := by
      rw [← schurUpperCLM_apply, map_zero]
    simp [schurCoordinateTangent, schurUpperCombination_entry, hz]

/-- The full real Schur tangent Jacobian, with the codomain in entry coordinates. -/
theorem schurCoordinateJacobian_det {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) :
    (schurCoordinateJacobian T).det = vandermondeWeight (fun i => T i i) := by
  rw [schurCoordinateJacobian_block T hT, real_triangular_prod_det]
  exact schurLowerJacobian_real_det T hT

/-- The Jacobian factor belongs to the derivative of the actual Schur chart. -/
theorem schurCoordinateChart_entry_fderiv_det {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) :
    (fderiv ℝ (fun p => schurEntryCoordinates (schurCoordinateChart T p)) 0).det =
      vandermondeWeight (fun i => T i i) := by
  let E := (schurEntryCoordinatesEquiv n).toContinuousLinearEquiv
  have hh := E.toContinuousLinearMap.hasFDerivAt.comp (0 : SchurCoordinates n)
    (schurCoordinateChart_hasStrictFDerivAt T).hasFDerivAt
  have he : fderiv ℝ (fun p => schurEntryCoordinates (schurCoordinateChart T p)) 0 =
      E.toContinuousLinearMap.comp (schurCoordinateTangentCLM T) := hh.fderiv
  rw [he]
  change (schurCoordinateJacobian T).det = _
  exact schurCoordinateJacobian_det T hT

end
end GinibrePoincare
