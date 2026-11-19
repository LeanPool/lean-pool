/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixUnitaryVolume.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixGaussianUnitaryInvariant
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Matrix unitary volume

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixUnitaryConjugation_volume_map`.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped Matrix Matrix.Norms.Operator
namespace GinibrePoincare
noncomputable section

theorem matrixUnitaryRealMap_abs_det {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    |(matrixUnitaryRealMap U).toLinearMap.det| = 1 := by
  have hn : ‖(matrixUnitaryEuclideanMap U).det‖ = 1 := by
    rw [← LinearMap.normDet_eq_norm_det]
    exact (matrixUnitaryEuclideanIsometry U hU).normDet_eq_one
  have hd : (matrixUnitaryEuclideanMap U).det = (matrixUnitaryRealMap U).toLinearMap.det := by
    exact LinearMap.det_conj (matrixUnitaryRealMap U).toLinearMap
      (WithLp.linearEquiv 2 ℝ (MatrixRealIndex n → ℝ)).symm
  rw [hd, Real.norm_eq_abs] at hn
  exact hn

theorem matrixUnitaryConjugation_abs_det {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    |(matrixUnitaryConjugation U).toLinearMap.det| = 1 := by
  have hd : (matrixUnitaryConjugation U).toLinearMap.det = (matrixUnitaryRealMap U).toLinearMap.det
      := by
    exact LinearMap.det_conj (matrixUnitaryRealMap U).toLinearMap
      (matrixRealCoordinates n).toLinearEquiv
  rw [hd]
  exact matrixUnitaryRealMap_abs_det U hU

theorem matrixUnitaryConjugation_volume_map {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (volume : Measure (Fin n → Fin n → ℂ)).map (matrixUnitaryConjugation U) = volume := by
  let : Measure.IsAddHaarMeasure (volume : Measure (Fin n → Fin n → ℂ)) :=
    Measure.pi.isAddHaarMeasure _
  have ha := matrixUnitaryConjugation_abs_det U hU
  have hd : (matrixUnitaryConjugation U).toLinearMap.det ≠ 0 := by
    intro hh
    rw [hh, abs_zero] at ha
    norm_num at ha
  have hm := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (Fin n → Fin n → ℂ)) hd
  have hm' := hm
  simp only [abs_inv, ha, inv_one, ENNReal.ofReal_one, one_smul] at hm'
  exact hm'

end
end GinibrePoincare
