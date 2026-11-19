/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralSobolevCoordinates.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurEntryVolume
public import LeanPool.GinibrePoincare.Analysis.MatrixGaussianH1Closure
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevFullWeightedDomain

/-! # Actual entry-coordinate and L² transports for spectral Sobolev domains -/

@[expose] public section
open MeasureTheory Matrix
namespace GinibrePoincare
noncomputable section

/-- The continuous linear equivalence between configurations and matrices given by the entry
labelling `e`: the `(i, j)` entry is `z (e.symm (i, j))`. -/
def matrixComplexEntryEquiv {n m : ℕ} (e : Fin m ≃ Fin n × Fin n) :
    Configuration m ≃L[ℝ] MatrixRealSpace n where
  toFun z := fun i j => z (e.symm (i, j))
  invFun A := fun k => A (e k).1 (e k).2
  left_inv z := by funext k; simp
  right_inv A := by funext i j; simp
  map_add' z w := rfl
  map_smul' c z := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Uncurrying `Fin n → Fin n → ℂ` to `Fin n × Fin n → ℂ`, as a measurable equivalence. -/
def matrixUncurryMeasurableEquiv (n : ℕ) :
    MatrixRealSpace n ≃ᵐ (Fin n × Fin n → ℂ) where
  toFun := Function.uncurry
  invFun := Function.curry
  left_inv A := rfl
  right_inv A := rfl
  measurable_toFun := by
    change Measurable (Function.uncurry : MatrixRealSpace n → (Fin n × Fin n → ℂ))
    fun_prop
  measurable_invFun := by
    change Measurable (Function.curry : (Fin n × Fin n → ℂ) → MatrixRealSpace n)
    fun_prop

theorem matrixComplexEntryEquiv_volume_preserving {n m : ℕ}
    (e : Fin m ≃ Fin n × Fin n) :
    MeasurePreserving (matrixComplexEntryEquiv e)
      (volume : Measure (Configuration m)) (volume : Measure (MatrixRealSpace n)) := by
  have h₁ := measurePreserving_piCongrLeft
    (fun _ : Fin n × Fin n => (volume : Measure ℂ)) e
  have h₂ := (matrixVolume_uncurry_preserving n).symm (matrixUncurryMeasurableEquiv n)
  convert h₂.comp h₁ using 1
  funext z i j
  change z (e.symm (i, j)) = (Equiv.piCongrLeft (fun _ => ℂ) e) z (i, j)
  rw [Equiv.piCongrLeft_apply_eq_cast, cast_eq]

/-- Every actual measure preserving coordinate equivalence yields a genuine
real L² isometry equivalence in the pullback direction. -/
def realL2CoordinatePullbackEquiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) :
    Lp ℝ 2 ν ≃ₗᵢ[ℝ] Lp ℝ 2 μ :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℝ e he) (by
    intro F
    refine ⟨Lp.compMeasurePreserving e.symm (he.symm e) F, ?_⟩
    change Lp.compMeasurePreserving e he
      (Lp.compMeasurePreserving e.symm (he.symm e) F) = F
    rw [← Lp.compMeasurePreserving_comp_apply]
    have hi : (e.symm : Y → X) ∘ e = id := by funext x; exact e.symm_apply_apply x
    simp only [hi, Lp.compMeasurePreserving_id_apply])

end
end GinibrePoincare
