/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurInjectiveIntegration.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurSortedDomain

/-!
# Matrix Schur injective integration

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixSchurChart_lintegral_of_injOn`.
-/

@[expose] public section

open Matrix NormedSpace MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator Topology ENNReal
namespace GinibrePoincare
noncomputable section

theorem matrixSchurChart_lintegral_of_injOn {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ i j, j < i → T i j = 0)
    (s : Set (SchurCoordinates n)) (hs : MeasurableSet s)
    (hinj : InjOn (matrixSchurFrameChart (matrixSchurExponentialFrame n) T) s)
    (g : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞) :
    ∫⁻ A in matrixSchurFrameChart (matrixSchurExponentialFrame n) T '' s, g A =
      ∫⁻ p in s, ENNReal.ofReal (vandermondeWeight (fun i => (T + schurUpperCombination p.2) i i) *
        matrixSchurAngularDensity n p.1) *
          g (matrixSchurFrameChart (matrixSchurExponentialFrame n) T p) := by
  let : BorelSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (BorelSpace (Fin n → Fin n → ℂ))
  let E := (schurEntryCoordinatesEquiv n).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hE : MeasurePreserving E := schurEntryCoordinates_volume_preserving n
  have hh := hE.setLIntegral_comp_emb E.measurableEmbedding
    (fun z => g (E.symm z)) (matrixSchurFrameChart (matrixSchurExponentialFrame n) T '' s)
  have hset : E '' (matrixSchurFrameChart (matrixSchurExponentialFrame n) T '' s) =
      matrixSchurEntryChart T '' s := by
    rw [← Set.image_comp]
    rfl
  simp only [E.symm_apply_apply, hset] at hh
  rw [hh]
  let : Measure.IsAddHaarMeasure (volume : Measure (SchurCoordinates n)) :=
    Measure.prod.instIsAddHaarMeasure
      (volume : Measure (SchurLowerIndex n → ℂ)) (volume : Measure (SchurUpperIndex n → ℂ))
  have hj : InjOn (matrixSchurEntryChart T) s := by
    intro p hp q hq he
    exact hinj hp hq (E.injective he)
  have hi := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (volume : Measure (SchurCoordinates n)) hs
    (fun p _ => (matrixSchurEntryChart_hasFDerivAt T p).hasFDerivWithinAt)
    hj (fun z => g (E.symm z))
  simp only [matrixSchurEntryDerivative_abs_det T hT] at hi
  rw [hi]
  apply lintegral_congr
  intro p
  have hp : E.symm (matrixSchurEntryChart T p) =
      matrixSchurFrameChart (matrixSchurExponentialFrame n) T p := E.symm_apply_apply _
  rw [hp]

end
end GinibrePoincare
