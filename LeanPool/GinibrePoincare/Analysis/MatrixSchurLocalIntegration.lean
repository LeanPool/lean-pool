/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurLocalIntegration.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurExponentialJacobian
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Matrix Schur local integration

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixSchurEntryChart_lintegral`.
-/

@[expose] public section

open Matrix NormedSpace MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator Topology ENNReal
namespace GinibrePoincare
noncomputable section

theorem matrixSchurExponentialChart_eq {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) :
    matrixSchurFrameChart (matrixSchurExponentialFrame n) T = schurCoordinateChart T := by
  funext p
  rw [schurCoordinateChart, schurCoordinateEmbedding_apply]
  exact (schurAmbientChart_skew_unitary T (schurUpperCombination p.2) p.1).2.symm

/-- The exponential-frame Schur chart around `T`, read in entry coordinates. -/
def matrixSchurEntryChart {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) :
    SchurCoordinates n → SchurCoordinates n :=
  fun p => schurEntryCoordinates (matrixSchurFrameChart (matrixSchurExponentialFrame n) T p)

/-- The derivative at `p` of the exponential-frame Schur chart around `T`, read in entry
coordinates. -/
def matrixSchurEntryDerivative {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (p : SchurCoordinates n) : SchurCoordinates n →L[ℝ] SchurCoordinates n :=
  (schurEntryCoordinatesEquiv n).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (fderiv ℝ (matrixSchurFrameChart (matrixSchurExponentialFrame n) T) p)

theorem matrixSchurExponentialChart_differentiable {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) :
    Differentiable ℝ (matrixSchurFrameChart (matrixSchurExponentialFrame n) T) := by
  intro p
  let Q := matrixSchurExponentialFrame n
  let F := ContinuousLinearMap.fst ℝ (SchurLowerIndex n → ℂ) (SchurUpperIndex n → ℂ)
  let S := ContinuousLinearMap.snd ℝ (SchurLowerIndex n → ℂ) (SchurUpperIndex n → ℂ)
  have hq := (matrixSchurExponentialFrame_differentiable n p.1).comp p F.differentiableAt
  have hu := ((schurUpperCLM n).restrictScalars ℝ).differentiableAt.comp p S.differentiableAt
  have ht := (differentiableAt_const (𝕜 := ℝ) T).add hu
  have ha := (schurConjTransposeCLM n).differentiableAt.comp p hq
  have hp := (hq.mul ht).mul ha
  have hf : matrixSchurFrameChart Q T =
      Q ∘ ⇑F * ((fun _ => T) + ⇑((schurUpperCLM n).restrictScalars ℝ) ∘ ⇑S) *
        ⇑(schurConjTransposeCLM n) ∘ Q ∘ ⇑F := by
    funext z
    change Q z.1 * (T + schurUpperCombination z.2) * (Q z.1)ᴴ =
      Q z.1 * (T + schurUpperCLM n z.2) * (Q z.1)ᴴ
    rw [schurUpperCLM_apply]
  rw [hf]
  exact hp

theorem matrixSchurEntryChart_hasFDerivAt {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (p : SchurCoordinates n) :
    HasFDerivAt (matrixSchurEntryChart T) (matrixSchurEntryDerivative T p) p :=
  (schurEntryCoordinatesEquiv n).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp p
    (matrixSchurExponentialChart_differentiable T p).hasFDerivAt

theorem matrixSchurEntryDerivative_abs_det {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ i j, j < i → T i j = 0)
    (p : SchurCoordinates n) :
    |(matrixSchurEntryDerivative T p).toLinearMap.det| =
      vandermondeWeight (fun i => (T + schurUpperCombination p.2) i i) *
        matrixSchurAngularDensity n p.1 :=
  matrixSchurExponentialJacobian T hT p.1 p.2

theorem matrixSchurEntryChart_injOn {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ i j, j < i → T i j = 0)
    (hd : Function.Injective (fun i => T i i)) :
    InjOn (matrixSchurEntryChart T) (schurLocalChart T hT hd).source := by
  intro p hp q hq he
  have he' : matrixSchurFrameChart (matrixSchurExponentialFrame n) T p =
      matrixSchurFrameChart (matrixSchurExponentialFrame n) T q :=
    (schurEntryCoordinatesEquiv n).injective he
  rw [matrixSchurExponentialChart_eq] at he'
  exact (schurLocalChart T hT hd).injOn hp hq he'

/-- Genuine local change of variables for the concrete Schur chart. -/
theorem matrixSchurEntryChart_lintegral {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ i j, j < i → T i j = 0)
    (hd : Function.Injective (fun i => T i i))
    (s : Set (SchurCoordinates n)) (hs : MeasurableSet s)
    (hsub : s ⊆ (schurLocalChart T hT hd).source)
    (g : SchurCoordinates n → ℝ≥0∞) :
    ∫⁻ z in matrixSchurEntryChart T '' s, g z =
      ∫⁻ p in s, ENNReal.ofReal (vandermondeWeight (fun i => (T + schurUpperCombination p.2) i i) *
        matrixSchurAngularDensity n p.1) * g (matrixSchurEntryChart T p) := by
  let : Measure.IsAddHaarMeasure (volume : Measure (SchurCoordinates n)) :=
    Measure.prod.instIsAddHaarMeasure
      (volume : Measure (SchurLowerIndex n → ℂ)) (volume : Measure (SchurUpperIndex n → ℂ))
  have hh := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (volume : Measure (SchurCoordinates n)) hs
    (fun p _ => (matrixSchurEntryChart_hasFDerivAt T p).hasFDerivWithinAt)
    ((matrixSchurEntryChart_injOn T hT hd).mono hsub) g
  simpa only [matrixSchurEntryDerivative_abs_det T hT] using hh

end
end GinibrePoincare
