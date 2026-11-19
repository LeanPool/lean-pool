/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurGaussianIntegration.lean.
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

/-!
# Matrix Schur Gaussian integration

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixSchurChart_gaussianDensity_lintegral`,
`matrixGaussianMeasure_schurChart_density`.
-/

@[expose] public section

open Matrix NormedSpace MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator Topology ENNReal
namespace GinibrePoincare
noncomputable section

/-- Local Schur change of variables in the original matrix-entry Lebesgue measure. -/
theorem matrixSchurChart_lintegral {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ i j, j < i → T i j = 0)
    (hd : Function.Injective (fun i => T i i))
    (s : Set (SchurCoordinates n)) (hs : MeasurableSet s)
    (hsub : s ⊆ (schurLocalChart T hT hd).source)
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
  have hi := matrixSchurEntryChart_lintegral T hT hd s hs hsub (fun z => g (E.symm z))
  rw [hi]
  apply lintegral_congr
  intro p
  have hp : E.symm (matrixSchurEntryChart T p) =
      matrixSchurFrameChart (matrixSchurExponentialFrame n) T p := E.symm_apply_apply _
  rw [hp]

/-- The diagonal Gaussian, strict-upper Gaussian, Vandermonde, and angular factor
appear together in an actual local matrix-volume integral. -/
theorem matrixSchurChart_gaussianDensity_lintegral {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ i j, j < i → T i j = 0)
    (hd : Function.Injective (fun i => T i i))
    (s : Set (SchurCoordinates n)) (hs : MeasurableSet s)
    (hsub : s ⊆ (schurLocalChart T hT hd).source)
    (g : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞) :
    ∫⁻ A in matrixSchurFrameChart (matrixSchurExponentialFrame n) T '' s,
        matrixGaussianDensity n A * g A =
      ∫⁻ p in s, ENNReal.ofReal (vandermondeWeight (fun i => (T + schurUpperCombination p.2) i i) *
        matrixSchurAngularDensity n p.1) *
        ENNReal.ofReal (((n : ℝ) / Real.pi) ^ (n * n) *
          Real.exp (-(n : ℝ) * ∑ i, Complex.normSq ((T + schurUpperCombination p.2) i i)) *
          Real.exp (-(n : ℝ) * matrixHSNormSq
            ((T + schurUpperCombination p.2) - Matrix.diagonal fun i => (T + schurUpperCombination
                p.2) i i))) *
          g (matrixSchurFrameChart (matrixSchurExponentialFrame n) T p) := by
  rw [matrixSchurChart_lintegral T hT hd s hs hsub]
  apply lintegral_congr
  intro p
  rw [matrixSchurFrameChart, matrixGaussianDensity_unitary_schur n _ _
    (matrixSchurExponentialFrame_unitary n p.1)]
  exact (mul_assoc _ _ _).symm

/-- The local chart integral uses the actual Gaussian matrix probability measure. -/
theorem matrixGaussianMeasure_schurChart_density {n : ℕ} (hn : 0 < n)
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ i j, j < i → T i j = 0)
    (hd : Function.Injective (fun i => T i i))
    (s : Set (SchurCoordinates n)) (hs : MeasurableSet s)
    (hsub : s ⊆ (schurLocalChart T hT hd).source)
    (g : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞) :
    ∫⁻ A in matrixSchurFrameChart (matrixSchurExponentialFrame n) T '' s,
        g A ∂matrixGaussianMeasure n =
      ∫⁻ A in matrixSchurFrameChart (matrixSchurExponentialFrame n) T '' s,
        matrixGaussianDensity n A * g A := by
  let : BorelSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (BorelSpace (Fin n → Fin n → ℂ))
  have hi : InjOn (matrixSchurFrameChart (matrixSchurExponentialFrame n) T) s := by
    rw [matrixSchurExponentialChart_eq]
    exact (schurLocalChart T hT hd).injOn.mono hsub
  have himage := hs.image_of_continuousOn_injOn
    (matrixSchurExponentialChart_differentiable T).continuous.continuousOn hi
  have hm : Measurable (matrixGaussianDensity n) := by
    unfold matrixGaussianDensity
    simp_rw [matrixHSNormSq_eq_sum]
    fun_prop
  rw [matrixGaussianMeasure_eq_withDensity hn]
  exact setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable
    volume hm g himage (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)

end
end GinibrePoincare
