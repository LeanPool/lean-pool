/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixOverlapGradientIntegrability.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixOverlapLowerBound
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralIntegralTransport
public import LeanPool.GinibrePoincare.Analysis.GinibrePermutationGradient
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-! # Finite overlap energy controls the ordinary Ginibre gradient

Differentiate the permutation identity to prove invariance of the classical
squared gradient. On the almost-everywhere simple-spectrum set, the matrix
overlap energy bounds this quantity by a factor of four. Transport integrals
through the spectral law to obtain both Ginibre gradient integrability and the
energy bound. Finally identify the squared Euclidean gradient norm with the
coordinate sum to obtain its L² membership.

The input here is finite overlap energy, not matrix Sobolev membership. The
latter is handled by the separate correspondence matrix weak-closure bridge.
-/

@[expose] public section

open Matrix MeasureTheory Filter
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- Relabeling invariance of the ordinary gradient energy follows by the
actual chain rule, requiring differentiability rather than smoothness. -/
theorem realGradientNormSq_symmetric {n : ℕ} (F : Configuration n → ℝ)
    (hF : Differentiable ℝ F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z)
    (e : Fin n ≃ Fin n) (z : Configuration n) :
    realGradientNormSq F (z ∘ e) = realGradientNormSq F z := by
  classical
  let P := (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin n => ℂ) e.symm)
  have hP (x : Configuration n) : P x = x ∘ e := by
    ext i
    simp [P, ContinuousLinearEquiv.piCongrLeft, 
      Equiv.piCongrLeft_apply]
  have hFP : F ∘ P = F := funext fun x => by simp only [Function.comp_apply, hP, hsym]
  have hd := fderiv_comp (x := z) (f := P) (g := F)
    (hF (P z)) P.differentiableAt
  rw [hFP, P.hasFDerivAt.fderiv] at hd
  have hdir (i : Fin n) (w : ℂ) : P (coordinateDirection i w) =
      coordinateDirection (e.symm i) w := by
    ext j
    simp [hP, coordinateDirection, Equiv.eq_symm_apply]
  have hr (i : Fin n) : fderiv ℝ F z (realCoordinateDirection i) =
      fderiv ℝ F (z ∘ e) (realCoordinateDirection (e.symm i)) := by
    rw [hd]
    change fderiv ℝ F (P z) (P (coordinateDirection i 1)) = _
    rw [hP, hdir]
    rfl
  have hi (i : Fin n) : fderiv ℝ F z (imaginaryCoordinateDirection i) =
      fderiv ℝ F (z ∘ e) (imaginaryCoordinateDirection (e.symm i)) := by
    rw [hd]
    change fderiv ℝ F (P z) (P (coordinateDirection i Complex.I)) = _
    rw [hP, hdir]
    rfl
  unfold realGradientNormSq
  simp_rw [hr, hi]
  exact (e.symm.sum_comp (fun i => (fderiv ℝ F (z ∘ e) (realCoordinateDirection i))^2 +
    (fderiv ℝ F (z ∘ e) (imaginaryCoordinateDirection i))^2)).symm

theorem realGradientNormSq_measurable {n : ℕ} (F : Configuration n → ℝ) :
    Measurable (realGradientNormSq F) := by
  unfold realGradientNormSq
  apply Finset.measurable_sum
  intro i hi
  exact ((measurable_fderiv_apply_const ℝ F _).pow_const 2).add
    ((measurable_fderiv_apply_const ℝ F _).pow_const 2)

/-- Finite matrix overlap energy forces finite ordinary Ginibre gradient energy,
with the precise factor four. -/
theorem matrixOverlap_finite_gradient_energy {n : ℕ} (hn : 0 < n)
    (F : Configuration n → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z)
    (hE : Integrable (matrixSpectralOverlapEnergy n F) (matrixGaussianMeasure n)) :
    Integrable (realGradientNormSq F) (ginibreMeasure n) ∧
      (∫ z, realGradientNormSq F z ∂ginibreMeasure n) ≤
        4 * ∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n := by
  have hmeas := realGradientNormSq_measurable F
  have hMsym := realGradientNormSq_symmetric F hF hsym
  have hnonneg (z : Configuration n) : 0 ≤ realGradientNormSq F z := by
    exact Finset.sum_nonneg fun i _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hbound : ∀ᵐ A ∂matrixGaussianMeasure n,
      realGradientNormSq F (matrixMeasurableEigenvalues n A) ≤
        4 * matrixSpectralOverlapEnergy n F A := by
    filter_upwards [matrixGaussian_charpoly_separable_ae n] with A hs
    exact matrixSpectralOverlapEnergy_ge_gradient A hs F
  have hM : Integrable (fun A : Matrix (Fin n) (Fin n) ℂ =>
      realGradientNormSq F (matrixMeasurableEigenvalues n A)) (matrixGaussianMeasure n) := by
    apply (hE.const_mul 4).mono'
      (hmeas.comp (matrixMeasurableEigenvalues_measurable n)).aestronglyMeasurable
    filter_upwards [hbound] with A hA
    change ‖realGradientNormSq F (matrixMeasurableEigenvalues n A)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)]
    exact hA
  refine ⟨(matrixSpectralLift_integrable_iff hn _ hmeas hMsym).mp hM, ?_⟩
  rw [← matrixSpectralLift_integral hn _ hmeas hMsym]
  erw [← integral_const_mul]
  exact integral_mono_ae hM (hE.const_mul 4) hbound

theorem matrixOverlap_finite_gradient_memLp {n : ℕ} (hn : 0 < n)
    (F : Configuration n → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z)
    (hE : Integrable (matrixSpectralOverlapEnergy n F) (matrixGaussianMeasure n)) :
    MemLp (ginibreEuclideanGradient F) 2 (ginibreMeasure n) := by
  have hm : Measurable (ginibreEuclideanGradient F) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin n × Fin 2 => ℝ)).measurable.comp
    apply Measurable.of_eval
    intro k
    by_cases hk : k.2 = 0
    · simpa only [hk, ite_true] using measurable_fderiv_apply_const ℝ F (realCoordinateDirection
        k.1)
    · simpa only [hk, ite_false] using measurable_fderiv_apply_const ℝ F
        (imaginaryCoordinateDirection k.1)
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  simpa only [ginibreEuclideanGradient_norm_sq] using
    (matrixOverlap_finite_gradient_energy hn F hF hsym hE).1

end
end GinibrePoincare
