/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryGaussianNoiseLSI.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianFiniteIndexBoundedLSI
public import LeanPool.GinibrePoincare.Analysis.StrongConvexBoundedLipschitzLSIExtension
public import LeanPool.GinibrePoincare.Analysis.FinitePiDensity

/-! # The finite Gaussian-noise entropy input for the Langevin proof
The input covers bounded Lipschitz functions, so differentiability of the
entire stochastic flow in every Gaussian coordinate is not assumed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ContDiff
namespace GinibrePoincare
noncomputable section

/-- Absolute continuity of the actual finite Gaussian noise law. -/
theorem bakryEmeryGaussianNoise_absolutelyContinuous
    (I : Type*) [Fintype I] (v : ℝ≥0) (hv : v ≠ 0) :
    Measure.pi (fun _ : I => gaussianReal 0 v) ≪ (volume : Measure (I → ℝ)) := by
  classical
  let (i : I) : IsProbabilityMeasure (volume.withDensity (gaussianPDF 0 v)) := by
    rw [← gaussianReal_of_var_ne_zero 0 hv]
    infer_instance
  simp_rw [gaussianReal_of_var_ne_zero 0 hv]
  rw [Measure.pi_withDensity (fun _ : I => (volume : Measure ℝ))
    (fun _ : I => gaussianPDF 0 v) (fun _ => measurable_gaussianPDF 0 v), ← volume_pi]
  exact withDensity_absolutelyContinuous _ _

/-- Sharp LSI for bounded Lipschitz observables of any nonempty finite Gaussian
noise family, with the actual a.e. coordinate derivatives in its energy. -/
theorem bakryEmeryGaussianNoise_lsi_boundedLipschitz
    (I : Type*) [Fintype I] [DecidableEq I] [Nonempty I] (v : ℝ≥0) (hv : v ≠ 0)
    (f : (I → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (C : ℝ) (hb : ∀ x, |f x| ≤ C) :
    squareEntropy (Measure.pi (fun _ : I => gaussianReal 0 v)) f ≤
      (2 * (v : ℝ)) * ∫ x, directionalEnergy (fun i : I => Pi.single i 1) f x
        ∂Measure.pi (fun _ : I => gaussianReal 0 v) := by
  apply boundedLipschitz_lsi_of_C1 volume (Measure.pi (fun _ : I => gaussianReal 0 v))
    (bakryEmeryGaussianNoise_absolutelyContinuous I v hv)
    (fun i : I => Pi.single i 1) (2 * (v : ℝ)) _ f hf C
      (by simpa only [Real.norm_eq_abs] using hb)
  intro g hg L hL D hD
  have hD0 : 0 ≤ D := (norm_nonneg (g 0)).trans (hD 0)
  exact gaussianFiniteIndex_lsi_bounded_C1 I v g hg D (L : ℝ) hD0
    (by simpa only [Real.norm_eq_abs] using hD)
    (fun x => norm_fderiv_le_of_lipschitz ℝ hL)

end
end GinibrePoincare
