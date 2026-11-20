/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianClosedFormVolume.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianClosedFormCurl
public import LeanPool.GinibrePoincare.Analysis.GaussianDbarSmoothTests

/-! # Remark 2.4 for arbitrary ordinary distributionally closed forms

The hypothesis is ordinary Lebesgue distributional curl against compact
C∞ tests. The potential is constructed in the actual Gaussian L² space.
Neither spectral compatibility nor an existing solution is assumed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
open ComplexHermite

/-- Ordinary distributional closedness of a square-integrable (0,1)-form.
Local Lebesgue integrability follows from Gaussian L² membership for `n>0`. -/
def IsGaussianVolumeClosedForm (n : ℕ)
    (α : Fin n → Lp ℂ 2 (complexGaussianMeasure n)) : Prop :=
  ∀ (j k : Fin n) (θ : Configuration n → ℂ),
    ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ z, α k z * dbarComponent θ j z) =
        ∫ z, α j z * dbarComponent θ k z

/-- Multiplication of compact smooth tests by the explicit Gaussian density
converts ordinary distributional curl to the weighted adjoint identity. -/
theorem gaussianVolumeClosedForm_weightedIntegral_identity {n : ℕ} (hn : 0 < n)
    (α : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hα : IsGaussianVolumeClosedForm n α) (j k : Fin n)
    (θ : Configuration n → ℂ) (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ) :
    (∫ z, α k z * ((n : ℂ) * z j * θ z - dbarComponent θ j z)
      ∂complexGaussianMeasure n) =
    ∫ z, α j z * ((n : ℂ) * z k * θ z - dbarComponent θ k z)
      ∂complexGaussianMeasure n := by
  let ρ : Configuration n → ℂ := fun z => gaussianLebesgueDensityReal n z
  have hρ : ContDiff ℝ ∞ ρ :=
    Complex.ofRealCLM.contDiff.comp (contDiff_gaussianLebesgueDensityReal n)
  have hd (r : Fin n) (z : Configuration n) :
      dbarComponent (fun z => ρ z * θ z) r z =
        -(ρ z * ((n : ℂ) * z r * θ z - dbarComponent θ r z)) := by
    rw [dbarComponent_mul (hρ.differentiable (by simp)) (hθ.differentiable (by simp))]
    have hr := dbarComponent_gaussianLebesgueDensityReal n r z
    change dbarComponent ρ r z = -(n : ℂ) * z r * ρ z at hr
    rw [hr]
    ring
  have hside (r : Fin n) (u : Lp ℂ 2 (complexGaussianMeasure n)) :
      (∫ z, u z * ((n : ℂ) * z r * θ z - dbarComponent θ r z)
        ∂complexGaussianMeasure n) =
      -(∫ z, u z * dbarComponent (fun w => ρ w * θ w) r z) := by
    rw [integral_complexGaussian_eq_density_volume hn, ← integral_neg]
    apply integral_congr_ae
    filter_upwards with z
    rw [hd]
    change ρ z * (u z * _) = _
    ring
  rw [hside j (α k), hside k (α j)]
  exact congrArg Neg.neg (hα j k (fun z => ρ z * θ z) (hρ.mul hθ) hc.mul_left)

/-- The exact Hermite curl coefficients follow from arbitrary ordinary
C∞ distributional closedness. -/
theorem gaussianVolumeClosedForm_hermiteCurl {n : ℕ} (hn : 0 < n)
    (α : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hα : IsGaussianVolumeClosedForm n α) (j k : Fin n)
    (pq : HermiteMultiIndex n) :
    (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
      gaussianHermiteCoefficient hn (α k) (raiseHermiteIndex j pq) =
    (Real.sqrt (n * (pq.2 k + 1) : ℕ) : ℂ) *
      gaussianHermiteCoefficient hn (α j) (raiseHermiteIndex k pq) := by
  have hleft := gaussianHermiteCutoff_adjointIntegral_tendsto hn (α k) j pq
  have hright := gaussianHermiteCutoff_adjointIntegral_tendsto hn (α j) k pq
  have heq (m : ℕ) :
      (∫ z, α k z * ((n : ℂ) * z j *
        ((ginibreSpatialCutoff n m z : ℂ) * multivariateNormalized n hn pq.2 pq.1 z) -
        dbarComponent (fun w => (ginibreSpatialCutoff n m w : ℂ) *
          multivariateNormalized n hn pq.2 pq.1 w) j z) ∂complexGaussianMeasure n) =
      ∫ z, α j z * ((n : ℂ) * z k *
        ((ginibreSpatialCutoff n m z : ℂ) * multivariateNormalized n hn pq.2 pq.1 z) -
        dbarComponent (fun w => (ginibreSpatialCutoff n m w : ℂ) *
          multivariateNormalized n hn pq.2 pq.1 w) k z) ∂complexGaussianMeasure n := by
    have hχ : ContDiff ℝ ∞ (fun z => (ginibreSpatialCutoff n m z : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (ginibreSpatialCutoff_smooth n m)
    have hcχ : HasCompactSupport (fun z => (ginibreSpatialCutoff n m z : ℂ)) :=
      (ginibreSpatialCutoff_compact n m).comp_left Complex.ofReal_zero
    exact gaussianVolumeClosedForm_weightedIntegral_identity hn α hα j k _
      (hχ.mul (contDiff_multivariateNormalized_real_smooth n hn _ _)) hcχ.mul_right
  exact tendsto_nhds_unique hleft (hright.congr (fun m => (heq m).symm))

/-- Literal closed-form solvability of Remark 2.4: every square-integrable
ordinary distributionally closed (0,1)-form has a Gaussian L² potential with
`dbar u = α` in ordinary volume distributions and the sharp `1/n` norm bound. -/
theorem gaussianVolumeClosedFormSolvability {n : ℕ} (hn : 0 < n)
    (α : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hα : IsGaussianVolumeClosedForm n α) :
    ∃ u : Lp ℂ 2 (complexGaussianMeasure n),
      ‖u‖ ^ 2 ≤ (n : ℝ)⁻¹ * ∑ j : Fin n, ‖α j‖ ^ 2 ∧
      ∀ j : Fin n, IsGaussianVolumeDistributionalDbar n u (α j) j := by
  refine ⟨gaussianClosedFormPotential α hn,
    gaussianClosedFormPotential_norm_sq_le α hn, ?_⟩
  intro j
  apply gaussianWeakDbar_volumeDistributional hn
  apply gaussianWeakDbar_of_hermiteCoefficient hn
  exact gaussianForm_potentialCoefficient_of_coefficientCurl hn α
    (gaussianVolumeClosedForm_hermiteCurl hn α hα) j

end
end GinibrePoincare

