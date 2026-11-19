/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianClosedFormCurl.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianClosedFormCoefficients
public import LeanPool.GinibrePoincare.Analysis.GaussianDbarWeakDomain

/-! # Actual weak curl forces Hermite coefficient compatibility

The coefficient identity here follows from compact-test weak closedness,
using the actual Gaussian adjoint and its spatial cutoff limits. No spectral
closedness hypothesis is substituted for distributional closedness.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section
open ComplexHermite

/-- Hermite curl identity derived from the genuine compact-test relation. -/
theorem gaussianWeakClosedForm_hermiteCurl {n : ℕ} (hn : 0 < n)
    (α : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hα : IsGaussianWeakClosedForm n α) (j k : Fin n)
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
    have hχ : ContDiff ℝ 1 (fun z => (ginibreSpatialCutoff n m z : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp ((ginibreSpatialCutoff_smooth n m).of_le (by simp))
    have hcχ : HasCompactSupport (fun z => (ginibreSpatialCutoff n m z : ℂ)) :=
      (ginibreSpatialCutoff_compact n m).comp_left Complex.ofReal_zero
    exact gaussianWeakClosedForm_integral_identity α hα j k _
      (hχ.mul (contDiff_multivariateNormalized_real n hn _ _)) hcχ.mul_right
  exact tendsto_nhds_unique hleft (hright.congr (fun m => (heq m).symm))

/-- Positive-coordinate source compatibility, derived from weak curl. -/
theorem gaussianForm_sourceCompatibility_of_coefficientCurl {n : ℕ} (hn : 0 < n)
    (α : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hcurl : ∀ (j k : Fin n) (pq : HermiteMultiIndex n),
      (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
        gaussianHermiteCoefficient hn (α k) (raiseHermiteIndex j pq) =
      (Real.sqrt (n * (pq.2 k + 1) : ℕ) : ℂ) *
        gaussianHermiteCoefficient hn (α j) (raiseHermiteIndex k pq))
    (r : HermiteMultiIndex n)
    (j k : Fin n) (hrj : 0 < r.2 j) (hrk : 0 < r.2 k) :
    (Real.sqrt (n * r.2 j : ℕ) : ℂ) *
      gaussianHermiteCoefficient hn (α k) (lowerHermiteIndex k r) =
    (Real.sqrt (n * r.2 k : ℕ) : ℂ) *
      gaussianHermiteCoefficient hn (α j) (lowerHermiteIndex j r) := by
  by_cases hjk : j = k
  · subst k
    rfl
  have hkj : k ≠ j := Ne.symm hjk
  let s := lowerHermiteIndex j (lowerHermiteIndex k r)
  have hs_j : s.2 j + 1 = r.2 j := by
    simp [s, lowerHermiteIndex, lowerAt, hjk]
    omega
  have hs_k : s.2 k + 1 = r.2 k := by
    simp [s, lowerHermiteIndex, lowerAt, hkj]
    omega
  have hsraisej : raiseHermiteIndex j s = lowerHermiteIndex k r := by
    apply Prod.ext
    · rfl
    · funext l
      by_cases hlj : l = j
      · subst l
        simp [s, raiseHermiteIndex, lowerHermiteIndex, raiseAt, lowerAt, hjk]
        omega
      · simp [s, raiseHermiteIndex, lowerHermiteIndex, raiseAt, lowerAt, hlj]
  have hsraisek : raiseHermiteIndex k s = lowerHermiteIndex j r := by
    apply Prod.ext
    · rfl
    · funext l
      by_cases hlk : l = k
      · subst l
        simp [s, raiseHermiteIndex, lowerHermiteIndex, raiseAt, lowerAt, hkj]
        omega
      · by_cases hlj : l = j
        · subst l
          simp [s, raiseHermiteIndex, lowerHermiteIndex, raiseAt, lowerAt, hjk]
        · simp [s, raiseHermiteIndex, lowerHermiteIndex, raiseAt, lowerAt, hlj, hlk]
  have h := hcurl j k s
  rw [hs_j, hs_k, hsraisej, hsraisek] at h
  exact h

/-- The canonical potential has exactly the desired coordinate lowering
coefficients. Both the potential and the input are actual Gaussian L² vectors;
closedness is the compact-test condition, not a spectral premise. -/
theorem gaussianForm_potentialCoefficient_of_coefficientCurl {n : ℕ} (hn : 0 < n)
    (α : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hcurl : ∀ (j k : Fin n) (pq : HermiteMultiIndex n),
      (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
        gaussianHermiteCoefficient hn (α k) (raiseHermiteIndex j pq) =
      (Real.sqrt (n * (pq.2 k + 1) : ℕ) : ℂ) *
        gaussianHermiteCoefficient hn (α j) (raiseHermiteIndex k pq))
    (j : Fin n) (pq : HermiteMultiIndex n) :
    gaussianHermiteCoefficient hn (α j) pq =
      (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
        gaussianHermiteCoefficient hn (gaussianClosedFormPotential α hn)
          (raiseHermiteIndex j pq) := by
  let r := raiseHermiteIndex j pq
  have hrj : 0 < r.2 j := by simp [r, raiseHermiteIndex, raiseAt]
  have hrpos : 0 < ∑ k : Fin n, r.2 k := hrj.trans_le
    (Finset.single_le_sum (fun k _ => Nat.zero_le (r.2 k)) (Finset.mem_univ j))
  have hc := gaussianClosedForm_contraction_of_compatible hn r.2 hrpos
    (fun k => gaussianHermiteCoefficient hn (α k) (lowerHermiteIndex k r)) j
    (fun k hrk => gaussianForm_sourceCompatibility_of_coefficientCurl hn α hcurl r j k hrj hrk)
  have hlow : lowerHermiteIndex j r = pq :=
    (raiseHermiteIndexEquivPositive j).left_inv pq
  rw [hlow] at hc
  rw [gaussianHermiteCoefficient_closedFormPotential]
  change gaussianHermiteCoefficient hn (α j) pq =
    (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
      gaussianClosedFormPotentialCoefficient α hn r
  simpa [gaussianClosedFormPotentialCoefficient, totalAntiDegree, hlow,
    r, raiseHermiteIndex, raiseAt] using hc.symm

/-- Actual weak closedness supplies every algebraic compatibility premise. -/
theorem gaussianWeakClosedForm_potentialCoefficient {n : ℕ} (hn : 0 < n)
    (α : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hα : IsGaussianWeakClosedForm n α) (j : Fin n) (pq : HermiteMultiIndex n) :
    gaussianHermiteCoefficient hn (α j) pq =
      (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
        gaussianHermiteCoefficient hn (gaussianClosedFormPotential α hn)
          (raiseHermiteIndex j pq) :=
  gaussianForm_potentialCoefficient_of_coefficientCurl hn α
    (gaussianWeakClosedForm_hermiteCurl hn α hα) j pq

/-- The explicitly synthesized Gaussian potential solves every actual
weakly closed square-integrable (0,1)-form. -/
theorem gaussianClosedFormPotential_weakDbar {n : ℕ} (hn : 0 < n)
    (α : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hα : IsGaussianWeakClosedForm n α) (j : Fin n) :
    IsGaussianWeakDbar n (gaussianClosedFormPotential α hn) (α j) j :=
  gaussianWeakDbar_of_hermiteCoefficient hn _ _ j
    (gaussianWeakClosedForm_potentialCoefficient hn α hα j)

/-- Remark 2.4: arbitrary actual weakly closed Gaussian square-integrable
(0,1)-forms admit a solution with the paper's sharp `1/n` bound. The equation
is the ordinary Lebesgue distributional `∂̄` equation, not a spectral proxy. -/
theorem gaussianClosedFormSolvability {n : ℕ} (hn : 0 < n)
    (α : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hα : IsGaussianWeakClosedForm n α) :
    ∃ u : Lp ℂ 2 (complexGaussianMeasure n),
      ‖u‖ ^ 2 ≤ (n : ℝ)⁻¹ * ∑ j : Fin n, ‖α j‖ ^ 2 ∧
      ∀ j : Fin n, IsGaussianVolumeDistributionalDbar n u (α j) j := by
  refine ⟨gaussianClosedFormPotential α hn,
    gaussianClosedFormPotential_norm_sq_le α hn, ?_⟩
  intro j
  exact gaussianWeakDbar_volumeDistributional hn _ _ j
    (gaussianClosedFormPotential_weakDbar hn α hα j)

end
end GinibrePoincare

