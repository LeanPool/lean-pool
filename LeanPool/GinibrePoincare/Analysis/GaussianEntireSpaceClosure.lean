/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianEntireSpaceClosure.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianEntireRegularity
public import LeanPool.GinibrePoincare.Analysis.GaussianEntireReconstruction
public import LeanPool.GinibrePoincare.Analysis.GaussianDbarWeakEquality

/-! # Actual entire representatives and the Gaussian zero-mode space -/

@[expose] public section
open MeasureTheory Filter
open scoped Topology BigOperators
open scoped ComplexConjugate
namespace GinibrePoincare
noncomputable section
open ComplexHermite

theorem gaussianWeakHolomorphic_has_entire_representative {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n))
    (hu : ∀ j, IsGaussianWeakDbar n u 0 j) :
    ∃ f, IsGaussianEntireRepresentative u f := by
  obtain ⟨f, hf⟩ := gaussianZeroMode_has_entire_representative hn u
  rw [gaussianWeakDbar_zero_modeZero hn u hu] at hf
  exact ⟨f, hf⟩

/-- Every actual entire Gaussian L² representative lies in the Gaussian
holomorphic zero mode; no regularity or coefficient fact is assumed. -/
theorem gaussianEntireRepresentative_zeroMode_eq {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (f : Configuration n → ℂ)
    (hf : IsGaussianEntireRepresentative u f) : gaussianHermiteMode hn 0 u = u := by
  apply gaussianWeakDbar_zero_modeZero hn u
  intro j
  apply gaussian_smooth_weak_dbar hn j u 0 f
    (gaussian_entire_contDiff_real_one hf.1) hf.2.symm
  filter_upwards [Lp.coeFn_zero ℂ 2 (complexGaussianMeasure n)] with z hz
  rw [hz, dbarComponent_eq_zero_of_differentiable_complex hf.1]
  rfl

theorem gaussianEntireL2_iff_zeroMode {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    u ∈ gaussianEntireL2 n ↔ gaussianHermiteMode hn 0 u = u := by
  constructor
  · rintro ⟨f, hf⟩
    exact gaussianEntireRepresentative_zeroMode_eq hn u f hf
  · intro h
    obtain ⟨f, hf⟩ := gaussianZeroMode_has_entire_representative hn u
    rw [h] at hf
    exact ⟨f, hf⟩

/-- The genuine Bargmann–Fock entire representative space equals the
already constructed closed Hermite zero-mode space. -/
theorem gaussianEntireL2_eq_zeroModeClosedSpan (n : ℕ) (hn : 0 < n) :
    gaussianEntireL2 n = (hermiteAntiDegreeClosedSpan n hn 0).toSubmodule := by
  ext u
  rw [gaussianEntireL2_iff_zeroMode hn u, gaussianHermiteMode_eq_antiDegreeProjection]
  exact Submodule.starProjection_eq_self_iff

/-- Remark 2.5: the actual multivariate entire L² space is closed. -/
theorem isClosed_gaussianEntireL2 (n : ℕ) (hn : 0 < n) :
    IsClosed (gaussianEntireL2 n : Set (Lp ℂ 2 (complexGaussianMeasure n))) := by
  rw [gaussianEntireL2_eq_zeroModeClosedSpan n hn]
  exact (hermiteAntiDegreeClosedSpan n hn 0).isClosed

/-- A local pointwise estimate for the actual entire representative in
terms of its Gaussian L² norm; the explicit tensor majorant is finite. -/
theorem gaussianEntireRepresentative_local_bound {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (f : Configuration n → ℂ)
    (hf : IsGaussianEntireRepresentative u f) {R : ℝ} (hR : 0 ≤ R)
    (z : Configuration n) (hz : ∀ j, ‖z j‖ ≤ R) :
    ‖f z‖ ≤ ‖u‖ * ∑' p : Fin n → ℕ,
      ∏ j, oneDimNormalization n (p j) * R ^ p j := by
  let c := fun p : Fin n → ℕ => gaussianHermiteCoefficient hn u (p, 0)
  let B := fun p : Fin n → ℕ => ∏ j, oneDimNormalization n (p j) * R ^ p j
  have hb : Summable B := summable_tensor_holomorphicHermite_bound n n hR
  have hcoef : ∀ p, ‖c p‖ ≤ ‖u‖ := fun p => gaussianHermiteCoefficient_norm_le hn u (p, 0)
  have hseries := gaussianZeroMode_holomorphic_series_ae hn u
  rw [gaussianEntireRepresentative_zeroMode_eq hn u f hf] at hseries
  have heq : (fun w => ∑' p, c p * multivariateNormalized n hn p 0 w) = f :=
    continuous_eq_of_ae_eq_complexGaussian hn
      (differentiable_holomorphicHermite_series n hn c hcoef).continuous hf.1.continuous
      (hseries.trans hf.2.symm)
  rw [← heq]
  have hs := summable_holomorphicHermite_series n hn c hcoef z
  have hnorm := hs.norm
  calc
    _ ≤ ∑' p, ‖c p * multivariateNormalized n hn p 0 z‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' p, ‖u‖ * B p := by
      apply hnorm.tsum_le_tsum _ (hb.mul_left ‖u‖)
      intro p
      rw [norm_mul]
      exact mul_le_mul (hcoef p)
        (norm_holomorphicHermite_le_tensor_bound n hn p hR hz) (norm_nonneg _) (norm_nonneg u)
    _ = _ := hb.tsum_mul_left ‖u‖

/-- L² convergence of entire functions implies uniform convergence on
all bounded configuration sets, with actual entire representatives. -/
theorem gaussianEntireRepresentative_tendstoUniformlyOn {n : ℕ} (hn : 0 < n)
    {ι : Type*} {l : Filter ι} (U : ι → Lp ℂ 2 (complexGaussianMeasure n))
    (u : Lp ℂ 2 (complexGaussianMeasure n))
    (F : ι → Configuration n → ℂ) (f : Configuration n → ℂ)
    (hF : ∀ i, IsGaussianEntireRepresentative (U i) (F i))
    (hf : IsGaussianEntireRepresentative u f) (ht : Tendsto U l (𝓝 u))
    {R : ℝ} (hR : 0 ≤ R) :
    TendstoUniformlyOn F f l {z | ∀ j, ‖z j‖ ≤ R} := by
  let K : ℝ := ∑' p : Fin n → ℕ, ∏ j, oneDimNormalization n (p j) * R ^ p j
  have hlim : Tendsto (fun i => ‖u - U i‖ * K) l (𝓝 0) := by
    simpa using (((show Tendsto (fun _ : ι => u) l (𝓝 u) from tendsto_const_nhds).sub
        ht).norm.mul_const K)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with i hi z hz
  have hdiff : IsGaussianEntireRepresentative (u - U i) (fun w => f w - F i w) := by
    refine ⟨hf.1.sub (hF i).1, ?_⟩
    filter_upwards [hf.2, (hF i).2, Lp.coeFn_sub u (U i)] with w hu hU hs
    simp only [Pi.sub_apply] at hs
    rw [hu, hU, hs]
  have hb := gaussianEntireRepresentative_local_bound hn (u - U i) _ hdiff hR z hz
  rw [dist_eq_norm]
  exact hb.trans_lt hi

/-- The local uniform convergence asserted in Remark 2.5 holds for any
Gaussian L²-convergent family of actual entire representatives. -/
theorem gaussianEntireRepresentative_tendstoLocallyUniformly {n : ℕ} (hn : 0 < n)
    {ι : Type*} {l : Filter ι} (U : ι → Lp ℂ 2 (complexGaussianMeasure n))
    (u : Lp ℂ 2 (complexGaussianMeasure n))
    (F : ι → Configuration n → ℂ) (f : Configuration n → ℂ)
    (hF : ∀ i, IsGaussianEntireRepresentative (U i) (F i))
    (hf : IsGaussianEntireRepresentative u f) (ht : Tendsto U l (𝓝 u)) :
    TendstoLocallyUniformly F f l := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  let R := ‖x‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hconv := gaussianEntireRepresentative_tendstoUniformlyOn hn U u F f hF hf ht hR
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x (by norm_num), ?_⟩
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hconv) ε hε] with i hi y hy
  apply hi y
  intro j
  have hdist : ‖y - x‖ < 1 := by simpa [dist_eq_norm] using hy
  exact (norm_le_pi_norm y j).trans (by
    dsimp [R]
    have hn := norm_sub_norm_le y x
    linarith)

/-- The genuine entire Gaussian L² subspace, with its proved closedness. -/
def gaussianEntireClosedSpace (n : ℕ) (hn : 0 < n) :
    ClosedSubmodule ℂ (Lp ℂ 2 (complexGaussianMeasure n)) where
  toSubmodule := gaussianEntireL2 n
  isClosed' := isClosed_gaussianEntireL2 n hn

theorem gaussianEntireClosedSpace_eq_hermite (n : ℕ) (hn : 0 < n) :
    gaussianEntireClosedSpace n hn = hermiteAntiDegreeClosedSpan n hn 0 := by
  ext u
  change u ∈ gaussianEntireL2 n ↔ u ∈ hermiteAntiDegreeClosedSpan n hn 0
  rw [gaussianEntireL2_eq_zeroModeClosedSpan n hn]
  rfl

theorem gaussianEntireProjection_eq_zeroMode {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    (gaussianEntireClosedSpace n hn).starProjection u = gaussianHermiteMode hn 0 u := by
  rw [gaussianEntireClosedSpace_eq_hermite, gaussianHermiteMode_eq_antiDegreeProjection]
  rfl

/-- Lemma 2.2 / Remark 2.3 with projection onto the actual entire function
space, on the full ordinary Schwartz distributional domain. -/
theorem gaussianSchwartzDbar_entire_gap {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hu : ∀ j, IsGaussianSchwartzDbar n u (D j) j) :
    ‖u - (gaussianEntireClosedSpace n hn).starProjection u‖ ^ 2 ≤
      (1 / (n : ℝ)) * ∑ j, ‖D j‖ ^ 2 := by
  let P := (gaussianEntireClosedSpace n hn).starProjection
  have hnorm := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (u - P u) (P u) (Submodule.starProjection_inner_eq_zero u (P u)
      (Submodule.starProjection_apply_mem _ u))
  rw [sub_add_cancel] at hnorm
  have hp : P u = gaussianHermiteMode hn 0 u := gaussianEntireProjection_eq_zeroMode hn u
  have hg := gaussianSchwartzDbar_gap hn u D hu
  simp only [pow_two] at hg ⊢
  rw [hp] at hnorm
  rw [gaussianEntireProjection_eq_zeroMode hn u]
  nlinarith

end
end GinibrePoincare

