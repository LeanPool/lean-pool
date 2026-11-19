/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryPositiveWeightUniform.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryPositiveWeightClosure
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Correspondence auxiliary positive weight uniform

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `positiveWeightEntire_limit`.
-/

@[expose] public section
open MeasureTheory Set Filter Metric
open scoped BigOperators ComplexConjugate Topology NNReal
namespace GinibrePoincare
noncomputable section

private theorem kernel_bound (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z, ‖configurationRadialSmoothingKernel n z‖ ≤ M := by
  have hb := (configurationRadialSmoothingKernel_compact n).bddAbove_image
    ((configurationRadialSmoothingKernel_contDiff n).continuous.norm.continuousOn)
  obtain ⟨M, hM⟩ := hb
  refine ⟨max 0 M, le_max_left _ _, fun z => ?_⟩
  by_cases hz : z ∈ tsupport (configurationRadialSmoothingKernel n)
  · exact (hM ⟨z, hz, rfl⟩).trans (le_max_right _ _)
  · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
    exact le_max_left _ _

private theorem kernel_support_ball (n : ℕ) :
    tsupport (configurationRadialSmoothingKernel n) ⊆ closedBall (0 : Configuration n) 2 := by
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  apply pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr
  intro i
  have hzi : planarRadialSmoothingKernel (z i) ≠ 0 := by
    intro hi
    exact hz (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  have hbase : planarRadialSmoothingBase (z i) ≠ 0 := by
    intro h
    exact hzi (by simp [planarRadialSmoothingKernel, h])
  have hpos : 0 < 2-Complex.normSq (z i) := by
    by_contra h
    exact hbase (Real.smoothTransition.zero_of_nonpos (le_of_not_gt h))
  rw [Complex.normSq_eq_norm_sq] at hpos
  nlinarith [norm_nonneg (z i)]

/-- Arbitrary positive-local weighted L² controls entire representatives
uniformly on each bounded set, through the actual product mean-value kernel. -/
theorem positiveWeightEntire_local_bound (n : ℕ) (w : Configuration n → ℝ)
    (hwm : Measurable w)
    (hw : ∀ K : Set (Configuration n), IsCompact K →
      ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, c ≤ w z)
    (R : ℝ) (_ : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Lp ℂ 2 (volume.withDensity (fun z => ENNReal.ofReal (w z))),
      ∀ F : Configuration n → ℂ, Differentiable ℂ F →
      F =ᵐ[volume.withDensity (fun z => ENNReal.ofReal (w z))] u →
      ∀ z, ‖z‖ ≤ R → ‖F z‖ ≤ C * ‖u‖ := by
  let K := closedBall (0 : Configuration n) (R+2)
  have hK : IsCompact K := isCompact_closedBall _ _
  let : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  obtain ⟨c, hc, hcw⟩ := hw K hK
  let T := positiveWeightLocalRestriction volume w hK.measurableSet hc hcw
  obtain ⟨M, hM, hMb⟩ := kernel_bound n
  let B : ℝ := (measureUnivNNReal (volume.restrict K) : ℝ) ^ ((2 : ENNReal).toReal⁻¹) * M
  refine ⟨B * ‖T‖, mul_nonneg (mul_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _) hM)
    (norm_nonneg _), fun u F hF hFu z hz => ?_⟩
  let φ : Configuration n → ℂ := fun y => (configurationRadialSmoothingKernel n (z-y) : ℂ)
  have hφ : Continuous φ := Complex.continuous_ofReal.comp
    ((configurationRadialSmoothingKernel_contDiff n).continuous.comp (continuous_const.sub
        continuous_id))
  have hm : MemLp (conj ∘ φ) 2 (volume.restrict K) :=
    MemLp.of_bound (Complex.continuous_conj.comp hφ).aestronglyMeasurable M
      (ae_of_all _ (fun y => by simpa [φ, Function.comp_def] using hMb (z-y)))
  let g := hm.toLp (conj ∘ φ)
  have hg : ‖g‖ ≤ B := by
    apply Lp.norm_le_of_ae_bound hM
      (f := g)
    filter_upwards [hm.coeFn_toLp] with y hy
    rw [hy]
    simpa [φ, Function.comp_def] using hMb (z-y)
  have hAC : volume ≪ volume.withDensity (fun y => ENNReal.ofReal (w y)) := by
    apply withDensity_absolutelyContinuous' hwm.ennreal_ofReal.aemeasurable
    apply Eventually.of_forall
    intro y
    obtain ⟨d, hd, hdw⟩ := hw {y} isCompact_singleton
    exact (ENNReal.ofReal_pos.mpr (hd.trans_le (hdw y (by simp)))).ne'
  have he : inner ℂ g (T u) = F z := by
    rw [L2.inner_def]
    have hpair : (∫ y in K, inner ℂ (g y) ((T u) y)) = ∫ y in K, φ y * F y := by
      apply integral_congr_ae
      filter_upwards [hm.coeFn_toLp, positiveWeightLocalRestriction_coe volume w
        hK.measurableSet hc hcw u, ae_restrict_of_ae (hAC.ae_le hFu)] with y hg ht hf
      rw [hg, ht,← hf]
      simp [RCLike.inner_apply, mul_comm]
    rw [hpair]
    have hs : ∀ y ∉ K, φ y * F y = 0 := by
      intro y hy
      have hnot : z-y ∉ tsupport (configurationRadialSmoothingKernel n) := by
        intro h
        have hk := kernel_support_ball n h
        have hnorm : ‖z-y‖ ≤ 2 := by simpa [Metric.mem_closedBall, dist_zero_right] using hk
        apply hy
        change dist y 0 ≤ R+2
        rw [dist_zero_right]
        have htri := norm_add_le (y-z) z
        rw [sub_add_cancel, norm_sub_rev] at htri
        linarith
      simp [φ, image_eq_zero_of_notMem_tsupport hnot]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hs]
    have hmval := configurationRadialSmoothing_mean_value n F hF z
    have hcvol := integral_sub_left_eq_self
      (fun y : Configuration n => configurationRadialSmoothingKernel n y • F (z-y)) volume z
    simpa only [φ, sub_sub_cancel, Complex.real_smul] using hcvol.trans hmval
  rw [← he]
  calc
    _ ≤ ‖g‖ * ‖T u‖ := norm_inner_le_norm _ _
    _ ≤ B * (‖T‖ * ‖u‖) := mul_le_mul hg (T.le_opNorm u) (norm_nonneg _) (by positivity)
    _ = (B * ‖T‖) * ‖u‖ := (mul_assoc _ _ _).symm

/-- The locally uniform convergence assertion of Remark 2.5 for any
measurable weight bounded below positively on compact sets. -/
theorem positiveWeightEntire_tendstoLocallyUniformly (n : ℕ) (w : Configuration n → ℝ)
    (hwm : Measurable w)
    (hw : ∀ K : Set (Configuration n), IsCompact K →
      ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, c ≤ w z)
    {ι : Type*} {l : Filter ι}
    (U : ι → Lp ℂ 2 (volume.withDensity (fun z => ENNReal.ofReal (w z))))
    (u : Lp ℂ 2 (volume.withDensity (fun z => ENNReal.ofReal (w z))))
    (F : ι → Configuration n → ℂ) (f : Configuration n → ℂ)
    (hF : ∀ i, Differentiable ℂ (F i) ∧
      F i =ᵐ[volume.withDensity (fun z => ENNReal.ofReal (w z))] U i)
    (hf : Differentiable ℂ f ∧
      f =ᵐ[volume.withDensity (fun z => ENNReal.ofReal (w z))] u)
    (ht : Tendsto U l (𝓝 u)) : TendstoLocallyUniformly F f l := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  let R := ‖x‖+1
  obtain ⟨C, hC, hbound⟩ := positiveWeightEntire_local_bound n w hwm hw R (by dsimp [R]; positivity)
  have hlim : Tendsto (fun i => C * ‖u-U i‖) l (𝓝 0) := by
    simpa using (((show Tendsto (fun _ : ι => u) l (𝓝 u) from tendsto_const_nhds).sub
        ht).norm.const_mul C)
  refine ⟨ball x 1, ball_mem_nhds x (by norm_num),?_⟩
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with i hi y hy
  have hdiff : (fun z => f z-F i z) =ᵐ[volume.withDensity (fun z => ENNReal.ofReal (w z))]
      ((u-U i : Lp ℂ 2 (volume.withDensity (fun z => ENNReal.ofReal (w z)))) : Configuration n → ℂ)
          := by
    filter_upwards [hf.2, (hF i).2, Lp.coeFn_sub u (U i)] with z hu hU hs
    simp only [Pi.sub_apply] at hs
    rw [hu, hU, hs]
  have hyR : ‖y‖ ≤ R := by
    have hdist : ‖y-x‖ < 1 := by simpa [dist_eq_norm] using hy
    dsimp [R]
    have hn := norm_sub_norm_le y x
    linarith
  rw [dist_eq_norm]
  exact (hbound (u-U i) _ (hf.1.sub (hF i).1) hdiff y hyR).trans_lt hi

/-- Weighted L² convergence of entire representatives produces an actual
entire limit and convergence locally uniformly to that same representative. -/
theorem positiveWeightEntire_limit (n : ℕ) (w : Configuration n → ℝ)
    (hwm : Measurable w)
    (hw : ∀ K : Set (Configuration n), IsCompact K →
      ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, c ≤ w z)
    {ι : Type*} {l : Filter ι} [NeBot l]
    (U : ι → Lp ℂ 2 (volume.withDensity (fun z => ENNReal.ofReal (w z))))
    (u : Lp ℂ 2 (volume.withDensity (fun z => ENNReal.ofReal (w z))))
    (F : ι → Configuration n → ℂ)
    (hF : ∀ i, Differentiable ℂ (F i) ∧
      F i =ᵐ[volume.withDensity (fun z => ENNReal.ofReal (w z))] U i)
    (ht : Tendsto U l (𝓝 u)) :
    ∃ f : Configuration n → ℂ, Differentiable ℂ f ∧
      f =ᵐ[volume.withDensity (fun z => ENNReal.ofReal (w z))] u ∧
      TendstoLocallyUniformly F f l := by
  have hu : u ∈ positiveLocalWeightedEntireL2 n w :=
    (isClosed_positiveLocalWeightedEntireL2 n w hwm hw).mem_of_tendsto ht
      (Eventually.of_forall (fun i => ⟨F i, (hF i).1, (hF i).2⟩))
  obtain ⟨f, hf, hfu⟩ := hu
  exact ⟨f, hf, hfu, positiveWeightEntire_tendstoLocallyUniformly n w hwm hw U u F f hF ⟨hf, hfu⟩
      ht⟩

end
end GinibrePoincare
