/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCGaussianEstimate

/-!
# Initial trace at the flatness center

The first pointwise vanishing order and continuity fix the trace at the
origin.
-/

public section


open Set Filter CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace ESS

/-- Pointwise first-order vanishing on the open cylinder forces a zero
continuous initial trace at its center. -/
theorem uc_origin_trace_zero
    (R T : ℝ) (hR : 0 < R) (hT : 0 < T)
    (w : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w (spaceTimeSet (vec3Ball 0 R) (Ico 0 T)))
    (hvanish : ∀ k : ℕ, ∃ C : ℝ,
      ∀ z ∈ spaceTimeSet (vec3Ball 0 R) (Ioo 0 T),
        vec3EuclideanNorm (w z) ≤
          C * (vec3EuclideanNorm z.1 + Real.sqrt z.2) ^ k) :
    w (0, 0) = 0 := by
  let S : Set ParabolicPoint := spaceTimeSet (vec3Ball 0 R) (Ico 0 T)
  have h0 : ((0 : Vec3), (0 : ℝ)) ∈ S := by
    exact ⟨by simpa only [mem_vec3Ball, sub_zero,
      vec3EuclideanNorm_zero] using hR, ⟨le_refl 0, hT⟩⟩
  let f : ℝ → ParabolicPoint := fun t =>
    parabolicHomeomorph.symm ((0 : Vec3), t)
  have hf : Continuous f :=
    parabolicHomeomorph.symm.continuous.comp
      (continuous_const.prodMk continuous_id)
  have hpath0 : Tendsto f (𝓝[>] (0 : ℝ))
      (𝓝 ((0 : Vec3), (0 : ℝ))) := by
    exact hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hpathS : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), f t ∈ S := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds] with t ht htT
    exact ⟨by simpa only [f, parabolicHomeomorph_symm_apply, mem_vec3Ball, sub_zero,
      vec3EuclideanNorm_zero] using hR, ⟨ht.le, htT⟩⟩
  have hpath : Tendsto f (𝓝[>] (0 : ℝ))
      (𝓝[S] ((0 : Vec3), (0 : ℝ))) :=
    tendsto_nhdsWithin_iff.mpr ⟨hpath0, hpathS⟩
  have hvalue : Tendsto (fun t : ℝ => vec3EuclideanNorm (w (f t)))
      (𝓝[>] (0 : ℝ)) (𝓝 (vec3EuclideanNorm (w (0, 0)))) :=
    (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.continuousAt.comp_continuousWithinAt
      (hcont.continuousWithinAt h0)).tendsto.comp hpath
  obtain ⟨C, hC⟩ := hvanish 1
  have hupper : Tendsto (fun t : ℝ => |C| * Real.sqrt t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert (Real.continuous_sqrt.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).const_mul |C| using 1; simp
  have hlow : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      0 ≤ vec3EuclideanNorm (w (0, t)) :=
    Filter.Eventually.of_forall (fun t => vec3EuclideanNorm_nonneg _)
  have hhigh : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      vec3EuclideanNorm (w (0, t)) ≤ |C| * Real.sqrt t := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds] with t ht htT
    have hz : ((0 : Vec3), t) ∈
        spaceTimeSet (vec3Ball 0 R) (Ioo 0 T) :=
      ⟨by simpa only [mem_vec3Ball, sub_zero,
        vec3EuclideanNorm_zero] using hR, ⟨ht, htT⟩⟩
    have h := hC ((0 : Vec3), t) hz
    simp only [vec3EuclideanNorm_zero, zero_add, pow_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self C)
      (Real.sqrt_nonneg _))
  have hzero : Tendsto (fun t : ℝ => vec3EuclideanNorm (w (0, t)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper hlow hhigh
  have hnorm : vec3EuclideanNorm (w (0, 0)) = 0 :=
    tendsto_nhds_unique hvalue hzero
  have hnorm' : vecEuclideanNorm (w (0, 0)) = 0 := by
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq,
      vecDot, pow_two] using hnorm
  exact vecEuclideanNorm_eq_zero_iff.mp hnorm'

end ESS
