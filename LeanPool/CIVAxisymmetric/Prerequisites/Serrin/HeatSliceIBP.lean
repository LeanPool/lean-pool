/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.HeatCommutatorIntegral
public import LeanPool.CIVAxisymmetric.Reduction.ClassicalIBPIntegrability
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Slice-wise integration by parts before the time `s`

On every time slice `τ < s` the backward heat kernel is smooth, so a spatial derivative can be
moved across the integral slice by slice and then integrated in time. This gives the three
integrations by parts in the cut-off heat representation of the interior estimates in the proof
of `lem:aniso:annulus`.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN CKN.Foundation.Heat

noncomputable section
namespace CIV



/-- The half-space `{τ < s}` as a product set, and Lebesgue measure on it as a product measure. -/
theorem restrict_halfSpace_eq_prod (s : ℝ) :
    (volume : Measure (Vec3 × ℝ)).restrict {z : Vec3 × ℝ | z.2 < s} =
      (volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Iio s)) := by
  have hset : {z : Vec3 × ℝ | z.2 < s} = univ ×ˢ Iio s := by
    ext z; simp
  rw [hset, ← Measure.restrict_univ (μ := (volume : Measure Vec3)), Measure.prod_restrict]
  rfl

/-- Integration by parts in a spatial direction on the half-space `{τ < s}`, performed slice by
slice: on each slice the first factor is smooth with compact support inside an open set where the
second factor is smooth. -/
theorem integral_mul_spatialPartial_eq_neg_of_slices {F G : ParabolicPoint → ℝ} {s : ℝ}
    (j : Fin 3)
    (hF : ∀ τ < s, ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => F (y, τ)))
    (hFc : ∀ τ < s, HasCompactSupport (fun y : Vec3 => F (y, τ)))
    (hG : ∀ τ < s, ∃ S : Set Vec3, IsOpen S ∧ tsupport (fun y : Vec3 => F (y, τ)) ⊆ S ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec3 => G (y, τ)) S)
    (hi1 : IntegrableOn (fun z => F z * spatialPartial G j z) {z : ParabolicPoint | z.2 < s})
    (hi2 : IntegrableOn (fun z => spatialPartial F j z * G z) {z : ParabolicPoint | z.2 < s}) :
    ∫ z in {z : ParabolicPoint | z.2 < s}, F z * spatialPartial G j z =
      -∫ z in {z : ParabolicPoint | z.2 < s}, spatialPartial F j z * G z := by
  have hμ := restrict_halfSpace_eq_prod s
  have hi1' : Integrable (fun z : Vec3 × ℝ => F z * spatialPartial G j z)
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Iio s))) := by
    rw [← hμ]; exact hi1
  have hi2' : Integrable (fun z : Vec3 × ℝ => spatialPartial F j z * G z)
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Iio s))) := by
    rw [← hμ]; exact hi2
  change ∫ z, F z * spatialPartial G j z ∂((volume : Measure (Vec3 × ℝ)).restrict
      {z : Vec3 × ℝ | z.2 < s}) = -∫ z, spatialPartial F j z * G z ∂((volume :
      Measure (Vec3 × ℝ)).restrict {z : Vec3 × ℝ | z.2 < s})
  rw [hμ, integral_prod_symm _ hi1', integral_prod_symm _ hi2', ← integral_neg]
  refine integral_congr_ae (ae_restrict_of_forall_mem measurableSet_Iio (fun τ hτ => ?_))
  obtain ⟨S, hS, hFS, hGS⟩ := hG τ hτ
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_continuousOn (μ := (volume : Measure Vec3))
    (v := (basisVec j : Vec3)) hS (hFc τ hτ) hFS hGS (hF τ hτ) (hFc τ hτ) subset_rfl
  change ∫ y, F (y, τ) * fderiv ℝ (fun y' => G (y', τ)) y (basisVec j) =
    -∫ y, fderiv ℝ (fun y' => F (y', τ)) y (basisVec j) * G (y, τ)
  have e1 : ∫ y, F (y, τ) * fderiv ℝ (fun y' => G (y', τ)) y (basisVec j) =
      ∫ y, fderiv ℝ (fun y' => G (y', τ)) y (basisVec j) * F (y, τ) := by
    congr 1; funext y; ring
  have e2 : ∫ y, fderiv ℝ (fun y' => F (y', τ)) y (basisVec j) * G (y, τ) =
      ∫ y, G (y, τ) * fderiv ℝ (fun y' => F (y', τ)) y (basisVec j) := by
    congr 1; funext y; ring
  rw [e1, e2, key, neg_neg]

/-- Integrability on the half-space of a function that vanishes off a closed window, is
continuous on the window, and is dominated there by an integrable function. -/
theorem integrableOn_of_window {f g : Vec3 × ℝ → ℝ} {W U : Set (Vec3 × ℝ)}
    (hWm : MeasurableSet W) (hUm : MeasurableSet U) (hcont : ContinuousOn f (W ∩ U))
    (hzero : ∀ z ∈ U, z ∉ W → f z = 0) (hg : IntegrableOn g U) (hg0 : ∀ z ∈ U, 0 ≤ g z)
    (hbound : ∀ z ∈ U, z ∈ W → |f z| ≤ g z) : IntegrableOn f U := by
  have hind : f =ᵐ[volume.restrict U] W.indicator f :=
    (ae_restrict_iff' hUm).mpr (Filter.Eventually.of_forall (fun z hz => by
      by_cases hzW : z ∈ W
      · rw [indicator_of_mem hzW]
      · rw [indicator_of_notMem hzW, hzero z hz hzW]))
  have hmeas : AEStronglyMeasurable f (volume.restrict U) := by
    refine AEStronglyMeasurable.congr ?_ hind.symm
    rw [aestronglyMeasurable_indicator_iff hWm, Measure.restrict_restrict hWm]
    exact hcont.aestronglyMeasurable (hWm.inter hUm)
  refine Integrable.mono' hg hmeas ((ae_restrict_iff' hUm).mpr
    (Filter.Eventually.of_forall (fun z hz => ?_)))
  rw [Real.norm_eq_abs]
  by_cases hzW : z ∈ W
  · exact hbound z hz hzW
  · rw [hzero z hz hzW, abs_zero]; exact hg0 z hz

/-- The spatial partial of a field smooth on an open set is continuous there. -/
theorem continuousOn_spatialPartial_of_isOpen {G : ParabolicPoint → ℝ} {O : Set (Vec3 × ℝ)}
    (hO : IsOpen O) (hG : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => G z) O) (j : Fin 3) :
    ContinuousOn (fun z : Vec3 × ℝ => spatialPartial G j z) O := by
  have hc : ContinuousOn (fun z : Vec3 × ℝ => fderiv ℝ (fun w : Vec3 × ℝ => G w) z
      ((basisVec j : Vec3), (0 : ℝ))) O := by
    have h := hG.continuousOn_fderiv_of_isOpen hO (by simp)
    intro z hz
    exact ContinuousWithinAt.clm_apply (h z hz) continuousWithinAt_const
  refine hc.congr (fun z hz => ?_)
  exact spatialPartial_eq_jointFDeriv ((hG.differentiableOn (by simp)).differentiableAt
    (hO.mem_nhds hz)) j

/-- The cut-off heat weight is smooth before the time `s`. -/
theorem contDiffOn_serrinHeatWeight (x : Vec3) {s ρ : ℝ} (hρ : 0 < ρ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => serrinHeatWeight x s ρ z)
      {z : Vec3 × ℝ | z.2 < s} := by
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => ((x - z.1, s - z.2) : Vec3 × ℝ)) := by
    fun_prop
  have hΓ := (heatKernel_contDiffOn_pos.of_le (by exact_mod_cast le_top)).comp hmap.contDiffOn
    (s := {z : Vec3 × ℝ | z.2 < s}) (fun z hz =>
      ⟨mem_univ _, show (0 : ℝ) < s - z.2 by linarith only [show z.2 < s from hz]⟩)
  exact hΓ.mul (contDiff_serrinCutoff x (s := s) hρ).contDiffOn

/-- On a slice before `s`, the heat weight is smooth, compactly supported, and supported in the
window slice. -/
theorem serrinHeatWeight_slice (x : Vec3) {s ρ : ℝ} (hρ : 0 < ρ) {τ : ℝ} (hτ : τ < s) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => serrinHeatWeight x s ρ (y, τ)) ∧
      tsupport (fun y : Vec3 => serrinHeatWeight x s ρ (y, τ)) ⊆
        {y : Vec3 | ((y, τ) : Vec3 × ℝ) ∈
          {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s} ∧
      HasCompactSupport (fun y : Vec3 => serrinHeatWeight x s ρ (y, τ)) := by
  have ht : 0 < s - τ := by linarith only [hτ]
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => serrinHeatWeight x s ρ (y, τ)) := by
    unfold serrinHeatWeight
    exact ((contDiff_heatKernel_space ht).comp (contDiff_const.sub contDiff_id)).mul
      ((contDiff_serrinCutoff x (s := s) hρ).comp (contDiff_id.prodMk contDiff_const))
  have hWs : IsClosed {y : Vec3 | ((y, τ) : Vec3 × ℝ) ∈
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s} := by
    have hc : Continuous (fun y : Vec3 => vec3EuclideanNorm (y - x)) := by
      unfold vec3EuclideanNorm; fun_prop
    by_cases hτm : τ ∈ Icc (s - ρ ^ 2) s
    · have e : {y : Vec3 | ((y, τ) : Vec3 × ℝ) ∈
          {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s} =
          {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} := by
        ext y; simp [hτm]
      rw [e]; exact isClosed_le hc continuous_const
    · have e : {y : Vec3 | ((y, τ) : Vec3 × ℝ) ∈
          {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s} = ∅ := by
        ext y; simp only [mem_ofPred_eq, mem_prod, mem_empty_iff_false, iff_false, not_and]
        exact fun _ h => hτm h
      rw [e]; exact isClosed_empty
  have hsupp : tsupport (fun y : Vec3 => serrinHeatWeight x s ρ (y, τ)) ⊆
      {y : Vec3 | ((y, τ) : Vec3 × ℝ) ∈
        {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s} := by
    refine closure_minimal (fun y hy => ?_) hWs
    by_contra hout
    apply hy
    have hev := serrinCutoff_eventually_eq_zero x hρ (z := ((y, τ) : Vec3 × ℝ)) hout hτ
    change heatKernel (x - y) (s - τ) * serrinCutoff x s ρ (y, τ) = 0
    rw [hev.self_of_nhds, mul_zero]
  have hsub : {y : Vec3 | ((y, τ) : Vec3 × ℝ) ∈
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s} ⊆
      closure (vec3Ball x ρ) := by
    intro y hy
    rw [closure_vec3Ball hρ]
    exact hy.1
  have hc : IsCompact (tsupport fun y : Vec3 => serrinHeatWeight x s ρ (y, τ)) :=
    (isCompact_closure_vec3Ball hρ).of_isClosed_subset (isClosed_tsupport _) (hsupp.trans hsub)
  exact ⟨hsm, hsupp, hc⟩

/-- The backward window is compact. -/
theorem isCompact_serrinWindow (x : Vec3) {s ρ : ℝ} (hρ : 0 < ρ) :
    IsCompact ({y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s) := by
  refine IsCompact.prod ?_ isCompact_Icc
  rw [← closure_vec3Ball hρ]
  exact isCompact_closure_vec3Ball hρ

/-- The translated heat kernel restricted to the strip `0 < s - τ ≤ ρ²` is integrable. -/
theorem integrable_heatKernel_translate_strip (x : Vec3) (s ρ : ℝ) :
    Integrable (fun z : Vec3 × ℝ =>
      (univ ×ˢ Ioc 0 (ρ ^ 2)).indicator (fun q : Vec3 × ℝ => heatKernelPlus q) ((x, s) - z)) := by
  have hi : Integrable ((univ ×ˢ Ioc 0 (ρ ^ 2)).indicator (fun q : Vec3 × ℝ => heatKernelPlus q)) :=
    (integrable_indicator_iff (MeasurableSet.univ.prod measurableSet_Ioc)).mpr
      heatKernelPlus_integrableOn_time
  exact ((measurePreserving_sub_left_prod (x, s)).integrable_comp_emb
    (measurableEmbedding_subLeft (x, s))).mpr hi

/-- The main-term integration by parts: before `s`, `∫ Ψ ∂ⱼY = -∫ ∂ⱼΨ Y` for `Y` smooth on an
open set containing the window. -/
theorem integral_serrinHeatWeight_mul_spatialPartial {Y : ParabolicPoint → ℝ}
    {O : Set ParabolicPoint} {x : Vec3} {s ρ : ℝ} (hO : IsOpen (X := Vec3 × ℝ) O) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hwin : {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s ⊆ O)
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => Y z) O) (j : Fin 3) :
    ∫ z in {z : ParabolicPoint | z.2 < s}, serrinHeatWeight x s ρ z * spatialPartial Y j z =
      -∫ z in {z : ParabolicPoint | z.2 < s},
        spatialPartial (serrinHeatWeight x s ρ) j z * Y z := by
  set W : Set (Vec3 × ℝ) := {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s
    with hW
  set U : Set (Vec3 × ℝ) := {z | z.2 < s} with hU
  have hUm : MeasurableSet U := measurableSet_lt measurable_snd measurable_const
  have hWc : IsCompact W := isCompact_serrinWindow x hρ
  have hWm : MeasurableSet W := hWc.isClosed.measurableSet
  have hYc : ContinuousOn (fun z : Vec3 × ℝ => Y z) O := hY.continuousOn
  have hdYc := continuousOn_spatialPartial_of_isOpen hO hY j
  obtain ⟨CY, hCY⟩ := hWc.exists_bound_of_continuousOn (hYc.mono hwin)
  obtain ⟨CdY, hCdY⟩ := hWc.exists_bound_of_continuousOn (hdYc.mono hwin)
  have hCY0 : 0 ≤ CY := (norm_nonneg _).trans (hCY ((x, s) : Vec3 × ℝ) ⟨by
    change vec3EuclideanNorm (x - x) ≤ ρ; rw [sub_self, vec3EuclideanNorm_zero]; exact hρ.le,
    by have := sq_nonneg ρ; linarith only [this], le_rfl⟩)
  have hCdY0 : 0 ≤ CdY := (norm_nonneg _).trans (hCdY ((x, s) : Vec3 × ℝ) ⟨by
    change vec3EuclideanNorm (x - x) ≤ ρ; rw [sub_self, vec3EuclideanNorm_zero]; exact hρ.le,
    by have := sq_nonneg ρ; linarith only [this], le_rfl⟩)
  have hΨc : ContinuousOn (fun z : Vec3 × ℝ => serrinHeatWeight x s ρ z) U :=
    (contDiffOn_serrinHeatWeight x (s := s) hρ).continuousOn
  have hdΨc : ContinuousOn (fun z : Vec3 × ℝ => spatialPartial (serrinHeatWeight x s ρ) j z) U := by
    have h := continuousOn_spatialPartial_serrinHeatWeight x (s := s) hρ j
    have hUeq : spaceTimeSet univ (Iio s) = U := by
      ext z; exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩
    rwa [hUeq] at h
  have hΨzero : ∀ z ∈ U, z ∉ W → serrinHeatWeight x s ρ z = 0 := by
    intro z hz hzW
    have hev := serrinCutoff_eventually_eq_zero x hρ hzW hz
    change heatKernel (x - z.1) (s - z.2) * serrinCutoff x s ρ z = 0
    rw [hev.self_of_nhds, mul_zero]
  obtain ⟨C₃, _, hC₃⟩ := serrinHeatWeight_spatialPartial_integral
  apply integral_mul_spatialPartial_eq_neg_of_slices j
  · exact fun τ hτ => (serrinHeatWeight_slice x hρ hτ).1
  · exact fun τ hτ => (serrinHeatWeight_slice x hρ hτ).2.2
  · intro τ hτ
    refine ⟨{y : Vec3 | ((y, τ) : Vec3 × ℝ) ∈ O}, hO.preimage (by fun_prop), ?_, ?_⟩
    · exact (serrinHeatWeight_slice x hρ hτ).2.1.trans (fun y hy => hwin hy)
    · exact hY.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun y hy => hy)
  · -- `Ψ ∂ⱼY` is dominated by the translated heat kernel
    refine integrableOn_of_window (g := fun z => CdY * (univ ×ˢ Ioc 0 (ρ ^ 2)).indicator
        (fun q : Vec3 × ℝ => heatKernelPlus q) ((x, s) - z)) hWm hUm
      ((hΨc.mono inter_subset_right).mul (hdYc.mono (inter_subset_left.trans hwin)))
      (fun z hz hzW => by rw [hΨzero z hz hzW, zero_mul])
      ((integrable_heatKernel_translate_strip x s ρ).const_mul CdY).integrableOn
      (fun z _ => mul_nonneg hCdY0 (indicator_nonneg (fun q _ => heatKernelPlus_nonneg q) _)) ?_
    intro z hz hzW
    have hmem : ((x, s) - z) ∈ (univ ×ˢ Ioc 0 (ρ ^ 2) : Set (Vec3 × ℝ)) :=
      ⟨mem_univ _, show 0 < s - z.2 by linarith only [show z.2 < s from hz],
        show s - z.2 ≤ ρ ^ 2 by linarith only [hzW.2.1]⟩
    rw [indicator_of_mem hmem, abs_mul]
    have hΨb : |serrinHeatWeight x s ρ z| ≤ heatKernelPlus ((x, s) - z) := by
      have hP : heatKernel (x - z.1) (s - z.2) = heatKernelPlus ((x, s) - z) :=
        (heatKernelPlus_eq_heatKernel (((x, s) - z : Vec3 × ℝ) : ParabolicPoint)).symm
      calc |serrinHeatWeight x s ρ z|
          = heatKernel (x - z.1) (s - z.2) * |serrinCutoff x s ρ z| := by
            change |heatKernel (x - z.1) (s - z.2) * serrinCutoff x s ρ z| = _
            rw [abs_mul, abs_of_nonneg (heatKernel_nonneg _ _)]
        _ ≤ heatKernel (x - z.1) (s - z.2) :=
            mul_le_of_le_one_right (heatKernel_nonneg _ _) (abs_serrinCutoff_le_one x s ρ z)
        _ = heatKernelPlus ((x, s) - z) := hP
    have hdY := hCdY z hzW
    rw [Real.norm_eq_abs] at hdY
    calc |serrinHeatWeight x s ρ z| * |spatialPartial Y j z|
        ≤ heatKernelPlus ((x, s) - z) * CdY :=
          mul_le_mul hΨb hdY (abs_nonneg _) (heatKernelPlus_nonneg _)
      _ = CdY * heatKernelPlus ((x, s) - z) := mul_comm _ _
  · -- `∂ⱼΨ Y` is dominated by `|∂ⱼΨ|`
    have hi := (hC₃ x s ρ hρ hρ1 j).1
    refine integrableOn_of_window (g := fun z => CY * |spatialPartial (serrinHeatWeight x s ρ) j z|)
      hWm hUm ((hdΨc.mono inter_subset_right).mul (hYc.mono (inter_subset_left.trans hwin)))
      (fun z hz hzW => by rw [(spatialPartial_serrinKernels_eq_zero x hρ hz hzW j).1, zero_mul])
      (hi.abs.const_mul CY) (fun z _ => mul_nonneg hCY0 (abs_nonneg _)) ?_
    intro z _ hzW
    have hYb := hCY z hzW
    rw [Real.norm_eq_abs] at hYb
    rw [abs_mul, mul_comm CY]
    exact mul_le_mul_of_nonneg_left hYb (abs_nonneg _)

/-- In the window before `s`, the products of the heat kernel (or its spatial derivative) with
the partials of the cutoff are bounded by `C ρ⁻⁵`. -/
theorem serrin_kernel_pieces_bounds : ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Vec3) (s ρ : ℝ), 0 < ρ →
    ∀ z : ParabolicPoint, z.2 < s →
    z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s → ∀ i : Fin 3,
      |heatKernel (x - z.1) (s - z.2) * timePartial (serrinCutoff x s ρ) z| ≤ C / ρ ^ 5 ∧
      |heatKernel (x - z.1) (s - z.2) * spatialSecondPartial (serrinCutoff x s ρ) i i z| ≤
        C / ρ ^ 5 ∧
      |heatKernel (x - z.1) (s - z.2) * spatialPartial (serrinCutoff x s ρ) i z| ≤ C / ρ ^ 4 ∧
      |spatialPartial (fun w : ParabolicPoint => heatKernel (x - w.1) (s - w.2)) i z *
        spatialPartial (serrinCutoff x s ρ) i z| ≤ C / ρ ^ 5 := by
  obtain ⟨Ck, hCk0, hCk⟩ := heatKernel_window_bounds
  obtain ⟨Cb, hCb0, hCb⟩ := serrinBallCutoff_dir_bounds
  obtain ⟨Ct, hCt0, hCt⟩ := serrinTimeCut_bounds
  refine ⟨Ck * (Ct + Cb), by positivity, fun x s ρ hρ z hz hw i => ?_⟩
  have ht : 0 < s - z.2 := by linarith only [hz]
  have hp := serrinCutoff_partials x (s := s) hρ i
  have e1 : timePartial (serrinCutoff x s ρ) z =
      serrinBallCutoff x ρ z.1 * deriv (serrinTimeCut s ρ) z.2 := congrFun hp.1 z
  have e2 : spatialPartial (serrinCutoff x s ρ) i z =
      fderiv ℝ (serrinBallCutoff x ρ) z.1 (basisVec i) * serrinTimeCut s ρ z.2 := congrFun hp.2.1 z
  have e3 : spatialSecondPartial (serrinCutoff x s ρ) i i z =
      fderiv ℝ (fun y => fderiv ℝ (serrinBallCutoff x ρ) y (basisVec i)) z.1 (basisVec i) *
        serrinTimeCut s ρ z.2 := congrFun hp.2.2 z
  have e4 := spatialPartial_heatKernel_translate x s hz i
  rw [e1, e2, e3, e4]
  have hYn : vec3EuclideanNorm (x - z.1) = vec3EuclideanNorm (z.1 - x) := by
    rw [← vec3EuclideanNorm_neg, neg_sub]
  have hYρ : vec3EuclideanNorm (x - z.1) ≤ ρ := by rw [hYn]; exact hw.1
  have htρ : s - z.2 ≤ ρ ^ 2 := by linarith only [hw.2.1]
  have hTb := hCt s ρ hρ z.2
  have hbB := hCb x ρ hρ z.1 i i 0
  have hΓ0 : 0 ≤ heatKernel (x - z.1) (s - z.2) := heatKernel_nonneg _ _
  have hρ5 : 0 ≤ Ck * (Ct + Cb) / ρ ^ 5 := by positivity
  have hρ4 : 0 ≤ Ck * (Ct + Cb) / ρ ^ 4 := by positivity
  by_cases hreg : ρ / 2 ≤ vec3EuclideanNorm (x - z.1) ∨ ρ ^ 2 / 2 ≤ s - z.2
  · obtain ⟨kΓ, kD, _⟩ := hCk ρ hρ (x - z.1) (s - z.2) ht htρ hYρ hreg
    have kΓ' : |heatKernel (x - z.1) (s - z.2)| ≤ Ck / ρ ^ 3 := by rw [abs_of_nonneg hΓ0]; exact kΓ
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [abs_mul, abs_mul]
      calc |heatKernel (x - z.1) (s - z.2)| * (|serrinBallCutoff x ρ z.1| *
            |deriv (serrinTimeCut s ρ) z.2|) ≤ Ck / ρ ^ 3 * (1 * (Ct / ρ ^ 2)) := by
            gcongr
            · exact hbB.1
            · exact hTb.2.1
        _ ≤ Ck * (Ct + Cb) / ρ ^ 5 := by
            rw [one_mul, div_mul_div_comm, ← pow_add]
            exact div_le_div_of_nonneg_right (by nlinarith only [hCk0, hCb0]) (by positivity)
    · rw [abs_mul, abs_mul]
      calc |heatKernel (x - z.1) (s - z.2)| *
            (|fderiv ℝ (fun y => fderiv ℝ (serrinBallCutoff x ρ) y (basisVec i)) z.1 (basisVec i)| *
            |serrinTimeCut s ρ z.2|) ≤ Ck / ρ ^ 3 * (Cb / ρ ^ 2 * 1) := by
            gcongr
            · exact hbB.2.2.1
            · exact hTb.1
        _ ≤ Ck * (Ct + Cb) / ρ ^ 5 := by
            rw [mul_one, div_mul_div_comm, ← pow_add]
            exact div_le_div_of_nonneg_right (by nlinarith only [hCk0, hCt0]) (by positivity)
    · rw [abs_mul, abs_mul]
      calc |heatKernel (x - z.1) (s - z.2)| * (|fderiv ℝ (serrinBallCutoff x ρ) z.1 (basisVec i)| *
            |serrinTimeCut s ρ z.2|) ≤ Ck / ρ ^ 3 * (Cb / ρ * 1) := by
            gcongr
            · exact hbB.2.1
            · exact hTb.1
        _ ≤ Ck * (Ct + Cb) / ρ ^ 4 := by
            rw [mul_one, div_mul_div_comm, ← pow_succ]
            exact div_le_div_of_nonneg_right (by nlinarith only [hCk0, hCt0]) (by positivity)
    · rw [abs_mul, abs_mul, abs_neg]
      calc |heatKernelSpaceDerivative (x - z.1) (s - z.2) i| *
            (|fderiv ℝ (serrinBallCutoff x ρ) z.1 (basisVec i)| * |serrinTimeCut s ρ z.2|)
          ≤ Ck / ρ ^ 4 * (Cb / ρ * 1) := by
            gcongr
            · exact kD i
            · exact hbB.2.1
            · exact hTb.1
        _ ≤ Ck * (Ct + Cb) / ρ ^ 5 := by
            rw [mul_one, div_mul_div_comm, ← pow_succ]
            exact div_le_div_of_nonneg_right (by nlinarith only [hCk0, hCt0]) (by positivity)
  · push Not at hreg
    obtain ⟨hin, htin⟩ := hreg
    have hin' : vec3EuclideanNorm (z.1 - x) < ρ / 2 := by rw [← hYn]; exact hin
    have hT' : deriv (serrinTimeCut s ρ) z.2 = 0 := hTb.2.2 (by linarith only [htin])
    have hz0 := (hCb x ρ hρ z.1 i i 0).2.2.2.2 hin'
    rw [hT', hz0.1, hz0.2.1]
    simp only [mul_zero, zero_mul, abs_zero]
    exact ⟨hρ5, hρ5, hρ4, hρ5⟩

/-- Before `s` and off the window, the commutator kernel vanishes. -/
theorem serrinCutoffKernel_eq_zero_off_window (x : Vec3) {s ρ : ℝ} (hρ : 0 < ρ) {z : Vec3 × ℝ}
    (hz : z.2 < s)
    (hout : z ∉ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s) :
    serrinCutoffKernel x s ρ z = 0 := by
  have hev := serrinCutoff_eventually_eq_zero x hρ hout hz
  have hev2 : ∀ᶠ w : Vec3 × ℝ in nhds z, ∀ᶠ w' : Vec3 × ℝ in nhds w,
      serrinCutoff x s ρ w' = 0 := hev.eventually_nhds
  have h1 : timePartial (serrinCutoff x s ρ) z = 0 := timePartial_eq_zero_of_eventually_eq_zero hev
  have h2 : ∀ i, spatialPartial (serrinCutoff x s ρ) i z = 0 := fun i =>
    spatialPartial_eq_zero_of_eventually_eq_zero hev i
  have h3 : ∀ i, spatialSecondPartial (serrinCutoff x s ρ) i i z = 0 := fun i =>
    spatialPartial_eq_zero_of_eventually_eq_zero
      (F := fun w' => spatialPartial (serrinCutoff x s ρ) i w')
      (hev2.mono (fun w hw => spatialPartial_eq_zero_of_eventually_eq_zero hw i)) i
  unfold serrinCutoffKernel
  simp only [h1, h2, h3, Finset.sum_const_zero, add_zero, mul_zero]

/-- The commutator kernel is bounded by `C ρ⁻⁵` in the window before `s`. -/
theorem abs_serrinCutoffKernel_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Vec3) (s ρ : ℝ), 0 < ρ →
    ∀ z : ParabolicPoint, z.2 < s →
    z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s →
      |serrinCutoffKernel x s ρ z| ≤ C / ρ ^ 5 := by
  obtain ⟨C, hC0, hC⟩ := serrin_kernel_pieces_bounds
  refine ⟨10 * C, by positivity, fun x s ρ hρ z hz hw => ?_⟩
  have hb := fun i => hC x s ρ hρ z hz hw i
  unfold serrinCutoffKernel
  simp only [Fin.sum_univ_three]
  have hA := (hb 0).1
  have hB0 := (hb 0).2.1
  have hB1 := (hb 1).2.1
  have hB2 := (hb 2).2.1
  have hD0 := (hb 0).2.2.2
  have hD1 := (hb 1).2.2.2
  have hD2 := (hb 2).2.2.2
  have e : heatKernel (x - z.1) (s - z.2) * (timePartial (serrinCutoff x s ρ) z +
      (spatialSecondPartial (serrinCutoff x s ρ) 0 0 z +
        spatialSecondPartial (serrinCutoff x s ρ) 1 1 z +
        spatialSecondPartial (serrinCutoff x s ρ) 2 2 z)) =
      heatKernel (x - z.1) (s - z.2) * timePartial (serrinCutoff x s ρ) z +
      heatKernel (x - z.1) (s - z.2) * spatialSecondPartial (serrinCutoff x s ρ) 0 0 z +
      heatKernel (x - z.1) (s - z.2) * spatialSecondPartial (serrinCutoff x s ρ) 1 1 z +
      heatKernel (x - z.1) (s - z.2) * spatialSecondPartial (serrinCutoff x s ρ) 2 2 z := by ring
  rw [e]
  have e10 : 10 * C / ρ ^ 5 = C / ρ ^ 5 + C / ρ ^ 5 + C / ρ ^ 5 + C / ρ ^ 5 +
      2 * (C / ρ ^ 5 + C / ρ ^ 5 + C / ρ ^ 5) := by ring
  rw [e10]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add hA hB0)) hB1)) hB2)
  · rw [abs_mul, abs_two]
    refine mul_le_mul_of_nonneg_left ?_ zero_le_two
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hD0 hD1)) hD2)

/-- The divergence-term integration by parts: before `s`,
`∫ (∑ₗ ∂ₗUₗ) K₀ = -∑ₗ ∫ Uₗ ∂ₗK₀` for `U` smooth on an open set containing the window. -/
theorem integral_divergence_mul_serrinCutoffKernel {U : Fin 3 → ParabolicPoint → ℝ}
    {O : Set ParabolicPoint} {x : Vec3} {s ρ : ℝ} (hO : IsOpen (X := Vec3 × ℝ) O) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hwin : {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s ⊆ O)
    (hU : ∀ l, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => U l z) O) :
    ∫ z in {z : ParabolicPoint | z.2 < s},
        (∑ l, spatialPartial (U l) l z) * serrinCutoffKernel x s ρ z =
      -∑ l, ∫ z in {z : ParabolicPoint | z.2 < s},
        U l z * spatialPartial (serrinCutoffKernel x s ρ) l z := by
  set W : Set (Vec3 × ℝ) := {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s
    with hW
  set V : Set (Vec3 × ℝ) := {z | z.2 < s} with hV
  have hVm : MeasurableSet V := measurableSet_lt measurable_snd measurable_const
  have hWc : IsCompact W := isCompact_serrinWindow x hρ
  have hWm : MeasurableSet W := hWc.isClosed.measurableSet
  have hWfin : volume W < ⊤ := hWc.measure_lt_top
  have hc0 : ((x, s) : Vec3 × ℝ) ∈ W := ⟨by
    change vec3EuclideanNorm (x - x) ≤ ρ; rw [sub_self, vec3EuclideanNorm_zero]; exact hρ.le,
    by have := sq_nonneg ρ; linarith only [this], le_rfl⟩
  have hVeq : spaceTimeSet univ (Iio s) = V := by
    ext z; exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩
  have hKs : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => serrinCutoffKernel x s ρ z) V := by
    rw [← hVeq]; exact contDiffOn_serrinCutoffKernel x hρ
  have hdKc : ∀ l, ContinuousOn (fun z : Vec3 × ℝ => spatialPartial (serrinCutoffKernel x s ρ) l z)
      V := by
    intro l
    have := (contDiffOn_spatialPartial_iterate_spaceTimeSet isOpen_univ isOpen_Iio
      (contDiffOn_serrinCutoffKernel x (s := s) hρ) l 1).continuousOn
    rwa [hVeq] at this
  obtain ⟨CK, hCK0, hCK⟩ := abs_serrinCutoffKernel_le
  obtain ⟨C₄, _, hC₄⟩ := serrinCutoffKernel_spatialPartial_integral
  -- one direction at a time
  have hone : ∀ l, IntegrableOn (fun z : Vec3 × ℝ =>
      spatialPartial (U l) l z * serrinCutoffKernel x s ρ z) V ∧
      ∫ z in {z : ParabolicPoint | z.2 < s}, spatialPartial (U l) l z * serrinCutoffKernel x s ρ z =
        -∫ z in {z : ParabolicPoint | z.2 < s},
          U l z * spatialPartial (serrinCutoffKernel x s ρ) l z := by
    intro l
    have hUc : ContinuousOn (fun z : Vec3 × ℝ => U l z) O := (hU l).continuousOn
    have hdUc := continuousOn_spatialPartial_of_isOpen hO (hU l) l
    obtain ⟨CU, hCU⟩ := hWc.exists_bound_of_continuousOn (hUc.mono hwin)
    obtain ⟨CdU, hCdU⟩ := hWc.exists_bound_of_continuousOn (hdUc.mono hwin)
    have hCU0 : 0 ≤ CU := (norm_nonneg _).trans (hCU _ hc0)
    have hCdU0 : 0 ≤ CdU := (norm_nonneg _).trans (hCdU _ hc0)
    have hi1 : IntegrableOn (fun z : Vec3 × ℝ =>
        serrinCutoffKernel x s ρ z * spatialPartial (U l) l z) V := by
      refine integrableOn_of_window (g := W.indicator (fun _ => CK / ρ ^ 5 * CdU)) hWm hVm
        ((hKs.continuousOn.mono inter_subset_right).mul (hdUc.mono (inter_subset_left.trans hwin)))
        (fun z hz hzW => by rw [serrinCutoffKernel_eq_zero_off_window x hρ hz hzW, zero_mul])
        ((integrable_indicator_iff hWm).mpr (integrableOn_const hWfin.ne)).integrableOn
        (fun z _ => indicator_nonneg (fun _ _ => by positivity) z) ?_
      intro z hz hzW
      rw [indicator_of_mem hzW, abs_mul]
      have h2 := hCdU z hzW
      rw [Real.norm_eq_abs] at h2
      exact mul_le_mul (hCK x s ρ hρ z hz hzW) h2 (abs_nonneg _) (by positivity)
    have hi2 : IntegrableOn (fun z : Vec3 × ℝ =>
        spatialPartial (serrinCutoffKernel x s ρ) l z * U l z) V := by
      have hi := (hC₄ x s ρ hρ hρ1 l).1
      refine integrableOn_of_window
        (g := fun z => CU * |spatialPartial (serrinCutoffKernel x s ρ) l z|) hWm hVm
        (((hdKc l).mono inter_subset_right).mul (hUc.mono (inter_subset_left.trans hwin)))
        (fun z hz hzW => by
          rw [(spatialPartial_serrinKernels_eq_zero x hρ hz hzW l).2, zero_mul])
        (hi.abs.const_mul CU) (fun z _ => mul_nonneg hCU0 (abs_nonneg _)) ?_
      intro z _ hzW
      have h2 := hCU z hzW
      rw [Real.norm_eq_abs] at h2
      rw [abs_mul, mul_comm CU]
      exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    have hslice := integral_mul_spatialPartial_eq_neg_of_slices (F := serrinCutoffKernel x s ρ)
      (G := U l) (s := s) l
      (fun τ hτ => by
        have := hKs.comp (contDiff_id.prodMk contDiff_const).contDiffOn
          (s := univ) (fun y _ => show ((y, τ) : Vec3 × ℝ).2 < s from hτ)
        exact contDiffOn_univ.mp this)
      (fun τ hτ => by
        refine HasCompactSupport.intro (K := closure (vec3Ball x ρ)) (isCompact_closure_vec3Ball hρ)
          (fun y hy => serrinCutoffKernel_eq_zero_off_window x hρ (z := ((y, τ) : Vec3 × ℝ)) hτ ?_)
        intro hmem
        apply hy
        rw [closure_vec3Ball hρ]
        exact hmem.1)
      (fun τ hτ => by
        refine ⟨{y : Vec3 | ((y, τ) : Vec3 × ℝ) ∈ O}, hO.preimage (by fun_prop), ?_,
          (hU l).comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun y hy => hy)⟩
        have hcl : IsClosed {y : Vec3 | ((y, τ) : Vec3 × ℝ) ∈ W} :=
          hWc.isClosed.preimage (by fun_prop)
        refine (closure_minimal (fun y hy => ?_) hcl).trans (fun y hy => hwin hy)
        by_contra hout
        exact hy (serrinCutoffKernel_eq_zero_off_window x hρ (z := ((y, τ) : Vec3 × ℝ)) hτ hout))
      hi1 hi2
    refine ⟨?_, ?_⟩
    · refine hi1.congr_fun (fun z _ => mul_comm _ _) hVm
    · have e1 : ∫ z in {z : ParabolicPoint | z.2 < s},
          spatialPartial (U l) l z * serrinCutoffKernel x s ρ z =
          ∫ z in {z : ParabolicPoint | z.2 < s},
            serrinCutoffKernel x s ρ z * spatialPartial (U l) l z := by
        congr 1; funext z; ring
      have e2 : ∫ z in {z : ParabolicPoint | z.2 < s},
          spatialPartial (serrinCutoffKernel x s ρ) l z * U l z =
          ∫ z in {z : ParabolicPoint | z.2 < s},
            U l z * spatialPartial (serrinCutoffKernel x s ρ) l z := by
        congr 1; funext z; ring
      rw [e1, hslice, e2]
  have esum : ∫ z in {z : ParabolicPoint | z.2 < s},
      (∑ l, spatialPartial (U l) l z) * serrinCutoffKernel x s ρ z =
      ∑ l, ∫ z in {z : ParabolicPoint | z.2 < s},
        spatialPartial (U l) l z * serrinCutoffKernel x s ρ z := by
    have hs := integral_finsetSum (μ := (volume : Measure (Vec3 × ℝ)).restrict V) Finset.univ
      (fun l _ => (hone l).1)
    exact (integral_congr_ae (Filter.Eventually.of_forall (fun z => Finset.sum_mul _ _ _))).trans hs
  rw [esum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun l _ => (hone l).2)

end CIV
