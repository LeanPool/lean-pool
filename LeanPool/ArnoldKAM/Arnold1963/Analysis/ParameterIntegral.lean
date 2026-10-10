/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Analysis.AnalyticLift
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Analyticity of integrals over compact parameter sets, obtained by lifting local power series
and passing through a bounded integral linear map.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
namespace KamProject.Arnold1963

variable {X E F : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  {μ : Measure X} [IsFiniteMeasure μ] {f : E × F → ℂ} {g : X → F} {p : E}

private theorem analytic_integral_local (hg : Continuous g) {x : X}
    (hf : AnalyticAt ℂ f (p, g x)) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ s ⊆ U, MeasurableSet s →
      AnalyticAt ℂ (fun a => ∫ t in s, f (a, g t) ∂μ) p ∧
        ∀ᶠ a in 𝓝 p, IntegrableOn (fun t => f (a, g t)) s μ := by
  obtain ⟨P, r, hP⟩ := hf
  obtain ⟨R, hR, hRr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hP.r_pos
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  let U := {t : X | ‖g t - g x‖ < (R : ℝ) / 4}
  refine ⟨U, isOpen_lt (hg.sub continuous_const).norm continuous_const, ?_, ?_⟩
  · simp [U, hR0]
  intro s hs hsm
  let b : s →ᵇ (E × F) := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => (0, g t - g x))
    (continuous_const.prodMk ((hg.comp continuous_subtype_val).sub continuous_const))
    ((R : ℝ) / 4) (fun t => by simpa using (hs t.property).le)
  have hb : ‖b‖ ≤ (R : ℝ) / 4 :=
    (BoundedContinuousFunction.norm_le (by positivity)).mpr (fun t => by
      simpa [b] using (hs t.property).le)
  let L : E →L[ℂ] (s →ᵇ (E × F)) :=
    boundedConstCLM.comp (ContinuousLinearMap.inl ℂ E F)
  let v (a : E) : s →ᵇ (E × F) := L (a - p) + b
  have hv_apply (a : E) (t : s) : v a t = (a - p, g t - g x) := by
    simp [v, L, b, boundedConstCLM, Prod.add_def]
  have hvp : v p = b := by simp [v]
  have hv (a : E) (ha : a ∈ Metric.ball p ((R : ℝ) / 4)) :
      v a ∈ Metric.eball 0 P.radius := by
    have hn : ‖v a‖ < R := calc
      ‖v a‖ ≤ ‖L (a - p)‖ + ‖b‖ := norm_add_le _ _
      _ ≤ ‖a - p‖ + (R : ℝ) / 4 := add_le_add (by
        simpa [L, boundedConstCLM] using
          BoundedContinuousFunction.norm_const_le (α := s) (a - p, (0 : F))) hb
      _ < R := by rw [Metric.mem_ball, dist_eq_norm] at ha; linarith
    have he : ENNReal.ofReal ‖v a‖ < (R : ℝ≥0∞) := by
      simpa using (ENNReal.ofReal_lt_ofReal_iff hR0).mpr hn
    simpa [Metric.mem_eball, edist_dist, dist_zero_right] using he.trans (hRr.trans_le hP.r_le)
  have hvb : b ∈ Metric.eball 0 (boundedSeriesLift (X := s) P).radius := by
    rw [← hvp]
    exact (hv p (Metric.mem_ball_self (by positivity))).trans_le (radius_boundedSeriesLift_le P)
  let I := boundedIntegralCLM (μ.comap (Subtype.val : s → X))
  have hsA : AnalyticAt ℂ (fun a : E => a - p) p := by
    convert (analyticAt_id.sub (analyticAt_const (v := p) (x := p))) using 1; rfl
  have hvA : AnalyticAt ℂ v p :=
    ((L.analyticAt (p - p)).comp (f := fun a => a - p) hsA).add analyticAt_const
  have hA : AnalyticAt ℂ (fun a => I ((boundedSeriesLift P).sum (v a))) p := by
    have h := (boundedSeriesLift (X := s) P).analyticOnNhd b hvb
    rw [← hvp] at h
    exact (I.analyticAt _).comp (f := fun a => (boundedSeriesLift P).sum (v a))
      (h.comp (f := v) hvA)
  have he (a : E) (ha : a ∈ Metric.ball p ((R : ℝ) / 4)) (t : s) :
      (boundedSeriesLift P).sum (v a) t = f (a, g t) := by
    rw [boundedSeriesLift_sum_apply P (hv a ha)]
    have hpt : v a t ∈ Metric.eball 0 r := by
      have hn : ‖v a t‖ < R := by
        rw [hv_apply]
        rw [Prod.norm_def, max_lt_iff]
        constructor
        · have := Metric.mem_ball.mp ha; rw [dist_eq_norm] at this; linarith
        · have := hs t.property; dsimp [U] at this; linarith
      have he : ENNReal.ofReal ‖v a t‖ < (R : ℝ≥0∞) := by
        simpa using (ENNReal.ofReal_lt_ofReal_iff hR0).mpr hn
      simpa [Metric.mem_eball, edist_dist, dist_zero_right] using he.trans hRr
    have hh := (hP.hasSum hpt).tsum_eq
    simpa [FormalMultilinearSeries.sum, v, L, b, boundedConstCLM,
      Prod.add_def] using hh
  have hloc : ∀ᶠ a in 𝓝 p,
      (I ((boundedSeriesLift P).sum (v a)) = ∫ t in s, f (a, g t) ∂μ) ∧
        IntegrableOn (fun t => f (a, g t)) s μ := by
    filter_upwards [Metric.ball_mem_nhds p (by positivity : (0 : ℝ) < (R : ℝ) / 4)] with a ha
    constructor
    · change (∫ t : s, (boundedSeriesLift P).sum (v a) t ∂μ.comap Subtype.val) = _
      simp_rw [he a ha]
      exact integral_subtype_comap (μ := μ) hsm (fun t => f (a, g t))
    · rw [integrableOn_iff_comap_subtypeVal hsm]
      have hi := ((boundedSeriesLift P).sum (v a)).integrable (μ.comap Subtype.val)
      exact hi.congr (Filter.Eventually.of_forall (fun t => he a ha t))
  exact ⟨hA.congr (hloc.mono fun _ h => h.1), hloc.mono fun _ h => h.2⟩

theorem analyticAt_integral_compact (hg : Continuous g) {K : Set X} (hK : IsCompact K)
    (hKm : MeasurableSet K) (hf : ∀ t ∈ K, AnalyticAt ℂ f (p, g t)) :
    AnalyticAt ℂ (fun a => ∫ t in K, f (a, g t) ∂μ) p := by
  let Good (s : Set X) := ∃ U : Set X, IsOpen U ∧ s ⊆ U ∧
    ∀ t ⊆ U, MeasurableSet t →
      AnalyticAt ℂ (fun a => ∫ x in t, f (a, g x) ∂μ) p ∧
        ∀ᶠ a in 𝓝 p, IntegrableOn (fun x => f (a, g x)) t μ
  have hgood : Good K := by
    refine hK.induction_on (p := Good) ?_ ?_ ?_ ?_
    · refine ⟨∅, isOpen_empty, Subset.rfl, ?_⟩
      intro t ht htm
      have he : t = ∅ := subset_empty_iff.mp ht
      subst t
      simp only [setIntegral_empty]
      exact ⟨analyticAt_const, Filter.Eventually.of_forall (fun _ => integrableOn_empty)⟩
    · rintro s t hst ⟨U, ho, ht, hu⟩
      exact ⟨U, ho, hst.trans ht, hu⟩
    · rintro s t ⟨U, hU, hs, hu⟩ ⟨V, hV, ht, hv⟩
      refine ⟨U ∪ V, hU.union hV, union_subset_union hs ht, ?_⟩
      intro A hA hm
      obtain ⟨ha, hia⟩ := hu (A ∩ U) inter_subset_right (hm.inter hU.measurableSet)
      obtain ⟨hb, hib⟩ := hv (A \ U) (by grind) (hm.diff hU.measurableSet)
      have hi : ∀ᶠ a in 𝓝 p, IntegrableOn (fun x => f (a, g x)) A μ := by
        filter_upwards [hia, hib] with a ha hb
        simpa only [inter_union_sdiff] using ha.union hb
      refine ⟨(ha.add hb).congr ?_, hi⟩
      filter_upwards [hi] with a ha
      exact integral_inter_add_sdiff hU.measurableSet ha
    · intro x hx
      obtain ⟨U, ho, hxU, hu⟩ := analytic_integral_local (μ := μ) hg (hf x hx)
      exact ⟨U, mem_nhdsWithin_of_mem_nhds (ho.mem_nhds hxU), U, ho, Subset.rfl, hu⟩
  obtain ⟨U, _, hKU, hU⟩ := hgood
  exact (hU K hKU hKm).1

end KamProject.Arnold1963
