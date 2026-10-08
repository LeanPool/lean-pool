/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedMildBounds
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildHeatContinuity

/-!
# Continuity of the force Duhamel integral

The Duhamel integral `∫₀ᵗ S(t-s) ℙ f(s) ds` of `eq:reg-mild-forced` is a
continuous curve in real `L²` for a force curve that is integrable on bounded
intervals: at almost every fixed time the integrand is continuous in the
evaluation time, and it is dominated by the norm of the force.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

noncomputable section

namespace CKN.Leray

theorem norm_forcedRealInverse_le (w : ComplexVectorL2) : ‖forcedRealInverse w‖ ≤ ‖w‖ := by
  rw [forcedRealInverse_apply]
  exact (realPartVectorL2_norm_le _).trans_eq (LinearIsometryEquiv.norm_map _ _)

theorem norm_forcedForceIntegrand_le (h : ℝ → RealVectorL2) (t s : ℝ) :
    ‖forcedForceIntegrand h t s‖ ≤ ‖h s‖ := by
  rw [← forcedRealInverse_forceIntegrand]
  exact (norm_forcedRealInverse_le _).trans ((norm_forcedFourierForceIntegrand_le _ t s).trans
    (norm_forcedFourierForceCurve_le h s))

theorem stronglyMeasurable_forcedForceIntegrand {h : ℝ → RealVectorL2}
    (hh : StronglyMeasurable h) (t : ℝ) : StronglyMeasurable (forcedForceIntegrand h t) := by
  obtain ⟨Hh, hHh, hrepH⟩ := exists_jointRep_of_stronglyMeasurable (μ := volume)
    (forcedFourierForceCurve h) (stronglyMeasurable_forcedFourierForceCurve hh)
  have hF : StronglyMeasurable (forcedFourierForceIntegrand (forcedFourierForceCurve h) t) :=
    stronglyMeasurable_of_jointRep (forcedFourierForceRep Hh t)
      (measurable_forcedFourierForceRep hHh.measurable t).stronglyMeasurable _
      (forcedFourierForceRep_slice hrepH t)
  have heq : forcedForceIntegrand h t =
      fun s => forcedRealInverse (forcedFourierForceIntegrand (forcedFourierForceCurve h) t s) :=
    funext fun s => (forcedRealInverse_forceIntegrand h t s).symm
  rw [heq]
  exact forcedRealInverse.continuous.comp_stronglyMeasurable hF

theorem forcedHeatLeray_congr (w : RealVectorL2) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a = b) : forcedHeatLeray a ha w = forcedHeatLeray b hb w := by
  subst hab
  rfl

/-- At a fixed time different from the evaluation time, the force integrand
is continuous in the evaluation time. -/
theorem continuousAt_forcedForceIntegrand (h : ℝ → RealVectorL2) {s t₀ : ℝ} (hst : s ≠ t₀) :
    ContinuousAt (fun t => forcedForceIntegrand h t s) t₀ := by
  rcases lt_or_gt_of_ne hst with hlt | hgt
  · let w := lerayProjectionL2 (complexifyVectorL2 (h s))
    let φ : ℝ → {τ : ℝ // 0 ≤ τ} := fun t => ⟨max (t - s) 0, le_max_right _ _⟩
    have hφ : Continuous φ :=
      ((continuous_id.sub continuous_const).max continuous_const).subtype_mk _
    have hφ0 : φ t₀ = ⟨t₀ - s, (sub_pos.2 hlt).le⟩ :=
      Subtype.ext (max_eq_left (sub_pos.2 hlt).le)
    have hheat := heatSemigroup_continuousAt (sub_pos.2 hlt).le w
    have hG : ContinuousAt (fun t => realPartVectorL2
        (heatSemigroup (φ t).1 (φ t).2 w)) t₀ := by
      have h1 : ContinuousAt (fun τ : {τ : ℝ // 0 ≤ τ} => heatSemigroup τ.1 τ.2 w) (φ t₀) := by
        rw [hφ0]; exact hheat
      exact realPartVectorL2.continuous.continuousAt.comp (h1.comp hφ.continuousAt)
    refine hG.congr ?_
    filter_upwards [eventually_gt_nhds hlt] with t ht
    simp only [forcedForceIntegrand, dite_eq_left ht.le]
    exact forcedHeatLeray_congr (h s) _ _ (max_eq_left (sub_pos.2 ht).le)
  · refine (continuousAt_const (y := (0 : RealVectorL2))).congr ?_
    filter_upwards [eventually_lt_nhds hgt] with t ht
    simp only [forcedForceIntegrand, dite_eq_right (not_le.2 ht)]

/-- The force Duhamel integral of a force curve that is integrable on bounded
intervals is continuous. -/
theorem continuous_forcedForceDuhamel {h : ℝ → RealVectorL2} (hh : StronglyMeasurable h)
    (hH : ∀ T : ℝ, IntegrableOn (fun s => ‖h s‖) (Ioc 0 T)) :
    Continuous (forcedForceDuhamel h) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  set T : ℝ := |t₀| + 1 with hT
  have ht₀T : t₀ < T := by
    have := le_abs_self t₀
    linarith only [this, hT]
  have heq : ∀ t, t < T → forcedForceDuhamel h t = ∫ s in Ioc 0 T, forcedForceIntegrand h t s := by
    intro t htT
    unfold forcedForceDuhamel
    symm
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
      (Ioc_subset_Ioc_right htT.le) fun s hs => ?_
    have hst : ¬ s ≤ t := fun hle => hs.2 ⟨hs.1.1, hle⟩
    simp only [forcedForceIntegrand, dite_eq_right hst]
  have hcont : ContinuousAt (fun t => ∫ s in Ioc 0 T, forcedForceIntegrand h t s) t₀ := by
    refine continuousAt_of_dominated (bound := fun s => ‖h s‖)
      (Eventually.of_forall fun t =>
        (stronglyMeasurable_forcedForceIntegrand hh t).aestronglyMeasurable)
      (Eventually.of_forall fun t => Eventually.of_forall fun s =>
        norm_forcedForceIntegrand_le h t s) (hH T) ?_
    have hne : ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) T)), s ≠ t₀ := by
      refine ae_restrict_of_ae ?_
      filter_upwards [(measure_singleton t₀ : volume {t₀} = 0) |>
        measure_eq_zero_iff_ae_notMem.1] with s hs
      exact hs
    filter_upwards [hne] with s hs
    exact continuousAt_forcedForceIntegrand h hs
  refine hcont.congr ?_
  filter_upwards [eventually_lt_nhds ht₀T] with t ht
  exact (heq t ht).symm

end CKN.Leray

end
