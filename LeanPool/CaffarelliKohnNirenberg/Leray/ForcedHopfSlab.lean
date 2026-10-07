/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropMomentum
public import LeanPool.CaffarelliKohnNirenberg.Foundation.WeakDerivOneDim
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure

/-!
# Space-time integrals over growing time slabs

The weak-continuity argument for the forced Leray--Hopf limit in
`thm:leray-forced` writes the change of a spatial pairing as a space-time
integral over `K × (0,t)`. For an integrable density on `K × (0,T)` this
integral is the primitive of an integrable function of time, hence continuous
in `t ∈ [0,T]`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The CKN slab measure is the product of the restricted spatial and time
measures. -/
theorem forcedHopf_slab_measure_eq_prod (K : Set Vec3) (I : Set ℝ) :
    ((volume : Measure ParabolicPoint).restrict (spaceTimeSet K I) :
        Measure (Vec3 × ℝ)) =
      (volume.restrict K).prod (volume.restrict I) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
  rfl

/-- An integral over the growing slab `K × (0,t)` is the primitive of the
integrated spatial density. -/
theorem forcedHopf_setIntegral_slab_eq_intervalIntegral
    (K : Set Vec3) (T : ℝ) (G : ParabolicPoint → ℝ)
    (hG : Integrable G (volume.restrict (spaceTimeSet K (Ioo 0 T)))) :
    ∀ t ∈ Icc 0 T,
      ∫ z in spaceTimeSet K (Ioo 0 t), G z =
        ∫ τ in (0 : ℝ)..t, (Ioo 0 T).indicator
          (fun τ => ∫ x in K, G (x, τ)) τ := by
  intro t ht
  have hGt : Integrable G (volume.restrict (spaceTimeSet K (Ioo 0 t))) :=
    hG.mono_measure (Measure.restrict_mono_set volume
      (Set.prod_mono subset_rfl (Ioo_subset_Ioo_right ht.2)))
  have hGt' : Integrable (fun q : Vec3 × ℝ => G q)
      ((volume.restrict K).prod (volume.restrict (Ioo 0 t))) := by
    rw [← forcedHopf_slab_measure_eq_prod]
    exact hGt
  have hprod : ∫ z in spaceTimeSet K (Ioo 0 t), G z =
      ∫ τ in Ioo 0 t, ∫ x in K, G (x, τ) := by
    change ∫ q, G q ∂((volume : Measure ParabolicPoint).restrict
      (spaceTimeSet K (Ioo 0 t)) : Measure (Vec3 × ℝ)) = _
    rw [forcedHopf_slab_measure_eq_prod]
    exact integral_prod_symm _ hGt'
  rw [hprod, intervalIntegral.integral_of_le ht.1, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo (fun τ hτ => ?_)
  exact (indicator_of_mem (show τ ∈ Ioo 0 T from ⟨hτ.1, hτ.2.trans_le ht.2⟩)
    (fun τ => ∫ x in K, G (x, τ))).symm

/-- The integrated spatial density of an integrable slab function is
integrable in time. -/
theorem forcedHopf_integrable_timeDensity
    (K : Set Vec3) (T : ℝ) (G : ParabolicPoint → ℝ)
    (hG : Integrable G (volume.restrict (spaceTimeSet K (Ioo 0 T)))) :
    Integrable ((Ioo 0 T).indicator (fun τ => ∫ x in K, G (x, τ))) := by
  have hG' : Integrable (fun q : Vec3 × ℝ => G q)
      ((volume.restrict K).prod (volume.restrict (Ioo 0 T))) := by
    rw [← forcedHopf_slab_measure_eq_prod]
    exact hG
  exact (integrable_indicator_iff measurableSet_Ioo).mpr hG'.integral_prod_right

/-- An integral over the growing slab `K × (0,t)` is continuous in
`t ∈ [0,T]`. -/
theorem forcedHopf_continuousOn_setIntegral_slab
    (K : Set Vec3) (T : ℝ) (G : ParabolicPoint → ℝ)
    (hG : Integrable G (volume.restrict (spaceTimeSet K (Ioo 0 T)))) :
    ContinuousOn (fun t => ∫ z in spaceTimeSet K (Ioo 0 t), G z) (Icc 0 T) :=
  ((forcedHopf_integrable_timeDensity K T G hG).continuous_primitive 0).continuousOn.congr
    (forcedHopf_setIntegral_slab_eq_intervalIntegral K T G hG)

end CKN.Leray

end
