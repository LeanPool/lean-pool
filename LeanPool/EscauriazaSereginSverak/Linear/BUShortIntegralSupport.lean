/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortHeatIntegral

/-!
# Restricting Carleman integrals to the cutoff support

The cutoff field and all specified weak derivative data vanish outside the
compact support of the scalar cutoff, so its Carleman integrals are
unchanged when restricted to that support.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

private theorem bu_integral_eq_on_support
    {K D : Set ParabolicPoint} (hDmeas : MeasurableSet D) (hK : K ⊆ D)
    (F : ParabolicPoint → ℝ)
    (hzero : ∀ z ∉ K, F z = 0) :
    (∫ z in D, F z ∂volume) = ∫ z in K, F z ∂volume := by
  have h := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (f := F) (μ := (volume : Measure ParabolicPoint))
    hDmeas
    hK (fun z hz => hzero z hz.2)
  exact h

/-- The mass-gradient and weak-heat Carleman integrals of a scalar cutoff
are exactly their restrictions to the scalar cutoff support. -/
theorem bu_short_cutoff_carleman_integral_eq_support
    (scale R ε a : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R) (hε : 0 < ε)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtv : ParabolicPoint → Vec3) :
    let κ := buShortFullCutoff scale R hR ε
    let K := buCutSupportSet κ
    let W := buCutField κ v
    let DW := buCutDw κ v Dv
    let D2W := buCutD2 κ v Dv D2v
    let DtW := buCutDt κ v Dtv
    (∫ z in halfSpaceDomain, buShortCarlemanWeight a z *
      (a * vec3EuclideanNorm (W z) ^ 2 / z.2 ^ 2 +
        spatialGradientSq W DW z / z.2)) =
      (∫ z in K, buShortCarlemanWeight a z *
        (a * vec3EuclideanNorm (W z) ^ 2 / z.2 ^ 2 +
          spatialGradientSq W DW z / z.2)) ∧
    (∫ z in halfSpaceDomain, buShortCarlemanWeight a z *
      (vec3EuclideanNorm (W z) ^ 2 + spatialGradientSq W DW z)) =
      (∫ z in K, buShortCarlemanWeight a z *
        (vec3EuclideanNorm (W z) ^ 2 + spatialGradientSq W DW z)) ∧
    (∫ z in halfSpaceDomain, buShortCarlemanWeight a z *
      vec3EuclideanNorm (ucWeakHeatVector D2W DtW z) ^ 2) =
      (∫ z in K, buShortCarlemanWeight a z *
        vec3EuclideanNorm (ucWeakHeatVector D2W DtW z) ^ 2) := by
  let κ := buShortFullCutoff scale R hR ε
  let K := buCutSupportSet κ
  let W := buCutField κ v
  let DW := buCutDw κ v Dv
  let D2W := buCutD2 κ v Dv D2v
  let DtW := buCutDt κ v Dtv
  have hK : K ⊆ halfSpaceDomain :=
    (bu_short_cutoff_support_geometry scale R ε hscale hscale1 hR hε).2.1
  have hDmeas : MeasurableSet halfSpaceDomain := by
    change MeasurableSet (spaceTimeSet {x : Vec3 | 1 < x 2} (Ioo 0 1))
    exact (isOpen_spaceTimeSet _ _
      (isOpen_lt continuous_const (continuous_apply 2)) isOpen_Ioo).measurableSet
  have hzero (z : ParabolicPoint) (hz : z ∉ K) :
      W z = 0 ∧ DW z = 0 ∧ D2W z = 0 ∧ DtW z = 0 :=
    buCut_data_zero_off_support κ v Dv D2v Dtv z hz
  have hheatZero (z : ParabolicPoint) (hz : z ∉ K) :
      ucWeakHeatVector D2W DtW z = 0 := by
    obtain ⟨_, _, hD2, hDt⟩ := hzero z hz
    funext i
    simp [ucWeakHeatVector, hD2, hDt]
  constructor
  · apply bu_integral_eq_on_support hDmeas hK
    intro z hz
    obtain ⟨hW, hDW, _, _⟩ := hzero z hz
    have hnorm : vec3EuclideanNorm (W z) = 0 := by
      simp only [hW, vec3EuclideanNorm_zero]
    have hgrad : spatialGradientSq W DW z = 0 := by
      rw [spatialGradientSq, hDW]
      simp
    change buShortCarlemanWeight a z *
      (a * vec3EuclideanNorm (W z) ^ 2 / z.2 ^ 2 +
        spatialGradientSq W DW z / z.2) = 0
    simp [hnorm, hgrad]
  constructor
  · apply bu_integral_eq_on_support hDmeas hK
    intro z hz
    obtain ⟨hW, hDW, _, _⟩ := hzero z hz
    have hnorm : vec3EuclideanNorm (W z) = 0 := by
      simp only [hW, vec3EuclideanNorm_zero]
    have hgrad : spatialGradientSq W DW z = 0 := by
      rw [spatialGradientSq, hDW]
      simp
    change buShortCarlemanWeight a z *
      (vec3EuclideanNorm (W z) ^ 2 + spatialGradientSq W DW z) = 0
    simp [hnorm, hgrad]
  · apply bu_integral_eq_on_support hDmeas hK
    intro z hz
    have hnorm : vec3EuclideanNorm (ucWeakHeatVector D2W DtW z) = 0 := by
      simp only [hheatZero z hz, vec3EuclideanNorm_zero]
    change buShortCarlemanWeight a z *
      vec3EuclideanNorm (ucWeakHeatVector D2W DtW z) ^ 2 = 0
    simp [hnorm]

end ESS
