/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCScaleIntegration

/-!
# Integral flatness under parabolic scaling

The all-orders integral condition in `lem:uc-gaussian` is invariant under a
fixed positive parabolic dilation.
-/

public section


open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Parabolic dilation preserves integral vanishing of every order at the
initial point (`eq:uc-integral-vanishing`). -/
theorem uc_integral_flatness_scaled
    (x₀ : Vec3) (R T scale ρ : ℝ) (hR : 0 < R) (hT : 0 < T)
    (hscale : 0 < scale) (w : ParabolicPoint → Vec3)
    (hwloc : LocallyIntegrableOn w
      (spaceTimeSet (vec3Ball x₀ R) (Ioo 0 T)) volume)
    (hL2 : (∫⁻ z in spaceTimeSet (vec3Ball x₀ R) (Ioo 0 T),
      ‖w z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hflat : UCIntegralFlatness x₀ R T w) :
    UCIntegralFlatness 0 ρ 2 (ucScaledField x₀ scale w) := by
  intro m
  obtain ⟨C, r₀, hC, hr₀, hbound⟩ := hflat m
  let δ := min (r₀ / scale) (min (R / scale) (Real.sqrt T / scale))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (div_pos hr₀ hscale)
      (lt_min (div_pos hR hscale) (div_pos (Real.sqrt_pos.2 hT) hscale))
  refine ⟨scale⁻¹ ^ 5 * C * scale ^ m, δ, ?_, hδ, ?_⟩
  · positivity
  intro r hr hrsmall
  have hrδ : r < δ := (lt_min_iff.mp (lt_min_iff.mp hrsmall).2).2
  have hr₀' : scale * r < r₀ := by
    have h := (lt_min_iff.mp hrδ).1
    simpa only [mul_comm] using (lt_div_iff₀ hscale).mp h
  have hrR : scale * r < R := by
    have h := (lt_min_iff.mp (lt_min_iff.mp hrδ).2).1
    simpa only [mul_comm] using (lt_div_iff₀ hscale).mp h
  have hrT : scale * r < Real.sqrt T := by
    have h := (lt_min_iff.mp (lt_min_iff.mp hrδ).2).2
    simpa only [mul_comm] using (lt_div_iff₀ hscale).mp h
  have hsr : 0 < scale * r := mul_pos hscale hr
  have hsource :
      (∫ z in spaceTimeSet (vec3Ball x₀ (scale * r))
        (Ioo 0 ((scale * r) ^ 2)), vec3EuclideanNorm (w z) ^ 2) ≤
        C * (scale * r) ^ m :=
    hbound (scale * r) hsr (lt_min hrR (lt_min hrT hr₀'))
  let S := spaceTimeSet (vec3Ball x₀ R) (Ioo 0 T)
  let Q := spaceTimeSet (vec3Ball x₀ (scale * r))
    (Ioo 0 ((scale * r) ^ 2))
  have hrTpow : (scale * r) ^ 2 < T := by
    have hsqrt : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hT.le
    nlinarith only [hrT, hsr, Real.sqrt_nonneg T, hsqrt]
  have hQsubS : Q ⊆ S := by
    intro z hz
    exact ⟨(mem_vec3Ball).2 ((mem_vec3Ball).1 hz.1 |>.trans hrR),
      ⟨hz.2.1, hz.2.2.trans hrTpow⟩⟩
  have hwQ : IntegrableOn
      (fun z : ParabolicPoint => vec3EuclideanNorm (w z) ^ 2) Q volume :=
    uc_squared_norm_integrable_on_subset S Q w hwloc hL2 hQsubS
  have hpoint : scalingParabolic scale (x₀, 0) = ucScaledPoint x₀ scale := by
    funext z
    simp only [scalingParabolic, parabolicTranslate, parabolicScale,
      ucScaledPoint, zero_add]
    rfl
  have hchange :
      (∫ z in spaceTimeSet (vec3Ball 0 r) (Ioo 0 (r ^ 2)),
        vec3EuclideanNorm ((ucScaledField x₀ scale w) z) ^ 2) =
      scale⁻¹ ^ 5 * ∫ z in Q, vec3EuclideanNorm (w z) ^ 2 := by
    have hΩ : MeasurableSet (vec3Ball x₀ (scale * r)) :=
      vec3Ball_measurable _ _
    have hI : MeasurableSet (Ioo 0 ((scale * r) ^ 2)) := measurableSet_Ioo
    have hc := CKN.integral_comp_scaling_test scale hscale (x₀, 0)
      (Ω := vec3Ball x₀ (scale * r)) (I := Ioo 0 ((scale * r) ^ 2))
      (F := fun z : ParabolicPoint => vec3EuclideanNorm (w z) ^ 2)
      hΩ hI hwQ.aestronglyMeasurable
    have hpre := uc_scaled_box_preimage x₀ scale r (r ^ 2) hscale
    have htimeeq : scale ^ 2 * r ^ 2 = (scale * r) ^ 2 := by ring
    rw [htimeeq] at hpre
    rw [hpre, hpoint] at hc
    rw [ENNReal.toReal_ofReal (by positivity)] at hc
    simpa only [Q, ucScaledField, smul_eq_mul] using hc
  calc
    (∫ z in spaceTimeSet (vec3Ball 0 r) (Ioo 0 (r ^ 2)),
        vec3EuclideanNorm ((ucScaledField x₀ scale w) z) ^ 2) =
        scale⁻¹ ^ 5 * ∫ z in Q, vec3EuclideanNorm (w z) ^ 2 := hchange
    _ ≤ scale⁻¹ ^ 5 * (C * (scale * r) ^ m) :=
      mul_le_mul_of_nonneg_left hsource (by positivity)
    _ = (scale⁻¹ ^ 5 * C * scale ^ m) * r ^ m := by
      rw [mul_pow]
      ring

end ESS
