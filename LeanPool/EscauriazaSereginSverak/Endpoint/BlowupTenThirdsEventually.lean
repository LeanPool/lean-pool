/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupTenThirdsSource
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupTenThirdsVector

public section

open CKN CKN.Foundation.Parabolic MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace ESS

/-- A common Dirichlet bound for suitable rescalings gives a common local
`L^(10/3)` bound for each velocity component up to time zero. -/
theorem blowupRescale_eventually_component_tenThirds_of_gradient_bound
    (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ)
    (hSuitable : IsSuitableWeakSolution (vec3Ball 0 (3 / 4 : ℝ))
      (Ioo (-1) 0) 3 u Du p (0 : ParabolicPoint → Vec3))
    (hu : AEStronglyMeasurable (goodPointDomain.indicator u)
      (volume : Measure ParabolicPoint))
    (M : ℝ≥0∞) (hM : M < ⊤)
    (hsource : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
      AEStronglyMeasurable
        (fun x : Vec3 => (goodPointDomain.indicator u) (x,s)) volume ∧
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm
        ((goodPointDomain.indicator u) (x,s))) 3 volume ≤ M)
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (nhds 0))
    (R a : ℝ) (hR : 0 < R) (ha : a < 0)
    (C : ℝ)
    (hgrad : ∀ᶠ k in atTop,
      IntegrableOn (fun z => spatialGradientSq
        (parabolicRescaleVelocity x₀ t₀ (r k) u)
        (parabolicRescaleGradient x₀ t₀ (r k) Du) z)
        (spaceTimeSet (CKN.euclideanBall 0 R) (Ioo a 0)) volume ∧
      2 * (∫ z in spaceTimeSet (CKN.euclideanBall 0 R) (Ioo a 0),
        spatialGradientSq
          (parabolicRescaleVelocity x₀ t₀ (r k) u)
          (parabolicRescaleGradient x₀ t₀ (r k) Du) z) ≤ C)
    (i : Fin 3) :
    let B := (blowupTenThirdsBound M (C / 2) R a) ^ ((10 / 3 : ℝ)⁻¹)
    B < ⊤ ∧ ∀ᶠ k in atTop,
      MemLp (fun z => parabolicRescaleVelocity x₀ t₀ (r k) u z i)
        (ENNReal.ofReal (10 / 3 : ℝ))
        (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ∧
      eLpNorm (fun z => parabolicRescaleVelocity x₀ t₀ (r k) u z i)
        (ENNReal.ofReal (10 / 3 : ℝ))
        (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ≤ B := by
  let K := blowupTenThirdsBound M (C / 2) R a
  let B := K ^ ((10 / 3 : ℝ)⁻¹)
  have hK : K < ⊤ := blowupTenThirdsBound_lt_top M hM (C / 2) R a
  have hB : B < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hK.ne
  refine ⟨hB, ?_⟩
  have hsuit := blowupRescale_eventually_suitableIntegrable_outer
    u Du p hSuitable x₀ t₀ r hx₀ ht₀ hr hr0 R a hR ha
  have hdom := blowupCylinder_eventually_subset_domain
    x₀ t₀ R a r hx₀ ht₀ hr hr0
  have htimeLim : Tendsto (fun k => (r k) ^ 2 * (-a)) atTop (nhds 0) := by
    simpa using (hr0.pow 2).mul_const (-a)
  have htime : ∀ᶠ k in atTop,
      Ioo a 0 ⊆ CKN.rescaledTime (r k) t₀ (Ioo (-1 : ℝ) 0) := by
    filter_upwards [htimeLim.eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 3 / 4))] with k hk
    exact blowupPastInterval_subset_source t₀ (r k) a ht₀ (hr k) hk
  filter_upwards [hsuit, hdom, htime, hgrad] with k hs hd ht hg
  have hball : CKN.euclideanBall (0 : Vec3) R = vec3Ball 0 R :=
    CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hR
  rw [hball] at hg
  have hhalf :
      (∫ z in vec3Ball (0 : Vec3) R ×ˢ Ioo a 0,
        spatialGradientSq
          (parabolicRescaleVelocity x₀ t₀ (r k) u)
          (parabolicRescaleGradient x₀ t₀ (r k) Du) z) ≤ C / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    change (∫ (z : ParabolicPoint) in vec3Ball 0 R ×ˢ Ioo a 0,
      spatialGradientSq
        (parabolicRescaleVelocity x₀ t₀ (r k) u)
        (parabolicRescaleGradient x₀ t₀ (r k) Du) z) * 2 ≤ C
    convert hg.2 using 1
    simp only [spaceTimeSet, mul_comm]
    rfl
  obtain ⟨_, hm, hpow⟩ := blowupRescale_component_tenThirds_uniform_top
    u Du p x₀ t₀ (r k) (hr k) R a hR hs hd ht
    hu M hM hsource (C / 2) hg.1 hhalf i
  refine ⟨hm, ?_⟩
  exact (ENNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 10 / 3)).2 hpow

/-- The rescaled velocity has a uniform vector `L^(10/3)` bound on each
fixed bounded open past cylinder. -/
theorem blowupRescale_eventually_tenThirds_of_gradient_bound
    (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ)
    (hSuitable : IsSuitableWeakSolution (vec3Ball 0 (3 / 4 : ℝ))
      (Ioo (-1) 0) 3 u Du p (0 : ParabolicPoint → Vec3))
    (hu : AEStronglyMeasurable (goodPointDomain.indicator u)
      (volume : Measure ParabolicPoint))
    (M : ℝ≥0∞) (hM : M < ⊤)
    (hsource : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
      AEStronglyMeasurable
        (fun x : Vec3 => (goodPointDomain.indicator u) (x,s)) volume ∧
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm
        ((goodPointDomain.indicator u) (x,s))) 3 volume ≤ M)
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (nhds 0))
    (R a : ℝ) (hR : 0 < R) (ha : a < 0)
    (C : ℝ)
    (hgrad : ∀ᶠ k in atTop,
      IntegrableOn (fun z => spatialGradientSq
        (parabolicRescaleVelocity x₀ t₀ (r k) u)
        (parabolicRescaleGradient x₀ t₀ (r k) Du) z)
        (spaceTimeSet (CKN.euclideanBall 0 R) (Ioo a 0)) volume ∧
      2 * (∫ z in spaceTimeSet (CKN.euclideanBall 0 R) (Ioo a 0),
        spatialGradientSq
          (parabolicRescaleVelocity x₀ t₀ (r k) u)
          (parabolicRescaleGradient x₀ t₀ (r k) Du) z) ≤ C) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ᶠ k in atTop,
      MemLp (parabolicRescaleVelocity x₀ t₀ (r k) u)
        (ENNReal.ofReal (10 / 3 : ℝ))
        (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ∧
      eLpNorm (parabolicRescaleVelocity x₀ t₀ (r k) u)
        (ENNReal.ofReal (10 / 3 : ℝ))
        (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ≤ B := by
  let B₀ := (blowupTenThirdsBound M (C / 2) R a) ^ ((10 / 3 : ℝ)⁻¹)
  let B : ℝ≥0∞ := ∑ _ : Fin 3, B₀
  have hcomponent (i : Fin 3) :=
    blowupRescale_eventually_component_tenThirds_of_gradient_bound
      u Du p hSuitable hu M hM hsource x₀ t₀ r hx₀ ht₀ hr hr0
      R a hR ha C hgrad i
  have hB₀ : B₀ < ⊤ := (hcomponent 0).1
  have hB : B < ⊤ := ENNReal.sum_lt_top.mpr (fun _ _ => hB₀)
  have hcomp : ∀ᶠ k in atTop, ∀ i : Fin 3,
      MemLp (fun z => parabolicRescaleVelocity x₀ t₀ (r k) u z i)
        (ENNReal.ofReal (10 / 3 : ℝ))
        (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ∧
      eLpNorm (fun z => parabolicRescaleVelocity x₀ t₀ (r k) u z i)
        (ENNReal.ofReal (10 / 3 : ℝ))
        (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ≤ B₀ :=
    Filter.eventually_all.mpr (fun i => (hcomponent i).2)
  refine ⟨B, hB, ?_⟩
  filter_upwards [hcomp] with k hk
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (10 / 3 : ℝ) := by norm_num
  have hnorm := blowup_vec3_eLpNorm_le_sum_components
    (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0))
    (ENNReal.ofReal (10 / 3 : ℝ)) hp
    (parabolicRescaleVelocity x₀ t₀ (r k) u) (fun i => (hk i).1)
  have hle : eLpNorm (parabolicRescaleVelocity x₀ t₀ (r k) u)
      (ENNReal.ofReal (10 / 3 : ℝ))
      (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ≤ B :=
    hnorm.trans (Finset.sum_le_sum (fun i _ => (hk i).2))
  exact ⟨(memLp_iff.mpr (lt_of_le_of_lt hle hB)), hle⟩

end ESS
