/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupTenThirdsTop
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupVelocityMeas
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupGradientSource

public section

open CKN CKN.Foundation.Parabolic MeasureTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace ESS

/-- The finite-past interpolation estimate holds on the entire open
terminal-time cylinder for one suitable rescaling. -/
theorem blowupRescale_component_tenThirds_uniform_top
    (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ)
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r)
    (R a : ℝ) (hR : 0 < R)
    (hsol : IsSuitableWeakSolutionIntegrable
      (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0) 3
      (parabolicRescaleVelocity x₀ t₀ r u)
      (parabolicRescaleGradient x₀ t₀ r Du)
      (parabolicRescalePressure x₀ t₀ r p) 0)
    (hdom : vec3Ball 0 R ×ˢ Ioo a 0 ⊆ blowupDomain x₀ t₀ r)
    (htime : Ioo a 0 ⊆ CKN.rescaledTime r t₀ (Ioo (-1 : ℝ) 0))
    (hu : AEStronglyMeasurable (goodPointDomain.indicator u)
      (volume : Measure ParabolicPoint))
    (M : ℝ≥0∞) (hM : M < ⊤)
    (hsource : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
      AEStronglyMeasurable
        (fun x : Vec3 => (goodPointDomain.indicator u) (x,s)) volume ∧
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm
        ((goodPointDomain.indicator u) (x,s))) 3 volume ≤ M)
    (Cg : ℝ)
    (hgradInt : IntegrableOn (fun z => spatialGradientSq
      (parabolicRescaleVelocity x₀ t₀ r u)
      (parabolicRescaleGradient x₀ t₀ r Du) z)
      (vec3Ball 0 R ×ˢ Ioo a 0) volume)
    (hgradBound : (∫ (z : ParabolicPoint) in vec3Ball 0 R ×ˢ Ioo a 0,
      spatialGradientSq
        (parabolicRescaleVelocity x₀ t₀ r u)
        (parabolicRescaleGradient x₀ t₀ r Du) z
      ∂(volume : Measure ParabolicPoint)) ≤ Cg)
    (i : Fin 3) :
    blowupTenThirdsBound M Cg R a < ⊤ ∧
      MemLp (fun z => parabolicRescaleVelocity x₀ t₀ r u z i)
        (ENNReal.ofReal (10 / 3 : ℝ))
        (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ∧
      eLpNorm (fun z => parabolicRescaleVelocity x₀ t₀ r u z i)
        (ENNReal.ofReal (10 / 3 : ℝ))
        (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ^ (10 / 3 : ℝ) ≤
          blowupTenThirdsBound M Cg R a := by
  let S := vec3Ball (0 : Vec3) R ×ˢ Ioo a 0
  have hmeasV : AEStronglyMeasurable (blowupVelocity x₀ t₀ r u)
      (volume : Measure ParabolicPoint) :=
    blowupRescaledVelocity_aestronglyMeasurable
      (goodPointDomain.indicator u) hu x₀ t₀ r hr
  have heq : (blowupVelocity x₀ t₀ r u) =ᵐ[volume.restrict S]
      parabolicRescaleVelocity x₀ t₀ r u := by
    filter_upwards [ae_restrict_mem
      ((isOpen_vec3Ball 0 R).measurableSet.prod measurableSet_Ioo)] with z hz
    exact blowupVelocity_eq_of_mem x₀ t₀ r u z (hdom hz)
  have hmeas : AEStronglyMeasurable
      (fun z => parabolicRescaleVelocity x₀ t₀ r u z i)
      (volume.restrict S) :=
    (continuous_apply i).comp_aestronglyMeasurable
      ((hmeasV.restrict).congr heq)
  let K := blowupTenThirdsBound M Cg R a
  obtain ⟨hK, hfinite⟩ :=
    blowupRescale_component_tenThirds_uniform_finite_past
      u Du p x₀ t₀ r hr R a hR hsol hdom htime
      M hM hsource Cg hgradInt hgradBound i
  let q : NNReal := ⟨10 / 3, by norm_num⟩
  have hq : (q : ℝ≥0∞) = ENNReal.ofReal (10 / 3 : ℝ) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (by norm_num : (0 : ℝ) ≤ 10 / 3)]
    congr 1
  have hqreal : (q : ℝ) = (10 / 3 : ℝ) := by rfl
  have hqne : q ≠ 0 := by
    intro hz
    have hzreal : (q : ℝ) = 0 := by rw [hz]; rfl
    rw [hqreal] at hzreal
    norm_num at hzreal
  have htop := blowup_eLpNorm_bound_to_time_zero
    (vec3Ball (0 : Vec3) R) (isOpen_vec3Ball 0 R).measurableSet a
    (fun z => parabolicRescaleVelocity x₀ t₀ r u z i)
    q hqne
    hmeas K hK (by
      intro b hb
      by_cases hab : a < b
      · simpa only [hq, hqreal] using hfinite b hab hb
      · have heq : Ioo a b = ∅ := Ioo_eq_empty_iff.mpr hab
        have hzero : (volume : Measure ParabolicPoint).restrict
            (vec3Ball 0 R ×ˢ Ioo a b) = 0 := by
          rw [heq, Set.prod_empty]
          change (volume : Measure (Vec3 × ℝ)).restrict ∅ = 0
          exact Measure.restrict_empty
        rw [hzero]
        refine ⟨memLp_measure_zero, ?_⟩
        have hqpos : 0 < (q : ℝ) := by rw [hqreal]; norm_num
        rw [eLpNorm_measure_zero, ENNReal.zero_rpow_of_pos hqpos]
        exact bot_le)
  exact ⟨hK, by simpa only [hq, hqreal] using htop⟩

end ESS
