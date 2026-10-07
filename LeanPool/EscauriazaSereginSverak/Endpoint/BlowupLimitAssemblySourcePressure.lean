/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitPressureData
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitSource

/-!
# Source data for the blow-up estimates

The hypotheses of `thm:ess-local` give the source suitability and the fixed
pressure split data (`lem:pressure-split`) in the shapes used by the
blow-up estimates of `prop:blowup-limit`.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The source hypotheses give suitability on the inner cylinder, the
measurability of the zero-extended velocity, and the pressure split data
with the harmonic remainder written as p - p₁. -/
theorem blowupLimitAssembly_source_pressure_data
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hpmeas : AEStronglyMeasurable p
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL2 : essSup (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
      ‖u (x,t)‖ₑ ^ (2 : ℝ)) (volume.restrict (Ioo (-1) 0)) < ⊤)
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hpLp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
      ENNReal.ofReal (vec3EuclideanNorm (u (x,t))) ^ (3 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1) (fun x => u (x,t) i)
        (fun x => Du (x,t) i))
    (hS2 : ∀ ψ ∈ spaceTimeTestFunction (V := ℝ)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0)
    (hS3 : ∀ φ ∈ spaceTimeTestFunction (V := Vec3)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i) = 0) :
    let p₁ : ParabolicPoint → ℝ := pressureSplitRieszPressure
      (pressureSplitTensor u) (pressureSplitTensor_memLp hu hDu henergy hL3 hgrad)
    IsSuitableWeakSolution (vec3Ball 0 (3 / 4 : ℝ)) (Ioo (-1) 0) 3 u Du p
        (0 : ParabolicPoint → Vec3) ∧
      AEStronglyMeasurable (goodPointDomain.indicator u)
        (volume : Measure ParabolicPoint) ∧
      AEStronglyMeasurable p₁ (volume.restrict (Set.univ ×ˢ Ioo (-1 : ℝ) 0)) ∧
      (∃ Mᵤ : ℝ≥0∞, Mᵤ < ⊤ ∧
        ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
          AEStronglyMeasurable (fun x : Vec3 =>
            (goodPointDomain.indicator u) (x,s)) volume ∧
          eLpNorm (fun x : Vec3 => vec3EuclideanNorm
            ((goodPointDomain.indicator u) (x,s))) 3 volume ≤ Mᵤ) ∧
      (∃ Mₚ : ℝ≥0∞, Mₚ < ⊤ ∧
        ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
          AEStronglyMeasurable (fun x : Vec3 => p₁ (x,s)) volume ∧
          eLpNorm (fun x : Vec3 => p₁ (x,s)) (3 / 2 : ℝ≥0∞) volume ≤ Mₚ) ∧
      MemLp (fun z : Vec3 × ℝ => p (z.1,z.2) - p₁ (z.1,z.2))
        (3 / 2 : ℝ≥0∞)
        ((volume.restrict (CKN.euclideanBall 0 1)).prod
          (volume.restrict (Ioo (-1 : ℝ) 0))) ∧
      (∀ᵐ t ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
        CKN.Foundation.Heat.WeaklyHarmonicOn (CKN.euclideanBall 0 1)
          (fun x : Vec3 => p (x,t) - p₁ (x,t))) := by
  intro p₁
  have hSuitable := blowup_limit_source_suitable
    hu hDu hpmeas hL2 henergy hpLp hL3 hgrad hS2 hS3
  rcases blowup_limit_pressure_split_data
      hu hDu hpmeas hL2 henergy hpLp hL3 hgrad hS2 hS3 with
    ⟨hp₁, hU, hP, hp₂, hharm⟩
  let p₂ : ParabolicPoint → ℝ := pressureSplitRemainder p p₁
  have hball : CKN.euclideanBall (0 : Vec3) 1 = vec3Ball 0 1 := by
    rw [CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball (by norm_num)]
  have hmeasure : (volume.restrict (CKN.euclideanBall (0 : Vec3) 1)).prod
      (volume.restrict (Ioo (-1 : ℝ) 0)) =
      (volume : Measure (Vec3 × ℝ)).restrict
        (CKN.euclideanBall 0 1 ×ˢ Ioo (-1 : ℝ) 0) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
  have hp₂diff : MemLp (fun z : Vec3 × ℝ => p (z.1,z.2) - p₁ (z.1,z.2))
      (3 / 2 : ℝ≥0∞)
      ((volume.restrict (CKN.euclideanBall 0 1)).prod
        (volume.restrict (Ioo (-1 : ℝ) 0))) := by
    have hp₂' := hp₂
    rw [hmeasure] at hp₂'
    have hdiff : (fun z : Vec3 × ℝ => p₂ (z.1,z.2)) =ᵐ[
        (volume : Measure (Vec3 × ℝ)).restrict
          (CKN.euclideanBall 0 1 ×ˢ Ioo (-1 : ℝ) 0)]
        (fun z => p (z.1,z.2) - p₁ (z.1,z.2)) := by
      filter_upwards [ae_restrict_mem (by
        rw [hball]
        exact (isOpen_vec3Ball (0 : Vec3) 1).measurableSet.prod measurableSet_Ioo)]
        with z hz
      have hx : z.1 ∈ vec3Ball (0 : Vec3) 1 := by simpa only [hball] using hz.1
      have hmem : ((z.1, z.2) : ParabolicPoint) ∈ goodPointDomain := ⟨hx, hz.2⟩
      exact Set.indicator_of_mem hmem (fun z => p z - p₁ z)
    rw [memLp_congr_ae hdiff] at hp₂'
    rw [hmeasure]
    exact hp₂'
  have hharm' : ∀ᵐ t ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      CKN.Foundation.Heat.WeaklyHarmonicOn (CKN.euclideanBall 0 1)
        (fun x : Vec3 => p (x,t) - p₁ (x,t)) := by
    filter_upwards [hharm, ae_restrict_mem measurableSet_Ioo] with t hh ht
    intro ψ hψsmooth hψcompact hψsupport
    have hEq (x : Vec3) (hx : x ∈ CKN.euclideanBall 0 1) :
        p₂ (x,t) = p (x,t) - p₁ (x,t) := by
      have hx' : x ∈ vec3Ball (0 : Vec3) 1 := by
        simpa only [hball] using hx
      have hmem : ((x,t) : ParabolicPoint) ∈ goodPointDomain := ⟨hx', ht⟩
      exact Set.indicator_of_mem hmem (fun z => p z - p₁ z)
    calc
      (∫ x in CKN.euclideanBall 0 1,
          (p (x,t) - p₁ (x,t)) * CKN.spatialLaplacian ψ x) =
        ∫ x in CKN.euclideanBall 0 1,
          p₂ (x,t) * CKN.spatialLaplacian ψ x := by
            apply setIntegral_congr_fun (by
              rw [hball]
              exact (isOpen_vec3Ball (0 : Vec3) 1).measurableSet)
            intro x hx
            simp only
            rw [hEq x hx]
      _ = 0 := hh ψ hψsmooth hψcompact hψsupport
  have hD : AEStronglyMeasurable (goodPointDomain.indicator u)
      (volume : Measure ParabolicPoint) :=
    (aestronglyMeasurable_indicator_iff
      ((isOpen_vec3Ball (0 : Vec3) 1).measurableSet.prod measurableSet_Ioo)).2 hu
  exact ⟨hSuitable, hD, hp₁, hU, hP, hp₂diff, hharm'⟩

end ESS

end
