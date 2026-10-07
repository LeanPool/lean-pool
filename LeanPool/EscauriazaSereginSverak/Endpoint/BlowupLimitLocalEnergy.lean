/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitPressureData
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitEnergyPressure
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitSource

/-!
# Source suitability and the first blow-up bounds

The local hypotheses supply suitability on the interior source cylinder and
uniform pressure and gradient bounds on each fixed rescaled past cylinder.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The first step of the blow-up limit follows from the local hypotheses and
the fixed pressure split. -/
theorem blowup_limit_local_energy_pressure_of_source_data
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
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i) = 0)
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (nhds 0))
    (R a : ℝ) (hR : 0 < R) (ha : a < 0) :
    IsSuitableWeakSolution (vec3Ball 0 (3 / 4 : ℝ)) (Ioo (-1) 0) 3
      u Du p (0 : ParabolicPoint → Vec3) ∧
    ∃ Cg Cp : ℝ, 0 ≤ Cg ∧ 0 ≤ Cp ∧ ∀ᶠ k in atTop,
      IntegrableOn (fun z => spatialGradientSq
        (parabolicRescaleVelocity x₀ t₀ (r k) u)
        (parabolicRescaleGradient x₀ t₀ (r k) Du) z)
        (spaceTimeSet (CKN.euclideanBall 0 R) (Ioo a 0)) volume ∧
      2 * (∫ z in spaceTimeSet (CKN.euclideanBall 0 R) (Ioo a 0),
        spatialGradientSq
          (parabolicRescaleVelocity x₀ t₀ (r k) u)
          (parabolicRescaleGradient x₀ t₀ (r k) Du) z) ≤ Cg ∧
      MemLp (blowupPressure x₀ t₀ (r k) p) (3 / 2 : ℝ≥0∞)
        ((volume : Measure ParabolicPoint).restrict
          (vec3Ball 0 R ×ˢ Ioo a 0)) ∧
      (∫ z in vec3Ball 0 R ×ˢ Ioo a 0,
        |blowupPressure x₀ t₀ (r k) p z| ^ (3 / 2 : ℝ)) ≤ Cp := by
  have hSuitable := blowup_limit_source_suitable
    hu hDu hpmeas hL2 henergy hpLp hL3 hgrad hS2 hS3
  rcases blowup_limit_pressure_split_data
      hu hDu hpmeas hL2 henergy hpLp hL3 hgrad hS2 hS3 with
    ⟨hp₁, ⟨Mᵤ, hMᵤ, hsourceU⟩, ⟨Mₚ, hMₚ, hsourceP⟩, hp₂, hharm⟩
  let p₁ : ParabolicPoint → ℝ := pressureSplitRieszPressure
    (pressureSplitTensor u) (pressureSplitTensor_memLp hu hDu henergy hL3 hgrad)
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
    have hdiffSymm : (fun z : Vec3 × ℝ =>
        p₂ (parabolicHomeomorph.symm z)) =ᵐ[
        (volume : Measure (Vec3 × ℝ)).restrict
          (CKN.euclideanBall 0 1 ×ˢ Ioo (-1 : ℝ) 0)]
        (fun z => p (parabolicHomeomorph.symm z) -
          p₁ (parabolicHomeomorph.symm z)) := by
      filter_upwards [ae_restrict_mem (by
        rw [hball]
        exact (isOpen_vec3Ball (0 : Vec3) 1).measurableSet.prod measurableSet_Ioo)]
        with z hz
      have hx : z.1 ∈ vec3Ball (0 : Vec3) 1 := by simpa only [hball] using hz.1
      have hmem : parabolicHomeomorph.symm z ∈ goodPointDomain := by
        change z.1 ∈ vec3Ball (0 : Vec3) 1 ∧ z.2 ∈ Ioo (-1 : ℝ) 0
        exact ⟨hx, hz.2⟩
      change goodPointDomain.indicator (fun z => p z - p₁ z)
        (parabolicHomeomorph.symm z) = _
      rw [Set.indicator_of_mem hmem]
    have hdiff : (fun z : Vec3 × ℝ => p₂ (z.1,z.2)) =ᵐ[
        (volume : Measure (Vec3 × ℝ)).restrict
          (CKN.euclideanBall 0 1 ×ˢ Ioo (-1 : ℝ) 0)]
        (fun z => p (z.1,z.2) - p₁ (z.1,z.2)) := by
      filter_upwards [hdiffSymm] with z hz
      simpa only [parabolicHomeomorph_symm_apply] using hz
    rw [memLp_congr_ae hdiff] at hp₂'
    rw [hmeasure]
    exact hp₂'
  have hharm' : ∀ᵐ t ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      CKN.Foundation.Heat.WeaklyHarmonicOn (CKN.euclideanBall 0 1)
        (fun x : Vec3 => p (x,t) - p₁ (x,t)) := by
    filter_upwards [hharm, ae_restrict_mem measurableSet_Ioo] with t hh ht
    intro ψ hψsmooth hψcompact hψsupport
    have hEq (x : Vec3) (hx : x ∈ CKN.euclideanBall 0 1) :
        p₂ (parabolicHomeomorph.symm (x,t)) =
          p (parabolicHomeomorph.symm (x,t)) -
            p₁ (parabolicHomeomorph.symm (x,t)) := by
      have hx' : x ∈ vec3Ball (0 : Vec3) 1 := by
        simpa only [hball] using hx
      have hmem : parabolicHomeomorph.symm (x,t) ∈ goodPointDomain := by
        change x ∈ vec3Ball (0 : Vec3) 1 ∧ t ∈ Ioo (-1 : ℝ) 0
        exact ⟨hx', ht⟩
      change goodPointDomain.indicator (fun z => p z - p₁ z)
        (parabolicHomeomorph.symm (x,t)) = _
      rw [Set.indicator_of_mem hmem]
    calc
      (∫ x in CKN.euclideanBall 0 1,
          (p (x,t) - p₁ (x,t)) * CKN.spatialLaplacian ψ x) =
        ∫ x in CKN.euclideanBall 0 1,
          p₂ (x,t) * CKN.spatialLaplacian ψ x := by
            apply setIntegral_congr_fun (by
              rw [hball]
              exact (isOpen_vec3Ball (0 : Vec3) 1).measurableSet)
            intro x hx
            simpa only [parabolicHomeomorph_symm_apply] using
              congrArg (fun y : ℝ => y * CKN.spatialLaplacian ψ x)
                (hEq x hx).symm
      _ = 0 := hh ψ hψsmooth hψcompact hψsupport
  obtain ⟨⟨Cg, hCg, hgradBound⟩, ⟨Cp, hCp, hpressBound⟩⟩ :=
    blowup_limit_local_energy_pressure u Du p
      p₁
      hSuitable (by
        have hD : AEStronglyMeasurable (goodPointDomain.indicator u)
            (volume : Measure ParabolicPoint) := by
          exact (aestronglyMeasurable_indicator_iff
            ((isOpen_vec3Ball (0 : Vec3) 1).measurableSet.prod
              measurableSet_Ioo)).2 hu
        exact hD)
      Mᵤ hMᵤ hsourceU hp₁ Mₚ hMₚ hsourceP hp₂diff hharm'
      x₀ t₀ r hx₀ ht₀ hr hr0 R a hR ha
  refine ⟨hSuitable, Cg, Cp, hCg, hCp, ?_⟩
  filter_upwards [hgradBound, hpressBound] with k hg hp
  exact ⟨hg.1, hg.2, hp.1, hp.2⟩

end ESS
