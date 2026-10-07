/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCCutoffL2
public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanSobolevPass
public import LeanPool.EscauriazaSereginSverak.Statements.CarlemanGaussian

/-!
# Gaussian Carleman inequality on a spatial ball

Compact support permits restricting the smooth Gaussian estimate to the
normalized ball used in `lem:uc-gaussian`.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

private theorem uc_gaussian_smooth_ball
    (c₀ : ℝ)
    (hgauss : ∀ a : ℝ, 0 < a → ∀ v : ParabolicPoint → Vec3,
      v ∈ spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 2) →
      (∫ z in spaceTimeSet Set.univ (Ioo 0 2),
        ucGaussianWeight a z *
          (a / z.2 * vec3EuclideanNorm (v z) ^ 2 +
            spatialGradientSq v (spatialGradient v) z)) ≤
        c₀ * (∫ z in spaceTimeSet Set.univ (Ioo 0 2),
          ucGaussianWeight a z *
            vec3EuclideanNorm (fun i =>
              timePartial (fun y => v y i) z +
                ∑ j, spatialSecondPartial (fun y => v y i) j j z) ^ 2))
    (ρ a : ℝ) (ha : 0 < a)
    (v : ParabolicPoint → Vec3)
    (hv : v ∈ spaceTimeTestFunction (V := Vec3) (vec3Ball 0 ρ) (Ioo 0 2)) :
    (∫ z in spaceTimeSet (vec3Ball 0 ρ) (Ioo 0 2),
      ucGaussianWeight a z *
        (a / z.2 * vec3EuclideanNorm (v z) ^ 2 +
          spatialGradientSq v (spatialGradient v) z)) ≤
      c₀ *
        (∫ z in spaceTimeSet (vec3Ball 0 ρ) (Ioo 0 2),
          ucGaussianWeight a z *
            vec3EuclideanNorm (fun i =>
              timePartial (fun y => v y i) z +
                ∑ j, spatialSecondPartial (fun y => v y i) j j z) ^ 2) := by
  have hfullTest : v ∈ spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 2) := by
    refine ⟨hv.1, hv.2.1, ?_⟩
    intro z hz
    exact ⟨Set.mem_univ _, (hv.2.2 hz).2⟩
  have hfull := hgauss a ha v hfullTest
  have hfullMeas : MeasurableSet (spaceTimeSet Set.univ (Ioo (0 : ℝ) 2)) :=
    (isOpen_spaceTimeSet Set.univ (Ioo 0 2) isOpen_univ isOpen_Ioo).measurableSet
  have hsub : spaceTimeSet (vec3Ball 0 ρ) (Ioo (0 : ℝ) 2) ⊆
      spaceTimeSet Set.univ (Ioo (0 : ℝ) 2) := by
    intro z hz
    exact ⟨Set.mem_univ _, hz.2⟩
  have hzero (z : ParabolicPoint)
      (hz : z ∈ spaceTimeSet Set.univ (Ioo (0 : ℝ) 2) \
        spaceTimeSet (vec3Ball 0 ρ) (Ioo (0 : ℝ) 2)) :
      v z = 0 ∧ spatialGradientSq v (spatialGradient v) z = 0 ∧
        (fun i : Fin 3 => timePartial (fun y => v y i) z +
          ∑ j, spatialSecondPartial (fun y => v y i) j j z) = 0 := by
    have hznot : z ∉ tsupport (show Vec3 × ℝ → Vec3 from v) := by
      intro hzs
      exact hz.2 (hv.2.2 hzs)
    have hcomponent (i : Fin 3) := gauss_component_zero_outside v z hznot i
    have hvzero : v z = 0 := by
      funext i
      exact (hcomponent i).1
    have hgrad : spatialGradientSq v (spatialGradient v) z = 0 := by
      simp only [spatialGradientSq, spatialGradient]
      simp [fun i j => (hcomponent i).2.2 j |>.1]
    have hres : (fun i : Fin 3 => timePartial (fun y => v y i) z +
        ∑ j, spatialSecondPartial (fun y => v y i) j j z) = 0 := by
      funext i
      simp [((hcomponent i).2.1), fun j => (hcomponent i).2.2 j |>.2]
    exact ⟨hvzero, hgrad, hres⟩
  have hleftEq :
      (∫ z in spaceTimeSet Set.univ (Ioo (0 : ℝ) 2),
        ucGaussianWeight a z *
          (a / z.2 * vec3EuclideanNorm (v z) ^ 2 +
            spatialGradientSq v (spatialGradient v) z)) =
      ∫ z in spaceTimeSet (vec3Ball 0 ρ) (Ioo (0 : ℝ) 2),
        ucGaussianWeight a z *
          (a / z.2 * vec3EuclideanNorm (v z) ^ 2 +
            spatialGradientSq v (spatialGradient v) z) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hfullMeas hsub
    intro z hz
    obtain ⟨hvzero, hgrad, _⟩ := hzero z hz
    simp [hvzero, hgrad, vec3EuclideanNorm_zero]
  have hrightEq :
      (∫ z in spaceTimeSet Set.univ (Ioo (0 : ℝ) 2),
        ucGaussianWeight a z *
          vec3EuclideanNorm (fun i =>
            timePartial (fun y => v y i) z +
              ∑ j, spatialSecondPartial (fun y => v y i) j j z) ^ 2) =
      ∫ z in spaceTimeSet (vec3Ball 0 ρ) (Ioo (0 : ℝ) 2),
        ucGaussianWeight a z *
          vec3EuclideanNorm (fun i =>
            timePartial (fun y => v y i) z +
              ∑ j, spatialSecondPartial (fun y => v y i) j j z) ^ 2 := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hfullMeas hsub
    intro z hz
    obtain ⟨_, _, hres⟩ := hzero z hz
    simp [hres, vec3EuclideanNorm_zero]
  have hfull' :
      (∫ z in spaceTimeSet Set.univ (Ioo (0 : ℝ) 2),
        ucGaussianWeight a z *
          (a / z.2 * vec3EuclideanNorm (v z) ^ 2 +
            spatialGradientSq v (spatialGradient v) z)) ≤
        c₀ *
          (∫ z in spaceTimeSet Set.univ (Ioo (0 : ℝ) 2),
            ucGaussianWeight a z *
              vec3EuclideanNorm (fun i =>
                timePartial (fun y => v y i) z +
                  ∑ j, spatialSecondPartial (fun y => v y i) j j z) ^ 2) := by
    simpa only [ucGaussianWeight, gaussCarlemanTimeWeight] using hfull
  rw [hleftEq, hrightEq] at hfull'
  exact hfull'

/-- A fixed smooth Gaussian constant passes unchanged to compactly
supported weak fields on a spatial ball. -/
theorem uc_gaussian_weak_carleman_ball_with_constant
    (ρ : ℝ) (c₀ : ℝ)
    (hgaussRaw : ∀ a : ℝ, 0 < a → ∀ v : ParabolicPoint → Vec3,
      v ∈ spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 2) →
      (∫ z in spaceTimeSet Set.univ (Ioo 0 2),
        (z.2 * Real.exp ((1 - z.2) / 3)) ^ (-2 * a) *
          Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2)) *
          (a / z.2 * vec3EuclideanNorm (v z) ^ 2 +
            spatialGradientSq v (spatialGradient v) z)) ≤
        c₀ * (∫ z in spaceTimeSet Set.univ (Ioo 0 2),
          (z.2 * Real.exp ((1 - z.2) / 3)) ^ (-2 * a) *
            Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2)) *
            vec3EuclideanNorm (fun i =>
              timePartial (fun y => v y i) z +
                ∑ j, spatialSecondPartial (fun y => v y i) j j z) ^ 2))
    {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
      w Dw D2w Dtw)
    (hcompact : HasCompactSupport w)
    (htsupport : tsupport w ⊆ ucCylinder ρ)
    (hL2 : (∫⁻ z in ucCylinder ρ,
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) :
    ∀ a : ℝ, 0 < a →
      (∫ z in vec3Ball 0 ρ ×ˢ Ioo (0 : ℝ) 2,
        ucGaussianWeight a z * (a / z.2) *
          vec3EuclideanNorm (w (parabolicHomeomorph.symm z)) ^ 2 +
        ucGaussianWeight a z *
          ∑ i, ∑ j, Dw (parabolicHomeomorph.symm z) i j ^ 2
        ∂(volume : Measure (Vec3 × ℝ))) ≤
        c₀ * (∫ z in vec3Ball 0 ρ ×ˢ Ioo (0 : ℝ) 2,
          ucGaussianWeight a z *
            vec3EuclideanNorm (fun i =>
              Dtw (parabolicHomeomorph.symm z) i +
                ∑ j, D2w (parabolicHomeomorph.symm z) i j j) ^ 2
          ∂(volume : Measure (Vec3 × ℝ))) := by
  have hgauss : ∀ a : ℝ, 0 < a → ∀ v : ParabolicPoint → Vec3,
      v ∈ spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 2) →
      (∫ z in spaceTimeSet Set.univ (Ioo 0 2),
        ucGaussianWeight a z *
          (a / z.2 * vec3EuclideanNorm (v z) ^ 2 +
            spatialGradientSq v (spatialGradient v) z)) ≤
        c₀ * (∫ z in spaceTimeSet Set.univ (Ioo 0 2),
          ucGaussianWeight a z *
            vec3EuclideanNorm (fun i =>
              timePartial (fun y => v y i) z +
                ∑ j, spatialSecondPartial (fun y => v y i) j j z) ^ 2) := by
    intro a ha v hv
    simpa only [ucGaussianWeight, gaussCarlemanTimeWeight] using
      hgaussRaw a ha v hv
  intro a ha
  let U : Set (Vec3 × ℝ) := vec3Ball 0 ρ ×ˢ Ioo (0 : ℝ) 2
  let ρw : Vec3 × ℝ → ℝ := fun z => ucGaussianWeight a z
  let σw : Vec3 × ℝ → ℝ := fun z => ρw z * (a / z.2)
  have hρcont : ContinuousOn ρw U := by
    have ht : Continuous (fun z : Vec3 × ℝ => gaussCarlemanTimeWeight z.2) := by
      dsimp [gaussCarlemanTimeWeight]
      fun_prop
    have htpos (z : Vec3 × ℝ) (hz : z ∈ U) :
        0 < gaussCarlemanTimeWeight z.2 := by
      have hz0 : 0 < z.2 := hz.2.1
      unfold gaussCarlemanTimeWeight
      positivity
    have htpow : ContinuousOn
        (fun z : Vec3 × ℝ => gaussCarlemanTimeWeight z.2 ^ (-2 * a)) U :=
      ht.continuousOn.rpow_const (fun z hz => Or.inl (htpos z hz).ne')
    have hnum : Continuous (fun z : Vec3 × ℝ => vec3EuclideanNorm z.1 ^ 2) :=
      (continuous_vec3EuclideanNorm.comp continuous_fst).pow 2
    have hden : Continuous (fun z : Vec3 × ℝ => 4 * z.2) :=
      continuous_const.mul continuous_snd
    have hquot : ContinuousOn
        (fun z : Vec3 × ℝ => -(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2)) U := by
      apply hnum.neg.continuousOn.div hden.continuousOn
      intro z hz
      have hz0 : 0 < z.2 := hz.2.1
      positivity
    have hexp : ContinuousOn
        (fun z : Vec3 × ℝ => Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) U :=
      Real.continuous_exp.comp_continuousOn hquot
    exact htpow.mul hexp
  have hdiv : ContinuousOn (fun z : Vec3 × ℝ => a / z.2) U := by
    apply continuous_const.continuousOn.div continuous_snd.continuousOn
    intro z hz
    exact hz.2.1.ne'
  have hσcont : ContinuousOn σw U := hρcont.mul hdiv
  have hsmooth : ∀ v : Vec3 × ℝ → Vec3,
      v ∈ spaceTimeTestFunction (V := Vec3) (vec3Ball 0 ρ) (Ioo 0 2) →
      (∫ z in U,
        σw z * vec3EuclideanNorm (v z) ^ 2 +
          ρw z * spatialGradientSq v (spatialGradient v) z
          ∂(volume : Measure (Vec3 × ℝ))) ≤
        c₀ * (∫ z in U,
          ρw z * vec3EuclideanNorm (fun i =>
            timePartial (fun y => v y i) z +
              ∑ j, spatialSecondPartial (fun y => v y i) j j z) ^ 2
            ∂(volume : Measure (Vec3 × ℝ))) := by
    intro v hv
    let vp : ParabolicPoint → Vec3 := fun z => v (parabolicHomeomorph z)
    have hvp : vp ∈ spaceTimeTestFunction (V := Vec3) (vec3Ball 0 ρ) (Ioo 0 2) := by
      have heq : (show Vec3 × ℝ → Vec3 from vp) = v := by
        funext z
        rcases z with ⟨x, s⟩
        rfl
      change (show Vec3 × ℝ → Vec3 from vp) ∈
        spaceTimeTestFunction (V := Vec3) (vec3Ball 0 ρ) (Ioo 0 2)
      rw [heq]
      exact hv
    have h := uc_gaussian_smooth_ball c₀ hgauss ρ a ha vp hvp
    have hvpeq : (show Vec3 × ℝ → Vec3 from vp) = v := by
      funext z
      rcases z with ⟨x, s⟩
      rfl
    rw [hvpeq] at h
    convert h using 1
    · congr 1
      ext z
      dsimp [σw, ρw, ucGaussianWeight, gaussCarlemanTimeWeight]
      ring
    · congr 1
  have hpass := compactlySupportedSpaceTimeCarleman_of_smooth
    (isOpen_vec3Ball 0 ρ) isOpen_Ioo hderiv hcompact
    (by simpa only [ucCylinder] using htsupport) hL2
    hρcont hσcont hρcont hsmooth
  simpa only [σw, ρw, mul_assoc] using hpass

end ESS
