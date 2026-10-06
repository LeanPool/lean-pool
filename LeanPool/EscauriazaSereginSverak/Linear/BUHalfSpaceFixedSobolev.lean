/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanSobolevConsumers

/-!
# Fixed constants in the half-space Sobolev passage

The density passage preserves the threshold and constant supplied by the
smooth half-space estimate (`lem:carleman-sobolev`).
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal Pointwise
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

private def halfSpacePhaseProduct (a α : ℝ) (z : Vec3 × ℝ) : ℝ :=
  -(z.1 0 ^ 2 + z.1 1 ^ 2) / (8 * z.2) +
    a * (1 - z.2) * z.1 2 ^ (2 * α) / z.2 ^ α

private def halfSpaceDensity (a α : ℝ) (z : Vec3 × ℝ) : ℝ :=
  z.2 ^ 2 * Real.exp (2 * halfSpacePhaseProduct a α z)

private def halfSpaceMassWeight (a α : ℝ) (z : Vec3 × ℝ) : ℝ :=
  halfSpaceDensity a α z * (a / z.2 ^ 2)

private def halfSpaceGradientWeight (a α : ℝ) (z : Vec3 × ℝ) : ℝ :=
  halfSpaceDensity a α z / z.2

private def productFieldToParabolic (v : Vec3 × ℝ → Vec3) : ParabolicPoint → Vec3 :=
  fun p => v (p.1, p.2)

/-- A fixed smooth half-space Carleman constant passes unchanged to a
compactly supported field with weak space-time derivatives. -/
theorem bu_carleman_sobolev_halfspace_fixed
    (α a₀ c : ℝ)
    (w : ParabolicPoint → Vec3) (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3) (Dtw : ParabolicPoint → Vec3)
    (hderiv : HasSpaceTimeWeakDerivs {x : Vec3 | 1 < x 2} (Ioo 0 1)
      w Dw D2w Dtw)
    (hcompact : HasCompactSupport w)
    (htsupport : tsupport w ⊆
      spaceTimeSet {x : Vec3 | 1 < x 2} (Ioo 0 1))
    (hL2 : (∫⁻ z in spaceTimeSet {x : Vec3 | 1 < x 2} (Ioo 0 1),
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hSmooth : ∀ a : ℝ, a₀ < a → ∀ v : ParabolicPoint → Vec3,
        v ∈ spaceTimeTestFunction (V := Vec3) {x : Vec3 | 1 < x 2} (Ioo 0 1) →
        (∫ z in spaceTimeSet {x : Vec3 | 1 < x 2} (Ioo 0 1),
          z.2 ^ 2 * Real.exp (2 * halfSpacePhase a α z) *
            (a * vec3EuclideanNorm (v z) ^ 2 / z.2 ^ 2 +
              spatialGradientSq v (spatialGradient v) z / z.2)) ≤
        c * (∫ z in spaceTimeSet {x : Vec3 | 1 < x 2} (Ioo 0 1),
          z.2 ^ 2 * Real.exp (2 * halfSpacePhase a α z) *
            vec3EuclideanNorm (fun i => timePartial (fun y => v y i) z +
              ∑ j, spatialSecondPartial (fun y => v y i) j j z) ^ 2)) :
    ∀ a : ℝ, a₀ < a →
      ∫ z in spaceTimeSet {x : Vec3 | 1 < x 2} (Ioo 0 1),
        z.2 ^ 2 * Real.exp (2 * halfSpacePhase a α z) *
          (a * vec3EuclideanNorm (w z) ^ 2 / z.2 ^ 2 +
            spatialGradientSq w Dw z / z.2) ≤
      c * ∫ z in spaceTimeSet {x : Vec3 | 1 < x 2} (Ioo 0 1),
        z.2 ^ 2 * Real.exp (2 * halfSpacePhase a α z) *
          vec3EuclideanNorm (fun i => Dtw z i + ∑ j, D2w z i j j) ^ 2 := by
  intro a ha
  let ρ : Vec3 × ℝ → ℝ := halfSpaceDensity a α
  let σ : Vec3 × ℝ → ℝ := halfSpaceMassWeight a α
  let τ : Vec3 × ℝ → ℝ := halfSpaceGradientWeight a α
  have hΩ : IsOpen {x : Vec3 | 1 < x 2} := by
    exact (isOpen_lt continuous_const (continuous_apply 2))
  have hI : IsOpen (Ioo (0 : ℝ) 1) := isOpen_Ioo
  have hSmoothProduct : ∀ v : Vec3 × ℝ → Vec3,
      v ∈ spaceTimeTestFunction (V := Vec3) {x : Vec3 | 1 < x 2} (Ioo 0 1) →
      (∫ z in {x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1,
        σ z * vec3EuclideanNorm (v z) ^ 2 +
          τ z * spatialGradientSq v (spatialGradient v) z
          ∂(volume : Measure (Vec3 × ℝ))) ≤
      c * (∫ z in {x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1,
          ρ z * vec3EuclideanNorm (fun i =>
            timePartial (fun y => v y i) z +
              ∑ j, spatialSecondPartial (fun y => v y i) j j z) ^ 2
            ∂(volume : Measure (Vec3 × ℝ))) := by
    intro v hv
    have htest : productFieldToParabolic v ∈ spaceTimeTestFunction (V := Vec3)
        {x : Vec3 | 1 < x 2} (Ioo 0 1) := by
      change (fun z : Vec3 × ℝ => v (z.1, z.2)) ∈
        spaceTimeTestFunction (V := Vec3) {x : Vec3 | 1 < x 2} (Ioo 0 1)
      simpa using hv
    have hsmooth := hSmooth a ha (productFieldToParabolic v) htest
    rw [setIntegral_parabolic_to_product] at hsmooth
    rw [setIntegral_parabolic_to_product] at hsmooth
    have hleft :
        (∫ z in {x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1,
          σ z * vec3EuclideanNorm (v z) ^ 2 +
            τ z * spatialGradientSq v (spatialGradient v) z
            ∂(volume : Measure (Vec3 × ℝ))) =
          ∫ z in {x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1,
            (parabolicHomeomorph.symm z).2 ^ 2 *
              Real.exp (2 * halfSpacePhase a α (parabolicHomeomorph.symm z)) *
              (a * vec3EuclideanNorm (productFieldToParabolic v
                (parabolicHomeomorph.symm z)) ^ 2 /
                (parabolicHomeomorph.symm z).2 ^ 2 +
                spatialGradientSq (productFieldToParabolic v)
                  (spatialGradient (productFieldToParabolic v))
                  (parabolicHomeomorph.symm z) /
                  (parabolicHomeomorph.symm z).2)
            ∂(volume : Measure (Vec3 × ℝ)) := by
      apply setIntegral_congr_ae (hΩ.prod hI).measurableSet
      filter_upwards [] with z hz
      rw [parabolicHomeomorph_symm_apply]
      simp [σ, τ, halfSpaceMassWeight, halfSpaceGradientWeight,
        halfSpaceDensity, halfSpacePhaseProduct, halfSpacePhase,
        productFieldToParabolic,
        spatialGradientSq, spatialGradient, spatialPartial]
      ring
    have hright :
        (∫ z in {x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1,
          ρ z * vec3EuclideanNorm (fun i =>
            timePartial (fun y => v y i) z +
              ∑ j, spatialSecondPartial (fun y => v y i) j j z) ^ 2
            ∂(volume : Measure (Vec3 × ℝ))) =
          ∫ z in {x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1,
            (parabolicHomeomorph.symm z).2 ^ 2 *
              Real.exp (2 * halfSpacePhase a α (parabolicHomeomorph.symm z)) *
              vec3EuclideanNorm (fun i =>
                timePartial (fun y => productFieldToParabolic v y i)
                  (parabolicHomeomorph.symm z) +
                  ∑ j, spatialSecondPartial (fun y => productFieldToParabolic v y i) j j
                    (parabolicHomeomorph.symm z)) ^ 2
            ∂(volume : Measure (Vec3 × ℝ)) := by
      apply setIntegral_congr_ae (hΩ.prod hI).measurableSet
      filter_upwards [] with z hz
      rw [parabolicHomeomorph_symm_apply]
      simp [ρ, halfSpaceDensity, halfSpacePhaseProduct, halfSpacePhase,
        productFieldToParabolic, timePartial, spatialSecondPartial, spatialPartial]
    calc
      _ = _ := hleft
      _ ≤ c * _ := hsmooth
      _ = _ := by rw [← hright]
  have hρcont : ContinuousOn ρ ({x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1) := by
    let U : Set (Vec3 × ℝ) := {x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1
    have hphase : ContinuousOn (halfSpacePhaseProduct a α) U := by
      change ContinuousOn (fun z : Vec3 × ℝ =>
        -(z.1 0 ^ 2 + z.1 1 ^ 2) / (8 * z.2) +
          a * (1 - z.2) * z.1 2 ^ (2 * α) / z.2 ^ α) U
      have htime : ContinuousOn (fun z : Vec3 × ℝ => z.2) U := by fun_prop
      have hx : ContinuousOn (fun z : Vec3 × ℝ => z.1 2) U := by fun_prop
      have hxpos (z : Vec3 × ℝ) (hz : z ∈ U) : 0 < z.1 2 :=
        lt_trans (by norm_num) hz.1
      have htpos (z : Vec3 × ℝ) (hz : z ∈ U) : 0 < z.2 := hz.2.1
      have hxpow : ContinuousOn (fun z : Vec3 × ℝ => z.1 2 ^ (2 * α)) U :=
        hx.rpow_const fun z hz => Or.inl (ne_of_gt (hxpos z hz))
      have htpow : ContinuousOn (fun z : Vec3 × ℝ => z.2 ^ α) U :=
        htime.rpow_const fun z hz => Or.inl (ne_of_gt (htpos z hz))
      have hfirstNum : ContinuousOn
          (fun z : Vec3 × ℝ => -(z.1 0 ^ 2 + z.1 1 ^ 2)) U := by fun_prop
      have hfirstDen : ContinuousOn (fun z : Vec3 × ℝ => 8 * z.2) U := by fun_prop
      have hfirstDenNe : ∀ z ∈ U, 8 * z.2 ≠ 0 := by
        intro z hz
        exact ne_of_gt (mul_pos (by norm_num) (htpos z hz))
      have hfirst := hfirstNum.div hfirstDen hfirstDenNe
      have hsecondNum : ContinuousOn
          (fun z : Vec3 × ℝ => a * (1 - z.2) * z.1 2 ^ (2 * α)) U := by
        have hconst : ContinuousOn (fun _ : Vec3 × ℝ => a) U := continuousOn_const
        have hone : ContinuousOn (fun _ : Vec3 × ℝ => (1 : ℝ)) U := continuousOn_const
        have hproduct := hconst.mul ((hone.sub htime).mul hxpow)
        refine hproduct.congr ?_
        intro z hz
        simp [mul_assoc]
      have hsecondDenNe : ∀ z ∈ U, z.2 ^ α ≠ 0 := by
        intro z hz
        exact ne_of_gt (Real.rpow_pos_of_pos (htpos z hz) α)
      exact hfirst.add (hsecondNum.div htpow hsecondDenNe)
    have htime : ContinuousOn (fun z : Vec3 × ℝ => z.2) U := by fun_prop
    have htimeSq := htime.pow 2
    have hexp : ContinuousOn
        (fun z : Vec3 × ℝ => Real.exp (2 * halfSpacePhaseProduct a α z)) U :=
      Real.continuous_exp.continuousOn.comp (continuousOn_const.mul hphase) (by
        intro z hz
        exact Set.mem_univ _)
    change ContinuousOn (fun z => z.2 ^ 2 * Real.exp (2 * halfSpacePhaseProduct a α z)) U
    exact htimeSq.mul hexp
  have hσcont : ContinuousOn σ ({x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1) := by
    let U : Set (Vec3 × ℝ) := {x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1
    have htime : ContinuousOn (fun z : Vec3 × ℝ => z.2 ^ 2) U := by fun_prop
    have htimeNe : ∀ z ∈ U, z.2 ^ 2 ≠ 0 := by
      intro z hz
      exact pow_ne_zero _ (ne_of_gt hz.2.1)
    have hfactor : ContinuousOn (fun z : Vec3 × ℝ => a / z.2 ^ 2) U :=
      continuousOn_const.div htime htimeNe
    exact hρcont.mul hfactor
  have hτcont : ContinuousOn τ ({x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1) := by
    let U : Set (Vec3 × ℝ) := {x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1
    have htime : ContinuousOn (fun z : Vec3 × ℝ => z.2) U := by fun_prop
    have htimeNe : ∀ z ∈ U, z.2 ≠ 0 := by
      intro z hz
      exact ne_of_gt hz.2.1
    have hfactor : ContinuousOn (fun z : Vec3 × ℝ => z.2⁻¹) U :=
      htime.inv₀ (by
        intro z hz
        exact ne_of_gt hz.2.1)
    have hmul := hρcont.mul hfactor
    have hgradEq : halfSpaceGradientWeight a α =
        halfSpaceDensity a α * (fun z : Vec3 × ℝ => z.2⁻¹) := by
      funext z
      simp [halfSpaceGradientWeight, div_eq_mul_inv]
    change ContinuousOn (halfSpaceGradientWeight a α)
      ({x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1)
    rw [hgradEq]
    exact hmul
  have hweak := compactlySupportedSpaceTimeCarleman_of_smooth
    (hΩ := hΩ) (hI := hI) hderiv hcompact htsupport hL2
    hρcont hσcont hτcont hSmoothProduct
  simp only [setIntegral_parabolic_to_product]
  have hleft :
      (∫ z in {x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1,
        (parabolicHomeomorph.symm z).2 ^ 2 *
          Real.exp (2 * halfSpacePhase a α (parabolicHomeomorph.symm z)) *
          (a * vec3EuclideanNorm (w (parabolicHomeomorph.symm z)) ^ 2 /
            (parabolicHomeomorph.symm z).2 ^ 2 +
            spatialGradientSq w Dw (parabolicHomeomorph.symm z) /
              (parabolicHomeomorph.symm z).2)
        ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ z in {x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1,
        σ z * vec3EuclideanNorm (w (parabolicHomeomorph.symm z)) ^ 2 +
          τ z * ∑ i, ∑ j, Dw (parabolicHomeomorph.symm z) i j ^ 2
        ∂(volume : Measure (Vec3 × ℝ)) := by
    apply setIntegral_congr_ae (hΩ.prod hI).measurableSet
    filter_upwards [] with z hz
    rw [parabolicHomeomorph_symm_apply]
    simp [σ, τ, halfSpaceMassWeight, halfSpaceGradientWeight,
      halfSpaceDensity, halfSpacePhaseProduct, halfSpacePhase,
      spatialGradientSq, vec3EuclideanNorm_sq]
    ring
  have hright :
      (∫ z in {x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1,
        ρ z * vec3EuclideanNorm (fun i =>
          Dtw (parabolicHomeomorph.symm z) i +
            ∑ j, D2w (parabolicHomeomorph.symm z) i j j) ^ 2
        ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ z in {x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1,
        (parabolicHomeomorph.symm z).2 ^ 2 *
          Real.exp (2 * halfSpacePhase a α (parabolicHomeomorph.symm z)) *
          vec3EuclideanNorm (fun i => Dtw (parabolicHomeomorph.symm z) i +
            ∑ j, D2w (parabolicHomeomorph.symm z) i j j) ^ 2
        ∂(volume : Measure (Vec3 × ℝ)) := by
    apply setIntegral_congr_ae (hΩ.prod hI).measurableSet
    filter_upwards [] with z hz
    rw [parabolicHomeomorph_symm_apply]
    simp [ρ, halfSpaceDensity, halfSpacePhaseProduct, halfSpacePhase]
  calc
    _ = ∫ z in {x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1,
          σ z * vec3EuclideanNorm (w (parabolicHomeomorph.symm z)) ^ 2 +
            τ z * ∑ i, ∑ j, Dw (parabolicHomeomorph.symm z) i j ^ 2
          ∂(volume : Measure (Vec3 × ℝ)) := hleft
    _ ≤ c * ∫ z in {x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1,
          ρ z * vec3EuclideanNorm (fun i => Dtw (parabolicHomeomorph.symm z) i +
            ∑ j, D2w (parabolicHomeomorph.symm z) i j j) ^ 2
          ∂(volume : Measure (Vec3 × ℝ)) := hweak
    _ = _ := by rw [hright]

end ESS
