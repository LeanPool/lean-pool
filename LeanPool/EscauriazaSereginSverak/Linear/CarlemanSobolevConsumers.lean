/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanSobolevPass
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanCoreProduct
public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanGaussExplicit
public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanHalfWeightsDerivatives
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanSobolevSupport
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradientSq

/-!
# Gaussian and half-space Sobolev Carleman estimates

The Gaussian smooth estimate is supplied by `prop:carleman-gauss`; the half-space estimate is
left as a smooth hypothesis so it can be connected to `prop:carleman-halfspace`.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal Pointwise
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The Gaussian Carleman density at parameter `a` and space-time point `z`. -/
@[expose] def gaussianDensity (a : ℝ) (z : Vec3 × ℝ) : ℝ :=
  gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
    Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))

/-- The Gaussian density multiplied by the time mass factor `a / z.2`. -/
@[expose] def gaussianMassWeight (a : ℝ) (z : Vec3 × ℝ) : ℝ :=
  gaussianDensity a z * (a / z.2)

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

section GaussianMeasureBridge

/-- The explicit Gaussian measure-space structure used for parabolic integral conversion. -/
local instance gaussianMeasureSpace : MeasureSpace ParabolicPoint :=
  ESS.gaussExplicitMeasureSpace

private theorem setIntegral_parabolic_to_product_gaussian
    {Ω : Set Vec3} {I : Set ℝ} {F : ParabolicPoint → ℝ} :
    (∫ (p : ParabolicPoint) in spaceTimeSet Ω I, F p
      ∂(volume : Measure ParabolicPoint)) =
    ∫ q in Ω ×ˢ I, F (parabolicHomeomorph.symm q)
      ∂(volume : Measure (Vec3 × ℝ)) := by
  have hpres : MeasurePreserving parabolicHomeomorph
      (volume : Measure ParabolicPoint) (volume : Measure (Vec3 × ℝ)) := by
    constructor
    · exact parabolicHomeomorph.measurable
    · change Measure.map (id : Vec3 × ℝ → Vec3 × ℝ)
        (Measure.prod (volume : Measure Vec3) (volume : Measure ℝ)) = _
      exact Measure.map_id
  have himage : parabolicHomeomorph '' spaceTimeSet Ω I = Ω ×ˢ I := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp
    · intro hq
      exact ⟨parabolicHomeomorph.symm q, hq,
        parabolicHomeomorph.apply_symm_apply q⟩
  have htrans := hpres.setIntegral_image_emb
    parabolicHomeomorph.measurableEmbedding
    (fun q : Vec3 × ℝ => F (parabolicHomeomorph.symm q)) (spaceTimeSet Ω I)
  rw [himage] at htrans
  have hright :
      (∫ (p : ParabolicPoint) in spaceTimeSet Ω I,
        F (parabolicHomeomorph.symm (parabolicHomeomorph p))
        ∂(volume : Measure ParabolicPoint)) =
      ∫ (p : ParabolicPoint) in spaceTimeSet Ω I, F p
        ∂(volume : Measure ParabolicPoint) := by
    apply integral_congr_ae
    filter_upwards [] with p
    exact congrArg F (parabolicHomeomorph.left_inv p)
  exact hright.symm.trans htrans.symm

end GaussianMeasureBridge

private theorem gaussianDensity_continuousOn (a : ℝ) :
    ContinuousOn (gaussianDensity a)
      (univ ×ˢ Ioo (0 : ℝ) 2) := by
  let U : Set (Vec3 × ℝ) := univ ×ˢ Ioo (0 : ℝ) 2
  have htime : Continuous (fun z : Vec3 × ℝ => gaussCarlemanTimeWeight z.2) := by
    unfold gaussCarlemanTimeWeight
    fun_prop
  have htimePos (z : Vec3 × ℝ) (hz : z ∈ U) :
      0 < gaussCarlemanTimeWeight z.2 := by
    exact mul_pos hz.2.1 (Real.exp_pos _)
  have hpower : ContinuousOn
      (fun z : Vec3 × ℝ => gaussCarlemanTimeWeight z.2 ^ (-2 * a)) U :=
    htime.continuousOn.rpow_const fun z hz => Or.inl (ne_of_gt (htimePos z hz))
  have hdenom : ContinuousOn (fun z : Vec3 × ℝ => 4 * z.2) U := by fun_prop
  have hdenomNe : ∀ z ∈ U, 4 * z.2 ≠ 0 := by
    intro z hz
    exact ne_of_gt (mul_pos (by norm_num) hz.2.1)
  have hnum : ContinuousOn
      (fun z : Vec3 × ℝ => -(vec3EuclideanNorm z.1 ^ 2)) U := by
    have hsum : ContinuousOn
        (fun z : Vec3 × ℝ => ∑ i : Fin 3, z.1 i ^ 2) U := by fun_prop
    have hnum' := hsum.neg
    refine hnum'.congr ?_
    intro z hz
    change -(vec3EuclideanNorm z.1 ^ 2) = -(∑ i : Fin 3, z.1 i ^ 2)
    rw [vec3EuclideanNorm_sq]
  have harg := hnum.div hdenom hdenomNe
  have hexp : ContinuousOn
      (fun z : Vec3 × ℝ => Real.exp
        (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) U :=
    Real.continuous_exp.continuousOn.comp harg (by
      intro z hz
      exact Set.mem_univ _)
  change ContinuousOn
    (fun z => gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
      Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) U
  exact hpower.mul hexp

private theorem gaussianMassWeight_continuousOn (a : ℝ) :
    ContinuousOn (gaussianMassWeight a)
      (univ ×ˢ Ioo (0 : ℝ) 2) := by
  have htime : ContinuousOn (fun z : Vec3 × ℝ => z.2)
      (univ ×ˢ Ioo (0 : ℝ) 2) := by fun_prop
  have htimeNe : ∀ z : Vec3 × ℝ, z ∈ univ ×ˢ Ioo (0 : ℝ) 2 → z.2 ≠ 0 := by
    intro z hz
    exact ne_of_gt hz.2.1
  have hfactor : ContinuousOn (fun z : Vec3 × ℝ => a / z.2)
      (univ ×ˢ Ioo (0 : ℝ) 2) := continuousOn_const.div htime htimeNe
  exact (gaussianDensity_continuousOn a).mul hfactor

private theorem halfSpaceDensity_continuousOn (a α : ℝ) :
    ContinuousOn (halfSpaceDensity a α)
      ({x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1) := by
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

private theorem halfSpaceMassWeight_continuousOn (a α : ℝ) :
    ContinuousOn (halfSpaceMassWeight a α)
      ({x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1) := by
  let U : Set (Vec3 × ℝ) := {x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1
  have htime : ContinuousOn (fun z : Vec3 × ℝ => z.2 ^ 2) U := by fun_prop
  have htimeNe : ∀ z ∈ U, z.2 ^ 2 ≠ 0 := by
    intro z hz
    exact pow_ne_zero _ (ne_of_gt hz.2.1)
  have hfactor : ContinuousOn (fun z : Vec3 × ℝ => a / z.2 ^ 2) U :=
    continuousOn_const.div htime htimeNe
  exact (halfSpaceDensity_continuousOn a α).mul hfactor

private theorem halfSpaceGradientWeight_continuousOn (a α : ℝ) :
    ContinuousOn (halfSpaceGradientWeight a α)
      ({x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1) := by
  let U : Set (Vec3 × ℝ) := {x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1
  have htime : ContinuousOn (fun z : Vec3 × ℝ => z.2) U := by fun_prop
  have htimeNe : ∀ z ∈ U, z.2 ≠ 0 := by
    intro z hz
    exact ne_of_gt hz.2.1
  have hfactor : ContinuousOn (fun z : Vec3 × ℝ => z.2⁻¹) U :=
    htime.inv₀ (by
      intro z hz
      exact ne_of_gt hz.2.1)
  have hmul := (halfSpaceDensity_continuousOn a α).mul hfactor
  have hgradEq : halfSpaceGradientWeight a α =
      halfSpaceDensity a α * (fun z : Vec3 × ℝ => z.2⁻¹) := by
    funext z
    simp [halfSpaceGradientWeight, div_eq_mul_inv]
  rw [hgradEq]
  exact hmul

/-- The Gaussian Carleman inequality with its explicit constant extends to compactly
supported space-time weak fields (`lem:carleman-sobolev`). -/
theorem bu_carleman_sobolev_gaussian
    (w : ParabolicPoint → Vec3) (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3) (Dtw : ParabolicPoint → Vec3)
    (hderiv : HasSpaceTimeWeakDerivs univ (Ioo 0 2) w Dw D2w Dtw)
    (hcompact : HasCompactSupport w)
    (htsupport : tsupport w ⊆ spaceTimeSet univ (Ioo 0 2))
    (hL2 : (∫⁻ z in spaceTimeSet univ (Ioo 0 2),
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) :
    ∀ a : ℝ, 0 < a →
      ∫ z in spaceTimeSet univ (Ioo 0 2),
        (gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
          Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
          (a / z.2 * vec3EuclideanNorm (w z) ^ 2 + spatialGradientSq w Dw z) ≤
      (Real.exp (4 / 3) * (9 + 2 * Real.sqrt 6)) *
        ∫ z in spaceTimeSet univ (Ioo 0 2),
          (gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
            Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
            vec3EuclideanNorm (fun i => Dtw z i + ∑ j, D2w z i j j) ^ 2 := by
  intro a ha
  have hUopen : IsOpen (univ : Set Vec3) ∧ IsOpen (Ioo (0 : ℝ) 2) :=
    ⟨isOpen_univ, isOpen_Ioo⟩
  let ρ : Vec3 × ℝ → ℝ := gaussianDensity a
  let σ : Vec3 × ℝ → ℝ := gaussianMassWeight a
  let τ : Vec3 × ℝ → ℝ := gaussianDensity a
  have hSmooth : ∀ v : Vec3 × ℝ → Vec3,
      v ∈ spaceTimeTestFunction (V := Vec3) univ (Ioo 0 2) →
      (∫ z in univ ×ˢ Ioo (0 : ℝ) 2,
        σ z * vec3EuclideanNorm (v z) ^ 2 +
          τ z * spatialGradientSq v (spatialGradient v) z
          ∂(volume : Measure (Vec3 × ℝ))) ≤
        (Real.exp (4 / 3) * (9 + 2 * Real.sqrt 6)) *
          (∫ z in univ ×ˢ Ioo (0 : ℝ) 2,
            ρ z * vec3EuclideanNorm (fun i =>
              timePartial (fun y => v y i) z +
                ∑ j, spatialSecondPartial (fun y => v y i) j j z) ^ 2
              ∂(volume : Measure (Vec3 × ℝ))) := by
    intro v hv
    have htest : productFieldToParabolic v ∈
        spaceTimeTestFunction (V := Vec3) univ (Ioo 0 2) := by
      change (fun z : Vec3 × ℝ => v (z.1, z.2)) ∈
        spaceTimeTestFunction (V := Vec3) univ (Ioo 0 2)
      simpa using hv
    have h := carlemanGaussian_explicit a ha (productFieldToParabolic v) htest
    rw [setIntegral_parabolic_to_product_gaussian] at h
    rw [setIntegral_parabolic_to_product_gaussian] at h
    have hleft :
        (∫ z in univ ×ˢ Ioo (0 : ℝ) 2,
          σ z * vec3EuclideanNorm (v z) ^ 2 +
            τ z * spatialGradientSq v (spatialGradient v) z
            ∂(volume : Measure (Vec3 × ℝ))) =
          ∫ z in univ ×ˢ Ioo (0 : ℝ) 2,
            gaussCarlemanTimeWeight (parabolicHomeomorph.symm z).2 ^ (-2 * a) *
              Real.exp (-(vec3EuclideanNorm (parabolicHomeomorph.symm z).1 ^ 2) /
                (4 * (parabolicHomeomorph.symm z).2)) *
              (a / (parabolicHomeomorph.symm z).2 *
                vec3EuclideanNorm (productFieldToParabolic v
                  (parabolicHomeomorph.symm z)) ^ 2 +
                spatialGradientSq (productFieldToParabolic v)
                  (spatialGradient (productFieldToParabolic v))
                  (parabolicHomeomorph.symm z))
            ∂(volume : Measure (Vec3 × ℝ)) := by
      apply setIntegral_congr_ae (isOpen_univ.prod isOpen_Ioo).measurableSet
      filter_upwards [] with z hz
      rw [parabolicHomeomorph_symm_apply]
      simp [σ, τ, gaussianMassWeight, gaussianDensity, productFieldToParabolic,
        spatialGradientSq, spatialGradient, spatialPartial]
      ring
    have hright :
        (∫ z in univ ×ˢ Ioo (0 : ℝ) 2,
          ρ z * vec3EuclideanNorm (fun i =>
            timePartial (fun y => v y i) z +
              ∑ j, spatialSecondPartial (fun y => v y i) j j z) ^ 2
            ∂(volume : Measure (Vec3 × ℝ))) =
          ∫ z in univ ×ˢ Ioo (0 : ℝ) 2,
            ((parabolicHomeomorph.symm z).2 *
              Real.exp ((1 - (parabolicHomeomorph.symm z).2) / 3)) ^ (-2 * a) *
              Real.exp (-(vec3EuclideanNorm (parabolicHomeomorph.symm z).1 ^ 2) /
                (4 * (parabolicHomeomorph.symm z).2)) *
              vec3EuclideanNorm (fun i =>
                timePartial (fun y => productFieldToParabolic v y i)
                  (parabolicHomeomorph.symm z) +
                  ∑ j, spatialSecondPartial (fun y => productFieldToParabolic v y i) j j
                    (parabolicHomeomorph.symm z)) ^ 2
            ∂(volume : Measure (Vec3 × ℝ)) := by
      apply setIntegral_congr_ae (isOpen_univ.prod isOpen_Ioo).measurableSet
      filter_upwards [] with z hz
      rw [parabolicHomeomorph_symm_apply]
      simp only [ρ, gaussianDensity, productFieldToParabolic,
        timePartial, spatialSecondPartial, spatialPartial, neg_mul]
      rw [gaussCarlemanTimeWeight]
    calc
      _ = _ := hleft
      _ ≤ _ := h
      _ = _ := by rw [← hright]
  have hρcont : ContinuousOn ρ (univ ×ˢ Ioo (0 : ℝ) 2) := by
    exact gaussianDensity_continuousOn a
  have hσcont : ContinuousOn σ (univ ×ˢ Ioo (0 : ℝ) 2) := by
    exact gaussianMassWeight_continuousOn a
  have hτcont : ContinuousOn τ (univ ×ˢ Ioo (0 : ℝ) 2) := by
    exact gaussianDensity_continuousOn a
  have hweak := compactlySupportedSpaceTimeCarleman_of_smooth
    (hΩ := hUopen.1) (hI := hUopen.2) hderiv hcompact htsupport hL2
    hρcont hσcont hτcont hSmooth
  simp only [setIntegral_parabolic_to_product]
  have hleft :
      (∫ z in univ ×ˢ Ioo (0 : ℝ) 2,
        (gaussCarlemanTimeWeight (parabolicHomeomorph.symm z).2 ^ (-2 * a) *
          Real.exp (-(vec3EuclideanNorm (parabolicHomeomorph.symm z).1 ^ 2) /
            (4 * (parabolicHomeomorph.symm z).2))) *
          (a / (parabolicHomeomorph.symm z).2 *
            vec3EuclideanNorm (w (parabolicHomeomorph.symm z)) ^ 2 +
            spatialGradientSq w Dw (parabolicHomeomorph.symm z))
        ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ z in univ ×ˢ Ioo (0 : ℝ) 2,
        σ z * vec3EuclideanNorm (w (parabolicHomeomorph.symm z)) ^ 2 +
          τ z * ∑ i, ∑ j, Dw (parabolicHomeomorph.symm z) i j ^ 2
        ∂(volume : Measure (Vec3 × ℝ)) := by
    apply setIntegral_congr_ae (isOpen_univ.prod isOpen_Ioo).measurableSet
    filter_upwards [] with z hz
    rw [parabolicHomeomorph_symm_apply]
    simp [σ, τ, gaussianMassWeight, gaussianDensity, spatialGradientSq,
      vec3EuclideanNorm_sq]
    ring
  have hright :
      (∫ z in univ ×ˢ Ioo (0 : ℝ) 2,
        ρ z * vec3EuclideanNorm (fun i =>
          Dtw (parabolicHomeomorph.symm z) i +
            ∑ j, D2w (parabolicHomeomorph.symm z) i j j) ^ 2
        ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ z in univ ×ˢ Ioo (0 : ℝ) 2,
        (gaussCarlemanTimeWeight (parabolicHomeomorph.symm z).2 ^ (-2 * a) *
          Real.exp (-(vec3EuclideanNorm (parabolicHomeomorph.symm z).1 ^ 2) /
            (4 * (parabolicHomeomorph.symm z).2))) *
          vec3EuclideanNorm (fun i => Dtw (parabolicHomeomorph.symm z) i +
            ∑ j, D2w (parabolicHomeomorph.symm z) i j j) ^ 2
        ∂(volume : Measure (Vec3 × ℝ)) := by
    apply setIntegral_congr_ae (isOpen_univ.prod isOpen_Ioo).measurableSet
    filter_upwards [] with z hz
    rw [parabolicHomeomorph_symm_apply]
    simp [ρ, gaussianDensity]
  calc
    _ = ∫ z in univ ×ˢ Ioo (0 : ℝ) 2,
          σ z * vec3EuclideanNorm (w (parabolicHomeomorph.symm z)) ^ 2 +
            τ z * ∑ i, ∑ j, Dw (parabolicHomeomorph.symm z) i j ^ 2
          ∂(volume : Measure (Vec3 × ℝ)) := hleft
    _ ≤ Real.exp (4 / 3) * (9 + 2 * Real.sqrt 6) *
        ∫ z in univ ×ˢ Ioo (0 : ℝ) 2,
          ρ z * vec3EuclideanNorm (fun i => Dtw (parabolicHomeomorph.symm z) i +
            ∑ j, D2w (parabolicHomeomorph.symm z) i j j) ^ 2
          ∂(volume : Measure (Vec3 × ℝ)) := hweak
    _ = _ := by rw [hright]

/-- The half-space density passage preserves any smooth weighted Carleman estimate supplied for
the stated domain (`lem:carleman-sobolev`). -/
theorem bu_carleman_sobolev_halfspace
    (α : ℝ)
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
    (hSmooth : ∃ a₀ c : ℝ, 0 < a₀ ∧ 0 < c ∧
      ∀ a : ℝ, a₀ < a → ∀ v : ParabolicPoint → Vec3,
        v ∈ spaceTimeTestFunction (V := Vec3) {x : Vec3 | 1 < x 2} (Ioo 0 1) →
        (∫ z in spaceTimeSet {x : Vec3 | 1 < x 2} (Ioo 0 1),
          z.2 ^ 2 * Real.exp (2 * halfSpacePhase a α z) *
            (a * vec3EuclideanNorm (v z) ^ 2 / z.2 ^ 2 +
              spatialGradientSq v (spatialGradient v) z / z.2)) ≤
        c * (∫ z in spaceTimeSet {x : Vec3 | 1 < x 2} (Ioo 0 1),
          z.2 ^ 2 * Real.exp (2 * halfSpacePhase a α z) *
            vec3EuclideanNorm (fun i => timePartial (fun y => v y i) z +
              ∑ j, spatialSecondPartial (fun y => v y i) j j z) ^ 2)) :
    ∃ a₀ c : ℝ, 0 < a₀ ∧ 0 < c ∧ ∀ a : ℝ, a₀ < a →
      ∫ z in spaceTimeSet {x : Vec3 | 1 < x 2} (Ioo 0 1),
        z.2 ^ 2 * Real.exp (2 * halfSpacePhase a α z) *
          (a * vec3EuclideanNorm (w z) ^ 2 / z.2 ^ 2 +
            spatialGradientSq w Dw z / z.2) ≤
      c * ∫ z in spaceTimeSet {x : Vec3 | 1 < x 2} (Ioo 0 1),
        z.2 ^ 2 * Real.exp (2 * halfSpacePhase a α z) *
          vec3EuclideanNorm (fun i => Dtw z i + ∑ j, D2w z i j j) ^ 2 := by
  obtain ⟨a₀, c, ha₀, hc, hSmooth⟩ := hSmooth
  refine ⟨a₀, c, ha₀, hc, ?_⟩
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
  have hρcont : ContinuousOn ρ ({x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1) :=
    halfSpaceDensity_continuousOn a α
  have hσcont : ContinuousOn σ ({x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1) :=
    halfSpaceMassWeight_continuousOn a α
  have hτcont : ContinuousOn τ ({x : Vec3 | 1 < x 2} ×ˢ Ioo (0 : ℝ) 1) :=
    halfSpaceGradientWeight_continuousOn a α
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
