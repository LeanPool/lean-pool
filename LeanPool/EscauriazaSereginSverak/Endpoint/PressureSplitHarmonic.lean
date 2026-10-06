/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.LocalEnergyWeakGradient
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Equation
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SpatialDerivSupport
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.DivergenceFreeIntegrand

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-! The source cylinder for the fixed pressure decomposition in
`lem:pressure-split`. -/

/-- The unit spatial ball used in the fixed pressure decomposition. -/
@[expose] def pressureSplitBall : Set Vec3 := vec3Ball (0 : Vec3) 1

/-- The source time interval used in the fixed pressure decomposition. -/
@[expose] def pressureSplitTime : Set ℝ := Ioo (-1 : ℝ) 0

/-- The parabolic source cylinder for the fixed pressure decomposition. -/
@[expose] def pressureSplitDomain : Set ParabolicPoint :=
  spaceTimeSet pressureSplitBall pressureSplitTime

/-- The product-coordinate source cylinder for the fixed pressure
decomposition. -/
@[expose] def pressureSplitProductDomain : Set (Vec3 × ℝ) :=
  pressureSplitBall ×ˢ pressureSplitTime

private theorem pressureSplit_productTest
    {Ω : Set Vec3} {I : Set ℝ} {ψ : Vec3 → ℝ} {θ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψΩ : tsupport ψ ⊆ Ω) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθc : HasCompactSupport θ) (hθI : tsupport θ ⊆ I) :
    (fun z : Vec3 × ℝ => ψ z.1 * θ z.2) ∈
      spaceTimeTestFunction (V := ℝ) Ω I := by
  let f : Vec3 × ℝ → ℝ := fun z => ψ z.1 * θ z.2
  have hsupport : tsupport f ⊆ tsupport ψ ×ˢ tsupport θ := by
    apply closure_minimal
    · intro z hz
      change f z ≠ 0 at hz
      by_contra hnot
      simp only [Set.mem_prod, not_and_or] at hnot
      rcases hnot with hψz | hθz
      · apply hz
        simp [f, image_eq_zero_of_notMem_tsupport hψz]
      · apply hz
        simp [f, image_eq_zero_of_notMem_tsupport hθz]
    exact IsClosed.prod (isClosed_tsupport ψ) (isClosed_tsupport θ)
  refine ⟨(hψ.comp (ContinuousLinearMap.fst ℝ Vec3 ℝ).contDiff).mul
      (hθ.comp (ContinuousLinearMap.snd ℝ Vec3 ℝ).contDiff), ?_, ?_⟩
  · exact (hψc.isCompact.prod hθc.isCompact).of_isClosed_subset
      (isClosed_tsupport f) hsupport
  · exact hsupport.trans (Set.prod_mono hψΩ hθI)

private theorem pressureSplit_productPartial_formula
    {η : Vec3 → ℝ} {θ : ℝ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (i : Fin 3) (z : ParabolicPoint) :
    spatialPartial (fun q : ParabolicPoint => η q.1 * θ q.2) i z =
      θ z.2 * spatialDeriv η i z.1 := by
  unfold spatialPartial spatialDeriv
  have hdiff : DifferentiableAt ℝ η z.1 := hη.differentiable (by norm_num) z.1
  change (fderiv ℝ (fun x : Vec3 => η x * θ z.2) z.1) (basisVec i) = _
  rw [fderiv_mul_const hdiff (θ z.2)]
  simp only [_root_.smul_apply, smul_eq_mul]

private theorem pressureSplit_productPartial_formula_prod
    {η : Vec3 → ℝ} {θ : ℝ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (i : Fin 3) (z : Vec3 × ℝ) :
    spatialPartial (fun q : Vec3 × ℝ => η q.1 * θ q.2) i z =
      θ z.2 * spatialDeriv η i z.1 := by
  change spatialPartial (fun q : ParabolicPoint => η q.1 * θ q.2) i
    (parabolicHomeomorph.symm z) = _
  exact pressureSplit_productPartial_formula hη i
    (parabolicHomeomorph.symm z)

private theorem pressureSplitProductDomain_finite :
    IsFiniteMeasure ((volume : Measure (Vec3 × ℝ)).restrict
      pressureSplitProductDomain) := by
  have hB : IsCompact (closure pressureSplitBall) := by
    simpa [pressureSplitBall] using (isCompact_closure_vec3Ball
      (x := (0 : Vec3)) (r := (1 : ℝ)) (by norm_num))
  have hK : IsCompact
      (closure pressureSplitBall ×ˢ Set.Icc (-1 : ℝ) 0) :=
    hB.prod isCompact_Icc
  have hsub : pressureSplitProductDomain ⊆
      closure pressureSplitBall ×ˢ Set.Icc (-1 : ℝ) 0 := by
    intro z hz
    exact ⟨subset_closure hz.1,
      ⟨le_of_lt hz.2.1, le_of_lt hz.2.2⟩⟩
  have hfinite : (volume : Measure (Vec3 × ℝ))
      pressureSplitProductDomain < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub) hK.measure_lt_top
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact hfinite

private theorem pressureSplit_productMemLpTwo
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hu : AEStronglyMeasurable u (volume.restrict pressureSplitDomain))
    (hDu : AEStronglyMeasurable Du (volume.restrict pressureSplitDomain))
    (henergy : (∫⁻ z in pressureSplitDomain,
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤) :
    MemLp (fun z : Vec3 × ℝ => u z) 2
        ((volume : Measure (Vec3 × ℝ)).restrict pressureSplitProductDomain) ∧
      MemLp (fun z : Vec3 × ℝ => Du z) 2
        ((volume : Measure (Vec3 × ℝ)).restrict pressureSplitProductDomain) := by
  have hparaMeas : MeasurableSet pressureSplitDomain := by
    exact (isOpen_spaceTimeSet pressureSplitBall pressureSplitTime
      (isOpen_vec3Ball (0 : Vec3) 1) isOpen_Ioo).measurableSet
  have hpre : parabolicHomeomorph.symm ⁻¹' pressureSplitDomain =
      pressureSplitProductDomain := by
    ext z
    rfl
  have hmp := parabolicHomeomorphSymm_measurePreserving.restrict_preimage hparaMeas
  rw [hpre] at hmp
  rcases energyL2_components_memLp hu hDu henergy with ⟨hu2, hDu2⟩
  have huProd : MemLp (fun z : Vec3 × ℝ => u z) 2
      ((volume : Measure (Vec3 × ℝ)).restrict pressureSplitProductDomain) := by
    have h := hu2.comp_measurePreserving hmp
    change MemLp (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z)) 2 _ at h
    have heq : (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z)) =
        (fun z => u z) := by
      funext z
      cases z
      rfl
    rw [heq] at h
    exact h
  have hDuProd : MemLp (fun z : Vec3 × ℝ => Du z) 2
      ((volume : Measure (Vec3 × ℝ)).restrict pressureSplitProductDomain) := by
    have h := hDu2.comp_measurePreserving hmp
    change MemLp (fun z : Vec3 × ℝ => Du (parabolicHomeomorph.symm z)) 2 _ at h
    have heq : (fun z : Vec3 × ℝ => Du (parabolicHomeomorph.symm z)) =
        (fun z => Du z) := by
      funext z
      cases z
      rfl
    rw [heq] at h
    exact h
  exact ⟨huProd, hDuProd⟩

private theorem pressureSplit_divergence_integral_product
    {u : ParabolicPoint → Vec3}
    (hdiv : ∀ χ : Vec3 × ℝ → ℝ,
      χ ∈ spaceTimeTestFunction (V := ℝ) pressureSplitBall pressureSplitTime →
      ∫ z in pressureSplitDomain,
        ∑ i : Fin 3, u z i * spatialPartial χ i z = 0)
    {χ : Vec3 × ℝ → ℝ}
    (hχ : χ ∈ spaceTimeTestFunction (V := ℝ)
      pressureSplitBall pressureSplitTime) :
    ∫ z in pressureSplitProductDomain,
      ∑ i : Fin 3, u z i * spatialPartial χ i z = 0 := by
  let g : ParabolicPoint → ℝ := fun z =>
    ∑ i : Fin 3, u z i * spatialPartial χ i z
  have h0 : (∫ z in spaceTimeSet pressureSplitBall pressureSplitTime, g z) = 0 := by
    simpa only [pressureSplitDomain, g] using hdiv χ hχ
  have hconvert := setIntegral_parabolic_to_product
    (Ω := pressureSplitBall) (I := pressureSplitTime) (F := g)
  calc
    _ = ∫ z in pressureSplitProductDomain, g (parabolicHomeomorph.symm z) := by
      apply integral_congr_ae
      filter_upwards [] with z
      cases z
      rfl
    _ = ∫ z in spaceTimeSet pressureSplitBall pressureSplitTime, g z := hconvert.symm
    _ = 0 := h0

private theorem pressureSplit_product_factor_integrable
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (henergy : (∫⁻ z in pressureSplitDomain,
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hu : AEStronglyMeasurable u (volume.restrict pressureSplitDomain))
    (hDu : AEStronglyMeasurable Du (volume.restrict pressureSplitDomain))
    {χ : Vec3 × ℝ → ℝ}
    (hχ : χ ∈ spaceTimeTestFunction (V := ℝ)
      pressureSplitBall pressureSplitTime) (i j : Fin 3) :
    IntegrableOn (fun z : Vec3 × ℝ => u z i * spatialPartial χ j z)
        pressureSplitProductDomain (volume : Measure (Vec3 × ℝ)) ∧
      IntegrableOn (fun z : Vec3 × ℝ => Du z i j * χ z)
        pressureSplitProductDomain (volume : Measure (Vec3 × ℝ)) := by
  let : IsFiniteMeasure ((volume : Measure (Vec3 × ℝ)).restrict
      pressureSplitProductDomain) := pressureSplitProductDomain_finite
  rcases pressureSplit_productMemLpTwo hu hDu henergy with ⟨hu2, hDu2⟩
  have hu_i : Integrable (fun z : Vec3 × ℝ => u z i)
      ((volume : Measure (Vec3 × ℝ)).restrict pressureSplitProductDomain) :=
    ((memLp_pi_iff.mp hu2) i).integrable (by norm_num)
  have hDu_ij : Integrable (fun z : Vec3 × ℝ => Du z i j)
      ((volume : Measure (Vec3 × ℝ)).restrict pressureSplitProductDomain) :=
    (((memLp_pi_iff.mp hDu2) i |> memLp_pi_iff.mp) j).integrable (by norm_num)
  obtain ⟨C, hC⟩ := exists_bound_spatialPartial_of_mem_spaceTimeTestFunction hχ j
  have hpartialMeas : AEStronglyMeasurable
      (fun z : Vec3 × ℝ => spatialPartial χ j z)
      ((volume : Measure (Vec3 × ℝ)).restrict pressureSplitProductDomain) :=
    (spatialPartial_contDiff hχ.1 j).continuous.measurable.aestronglyMeasurable
  have hχmeas : AEStronglyMeasurable χ
      ((volume : Measure (Vec3 × ℝ)).restrict pressureSplitProductDomain) :=
    hχ.1.continuous.measurable.aestronglyMeasurable
  obtain ⟨Cχ, hCχ⟩ := hχ.2.1.exists_bound_of_continuous hχ.1.continuous
  refine ⟨?_, ?_⟩
  · exact hu_i.mul_bdd hpartialMeas
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using hC z)
  · exact hDu_ij.mul_bdd hχmeas
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using hCχ z)

private theorem pressureSplit_viscous_pair_identity
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hu : AEStronglyMeasurable u (volume.restrict pressureSplitDomain))
    (hDu : AEStronglyMeasurable Du (volume.restrict pressureSplitDomain))
    (henergy : (∫⁻ z in pressureSplitDomain,
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict pressureSplitTime), ∀ i : Fin 3,
      HasWeakGradientOn pressureSplitBall (fun x => u (x, t) i)
        (fun x => Du (x, t) i))
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψB : tsupport ψ ⊆ pressureSplitBall)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθc : HasCompactSupport θ) (hθI : tsupport θ ⊆ pressureSplitTime)
    (i j : Fin 3) :
    (∫ z in pressureSplitProductDomain,
      Du z i j * (θ z.2 * mixedSecond ψ j i z.1)) =
      -(∫ z in pressureSplitProductDomain,
        u z i * θ z.2 * spatialDeriv (mixedSecond ψ j i) j z.1) := by
      let : IsFiniteMeasure ((volume : Measure (Vec3 × ℝ)).restrict
          pressureSplitProductDomain) := pressureSplitProductDomain_finite
      let χ : Vec3 × ℝ → ℝ := fun z => mixedSecond ψ j i z.1 * θ z.2
      have hχ := pressureSplit_productTest
        (contDiff_mixedSecond_smooth hψ j i)
        (hasCompactSupport_mixedSecond hψc j i)
        ((tsupport_mixedSecond_subset j i).trans hψB) hθ hθc hθI
      have hIBP := essLocal_sliceGradient_integrationByParts hu hDu henergy hgrad
        hχ.1 hχ.2.1 hχ.2.2 i j
      have hmul : ∀ z : Vec3 × ℝ,
          spatialPartial χ j z =
            θ z.2 * spatialDeriv (mixedSecond ψ j i) j z.1 := by
        intro z
        change spatialPartial
          (fun q : ParabolicPoint => mixedSecond ψ j i q.1 * θ q.2) j
          (parabolicHomeomorph.symm z) = _
        exact pressureSplit_productPartial_formula
          (contDiff_mixedSecond_smooth hψ j i) j (parabolicHomeomorph.symm z)
      have hconverted :
          (∫ z in pressureSplitProductDomain,
            u z i * spatialPartial χ j z) =
          -(∫ z in pressureSplitProductDomain, Du z i j * χ z) := hIBP
      have hconvertedLeft :
          (∫ z in pressureSplitProductDomain,
            u z i * spatialPartial χ j z) =
          (∫ z in pressureSplitProductDomain,
            u z i * θ z.2 * spatialDeriv (mixedSecond ψ j i) j z.1) := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [hmul]
        ring
      have hconvertedRight :
          (∫ z in pressureSplitProductDomain, Du z i j * χ z) =
          (∫ z in pressureSplitProductDomain,
            Du z i j * (θ z.2 * mixedSecond ψ j i z.1)) := by
        apply integral_congr_ae
        filter_upwards [] with z
        dsimp [χ]
        ring
      have hconvertedNeg :
          (∫ z in pressureSplitProductDomain, Du z i j * χ z) =
            -(∫ z in pressureSplitProductDomain,
              u z i * spatialPartial χ j z) := by
        have h := congrArg (fun x : ℝ => -x) hconverted
        simpa only [neg_neg] using h.symm
      exact hconvertedRight.symm.trans
        (hconvertedNeg.trans
          (congrArg (fun x : ℝ => -x) hconvertedLeft))

/-- The viscous contribution vanishes when the momentum equation is tested
against a separated spatial gradient in `lem:pressure-split`. -/
theorem pressureSplit_viscousTerm_zero_product
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hu : AEStronglyMeasurable u (volume.restrict pressureSplitDomain))
    (hDu : AEStronglyMeasurable Du (volume.restrict pressureSplitDomain))
    (henergy : (∫⁻ z in pressureSplitDomain,
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict pressureSplitTime), ∀ i : Fin 3,
      HasWeakGradientOn pressureSplitBall (fun x => u (x, t) i)
        (fun x => Du (x, t) i))
    (hdiv : ∀ χ : Vec3 × ℝ → ℝ,
      χ ∈ spaceTimeTestFunction (V := ℝ) pressureSplitBall pressureSplitTime →
      ∫ z in pressureSplitDomain,
        ∑ i : Fin 3, u z i * spatialPartial χ i z = 0)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψB : tsupport ψ ⊆ pressureSplitBall)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθc : HasCompactSupport θ) (hθI : tsupport θ ⊆ pressureSplitTime) :
    ∫ z in pressureSplitProductDomain,
      ∑ i : Fin 3, ∑ j : Fin 3,
        Du z i j * (θ z.2 * mixedSecond ψ j i z.1) = 0 := by
      let : IsFiniteMeasure ((volume : Measure (Vec3 × ℝ)).restrict
          pressureSplitProductDomain) := pressureSplitProductDomain_finite
      have hpairInt (i j : Fin 3) : IntegrableOn
          (fun z : Vec3 × ℝ => Du z i j *
            (θ z.2 * mixedSecond ψ j i z.1)) pressureSplitProductDomain
            (volume : Measure (Vec3 × ℝ)) := by
        let χ : Vec3 × ℝ → ℝ := fun z => mixedSecond ψ j i z.1 * θ z.2
        have hχ := pressureSplit_productTest
          (contDiff_mixedSecond_smooth hψ j i)
          (hasCompactSupport_mixedSecond hψc j i)
          ((tsupport_mixedSecond_subset j i).trans hψB) hθ hθc hθI
        have h := (pressureSplit_product_factor_integrable henergy hu hDu hχ i j).2
        exact h.congr (Filter.Eventually.of_forall fun z => by
          change (Du z i j * χ z) = _
          dsimp [χ]
          ring)
      have hdiv_j (j : Fin 3) :
          ∫ z in pressureSplitProductDomain,
            ∑ i : Fin 3, u z i * θ z.2 *
              spatialDeriv (mixedSecond ψ j j) i z.1 = 0 := by
        let χ : Vec3 × ℝ → ℝ := fun z => mixedSecond ψ j j z.1 * θ z.2
        have hχ := pressureSplit_productTest
          (contDiff_mixedSecond_smooth hψ j j)
          (hasCompactSupport_mixedSecond hψc j j)
          ((tsupport_mixedSecond_subset j j).trans hψB)
          hθ hθc hθI
        have hzero := pressureSplit_divergence_integral_product hdiv hχ
        have hfun : (fun z : Vec3 × ℝ =>
            ∑ i : Fin 3, u z i * spatialPartial χ i z) =
            (fun z => ∑ i : Fin 3, u z i * θ z.2 *
              spatialDeriv (mixedSecond ψ j j) i z.1) := by
          funext z
          apply Finset.sum_congr rfl
          intro i hi
          have hpartial : spatialPartial χ i z =
              θ z.2 * spatialDeriv (mixedSecond ψ j j) i z.1 := by
            simpa only [χ] using pressureSplit_productPartial_formula_prod
              (contDiff_mixedSecond_smooth hψ j j) i z
          rw [hpartial]
          ring
        rw [hfun] at hzero
        exact hzero
      have hsumI (j : Fin 3) :
          (∑ i : Fin 3, ∫ z in pressureSplitProductDomain,
            u z i * θ z.2 * spatialDeriv (mixedSecond ψ j j) i z.1) = 0 := by
        have hterm (i : Fin 3) : IntegrableOn
            (fun z : Vec3 × ℝ => u z i * θ z.2 *
              spatialDeriv (mixedSecond ψ j j) i z.1)
            pressureSplitProductDomain (volume : Measure (Vec3 × ℝ)) := by
          let χ : Vec3 × ℝ → ℝ := fun z => mixedSecond ψ j j z.1 * θ z.2
          have hχ := pressureSplit_productTest
            (contDiff_mixedSecond_smooth hψ j j)
            (hasCompactSupport_mixedSecond hψc j j)
            ((tsupport_mixedSecond_subset j j).trans hψB)
            hθ hθc hθI
          have h := (pressureSplit_product_factor_integrable henergy hu hDu hχ i i).1
          change IntegrableOn (fun z : Vec3 × ℝ =>
            u z i * spatialPartial χ i z)
            pressureSplitProductDomain (volume : Measure (Vec3 × ℝ)) at h
          exact h.congr (Filter.Eventually.of_forall fun z => by
            change u (parabolicHomeomorph.symm z) i *
              spatialPartial
                (fun q : ParabolicPoint => mixedSecond ψ j j q.1 * θ q.2)
                i (parabolicHomeomorph.symm z) = _
            rw [pressureSplit_productPartial_formula
              (contDiff_mixedSecond_smooth hψ j j) i
              (parabolicHomeomorph.symm z)]
            simp only [parabolicHomeomorph_symm_apply]
            ring)
        have hsum := integral_finsetSum Finset.univ (fun i hi => hterm i)
        rw [← hsum]
        rw [hdiv_j j]
      have hPairSumZero (j : Fin 3) :
          ∑ i : Fin 3, ∫ z in pressureSplitProductDomain,
            Du z i j * (θ z.2 * mixedSecond ψ j i z.1) = 0 := by
        calc
          _ = -∑ i : Fin 3, ∫ z in pressureSplitProductDomain,
              u z i * θ z.2 *
                spatialDeriv (mixedSecond ψ j i) j z.1 := by
                  rw [← Finset.sum_neg_distrib]
                  apply Finset.sum_congr rfl
                  intro i hi
                  exact pressureSplit_viscous_pair_identity hu hDu henergy hgrad
                    hψ hψc hψB hθ hθc hθI i j
          _ = -∑ i : Fin 3, ∫ z in pressureSplitProductDomain,
              u z i * θ z.2 *
                spatialDeriv (mixedSecond ψ j j) i z.1 := by
                  congr 1
                  apply Finset.sum_congr rfl
                  intro i hi
                  apply integral_congr_ae
                  filter_upwards [] with z
                  rw [thirdDerivative_identity hψ i j z.1]
          _ = 0 := by rw [hsumI j]; simp
      have htermInt (i j : Fin 3) : IntegrableOn
          (fun z : Vec3 × ℝ => Du z i j *
            (θ z.2 * mixedSecond ψ j i z.1))
          pressureSplitProductDomain (volume : Measure (Vec3 × ℝ)) := hpairInt i j
      have hinnerInt (i : Fin 3) : IntegrableOn
          (fun z : Vec3 × ℝ => ∑ j : Fin 3,
            Du z i j * (θ z.2 * mixedSecond ψ j i z.1))
          pressureSplitProductDomain (volume : Measure (Vec3 × ℝ)) := by
        change Integrable (fun z : Vec3 × ℝ => ∑ j : Fin 3,
          Du z i j * (θ z.2 * mixedSecond ψ j i z.1))
          ((volume : Measure (Vec3 × ℝ)).restrict pressureSplitProductDomain)
        exact integrable_finsetSum Finset.univ fun j hj => htermInt i j
      have hsumExpand :
          ∫ z in pressureSplitProductDomain,
            ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * (θ z.2 * mixedSecond ψ j i z.1) =
          ∑ i : Fin 3, ∑ j : Fin 3,
            ∫ z in pressureSplitProductDomain,
              Du z i j * (θ z.2 * mixedSecond ψ j i z.1) := by
        rw [integral_finsetSum Finset.univ (fun i hi => by
          change Integrable (fun z : Vec3 × ℝ => ∑ j : Fin 3,
            Du z i j * (θ z.2 * mixedSecond ψ j i z.1))
            ((volume : Measure (Vec3 × ℝ)).restrict pressureSplitProductDomain)
          exact hinnerInt i)]
        apply Finset.sum_congr rfl
        intro i hi
        exact integral_finsetSum Finset.univ (fun j hj => by
          change Integrable (fun z : Vec3 × ℝ =>
            Du z i j * (θ z.2 * mixedSecond ψ j i z.1))
            ((volume : Measure (Vec3 × ℝ)).restrict pressureSplitProductDomain)
          exact htermInt i j)
      rw [hsumExpand, Finset.sum_comm]
      exact Finset.sum_eq_zero fun j hj => hPairSumZero j

end ESS

end
