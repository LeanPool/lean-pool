/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.PressureSplitHarmonic
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.PressureSplitTensor
public import LeanPool.EscauriazaSereginSverak.Endpoint.PressureSplitData
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszProductTest
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.MomentumIntegrand
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.DivergenceFreeIntegrand

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem pressureSplit_integral_to_product
    {f : ParabolicPoint → ℝ} :
    (∫ z in pressureSplitDomain, f z) =
      ∫ z in pressureSplitProductDomain, f (parabolicHomeomorph.symm z) := by
  have hconvert := setIntegral_parabolic_to_product
    (Ω := pressureSplitBall) (I := pressureSplitTime) (F := f)
  exact hconvert.symm

private theorem pressureSplit_pressureTest_mem
    {ψ : Vec3 → ℝ} {θ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψB : tsupport ψ ⊆ pressureSplitBall)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ)
    (hθI : tsupport θ ⊆ pressureSplitTime) :
    CKN.pressureTestProduct ψ θ ∈
      spaceTimeTestFunction (V := Vec3) pressureSplitBall pressureSplitTime :=
  CKN.pressureTest_mem_spaceTimeTestFunction hψ hψc hψB hθ hθc hθI

private theorem pressureSplitRieszInput_memLp
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hu : AEStronglyMeasurable u (volume.restrict pressureSplitDomain))
    (hDu : AEStronglyMeasurable Du (volume.restrict pressureSplitDomain))
    (henergy : (∫⁻ z in pressureSplitDomain,
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in pressureSplitBall,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict pressureSplitTime) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict pressureSplitTime), ∀ k : Fin 3,
      HasWeakGradientOn pressureSplitBall (fun x => u (x, t) k)
        (fun x => Du (x, t) k)) :
    ∀ i j : Fin 3,
      MemLp (pressureSplitTensor u i j) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume : Measure (Vec3 × ℝ)) := by
  exact pressureSplitTensor_memLp hu hDu henergy hL3 hgrad

private theorem pressureSplit_productDomain_measurable :
    MeasurableSet pressureSplitProductDomain := by
  exact (isOpen_vec3Ball (0 : Vec3) 1).measurableSet.prod measurableSet_Ioo

private theorem pressureSplit_parabolicDomain_measurable :
    MeasurableSet pressureSplitDomain := by
  exact (isOpen_spaceTimeSet pressureSplitBall pressureSplitTime
    (isOpen_vec3Ball (0 : Vec3) 1) isOpen_Ioo).measurableSet

private theorem pressureSplit_hessianWeight_memLp
    {ψ : Vec3 → ℝ} {θ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ)
    (i j : Fin 3) :
    MemLp (fun z : Vec3 × ℝ => θ z.2 * CKN.mixedSecond ψ i j z.1)
      (ENNReal.ofReal (3 : ℝ)) (volume : Measure (Vec3 × ℝ)) := by
  have hcont : Continuous
      (fun z : Vec3 × ℝ => CKN.mixedSecond ψ i j z.1 * θ z.2) :=
    ((CKN.contDiff_mixedSecond_smooth hψ i j).continuous.comp continuous_fst).mul
      (hθ.continuous.comp continuous_snd)
  have hcompact : HasCompactSupport
      (fun z : Vec3 × ℝ => CKN.mixedSecond ψ i j z.1 * θ z.2) := by
    change IsCompact (tsupport (fun z : Vec3 × ℝ =>
      CKN.mixedSecond ψ i j z.1 * θ z.2))
    rw [CKN.tsupport_mul_prod_eq]
    exact (CKN.hasCompactSupport_mixedSecond hψc i j).isCompact.prod hθc.isCompact
  have hmem : MemLp (fun z : Vec3 × ℝ =>
      CKN.mixedSecond ψ i j z.1 * θ z.2) (ENNReal.ofReal (3 : ℝ)) volume :=
    hcont.memLp_of_hasCompactSupport (p := ENNReal.ofReal (3 : ℝ)) hcompact
  have hEq : (fun z : Vec3 × ℝ => θ z.2 * CKN.mixedSecond ψ i j z.1) =ᵐ[volume]
      (fun z => CKN.mixedSecond ψ i j z.1 * θ z.2) := by
    filter_upwards [] with z
    ring
  exact (memLp_congr_ae hEq).2 hmem

/-- Testing the weak momentum equation with a compactly supported spatial
gradient gives the pressure Poisson identity in the source cylinder. -/
theorem pressureSplit_momentum_poisson
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict pressureSplitDomain))
    (hDu : AEStronglyMeasurable Du (volume.restrict pressureSplitDomain))
    (hpmeas : AEStronglyMeasurable p (volume.restrict pressureSplitDomain))
    (hL2 : essSup (fun t : ℝ => ∫⁻ x in pressureSplitBall,
      ‖u (x, t)‖ₑ ^ (2 : ℝ)) (volume.restrict pressureSplitTime) < ⊤)
    (henergy : (∫⁻ z in pressureSplitDomain,
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict pressureSplitDomain))
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in pressureSplitBall,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict pressureSplitTime) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict pressureSplitTime), ∀ i : Fin 3,
      HasWeakGradientOn pressureSplitBall (fun x => u (x, t) i)
        (fun x => Du (x, t) i))
    (hdiv : ∀ χ : Vec3 × ℝ → ℝ,
      χ ∈ spaceTimeTestFunction (V := ℝ) pressureSplitBall pressureSplitTime →
      ∫ z in pressureSplitDomain,
        ∑ i : Fin 3, u z i * spatialPartial χ i z = 0)
    (hMomentum : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) pressureSplitBall pressureSplitTime →
      ∫ z in pressureSplitDomain,
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i) = 0)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψB : tsupport ψ ⊆ pressureSplitBall)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθc : HasCompactSupport θ) (hθI : tsupport θ ⊆ pressureSplitTime) :
    ∫ z in pressureSplitProductDomain,
      p (parabolicHomeomorph.symm z) *
          (θ z.2 * CKN.spatialLaplacian ψ z.1) =
      -∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z in pressureSplitProductDomain,
          pressureSplitTensor u i j z *
            (θ z.2 * CKN.mixedSecond ψ j i z.1) := by
  let hdata := pressureSplit_localData hu hDu hpmeas hL2 henergy hp hgrad
  let φP := CKN.pressureTestProduct ψ θ
  let φ : ParabolicPoint → Vec3 :=
    fun z => CKN.pressureTestParabolic ψ θ z
  have hφP := pressureSplit_pressureTest_mem hψ hψc hψB hθ hθc hθI
  have hφeq :
      (fun z : Vec3 × ℝ => φ (parabolicHomeomorph.symm z)) = φP := by
    funext z
    rfl
  have hφ : φ ∈ spaceTimeTestFunction (V := Vec3)
      pressureSplitBall pressureSplitTime := by
    change (fun z : Vec3 × ℝ => φ (parabolicHomeomorph.symm z)) ∈ _
    rw [hφeq]
    exact hφP
  let K : Set ParabolicPoint := tsupport (show ParabolicPoint → Vec3 from φ)
  have hKcompact : IsCompact K := isCompact_tsupport_parabolic hφ.2.1
  have hKsubset : K ⊆ pressureSplitDomain :=
    CKN.tsupport_parabolic_subset_spaceTimeSet hφ
  have hφval : (show ParabolicPoint → Vec3 from φ) =
      (show ParabolicPoint → Vec3 from φP) := by
    funext y
    cases y with
    | mk x t =>
      have h := congrFun hφeq (x, t)
      simpa only [parabolicHomeomorph_symm_apply] using h
  have hK_eq : K = tsupport φP := by
    change tsupport (show ParabolicPoint → Vec3 from φ) = tsupport φP
    rw [hφval]
    exact CKN.tsupport_parabolic_eq (show Vec3 × ℝ → Vec3 from φP)
  have hcomponent_prod_eq (i : Fin 3) :
      (fun y : Vec3 × ℝ => φ y i) = fun y => φP y i := by
    funext y
    have h := congrFun hφeq y
    simpa only [parabolicHomeomorph_symm_apply] using congrArg (fun w : Vec3 => w i) h
  have hnotTest (z : ParabolicPoint) (hz : z ∉ K) :
      (show Vec3 × ℝ from z) ∉ tsupport φP := by
    have hz' : z ∉ tsupport φP := by
      rw [← hK_eq]
      exact hz
    exact hz'
  have hcomponent_eq (i : Fin 3) :
      (fun z : Vec3 × ℝ => φ (parabolicHomeomorph.symm z) i) =
        (fun z => φP z i) := by
    funext z
    exact congrArg (fun w : Vec3 => w i) (congrFun hφeq z)
  have hpartial (i j : Fin 3) (z : ParabolicPoint) :
      spatialPartial (fun y : ParabolicPoint => φ y i) j z =
        θ z.2 * CKN.mixedSecond ψ j i z.1 := by
    change spatialPartial
      (fun y : ParabolicPoint => CKN.pressureTestParabolic ψ θ y i) j z = _
    exact CKN.pressureTest_spatialPartial hψ i j z
  have hpartialProd (i j : Fin 3) (z : Vec3 × ℝ) :
      spatialPartial (fun y : ParabolicPoint => φ y i) j
          (parabolicHomeomorph.symm z) =
        θ z.2 * CKN.mixedSecond ψ j i z.1 := by
    simpa only [parabolicHomeomorph_symm_apply] using
      hpartial i j (parabolicHomeomorph.symm z)
  let T : ParabolicPoint → ℝ := fun z =>
    ∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z
  let N : ParabolicPoint → ℝ := fun z =>
    ∑ i : Fin 3, ∑ j : Fin 3,
      u z i * u z j * spatialPartial (fun y => φ y i) j z
  let V : ParabolicPoint → ℝ := fun z =>
    ∑ i : Fin 3, ∑ j : Fin 3,
      Du z i j * spatialPartial (fun y => φ y i) j z
  let P : ParabolicPoint → ℝ := fun z =>
    p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
  have hTzero (z : ParabolicPoint) (hz : z ∉ K) : T z = 0 := by
    have hcomp (i : Fin 3) :
        (show Vec3 × ℝ from z) ∉ tsupport (fun y : Vec3 × ℝ => φP y i) := by
      intro hi
      exact hnotTest z hz
        (CKN.tsupport_component_subset (V := Vec3) (ι := Fin 3) φP i
          (by intro y hy; simp [hy]) hi)
    have hcomp' (i : Fin 3) : (show Vec3 × ℝ from z) ∉
        tsupport (fun y : Vec3 × ℝ => φ y i) := by
      rw [hcomponent_prod_eq i]
      exact hcomp i
    simp only [T]
    apply Finset.sum_eq_zero
    intro i hi
    have hzero := CKN.timePartial_eq_zero_off_tsupport
      (ψ := fun y : Vec3 × ℝ => φ y i) (hcomp' i)
    have hzero' : timePartial (fun y : Vec3 × ℝ => φ y i)
        (show Vec3 × ℝ from z) = 0 := hzero
    change u z i * timePartial (fun y : Vec3 × ℝ => φ y i)
        (show Vec3 × ℝ from z) = 0
    rw [hzero', mul_zero]
  have hNzero (z : ParabolicPoint) (hz : z ∉ K) : N z = 0 := by
    have hcomp (i : Fin 3) :
        (show Vec3 × ℝ from z) ∉ tsupport (fun y : Vec3 × ℝ => φP y i) := by
      intro hi
      exact hnotTest z hz
        (CKN.tsupport_component_subset (V := Vec3) (ι := Fin 3) φP i
          (by intro y hy; simp [hy]) hi)
    have hcomp' (i : Fin 3) : (show Vec3 × ℝ from z) ∉
        tsupport (fun y : Vec3 × ℝ => φ y i) := by
      rw [hcomponent_prod_eq i]
      exact hcomp i
    simp only [N]
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    have hzero := CKN.spatialPartial_eq_zero_off_tsupport
      (ψ := fun y : Vec3 × ℝ => φ y i) (hcomp' i) j
    have hzero' : spatialPartial (fun y : Vec3 × ℝ => φ y i) j
        (show Vec3 × ℝ from z) = 0 := hzero
    change u z i * u z j * spatialPartial (fun y : Vec3 × ℝ => φ y i) j
        (show Vec3 × ℝ from z) = 0
    rw [hzero', mul_zero]
  have hVzero (z : ParabolicPoint) (hz : z ∉ K) : V z = 0 := by
    have hcomp (i : Fin 3) :
        (show Vec3 × ℝ from z) ∉ tsupport (fun y : Vec3 × ℝ => φP y i) := by
      intro hi
      exact hnotTest z hz
        (CKN.tsupport_component_subset (V := Vec3) (ι := Fin 3) φP i
          (by intro y hy; simp [hy]) hi)
    have hcomp' (i : Fin 3) : (show Vec3 × ℝ from z) ∉
        tsupport (fun y : Vec3 × ℝ => φ y i) := by
      rw [hcomponent_prod_eq i]
      exact hcomp i
    simp only [V]
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    have hzero := CKN.spatialPartial_eq_zero_off_tsupport
      (ψ := fun y : Vec3 × ℝ => φ y i) (hcomp' i) j
    have hzero' : spatialPartial (fun y : Vec3 × ℝ => φ y i) j
        (show Vec3 × ℝ from z) = 0 := hzero
    change Du z i j * spatialPartial (fun y : Vec3 × ℝ => φ y i) j
        (show Vec3 × ℝ from z) = 0
    rw [hzero', mul_zero]
  have hPzero (z : ParabolicPoint) (hz : z ∉ K) : P z = 0 := by
    have hcomp (i : Fin 3) :
        (show Vec3 × ℝ from z) ∉ tsupport (fun y : Vec3 × ℝ => φP y i) := by
      intro hi
      exact hnotTest z hz
        (CKN.tsupport_component_subset (V := Vec3) (ι := Fin 3) φP i
          (by intro y hy; simp [hy]) hi)
    have hcomp' : ∀ i : Fin 3, (show Vec3 × ℝ from z) ∉
        tsupport (fun y : Vec3 × ℝ => φ y i) := by
      intro i
      rw [hcomponent_prod_eq i]
      exact hcomp i
    simp only [P]
    have hsum : (∑ i : Fin 3,
        spatialPartial (fun y : ParabolicPoint => φ y i) i z) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact CKN.spatialPartial_eq_zero_off_tsupport (hcomp' i) i
    rw [hsum, mul_zero]
  have hT_K := CKN.momentum_timeTerm_integrableOn_of_data
    hdata hKcompact hKsubset hφP
  have hN_K := CKN.momentum_nonlinearTerm_integrableOn_of_data
    hdata hKcompact hKsubset hφP
  have hV_K := CKN.momentum_viscousTerm_integrableOn_of_data
    hdata hKcompact hKsubset hφP
  have hP_K := CKN.momentum_pressureTerm_integrableOn_of_data
    hdata hKcompact hKsubset hφP
  have hT_D : IntegrableOn T pressureSplitDomain volume := by
    apply hT_K.of_ae_sdiff_eq_zero
      pressureSplit_parabolicDomain_measurable.nullMeasurableSet
    filter_upwards [] with z hz
    exact hTzero z hz.2
  have hN_D : IntegrableOn N pressureSplitDomain volume := by
    apply hN_K.of_ae_sdiff_eq_zero
      pressureSplit_parabolicDomain_measurable.nullMeasurableSet
    filter_upwards [] with z hz
    exact hNzero z hz.2
  have hV_D : IntegrableOn V pressureSplitDomain volume := by
    apply hV_K.of_ae_sdiff_eq_zero
      pressureSplit_parabolicDomain_measurable.nullMeasurableSet
    filter_upwards [] with z hz
    exact hVzero z hz.2
  have hP_D : IntegrableOn P pressureSplitDomain volume := by
    apply hP_K.of_ae_sdiff_eq_zero
      pressureSplit_parabolicDomain_measurable.nullMeasurableSet
    filter_upwards [] with z hz
    exact hPzero z hz.2
  have htimeZero : ∫ z in pressureSplitProductDomain,
      T (parabolicHomeomorph.symm z) = 0 := by
    have hS2 : ∀ χ : Vec3 × ℝ → ℝ,
        χ ∈ spaceTimeTestFunction (V := ℝ) pressureSplitBall pressureSplitTime →
        IntegrableOn (fun z => ∑ i, u z i * spatialPartial χ i z)
          (tsupport χ) volume ∧
        ∫ z in pressureSplitDomain, ∑ i, u z i * spatialPartial χ i z = 0 := by
      intro χ hχ
      exact ⟨CKN.divergenceFree_integrand_integrableOn_of_data hdata hχ,
        hdiv χ hχ⟩
    have h := CKN.pressure_time_integral_zero hS2 hψ hψc hψB hθ hθc hθI
    have hconvert := pressureSplit_integral_to_product (f := T)
    simpa only [T, φ, CKN.pressureTestParabolic] using hconvert.symm.trans h.2
  have hviscousZero : ∫ z in pressureSplitProductDomain,
      ∑ i : Fin 3, ∑ j : Fin 3,
        Du (parabolicHomeomorph.symm z) i j *
          (θ z.2 * CKN.mixedSecond ψ j i z.1) = 0 :=
    pressureSplit_viscousTerm_zero_product hu hDu henergy hgrad hdiv
      hψ hψc hψB hθ hθc hθI
  have hmpre : parabolicHomeomorph.symm ⁻¹' pressureSplitDomain =
      pressureSplitProductDomain := by
    ext z
    rfl
  have hmp := parabolicHomeomorphSymm_measurePreserving.restrict_preimage
    pressureSplit_parabolicDomain_measurable
  rw [hmpre] at hmp
  let Tprod : Vec3 × ℝ → ℝ := fun z => T (parabolicHomeomorph.symm z)
  let Nprod : Vec3 × ℝ → ℝ := fun z => N (parabolicHomeomorph.symm z)
  let Vprod : Vec3 × ℝ → ℝ := fun z => V (parabolicHomeomorph.symm z)
  let Pprod : Vec3 × ℝ → ℝ := fun z => P (parabolicHomeomorph.symm z)
  have hTprod : IntegrableOn Tprod pressureSplitProductDomain
      (volume : Measure (Vec3 × ℝ)) := by
    exact hmp.integrable_comp_of_integrable hT_D
  have hNprod : IntegrableOn Nprod pressureSplitProductDomain
      (volume : Measure (Vec3 × ℝ)) := by
    exact hmp.integrable_comp_of_integrable hN_D
  have hVprod : IntegrableOn Vprod pressureSplitProductDomain
      (volume : Measure (Vec3 × ℝ)) := by
    exact hmp.integrable_comp_of_integrable hV_D
  have hPprod : IntegrableOn Pprod pressureSplitProductDomain
      (volume : Measure (Vec3 × ℝ)) := by
    exact hmp.integrable_comp_of_integrable hP_D
  have hMomentumProduct :
      ∫ z in pressureSplitProductDomain,
        (-(Tprod z) - Nprod z + Vprod z - Pprod z) = 0 := by
    have hsource : ∫ z in pressureSplitDomain,
        -T z - N z + V z - P z = 0 := by
      have h := hMomentum φ hφ
      simpa [T, N, V, P, zero_mul] using h
    have hconvert := pressureSplit_integral_to_product
      (f := fun z : ParabolicPoint => -T z - N z + V z - P z)
    calc
      _ = ∫ z in pressureSplitDomain, -T z - N z + V z - P z := hconvert.symm
      _ = 0 := hsource
      _ = _ := rfl
  have hlinear :
      (∫ z in pressureSplitProductDomain,
        (-(Tprod z) - Nprod z + Vprod z - Pprod z)) =
      (-(∫ z in pressureSplitProductDomain, Tprod z)
          - (∫ z in pressureSplitProductDomain, Nprod z)
          + (∫ z in pressureSplitProductDomain, Vprod z)
          - (∫ z in pressureSplitProductDomain, Pprod z)) := by
    have hsub :
        (∫ z in pressureSplitProductDomain, -Tprod z - Nprod z) =
          -(∫ z in pressureSplitProductDomain, Tprod z) -
            ∫ z in pressureSplitProductDomain, Nprod z := by
      calc
        _ = (∫ z in pressureSplitProductDomain, -Tprod z) -
              ∫ z in pressureSplitProductDomain, Nprod z :=
          integral_sub hTprod.neg hNprod
        _ = _ := by rw [integral_neg]
    have hadd :
        (∫ z in pressureSplitProductDomain,
          (-Tprod z - Nprod z) + Vprod z) =
          (∫ z in pressureSplitProductDomain, -Tprod z - Nprod z) +
            ∫ z in pressureSplitProductDomain, Vprod z :=
      integral_add (hTprod.neg.sub hNprod) hVprod
    calc
      _ = (∫ z in pressureSplitProductDomain,
          (-Tprod z - Nprod z + Vprod z) - Pprod z) := rfl
      _ = (∫ z in pressureSplitProductDomain,
            (-Tprod z - Nprod z) + Vprod z) -
              ∫ z in pressureSplitProductDomain, Pprod z :=
        integral_sub ((hTprod.neg.sub hNprod).add hVprod) hPprod
      _ = _ := by rw [hadd, hsub]
  have hNproduct :
      (∫ z in pressureSplitProductDomain, Nprod z) =
        ∑ i : Fin 3, ∑ j : Fin 3,
          ∫ z in pressureSplitProductDomain,
            pressureSplitTensor u i j z *
              (θ z.2 * CKN.mixedSecond ψ j i z.1) := by
    have : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by norm_num⟩
    have : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩
    have hHolder : (3 / 2 : ℝ).HolderConjugate 3 := by
      rw [Real.holderConjugate_iff]
      norm_num
    let : (ENNReal.ofReal (3 / 2 : ℝ)).HolderConjugate
        (ENNReal.ofReal (3 : ℝ)) := Real.HolderConjugate.ennrealOfReal hHolder
    have hF := pressureSplitRieszInput_memLp hu hDu henergy hL3 hgrad
    have htermLp (i j : Fin 3) : IntegrableOn
        (fun z : Vec3 × ℝ => pressureSplitTensor u i j z *
          (θ z.2 * CKN.mixedSecond ψ j i z.1))
        pressureSplitProductDomain (volume : Measure (Vec3 × ℝ)) := by
      have hglobal := (hF i j).integrable_mul
        (pressureSplit_hessianWeight_memLp hψ hψc hθ hθc j i)
      exact hglobal.integrableOn
    have hsumIntegral :
        (∫ z in pressureSplitProductDomain,
          ∑ i : Fin 3, ∑ j : Fin 3,
            pressureSplitTensor u i j z *
              (θ z.2 * CKN.mixedSecond ψ j i z.1)) =
        ∑ i : Fin 3, ∑ j : Fin 3,
          ∫ z in pressureSplitProductDomain,
            pressureSplitTensor u i j z *
              (θ z.2 * CKN.mixedSecond ψ j i z.1) := by
      rw [integral_finsetSum Finset.univ (fun i hi => by
        change Integrable (fun z : Vec3 × ℝ =>
          ∑ j : Fin 3, pressureSplitTensor u i j z *
            (θ z.2 * CKN.mixedSecond ψ j i z.1))
          ((volume : Measure (Vec3 × ℝ)).restrict pressureSplitProductDomain)
        exact integrable_finsetSum Finset.univ (fun j hj => htermLp i j))]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finsetSum Finset.univ (fun j hj => htermLp i j)
    have hsource (z : Vec3 × ℝ) (hz : z ∈ pressureSplitProductDomain)
        (i j : Fin 3) : pressureSplitTensor u i j z =
          u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j := by
      have hin : parabolicHomeomorph.symm z ∈
          pressureSplitDomain := by
        change (parabolicHomeomorph.symm z).1 ∈ pressureSplitBall ∧
          (parabolicHomeomorph.symm z).2 ∈ pressureSplitTime
        change z.1 ∈ pressureSplitBall ∧ z.2 ∈ pressureSplitTime at hz
        simpa only [parabolicHomeomorph_symm_apply] using hz
      unfold pressureSplitTensor
      change pressureSplitDomain.indicator
        (fun q : ParabolicPoint => u q i * u q j)
        (parabolicHomeomorph.symm z) = _
      rw [Set.indicator_of_mem hin]
    have hpoint : ∀ᵐ z ∂((volume : Measure (Vec3 × ℝ)).restrict
        pressureSplitProductDomain),
        Nprod z = ∑ i : Fin 3, ∑ j : Fin 3,
          pressureSplitTensor u i j z *
            (θ z.2 * CKN.mixedSecond ψ j i z.1) := by
      filter_upwards [ae_restrict_mem pressureSplit_productDomain_measurable]
        with z hz
      simp only [Nprod, N]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hpartialProd i j z, hsource z hz i j]
    calc
      (∫ z in pressureSplitProductDomain, Nprod z) =
          ∫ z in pressureSplitProductDomain,
            ∑ i : Fin 3, ∑ j : Fin 3,
              pressureSplitTensor u i j z *
                (θ z.2 * CKN.mixedSecond ψ j i z.1) :=
        integral_congr_ae hpoint
      _ = _ := hsumIntegral
  have hPproduct :
      (∫ z in pressureSplitProductDomain, Pprod z) =
        ∫ z in pressureSplitProductDomain,
          p (parabolicHomeomorph.symm z) *
            (θ z.2 * CKN.spatialLaplacian ψ z.1) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem pressureSplit_productDomain_measurable]
      with z hz
    dsimp only [Pprod, P]
    have htrace :
        (∑ i : Fin 3, spatialPartial (fun y : ParabolicPoint => φ y i) i
          (parabolicHomeomorph.symm z)) =
        θ z.2 * CKN.spatialLaplacian ψ z.1 := by
      calc
        _ = ∑ i : Fin 3, θ z.2 * CKN.mixedSecond ψ i i z.1 := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hpartialProd i i z
        _ = θ z.2 * CKN.spatialLaplacian ψ z.1 := by
          rw [← Finset.mul_sum]
          rfl
    rw [htrace]
  have hNsum :
      (∫ z in pressureSplitProductDomain, Nprod z) =
        ∑ i : Fin 3, ∑ j : Fin 3,
          ∫ z in pressureSplitProductDomain,
            pressureSplitTensor u i j z *
              (θ z.2 * CKN.mixedSecond ψ j i z.1) := hNproduct
  have hPsum :
      (∫ z in pressureSplitProductDomain, Pprod z) =
        ∫ z in pressureSplitProductDomain,
          p (parabolicHomeomorph.symm z) *
            (θ z.2 * CKN.spatialLaplacian ψ z.1) := hPproduct
  have hEq : (∫ z in pressureSplitProductDomain, Pprod z) =
      -(∫ z in pressureSplitProductDomain, Nprod z) := by
    have h := hMomentumProduct
    rw [hlinear] at h
    have hVprodZero : ∫ z in pressureSplitProductDomain, Vprod z = 0 := by
      calc
        (∫ z in pressureSplitProductDomain, Vprod z) =
            ∫ z in pressureSplitProductDomain,
              ∑ i : Fin 3, ∑ j : Fin 3,
                Du (parabolicHomeomorph.symm z) i j *
                  (θ z.2 * CKN.mixedSecond ψ j i z.1) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem pressureSplit_productDomain_measurable]
            with z hz
          dsimp only [Vprod, V]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [hpartialProd i j z]
        _ = 0 := hviscousZero
    rw [htimeZero, hVprodZero] at h
    linarith only [h]
  rw [hPsum, hNsum] at hEq
  exact hEq

end ESS

end
