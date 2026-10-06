/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.PressureSplitPoisson
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszTimeSlice
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupPressureIntegrability
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionPairingSwap

/-!
# Harmonicity of the fixed pressure remainder

The whole-space Riesz pressure and the pressure from the weak momentum
equation have the same spatial Laplacian on the source cylinder.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The fixed whole-space pressure of the zero-extended local velocity tensor,
written in parabolic coordinates. -/
@[expose] def pressureSplitRieszPressure
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ))) : ParabolicPoint → ℝ :=
  fun z => CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
    F hF (parabolicHomeomorph z)

/-- The pressure remainder on the original source cylinder, extended by zero. -/
@[expose] def pressureSplitRemainder (p p₁ : ParabolicPoint → ℝ) : ParabolicPoint → ℝ :=
  goodPointDomain.indicator (fun z => p z - p₁ z)

theorem pressureSplit_remainder_memLp_product
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict pressureSplitDomain))
    (hDu : AEStronglyMeasurable Du (volume.restrict pressureSplitDomain))
    (henergy : (∫⁻ z in pressureSplitDomain,
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict pressureSplitDomain))
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in pressureSplitBall,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict pressureSplitTime) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict pressureSplitTime), ∀ i : Fin 3,
      HasWeakGradientOn pressureSplitBall (fun x => u (x, t) i)
        (fun x => Du (x, t) i)) :
    MemLp (fun z : Vec3 × ℝ => pressureSplitRemainder p
      (pressureSplitRieszPressure (pressureSplitTensor u)
        (pressureSplitTensor_memLp hu hDu henergy hL3 hgrad))
      (parabolicHomeomorph.symm z))
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) := by
  let D : Set (Vec3 × ℝ) := pressureSplitProductDomain
  let hF : ∀ i j, MemLp (pressureSplitTensor u i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) :=
    pressureSplitTensor_memLp hu hDu henergy hL3 hgrad
  let P : Vec3 × ℝ → ℝ := CKN.Leray.rieszPressureSpaceTime
    (3 / 2 : ℝ) (by norm_num) (pressureSplitTensor u) hF
  let Ppara : ParabolicPoint → ℝ :=
    pressureSplitRieszPressure (pressureSplitTensor u) hF
  have hpP : MemLp P (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) :=
    CKN.Leray.rieszPressureSpaceTime_memLp (3 / 2 : ℝ) (by norm_num)
      (pressureSplitTensor u) hF
  have hpDomain : MemLp (fun z : Vec3 × ℝ => p (parabolicHomeomorph.symm z))
      (ENNReal.ofReal (3 / 2 : ℝ))
      ((volume : Measure (Vec3 × ℝ)).restrict D) := by
    have hpara : MeasurableSet pressureSplitDomain := by
      exact (isOpen_spaceTimeSet pressureSplitBall pressureSplitTime
        (isOpen_vec3Ball 0 1) isOpen_Ioo).measurableSet
    have hpre : parabolicHomeomorph.symm ⁻¹' pressureSplitDomain = D := by
      ext z
      rfl
    have hmp := parabolicHomeomorphSymm_measurePreserving.restrict_preimage hpara
    rw [hpre] at hmp
    have h := hp.comp_measurePreserving hmp
    change MemLp (fun z : Vec3 × ℝ => p (parabolicHomeomorph.symm z))
      (ENNReal.ofReal (3 / 2 : ℝ)) _ at h
    exact h
  have hD : MeasurableSet D := by
    exact (isOpen_vec3Ball 0 1).measurableSet.prod measurableSet_Ioo
  have hpGlobal : MemLp (D.indicator
      (fun z : Vec3 × ℝ => p (parabolicHomeomorph.symm z)))
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) :=
    (memLp_indicator_iff_restrict hD).2 hpDomain
  have hPGlobal : MemLp (D.indicator P)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) :=
    hpP.indicator hD
  have hdiff : MemLp (fun z : Vec3 × ℝ =>
      D.indicator (fun w => p (parabolicHomeomorph.symm w) - P w) z)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) := by
    have hsub := hpGlobal.sub hPGlobal
    apply (memLp_congr_ae ?_).2 hsub
    filter_upwards [] with z
    by_cases hz : z ∈ D <;> simp [hz]
  have hdef : (fun z : Vec3 × ℝ => pressureSplitRemainder p Ppara
        (parabolicHomeomorph.symm z)) =
      (fun z => D.indicator
        (fun w => p (parabolicHomeomorph.symm w) - P w) z) := by
    funext z
    change goodPointDomain.indicator (fun y => p y - Ppara y)
      (parabolicHomeomorph.symm z) =
        D.indicator (fun w => p (parabolicHomeomorph.symm w) - P w) z
    have hmem : parabolicHomeomorph.symm z ∈ goodPointDomain ↔ z ∈ D := by
      change ((z.1, z.2) : ParabolicPoint) ∈
          (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1 : ℝ) 0) ↔
        (z.1, z.2) ∈ (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1 : ℝ) 0)
      rfl
    by_cases hz : z ∈ D
    · rw [Set.indicator_of_mem (hmem.mpr hz), Set.indicator_of_mem hz]
      have hP : Ppara (parabolicHomeomorph.symm z) = P z := by
        change CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
            (pressureSplitTensor u) hF
            (parabolicHomeomorph (parabolicHomeomorph.symm z)) = _
        rw [parabolicHomeomorph.apply_symm_apply]
      rw [hP]
    · rw [Set.indicator_of_notMem (fun hm => hz (hmem.mp hm)),
        Set.indicator_of_notMem hz]
  rw [hdef]
  exact hdiff

private theorem pressureSplit_spatialDeriv_mul_const
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (c : ℝ) (i : Fin 3) (x : Vec3) :
    CKN.spatialDeriv (fun y : Vec3 => ψ y * c) i x =
      c * CKN.spatialDeriv ψ i x := by
  unfold CKN.spatialDeriv
  have hd : DifferentiableAt ℝ ψ x := hψ.differentiable (by norm_num) x
  rw [fderiv_mul_const hd c]
  simp only [smul_apply, smul_eq_mul]

private theorem pressureSplit_mixedSecond_mul_const
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (c : ℝ) (i j : Fin 3) (x : Vec3) :
    CKN.mixedSecond (fun y : Vec3 => ψ y * c) i j x =
      c * CKN.mixedSecond ψ i j x := by
  have hfirst : CKN.spatialDeriv (fun y : Vec3 => ψ y * c) j =
      fun y => c * CKN.spatialDeriv ψ j y := by
    funext y
    exact pressureSplit_spatialDeriv_mul_const hψ c j y
  rw [CKN.mixedSecond, hfirst]
  have hψj : ContDiff ℝ (⊤ : ℕ∞) (CKN.spatialDeriv ψ j) := by
    unfold CKN.spatialDeriv
    have hfd := (contDiff_infty_iff_fderiv.mp hψ).2
    exact hfd.clm_apply (contDiff_const :
      ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec3 => CKN.basisVec j))
  have hcomm : (fun y : Vec3 => c * CKN.spatialDeriv ψ j y) =
      fun y => CKN.spatialDeriv ψ j y * c := by
    funext y
    ring
  rw [hcomm, pressureSplit_spatialDeriv_mul_const hψj c i x]
  change c * CKN.spatialDeriv (CKN.spatialDeriv ψ j) i x = _
  rfl

private theorem pressureSplit_jointHessian_product
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (i j : Fin 3) (z : Vec3 × ℝ) :
    CKN.Leray.rieszPressureJointHessian
        (fun w : Vec3 × ℝ => ψ w.1 * θ w.2) i j z =
      θ z.2 * CKN.mixedSecond ψ i j z.1 := by
  let φ : Vec3 × ℝ → ℝ := fun w => ψ w.1 * θ w.2
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ :=
    (hψ.comp (ContinuousLinearMap.fst ℝ Vec3 ℝ).contDiff).mul
      (hθ.comp (ContinuousLinearMap.snd ℝ Vec3 ℝ).contDiff)
  have hs := CKN.Leray.rieszPressure_sliceMixedSecond_eq_joint hφ i j z
  have heq : (fun x : Vec3 => φ (x, z.2)) =
      fun x => ψ x * θ z.2 := by
    funext x
    rfl
  rw [← hs, heq]
  exact pressureSplit_mixedSecond_mul_const hψ (θ z.2) i j z.1

theorem pressureSplit_remainder_pairing_zero
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
    ∫ z : Vec3 × ℝ,
      pressureSplitRemainder p
        (pressureSplitRieszPressure (pressureSplitTensor u)
          (pressureSplitTensor_memLp hu hDu henergy hL3 hgrad))
        (parabolicHomeomorph.symm z) *
        (θ z.2 * CKN.spatialLaplacian ψ z.1) = 0 := by
  let hF : ∀ i j, MemLp (pressureSplitTensor u i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) :=
    pressureSplitTensor_memLp hu hDu henergy hL3 hgrad
  let P : Vec3 × ℝ → ℝ :=
    CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
      (pressureSplitTensor u) hF
  let D : Set (Vec3 × ℝ) := pressureSplitProductDomain
  let Ppara : ParabolicPoint → ℝ :=
    pressureSplitRieszPressure (pressureSplitTensor u) hF
  let R : Vec3 × ℝ → ℝ := fun z =>
    pressureSplitRemainder p Ppara (parabolicHomeomorph.symm z)
  let W : Vec3 × ℝ → ℝ := fun z => θ z.2 * CKN.spatialLaplacian ψ z.1
  let φ : Vec3 × ℝ → ℝ := fun z => ψ z.1 * θ z.2
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ :=
    (hψ.comp (ContinuousLinearMap.fst ℝ Vec3 ℝ).contDiff).mul
      (hθ.comp (ContinuousLinearMap.snd ℝ Vec3 ℝ).contDiff)
  have hφc : HasCompactSupport φ := by
    change IsCompact (tsupport φ)
    rw [show φ = fun z => ψ z.1 * θ z.2 by rfl, CKN.tsupport_mul_prod_eq]
    exact hψc.isCompact.prod hθc.isCompact
  have hWsupport : tsupport W ⊆ pressureSplitProductDomain := by
    rw [show pressureSplitProductDomain = pressureSplitBall ×ˢ pressureSplitTime by rfl]
    rw [show W = fun z => CKN.spatialLaplacian ψ z.1 * θ z.2 by
      funext z
      dsimp [W]
      ring, CKN.tsupport_mul_prod_eq]
    exact Set.prod_mono
      (CKN.tsupport_spatialLaplacian_subset.trans hψB) hθI
  have hMsupport (i j : Fin 3) :
      tsupport (fun z : Vec3 × ℝ =>
        θ z.2 * CKN.mixedSecond ψ j i z.1) ⊆ D := by
    rw [show D = pressureSplitBall ×ˢ pressureSplitTime by rfl]
    rw [show (fun z : Vec3 × ℝ => θ z.2 * CKN.mixedSecond ψ j i z.1) =
      fun z => CKN.mixedSecond ψ j i z.1 * θ z.2 by
        funext z
        ring, CKN.tsupport_mul_prod_eq]
    exact Set.prod_mono ((CKN.tsupport_mixedSecond_subset j i).trans hψB) hθI
  have hprodDomain : MeasurableSet D := by
    exact (isOpen_vec3Ball 0 1).measurableSet.prod measurableSet_Ioo
  have hpoisson := pressureSplit_momentum_poisson hu hDu hpmeas hL2 henergy hp
    hL3 hgrad hdiv hMomentum hψ hψc hψB hθ hθc hθI
  have hdual := blowup_rieszPressureSpaceTime_compact_duality
    (pressureSplitTensor u) hF hφ hφc
  have hdual' : ∫ z : Vec3 × ℝ, P z * W z =
      -∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z : Vec3 × ℝ, pressureSplitTensor u i j z *
          (θ z.2 * CKN.mixedSecond ψ i j z.1) := by
    simpa only [P, W, φ, blowup_rieszPressureJointLaplacian_product hψ hθ,
      pressureSplit_jointHessian_product hψ hθ] using hdual
  have hPweightInt : Integrable (fun z : Vec3 × ℝ => P z * W z) volume :=
    blowup_pressure_mul_product_laplacian_integrable
      (CKN.Leray.rieszPressureSpaceTime_memLp (3 / 2 : ℝ) (by norm_num)
        (pressureSplitTensor u) hF) hψ hψc hθ hθc
  have hPset : (∫ z in D, P z * W z) = ∫ z, P z * W z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hnotW : z ∉ tsupport W := fun h => hz (hWsupport h)
    exact mul_eq_zero_of_right _
      (image_eq_zero_of_notMem_tsupport (f := W) hnotW)
  have hTensorSet (i j : Fin 3) :
      (∫ z in D, pressureSplitTensor u i j z *
        (θ z.2 * CKN.mixedSecond ψ j i z.1)) =
      ∫ z, pressureSplitTensor u i j z *
        (θ z.2 * CKN.mixedSecond ψ j i z.1) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hnot : z ∉ tsupport
        (fun w : Vec3 × ℝ => θ w.2 * CKN.mixedSecond ψ j i w.1) :=
      fun h => hz (hMsupport i j h)
    exact mul_eq_zero_of_right _
      (image_eq_zero_of_notMem_tsupport
        (f := fun w : Vec3 × ℝ => θ w.2 * CKN.mixedSecond ψ j i w.1) hnot)
  have hsumOrient :
      (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z, pressureSplitTensor u i j z *
          (θ z.2 * CKN.mixedSecond ψ j i z.1)) =
      (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z, pressureSplitTensor u i j z *
          (θ z.2 * CKN.mixedSecond ψ i j z.1)) := by
    calc
      _ = ∑ j : Fin 3, ∑ i : Fin 3,
          ∫ z, pressureSplitTensor u i j z *
            (θ z.2 * CKN.mixedSecond ψ j i z.1) := by rw [Finset.sum_comm]
      _ = ∑ j : Fin 3, ∑ i : Fin 3,
          ∫ z, pressureSplitTensor u i j z *
            (θ z.2 * CKN.mixedSecond ψ i j z.1) := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro i hi
          apply integral_congr_ae
          filter_upwards [] with z
          rw [CKN.mixedSecond_swap hψ j i z.1]
      _ = _ := by rw [Finset.sum_comm]
  have hpoissonFull : ∫ z in D,
      p (parabolicHomeomorph.symm z) * W z =
      -∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z, pressureSplitTensor u i j z *
          (θ z.2 * CKN.mixedSecond ψ j i z.1) := by
    calc
      _ = -∑ i : Fin 3, ∑ j : Fin 3,
          ∫ z in D, pressureSplitTensor u i j z *
            (θ z.2 * CKN.mixedSecond ψ j i z.1) := by
          simpa only [D, W] using hpoisson
      _ = -∑ i : Fin 3, ∑ j : Fin 3,
          ∫ z, pressureSplitTensor u i j z *
            (θ z.2 * CKN.mixedSecond ψ j i z.1) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact hTensorSet i j
  have hsourceIntegral :
      (∫ z in D, p (parabolicHomeomorph.symm z) * W z) =
        ∫ z in D, P z * W z := by
    calc
      _ = -∑ i : Fin 3, ∑ j : Fin 3,
          ∫ z, pressureSplitTensor u i j z *
            (θ z.2 * CKN.mixedSecond ψ j i z.1) := hpoissonFull
      _ = -∑ i : Fin 3, ∑ j : Fin 3,
          ∫ z, pressureSplitTensor u i j z *
            (θ z.2 * CKN.mixedSecond ψ i j z.1) := by rw [hsumOrient]
      _ = ∫ z, P z * W z := by rw [hdual']
      _ = ∫ z in D, P z * W z := hPset.symm
  have hprodPressureMeas : MeasurableSet pressureSplitDomain := by
    exact (isOpen_spaceTimeSet pressureSplitBall pressureSplitTime
      (isOpen_vec3Ball 0 1) isOpen_Ioo).measurableSet
  have hpProduct : MemLp (fun z : Vec3 × ℝ => p (parabolicHomeomorph.symm z))
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict D) := by
    have hpre : parabolicHomeomorph.symm ⁻¹' pressureSplitDomain = D := by
      ext z
      rfl
    have hmp := parabolicHomeomorphSymm_measurePreserving.restrict_preimage
      hprodPressureMeas
    rw [hpre] at hmp
    exact hp.comp_measurePreserving hmp
  have hpProductGlobal : MemLp (D.indicator
      (fun z : Vec3 × ℝ => p (parabolicHomeomorph.symm z)))
      (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
    (memLp_indicator_iff_restrict hprodDomain).2 hpProduct
  have hpWeightGlobal := blowup_pressure_mul_product_laplacian_integrable
    hpProductGlobal hψ hψc hθ hθc
  have hpWeightSet : IntegrableOn
      (fun z : Vec3 × ℝ => p (parabolicHomeomorph.symm z) * W z) D volume := by
    apply (hpWeightGlobal.integrableOn (s := D)).congr_fun_ae
    filter_upwards [ae_restrict_mem hprodDomain] with z hz
    simp [W, Set.indicator_of_mem hz]
  have hRdef : R = D.indicator
      (fun z => p (parabolicHomeomorph.symm z) - P z) := by
    funext z
    change goodPointDomain.indicator (fun y => p y - Ppara y)
      (parabolicHomeomorph.symm z) =
        D.indicator (fun y => p (parabolicHomeomorph.symm y) - P y) z
    have hmem : parabolicHomeomorph.symm z ∈ goodPointDomain ↔ z ∈ D := by
      change ((z.1, z.2) : ParabolicPoint) ∈
          (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1 : ℝ) 0) ↔
        (z.1, z.2) ∈ (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1 : ℝ) 0)
      rfl
    by_cases hz : z ∈ D
    · rw [Set.indicator_of_mem (hmem.mpr hz), Set.indicator_of_mem hz]
      have hP : Ppara (parabolicHomeomorph.symm z) = P z := by
        change CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
            (pressureSplitTensor u) hF
            (parabolicHomeomorph (parabolicHomeomorph.symm z)) = _
        rw [parabolicHomeomorph.apply_symm_apply]
      rw [hP]
    · rw [Set.indicator_of_notMem (fun hm => hz (hmem.mp hm)),
        Set.indicator_of_notMem hz]
  have hRweightInt : Integrable (fun z : Vec3 × ℝ => R z * W z) volume := by
    have hR : MemLp R (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
      exact pressureSplit_remainder_memLp_product hu hDu henergy hp hL3 hgrad
    exact blowup_pressure_mul_product_laplacian_integrable hR hψ hψc hθ hθc
  have hRweight : (fun z : Vec3 × ℝ => R z * W z) =ᵐ[volume]
      (fun z => D.indicator
        (fun w => p (parabolicHomeomorph.symm w) - P w) z * W z) := by
    filter_upwards [] with z
    rw [show R z = D.indicator
      (fun w => p (parabolicHomeomorph.symm w) - P w) z from congrFun hRdef z]
  have hRsplit : ∫ z : Vec3 × ℝ, R z * W z =
      (∫ z in D, p (parabolicHomeomorph.symm z) * W z) -
        ∫ z in D, P z * W z := by
    calc
      _ = ∫ z, D.indicator
          (fun w => p (parabolicHomeomorph.symm w) - P w) z * W z :=
        integral_congr_ae hRweight
      _ = ∫ z in D, (p (parabolicHomeomorph.symm z) - P z) * W z := by
        calc
          _ = ∫ z, D.indicator (fun z =>
              (p (parabolicHomeomorph.symm z) - P z) * W z) z := by
                apply integral_congr_ae
                filter_upwards [] with z
                by_cases hz : z ∈ D <;> simp [hz]
          _ = _ := by rw [integral_indicator hprodDomain]
      _ = _ := by
        calc
          _ = ∫ z in D,
              (p (parabolicHomeomorph.symm z) * W z - P z * W z) := by
                apply integral_congr_ae
                filter_upwards [] with z
                ring
          _ = _ := integral_sub hpWeightSet hPweightInt.integrableOn
  have hzero : ∫ z : Vec3 × ℝ, R z * W z = 0 := by
    rw [hRsplit, hsourceIntegral]
    ring
  change (∫ z : Vec3 × ℝ,
      pressureSplitRemainder p Ppara (parabolicHomeomorph.symm z) * W z) = 0
  exact hzero

end ESS

end
