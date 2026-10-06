/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.PressureSplitRemainder
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszSliceCore

/-!
# Harmonicity of the pressure remainder

The momentum equation and the Poisson identity for the fixed Riesz pressure
give distributional harmonicity of the remainder on almost every time slice.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

private theorem pressureSplit_remainder_slice_pairing_ae
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
    (hψc : HasCompactSupport ψ) (hψB : tsupport ψ ⊆ pressureSplitBall) :
    ∀ᵐ t ∂(volume.restrict pressureSplitTime),
      ∫ x : Vec3,
        pressureSplitRemainder p
          (pressureSplitRieszPressure (pressureSplitTensor u)
            (pressureSplitTensor_memLp hu hDu henergy hL3 hgrad)) (x,t) *
          CKN.spatialLaplacian ψ x = 0 := by
  let hF : ∀ i j, MemLp (pressureSplitTensor u i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) :=
    pressureSplitTensor_memLp hu hDu henergy hL3 hgrad
  let P : ParabolicPoint → ℝ :=
    pressureSplitRieszPressure (pressureSplitTensor u) hF
  let R : Vec3 × ℝ → ℝ := fun z =>
    pressureSplitRemainder p P (parabolicHomeomorph.symm z)
  have hR : MemLp R (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) := by
    exact pressureSplit_remainder_memLp_product hu hDu henergy hp hL3 hgrad
  let H : ℝ → ℝ := fun t => ∫ x : Vec3,
    R (x,t) * CKN.spatialLaplacian ψ x
  have hH : LocallyIntegrableOn H pressureSplitTime volume :=
    blowup_pressure_slice_laplacian_locallyIntegrable hR hψ hψc
      (by norm_num : (-1 : ℝ) < 0)
  have hpair : ∀ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ →
      HasCompactSupport θ → tsupport θ ⊆ pressureSplitTime →
      ∫ t : ℝ, θ t • H t = 0 := by
    intro θ hθ hθc hθI
    have hzero := pressureSplit_remainder_pairing_zero
      hu hDu hpmeas hL2 henergy hp hL3 hgrad hdiv hMomentum
      hψ hψc hψB hθ hθc hθI
    have hFub := blowup_pressure_product_laplacian_fubini
      hR hψ hψc hθ hθc
    simpa only [H, R, P, smul_eq_mul] using hFub.symm.trans hzero
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    hH hpair
  exact (ae_restrict_iff' measurableSet_Ioo).mpr hae

/-- The fixed pressure remainder is weakly harmonic in the source ball for
almost every time slice. -/
theorem pressureSplitRemainder_harmonic_slices
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
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i) = 0) :
    ∀ᵐ t ∂(volume.restrict pressureSplitTime),
      CKN.Foundation.Heat.WeaklyHarmonicOn pressureSplitBall
        (fun x : Vec3 => pressureSplitRemainder p
          (pressureSplitRieszPressure (pressureSplitTensor u)
            (pressureSplitTensor_memLp hu hDu henergy hL3 hgrad)) (x,t)) := by
  classical
  obtain ⟨Q, hQcount, hQdense⟩ := TopologicalSpace.exists_countable_dense Vec3
  let : Countable Q := hQcount.to_subtype
  let hF : ∀ i j, MemLp (pressureSplitTensor u i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) :=
    pressureSplitTensor_memLp hu hDu henergy hL3 hgrad
  let P : ParabolicPoint → ℝ := pressureSplitRieszPressure
    (pressureSplitTensor u) hF
  let R : ParabolicPoint → ℝ := pressureSplitRemainder p P
  have hbump : ∀ᵐ t ∂(volume.restrict pressureSplitTime),
      ∀ q : Q × ℕ,
        Metric.closedBall (q.1 : Vec3) (CKN.sliceRadius q.2) ⊆ pressureSplitBall →
        ∫ x : Vec3, R ((x,t) : ParabolicPoint) * CKN.spatialLaplacian
            (fun z : Vec3 => CKN.mollifier (d := 3)
              (CKN.sliceRadius q.2) (CKN.sliceRadius_pos q.2)
              (z - (q.1 : Vec3))) x = 0 := by
    rw [ae_all_iff]
    intro q
    by_cases hball : Metric.closedBall (q.1 : Vec3)
        (CKN.sliceRadius q.2) ⊆ pressureSplitBall
    · have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 =>
        CKN.mollifier (d := 3) (CKN.sliceRadius q.2)
          (CKN.sliceRadius_pos q.2) (z - (q.1 : Vec3))) :=
        CKN.contDiff_mollifier_sub (CKN.sliceRadius_pos q.2) (q.1 : Vec3)
      have hψc : HasCompactSupport (fun z : Vec3 =>
        CKN.mollifier (d := 3) (CKN.sliceRadius q.2)
          (CKN.sliceRadius_pos q.2) (z - (q.1 : Vec3))) :=
        CKN.hasCompactSupport_mollifier_sub (CKN.sliceRadius_pos q.2)
          (q.1 : Vec3)
      have hψB : tsupport (fun z : Vec3 => CKN.mollifier (d := 3)
          (CKN.sliceRadius q.2) (CKN.sliceRadius_pos q.2)
          (z - (q.1 : Vec3))) ⊆ pressureSplitBall := by
        rw [CKN.tsupport_mollifier_sub_eq]
        exact hball
      filter_upwards [pressureSplit_remainder_slice_pairing_ae
        hu hDu hpmeas hL2 henergy hp hL3 hgrad hdiv hMomentum hψ hψc hψB]
        with t ht _
      exact ht
    · filter_upwards [] with t ht
      exact False.elim (hball ht)
  have hglobal : ∀ᵐ t ∂(volume.restrict pressureSplitTime),
      MemLp (fun x : Vec3 => R ((x,t) : ParabolicPoint))
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict pressureSplitBall) := by
    have hBallMeas : MeasurableSet pressureSplitBall :=
      (isOpen_vec3Ball 0 1).measurableSet
    have hmeasure : (volume.restrict pressureSplitBall).prod
        (volume.restrict pressureSplitTime) ≤
          (volume : Measure (Vec3 × ℝ)) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
      exact Measure.restrict_le_self
    have hproduct : MemLp (fun z : Vec3 × ℝ =>
        R ((z.1,z.2) : ParabolicPoint)) (ENNReal.ofReal (3 / 2 : ℝ))
        ((volume.restrict pressureSplitBall).prod
          (volume.restrict pressureSplitTime)) := by
      have hR : MemLp (fun z : Vec3 × ℝ =>
          R (parabolicHomeomorph.symm z)) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume : Measure (Vec3 × ℝ)) :=
        pressureSplit_remainder_memLp_product hu hDu henergy hp hL3 hgrad
      simpa only [parabolicHomeomorph_symm_apply] using hR.mono_measure hmeasure
    have hBall : pressureSplitBall = CKN.euclideanBall (0 : Vec3) 1 := by
      simpa only [pressureSplitBall] using
        (CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball
          (by norm_num : (0 : ℝ) < 1)).symm
    rw [hBall] at hproduct
    have hcoeff : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [hcoeff] at hproduct
    have hslices := pressureSlice_memLp_ae (J := pressureSplitTime) R hproduct
    norm_num at hslices ⊢
    simpa only [hBall, ← hcoeff] using hslices
  have hloc : ∀ᵐ t ∂(volume.restrict pressureSplitTime),
      LocallyIntegrableOn
        (fun x : Vec3 => R ((x,t) : ParabolicPoint)) pressureSplitBall volume := by
    filter_upwards [hglobal] with t ht
    have hzero (x : Vec3) (hx : x ∉ pressureSplitBall) :
        R ((x,t) : ParabolicPoint) = 0 := by
      have hnot : ((x,t) : ParabolicPoint) ∉ goodPointDomain := by
        intro hz
        exact hx (by simpa only [goodPointDomain, pressureSplitBall] using hz.1)
      change goodPointDomain.indicator (fun z => p z - P z)
        ((x,t) : ParabolicPoint) = 0
      exact Set.indicator_of_notMem hnot _
    have hEq : pressureSplitBall.indicator (fun x : Vec3 => R ((x,t) : ParabolicPoint)) =
        fun x => R ((x,t) : ParabolicPoint) := by
      funext x
      by_cases hx : x ∈ pressureSplitBall
      · exact Set.indicator_of_mem hx _
      · rw [Set.indicator_of_notMem hx, hzero x hx]
    have hBallMeas : MeasurableSet pressureSplitBall :=
      (isOpen_vec3Ball 0 1).measurableSet
    have hMem : MemLp (fun x : Vec3 => R ((x,t) : ParabolicPoint))
        (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
      exact (memLp_congr_ae (Filter.Eventually.of_forall fun x =>
        congrFun hEq x)).1
        ((memLp_indicator_iff_restrict hBallMeas).2 ht)
    exact (hMem.locallyIntegrable (by norm_num)).locallyIntegrableOn
      pressureSplitBall
  filter_upwards [hbump, hloc] with t ht hloc
  apply blowup_harmonic_of_mollifier_bump_pairings
    (isOpen_vec3Ball 0 1) hQdense hloc
  intro y hy n hn
  have h := ht (⟨y, hy⟩, n) hn
  calc
    ∫ x in pressureSplitBall, R (x,t) * CKN.spatialLaplacian
        (fun z : Vec3 => CKN.mollifier (d := 3) (CKN.sliceRadius n)
          (CKN.sliceRadius_pos n) (z - y)) x =
      ∫ x : Vec3, R (x,t) * CKN.spatialLaplacian
        (fun z : Vec3 => CKN.mollifier (d := 3) (CKN.sliceRadius n)
          (CKN.sliceRadius_pos n) (z - y)) x := by
      apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hts : tsupport (fun z : Vec3 => CKN.mollifier (d := 3)
          (CKN.sliceRadius n) (CKN.sliceRadius_pos n) (z - y)) ⊆
          pressureSplitBall := by
        rw [CKN.tsupport_mollifier_sub_eq]
        exact hn
      have hx' : x ∉ tsupport (fun z : Vec3 => CKN.mollifier (d := 3)
          (CKN.sliceRadius n) (CKN.sliceRadius_pos n) (z - y)) :=
        fun hm => hx (hts hm)
      have hLap : CKN.spatialLaplacian (fun z : Vec3 =>
          CKN.mollifier (d := 3) (CKN.sliceRadius n)
            (CKN.sliceRadius_pos n) (z - y)) x = 0 := by
        simp only [CKN.spatialLaplacian]
        apply Finset.sum_eq_zero
        intro i _
        have hsub : tsupport (CKN.spatialDeriv (fun z : Vec3 =>
            CKN.mollifier (d := 3) (CKN.sliceRadius n)
              (CKN.sliceRadius_pos n) (z - y)) i) ⊆
            tsupport (fun z : Vec3 => CKN.mollifier (d := 3)
              (CKN.sliceRadius n) (CKN.sliceRadius_pos n) (z - y)) :=
          tsupport_fderiv_apply_subset ℝ (CKN.basisVec i)
        rw [CKN.spatialDeriv]
        simp [fderiv_of_notMem_tsupport (𝕜 := ℝ)
          (fun hm => hx' (hsub hm))]
      simp [hLap]
    _ = 0 := h

end ESS

end
