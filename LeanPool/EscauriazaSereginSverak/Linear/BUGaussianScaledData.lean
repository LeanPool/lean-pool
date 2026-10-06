/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianData
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianRescaling
public import LeanPool.EscauriazaSereginSverak.Linear.UCScaleAE
public import LeanPool.EscauriazaSereginSverak.Linear.UCScaleL2
public import LeanPool.EscauriazaSereginSverak.Linear.UCScaleWeak
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics

/-!
# Local data under the Gaussian rescaling

The hypotheses of `lem:bu-gaussian` restrict to the physical cylinder used by
its parabolic change of variables, and then transfer to the normalized ball.
-/

public section


open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

private theorem weakDerivs_restrict_to_spaceTimeSet
    {Ω₀ Ω : Set Vec3} {I₀ I : Set ℝ}
    {w : ParabolicPoint → Vec3} {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtw : ParabolicPoint → Vec3}
    (hΩ₀ : IsOpen Ω₀) (hI₀ : IsOpen I₀)
    (hderiv : HasSpaceTimeWeakDerivs Ω₀ I₀ w Dw D2w Dtw)
    (hsubset : spaceTimeSet Ω I ⊆ spaceTimeSet Ω₀ I₀) :
    HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw := by
  refine ⟨hderiv.1.mono_set hsubset, hderiv.2.1.mono_set hsubset,
    hderiv.2.2.1.mono_set hsubset, hderiv.2.2.2.1.mono_set hsubset, ?_⟩
  intro φ hφ
  have hφsource : φ ∈ spaceTimeTestFunction (V := ℝ) Ω₀ I₀ := by
    refine ⟨hφ.1, hφ.2.1, ?_⟩
    exact hφ.2.2.trans hsubset
  obtain ⟨hsp, hsp2, htm⟩ := hderiv.2.2.2.2 φ hφsource
  have hRestrict {F : ParabolicPoint → ℝ}
      (hF : ∀ z, z ∉ tsupport (show Vec3 × ℝ → ℝ from φ) → F z = 0) :
      (∫ z in spaceTimeSet Ω₀ I₀, F z) =
        ∫ z in spaceTimeSet Ω I, F z := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      ((isOpen_spaceTimeSet Ω₀ I₀ hΩ₀ hI₀).measurableSet) hsubset
    intro z hz
    exact hF z (fun h => hz.2 (hφ.2.2 h))
  have hφzero (z : ParabolicPoint)
      (hz : z ∉ tsupport (show Vec3 × ℝ → ℝ from φ)) : φ z = 0 :=
    image_eq_zero_of_notMem_tsupport
      (f := show Vec3 × ℝ → ℝ from φ) hz
  have hspzero (z : ParabolicPoint)
      (hz : z ∉ tsupport (show Vec3 × ℝ → ℝ from φ)) (j : Fin 3) :
      spatialPartial φ j z = 0 := CKN.spatialPartial_eq_zero_off_tsupport hz j
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    calc
      (∫ z in spaceTimeSet Ω I, w z i * spatialPartial φ j z) =
          ∫ z in spaceTimeSet Ω₀ I₀, w z i * spatialPartial φ j z :=
            (hRestrict (fun z hz => by simp [hspzero z hz j])).symm
      _ = -∫ z in spaceTimeSet Ω₀ I₀, Dw z i j * φ z := hsp i j
      _ = -∫ z in spaceTimeSet Ω I, Dw z i j * φ z := by
        rw [hRestrict (fun z hz => by simp [hφzero z hz])]
  · intro i j k
    calc
      (∫ z in spaceTimeSet Ω I, Dw z i j * spatialPartial φ k z) =
          ∫ z in spaceTimeSet Ω₀ I₀, Dw z i j * spatialPartial φ k z :=
            (hRestrict (fun z hz => by simp [hspzero z hz k])).symm
      _ = -∫ z in spaceTimeSet Ω₀ I₀, D2w z i j k * φ z := hsp2 i j k
      _ = -∫ z in spaceTimeSet Ω I, D2w z i j k * φ z := by
        rw [hRestrict (fun z hz => by simp [hφzero z hz])]
  · intro i
    calc
      (∫ z in spaceTimeSet Ω I, w z i * timePartial φ z) =
          ∫ z in spaceTimeSet Ω₀ I₀, w z i * timePartial φ z :=
            (hRestrict (fun z hz => by
              simp [CKN.timePartial_eq_zero_off_tsupport hz])).symm
      _ = -∫ z in spaceTimeSet Ω₀ I₀, Dtw z i * φ z := htm i
      _ = -∫ z in spaceTimeSet Ω I, Dtw z i * φ z := by
        rw [hRestrict (fun z hz => by simp [hφzero z hz])]

/-- The bounded source data in `lem:bu-gaussian` give the weak derivatives,
finite quadratic data, and heat inequality on the rescaled cylinder. -/
theorem buGaussian_rescaled_data
    (c₁ A : ℝ) (hc₁ : 0 < c₁)
    (w : ParabolicPoint → Vec3) (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3) (Dtw : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w (buHalfSpace ×ˢ Ico 0 1))
    (hzero : ∀ x : Vec3, 0 < x 2 → w (x, 0) = 0)
    (hderiv : HasSpaceTimeWeakDerivs buHalfSpace (Ioo 0 1) w Dw D2w Dtw)
    (hL2 : ∀ S : Set ParabolicPoint, S ⊆ buHalfCylinder → Bornology.IsBounded S →
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) + ‖D2w z‖ₑ ^ (2 : ℝ) +
        ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict buHalfCylinder),
      vec3EuclideanNorm (fun i => Dtw z i + ∑ j, D2w z i j j) ≤
        c₁ * (Real.sqrt (spatialGradientSq w Dw z) + vec3EuclideanNorm (w z)))
    (hgrowth : ∀ z ∈ buHalfCylinder,
      vec3EuclideanNorm (w z) ≤ Real.exp (A * vec3EuclideanNorm z.1 ^ 2))
    (x : Vec3) (t γ : ℝ) (hx₃ : 2 < x 2) (ht : 0 < t)
    (hγ : γ ≤ 1 / 12) (htγ : t < γ) :
    let scale := Real.sqrt (3 * t)
    let ρ := (x 2 - 1) / scale
    HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
      (ucScaledField x scale w) (ucScaledDw x scale Dw)
      (ucScaledD2w x scale D2w) (ucScaledDtw x scale Dtw) ∧
    (∫⁻ z in ucCylinder ρ,
      ‖(ucScaledField x scale w) z‖ₑ ^ (2 : ℝ) +
        ‖(ucScaledDw x scale Dw) z‖ₑ ^ (2 : ℝ) +
        ‖(ucScaledD2w x scale D2w) z‖ₑ ^ (2 : ℝ) +
        ‖(ucScaledDtw x scale Dtw) z‖ₑ ^ (2 : ℝ)) < ⊤ ∧
    ContinuousOn (ucScaledField x scale w)
      (vec3Ball 0 ρ ×ˢ Ico 0 2) ∧
    (∀ y : Vec3, y ∈ vec3Ball 0 ρ →
      (ucScaledField x scale w) (y, 0) = 0) ∧
    (∀ᵐ z ∂(volume.restrict (ucCylinder ρ)),
      vec3EuclideanNorm (ucWeakHeatVector (ucScaledD2w x scale D2w)
        (ucScaledDtw x scale Dtw) z) ≤
        c₁ * scale * (vec3EuclideanNorm ((ucScaledField x scale w) z) +
          Real.sqrt (spatialGradientSq (ucScaledField x scale w)
            (ucScaledDw x scale Dw) z))) := by
  dsimp
  let scale : ℝ := Real.sqrt (3 * t)
  let ρ : ℝ := (x 2 - 1) / scale
  have hgeom := buGaussian_rescaling_geometry x t γ ht hγ htγ
  have hscalePos : 0 < scale := hgeom.1
  have hscale1 : scale ≤ 1 := by
    simpa [scale] using le_of_lt hgeom.2.1
  have hscaleSq : scale ^ 2 = 3 * t := by
    dsimp [scale]
    exact Real.sq_sqrt (by positivity)
  have hballRadius : scale * ρ = x 2 - 1 := by
    dsimp [ρ]
    field_simp
  have hballPos : 0 < scale * ρ := by
    rw [hballRadius]
    linarith only [hx₃]
  let Ω : Set Vec3 := vec3Ball x (scale * ρ)
  let I : Set ℝ := Ioo 0 (scale ^ 2 * 2)
  let Q : Set ParabolicPoint := spaceTimeSet Ω I
  have hQsub : Q ⊆ buHalfCylinder := by
    intro z hz
    rcases hz with ⟨hzx, hzt⟩
    let y : Vec3 := scale⁻¹ • (z.1 - x)
    have hyscale : x + scale • y = z.1 := by
      dsimp [y]
      have hne : scale ≠ 0 := ne_of_gt hscalePos
      simp only [smul_smul, mul_inv_cancel₀ hne, one_smul]
      abel
    have hyNorm : vec3EuclideanNorm y < ρ := by
      have hn : vec3EuclideanNorm (z.1 - x) < scale * ρ := hzx
      rw [show y = scale⁻¹ • (z.1 - x) from rfl,
        vec3EuclideanNorm_smul, abs_of_pos (inv_pos.mpr hscalePos)]
      have hdiv : scale⁻¹ * vec3EuclideanNorm (z.1 - x) =
          vec3EuclideanNorm (z.1 - x) / scale := by ring
      rw [hdiv]
      apply (div_lt_iff₀ hscalePos).2
      calc
        vec3EuclideanNorm (z.1 - x) < scale * ρ := hn
        _ = ρ * scale := by ring
    have hspace : 1 < z.1 2 := by
      rw [← hyscale]
      exact hgeom.2.2.1 y hyNorm
    have htime : 0 < z.2 ∧ z.2 < 1 := by
      constructor
      · exact hzt.1
      · have htop : scale ^ 2 * 2 < 1 := by
          rw [hscaleSq]
          have htγ' := mul_lt_mul_of_pos_left htγ (by norm_num : (0 : ℝ) < 6)
          have hγ' : 6 * γ ≤ 1 / 2 := by nlinarith only [hγ]
          nlinarith only [htγ', hγ']
        exact lt_trans hzt.2 htop
    change z ∈ spaceTimeSet buHalfSpace (Ioo 0 1)
    exact ⟨by change 0 < z.1 2; linarith only [hspace], htime⟩
  have hQbounded : Bornology.IsBounded Q := by
    let Kprod : Set (Vec3 × ℝ) := closure Ω ×ˢ Icc (0 : ℝ) (scale ^ 2 * 2)
    let K : Set ParabolicPoint := parabolicHomeomorph.symm '' Kprod
    have hKprod : IsCompact Kprod :=
      (isCompact_closure_vec3Ball (x := x) hballPos).prod isCompact_Icc
    have hK : IsCompact K := parabolicHomeomorph.symm.isCompact_image.mpr hKprod
    have hQsubK : Q ⊆ K := by
      intro z hz
      rcases hz with ⟨hzx, hzt⟩
      refine ⟨(z.1, z.2), ⟨subset_closure hzx, ⟨hzt.1.le, hzt.2.le⟩⟩, ?_⟩
      rw [← parabolicHomeomorph_apply]
      exact parabolicHomeomorph.left_inv z
    exact hK.isBounded.subset hQsubK
  have hlocal := buGaussian_local_quadratic_l2 A w Dw D2w Dtw hderiv hL2 hgrowth
  have hQL2 := hlocal Q hQsub hQbounded
  have hΩopen : IsOpen Ω := by
    simpa [Ω] using isOpen_vec3Ball x (scale * ρ)
  have hIopen : IsOpen I := isOpen_Ioo
  have hQmeas : MeasurableSet Q := (hΩopen.prod hIopen).measurableSet
  have hsourceOpen : IsOpen buHalfSpace := by
    change IsOpen {y : Vec3 | 0 < y 2}
    exact isOpen_lt continuous_const (continuous_apply 2)
  have hsourceTimeOpen : IsOpen (Ioo (0 : ℝ) 1) := isOpen_Ioo
  have hrestricted : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw :=
    weakDerivs_restrict_to_spaceTimeSet hsourceOpen hsourceTimeOpen hderiv hQsub
  have hineqQ : ∀ᵐ z ∂(volume.restrict Q),
          vec3EuclideanNorm (ucWeakHeatVector D2w Dtw z) ≤
          c₁ * (vec3EuclideanNorm (w z) + Real.sqrt (spatialGradientSq w Dw z)) := by
    have hineq'' : ∀ᵐ z ∂(volume.restrict buHalfCylinder),
        vec3EuclideanNorm (ucWeakHeatVector D2w Dtw z) ≤
          c₁ * (vec3EuclideanNorm (w z) + Real.sqrt (spatialGradientSq w Dw z)) := by
      filter_upwards [hineq] with z hz
      change vec3EuclideanNorm (fun i => Dtw z i + ∑ j, D2w z i j j) ≤ _
      simpa only [add_comm] using hz
    exact ae_restrict_of_ae_restrict_of_subset hQsub hineq''
  have hscaleDeriv := uc_scaled_weak_derivatives x scale ρ hscalePos hscale1
    w Dw D2w Dtw hrestricted hQL2
  have hscaleL2 := uc_scaled_l2_data x (scale * ρ) (scale ^ 2 * 2)
    scale ρ hscalePos hscale1 le_rfl (by
      calc
        2 * scale ^ 2 = scale ^ 2 * 2 := by ring
        _ ≤ scale ^ 2 * 2 := le_rfl)
    w Dw D2w Dtw hrestricted hQL2
  have hscaleIneq := uc_scaled_weak_heat_ae_bound x scale ρ c₁ hscalePos hscale1
    (le_of_lt hc₁) w Dw D2w Dtw hineqQ
  have hscaleCont : ContinuousOn (ucScaledField x scale w)
      (vec3Ball 0 ρ ×ˢ Ico 0 2) := by
    let g : Vec3 × ℝ → Vec3 × ℝ := fun z =>
      (x + scale • z.1, scale ^ 2 * z.2)
    have hg : Continuous g := by fun_prop
    have hmap' : Continuous
        (fun z : ParabolicPoint => parabolicHomeomorph.symm
          (g (parabolicHomeomorph z))) := by
      exact parabolicHomeomorph.symm.continuous.comp
        (hg.comp parabolicHomeomorph.continuous)
    have hmapEq : (fun z : ParabolicPoint => parabolicHomeomorph.symm
        (g (parabolicHomeomorph z))) = ucScaledPoint x scale := by
      funext z
      rfl
    have hmap : Continuous (ucScaledPoint x scale) := by
      rw [← hmapEq]
      exact hmap'
    apply hcont.comp hmap.continuousOn
    intro q hq
    have hspace : 1 < (x + scale • q.1) 2 := by
      have hy : vec3EuclideanNorm q.1 < ρ := by
        have hq' := hq
        change q.1 ∈ vec3Ball 0 ρ ∧ q.2 ∈ Ico 0 2 at hq'
        simpa only [mem_vec3Ball, sub_zero] using hq'.1
      exact hgeom.2.2.1 q.1 hy
    have htime : 0 ≤ scale ^ 2 * q.2 ∧ scale ^ 2 * q.2 < 1 := by
      constructor
      · exact mul_nonneg (sq_nonneg scale) hq.2.1
      · have htop : scale ^ 2 * 2 < 1 := by
          rw [hscaleSq]
          have htγ' := mul_lt_mul_of_pos_left htγ (by norm_num : (0 : ℝ) < 6)
          have hγ' : 6 * γ ≤ 1 / 2 := by nlinarith only [hγ]
          nlinarith only [htγ', hγ']
        have hq' := hq
        change q.1 ∈ vec3Ball 0 ρ ∧ q.2 ∈ Ico 0 2 at hq'
        have hs : q.2 ≤ 2 := le_of_lt hq'.2.2
        nlinarith only [hs, htop, sq_nonneg scale, hq'.2.1]
    have hq' := hq
    change q.1 ∈ vec3Ball 0 ρ ∧ q.2 ∈ Ico 0 2 at hq'
    exact ⟨by change 0 < (x + scale • q.1) 2; linarith only [hspace], htime⟩
  have hscaleZero : ∀ y : Vec3, y ∈ vec3Ball 0 ρ →
      (ucScaledField x scale w) (y, 0) = 0 := by
    intro y hy
    have hy' : vec3EuclideanNorm y < ρ := by
      simpa only [mem_vec3Ball, sub_zero] using hy
    have hspace : 0 < (x + scale • y) 2 := by
      have hge := hgeom.2.2.1 y hy'
      linarith only [hge]
    simpa [ucScaledField, ucScaledPoint] using hzero (x + scale • y) hspace
  exact ⟨hscaleDeriv, hscaleL2, hscaleCont, hscaleZero,
    by simpa only [ucCylinder] using hscaleIneq⟩

end ESS
