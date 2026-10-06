/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianScaledData
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianTimeShift
public import LeanPool.EscauriazaSereginSverak.Linear.UCRestriction

/-!
# Data on the shifted Gaussian cylinder

The time shift in `lem:bu-gaussian` moves the rescaled solution away from the
singular initial face of the Gaussian Carleman weight.
-/

public section


open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The rescaled field after the positive-time translation in
`lem:bu-gaussian`. -/
@[expose] def buGaussianShiftedField (σ : ℝ) (v : ParabolicPoint → Vec3) :
    ParabolicPoint → Vec3 :=
  fun z => v ((buGaussianTimeShiftPoint σ).symm z)

/-- The first derivative after time translation. -/
@[expose] def buGaussianShiftedDw (σ : ℝ) (Dv : ParabolicPoint → Fin 3 → Vec3) :
    ParabolicPoint → Fin 3 → Vec3 :=
  fun z i j => Dv ((buGaussianTimeShiftPoint σ).symm z) i j

/-- The second derivative after time translation. -/
@[expose] def buGaussianShiftedD2w (σ : ℝ)
    (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3) :
    ParabolicPoint → Fin 3 → Fin 3 → Vec3 :=
  fun z i j k => D2v ((buGaussianTimeShiftPoint σ).symm z) i j k

/-- The time derivative after time translation. -/
@[expose] def buGaussianShiftedDtw (σ : ℝ) (Dtv : ParabolicPoint → Vec3) :
    ParabolicPoint → Vec3 :=
  fun z i => Dtv ((buGaussianTimeShiftPoint σ).symm z) i

private theorem buGaussian_shifted_growth_on_cylinder
    (x : Vec3) (scale ρ σ A : ℝ) (w : ParabolicPoint → Vec3)
    (hA : 0 ≤ A) (hscale : 0 ≤ scale)
    (hspace : ∀ y : Vec3, vec3EuclideanNorm y < ρ →
      1 < (x + scale • y) 2)
    (htime : ∀ s : ℝ, σ < s → s < 2 →
      0 < scale ^ 2 * (s - σ) ∧ scale ^ 2 * (s - σ) < 1)
    (hgrowth : ∀ z ∈ buHalfCylinder,
      vec3EuclideanNorm (w z) ≤ Real.exp (A * vec3EuclideanNorm z.1 ^ 2)) :
    ∀ z ∈ spaceTimeSet (vec3Ball 0 ρ) (Ioo σ 2),
      vec3EuclideanNorm (buGaussianShiftedField σ (ucScaledField x scale w) z) ≤
        Real.exp (2 * A * vec3EuclideanNorm x ^ 2 +
          2 * A * scale ^ 2 * vec3EuclideanNorm z.1 ^ 2) := by
  intro z hz
  rcases hz with ⟨hy, hs⟩
  have hy' : vec3EuclideanNorm z.1 < ρ := by
    simpa only [mem_vec3Ball, sub_zero] using hy
  have hphysical := htime z.2 hs.1 hs.2
  have hsource : ucScaledPoint x scale (z.1, z.2 - σ) ∈ buHalfCylinder := by
    change 0 < (x + scale • z.1) 2 ∧
      0 < scale ^ 2 * (z.2 - σ) ∧ scale ^ 2 * (z.2 - σ) < 1
    exact ⟨by linarith only [hspace z.1 hy'], hphysical⟩
  have hpoint := hgrowth _ hsource
  have hpoint' : vec3EuclideanNorm
      (w (buGaussianScaledPoint x scale 0 (z.1, z.2 - σ))) ≤
      Real.exp (A * vec3EuclideanNorm
        (buGaussianScaledPoint x scale 0 (z.1, z.2 - σ)).1 ^ 2) := by
    simpa [ucScaledPoint, buGaussianScaledPoint] using hpoint
  have hrescale := buGaussian_rescaling_growth A scale x z.1 (z.2 - σ)
    0 w hA hscale hpoint'
  simpa [buGaussianShiftedField, ucScaledField, ucScaledPoint,
    buGaussianScaledPoint, buGaussian_timeShift_point_symm_apply] using hrescale

private theorem continuousOn_after_timeShift
    {B : Set Vec3} (σ : ℝ) (hσpos : 0 < σ)
    {f : ParabolicPoint → Vec3}
    (hcont : ContinuousOn f (B ×ˢ Ico (0 : ℝ) 2)) :
    ContinuousOn (fun z => f ((buGaussianTimeShiftPoint σ).symm z))
      (B ×ˢ Ico σ 2) := by
  have hTinv : Continuous (buGaussianTimeShiftPoint σ).symm :=
    (buGaussianTimeShiftPoint σ).symm.continuous
  change ContinuousOn (fun z => f ((buGaussianTimeShiftPoint σ).symm z))
    (B ×ˢ Ico σ 2)
  apply hcont.comp hTinv.continuousOn
  intro z hz
  have htime : ((buGaussianTimeShiftPoint σ).symm z).2 = z.2 - σ := by
    rw [buGaussian_timeShift_point_symm_apply]
  refine ⟨hz.1, ?_⟩
  rw [htime]
  constructor <;> linarith only [hz.2.1, hz.2.2, hσpos]

/-- The local source hypotheses give weak derivatives, finite quadratic data,
and the differential inequality on the shifted Gaussian cylinder. -/
theorem buGaussian_shifted_rescaled_data
    (c₁ A : ℝ) (hc₁ : 0 < c₁) (hA : 0 ≤ A)
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
    let σ := 1 / 6
    HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo σ 2)
      (buGaussianShiftedField σ (ucScaledField x scale w))
      (buGaussianShiftedDw σ (ucScaledDw x scale Dw))
      (buGaussianShiftedD2w σ (ucScaledD2w x scale D2w))
      (buGaussianShiftedDtw σ (ucScaledDtw x scale Dtw)) ∧
    (∫⁻ z in spaceTimeSet (vec3Ball 0 ρ) (Ioo σ 2),
      ‖buGaussianShiftedField σ (ucScaledField x scale w) z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedDw σ (ucScaledDw x scale Dw) z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedD2w σ (ucScaledD2w x scale D2w) z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedDtw σ (ucScaledDtw x scale Dtw) z‖ₑ ^ (2 : ℝ)) < ⊤ ∧
    (∀ᵐ z ∂(volume.restrict
      (spaceTimeSet (vec3Ball 0 ρ) (Ioo σ 2))),
      vec3EuclideanNorm (ucWeakHeatVector
        (buGaussianShiftedD2w σ (ucScaledD2w x scale D2w))
        (buGaussianShiftedDtw σ (ucScaledDtw x scale Dtw)) z) ≤
        c₁ * scale *
          (vec3EuclideanNorm
              (buGaussianShiftedField σ (ucScaledField x scale w) z) +
            Real.sqrt (spatialGradientSq
              (buGaussianShiftedField σ (ucScaledField x scale w))
              (buGaussianShiftedDw σ (ucScaledDw x scale Dw)) z))) ∧
    ContinuousOn (buGaussianShiftedField σ (ucScaledField x scale w))
      (vec3Ball 0 ρ ×ˢ Ico σ 2) ∧
    (∀ y : Vec3, y ∈ vec3Ball 0 ρ →
      buGaussianShiftedField σ (ucScaledField x scale w) (y, σ) = 0) ∧
    (∀ z ∈ spaceTimeSet (vec3Ball 0 ρ) (Ioo σ 2),
      vec3EuclideanNorm
        (buGaussianShiftedField σ (ucScaledField x scale w) z) ≤
        Real.exp (2 * A * vec3EuclideanNorm x ^ 2 +
          2 * A * (Real.sqrt (3 * t)) ^ 2 * vec3EuclideanNorm z.1 ^ 2)) := by
  dsimp
  let scale : ℝ := Real.sqrt (3 * t)
  let ρ : ℝ := (x 2 - 1) / scale
  let σ : ℝ := 1 / 6
  have hgeom := buGaussian_rescaling_geometry x t γ ht (by
    have : (1 / 12 : ℝ) ≤ 1 / 12 := le_rfl
    exact le_trans hγ this) htγ
  have hscalePos : 0 < scale := hgeom.1
  have hscaleLe : scale ≤ 1 := by
    simpa [scale] using le_of_lt hgeom.2.1
  have hσpos : 0 < σ := by norm_num [σ]
  have hσlt : σ < 2 := by norm_num [σ]
  obtain ⟨hweak0, hL20, hcont0, hzero0, hineq0⟩ :=
    buGaussian_rescaled_data c₁ A hc₁ w Dw D2w Dtw hcont hzero
      hderiv hL2 hineq hgrowth x t γ hx₃ ht hγ htγ
  let B : Set Vec3 := vec3Ball 0 ρ
  let I₀ : Set ℝ := Ioo 0 (2 - σ)
  let I₁ : Set ℝ := Ioo σ 2
  let S₀ : Set ParabolicPoint := spaceTimeSet B I₀
  let S₁ : Set ParabolicPoint := spaceTimeSet B I₁
  have hI₀sub : I₀ ⊆ Ioo 0 2 := by
    intro s hs
    exact ⟨hs.1, lt_of_lt_of_le hs.2 (by dsimp [σ]; norm_num)⟩
  have hcont0' : ContinuousOn (ucScaledField x scale w) (B ×ˢ Ioo 0 2) :=
    hcont0.mono (fun z hz => ⟨hz.1, ⟨hz.2.1.le, hz.2.2⟩⟩)
  have hrestricted := uc_restrict_data (c₁ * scale) B B I₀ (Ioo 0 2)
    (ucScaledField x scale w) (ucScaledDw x scale Dw)
    (ucScaledD2w x scale D2w) (ucScaledDtw x scale Dtw)
    (isOpen_vec3Ball 0 ρ) isOpen_Ioo subset_rfl hI₀sub hcont0'
    hweak0 hL20 hineq0
  have hweak₀ : HasSpaceTimeWeakDerivs B I₀
      (ucScaledField x scale w) (ucScaledDw x scale Dw)
      (ucScaledD2w x scale D2w) (ucScaledDtw x scale Dtw) := hrestricted.2.1
  have hL2₀ : (∫⁻ z in S₀,
      ‖(ucScaledField x scale w) z‖ₑ ^ (2 : ℝ) +
        ‖(ucScaledDw x scale Dw) z‖ₑ ^ (2 : ℝ) +
        ‖(ucScaledD2w x scale D2w) z‖ₑ ^ (2 : ℝ) +
        ‖(ucScaledDtw x scale Dtw) z‖ₑ ^ (2 : ℝ)) < ⊤ := hrestricted.2.2.1
  have hineq₀ : ∀ᵐ z ∂(volume.restrict S₀),
      vec3EuclideanNorm (ucWeakHeatVector (ucScaledD2w x scale D2w)
        (ucScaledDtw x scale Dtw) z) ≤
        c₁ * scale * (vec3EuclideanNorm (ucScaledField x scale w z) +
          Real.sqrt (spatialGradientSq (ucScaledField x scale w)
            (ucScaledDw x scale Dw) z)) := hrestricted.2.2.2
  have hshiftweak0 := buGaussian_timeShift_weak_derivatives hweak₀
  have hshiftweak : HasSpaceTimeWeakDerivs B I₁
      (buGaussianShiftedField σ (ucScaledField x scale w))
      (buGaussianShiftedDw σ (ucScaledDw x scale Dw))
      (buGaussianShiftedD2w σ (ucScaledD2w x scale D2w))
      (buGaussianShiftedDtw σ (ucScaledDtw x scale Dtw)) := hshiftweak0
  have hS₀sub : S₀ ⊆ ucCylinder ρ := by
    intro z hz
    rcases hz with ⟨hzx, hzt⟩
    exact ⟨hzx, hI₀sub hzt⟩
  let F : ParabolicPoint → ℝ≥0∞ := fun z =>
    ‖(ucScaledField x scale w) z‖ₑ ^ (2 : ℝ) +
      ‖(ucScaledDw x scale Dw) z‖ₑ ^ (2 : ℝ) +
      ‖(ucScaledD2w x scale D2w) z‖ₑ ^ (2 : ℝ) +
      ‖(ucScaledDtw x scale Dtw) z‖ₑ ^ (2 : ℝ)
  have hF₀ : (∫⁻ z in S₀, F z) < ⊤ := by
    apply (lintegral_mono_set hS₀sub).trans_lt
    simpa only [F] using hL20
  let T := buGaussianTimeShiftPoint σ
  have himage₁ : T '' S₀ = S₁ := by
    simpa [T, S₀, S₁, B] using buGaussian_timeShift_image ρ σ
  have hshiftIntegral : (∫⁻ z in S₁, F (T.symm z)) = ∫⁻ z in S₀, F z := by
    have htrans := (buGaussian_timeShift_measurePreserving σ).setLIntegral_comp_emb
      T.measurableEmbedding (fun z => F (T.symm z)) S₀
    calc
      _ = ∫⁻ z in T '' S₀, F (T.symm z) := by rw [himage₁]
      _ = ∫⁻ z in S₀, F z := by
        change (∫⁻ z in (buGaussianTimeShiftPoint σ) '' S₀, F (T.symm z)) = _
        simpa only [T, Homeomorph.symm_apply_apply] using htrans.symm
  have hL2₁ : (∫⁻ z in S₁,
      ‖buGaussianShiftedField σ (ucScaledField x scale w) z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedDw σ (ucScaledDw x scale Dw) z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedD2w σ (ucScaledD2w x scale D2w) z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedDtw σ (ucScaledDtw x scale Dtw) z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    rw [show (fun z =>
        ‖buGaussianShiftedField σ (ucScaledField x scale w) z‖ₑ ^ (2 : ℝ) +
          ‖buGaussianShiftedDw σ (ucScaledDw x scale Dw) z‖ₑ ^ (2 : ℝ) +
          ‖buGaussianShiftedD2w σ (ucScaledD2w x scale D2w) z‖ₑ ^ (2 : ℝ) +
          ‖buGaussianShiftedDtw σ (ucScaledDtw x scale Dtw) z‖ₑ ^ (2 : ℝ)) =
        (fun z => F (T.symm z)) by
          funext z
          rfl]
    rw [hshiftIntegral]
    exact hF₀
  have hineq₁raw := buGaussian_timeShift_ae hineq₀
  have hineq₁ : ∀ᵐ z ∂(volume.restrict S₁),
      vec3EuclideanNorm (ucWeakHeatVector
        (buGaussianShiftedD2w σ (ucScaledD2w x scale D2w))
        (buGaussianShiftedDtw σ (ucScaledDtw x scale Dtw)) z) ≤
        c₁ * scale *
          (vec3EuclideanNorm (buGaussianShiftedField σ (ucScaledField x scale w) z) +
            Real.sqrt (spatialGradientSq
              (buGaussianShiftedField σ (ucScaledField x scale w))
              (buGaussianShiftedDw σ (ucScaledDw x scale Dw)) z)) := by
    have hOp (z : ParabolicPoint) :
        ucWeakHeatVector
            (buGaussianShiftedD2w σ (ucScaledD2w x scale D2w))
            (buGaussianShiftedDtw σ (ucScaledDtw x scale Dtw)) z =
          ucWeakHeatVector (ucScaledD2w x scale D2w)
            (ucScaledDtw x scale Dtw) (T.symm z) := by rfl
    have hGradient (z : ParabolicPoint) :
        spatialGradientSq (buGaussianShiftedField σ (ucScaledField x scale w))
            (buGaussianShiftedDw σ (ucScaledDw x scale Dw)) z =
          spatialGradientSq (ucScaledField x scale w)
            (ucScaledDw x scale Dw) (T.symm z) := by rfl
    filter_upwards [hineq₁raw] with z hz
    rw [hOp, hGradient]
    exact hz
  have hshiftCont : ContinuousOn (buGaussianShiftedField σ
      (ucScaledField x scale w)) (B ×ˢ Ico σ 2) := by
    change ContinuousOn (fun z =>
      (ucScaledField x scale w) ((buGaussianTimeShiftPoint σ).symm z))
      (B ×ˢ Ico σ 2)
    exact continuousOn_after_timeShift (B := B) σ hσpos hcont0
  have hshiftZero : ∀ y : Vec3, y ∈ B →
      buGaussianShiftedField σ (ucScaledField x scale w) (y, σ) = 0 := by
    intro y hy
    have htime : (buGaussianTimeShiftPoint σ).symm
        ((y, σ) : ParabolicPoint) = ((y, 0) : ParabolicPoint) := by
      simpa [ParabolicPoint, σ] using
        (buGaussian_timeShift_point_symm_apply σ ((y, σ) : ParabolicPoint))
    change ucScaledField x scale w
      ((buGaussianTimeShiftPoint σ).symm ((y, σ) : ParabolicPoint)) = 0
    rw [htime]
    exact hzero0 y hy
  have hgrowth₁ : ∀ z ∈ S₁,
      vec3EuclideanNorm (buGaussianShiftedField σ (ucScaledField x scale w) z) ≤
        Real.exp (2 * A * vec3EuclideanNorm x ^ 2 +
          2 * A * (Real.sqrt (3 * t)) ^ 2 * vec3EuclideanNorm z.1 ^ 2) := by
    have hgrowth' := buGaussian_shifted_growth_on_cylinder x scale ρ σ A w
      hA (le_of_lt hscalePos)
      (fun y hy => hgeom.2.2.1 y hy)
      (fun s hs1 hs2 => hgeom.2.2.2 s
        hs1
        (by linarith only [hs2]))
      hgrowth
    intro z hz
    have hbound := hgrowth' z hz
    simpa [scale] using hbound
  exact ⟨hshiftweak, hL2₁, hineq₁, hshiftCont, hshiftZero, hgrowth₁⟩

end ESS
