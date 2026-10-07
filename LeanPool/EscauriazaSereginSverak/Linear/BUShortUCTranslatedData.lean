/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortUCLocalZero
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianData
public import LeanPool.EscauriazaSereginSverak.Linear.UCScaleWeak
public import LeanPool.EscauriazaSereginSverak.Linear.UCScaleAE
public import LeanPool.EscauriazaSereginSverak.Linear.BUAffineIntervalHeat

/-!
# Translated data for spatial unique continuation

An affine time change followed by spatial translation places a ball
inside the positive half-space at initial time zero.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The field translated from an interior half-space ball has the
continuity, weak derivatives, quadratic energy, and differential
inequality required by unique continuation (`thm:uc`). -/
theorem bu_short_uc_translated_data
    (M τ δ c₁ R : ℝ) (c : Vec3)
    (hτ : 0 < τ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hend : τ + δ ^ 2 * 2 < 1) (hc₁ : 0 < c₁) (hR : 0 < R)
    (hball : vec3Ball c R ⊆ {x : Vec3 | 0 < x 2})
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico (0 : ℝ) 1))
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
      w Dw D2w Dtw)
    (hL2 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1))),
      vec3EuclideanNorm (ucWeakHeatVector D2w Dtw z) ≤
        c₁ * (Real.sqrt (spatialGradientSq w Dw z) +
          vec3EuclideanNorm (w z)))
    (hgrowth : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
      vec3EuclideanNorm (w z) ≤
        Real.exp (M * vec3EuclideanNorm z.1 ^ 2)) :
    let W := ucScaledField c 1 (buAffineField τ δ w)
    let G := ucScaledDw c 1 (buAffineDw τ δ Dw)
    let H := ucScaledD2w c 1 (buAffineD2w τ δ D2w)
    let T := ucScaledDtw c 1 (buAffineDtw τ δ Dtw)
    ContinuousOn W (vec3Ball 0 R ×ˢ Ico 0 2) ∧
    HasSpaceTimeWeakDerivs (vec3Ball 0 R) (Ioo 0 2) W G H T ∧
    (∫⁻ z in spaceTimeSet (vec3Ball 0 R) (Ioo 0 2),
      ‖W z‖ₑ ^ (2 : ℝ) + ‖G z‖ₑ ^ (2 : ℝ) +
        ‖H z‖ₑ ^ (2 : ℝ) + ‖T z‖ₑ ^ (2 : ℝ)) < ⊤ ∧
    (∀ᵐ z ∂(volume.restrict
      (spaceTimeSet (vec3Ball 0 R) (Ioo 0 2))),
      vec3EuclideanNorm (ucWeakHeatVector H T z) ≤
        (c₁ * δ) * (vec3EuclideanNorm (W z) +
          Real.sqrt (spatialGradientSq W G z))) := by
  let V := buAffineField τ δ w
  let DV := buAffineDw τ δ Dw
  let D2V := buAffineD2w τ δ D2w
  let DtV := buAffineDtw τ δ Dtw
  let W := ucScaledField c 1 V
  let G := ucScaledDw c 1 DV
  let H := ucScaledD2w c 1 D2V
  let T := ucScaledDtw c 1 DtV
  let B := vec3Ball c R
  let K := spaceTimeSet B (Ioo 0 2)
  have hsource : Ioo (τ + δ ^ 2 * 0) (τ + δ ^ 2 * 2) ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    constructor
    · have htτ : τ < t := by simpa only [mul_zero, add_zero] using ht.1
      exact hτ.trans htτ
    · exact ht.2.trans hend
  have hweakSource := bu_weak_restrict_time hsource w Dw D2w Dtw hweak
  have hweakV := bu_affine_weak_derivatives_interval τ δ 0 2 hδ
    w Dw D2w Dtw hweakSource
  have hweakBall : HasSpaceTimeWeakDerivs B (Ioo 0 2)
      V DV D2V DtV :=
    bu_weak_restrict_space_interval measurableSet_Ioo hball
      V DV D2V DtV hweakV
  have hlocalFull := buGaussian_local_quadratic_l2 M w Dw D2w Dtw
    hweak hL2 hgrowth
  have hlocalSource (S : Set ParabolicPoint)
      (hS : S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (τ + δ ^ 2 * 0) (τ + δ ^ 2 * 2)))
      (hSb : Bornology.IsBounded S) :
      (∫⁻ z in S, ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    apply hlocalFull S _ hSb
    intro z hz
    have hz' := hS hz
    exact ⟨hz'.1, hsource hz'.2⟩
  have hKsub : K ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 2) := by
    intro z hz
    exact ⟨hball hz.1, hz.2⟩
  let C : Set ParabolicPoint := parabolicHomeomorph ⁻¹'
    (euclideanClosedBall c R ×ˢ Icc (0 : ℝ) 2)
  have hCcompact : IsCompact C :=
    parabolicHomeomorph.isCompact_preimage.mpr
      ((isCompact_euclideanClosedBall c hR.le).prod isCompact_Icc)
  have hKsubC : K ⊆ C := by
    intro z hz
    change z.1 ∈ euclideanClosedBall c R ∧ z.2 ∈ Icc (0 : ℝ) 2
    exact ⟨(mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR.le).2
        (by simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq,
          vecDot, pow_two] using ((mem_vec3Ball).1 hz.1).le),
      ⟨hz.2.1.le, hz.2.2.le⟩⟩
  have hKb : Bornology.IsBounded K := hCcompact.isBounded.subset hKsubC
  have hL2V : (∫⁻ z in K,
      ‖V z‖ₑ ^ (2 : ℝ) + ‖DV z‖ₑ ^ (2 : ℝ) +
        ‖D2V z‖ₑ ^ (2 : ℝ) + ‖DtV z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    bu_short_uc_affine_l2 τ δ 0 2 hδ hδ1 w Dw D2w Dtw
      hweakSource hlocalSource K hKsub hKb
  have hweakW : HasSpaceTimeWeakDerivs (vec3Ball 0 R)
      (Ioo 0 2) W G H T := by
    have hweakBall' : HasSpaceTimeWeakDerivs
        (vec3Ball c (1 * R)) (Ioo 0 (1 ^ 2 * 2)) V DV D2V DtV := by
      simpa only [B, one_mul, one_pow] using hweakBall
    have hL2V' : (∫⁻ z in spaceTimeSet
        (vec3Ball c (1 * R)) (Ioo 0 (1 ^ 2 * 2)),
          ‖V z‖ₑ ^ (2 : ℝ) + ‖DV z‖ₑ ^ (2 : ℝ) +
            ‖D2V z‖ₑ ^ (2 : ℝ) + ‖DtV z‖ₑ ^ (2 : ℝ)) < ⊤ := by
      simpa only [B, K, one_mul, one_pow] using hL2V
    simpa only [W, G, H, T, one_mul, one_pow] using
      (uc_scaled_weak_derivatives c 1 R (by norm_num) (by norm_num)
        V DV D2V DtV hweakBall' hL2V')
  have hL2W : (∫⁻ z in spaceTimeSet (vec3Ball 0 R) (Ioo 0 2),
      ‖W z‖ₑ ^ (2 : ℝ) + ‖G z‖ₑ ^ (2 : ℝ) +
        ‖H z‖ₑ ^ (2 : ℝ) + ‖T z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    simpa only [W, G, H, T, B, K, one_mul, one_pow,
      ucCylinder] using
      (uc_scaled_l2_data c R 2 1 R (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) V DV D2V DtV hweakBall hL2V)
  have hineqV := bu_affine_weak_heat_ae_bound_interval
    τ δ 0 2 c₁ hδ hδ1 hc₁.le hsource
    w Dw D2w Dtw hineq
  have hineqBall : ∀ᵐ z ∂(volume.restrict K),
      vec3EuclideanNorm (ucWeakHeatVector D2V DtV z) ≤
        (c₁ * δ) * (vec3EuclideanNorm (V z) +
          Real.sqrt (spatialGradientSq V DV z)) := by
    have h := ae_restrict_of_ae_restrict_of_subset hKsub hineqV
    simpa only [V, DV, D2V, DtV, add_comm] using h
  have hineqW : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet (vec3Ball 0 R) (Ioo 0 2))),
      vec3EuclideanNorm (ucWeakHeatVector H T z) ≤
        (c₁ * δ) * (vec3EuclideanNorm (W z) +
          Real.sqrt (spatialGradientSq W G z)) := by
    have h := uc_scaled_weak_heat_ae_bound c 1 R (c₁ * δ)
      (by norm_num) (by norm_num) (mul_pos hc₁ hδ).le
      V DV D2V DtV (by
        simpa only [K, B, one_mul, one_pow] using hineqBall)
    simpa only [W, G, H, T, one_mul, one_pow, mul_one,
      ucCylinder] using h
  have hmapCont : Continuous (fun z : ParabolicPoint =>
      buAffinePoint τ δ (ucScaledPoint c 1 z)) := by
    apply (buAffinePoint_continuous τ δ).comp
    have hs : Continuous (fun z : ParabolicPoint => c + z.1) :=
      continuous_const.add continuous_fst_parabolicPoint
    have ht : Continuous (fun z : ParabolicPoint => z.2) :=
      continuous_snd_parabolicPoint
    have h := continuous_prod_to_parabolicPoint.comp (hs.prodMk ht)
    convert h using 1
    funext z
    apply Prod.ext
    · simp [ucScaledPoint]
      rfl
    · simp [ucScaledPoint]
      rfl
  have hmapDomain : ∀ z ∈ vec3Ball 0 R ×ˢ Ico (0 : ℝ) 2,
      buAffinePoint τ δ (ucScaledPoint c 1 z) ∈
        {x : Vec3 | 0 < x 2} ×ˢ Ico (0 : ℝ) 1 := by
    intro z hz
    have hx : c + z.1 ∈ B := by
      apply (mem_vec3Ball).2
      simpa only [add_sub_cancel_left, sub_zero] using (mem_vec3Ball).1 hz.1
    have hspace : 0 < (δ • (c + z.1)) 2 := by
      change 0 < δ * (c + z.1) 2
      exact mul_pos hδ (hball hx)
    have htime : 0 ≤ τ + δ ^ 2 * z.2 ∧
        τ + δ ^ 2 * z.2 < 1 := by
      have hsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
      constructor
      · have hnonneg : 0 ≤ δ ^ 2 * z.2 :=
          mul_nonneg hsq.le hz.2.1
        linarith only [hτ, hnonneg]
      · have hlt := mul_lt_mul_of_pos_left hz.2.2 hsq
        linarith only [hlt, hend]
    simp only [buAffinePoint, ucScaledPoint, one_smul,
      one_pow, one_mul]
    exact ⟨hspace, htime⟩
  have hcontW : ContinuousOn W
      (vec3Ball 0 R ×ˢ Ico (0 : ℝ) 2) := by
    change ContinuousOn (w ∘ fun z =>
      buAffinePoint τ δ (ucScaledPoint c 1 z)) _
    exact hcont.comp hmapCont.continuousOn hmapDomain
  exact ⟨hcontW, hweakW, hL2W, hineqW⟩

end ESS
