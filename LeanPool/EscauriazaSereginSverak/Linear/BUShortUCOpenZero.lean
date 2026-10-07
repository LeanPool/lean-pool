/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortUCTranslatedData

/-!
# Unique continuation from an open zero region

An open zero neighborhood around an interior point gives integral
flatness after translating that point to the origin.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- A zero neighborhood at an interior point fills a half-space ball
at that time (`lem:bu-small-time`, `thm:uc`). -/
theorem bu_short_uc_zero_from_open_set
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
        Real.exp (M * vec3EuclideanNorm z.1 ^ 2))
    (U : Set ParabolicPoint) (hUopen : IsOpen U)
    (hcenter : (δ • c, τ) ∈ U)
    (hUzero : ∀ q ∈ U, w q = 0) :
    let W := ucScaledField c 1 (buAffineField τ δ w)
    ∀ y ∈ vec3Ball 0 R, W (y, 0) = 0 := by
  let W := ucScaledField c 1 (buAffineField τ δ w)
  let G := ucScaledDw c 1 (buAffineDw τ δ Dw)
  let H := ucScaledD2w c 1 (buAffineD2w τ δ D2w)
  let T := ucScaledDtw c 1 (buAffineDtw τ δ Dtw)
  obtain ⟨hcontW, hweakW, hL2W, hineqW⟩ :=
    bu_short_uc_translated_data M τ δ c₁ R c
      hτ hδ hδ1 hend hc₁ hR hball
      w Dw D2w Dtw hcont hweak hL2 hineq hgrowth
  let F : ParabolicPoint → ParabolicPoint :=
    fun z => buAffinePoint τ δ (ucScaledPoint c 1 z)
  have hFcont : Continuous F := by
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
  have hF0 : F (0, 0) = (δ • c, τ) := by
    apply Prod.ext
    · simp [F, buAffinePoint, ucScaledPoint]
    · simp [F, buAffinePoint, ucScaledPoint]
  have hpreOpen : IsOpen (F ⁻¹' U) := hUopen.preimage hFcont
  have h0pre : ((0 : Vec3), (0 : ℝ)) ∈ F ⁻¹' U := by
    change F (0, 0) ∈ U
    rw [hF0]
    exact hcenter
  obtain ⟨r, hr, hballOpen⟩ :=
    (Metric.isOpen_iff.mp hpreOpen) ((0 : Vec3), (0 : ℝ)) h0pre
  let r₀ := r / 2
  have hr₀ : 0 < r₀ := by dsimp [r₀]; positivity
  have hr₀r : r₀ < r := by dsimp [r₀]; linarith only [hr]
  have hlocal : ∀ z ∈ spaceTimeSet (vec3Ball 0 r₀)
      (Ioo 0 (r₀ ^ 2)), W z = 0 := by
    intro z hz
    have hspace : vec3EuclideanNorm z.1 < r₀ := by
      simpa only [sub_zero] using (mem_vec3Ball).1 hz.1
    have htime : Real.sqrt |z.2| < r₀ := by
      rw [abs_of_pos hz.2.1]
      have hsq : (Real.sqrt z.2) ^ 2 < r₀ ^ 2 := by
        rw [Real.sq_sqrt hz.2.1.le]
        exact hz.2.2
      exact (sq_lt_sq₀ (Real.sqrt_nonneg _) hr₀.le).1 hsq
    have hdist : dist z (show ParabolicPoint from
        ((0 : Vec3), (0 : ℝ))) < r := by
      rw [dist_eq_parabolicDist]
      change max (vec3EuclideanNorm (z.1 - 0))
        (Real.sqrt |z.2 - 0|) < r
      simpa only [sub_zero] using
        (max_lt (hspace.trans hr₀r) (htime.trans hr₀r))
    have hzU : F z ∈ U := hballOpen (Metric.mem_ball.mpr hdist)
    exact hUzero (F z) hzU
  have hzero : W (0, 0) = 0 := by
    change w (F (0, 0)) = 0
    rw [hF0]
    exact hUzero _ hcenter
  exact bu_short_uc_propagate_local_zero R 2 (c₁ * δ)
    hR (by norm_num) (mul_pos hc₁ hδ)
    W G H T hcontW hweakW hL2W hineqW
    hzero r₀ hr₀ hlocal

end ESS
