/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortUCOpenZero
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCurvedGeometry

/-!
# Filling the short-time half-space

Unique continuation propagates the positive-phase zero set to every
interior point of each fixed time slice.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Vanishing in the positive-phase region propagates throughout the
short-time half-space cylinder (`lem:bu-small-time`). -/
theorem bu_short_fill_halfspace_from_positive
    (M scale c₁ : ℝ) (hscale : 0 < scale)
    (hscaleHalf : scale ≤ 1 / 2) (hc₁ : 0 < c₁)
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
    (hpositive : ∀ z ∈ buShortPositivePhaseRegion scale,
      buAffineField (-scale ^ 2 / 2) scale w z = 0) :
    ∀ y : Vec3, 0 < y 2 → ∀ s : ℝ, 1 / 2 < s → s < 1 →
      buAffineField (-scale ^ 2 / 2) scale w (y, s) = 0 := by
  intro y hy s hs hs1
  obtain ⟨c, R, hR, hyBall, hball, hphase⟩ :=
    bu_short_positive_phase_ball (scale := scale) hs hs1 y hy
  have hcBall : c ∈ vec3Ball c R := by
    simpa only [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero] using hR
  have hcpos : 0 < c 2 := hball hcBall
  have hphasePos : 0 < buShortF (c 2) s - buShortB scale :=
    sub_pos.mpr hphase
  have hYplus : buShortYPlus scale < c 2 :=
    buShort_positive_phase_above_transition hscale hcpos.le
      hs.le hs1.le hphasePos
  have hY2 : 2 < buShortYPlus scale := by
    have hdiv : 6 ≤ 3 / scale :=
      (le_div_iff₀ hscale).2 (by nlinarith only [hscaleHalf])
    dsimp [buShortYPlus]
    linarith only [hdiv]
  have hc2 : 2 < c 2 := hY2.trans hYplus
  have hcenterPos : ((c, s) : ParabolicPoint) ∈
      buShortPositivePhaseRegion scale := by
    refine ⟨hc2, hs, hs1, ?_⟩
    rw [buShortFExt_eq hc2.le hs.le]
    exact hphase
  let e := buAffineParabolicHomeomorph (-scale ^ 2 / 2) scale hscale
  let U : Set ParabolicPoint := e '' buShortPositivePhaseRegion scale
  have hUopen : IsOpen U :=
    e.isOpenMap _ (buShortPositivePhaseRegion_isOpen scale)
  have hUzero : ∀ q ∈ U, w q = 0 := by
    intro q hq
    obtain ⟨z, hz, rfl⟩ := hq
    rw [buAffineParabolicHomeomorph_eq]
    exact hpositive z hz
  let τ := scale ^ 2 * (s - 1 / 2)
  have hτ : 0 < τ := by
    dsimp [τ]
    exact mul_pos (sq_pos_of_pos hscale) (sub_pos.mpr hs)
  have hscale1 : scale ≤ 1 := by linarith only [hscaleHalf]
  have hsqle : scale ^ 2 ≤ 1 / 4 := by
    have h := pow_le_pow_left₀ hscale.le hscaleHalf 2
    norm_num at h
    exact h
  have hend : τ + scale ^ 2 * 2 < 1 := by
    have hsbound : s + 3 / 2 < 5 / 2 := by linarith only [hs1]
    have hsqpos : 0 < scale ^ 2 := sq_pos_of_pos hscale
    calc
      τ + scale ^ 2 * 2 = scale ^ 2 * (s + 3 / 2) := by dsimp [τ]; ring
      _ < scale ^ 2 * (5 / 2) := mul_lt_mul_of_pos_left hsbound hsqpos
      _ ≤ (1 / 4 : ℝ) * (5 / 2) :=
        mul_le_mul_of_nonneg_right hsqle (by norm_num)
      _ < 1 := by norm_num
  have hcenter : (scale • c, τ) ∈ U := by
    refine ⟨(c, s), hcenterPos, ?_⟩
    rw [buAffineParabolicHomeomorph_eq]
    apply Prod.ext
    · rfl
    · dsimp [buAffinePoint, τ]
      ring
  have hUC := bu_short_uc_zero_from_open_set M τ scale c₁ R c
    hτ hscale hscale1 hend hc₁ hR hball
    w Dw D2w Dtw hcont hweak hL2 hineq hgrowth
    U hUopen hcenter hUzero
  have hy0 : y - c ∈ vec3Ball 0 R := by
    simpa only [mem_vec3Ball, sub_zero] using hyBall
  have hzero := hUC (y - c) hy0
  have hpoint : buAffinePoint τ scale
      (ucScaledPoint c 1 ((y - c, 0) : ParabolicPoint)) =
        buAffinePoint (-scale ^ 2 / 2) scale ((y, s) : ParabolicPoint) := by
    apply Prod.ext
    · simp only [buAffinePoint, ucScaledPoint, one_smul]
      congr 1
      abel
    · simp only [buAffinePoint, ucScaledPoint, one_pow,
        mul_zero, add_zero]
      dsimp [τ]
      ring
  simpa only [buAffineField, ucScaledField, hpoint] using hzero

end ESS
