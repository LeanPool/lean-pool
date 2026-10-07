/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortPointwiseSquare
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortEarlyIndicator

/-!
# Time-localized cutoff error comparison

The singular lower-time derivative appears only in its transition
strip; this support is retained when estimating the squared error.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

attribute [local instance] Classical.propDecidable

/-- Bounds for the two fixed cutoff derivative sizes yield a bound for
the full cutoff heat error with its lower-time support retained. -/
theorem buShortCutoffHeatErrorSize_le_coeff_indicator
    {scale R ε c₁ m h : ℝ} (hscale : 0 < scale)
    (hR : 0 < R) (hε : 0 < ε) (hc₁ : 0 ≤ c₁)
    (hm : 0 ≤ m) (hh : 0 ≤ h)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    {z : ParabolicPoint}
    (hM : buShortSpacePhaseGradientSize scale R hR z ≤ m)
    (hH : buShortSpacePhaseHeatSize scale R hR z ≤ h) :
    buShortCutoffHeatErrorSize scale R hR ε c₁ v Dv z ≤
      ((3 * (c₁ * scale) + 18) * m + h) *
        (vec3EuclideanNorm (v z) +
          Real.sqrt (spatialGradientSq v Dv z)) +
      (if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
        8 / ε * vec3EuclideanNorm (v z) else 0) := by
  let M := buShortSpacePhaseGradientSize scale R hR z
  let H := buShortSpacePhaseHeatSize scale R hR z
  let V := vec3EuclideanNorm (v z)
  let G := Real.sqrt (spatialGradientSq v Dv z)
  let q := 3 * (c₁ * scale)
  let T := if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
    8 / ε * V else 0
  have hV : 0 ≤ V := vec3EuclideanNorm_nonneg _
  have hG : 0 ≤ G := Real.sqrt_nonneg _
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcoef : q * M + H ≤ q * m + h :=
    add_le_add (mul_le_mul_of_nonneg_left hM hq) hH
  have hgrad : 18 * M ≤ 18 * m :=
    mul_le_mul_of_nonneg_left hM (by norm_num)
  have hfirst := mul_le_mul_of_nonneg_right hcoef hV
  have hsecond := mul_le_mul_of_nonneg_right hgrad hG
  have hcross₁ : 0 ≤ (q * m + h) * G := by positivity
  have hcross₂ : 0 ≤ 18 * m * V := by positivity
  have hbase := buShortCutoffHeatErrorSize_le_spacePhase_indicator
    scale R ε c₁ hR hε hscale.le hc₁ v Dv z
  dsimp [M, H, V, G, q, T] at hfirst hsecond hcross₁ hcross₂ hbase ⊢
  split_ifs at hbase ⊢ <;>
    nlinarith only [hfirst, hsecond, hcross₁, hcross₂, hbase]

/-- The phase-gap or shell majorant retains the lower-time transition
indicator. -/
theorem buShortCutoffHeatErrorSize_pointwise_indicator
    {scale R ε c₁ C₁ C₂ : ℝ}
    (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 1 ≤ R) (hε : 0 < ε) (hc₁ : 0 ≤ c₁)
    (hC₁ : 0 ≤ C₁)
    (hN : ∀ scale y : ℝ,
      |deriv (deriv (buShortNormalCutoff scale)) y| ≤ C₁)
    (hC₂ : 0 ≤ C₂)
    (hP : ∀ x : ℝ,
      |deriv (deriv smoothTransitionProfile) x| ≤ C₂)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    {z : ParabolicPoint} (hs : 1 / 2 < z.2) (hs1 : z.2 < 1) :
    buShortCutoffHeatErrorSize scale R (by linarith only [hR]) ε c₁ v Dv z ≤
      (if z ∈ buShortWideGapRegion scale then
        buShortUniformErrorCoeff scale c₁ C₁ C₂ * (1 + z.1 2) ^ 2
      else buShortShellCoeff scale R c₁) *
        (vec3EuclideanNorm (v z) +
          Real.sqrt (spatialGradientSq v Dv z)) +
      (if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
        8 / ε * vec3EuclideanNorm (v z) else 0) := by
  classical
  have hR0 : 0 < R := by linarith only [hR]
  by_cases hgap : z ∈ buShortWideGapRegion scale
  · have hthree : 1 < 3 / scale := by
      apply (lt_div_iff₀ hscale).2
      linarith only [hscale1]
    have hy : 2 < z.1 2 := by
      have hminus : 2 < buShortYMinus scale := by
        dsimp [buShortYMinus]
        linarith only [hthree]
      exact lt_of_lt_of_le hminus hgap.1
    let P := (1 + z.1 2) ^ 2
    let CM := buShortUniformGradientCoeff scale
    let CH := buShortUniformHeatCoeff scale C₁ C₂
    have hM := buShortSpacePhaseGradientSize_uniform
      hscale hR hy hs.le hs1.le
    have hH := buShortSpacePhaseHeatSize_uniform
      hscale hR hy hs hs1.le hC₁ hN hC₂ hP
    have hK : 0 ≤ 12 / buShortB scale :=
      (div_pos (by norm_num) (buShortB_pos hscale)).le
    have hCG : 0 ≤ cutoffGradientConstant :=
      CKN.Foundation.Heat.cutoffGradientConstant_nonneg_global
    have hCS : 0 ≤ cutoffSecondDerivativeConstant :=
      CKN.Foundation.Heat.cutoffSecondDerivativeConstant_nonneg_global
    have hm : 0 ≤ CM * P := by
      dsimp [CM, P, buShortUniformGradientCoeff]
      positivity
    have hh : 0 ≤ CH * P := by
      dsimp [CH, P, buShortUniformHeatCoeff]
      positivity
    have hmain := buShortCutoffHeatErrorSize_le_coeff_indicator
      hscale hR0 hε hc₁ hm hh v Dv hM hH
    simpa only [hgap, ite_true] using
      (show buShortCutoffHeatErrorSize scale R hR0 ε c₁ v Dv z ≤
        buShortUniformErrorCoeff scale c₁ C₁ C₂ * P *
          (vec3EuclideanNorm (v z) +
            Real.sqrt (spatialGradientSq v Dv z)) +
        (if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
          8 / ε * vec3EuclideanNorm (v z) else 0) from by
        convert hmain using 1
        dsimp [buShortUniformErrorCoeff]
        ring)
  · let E := buShortCutoffHeatErrorSize scale R hR0 ε c₁ v Dv z
    by_cases hE : E = 0
    · simp only [hgap, ite_false]
      rw [show buShortCutoffHeatErrorSize scale R hR0 ε c₁ v Dv z = 0 from hE]
      have hcoeff := buShortShellCoeff_nonneg hscale hR0 hc₁
      have hV := vec3EuclideanNorm_nonneg (v z)
      have hG := Real.sqrt_nonneg (spatialGradientSq v Dv z)
      have hεinv : 0 ≤ 8 / ε := by positivity
      split_ifs <;> positivity
    · have habove := buShortCutoffHeatErrorSize_aboveGap_of_not_wideGap
        hscale hscale1 hR0 hε v Dv hs hs1 hE hgap
      have hM := buShortSpacePhaseGradientSize_shell_on_aboveGap
        hscale hscale1 hR0 habove
      have hH := buShortSpacePhaseHeatSize_shell_on_aboveGap
        hscale hscale1 hR0 habove
      have hm : 0 ≤ 3 * (cutoffGradientConstant / (2 * R)) := by
        have hCG := CKN.Foundation.Heat.cutoffGradientConstant_nonneg_global
        positivity
      have hh : 0 ≤ 3 * (cutoffSecondDerivativeConstant / (2 * R) ^ 2) := by
        have hCS := CKN.Foundation.Heat.cutoffSecondDerivativeConstant_nonneg_global
        positivity
      have hmain := buShortCutoffHeatErrorSize_le_coeff_indicator
        hscale hR0 hε hc₁ hm hh v Dv hM hH
      simpa only [hgap, ite_false] using
        (show buShortCutoffHeatErrorSize scale R hR0 ε c₁ v Dv z ≤
          buShortShellCoeff scale R c₁ *
            (vec3EuclideanNorm (v z) +
              Real.sqrt (spatialGradientSq v Dv z)) +
          (if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
            8 / ε * vec3EuclideanNorm (v z) else 0) from by
          convert hmain using 1
          dsimp [buShortShellCoeff]
          ring)

/-- The squared cutoff heat error separates phase, shell, and
time-transition densities with the time support retained. -/
theorem buShortCutoffHeatErrorSize_sq_pointwise_indicator
    {scale R ε c₁ C₁ C₂ : ℝ}
    (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 1 ≤ R) (hε : 0 < ε) (hc₁ : 0 ≤ c₁)
    (hC₁ : 0 ≤ C₁)
    (hN : ∀ scale y : ℝ,
      |deriv (deriv (buShortNormalCutoff scale)) y| ≤ C₁)
    (hC₂ : 0 ≤ C₂)
    (hP : ∀ x : ℝ,
      |deriv (deriv smoothTransitionProfile) x| ≤ C₂)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    {z : ParabolicPoint} (hs : 1 / 2 < z.2) (hs1 : z.2 < 1) :
    buShortCutoffHeatErrorSize scale R (by linarith only [hR]) ε c₁ v Dv z ^ 2 ≤
      4 * (if z ∈ buShortWideGapRegion scale then
          buShortUniformErrorCoeff scale c₁ C₁ C₂ ^ 2 *
            (1 + z.1 2) ^ 4
        else buShortShellCoeff scale R c₁ ^ 2) *
        (vec3EuclideanNorm (v z) ^ 2 +
          spatialGradientSq v Dv z) +
      2 * (if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
        8 / ε * vec3EuclideanNorm (v z) else 0) ^ 2 := by
  let E := buShortCutoffHeatErrorSize scale R
    (by linarith only [hR]) ε c₁ v Dv z
  let A := if z ∈ buShortWideGapRegion scale then
      buShortUniformErrorCoeff scale c₁ C₁ C₂ * (1 + z.1 2) ^ 2
    else buShortShellCoeff scale R c₁
  let V := vec3EuclideanNorm (v z)
  let G := Real.sqrt (spatialGradientSq v Dv z)
  let B := if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
    8 / ε * V else 0
  have hE : 0 ≤ E := by
    dsimp [E, buShortCutoffHeatErrorSize]
    have hM : 0 ≤ buShortCutoffGradientSize scale R
        (by linarith only [hR]) ε z := by
      unfold buShortCutoffGradientSize
      positivity
    have hq : 0 ≤ 3 * (c₁ * scale) := by positivity
    have hV : 0 ≤ vec3EuclideanNorm (v z) := vec3EuclideanNorm_nonneg _
    have hG : 0 ≤ Real.sqrt (spatialGradientSq v Dv z) := Real.sqrt_nonneg _
    positivity
  have hbound : E ≤ A * (V + G) + B :=
    buShortCutoffHeatErrorSize_pointwise_indicator
      hscale hscale1 hR hε hc₁ hC₁ hN hC₂ hP v Dv hs hs1
  have hsq := bu_short_two_term_square hE hbound
  have hGrad : 0 ≤ spatialGradientSq v Dv z := by
    dsimp [spatialGradientSq]
    positivity
  have hGsq : G ^ 2 = spatialGradientSq v Dv z := Real.sq_sqrt hGrad
  rw [hGsq] at hsq
  by_cases hgap : z ∈ buShortWideGapRegion scale
  · simp only [A, hgap, ite_true] at hsq ⊢
    nlinarith only [hsq]
  · simp only [A, hgap, ite_false] at hsq ⊢
    nlinarith only [hsq]

end ESS
