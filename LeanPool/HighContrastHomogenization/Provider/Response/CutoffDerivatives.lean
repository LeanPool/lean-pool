/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.CutoffAdaptedMean

/-!
# High-contrast homogenization: Provider.Response.CutoffDerivatives

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Quantitative adapted-coordinate derivatives

Pulling the physical cutoff back by the grid matrix is the normalized reference
cutoff.  The estimates below therefore control exactly the tensors denoted by
`q ∇φ` and `q² ∇²φ` in the response argument.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

noncomputable section

/-- The reciprocal transition width for the chosen two concentric cubes. -/
theorem adaptedPreYoungCutoff_transitionScale {d : ℕ} [NeZero d] (t : ℤ) :
    2 / (((1 - 1 / (4 * (d : ℝ))) - (1 - 1 / (2 * (d : ℝ)))) *
        cubeRadius (originCube d t)) =
      16 * (d : ℝ) * (3 : ℝ) ^ (-t) := by
  have hd : (d : ℝ) ≠ 0 := by
    exact_mod_cast NeZero.ne d
  have hthree : (3 : ℝ) ≠ 0 := by norm_num
  have hthreepow : (3 : ℝ) ^ t ≠ 0 := zpow_ne_zero t hthree
  unfold cubeRadius
  rw [cubeScaleFactor_originCube]
  rw [show (1 - 1 / (4 * (d : ℝ))) - (1 - 1 / (2 * (d : ℝ))) =
      1 / (4 * (d : ℝ)) by
    field_simp [hd]
    ring]
  rw [zpow_neg]
  field_simp [hd, hthreepow]
  ring

/-- The common second-order coefficient also dominates the sharper gradient
coefficient. -/
theorem adaptedPreYoungCutoff_gradientCoefficient_le_common
    (d : ℕ) [NeZero d] :
    32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound ≤
      1024 * (d : ℝ) ^ 4 *
        (max 1 (max smoothTransitionProfile.derivBound
          smoothTransitionProfile.secondDerivBound)) ^ 2 := by
  let D : ℝ := d
  let B : ℝ := smoothTransitionProfile.derivBound
  let K : ℝ := max 1 (max smoothTransitionProfile.derivBound
    smoothTransitionProfile.secondDerivBound)
  have hD : 1 ≤ D := by
    dsimp [D]
    exact_mod_cast (NeZero.one_le : 1 ≤ d)
  have hD_nonneg : 0 ≤ D := le_trans (by norm_num) hD
  have hB_nonneg : 0 ≤ B := by
    exact smoothTransitionProfile.derivBound_nonneg
  have hK_one : 1 ≤ K := by
    exact le_max_left _ _
  have hB_K : B ≤ K := by
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hDsq : 1 ≤ D ^ 2 := by
    nlinarith only [hD]
  have hDpow : D ^ 2 ≤ D ^ 4 := by
    calc
      D ^ 2 = D ^ 2 * 1 := by ring
      _ ≤ D ^ 2 * D ^ 2 := mul_le_mul_of_nonneg_left hDsq (sq_nonneg D)
      _ = D ^ 4 := by ring
  have hKpow : K ≤ K ^ 2 := by
    nlinarith only [hK_one]
  have hsmall : D ^ 2 * B ≤ D ^ 4 * K ^ 2 :=
    (mul_le_mul_of_nonneg_right hDpow hB_nonneg).trans
      (mul_le_mul_of_nonneg_left (hB_K.trans hKpow) (by positivity))
  dsimp [D, B, K] at hsmall ⊢
  calc
    32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound =
        32 * ((d : ℝ) ^ 2 * smoothTransitionProfile.derivBound) := by ring
    _ ≤ 32 * ((d : ℝ) ^ 4 *
        (max 1 (max smoothTransitionProfile.derivBound
          smoothTransitionProfile.secondDerivBound)) ^ 2) :=
      mul_le_mul_of_nonneg_left hsmall (by norm_num)
    _ ≤ 1024 * ((d : ℝ) ^ 4 *
        (max 1 (max smoothTransitionProfile.derivBound
          smoothTransitionProfile.secondDerivBound)) ^ 2) := by
      have hfactor : 0 ≤ (d : ℝ) ^ 4 *
          (max 1 (max smoothTransitionProfile.derivBound
            smoothTransitionProfile.secondDerivBound)) ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_right
        (show (32 : ℝ) ≤ 1024 by norm_num) hfactor
    _ = 1024 * (d : ℝ) ^ 4 *
        (max 1 (max smoothTransitionProfile.derivBound
          smoothTransitionProfile.secondDerivBound)) ^ 2 := by ring

/-- The adapted-coordinate first derivative has the common dimension-only
bound used for both derivative orders. -/
theorem adaptedPreYoungCutoff_pullback_fderiv_bound {d : ℕ} [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (x : Vec d) :
    ‖fderiv ℝ (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y)) x‖ ≤
      1024 * (d : ℝ) ^ 4 *
        (max 1 (max smoothTransitionProfile.derivBound
          smoothTransitionProfile.secondDerivBound)) ^ 2 *
        (3 : ℝ) ^ (-t) := by
  let Q : TriadicCube d := originCube d t
  let ρ₁ : ℝ := 1 - 1 / (2 * (d : ℝ))
  let ρ₂ : ℝ := 1 - 1 / (4 * (d : ℝ))
  let η : Vec d → ℝ := QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂
  let A : ℝ := cubeAverage Q η
  obtain ⟨hρ₁, hρ₁₂, _hρ₂⟩ := cutoffRadii_spec d
  have hApos : 0 < A := by
    simpa [A, η, Q, ρ₁, ρ₂] using
      adaptedPreYoungCutoff_rawAverage_pos (d := d) t
  have hAinv : 0 ≤ A⁻¹ := inv_nonneg.mpr hApos.le
  have hAinv_le : A⁻¹ ≤ 2 := by
    simpa [A, η, Q, ρ₁, ρ₂] using
      adaptedPreYoungCutoff_inv_rawAverage_le_two (d := d) t
  have hpull : (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y)) =
      fun y => A⁻¹ * η y := by
    funext y
    simpa [A, η, Q, ρ₁, ρ₂] using
      adaptedPreYoungCutoff_pullback_apply hq t y
  have hraw := QuantitativeCubeCutoff.canonicalFun_gradient_bound Q
    hρ₁ hρ₁₂ x
  have hscale : 2 / ((ρ₂ - ρ₁) * cubeRadius Q) =
      16 * (d : ℝ) * (3 : ℝ) ^ (-t) := by
    simpa [Q, ρ₁, ρ₂] using adaptedPreYoungCutoff_transitionScale (d := d) t
  rw [hscale] at hraw
  have hnorm :
      ‖fderiv ℝ (fun y => A⁻¹ * η y) x‖ = A⁻¹ * ‖fderiv ℝ η x‖ := by
    rw [show (fun y => A⁻¹ * η y) = A⁻¹ • η by
      funext y
      exact (smul_eq_mul _ _).symm]
    rw [fderiv_const_smul_field]
    simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hAinv]
  rw [hpull, hnorm]
  calc
    A⁻¹ * ‖fderiv ℝ η x‖ ≤
        2 * ((d : ℝ) * smoothTransitionProfile.derivBound *
          (16 * (d : ℝ) * (3 : ℝ) ^ (-t))) :=
      mul_le_mul hAinv_le hraw (norm_nonneg _) (by positivity)
    _ = (32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound) *
        (3 : ℝ) ^ (-t) := by ring
    _ ≤ (1024 * (d : ℝ) ^ 4 *
        (max 1 (max smoothTransitionProfile.derivBound
          smoothTransitionProfile.secondDerivBound)) ^ 2) *
        (3 : ℝ) ^ (-t) :=
      mul_le_mul_of_nonneg_right
        (adaptedPreYoungCutoff_gradientCoefficient_le_common d)
        (by positivity)

/-- The adapted-coordinate Hessian has the same dimension-only coefficient as
the first derivative. -/
theorem adaptedPreYoungCutoff_pullback_iteratedFDeriv_two_bound
    {d : ℕ} [NeZero d] {q : Mat d} (hq : q.PosDef) (t : ℤ) (x : Vec d) :
    ‖iteratedFDeriv ℝ 2
        (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y)) x‖ ≤
      1024 * (d : ℝ) ^ 4 *
        (max 1 (max smoothTransitionProfile.derivBound
          smoothTransitionProfile.secondDerivBound)) ^ 2 *
        (3 : ℝ) ^ (-2 * t) := by
  let Q : TriadicCube d := originCube d t
  let ρ₁ : ℝ := 1 - 1 / (2 * (d : ℝ))
  let ρ₂ : ℝ := 1 - 1 / (4 * (d : ℝ))
  let η : Vec d → ℝ := QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂
  let A : ℝ := cubeAverage Q η
  let K : ℝ := max 1 (max smoothTransitionProfile.derivBound
    smoothTransitionProfile.secondDerivBound)
  obtain ⟨hρ₁, hρ₁₂, _hρ₂⟩ := cutoffRadii_spec d
  have hApos : 0 < A := by
    simpa [A, η, Q, ρ₁, ρ₂] using
      adaptedPreYoungCutoff_rawAverage_pos (d := d) t
  have hAinv : 0 ≤ A⁻¹ := inv_nonneg.mpr hApos.le
  have hAinv_le : A⁻¹ ≤ 2 := by
    simpa [A, η, Q, ρ₁, ρ₂] using
      adaptedPreYoungCutoff_inv_rawAverage_le_two (d := d) t
  have hηsmooth : ContDiff ℝ (⊤ : ℕ∞) η := by
    simpa [η, Q, ρ₁, ρ₂] using
      QuantitativeCubeCutoff.canonicalFun_smooth Q hρ₁ hρ₁₂
  have hpull : (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y)) =
      fun y => A⁻¹ * η y := by
    funext y
    simpa [A, η, Q, ρ₁, ρ₂] using
      adaptedPreYoungCutoff_pullback_apply hq t y
  have hraw := QuantitativeCubeCutoff.canonicalFun_hessian_bound Q
    hρ₁ hρ₁₂ x
  have hscale : 2 / ((ρ₂ - ρ₁) * cubeRadius Q) =
      16 * (d : ℝ) * (3 : ℝ) ^ (-t) := by
    simpa [Q, ρ₁, ρ₂] using adaptedPreYoungCutoff_transitionScale (d := d) t
  rw [hscale] at hraw
  have hnorm :
      ‖iteratedFDeriv ℝ 2 (fun y => A⁻¹ * η y) x‖ =
        A⁻¹ * ‖iteratedFDeriv ℝ 2 η x‖ := by
    have hiter :
        iteratedFDeriv ℝ 2 (fun y => A⁻¹ * η y) x =
          A⁻¹ • iteratedFDeriv ℝ 2 η x := by
      rw [show (fun y => A⁻¹ * η y) = A⁻¹ • η by
        funext y
        exact (smul_eq_mul _ _).symm]
      rw [iteratedFDeriv_const_smul_apply]
      exact hηsmooth.contDiffAt.of_le (by
        exact WithTop.coe_le_coe.2 (show (2 : ℕ∞) ≤ ⊤ from le_top))
    rw [hiter, norm_smul, Real.norm_eq_abs, abs_of_nonneg hAinv]
  have hzpow : ((3 : ℝ) ^ (-t)) ^ 2 = (3 : ℝ) ^ (-2 * t) := by
    rw [← zpow_natCast]
    rw [← zpow_mul]
    congr 1
    ring
  rw [hpull, hnorm]
  calc
    A⁻¹ * ‖iteratedFDeriv ℝ 2 η x‖ ≤
        2 * (2 * (d : ℝ) ^ 2 *
          (K * (16 * (d : ℝ) * (3 : ℝ) ^ (-t))) ^ 2) :=
      mul_le_mul hAinv_le (by simpa [K, η, ρ₁, ρ₂] using hraw)
        (norm_nonneg _) (by positivity)
    _ = 1024 * (d : ℝ) ^ 4 * K ^ 2 * (3 : ℝ) ^ (-2 * t) := by
      rw [← hzpow]
      ring
    _ = 1024 * (d : ℝ) ^ 4 *
        (max 1 (max smoothTransitionProfile.derivBound
          smoothTransitionProfile.secondDerivBound)) ^ 2 *
        (3 : ℝ) ^ (-2 * t) := by rfl

end

end Response
end HighContrast
end HCPolySupport
