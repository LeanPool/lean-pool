/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCInitialBall

/-!
# Geometry of the Gaussian rescaling

The translated parabolic cylinder used in `lem:uc-gaussian` stays inside
the source cylinder.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The output-point conditions of `lem:uc-gaussian` give the scaled radius
and the source-cylinder inclusion inequalities. -/
theorem uc_gaussian_scale_geometry
    (R T γ t : ℝ) (hT : 0 < T) (hγ' : γ < 3 / 16)
    (x₀ x : Vec3) (ht : 0 < t) (ht' : t ≤ γ * T)
    (hx : vec3EuclideanNorm (x - x₀) ≤
      (3 / 8) * Real.sqrt (2 / 100) * R)
    (hd : (16 / 100) * t ≤ vec3EuclideanNorm (x - x₀) ^ 2) :
    let scale := Real.sqrt (2 * t)
    let X := (Real.sqrt (2 / 100))⁻¹ • (x - x₀)
    let ρ := 2 * vec3EuclideanNorm X / scale
    4 ≤ ρ ∧ scale * ρ ≤ 3 * R / 4 ∧ 2 * scale ^ 2 ≤ 3 * T / 4 := by
  dsimp
  let μ : ℝ := Real.sqrt (2 / 100)
  let sc : ℝ := Real.sqrt (2 * t)
  let d : ℝ := vec3EuclideanNorm (x - x₀)
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hsc : 0 < sc := by dsimp [sc]; positivity
  have hμsq : μ ^ 2 = 1 / 50 := by dsimp [μ]; norm_num
  have hscsq : sc ^ 2 = 2 * t := by dsimp [sc]; rw [Real.sq_sqrt (by positivity)]
  have hdnn : 0 ≤ d := vec3EuclideanNorm_nonneg _
  have hX : vec3EuclideanNorm (μ⁻¹ • (x - x₀)) = d / μ := by
    rw [vec3EuclideanNorm_smul, abs_of_pos (inv_pos.mpr hμ)]
    simp only [d, inv_mul_eq_div]
  have hρ : 2 * vec3EuclideanNorm (μ⁻¹ • (x - x₀)) / sc =
      2 * d / (μ * sc) := by
    rw [hX]
    ring
  rw [show Real.sqrt (2 / 100 : ℝ) = μ from rfl,
    show Real.sqrt (2 * t) = sc from rfl, hρ]
  have hμsc : 0 < μ * sc := mul_pos hμ hsc
  have hρlower : 4 * μ * sc ≤ 2 * d := by
    by_contra hnot
    have hstrict : 2 * d < 4 * μ * sc := lt_of_not_ge hnot
    have hsq : (2 * d) ^ 2 < (4 * μ * sc) ^ 2 := by
      exact (sq_lt_sq₀ (by positivity) (by positivity)).2 hstrict
    have hbound : (16 / 100 : ℝ) * t ≤ d ^ 2 := hd
    have hpow : (4 * μ * sc) ^ 2 = 16 * (1 / 50 : ℝ) * (2 * t) := by
      calc
        _ = 16 * μ ^ 2 * sc ^ 2 := by ring
        _ = _ := by rw [hμsq, hscsq]
    rw [hpow] at hsq
    nlinarith only [hsq, hbound]
  have htime : 2 * sc ^ 2 ≤ 3 * T / 4 := by
    have hγT := mul_lt_mul_of_pos_right hγ' hT
    rw [hscsq]
    linarith only [ht', hγT]
  refine ⟨?_, ?_, htime⟩
  · apply (le_div_iff₀ hμsc).2
    nlinarith only [hρlower]
  · have hx' : d ≤ (3 / 8) * μ * R := hx
    have hupper : 2 * d ≤ (3 / 4) * μ * R := by
      nlinarith only [hx']
    have hnum : sc * (2 * d / (μ * sc)) = 2 * d / μ := by
      field_simp
    rw [hnum]
    apply (div_le_iff₀ hμ).2
    nlinarith only [hupper]

end ESS
