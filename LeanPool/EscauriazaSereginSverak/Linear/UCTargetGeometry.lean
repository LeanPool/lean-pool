/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCNormalize

/-!
# Geometry of the Gaussian target box

The target box in `lem:uc-gaussian` is contained in the plateau of the
Carleman cutoff after parabolic dilation.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

private theorem uc_time_weight_le_one_on_target
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    gaussCarlemanTimeWeight s ≤ 1 := by
  have hh : 0 < gaussCarlemanTimeWeight s := by
    unfold gaussCarlemanTimeWeight
    positivity
  have hlog : Real.log (gaussCarlemanTimeWeight s) =
      Real.log s + (1 - s) / 3 := by
    rw [gaussCarlemanTimeWeight,
      Real.log_mul hs.ne' (Real.exp_ne_zero _), Real.log_exp]
  have hslog := Real.log_le_sub_one_of_pos hs
  have hlogle : Real.log (gaussCarlemanTimeWeight s) ≤ 0 := by
    rw [hlog]
    linarith only [hslog, hs1]
  have hexp := Real.exp_le_exp.mpr hlogle
  simpa only [Real.exp_log hh, Real.exp_zero] using hexp

/-- On the normalized target box the Gaussian weight has the lower bound
used to return to the unweighted field (`lem:uc-gaussian`). -/
theorem uc_gaussian_weight_lower_on_target
    (a : ℝ) (ha : 0 ≤ a) (center : Vec3) (z : ParabolicPoint)
    (hz : z ∈ spaceTimeSet (vec3Ball center 1) (Ioo (1 / 2) 1)) :
    Real.exp (-(vec3EuclideanNorm center ^ 2 + 1)) ≤
      ucGaussianWeight a z := by
  have hs : 0 < z.2 := by linarith only [hz.2.1]
  have hs1 : z.2 ≤ 1 := hz.2.2.le
  have hweightPos : 0 < gaussCarlemanTimeWeight z.2 := by
    unfold gaussCarlemanTimeWeight
    positivity
  have hweightLe : gaussCarlemanTimeWeight z.2 ≤ 1 :=
    uc_time_weight_le_one_on_target hs hs1
  have hpow : 1 ≤ gaussCarlemanTimeWeight z.2 ^ (-2 * a) := by
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hweightPos hweightLe (by linarith only [ha])
  have hball : vec3EuclideanNorm (z.1 - center) < 1 :=
    (mem_vec3Ball).1 hz.1
  have htri := vec3EuclideanNorm_add_le (z.1 - center) center
  have heq : z.1 - center + center = z.1 := sub_add_cancel _ _
  rw [heq] at htri
  have hnorm : vec3EuclideanNorm z.1 ^ 2 ≤
      2 * vec3EuclideanNorm center ^ 2 + 2 := by
    have hzn : 0 ≤ vec3EuclideanNorm z.1 := vec3EuclideanNorm_nonneg _
    have hcn : 0 ≤ vec3EuclideanNorm center := vec3EuclideanNorm_nonneg _
    have hdn : 0 ≤ vec3EuclideanNorm (z.1 - center) := vec3EuclideanNorm_nonneg _
    have hdsq : vec3EuclideanNorm (z.1 - center) ^ 2 < 1 := by
      nlinarith only [hball, hdn]
    nlinarith only [htri, hzn, hcn, hdn, hdsq,
      sq_nonneg (vec3EuclideanNorm (z.1 - center) - vec3EuclideanNorm center)]
  have hden : 0 < 4 * z.2 := by linarith only [hs]
  have hden2 : 2 < 4 * z.2 := by linarith only [hz.2.1]
  have hquot : vec3EuclideanNorm z.1 ^ 2 / (4 * z.2) ≤
      vec3EuclideanNorm center ^ 2 + 1 := by
    apply (div_le_iff₀ hden).2
    have hcpos : 0 ≤ vec3EuclideanNorm center ^ 2 + 1 := by positivity
    nlinarith only [hnorm, hden2, hcpos]
  have hexp : Real.exp (-(vec3EuclideanNorm center ^ 2 + 1)) ≤
      Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2)) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg hquot
  calc
    _ ≤ Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2)) := hexp
    _ ≤ ucGaussianWeight a z := by
      unfold ucGaussianWeight
      exact le_mul_of_one_le_left (Real.exp_nonneg _) hpow

/-- The normalized target box lies in the interior region of the Gaussian
cutoff (`lem:uc-gaussian`). -/
theorem uc_target_box_subset_inner
    (x₀ x : Vec3) (scale ρ : ℝ)
    (hscale : 0 < scale) (hρ : 4 ≤ ρ)
    (hρdef : ρ = 2 * vec3EuclideanNorm
      ((Real.sqrt (2 / 100))⁻¹ • (x - x₀)) / scale) :
    spaceTimeSet (vec3Ball (scale⁻¹ • (x - x₀)) 1) (Ioo (1 / 2) 1) ⊆
      ucInnerRegion ρ := by
  let μ : ℝ := Real.sqrt (2 / 100)
  let d : ℝ := vec3EuclideanNorm (x - x₀)
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hμhalf : μ ≤ 1 / 2 := by
    have hμsq : μ ^ 2 = 1 / 50 := by dsimp [μ]; norm_num
    nlinarith only [hμ, hμsq]
  have hd : 0 ≤ d := vec3EuclideanNorm_nonneg _
  have hnormX : vec3EuclideanNorm (μ⁻¹ • (x - x₀)) = d / μ := by
    rw [vec3EuclideanNorm_smul, abs_of_pos (inv_pos.mpr hμ)]
    simp only [d, inv_mul_eq_div]
  have hρeq : ρ = 2 * d / (μ * scale) := by
    rw [hρdef, show Real.sqrt (2 / 100 : ℝ) = μ from rfl, hnormX]
    ring
  have hcenter : vec3EuclideanNorm (scale⁻¹ • (x - x₀)) ≤ ρ / 4 := by
    rw [vec3EuclideanNorm_smul, abs_of_pos (inv_pos.mpr hscale)]
    have hρmul : ρ * (μ * scale) = 2 * d := by
      rw [hρeq]
      field_simp [ne_of_gt hμ, ne_of_gt hscale]
    have hbasic : d / scale = μ * ρ / 2 := by
      apply (div_eq_iff (ne_of_gt hscale)).2
      nlinarith only [hρmul]
    rw [inv_mul_eq_div, hbasic]
    have hρnn : 0 ≤ ρ := by linarith only [hρ]
    nlinarith only [hμhalf, hρnn, mul_nonneg (by linarith only [hμhalf, hμ]) hρnn]
  intro z hz
  change z.1 ∈ vec3Ball 0 (ρ / 2) ∧ z.2 ∈ Ioo 0 (3 / 2)
  constructor
  · have hnorm : vec3EuclideanNorm (z.1 - (scale⁻¹ • (x - x₀))) < 1 :=
      (mem_vec3Ball).1 hz.1
    have htri := vec3EuclideanNorm_add_le
      (z.1 - (scale⁻¹ • (x - x₀))) (scale⁻¹ • (x - x₀))
    have hzbound : vec3EuclideanNorm z.1 < 1 + ρ / 4 := by
      have heq : z.1 - (scale⁻¹ • (x - x₀)) + (scale⁻¹ • (x - x₀)) = z.1 :=
        sub_add_cancel _ _
      rw [heq] at htri
      linarith only [htri, hnorm, hcenter]
    have hmargin : 1 + ρ / 4 ≤ ρ / 2 := by linarith only [hρ]
    apply (mem_vec3Ball).2
    simpa only [sub_zero] using lt_of_lt_of_le hzbound hmargin
  · exact ⟨by linarith only [hz.2.1], by linarith only [hz.2.2]⟩

end ESS
