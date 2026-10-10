/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Convergence.JointAnalyticity
public import LeanPool.ArnoldKAM.Arnold1963.Analysis.MeanValue
public import LeanPool.ArnoldKAM.Arnold1963.Analysis.Cauchy
public import LeanPool.ArnoldKAM.Arnold1963.Geometry.RealJacobian

/-!
Angle correction bounds, derivative smallness, and injectivity on a thinner complex strip.
-/

@[expose] public section
noncomputable section
open Set Metric
open scoped NNReal
namespace KamProject.Arnold1963

theorem norm_imagPart_le {n} (z : ComplexSpace n) : ‖imagPart z‖ ≤ ‖z‖ := by
  apply (real_norm_le_iff _ (norm_nonneg _)).mpr
  intro j
  exact (Complex.abs_im_le_norm (z j)).trans (norm_le_pi_norm z j)

theorem convex_angleStrip (n : ℕ) (r : ℝ≥0) : Convex ℝ (angleStrip n r) := by
  intro x hx y hy a b ha hb hab
  have he : imagPart (a • x + b • y) = a • imagPart x + b • imagPart y := by
    ext j
    simp [imagPart, Complex.real_smul]
  change ‖imagPart (a • x + b • y)‖ ≤ (r : ℝ)
  rw [he]
  calc
    _ ≤ ‖a • imagPart x‖ + ‖b • imagPart y‖ := norm_add_le _ _
    _ = a * ‖imagPart x‖ + b * ‖imagPart y‖ := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * r + b * r := add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hb)
    _ = r := by nlinarith

namespace Iteration
namespace InitialParameters
variable {n : ℕ} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
include b

theorem beta_width_budget : 48 * (beta δ₁ 0 : ℝ) < ρ₀ := by
  obtain ⟨hgρ, hg4⟩ := gamma_initial_bounds b.dimension_pos (threshold5_bounds b.small).2.1
  have hdg : (δ₁ : ℝ) ≤ gamma n δ₁ 0 := by
    have hh := pow_le_of_le_one (gamma n δ₁ 0).coe_nonneg
      (show (gamma n δ₁ 0 : ℝ) ≤ 1 by linarith)
      (show 4 * n ≠ 0 from Nat.mul_ne_zero (by norm_num) b.dimension_pos.ne')
    simpa only [← NNReal.coe_pow, gamma_pow b.dimension_pos, delta, decay_zero] using hh
  have hd : (0 : ℝ) < δ₁ := b.delta_pos
  have hq : (δ₁ : ℝ) < 1 / 4 := b.delta_quarter
  have hs : (δ₁ : ℝ) ^ 2 < 1 / 16 := by nlinarith
  have ht := mul_lt_mul_of_pos_left hs hd
  simp only [beta, delta, decay_zero, NNReal.coe_pow]
  nlinarith

theorem angle_derivative_budget :
    2 * (beta δ₁ 0 : ℝ) / ((ρ₀ : ℝ) / 12) < 1 / 2 := by
  apply (div_lt_iff₀ (div_pos (show (0 : ℝ) < ρ₀ from b.width_pos) (by norm_num))).mpr
  linarith [b.beta_width_budget]

end InitialParameters

namespace InitialData
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

/-- The angle component of the limiting phase transformation at a fixed action label. -/
def angleMap (p q : ComplexSpace n) : ComplexSpace n := (h.limitMap b (p, q)).2
/-- The displacement of the limiting angle map from the identity. -/
def angleCorrection (p q : ComplexSpace n) : ComplexSpace n := h.angleMap b p q - q

theorem angleCorrection_analytic {p : ComplexSpace n} (hp : p ∈ h.limitDomain b) :
    AnalyticOnNhd ℂ (h.angleCorrection b p) (commonAngleStrip n ρ₀) := by
  intro q hq
  exact (analyticAt_snd.comp (h.limitMap_angle_analytic b hp q hq)).sub analyticAt_id

theorem angleCorrection_bound {p : ComplexSpace n} (hp : p ∈ h.limitDomain b)
    {q : ComplexSpace n} (hq : q ∈ commonAngleStrip n ρ₀) :
    ‖h.angleCorrection b p q‖ < 2 * (beta δ₁ 0 : ℝ) :=
  (norm_snd_le (h.limitMap b (p, q) - (p, q))).trans_lt
    (h.limitMap_displacement b (h.angle_mem_limitPhase b hp hq))

include b in
theorem thinAngleStrip_subset : angleStrip n (ρ₀ / 6) ⊆ commonAngleStrip n ρ₀ := by
  intro q hq
  change ‖imagPart q‖ ≤ ((ρ₀ / 6 : ℝ≥0) : ℝ) at hq
  change ‖imagPart q‖ < (ρ₀ : ℝ) / 3
  have hr : (0 : ℝ) < ρ₀ := b.width_pos
  push_cast at hq
  linarith

include b in
theorem thinAngleStrip_buffer {q : ComplexSpace n} (hq : q ∈ angleStrip n (ρ₀ / 6)) :
    q ∈ erosion (commonAngleStrip n ρ₀) (ρ₀ / 12) := by
  intro y hy
  have he : imagPart y = imagPart (y - q) + imagPart q := by ext j; simp [imagPart]
  have hh := (norm_add_le (imagPart (y - q)) (imagPart q)).trans
    (add_le_add (norm_imagPart_le (y - q)) le_rfl)
  rw [← he] at hh
  change ‖imagPart q‖ ≤ ((ρ₀ / 6 : ℝ≥0) : ℝ) at hq
  rw [mem_closedBall, dist_eq_norm] at hy
  change ‖imagPart y‖ < (ρ₀ : ℝ) / 3
  push_cast at hq hy
  have hr : (0 : ℝ) < ρ₀ := b.width_pos
  linarith

theorem angleCorrection_derivative {p : ComplexSpace n} (hp : p ∈ h.limitDomain b)
    {q : ComplexSpace n} (hq : q ∈ angleStrip n (ρ₀ / 6)) :
    ‖fderiv ℂ (h.angleCorrection b p) q‖ < 1 / 2 := by
  have hh := norm_fderiv_le_div_of_mem_erosion
    (show 0 < ρ₀ / 12 from div_pos b.width_pos (by norm_num))
    (h.angleCorrection_analytic b hp)
    ⟨by positivity, fun z hz => (h.angleCorrection_bound b hp hz).le⟩
    (thinAngleStrip_buffer b hq)
  exact hh.trans_lt (by simpa using b.angle_derivative_budget)

theorem angleCorrection_lipschitz {p : ComplexSpace n} (hp : p ∈ h.limitDomain b) :
    LipschitzOnWith (1 / 2) (h.angleCorrection b p) (angleStrip n (ρ₀ / 6)) :=
  (convex_angleStrip n (ρ₀ / 6)).lipschitzOnWith_of_nnnorm_fderiv_le
    (fun q hq => (h.angleCorrection_analytic b hp q (thinAngleStrip_subset b hq)).differentiableAt)
    (fun q hq => by exact_mod_cast (h.angleCorrection_derivative b hp hq).le)

theorem angleMap_injOn {p : ComplexSpace n} (hp : p ∈ h.limitDomain b) :
    InjOn (h.angleMap b p) (angleStrip n (ρ₀ / 6)) := by
  intro q hq r hr he
  have hh := (h.angleCorrection_lipschitz b hp).dist_le_mul q hq r hr
  have hc : h.angleCorrection b p q - h.angleCorrection b p r = r - q := by
    unfold angleCorrection
    rw [he]
    abel
  rw [dist_eq_norm, hc, norm_sub_rev, ← dist_eq_norm] at hh
  apply dist_eq_zero.mp
  have hd := dist_nonneg (x := q) (y := r)
  norm_num at hh
  linarith

end InitialData
end Iteration
end KamProject.Arnold1963
