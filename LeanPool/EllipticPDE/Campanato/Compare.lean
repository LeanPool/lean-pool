/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Campanato.Basic


/-!
# Comparing two ball means under the Campanato hypothesis

Every estimate Campanato's characterisation needs is one instance of a single comparison. If a
ball `B(z, σ)` sits inside both `B(x, r)` and `B(y, t)`, then averaging the elementary bound

  `(a - b)² ≤ 2 (u - a)² + 2 (u - b)²`

over `B(z, σ)` turns the two Campanato integrals into a bound on `(u_{x,r} - u_{y,t})²`, with the
volume of the common ball in the denominator. That is `sq_ballAverage_sub_le`, and no Hölder or
Cauchy-Schwarz inequality enters: the left-hand side is a constant, so its mean over `B(z, σ)` is
itself.

Three instances follow, each with the single constant `campanatoConst d = √(2^{d+4} / |B(0,1)|)`.

* `abs_ballAverage_sub_le_of_le`: two concentric balls of comparable radii, `s ≤ r ≤ 2 s`.
* `abs_ballAverage_sub_half_le`: the dyadic step `s = r / 2`, which drives the telescoping.
* `abs_ballAverage_sub_of_dist_le`: two centres at distance at most `r / 2`, at the same radius.

This is the computational core of property (H3) of Fernández-Real and Ros-Oton, *Regularity
Theory for Elliptic PDE*.
-/

@[expose] public section

open MeasureTheory Set Metric

open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Campanato

variable {d : ℕ}

/-- A square bound transfers to the absolute value. -/
private theorem abs_le_of_sq_le_sq {X c : ℝ} (hc : 0 ≤ c) (h : X ^ 2 ≤ c ^ 2) : |X| ≤ c := by
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq hc]
  exact Real.sqrt_le_sqrt h

/-- Splitting the Campanato exponent off the dimension. -/
private theorem rpow_dim_add_two_mul {r : ℝ} (hr : 0 < r) (α : ℝ) (d : ℕ) :
    r ^ ((d : ℝ) + 2 * α) = r ^ (d : ℝ) * (r ^ α) ^ 2 := by
  have h2 : (r ^ α) ^ 2 = r ^ (2 * α) := by
    rw [← Real.rpow_natCast (r ^ α) 2, ← Real.rpow_mul hr.le]
    congr 1
    push_cast
    ring
  rw [Real.rpow_add hr, h2]

/-- **Comparison of two ball means.** When `B(z, σ)` lies inside both `B(x, r)` and `B(y, t)`, the
squared difference of the two means is controlled by the two Campanato integrals divided by the
volume of the common ball. Averaging `(a - b)² ≤ 2 (u - a)² + 2 (u - b)²` over `B(z, σ)` is the
whole proof. -/
theorem sq_ballAverage_sub_le {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {α M : ℝ} (hu : MemLp u 2 (volume.restrict Ω))
    (hcamp : CampanatoOn Ω u α M) {x y z : EuclideanSpace ℝ (Fin d)} {r t σ : ℝ}
    (hr : 0 < r) (ht : 0 < t) (hσ : 0 < σ)
    (hxr : Metric.ball x r ⊆ Ω) (hyt : Metric.ball y t ⊆ Ω)
    (hzx : Metric.ball z σ ⊆ Metric.ball x r) (hzy : Metric.ball z σ ⊆ Metric.ball y t) :
    (ballAverage u x r - ballAverage u y t) ^ 2 * (σ ^ (d : ℝ) * unitBallVolume d)
      ≤ 2 * M ^ 2 * (r ^ ((d : ℝ) + 2 * α) + t ^ ((d : ℝ) + 2 * α)) := by
  set A := ballAverage u x r with hA
  set B := ballAverage u y t with hB
  have hzΩ : Metric.ball z σ ⊆ Ω := hzx.trans hxr
  have hiA : IntegrableOn (fun w => (u w - A) ^ 2) (Metric.ball z σ) volume :=
    integrableOn_sq_sub_const hu hzΩ A
  have hiB : IntegrableOn (fun w => (u w - B) ^ 2) (Metric.ball z σ) volume :=
    integrableOn_sq_sub_const hu hzΩ B
  have hconst : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin d) => (A - B) ^ 2)
      (Metric.ball z σ) volume := integrable_const _
  have hpt : ∀ w ∈ Metric.ball z σ, (A - B) ^ 2 ≤ 2 * (u w - A) ^ 2 + 2 * (u w - B) ^ 2 := by
    intro w _
    nlinarith [sq_nonneg ((u w - A) + (u w - B))]
  have hmono := setIntegral_mono_on hconst ((hiA.const_mul 2).add (hiB.const_mul 2))
    measurableSet_ball hpt
  simp only [Pi.add_apply] at hmono
  rw [setIntegral_const, smul_eq_mul, integral_add (hiA.const_mul 2) (hiB.const_mul 2),
    integral_const_mul, integral_const_mul, measureReal_ball_rpow z hσ] at hmono
  have hAmono : ∫ w in Metric.ball z σ, (u w - A) ^ 2
      ≤ ∫ w in Metric.ball x r, (u w - A) ^ 2 :=
    setIntegral_mono_set (integrableOn_sq_sub_const hu hxr A)
      (Filter.Eventually.of_forall fun w => sq_nonneg _) hzx.eventuallyLE
  have hBmono : ∫ w in Metric.ball z σ, (u w - B) ^ 2
      ≤ ∫ w in Metric.ball y t, (u w - B) ^ 2 :=
    setIntegral_mono_set (integrableOn_sq_sub_const hu hyt B)
      (Filter.Eventually.of_forall fun w => sq_nonneg _) hzy.eventuallyLE
  have hAc : ∫ w in Metric.ball x r, (u w - A) ^ 2 ≤ M ^ 2 * r ^ ((d : ℝ) + 2 * α) :=
    hcamp x r hr hxr
  have hBc : ∫ w in Metric.ball y t, (u w - B) ^ 2 ≤ M ^ 2 * t ^ ((d : ℝ) + 2 * α) :=
    hcamp y t ht hyt
  calc (A - B) ^ 2 * (σ ^ (d : ℝ) * unitBallVolume d)
      = σ ^ (d : ℝ) * unitBallVolume d * (A - B) ^ 2 := by ring
    _ ≤ (2 * ∫ w in Metric.ball z σ, (u w - A) ^ 2)
          + 2 * ∫ w in Metric.ball z σ, (u w - B) ^ 2 := hmono
    _ ≤ 2 * M ^ 2 * (r ^ ((d : ℝ) + 2 * α) + t ^ ((d : ℝ) + 2 * α)) := by linarith

/-- The single constant every mean comparison in this file uses. -/
def campanatoConst (d : ℕ) : ℝ := Real.sqrt (2 ^ (d + 4) / unitBallVolume d)

/-- The Campanato constant is positive. -/
theorem campanatoConst_pos : 0 < campanatoConst d :=
  Real.sqrt_pos.mpr (div_pos (by positivity) unitBallVolume_pos)

/-- The Campanato constant is nonnegative. -/
theorem campanatoConst_nonneg : 0 ≤ campanatoConst d := campanatoConst_pos.le

/-- The defining identity of the Campanato constant, in the cleared form the estimates use. -/
theorem sq_campanatoConst_mul (d : ℕ) :
    campanatoConst d ^ 2 * unitBallVolume d = 2 ^ (d + 4) := by
  have hω : (0 : ℝ) < unitBallVolume d := unitBallVolume_pos
  rw [campanatoConst, Real.sq_sqrt (div_nonneg (by positivity) hω.le),
    div_mul_cancel₀ _ hω.ne']

/-- **Concentric balls of comparable radii.** For `s ≤ r ≤ 2 s` the two means differ by at most
`campanatoConst d · M · r^α`. -/
theorem abs_ballAverage_sub_le_of_le {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {α M : ℝ} (hα : 0 ≤ α) (hM : 0 ≤ M)
    (hu : MemLp u 2 (volume.restrict Ω)) (hcamp : CampanatoOn Ω u α M)
    {x : EuclideanSpace ℝ (Fin d)} {r s : ℝ} (hs : 0 < s) (hsr : s ≤ r) (hrs : r ≤ 2 * s)
    (hxr : Metric.ball x r ⊆ Ω) :
    |ballAverage u x r - ballAverage u x s| ≤ campanatoConst d * M * r ^ α := by
  have hr : 0 < r := lt_of_lt_of_le hs hsr
  have hω : 0 < unitBallVolume d := unitBallVolume_pos
  have hsd : (0 : ℝ) < s ^ (d : ℝ) := Real.rpow_pos_of_pos hs d
  have hsub : Metric.ball x s ⊆ Metric.ball x r := Metric.ball_subset_ball hsr
  have hmaster := sq_ballAverage_sub_le hu hcamp hr hs hs hxr (hsub.trans hxr) hsub
    (subset_refl _)
  -- The two Campanato terms, each rewritten as `radius^d · (radius^α)²`.
  have hrsplit : r ^ ((d : ℝ) + 2 * α) = r ^ (d : ℝ) * (r ^ α) ^ 2 := rpow_dim_add_two_mul hr α d
  have hssplit : s ^ ((d : ℝ) + 2 * α) = s ^ (d : ℝ) * (s ^ α) ^ 2 := rpow_dim_add_two_mul hs α d
  have hrd : r ^ (d : ℝ) ≤ 2 ^ d * s ^ (d : ℝ) := by
    calc r ^ (d : ℝ) ≤ (2 * s) ^ (d : ℝ) :=
          Real.rpow_le_rpow hr.le hrs (Nat.cast_nonneg d)
      _ = 2 ^ (d : ℝ) * s ^ (d : ℝ) := Real.mul_rpow (by norm_num) hs.le
      _ = 2 ^ d * s ^ (d : ℝ) := by rw [Real.rpow_natCast]
  have hsα : (s ^ α) ^ 2 ≤ (r ^ α) ^ 2 := by
    have h : s ^ α ≤ r ^ α := Real.rpow_le_rpow hs.le hsr hα
    exact pow_le_pow_left₀ (Real.rpow_nonneg hs.le α) h 2
  have hsq : (0 : ℝ) ≤ (r ^ α) ^ 2 := sq_nonneg _
  -- Bound the right-hand side of the master estimate.
  have hbound : 2 * M ^ 2 * (r ^ ((d : ℝ) + 2 * α) + s ^ ((d : ℝ) + 2 * α))
      ≤ 2 ^ (d + 4) * M ^ 2 * (r ^ α) ^ 2 * s ^ (d : ℝ) := by
    have h1 : r ^ ((d : ℝ) + 2 * α) ≤ 2 ^ d * s ^ (d : ℝ) * (r ^ α) ^ 2 := by
      rw [hrsplit]; exact mul_le_mul_of_nonneg_right hrd hsq
    have h2 : s ^ ((d : ℝ) + 2 * α) ≤ s ^ (d : ℝ) * (r ^ α) ^ 2 := by
      rw [hssplit]; exact mul_le_mul_of_nonneg_left hsα hsd.le
    have hM2 : (0 : ℝ) ≤ M ^ 2 := sq_nonneg M
    have hpow : (2 : ℝ) * (2 ^ d + 1) ≤ 2 ^ (d + 4) := by
      have : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
      rw [pow_add]
      nlinarith
    nlinarith [mul_nonneg hsd.le hsq, mul_nonneg (mul_nonneg hM2 hsd.le) hsq]
  refine abs_le_of_sq_le_sq
    (mul_nonneg (mul_nonneg campanatoConst_nonneg hM) (Real.rpow_nonneg hr.le α)) ?_
  refine le_of_mul_le_mul_right ?_ (mul_pos hsd hω)
  calc (ballAverage u x r - ballAverage u x s) ^ 2 * (s ^ (d : ℝ) * unitBallVolume d)
      ≤ 2 * M ^ 2 * (r ^ ((d : ℝ) + 2 * α) + s ^ ((d : ℝ) + 2 * α)) := hmaster
    _ ≤ 2 ^ (d + 4) * M ^ 2 * (r ^ α) ^ 2 * s ^ (d : ℝ) := hbound
    _ = (campanatoConst d ^ 2 * unitBallVolume d) * M ^ 2 * (r ^ α) ^ 2 * s ^ (d : ℝ) := by
          rw [sq_campanatoConst_mul]
    _ = (campanatoConst d * M * r ^ α) ^ 2 * (s ^ (d : ℝ) * unitBallVolume d) := by ring

/-- **Dyadic step.** Halving the radius moves the mean by at most
`campanatoConst d · M · r^α`. This is the estimate the telescoping sums. -/
theorem abs_ballAverage_sub_half_le {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {α M : ℝ} (hα : 0 ≤ α) (hM : 0 ≤ M)
    (hu : MemLp u 2 (volume.restrict Ω)) (hcamp : CampanatoOn Ω u α M)
    {x : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hr : 0 < r) (hxr : Metric.ball x r ⊆ Ω) :
    |ballAverage u x r - ballAverage u x (r / 2)| ≤ campanatoConst d * M * r ^ α :=
  abs_ballAverage_sub_le_of_le hα hM hu hcamp (by linarith) (by linarith) (by linarith) hxr

/-- **Two centres at the same radius.** When the centres are at distance at most `r / 2`, the two
means differ by at most `campanatoConst d · M · r^α`. -/
theorem abs_ballAverage_sub_of_dist_le {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {α M : ℝ} (hM : 0 ≤ M)
    (hu : MemLp u 2 (volume.restrict Ω)) (hcamp : CampanatoOn Ω u α M)
    {x y : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hr : 0 < r) (hxy : dist x y ≤ r / 2)
    (hxr : Metric.ball x r ⊆ Ω) (hyr : Metric.ball y r ⊆ Ω) :
    |ballAverage u x r - ballAverage u y r| ≤ campanatoConst d * M * r ^ α := by
  have hω : 0 < unitBallVolume d := unitBallVolume_pos
  have hhalf : (0 : ℝ) < r / 2 := by linarith
  have hhd : (0 : ℝ) < (r / 2) ^ (d : ℝ) := Real.rpow_pos_of_pos hhalf d
  have hzx : Metric.ball x (r / 2) ⊆ Metric.ball x r := Metric.ball_subset_ball (by linarith)
  have hzy : Metric.ball x (r / 2) ⊆ Metric.ball y r := by
    intro w hw
    rw [Metric.mem_ball] at hw ⊢
    calc dist w y ≤ dist w x + dist x y := dist_triangle _ _ _
      _ < r / 2 + r / 2 := by linarith
      _ = r := by ring
  have hmaster := sq_ballAverage_sub_le hu hcamp hr hr hhalf hxr hyr hzx hzy
  have hsplit : r ^ ((d : ℝ) + 2 * α) = r ^ (d : ℝ) * (r ^ α) ^ 2 := rpow_dim_add_two_mul hr α d
  have hhalfd : r ^ (d : ℝ) = 2 ^ d * (r / 2) ^ (d : ℝ) := by
    calc r ^ (d : ℝ) = (2 * (r / 2)) ^ (d : ℝ) := by rw [show 2 * (r / 2) = r from by ring]
      _ = 2 ^ (d : ℝ) * (r / 2) ^ (d : ℝ) := Real.mul_rpow (by norm_num) hhalf.le
      _ = 2 ^ d * (r / 2) ^ (d : ℝ) := by rw [Real.rpow_natCast]
  have hM2 : (0 : ℝ) ≤ M ^ 2 := sq_nonneg M
  have hsq : (0 : ℝ) ≤ (r ^ α) ^ 2 := sq_nonneg _
  have hbound : 2 * M ^ 2 * (r ^ ((d : ℝ) + 2 * α) + r ^ ((d : ℝ) + 2 * α))
      ≤ 2 ^ (d + 4) * M ^ 2 * (r ^ α) ^ 2 * (r / 2) ^ (d : ℝ) := by
    rw [hsplit, hhalfd]
    have hpow : (4 : ℝ) * 2 ^ d ≤ 2 ^ (d + 4) := by
      have : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
      rw [pow_add]
      nlinarith
    nlinarith [mul_nonneg hhd.le hsq, mul_nonneg (mul_nonneg hM2 hhd.le) hsq]
  refine abs_le_of_sq_le_sq
    (mul_nonneg (mul_nonneg campanatoConst_nonneg hM) (Real.rpow_nonneg hr.le α)) ?_
  refine le_of_mul_le_mul_right ?_ (mul_pos hhd hω)
  calc (ballAverage u x r - ballAverage u y r) ^ 2 * ((r / 2) ^ (d : ℝ) * unitBallVolume d)
      ≤ 2 * M ^ 2 * (r ^ ((d : ℝ) + 2 * α) + r ^ ((d : ℝ) + 2 * α)) := hmaster
    _ ≤ 2 ^ (d + 4) * M ^ 2 * (r ^ α) ^ 2 * (r / 2) ^ (d : ℝ) := hbound
    _ = (campanatoConst d ^ 2 * unitBallVolume d) * M ^ 2 * (r ^ α) ^ 2 * (r / 2) ^ (d : ℝ) := by
          rw [sq_campanatoConst_mul]
    _ = (campanatoConst d * M * r ^ α) ^ 2 * ((r / 2) ^ (d : ℝ) * unitBallVolume d) := by ring

end EllipticPdes.Campanato
