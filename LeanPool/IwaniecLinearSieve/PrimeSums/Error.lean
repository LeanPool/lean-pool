/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.Vendor.PrimeNumberTheoremAnd.StrongPNT
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The de la Vallée Poussin error term

We fix once and for all a constant `pntκ > 0` and the error function
`pntE x = exp (-pntκ * √(log x))`, and deduce from `StrongPNT` that
`θ(x) = x + O(x · pntE x)` for `x ≥ 2`, with an explicit constant valid for all `x ≥ 2`.

The constant `pntκ` is the minimum of the constant `c` of `StrongPNT` and `1 / 2`; the bound
`pntκ ≤ 1 / 2` lets `pntE x` dominate `x ^ (-1/2) * log x` and `1 / x`.
-/

@[expose] public section

open IwaniecLinearSievePNT Real Filter Asymptotics Topology

namespace IwaniecLinearSieve

/-- The constant `c` in `StrongPNT`. -/
noncomputable def pntc : ℝ := StrongPNT.choose

theorem pntc_pos : 0 < pntc := StrongPNT.choose_spec.1

/-- The constant `κ` in the error term `exp (-κ √(log x))` used throughout. -/
noncomputable def pntκ : ℝ := min pntc (1 / 2)

theorem pntκ_pos : 0 < pntκ := lt_min pntc_pos (by norm_num)

theorem pntκ_le_half : pntκ ≤ 1 / 2 := min_le_right _ _

theorem pntκ_le_pntc : pntκ ≤ pntc := min_le_left _ _

/-- The de la Vallée Poussin error term `exp (-κ √(log x))`. -/
noncomputable def pntE (x : ℝ) : ℝ := exp (-pntκ * √(log x))

theorem pntE_pos (x : ℝ) : 0 < pntE x := exp_pos _

theorem pntE_nonneg (x : ℝ) : 0 ≤ pntE x := (pntE_pos x).le

theorem pntE_le_one (x : ℝ) : pntE x ≤ 1 := by
  rw [pntE, exp_le_one_iff, neg_mul]
  exact neg_nonpos.2 (mul_nonneg pntκ_pos.le (sqrt_nonneg _))

theorem pntE_le_pntE {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : pntE y ≤ pntE x := by
  unfold pntE
  apply exp_le_exp.2
  rw [neg_mul, neg_mul, neg_le_neg_iff]
  exact mul_le_mul_of_nonneg_left (sqrt_le_sqrt (log_le_log hx hxy)) pntκ_pos.le

theorem pntE_antitoneOn : AntitoneOn pntE (Set.Ioi 0) :=
  fun _ hx _ _ hxy ↦ pntE_le_pntE hx hxy

theorem pntE_antitoneOn_Ici_one : AntitoneOn pntE (Set.Ici 1) :=
  pntE_antitoneOn.mono fun _ hx ↦ lt_of_lt_of_le one_pos (Set.mem_Ici.1 hx)

theorem tendsto_pntE : Tendsto pntE atTop (𝓝 0) := by
  have h : Tendsto (fun x ↦ -pntκ * √(log x)) atTop atBot :=
    (tendsto_sqrt_atTop.comp tendsto_log_atTop).const_mul_atTop_of_neg (neg_lt_zero.2 pntκ_pos)
  exact tendsto_exp_atBot.comp h

/-- `pntE` dominates `1 / x`. -/
theorem inv_le_pntE {x : ℝ} (hx : 2 ≤ x) : x⁻¹ ≤ pntE x := by
  have hx0 : 0 < x := by linarith
  have hL : 1 / 4 ≤ log x := by
    have := log_two_gt_d9
    have := log_le_log (by norm_num) hx
    linarith
  have hs : 1 / 2 ≤ √(log x) := by
    exact (le_sqrt (by norm_num) (by linarith)).2 (by linarith)
  rw [← exp_log (inv_pos.2 hx0), pntE, log_inv]
  apply exp_le_exp.2
  have h1 : pntκ * √(log x) ≤ √(log x) * √(log x) := by
    have := pntκ_le_half
    have := sqrt_nonneg (log x)
    nlinarith
  rw [mul_self_sqrt (by linarith)] at h1
  linarith

theorem one_div_mul_log_le_pntE {x : ℝ} (hx : 2 ≤ x) : 1 / (x * log x) ≤ 2 * pntE x := by
  have hx0 : 0 < x := by linarith
  have hL : 1 / 2 ≤ log x := by
    have := log_two_gt_d9
    have := log_le_log (by norm_num) hx
    linarith
  calc 1 / (x * log x) = x⁻¹ * (log x)⁻¹ := by rw [one_div, mul_inv]
    _ ≤ pntE x * 2 := by
      refine mul_le_mul (inv_le_pntE hx) ?_ (inv_nonneg.2 (by linarith)) (pntE_nonneg _)
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    _ = 2 * pntE x := mul_comm _ _

/-- `pntE` dominates `x ^ (-1/2) * log x`. -/
theorem sqrt_mul_log_le {x : ℝ} (hx : 1 ≤ x) : √x * log x ≤ 12 * x * pntE x := by
  have hx0 : 0 < x := by linarith
  set L := log x with hLdef
  have hL : 0 ≤ L := log_nonneg hx
  have hsx : √x = exp (L / 2) := by
    rw [sqrt_eq_iff_mul_self_eq hx0.le (exp_pos _).le, ← exp_add, add_halves, hLdef,
      exp_log hx0]
  have hxL : x = exp (L / 2) * exp (L / 2) := by
    rw [← exp_add, add_halves, hLdef, exp_log hx0]
  clear_value L
  -- `L ≤ 4 exp (L / 4)` and `κ √L ≤ (L + 1) / 4`.
  have h1 : L ≤ 4 * exp (L / 4) := by linarith [add_one_le_exp (L / 4)]
  have h2 : pntκ * √L ≤ L / 4 + 1 / 4 := by
    have hκ := pntκ_le_half
    have hs := sqrt_nonneg L
    have hsq := mul_self_sqrt hL
    nlinarith [sq_nonneg (√L - 1)]
  have h3 : exp (pntκ * √L) ≤ 3 * exp (L / 4) := by
    calc exp (pntκ * √L) ≤ exp (L / 4 + 1 / 4) := exp_le_exp.2 h2
      _ = exp (L / 4) * exp (1 / 4) := exp_add _ _
      _ ≤ exp (L / 4) * 3 := by
        gcongr
        calc exp (1 / 4 : ℝ) ≤ exp 1 := exp_le_exp.2 (by norm_num)
          _ ≤ 3 := by have := exp_one_lt_d9; linarith
      _ = 3 * exp (L / 4) := mul_comm _ _
  have h4 : L * exp (pntκ * √L) ≤ 12 * exp (L / 2) := by
    calc L * exp (pntκ * √L) ≤ (4 * exp (L / 4)) * (3 * exp (L / 4)) := by
          gcongr
      _ = 12 * (exp (L / 4) * exp (L / 4)) := by ring
      _ = 12 * exp (L / 2) := by rw [← exp_add]; ring_nf
  have hE : pntE x * exp (pntκ * √L) = 1 := by
    rw [pntE, ← exp_add, ← hLdef]; simp
  have h5 : √x * (12 * exp (L / 2)) = 12 * x := by
    rw [hsx, hxL]; ring
  calc √x * L = √x * L * (pntE x * exp (pntκ * √L)) := by rw [hE, mul_one]
    _ = √x * pntE x * (L * exp (pntκ * √L)) := by ring
    _ ≤ √x * pntE x * (12 * exp (L / 2)) := by
        gcongr
        exact mul_nonneg (sqrt_nonneg _) (pntE_nonneg _)
    _ = pntE x * (√x * (12 * exp (L / 2))) := by ring
    _ = 12 * x * pntE x := by rw [h5]; ring

theorem hasDerivAt_pntE {x : ℝ} (hx : 1 < x) :
    HasDerivAt pntE (pntE x * (-pntκ * (x⁻¹ / (2 * √(log x))))) x := by
  have hlog : HasDerivAt log x⁻¹ x := hasDerivAt_log (by linarith)
  have h := ((hlog.sqrt (log_pos hx).ne').const_mul (-pntκ)).exp
  exact h

/-- The prime number theorem for `ψ` with the error term `pntE`, valid from some point on. -/
theorem exists_abs_psi_sub_le :
    ∃ C X : ℝ, 0 ≤ C ∧ ∀ x ≥ X, |Chebyshev.psi x - x| ≤ C * x * pntE x := by
  obtain ⟨C, hC⟩ := isBigO_iff.1 StrongPNT.choose_spec.2
  obtain ⟨X, hX⟩ := eventually_atTop.1 hC
  refine ⟨max C 0, max X 1, le_max_right _ _, fun x hx ↦ ?_⟩
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have h := hX x ((le_max_left _ _).trans hx)
  simp only [Pi.sub_apply, id, norm_eq_abs, norm_mul, abs_of_pos hx0, abs_exp] at h
  have hexp : exp (-StrongPNT.choose * log x ^ ((1 : ℝ) / 2)) ≤ pntE x := by
    rw [pntE, ← sqrt_eq_rpow]
    apply exp_le_exp.2
    rw [neg_mul, neg_mul, neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_right pntκ_le_pntc (sqrt_nonneg _)
  calc |Chebyshev.psi x - x| ≤ C * (x * exp (-StrongPNT.choose * log x ^ ((1 : ℝ) / 2))) := h
    _ ≤ max C 0 * (x * exp (-StrongPNT.choose * log x ^ ((1 : ℝ) / 2))) := by
      gcongr
      exact le_max_left _ _
    _ ≤ max C 0 * (x * pntE x) := by gcongr
    _ = max C 0 * x * pntE x := by ring

/-- The prime number theorem for `θ`: `|θ x - x| ≤ C x exp (-κ √(log x))` for all `x ≥ 2`. -/
theorem theta_asymp : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ≥ 2, |Chebyshev.theta x - x| ≤ C * x * pntE x := by
  obtain ⟨C, X, hC, hX⟩ := exists_abs_psi_sub_le
  set X' := max X 2
  refine ⟨max (C + 24) (pntE X')⁻¹, (hC.trans (by linarith)).trans (le_max_left _ _),
    fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hE := pntE_pos x
  rcases le_or_gt X' x with hxX | hxX
  · -- large `x`: use the PNT for `ψ` and `ψ - θ = O(√x log x)`.
    have h1 := hX x ((le_max_left _ _).trans hxX)
    have h2 := Chebyshev.psi_sub_theta_le (x := x) (by linarith)
    have h3 := Chebyshev.theta_le_psi x
    have h4 := sqrt_mul_log_le (x := x) (by linarith)
    calc |Chebyshev.theta x - x|
        ≤ |Chebyshev.psi x - x| + (Chebyshev.psi x - Chebyshev.theta x) := by
          have h5 := le_abs_self (Chebyshev.psi x - x)
          have h6 := neg_abs_le (Chebyshev.psi x - x)
          rw [abs_le]; constructor <;> linarith
      _ ≤ C * x * pntE x + 2 * (12 * x * pntE x) := by linarith
      _ = (C + 24) * x * pntE x := by ring
      _ ≤ max (C + 24) (pntE X')⁻¹ * x * pntE x := by gcongr; exact le_max_left _ _
  · -- small `x`: `0 ≤ θ x ≤ log 4 * x ≤ 2 x` and `pntE x ≥ pntE X'`.
    have h1 := Chebyshev.theta_nonneg x
    have h2 := Chebyshev.theta_le_log4_mul_x hx0.le
    have hlog4 : log 4 < 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
      have := log_two_lt_d9
      push_cast
      linarith
    have h3 : |Chebyshev.theta x - x| ≤ x := by
      rw [abs_le]; constructor <;> nlinarith
    have h4 : pntE X' ≤ pntE x := pntE_le_pntE hx0 hxX.le
    calc |Chebyshev.theta x - x| ≤ x := h3
      _ = (pntE X')⁻¹ * x * pntE X' := by have := (pntE_pos X').ne'; field_simp
      _ ≤ (pntE X')⁻¹ * x * pntE x :=
        mul_le_mul_of_nonneg_left h4 (by have := pntE_pos X'; positivity)
      _ ≤ max (C + 24) (pntE X')⁻¹ * x * pntE x := by gcongr; exact le_max_right _ _

end IwaniecLinearSieve
