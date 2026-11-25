/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.Friedrichs.FunctionalCalculusSemigroup

/-! # Smoothing: `T_t = R^k B_t` for `t > 0`

For every `k` and `t > 0` the semigroup factors as `T_t = R^k ∘ B` with a bounded operator `B`
(`B = ψ(R)`, `ψ(r) = h_t(r) r^{-k}` is continuous on `[0,1]` since `h_t` decays like
`exp(-t/r)`).  In terms of the Friedrichs operator: `T_t` maps `H` into `D(A_F^{k-1})`.
-/

@[expose] public section

open Filter Topology Set
open scoped NNReal

namespace CutoffRigidity.Riemann.Diff


/-- `ψ_{t,k}(r) = h_t(r) r^{-k}`. -/
noncomputable def psiFun (t : ℝ≥0) (k : ℕ) (r : ℝ) : ℝ := hfun t r * (r⁻¹) ^ k

lemma continuous_psiFun {t : ℝ≥0} (ht : t ≠ 0) (k : ℕ) : Continuous (psiFun t k) := by
  have htp : (0 : ℝ) < t := by positivity
  rw [continuous_iff_continuousAt]
  intro r
  rcases lt_trichotomy r 0 with hr | hr | hr
  · have hc0 : ContinuousAt (fun _ : ℝ => (0 : ℝ)) r := continuousAt_const
    refine hc0.congr ?_
    filter_upwards [Iio_mem_nhds hr] with x hx
    simp [psiFun, hfun_of_nonpos ht (le_of_lt (show x < 0 from hx))]
  · subst hr
    rw [continuousAt_iff_continuous_left_right]
    have h0 : psiFun t k 0 = 0 := by simp [psiFun, hfun_of_nonpos ht le_rfl]
    constructor
    · have hc0 : ContinuousWithinAt (fun _ : ℝ => (0 : ℝ)) (Iic 0) 0 := continuousWithinAt_const
      refine hc0.congr ?_ h0
      intro x hx; simp [psiFun, hfun_of_nonpos ht hx]
    · rw [← continuousWithinAt_Ioi_iff_Ici]
      unfold ContinuousWithinAt
      rw [h0]
      have hy : Tendsto (fun r : ℝ => (t : ℝ) * r⁻¹) (𝓝[>] 0) atTop :=
        tendsto_inv_nhdsGT_zero.const_mul_atTop htp
      have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp hy
      have h2 := h1.const_mul (Real.exp t * ((t : ℝ) ^ k)⁻¹)
      rw [mul_zero] at h2
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : (0 : ℝ) < x := hx
      simp only [Function.comp_apply, psiFun, hfun_of_pos ht hx']
      rw [mul_pow, inv_pow]
      have : Real.exp (-(t : ℝ) * (x⁻¹ - 1)) = Real.exp t * Real.exp (-((t : ℝ) * x⁻¹)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this]
      field_simp
  · have : ContinuousAt (fun x : ℝ => hfun t x * (x⁻¹) ^ k) r :=
      (continuous_hfun t).continuousAt.mul ((continuousAt_inv₀ hr.ne').pow k)
    exact this

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {R : H →L[ℝ] H} (hR : UnitOp R)
include hR

/-- **Smoothing**: for `t > 0` and every `k`, `T_t = R^k B` for a bounded operator `B`
(namely `B = ψ_{t,k}(R)`); it commutes with `R`. -/
theorem cfcSemigroup_eq_pow_mul {t : ℝ≥0} (ht : t ≠ 0) (k : ℕ) :
    cfcSemigroup R t = R ^ k * cfc (psiFun t k) R := by
  have hc : ContinuousOn (psiFun t k) (Icc 0 1) := (continuous_psiFun ht k).continuousOn
  have hid : ContinuousOn (fun r : ℝ => r ^ k) (Icc 0 1) := by fun_prop
  have h1 := hR.rcfc_mul hid hc
  have h2 : cfc (fun r : ℝ => r ^ k) R = R ^ k := by
    have := hR.rcfc_pow (f := id) continuousOn_id k
    rw [hR.rcfc_id] at this
    exact this
  rw [h2] at h1
  rw [← h1]
  unfold cfcSemigroup
  apply hR.rcfc_congr
  intro r hr
  rcases hr.1.eq_or_lt with h | h
  · rw [← h]
    simp [hfun_of_nonpos ht le_rfl, psiFun]
  · simp only [psiFun]
    have : r ^ k ≠ 0 := pow_ne_zero _ h.ne'
    rw [inv_pow]
    field_simp

end CutoffRigidity.Riemann.Diff
