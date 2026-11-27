/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalScalarDefs
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Thermal comparison (scalar content of Lemma 4.3)

With `d = tanh u`, the thermal increment is `d coth(τ u) - 1` and the reserve is
`(1 - d²)^{1/2}`. This file proves the scalar comparison of Lemma 4.3.
-/

@[expose] public section

namespace VacuumBellSeparation

/-! ### Milestone 1: algebraic reduction -/

theorem one_sub_tanh_sq_mul_cosh_sq (u : ℝ) :
    (1 - Real.tanh u ^ 2) * Real.cosh u ^ 2 = 1 := by
  have hc : 0 < Real.cosh u := Real.cosh_pos u
  have hc' : Real.cosh u ≠ 0 := hc.ne'
  have hsc : Real.sinh u = Real.tanh u * Real.cosh u := by
    rw [Real.tanh_eq_sinh_div_cosh, div_mul_cancel₀ _ hc']
  have h := Real.cosh_sq_sub_sinh_sq u
  rw [hsc] at h
  linear_combination h

theorem one_sub_tanh_sq (u : ℝ) : 1 - Real.tanh u ^ 2 = (Real.cosh u ^ 2)⁻¹ :=
  eq_inv_of_mul_eq_one_left (one_sub_tanh_sq_mul_cosh_sq u)

theorem one_sub_tanh_sq_pos (u : ℝ) : 0 < 1 - Real.tanh u ^ 2 := by
  rw [one_sub_tanh_sq]
  exact inv_pos.mpr (pow_pos (Real.cosh_pos u) 2)

/-- The thermal increment equals the ratio times the reserve power. -/
theorem thermal_increment_eq {τ u : ℝ} (hτ0 : 0 < τ) (hu : 0 < u) :
    Real.tanh u * (Real.cosh (τ * u) / Real.sinh (τ * u)) - 1
      = thermalRatio τ u * (1 - Real.tanh u ^ 2) ^ τ := by
  have hc : 0 < Real.cosh u := Real.cosh_pos u
  have hs : 0 < Real.sinh (τ * u) := Real.sinh_pos_iff.mpr (mul_pos hτ0 hu)
  have hc' : Real.cosh u ≠ 0 := hc.ne'
  have hs' : Real.sinh (τ * u) ≠ 0 := hs.ne'
  have h1 : (1 - Real.tanh u ^ 2) ^ τ = Real.cosh u ^ (-2 * τ) := by
    rw [one_sub_tanh_sq, Real.rpow_mul hc.le, Real.rpow_neg hc.le, Real.rpow_two]
  have hpow : Real.cosh u ^ (2 * τ - 1) * Real.cosh u ^ (-2 * τ) = (Real.cosh u)⁻¹ := by
    rw [← Real.rpow_add hc, show 2 * τ - 1 + -2 * τ = -1 by ring, Real.rpow_neg_one]
  have hsub : Real.sinh ((1 - τ) * u)
      = Real.sinh u * Real.cosh (τ * u) - Real.cosh u * Real.sinh (τ * u) := by
    rw [show (1 - τ) * u = u - τ * u by ring, Real.sinh_sub]
  have hR : thermalRatio τ u * (1 - Real.tanh u ^ 2) ^ τ
      = Real.sinh ((1 - τ) * u) / Real.sinh (τ * u) * (Real.cosh u)⁻¹ := by
    rw [h1, thermalRatio, mul_assoc, hpow]
  rw [hR, hsub, Real.tanh_eq_sinh_div_cosh]
  field_simp

/-- Reduction of the scalar Lemma 4.3 to a lower bound on the ratio. -/
theorem thermal_increment_ge_of_le_ratio {τ u c : ℝ} (hτ0 : 0 < τ) (hu : 0 < u)
    (hc : c ≤ thermalRatio τ u) :
    c * (1 - Real.tanh u ^ 2) ^ τ
      ≤ Real.tanh u * (Real.cosh (τ * u) / Real.sinh (τ * u)) - 1 := by
  rw [thermal_increment_eq hτ0 hu]
  exact mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (one_sub_tanh_sq_pos u).le _)

/-! ### Milestone 2: the case `τ ≤ 1/2` (elementary) -/

theorem partA_core {p y : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1) :
    y ^ p + p * y ^ ((1 + p) / 2) ≤ 1 + p * y := by
  have h1 : y ^ p ≤ 1 + p * (y - 1) := by
    have h := rpow_one_add_le_one_add_mul_self (s := y - 1) (by linarith) hp0 hp1
    rw [show 1 + (y - 1) = y by ring] at h
    exact h
  have h2 : y ^ ((1 + p) / 2) ≤ 1 := Real.rpow_le_one hy0.le hy1 (by linarith)
  have h3 := mul_le_mul_of_nonneg_left h2 hp0
  nlinarith

theorem partA_exp {τ u : ℝ} (hτ0 : 0 < τ) (hτ : τ ≤ 1 / 2) (hu : 0 < u) :
    (1 - Real.exp (-2 * u) ^ τ) * (1 + Real.exp (-2 * u)) ^ (1 - 2 * τ)
      ≤ 1 - Real.exp (-2 * u) ^ (1 - τ) := by
  obtain ⟨y, hy⟩ : ∃ y, y = Real.exp (-2 * u) := ⟨_, rfl⟩
  rw [← hy]
  have hy0 : 0 < y := by rw [hy]; exact Real.exp_pos _
  have hy1 : y < 1 := by
    rw [hy]
    calc Real.exp (-2 * u) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hp0 : 0 ≤ 1 - 2 * τ := by linarith
  have hp1 : 1 - 2 * τ ≤ 1 := by linarith
  have hcore := partA_core hp0 hp1 hy0 hy1.le
  rw [show (1 + (1 - 2 * τ)) / 2 = 1 - τ by ring] at hcore
  have hb : (1 + y) ^ (1 - 2 * τ) ≤ 1 + (1 - 2 * τ) * y :=
    rpow_one_add_le_one_add_mul_self (by linarith) hp0 hp1
  have hyτ : y ^ τ ≤ 1 := Real.rpow_le_one hy0.le hy1.le hτ0.le
  have hyτ0 : 0 < y ^ τ := Real.rpow_pos_of_pos hy0 τ
  have e2 : y ^ τ * y ^ (1 - 2 * τ) = y ^ (1 - τ) := by
    rw [← Real.rpow_add hy0]; congr 1; ring
  have e3 : y ^ τ * y ^ (1 - τ) = y := by
    rw [← Real.rpow_add hy0, show τ + (1 - τ) = (1 : ℝ) by ring, Real.rpow_one]
  have h4 : y ^ (1 - τ) + (1 - 2 * τ) * y ≤ y ^ τ + (1 - 2 * τ) * y * y ^ τ := by
    have h := mul_le_mul_of_nonneg_left hcore hyτ0.le
    calc y ^ (1 - τ) + (1 - 2 * τ) * y
        = y ^ τ * (y ^ (1 - 2 * τ) + (1 - 2 * τ) * y ^ (1 - τ)) := by
          linear_combination -e2 - (1 - 2 * τ) * e3
      _ ≤ y ^ τ * (1 + (1 - 2 * τ) * y) := h
      _ = y ^ τ + (1 - 2 * τ) * y * y ^ τ := by ring
  have h5 : (1 - y ^ τ) * (1 + y) ^ (1 - 2 * τ) ≤ (1 - y ^ τ) * (1 + (1 - 2 * τ) * y) :=
    mul_le_mul_of_nonneg_left hb (by linarith)
  nlinarith [h4, h5]

theorem thermalRatio_ge_of_le_half {τ u : ℝ} (hτ0 : 0 < τ) (hτ : τ ≤ 1 / 2) (hu : 0 < u) :
    (2 : ℝ) ^ (1 - 2 * τ) ≤ thermalRatio τ u := by
  have hc : 0 < Real.cosh u := Real.cosh_pos u
  have hs : 0 < Real.sinh (τ * u) := Real.sinh_pos_iff.mpr (mul_pos hτ0 hu)
  have key := partA_exp hτ0 hτ hu
  have e1 : Real.exp (τ * u) * Real.exp (-2 * u) ^ τ = Real.exp (-(τ * u)) := by
    rw [← Real.exp_mul, ← Real.exp_add]; congr 1; ring
  have hsτ : Real.sinh (τ * u) = Real.exp (τ * u) * (1 - Real.exp (-2 * u) ^ τ) / 2 := by
    rw [Real.sinh_eq, mul_sub, mul_one, e1]
  have e2 : Real.exp ((1 - τ) * u) * Real.exp (-2 * u) ^ (1 - τ)
      = Real.exp (-((1 - τ) * u)) := by
    rw [← Real.exp_mul, ← Real.exp_add]; congr 1; ring
  have hsa : Real.sinh ((1 - τ) * u)
      = Real.exp ((1 - τ) * u) * (1 - Real.exp (-2 * u) ^ (1 - τ)) / 2 := by
    rw [Real.sinh_eq, mul_sub, mul_one, e2]
  have e3' : Real.exp u * Real.exp (-2 * u) = Real.exp (-u) := by
    rw [← Real.exp_add]; congr 1; ring
  have e3 : 2 * Real.cosh u = Real.exp u * (1 + Real.exp (-2 * u)) := by
    rw [Real.cosh_eq, mul_add, mul_one, e3']; ring
  have e4 : (2 : ℝ) ^ (1 - 2 * τ) * Real.cosh u ^ (1 - 2 * τ)
      = Real.exp (u * (1 - 2 * τ)) * (1 + Real.exp (-2 * u)) ^ (1 - 2 * τ) := by
    rw [← Real.mul_rpow (show (0 : ℝ) ≤ 2 by norm_num) hc.le, e3,
      Real.mul_rpow (Real.exp_pos u).le (show (0 : ℝ) ≤ 1 + Real.exp (-2 * u) by positivity),
      ← Real.exp_mul]
  have e5 : Real.exp (τ * u) * Real.exp (u * (1 - 2 * τ)) = Real.exp ((1 - τ) * u) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold thermalRatio
  rw [show 2 * τ - 1 = -(1 - 2 * τ) by ring, Real.rpow_neg hc.le, ← div_eq_mul_inv, div_div,
    le_div_iff₀ (mul_pos hs (Real.rpow_pos_of_pos hc _))]
  calc (2 : ℝ) ^ (1 - 2 * τ) * (Real.sinh (τ * u) * Real.cosh u ^ (1 - 2 * τ))
      = Real.sinh (τ * u) * ((2 : ℝ) ^ (1 - 2 * τ) * Real.cosh u ^ (1 - 2 * τ)) := by ring
    _ = Real.exp ((1 - τ) * u) / 2
          * ((1 - Real.exp (-2 * u) ^ τ) * (1 + Real.exp (-2 * u)) ^ (1 - 2 * τ)) := by
        rw [e4, hsτ, ← e5]; ring
    _ ≤ Real.exp ((1 - τ) * u) / 2 * (1 - Real.exp (-2 * u) ^ (1 - τ)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = Real.sinh ((1 - τ) * u) := by rw [hsa]; ring

/-- Lemma 4.3 for `0 < τ ≤ 1/2`: `c_τ ≤ 𝔮_τ(u)`. -/
theorem thermalConst_le_thermalRatio_of_le_half {τ u : ℝ} (hτ0 : 0 < τ) (hτ : τ ≤ 1 / 2)
    (hu : 0 < u) : thermalConst τ ≤ thermalRatio τ u := by
  rw [thermalConst, ite_eq_left hτ]
  exact thermalRatio_ge_of_le_half hτ0 hτ hu

/-- Lemma 4.3, scalar form, for `0 < τ ≤ 1/2` (`d = tanh u`). -/
theorem thermal_increment_ge_of_le_half {τ u : ℝ} (hτ0 : 0 < τ) (hτ : τ ≤ 1 / 2) (hu : 0 < u) :
    thermalConst τ * (1 - Real.tanh u ^ 2) ^ τ
      ≤ Real.tanh u * (Real.cosh (τ * u) / Real.sinh (τ * u)) - 1 :=
  thermal_increment_ge_of_le_ratio hτ0 hu (thermalConst_le_thermalRatio_of_le_half hτ0 hτ hu)

/-! ### Stage B1 of the case `τ ≥ 1/2` (calculus) -/

/-- Stage B1: `sinh x ≤ x cosh x` for `0 ≤ x`. -/
theorem sinh_le_mul_cosh {x : ℝ} (hx : 0 ≤ x) : Real.sinh x ≤ x * Real.cosh x := by
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun t => t * Real.cosh t - Real.sinh t) (t * Real.sinh t) t := by
    intro t
    have h1 := ((hasDerivAt_id' (x := t)).mul (Real.hasDerivAt_cosh t)).sub
      (Real.hasDerivAt_sinh t)
    exact h1.congr_deriv (by ring)
  have hmono : MonotoneOn (fun t => t * Real.cosh t - Real.sinh t) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => (hderiv t).continuousAt.continuousWithinAt
    · exact fun t _ => (hderiv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hderiv t).deriv]
      exact mul_nonneg (le_of_lt ht) (Real.sinh_nonneg_iff.mpr (le_of_lt ht))
  have h0 : (0 : ℝ) * Real.cosh 0 - Real.sinh 0 ≤ x * Real.cosh x - Real.sinh x :=
    hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  rw [Real.sinh_zero] at h0
  linarith

/-- Stage B1': `tanh x ≤ x` for `0 ≤ x`. -/
theorem tanh_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  rw [Real.tanh_eq_sinh_div_cosh, div_le_iff₀ (Real.cosh_pos x)]
  exact sinh_le_mul_cosh hx

/-! ### Stage B2 of the case `τ ≥ 1/2`: two auxiliary inequalities -/

/-- (S1) `m(u) = log (cosh u) + tanh u ^ 2 - u tanh u ≥ 0` for `u ≥ 0`. -/
theorem log_cosh_add_tanh_sq_sub_mul_tanh_nonneg {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ Real.log (Real.cosh u) + Real.tanh u ^ 2 - u * Real.tanh u := by
  have hderiv : ∀ v : ℝ, HasDerivAt
      (fun v => Real.log (Real.cosh v) - Real.tanh u * (v - Real.sinh v / Real.cosh v))
      (Real.sinh v / Real.cosh v - Real.tanh u *
        (1 - (Real.cosh v * Real.cosh v - Real.sinh v * Real.sinh v) / Real.cosh v ^ 2)) v := by
    intro v
    have hc : Real.cosh v ≠ 0 := (Real.cosh_pos v).ne'
    have h1 := (Real.hasDerivAt_cosh v).log hc
    have h2 := (Real.hasDerivAt_sinh v).div (Real.hasDerivAt_cosh v) hc
    exact h1.sub (((hasDerivAt_id' (x := v)).sub h2).const_mul (Real.tanh u))
  have hmono : MonotoneOn
      (fun v => Real.log (Real.cosh v) - Real.tanh u * (v - Real.sinh v / Real.cosh v))
      (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun v _ => (hderiv v).continuousAt.continuousWithinAt
    · exact fun v _ => (hderiv v).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [interior_Ici] at hv
      rw [(hderiv v).deriv]
      have hv0 : 0 < v := hv
      have hcs : Real.cosh v * Real.cosh v - Real.sinh v * Real.sinh v = 1 := by
        linear_combination Real.cosh_sq_sub_sinh_sq v
      rw [hcs, one_div, ← one_sub_tanh_sq, ← Real.tanh_eq_sinh_div_cosh]
      have hT0 : 0 ≤ Real.tanh v := by
        rw [Real.tanh_eq_sinh_div_cosh]
        exact div_nonneg (Real.sinh_nonneg_iff.mpr hv0.le) (Real.cosh_pos v).le
      have hT1 : Real.tanh v < 1 := Real.tanh_lt_one v
      have ht1 : Real.tanh u < 1 := Real.tanh_lt_one u
      nlinarith [mul_nonneg hT0 (sub_nonneg.mpr hT1.le),
        mul_nonneg (sq_nonneg (Real.tanh v)) (sub_nonneg.mpr ht1.le)]
  have h0 : Real.log (Real.cosh 0) - Real.tanh u * (0 - Real.sinh 0 / Real.cosh 0)
      ≤ Real.log (Real.cosh u) - Real.tanh u * (u - Real.sinh u / Real.cosh u) :=
    hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu) hu
  have hM0 : Real.log (Real.cosh 0) - Real.tanh u * (0 - Real.sinh 0 / Real.cosh 0) = 0 := by
    simp
  rw [hM0, ← Real.tanh_eq_sinh_div_cosh] at h0
  nlinarith [h0]

/-- (S2) `N(u) = sinh u · log (cosh u) - u cosh u + sinh u ≥ 0` for `u ≥ 0`. -/
theorem sinh_mul_log_cosh_sub_nonneg {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ Real.sinh u * Real.log (Real.cosh u) - u * Real.cosh u + Real.sinh u := by
  have hderiv : ∀ t : ℝ, HasDerivAt
      (fun t => Real.sinh t * Real.log (Real.cosh t) - t * Real.cosh t + Real.sinh t)
      (Real.cosh t * Real.log (Real.cosh t) + Real.sinh t * (Real.sinh t / Real.cosh t)
        - (1 * Real.cosh t + t * Real.sinh t) + Real.cosh t) t := by
    intro t
    have hc : Real.cosh t ≠ 0 := (Real.cosh_pos t).ne'
    exact (((Real.hasDerivAt_sinh t).mul ((Real.hasDerivAt_cosh t).log hc)).sub
      ((hasDerivAt_id' (x := t)).mul (Real.hasDerivAt_cosh t))).add (Real.hasDerivAt_sinh t)
  have hmono : MonotoneOn
      (fun t => Real.sinh t * Real.log (Real.cosh t) - t * Real.cosh t + Real.sinh t)
      (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => (hderiv t).continuousAt.continuousWithinAt
    · exact fun t _ => (hderiv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hderiv t).deriv]
      have hm := log_cosh_add_tanh_sq_sub_mul_tanh_nonneg (le_of_lt ht)
      have hc : 0 < Real.cosh t := Real.cosh_pos t
      have hsc : Real.sinh t = Real.tanh t * Real.cosh t := by
        rw [Real.tanh_eq_sinh_div_cosh, div_mul_cancel₀ _ hc.ne']
      rw [← Real.tanh_eq_sinh_div_cosh, hsc]
      nlinarith [mul_nonneg hc.le hm]
  have h0 : Real.sinh 0 * Real.log (Real.cosh 0) - 0 * Real.cosh 0 + Real.sinh 0
      ≤ Real.sinh u * Real.log (Real.cosh u) - u * Real.cosh u + Real.sinh u :=
    hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu) hu
  have hN0 : Real.sinh 0 * Real.log (Real.cosh 0) - 0 * Real.cosh 0 + Real.sinh 0 = 0 := by
    simp
  rw [hN0] at h0
  exact h0

/-- Consequence of (S2): `u coth u - 1 ≤ log (cosh u)` for `u > 0`. -/
theorem mul_coth_sub_one_le_log_cosh {u : ℝ} (hu : 0 < u) :
    u * Real.cosh u / Real.sinh u - 1 ≤ Real.log (Real.cosh u) := by
  have hs : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu
  have hN := sinh_mul_log_cosh_sub_nonneg hu.le
  rw [sub_le_iff_le_add, div_le_iff₀ hs]
  nlinarith [hN]

/-! ### Stage B3: monotonicity of `coth x - 1/x` and of `log φ` -/

/-- (S3) `q(x) = coth x - 1/x` is monotone on `(0, ∞)`. -/
theorem coth_sub_inv_monotoneOn :
    MonotoneOn (fun x => Real.cosh x / Real.sinh x - x⁻¹) (Set.Ioi 0) := by
  have hderiv : ∀ x : ℝ, 0 < x → HasDerivAt (fun x => Real.cosh x / Real.sinh x - x⁻¹)
      ((Real.sinh x * Real.sinh x - Real.cosh x * Real.cosh x) / Real.sinh x ^ 2
        - -(x ^ 2)⁻¹) x := by
    intro x hx
    have hs : Real.sinh x ≠ 0 := (Real.sinh_pos_iff.mpr hx).ne'
    exact ((Real.hasDerivAt_cosh x).div (Real.hasDerivAt_sinh x) hs).sub (hasDerivAt_inv hx.ne')
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · exact fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hderiv x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(hderiv x hx).deriv]
    have hx0 : 0 < x := hx
    have hcs : Real.sinh x * Real.sinh x - Real.cosh x * Real.cosh x = -1 := by
      linear_combination (-1 : ℝ) * Real.cosh_sq_sub_sinh_sq x
    have hxs : x ≤ Real.sinh x := Real.self_le_sinh_iff.mpr hx0.le
    have h2 : x ^ 2 ≤ Real.sinh x ^ 2 := by nlinarith
    have h3 : (Real.sinh x ^ 2)⁻¹ ≤ (x ^ 2)⁻¹ := inv_anti₀ (pow_pos hx0 2) h2
    rw [hcs]
    have e : -1 / Real.sinh x ^ 2 - -(x ^ 2)⁻¹ = (x ^ 2)⁻¹ - (Real.sinh x ^ 2)⁻¹ := by ring
    rw [e]
    linarith

/-- The derivative bound used in (S4): `u coth(cu) - 1/c - log (cosh u) ≤ 0` for `0 < c ≤ 1`. -/
theorem coth_mul_sub_inv_le_log_cosh {u c : ℝ} (hu : 0 < u) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    Real.cosh (c * u) * (1 * u) / Real.sinh (c * u) - c⁻¹ - 1 * Real.log (Real.cosh u) ≤ 0 := by
  have hcu : 0 < c * u := mul_pos hc0 hu
  have hq : Real.cosh (c * u) / Real.sinh (c * u) - (c * u)⁻¹
      ≤ Real.cosh u / Real.sinh u - u⁻¹ :=
    coth_sub_inv_monotoneOn (Set.mem_Ioi.mpr hcu) (Set.mem_Ioi.mpr hu) (by nlinarith)
  have e1 : u * (c * u)⁻¹ = c⁻¹ := by
    rw [mul_inv, mul_left_comm, mul_inv_cancel₀ hu.ne', mul_one]
  have e2 : u * u⁻¹ = 1 := mul_inv_cancel₀ hu.ne'
  have hS2 := mul_coth_sub_one_le_log_cosh hu
  calc Real.cosh (c * u) * (1 * u) / Real.sinh (c * u) - c⁻¹ - 1 * Real.log (Real.cosh u)
      = u * (Real.cosh (c * u) / Real.sinh (c * u) - (c * u)⁻¹) - Real.log (Real.cosh u) := by
        rw [mul_sub, e1]; ring
    _ ≤ u * (Real.cosh u / Real.sinh u - u⁻¹) - Real.log (Real.cosh u) :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left hq hu.le) _
    _ = (u * Real.cosh u / Real.sinh u - 1) - Real.log (Real.cosh u) := by
        rw [mul_sub, e2]; ring
    _ ≤ 0 := sub_nonpos.mpr hS2

/-- (S4) `ψ(c) = log (sinh (c u)) - log c - c log (cosh u)` is antitone on `(0, 1]`. -/
theorem psi_antitoneOn {u : ℝ} (hu : 0 < u) :
    AntitoneOn (fun c => Real.log (Real.sinh (c * u)) - Real.log c - c * Real.log (Real.cosh u))
      (Set.Ioc 0 1) := by
  have hderiv : ∀ c : ℝ, 0 < c → HasDerivAt
      (fun c => Real.log (Real.sinh (c * u)) - Real.log c - c * Real.log (Real.cosh u))
      (Real.cosh (c * u) * (1 * u) / Real.sinh (c * u) - c⁻¹ - 1 * Real.log (Real.cosh u)) c := by
    intro c hc
    have hs : Real.sinh (c * u) ≠ 0 := (Real.sinh_pos_iff.mpr (mul_pos hc hu)).ne'
    have h1 : HasDerivAt (fun y => y * u) (1 * u) c := (hasDerivAt_id' (x := c)).mul_const u
    have h2 : HasDerivAt (fun y => Real.sinh (y * u)) (Real.cosh (c * u) * (1 * u)) c := h1.sinh
    exact ((h2.log hs).sub (Real.hasDerivAt_log hc.ne')).sub
      ((hasDerivAt_id' (x := c)).mul_const (Real.log (Real.cosh u)))
  apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 1)
  · exact fun c hc => (hderiv c hc.1).continuousAt.continuousWithinAt
  · intro c hc
    rw [interior_Ioc] at hc
    exact (hderiv c hc.1).differentiableAt.differentiableWithinAt
  · intro c hc
    rw [interior_Ioc] at hc
    rw [(hderiv c hc.1).deriv]
    exact coth_mul_sub_inv_le_log_cosh hu hc.1 hc.2.le

/-! ### Lemma 4.3 for `1/2 ≤ τ < 1` and the full statement -/

/-- Lemma 4.3 for `1/2 ≤ τ < 1`: `(1-τ)/τ ≤ 𝔮_τ(u)`. -/
theorem thermalRatio_ge_of_half_le {τ u : ℝ} (hτ : 1 / 2 ≤ τ) (hτ1 : τ < 1) (hu : 0 < u) :
    (1 - τ) / τ ≤ thermalRatio τ u := by
  have hτ0 : 0 < τ := by linarith
  have ha0 : 0 < 1 - τ := by linarith
  have hab : 1 - τ ≤ τ := by linarith
  have hψ : Real.log (Real.sinh (τ * u)) - Real.log τ - τ * Real.log (Real.cosh u)
      ≤ Real.log (Real.sinh ((1 - τ) * u)) - Real.log (1 - τ)
        - (1 - τ) * Real.log (Real.cosh u) :=
    psi_antitoneOn hu ⟨ha0, by linarith⟩ ⟨hτ0, hτ1.le⟩ hab
  have hsa : 0 < Real.sinh ((1 - τ) * u) := Real.sinh_pos_iff.mpr (mul_pos ha0 hu)
  have hsb : 0 < Real.sinh (τ * u) := Real.sinh_pos_iff.mpr (mul_pos hτ0 hu)
  have hc : 0 < Real.cosh u := Real.cosh_pos u
  have hR : 0 < thermalRatio τ u :=
    mul_pos (div_pos hsa hsb) (Real.rpow_pos_of_pos hc _)
  rw [← Real.log_le_log_iff (div_pos ha0 hτ0) hR, Real.log_div ha0.ne' hτ0.ne']
  unfold thermalRatio
  rw [Real.log_mul (div_pos hsa hsb).ne' (Real.rpow_pos_of_pos hc _).ne',
    Real.log_div hsa.ne' hsb.ne', Real.log_rpow hc]
  nlinarith [hψ]

/-- Lemma 4.3: `c_τ ≤ 𝔮_τ(u)` for `0 < τ < 1` and `u > 0`. -/
theorem thermalConst_le_thermalRatio {τ u : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (hu : 0 < u) :
    thermalConst τ ≤ thermalRatio τ u := by
  by_cases hτ : τ ≤ 1 / 2
  · exact thermalConst_le_thermalRatio_of_le_half hτ0 hτ hu
  · rw [thermalConst, ite_eq_right hτ]
    exact thermalRatio_ge_of_half_le (le_of_lt (not_le.mp hτ)) hτ1 hu

/-- Lemma 4.3, scalar form (`d = tanh u`): `d coth(τu) - 1 ≥ c_τ (1 - d²)^τ`. -/
theorem thermal_increment_ge {τ u : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (hu : 0 < u) :
    thermalConst τ * (1 - Real.tanh u ^ 2) ^ τ
      ≤ Real.tanh u * (Real.cosh (τ * u) / Real.sinh (τ * u)) - 1 :=
  thermal_increment_ge_of_le_ratio hτ0 hu (thermalConst_le_thermalRatio hτ0 hτ1 hu)

end VacuumBellSeparation
