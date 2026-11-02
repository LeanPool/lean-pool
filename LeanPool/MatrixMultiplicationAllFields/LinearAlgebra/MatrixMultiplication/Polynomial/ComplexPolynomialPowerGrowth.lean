/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

open Filter
open scoped Topology

namespace MatrixMultiplication.Foundation

theorem tendsto_affine_mul_geometric_zero (D C : ℝ) {q : ℝ}
    (hq : 0 ≤ q) (hq_one : q < 1) :
    Tendsto (fun n : ℕ => (D * (n : ℝ) + C) * q ^ n) atTop (𝓝 0) := by
  have hlinear := (tendsto_self_mul_const_pow_of_lt_one hq hq_one).const_mul D
  have hconstant := (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq_one).const_mul C
  simpa only [mul_zero, add_zero, add_mul, mul_assoc] using hlinear.add hconstant

theorem eventually_affine_mul_pow_le_pow (D C : ℝ) {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r < s) :
    ∀ᶠ n : ℕ in atTop, (D * (n : ℝ) + C) * r ^ n ≤ s ^ n := by
  have hs : 0 < s := hr.trans_lt hrs
  have hratio : 0 ≤ r / s := div_nonneg hr hs.le
  have hratio_one : r / s < 1 := (div_lt_one hs).2 hrs
  have hsmall :=
    (tendsto_affine_mul_geometric_zero D C hratio hratio_one).eventually_lt_const
      (show (0 : ℝ) < 1 from zero_lt_one)
  filter_upwards [hsmall] with n hn
  rw [div_pow, ← mul_div_assoc] at hn
  exact ((div_lt_iff₀ (pow_pos hs n)).1 hn).le.trans_eq (one_mul _)

theorem eventually_affine_mul_pow_le_add_pow (D C : ℝ) {r ε : ℝ}
    (hr : 0 ≤ r) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (D * (n : ℝ) + C) * r ^ n ≤ (r + ε) ^ n :=
  eventually_affine_mul_pow_le_pow D C hr (lt_add_of_pos_right r hε)

theorem power_le_of_eventually_pow_le_affine_mul_pow {a r D C : ℝ}
    (hr : 0 ≤ r)
    (h : ∀ᶠ n : ℕ in atTop, a ^ n ≤ (D * (n : ℝ) + C) * r ^ n) :
    a ≤ r := by
  by_contra hnot
  have hra : r < a := lt_of_not_ge hnot
  have ha : 0 < a := hr.trans_lt hra
  have hratio : 0 ≤ r / a := div_nonneg hr ha.le
  have hratio_one : r / a < 1 := (div_lt_one ha).2 hra
  have hsmall :=
    (tendsto_affine_mul_geometric_zero D C hratio hratio_one).eventually_lt_const
      (show (0 : ℝ) < 1 from zero_lt_one)
  rcases (h.and hsmall).exists with ⟨n, hbound, hlt⟩
  have hge : (1 : ℝ) ≤ (D * (n : ℝ) + C) * (r / a) ^ n := by
    rw [div_pow, ← mul_div_assoc]
    exact (le_div_iff₀ (pow_pos ha n)).2 (by simpa only [one_mul] using hbound)
  exact (not_lt_of_ge hge) hlt

theorem power_le_of_forall_pow_le_affine_mul_pow {a r D C : ℝ}
    (hr : 0 ≤ r)
    (h : ∀ n : ℕ, 0 < n → a ^ n ≤ (D * (n : ℝ) + C) * r ^ n) :
    a ≤ r := by
  apply power_le_of_eventually_pow_le_affine_mul_pow hr
  exact eventually_atTop.2 ⟨1, fun n hn => h n (Nat.zero_lt_one.trans_le hn)⟩

theorem power_le_of_forall_pow_le_mul_pow {a r C : ℝ}
    (hr : 0 ≤ r) (h : ∀ n : ℕ, 0 < n → a ^ n ≤ C * r ^ n) :
    a ≤ r := by
  apply power_le_of_forall_pow_le_affine_mul_pow (D := 0) (C := C) hr
  simpa only [zero_mul, zero_add] using h

theorem power_le_of_forall_pow_le_linear_mul_pow (D : ℕ) {a r : ℝ}
    (hr : 0 ≤ r)
    (h : ∀ n : ℕ, 0 < n → a ^ n ≤ ((D * n + 1 : ℕ) : ℝ) * r ^ n) :
    a ≤ r := by
  apply power_le_of_forall_pow_le_affine_mul_pow (D := (D : ℝ)) (C := 1) hr
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using h

theorem eventually_linear_mul_pow_le_add_pow (D : ℕ) {r ε : ℝ}
    (hr : 0 ≤ r) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ((D * n + 1 : ℕ) : ℝ) * r ^ n ≤ (r + ε) ^ n := by
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using
    eventually_affine_mul_pow_le_add_pow (D : ℝ) 1 hr hε

end MatrixMultiplication.Foundation

end

end MatrixMultiplicationAllFields
