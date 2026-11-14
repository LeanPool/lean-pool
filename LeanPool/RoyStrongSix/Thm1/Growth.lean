/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.Thm1.Params

/-!
# Growth: the independent branch is impossible for large `β`

Write `G = 1 + log β`, `T = β^{nθ}`, `L₀ = β^a` with `a = nQ ≤ nθ`, `L₁ ≤ L₀`, `L₁ S = d L₀`,
`S ≤ d β^b` and `T_J ≤ (d+1)T`.

* `log_N_le`, `log_B_le`, `log_E_le`, `log_H_le`: each term on the right of `log_ineq` is at most
  `const · T · G`.
* `growth_core`: `x ≤ C T G` forces `x < (Tβ²/2 − (dT + 1)) log 2` for all large `β`. The left of
  `log_ineq` is exactly this, since `M = β^{nθ+2} = T β²`.
-/

@[expose] public section

namespace LeanPool

namespace StrongSix.Thm1

open Params

/-- `log x ≤ (log c + a)(1 + log β)` when `0 < x ≤ c β^a`, `c ≥ 1`, `β ≥ 1`. -/
theorem log_le_of_le_cpow {c : ℝ} (hc : 1 ≤ c) {β : ℕ} (hβ : 1 ≤ β) (a : ℕ) {x : ℝ} (hx0 : 0 < x)
    (hx : x ≤ c * (β : ℝ) ^ a) : Real.log x ≤ (Real.log c + a) * (1 + Real.log β) := by
  have hb : (1 : ℝ) ≤ β := by exact_mod_cast hβ
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hlb : 0 ≤ Real.log β := Real.log_nonneg hb
  have h1 : Real.log x ≤ Real.log c + a * Real.log β := by
    calc Real.log x ≤ Real.log (c * (β : ℝ) ^ a) := Real.log_le_log hx0 hx
      _ = Real.log c + a * Real.log β := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  nlinarith [mul_nonneg hlc hlb, Nat.cast_nonneg (α := ℝ) a]

/-- **The final comparison.** -/
theorem growth_core (d : ℕ) (C : ℝ) : ∃ β₀ : ℕ, ∀ β : ℕ, β₀ ≤ β → ∀ T x : ℝ, 1 ≤ T →
    x ≤ C * T * (1 + Real.log β) → x < (T * (β : ℝ) ^ 2 / 2 - (d * T + 1)) * Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨β₁, hβ₁⟩ := log_dominated (|C| / Real.log 2 + d + 1)
  refine ⟨max β₁ 2, fun β hβ T x hT hx => ?_⟩
  have hβ2 : (2 : ℝ) ≤ β := by exact_mod_cast le_of_max_le_right hβ
  have hb : (1 : ℝ) ≤ β := by linarith
  have hlb : 0 ≤ Real.log β := Real.log_nonneg hb
  set G := 1 + Real.log β with hG
  have hG1 : 1 ≤ G := by linarith
  have hdom := hβ₁ β (le_of_max_le_left hβ)
  -- `β > (|C|/log 2 + d + 1) G ≥ |C| G / log 2 + d + 1`
  have hdom' : |C| * G / Real.log 2 + d + 1 < β := by
    have : (|C| / Real.log 2 + d + 1) * 1 ≤ (|C| / Real.log 2 + d + 1) * G :=
      mul_le_mul_of_nonneg_left hG1 (by positivity)
    have e : |C| * G / Real.log 2 = |C| / Real.log 2 * G := by ring
    nlinarith [div_nonneg (abs_nonneg C) hl2.le, Nat.cast_nonneg (α := ℝ) d]
  have hCG : |C| * G < (β - d - 1) * Real.log 2 := by
    have := (div_lt_iff₀ hl2).mp (show |C| * G / Real.log 2 < β - d - 1 by linarith)
    linarith
  have hx' : x ≤ |C| * G * T := by
    calc x ≤ C * T * G := hx
      _ ≤ |C| * T * G := by gcongr; exact le_abs_self C
      _ = |C| * G * T := by ring
  have hβsq : (β : ℝ) ≤ (β : ℝ) ^ 2 / 2 := by nlinarith
  have hrhs : T * ((β : ℝ) - d - 1) * Real.log 2 ≤ (T * (β : ℝ) ^ 2 / 2 - (d * T + 1)) *
    Real.log 2 := by
    apply mul_le_mul_of_nonneg_right _ hl2.le
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have : |C| * G * T < T * ((β : ℝ) - d - 1) * Real.log 2 := by
    have := mul_lt_mul_of_pos_right hCG (show (0 : ℝ) < T by linarith)
    linarith
  linarith

variable {β : ℕ} (hβ : 1 ≤ β)
include hβ

/-- `log N ≤ d (log 2 + a) G T` when `N ≤ (2 β^a)^d`. -/
theorem log_N_le {N d a : ℕ} {T : ℝ} (hT : 1 ≤ T) (hN : 1 ≤ N)
    (hNle : (N : ℝ) ≤ (2 * (β : ℝ) ^ a) ^ d) :
    Real.log N ≤ d * (Real.log 2 + a) * T * (1 + Real.log β) := by
  have hb : (1 : ℝ) ≤ β := by exact_mod_cast hβ
  have h0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := log_le_of_le_cpow (c := (2 : ℝ) ^ d) (one_le_pow₀ (by norm_num)) hβ (a * d) h0 (by
    calc (N : ℝ) ≤ (2 * (β : ℝ) ^ a) ^ d := hNle
      _ = 2 ^ d * (β : ℝ) ^ (a * d) := by rw [mul_pow, ← pow_mul])
  rw [Real.log_pow] at h1
  push_cast at h1
  have hlb : 0 ≤ Real.log β := Real.log_nonneg hb
  have hc : 0 ≤ (d : ℝ) * (Real.log 2 + a) * (1 + Real.log β) := by
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); positivity
  calc Real.log N ≤ d * (Real.log 2 + a) * (1 + Real.log β) := by
        refine h1.trans (le_of_eq ?_); ring
    _ ≤ d * (Real.log 2 + a) * (1 + Real.log β) * T := le_mul_of_one_le_right hc hT
    _ = d * (Real.log 2 + a) * T * (1 + Real.log β) := by ring

/-- `log (Hd (L₀ + L₁)) ≤ (log (2Hd) + a) G`. -/
theorem log_HL_le {a L0 L1 : ℕ} {Hd : ℝ} (hHd : 1 ≤ Hd) (hL0 : (L0 : ℝ) = (β : ℝ) ^ a)
    (hL1 : L1 ≤ L0) (hL01 : 1 ≤ L0) :
    Real.log (Hd * (L0 + L1)) ≤ (Real.log (2 * Hd) + a) * (1 + Real.log β) := by
  have h1 : (L1 : ℝ) ≤ L0 := by exact_mod_cast hL1
  have h2 : (1 : ℝ) ≤ L0 := by exact_mod_cast hL01
  refine log_le_of_le_cpow (by linarith) hβ a (by positivity) ?_
  rw [← hL0]; nlinarith

/-- `log (1 + c S) ≤ (log (1 + c d) + b) G` when `S ≤ d β^b`. -/
theorem log_one_add_le {b d S : ℕ} {c : ℝ} (hc : 0 ≤ c) (hS : (S : ℝ) ≤ d * (β : ℝ) ^ b) :
    Real.log (1 + c * S) ≤ (Real.log (1 + c * d) + b) * (1 + Real.log β) := by
  have hb : (1 : ℝ) ≤ β := by exact_mod_cast hβ
  have hβb : (1 : ℝ) ≤ (β : ℝ) ^ b := one_le_pow₀ hb
  refine log_le_of_le_cpow (by nlinarith [Nat.cast_nonneg (α := ℝ) d]) hβ b (by positivity) ?_
  have : c * S ≤ c * d * (β : ℝ) ^ b := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hS hc
  nlinarith [Nat.cast_nonneg (α := ℝ) d]

section Terms

variable {a b d ℓ L0 L1 S TJ : ℕ} {T : ℝ} (hT : 1 ≤ T) (hL0 : (L0 : ℝ) = (β : ℝ) ^ a)
  (hL0T : (L0 : ℝ) ≤ T) (hL1 : L1 ≤ L0) (hL01 : 1 ≤ L0) (hTJ : (TJ : ℝ) ≤ (d + 1) * T)
  (hS : (S : ℝ) ≤ d * (β : ℝ) ^ b) (hL1S : (L1 : ℝ) * S ≤ d * T)
include hT hL0 hL0T hL1 hL01 hTJ hS hL1S

omit hL0T hS hL1S in
/-- `TJ · log (Hd (L₀+L₁)) ≤ (d+1)(log(2Hd) + a) T G`. -/
theorem TJ_log_HL_le {Hd : ℝ} (hHd : 1 ≤ Hd) :
    TJ * Real.log (Hd * (L0 + L1)) ≤ (d + 1) * (Real.log (2 * Hd) + a) * T * (1 + Real.log β) := by
  have h1 := log_HL_le hβ hHd hL0 hL1 hL01
  have h0 : 0 ≤ Real.log (Hd * (L0 + L1)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ L0 := by exact_mod_cast hL01
    nlinarith [Nat.cast_nonneg (α := ℝ) L1]
  calc TJ * Real.log (Hd * (L0 + L1)) ≤ ((d + 1) * T) * ((Real.log (2 * Hd) + a) * (1 + Real.log
    β)) :=
        mul_le_mul hTJ h1 h0 (by positivity)
    _ = (d + 1) * (Real.log (2 * Hd) + a) * T * (1 + Real.log β) := by ring

/-- **The analytic bound term.** -/
theorem log_B_le {Hd H0 H1 : ℝ} (hHd : 1 ≤ Hd) (hH0 : 0 ≤ H0) (hH1 : 0 ≤ H1) :
    Real.log ((Hd * (L0 + L1)) ^ TJ * (1 + 2 * (ℓ * S * H0)) ^ L0 *
        (Real.exp (2 * (ℓ * S * H1))) ^ L1) ≤
      ((d + 1) * (Real.log (2 * Hd) + a) + (Real.log (1 + 2 * ℓ * H0 * d) + b) + 2 * ℓ * d * H1) *
        T * (1 + Real.log β) := by
  have hb : (1 : ℝ) ≤ β := by exact_mod_cast hβ
  have hG : (1 : ℝ) ≤ 1 + Real.log β := by linarith [Real.log_nonneg hb]
  have hpos1 : 0 < Hd * (L0 + L1) := by
    have : (1 : ℝ) ≤ L0 := by exact_mod_cast hL01
    nlinarith [Nat.cast_nonneg (α := ℝ) L1]
  have hpos2 : 0 < 1 + 2 * (ℓ * S * H0) := by positivity
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_exp]
  have t1 := TJ_log_HL_le hβ hT hL0 hL1 hL01 hTJ hHd
  have t2 : (L0 : ℝ) * Real.log (1 + 2 * (ℓ * S * H0)) ≤
      (Real.log (1 + 2 * ℓ * H0 * d) + b) * T * (1 + Real.log β) := by
    have h := log_one_add_le hβ (c := 2 * ℓ * H0) (by positivity) hS
    have h0 : 0 ≤ Real.log (1 + 2 * (ℓ * S * H0)) :=
      Real.log_nonneg (by nlinarith [show (0 : ℝ) ≤ ℓ * S * H0 by positivity])
    have e : 1 + 2 * (ℓ * S * H0) = 1 + 2 * ℓ * H0 * S := by ring
    rw [e] at h0 ⊢
    calc (L0 : ℝ) * Real.log (1 + 2 * ℓ * H0 * S) ≤ T * ((Real.log (1 + 2 * ℓ * H0 * d) + b) *
          (1 + Real.log β)) := mul_le_mul hL0T h h0 (by positivity)
      _ = _ := by ring
  have t3 : (L1 : ℝ) * (2 * (ℓ * S * H1)) ≤ 2 * ℓ * d * H1 * T * (1 + Real.log β) := by
    have : (L1 : ℝ) * (2 * (ℓ * S * H1)) = 2 * ℓ * H1 * (L1 * S) := by ring
    rw [this]
    calc 2 * ℓ * H1 * ((L1 : ℝ) * S) ≤ 2 * ℓ * H1 * (d * T) :=
          mul_le_mul_of_nonneg_left hL1S (by positivity)
      _ = 2 * ℓ * d * H1 * T * 1 := by ring
      _ ≤ 2 * ℓ * d * H1 * T * (1 + Real.log β) :=
          mul_le_mul_of_nonneg_left hG (mul_nonneg (by positivity) (by linarith))
  nlinarith [t1, t2, t3]

omit hL0 hL1 hL01 hS in
/-- **The denominator term.** -/
theorem log_E_le {δ : ℕ} (hδ : 1 ≤ δ) :
    Real.log (((δ ^ TJ * δ ^ L0 * (δ ^ (ℓ * S)) ^ L1 : ℕ) : ℝ)) ≤
      Real.log δ * (d + 2 + ℓ * d) * T * (1 + Real.log β) := by
  have hb : (1 : ℝ) ≤ β := by exact_mod_cast hβ
  have hG : (1 : ℝ) ≤ 1 + Real.log β := by linarith [Real.log_nonneg hb]
  have hlδ : 0 ≤ Real.log δ := Real.log_nonneg (by exact_mod_cast hδ)
  have e : (((δ ^ TJ * δ ^ L0 * (δ ^ (ℓ * S)) ^ L1 : ℕ) : ℝ)) = (δ : ℝ) ^ (TJ + L0 + ℓ * S * L1)
    := by
    push_cast; rw [← pow_mul, ← pow_add, ← pow_add]
  rw [e, Real.log_pow]
  have hsum : ((TJ + L0 + ℓ * S * L1 : ℕ) : ℝ) ≤ (d + 2 + ℓ * d) * T := by
    push_cast
    have : (ℓ : ℝ) * S * L1 ≤ ℓ * (d * T) := by
      rw [mul_assoc, mul_comm (S : ℝ)]; exact mul_le_mul_of_nonneg_left hL1S (Nat.cast_nonneg _)
    nlinarith
  calc ((TJ + L0 + ℓ * S * L1 : ℕ) : ℝ) * Real.log δ ≤ ((d + 2 + ℓ * d) * T) * Real.log δ :=
        mul_le_mul_of_nonneg_right hsum hlδ
    _ = Real.log δ * (d + 2 + ℓ * d) * T * 1 := by ring
    _ ≤ Real.log δ * (d + 2 + ℓ * d) * T * (1 + Real.log β) :=
        mul_le_mul_of_nonneg_left hG (by positivity)

/-- **The house term.** -/
theorem log_H_le {Hd : ℝ} (hHd : 1 ≤ Hd) :
    Real.log ((Hd * (L0 + L1)) ^ TJ * (1 + ℓ * S * Hd) ^ L0 * (Hd ^ (ℓ * S)) ^ L1) ≤
      ((d + 1) * (Real.log (2 * Hd) + a) + (Real.log (1 + ℓ * Hd * d) + b) +
        ℓ * d * Real.log Hd) * T * (1 + Real.log β) := by
  have hb : (1 : ℝ) ≤ β := by exact_mod_cast hβ
  have hG : (1 : ℝ) ≤ 1 + Real.log β := by linarith [Real.log_nonneg hb]
  have hlH : 0 ≤ Real.log Hd := Real.log_nonneg hHd
  have hpos1 : 0 < Hd * (L0 + L1) := by
    have : (1 : ℝ) ≤ L0 := by exact_mod_cast hL01
    nlinarith [Nat.cast_nonneg (α := ℝ) L1]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
  have t1 := TJ_log_HL_le hβ hT hL0 hL1 hL01 hTJ hHd
  have t2 : (L0 : ℝ) * Real.log (1 + ℓ * S * Hd) ≤
      (Real.log (1 + ℓ * Hd * d) + b) * T * (1 + Real.log β) := by
    have h := log_one_add_le hβ (c := ℓ * Hd) (by positivity) hS
    have e : 1 + ℓ * S * Hd = 1 + ℓ * Hd * S := by ring
    have h0 : 0 ≤ Real.log (1 + ℓ * Hd * (S : ℝ)) := Real.log_nonneg (by
      nlinarith [show (0:ℝ) ≤ ℓ * Hd * S by positivity])
    rw [e]
    calc (L0 : ℝ) * Real.log (1 + ℓ * Hd * S) ≤ T * ((Real.log (1 + ℓ * Hd * d) + b) *
          (1 + Real.log β)) := mul_le_mul hL0T h h0 (by positivity)
      _ = _ := by ring
  have t3 : (L1 : ℝ) * (((ℓ * S : ℕ) : ℝ) * Real.log Hd) ≤ ℓ * d * Real.log Hd * T * (1 +
    Real.log β) := by
    push_cast
    have : (L1 : ℝ) * (ℓ * S * Real.log Hd) = ℓ * Real.log Hd * (L1 * S) := by ring
    rw [this]
    calc ℓ * Real.log Hd * ((L1 : ℝ) * S) ≤ ℓ * Real.log Hd * (d * T) :=
          mul_le_mul_of_nonneg_left hL1S (by positivity)
      _ = ℓ * d * Real.log Hd * T * 1 := by ring
      _ ≤ ℓ * d * Real.log Hd * T * (1 + Real.log β) :=
          mul_le_mul_of_nonneg_left hG (by positivity)
  nlinarith [t1, t2, t3]

end Terms

end StrongSix.Thm1

end LeanPool
