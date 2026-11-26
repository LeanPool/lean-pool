/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R417.LogErrorAbsorption
public import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! Choosing the dimension and an odd modulus at every sufficiently large order. -/

@[expose] public section

namespace GapExtremal.R434

open Real

theorem odd_floor_close {x : ℝ} (hx : 1 ≤ x) :
    ∃ m : ℕ, Odd m ∧ (m : ℝ) ≤ x ∧ x < (m : ℝ) + 2 := by
  let y := (x - 1) / 2
  let k := ⌊y⌋₊
  refine ⟨2 * k + 1, ⟨k, by omega⟩, ?_, ?_⟩
  · push_cast
    have hk : (k : ℝ) ≤ y := Nat.floor_le (by dsimp [y]; linarith)
    dsimp only [y] at hk
    linarith
  · push_cast
    have hk : y < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    dsimp only [y] at hk
    linarith

theorem log_linear_error (A B d : ℝ) (hA : 0 ≤ A) (hd : 0 < d) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t : ℝ, T ≤ t → A * log t + B ≤ d * t := by
  obtain ⟨T,hT,h⟩ := R417.log_error_absorption A B d hA hd
  refine ⟨T,hT,fun t ht => ?_⟩
  have ht₀ : 0 < t := by linarith
  apply (mul_le_mul_iff_left₀ ht₀).mp
  convert h t ht using 1 <;> ring

theorem rounded_order_witness (H : ℕ → ℕ) (A c : ℝ) (hA : 1 ≤ A)
    (hc : 0 < c) (W : ℝ) (hW : 10 ≤ W) (m₀ : ℕ)
    (hH : ∀ j : ℕ, 1 ≤ j → 1 ≤ H j ∧ (H j : ℝ) ≤ A * (j : ℝ)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ m j : ℕ,
      1 ≤ m ∧ m₀ ≤ m ∧ Odd m ∧ 1 ≤ j ∧ H j * m ^ (2*j) ≤ n ∧
      W / 2 * (j : ℝ) ≤ m ∧ 0 < (n : ℝ) ∧
      let t := sqrt (log n / c)
      (m₀ : ℝ) + 2 ≤ t ∧ (j : ℝ) ≤ t ∧ log n = c * t^2 ∧
      2 * (log n - 2 * (j : ℝ) * log (m : ℝ)) ≤ 2 * (log A + log t + 1) ∧
      2 * log (m : ℝ) ≤ c * (t + 2) := by
  obtain ⟨T₁,hT₁,h₁⟩ := log_linear_error 1 (log A) (c/2) (by norm_num) (by positivity)
  have hWpos : 0 < W := by linarith
  let T := 2 + T₁ + 32 * W / c ^ 2 + (m₀ : ℝ) + 2
  refine ⟨⌈exp (c * T ^ 2)⌉₊, fun n hn => ?_⟩
  have hT : 2 ≤ T := by
    dsimp [T]
    have : 0 ≤ 32 * W / c ^ 2 := by positivity
    have : 0 ≤ (m₀ : ℝ) := by positivity
    linarith
  have hT₁' : T₁ ≤ T := by
    dsimp [T]
    have : 0 ≤ 32 * W / c ^ 2 := by positivity
    have : 0 ≤ (m₀ : ℝ) := by positivity
    linarith
  have hTlarge : 32 * W / c ^ 2 ≤ T := by
    dsimp [T]
    have : 0 ≤ (m₀ : ℝ) := by positivity
    linarith
  have hTm : (m₀ : ℝ) + 2 ≤ T := by
    dsimp [T]
    have : 0 ≤ 32 * W / c ^ 2 := by positivity
    linarith
  have hnR : exp (c * T ^ 2) ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hn₀ : 0 < (n : ℝ) := (exp_pos _).trans_le hnR
  let L := log (n : ℝ)
  have hL : c * T ^ 2 ≤ L := by
    simpa only [log_exp] using (log_le_log_iff (exp_pos _) hn₀).mpr hnR
  have hL₀ : 0 ≤ L := (by positivity : 0 ≤ c * T ^ 2).trans hL
  let t := sqrt (L / c)
  have ht : T ≤ t := by
    apply le_sqrt_of_sq_le
    exact (le_div_iff₀ hc).mpr (by nlinarith only [hL])
  have ht2 : 2 ≤ t := hT.trans ht
  have ht₀ : 0 < t := by linarith
  have hLt : L = c * t ^ 2 := by
    dsimp [t]
    rw [sq_sqrt (by positivity), mul_div_cancel₀ _ hc.ne']
  let j := ⌊t⌋₊
  have hj₁ : 1 ≤ j := Nat.le_floor (by norm_cast; linarith)
  have hjU : (j : ℝ) ≤ t := Nat.floor_le ht₀.le
  have hjL : t < (j : ℝ) + 1 := Nat.lt_floor_add_one t
  have hjpos : 0 < (j : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hj₁)
  obtain ⟨hH₁,hHU⟩ := hH j hj₁
  have hHpos : 0 < (H j : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hH₁)
  have hlogH₀ : 0 ≤ log (H j : ℝ) := log_natCast_nonneg _
  have hlogH : log (H j : ℝ) ≤ log A + log t := by
    rw [← log_mul (by linarith : A ≠ 0) ht₀.ne']
    apply (log_le_log_iff hHpos (by positivity)).mpr
    exact hHU.trans (mul_le_mul_of_nonneg_left hjU (by linarith))
  have hlogH' : log (H j : ℝ) ≤ L / 2 := by
    have hh := h₁ t (hT₁'.trans ht)
    have ht' : t ≤ t ^ 2 := by nlinarith only [mul_nonneg ht₀.le (show 0 ≤ t - 1 by linarith)]
    have hh' := mul_le_mul_of_nonneg_left ht' (show 0 ≤ c/2 by positivity)
    rw [hLt]
    nlinarith only [hlogH, hh, hh']
  let x := exp ((L - log (H j : ℝ)) / (2 * (j : ℝ)))
  have hxpos : 0 < x := exp_pos _
  have hxLog : 2 * (j : ℝ) * log x = L - log (H j : ℝ) := by
    simp only [x, log_exp]
    field_simp
  have hxLower : c * t / 4 ≤ log x := by
    have hp := mul_le_mul_of_nonneg_left hjU (show 0 ≤ c*t/2 by positivity)
    apply (mul_le_mul_iff_left₀ (show 0 < 2 * (j : ℝ) by positivity)).mp
    nlinarith only [hp,hlogH',hLt,hxLog]
  have hxWide : W * t ≤ x := by
    have hlarge : 32 * W ≤ c ^ 2 * t :=
      (div_le_iff₀ (sq_pos_of_pos hc)).mp (hTlarge.trans ht) |>.trans_eq (mul_comm _ _)
    have hmul := mul_le_mul_of_nonneg_right hlarge ht₀.le
    have hq := quadratic_le_exp_of_nonneg (show 0 ≤ c * t / 4 by positivity)
    have hx := (exp_le_exp.mpr hxLower)
    rw [exp_log hxpos] at hx
    nlinarith only [hmul,hq,hx,show 0 ≤ c*t/4 by positivity]
  have h8 : 8*t ≤ x := (mul_le_mul_of_nonneg_right (by linarith : 8 ≤ W) ht₀.le).trans hxWide
  obtain ⟨m,hmOdd,hmx,hxm⟩ := odd_floor_close (x := x) (by linarith)
  have hm₁ : 1 ≤ m := by exact_mod_cast (show (1 : ℝ) ≤ m by linarith)
  have hm₀ : m₀ ≤ m := by
    have h := hTm.trans ht
    exact_mod_cast (show (m₀ : ℝ) ≤ m by linarith)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm₁
  have hmpos : 0 < (m : ℝ) := by linarith
  have hmLog₀ : 0 ≤ log (m : ℝ) := log_nonneg hmR
  have hmLog : log (m : ℝ) ≤ log x := (log_le_log_iff hmpos hxpos).mpr hmx
  have hmLogLoss : 2 * (j : ℝ) * (log x - log (m : ℝ)) ≤ 1 := by
    have h := log_le_sub_one_of_pos (div_pos hxpos hmpos)
    rw [log_div hxpos.ne' hmpos.ne', div_sub_one hmpos.ne'] at h
    have h' := (le_div_iff₀ hmpos).mp h
    have hm4 : 4 * (j : ℝ) ≤ m := by linarith
    have hmLoss₀ : 0 ≤ log x - log (m : ℝ) := sub_nonneg.mpr hmLog
    have hmul := mul_le_mul_of_nonneg_right hm4 hmLoss₀
    nlinarith only [h',hxm,hmul]
  have horder : H j * m ^ (2 * j) ≤ n := by
    have hcast : (H j : ℝ) * (m : ℝ) ^ (2*j) ≤ (n : ℝ) := by
      apply (log_le_log_iff (by positivity) hn₀).mp
      rw [log_mul hHpos.ne' (pow_ne_zero _ hmpos.ne'), log_pow]
      push_cast
      have hp := mul_le_mul_of_nonneg_left hmLog (show 0 ≤ 2 * (j : ℝ) by positivity)
      linarith only [hp,hxLog]
    exact_mod_cast hcast
  have hshort : 2 * log (m : ℝ) ≤ c * (t + 2) := by
    have hcj : c * (t - 1) ≤ c * (j : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith) hc.le
    have hprod := mul_le_mul_of_nonneg_right hcj (show 0 ≤ t + 2 by linarith)
    have hct := mul_nonneg hc.le (show 0 ≤ t - 2 by linarith)
    have hupper := mul_le_mul_of_nonneg_left hmLog (show 0 ≤ 2 * (j : ℝ) by positivity)
    apply (mul_le_mul_iff_left₀ hjpos).mp
    nlinarith only [hupper,hxLog,hlogH₀,hprod,hct,hLt]
  refine ⟨m,j,hm₁,hm₀,hmOdd,hj₁,horder,?_,hn₀,hTm.trans ht,hjU,hLt,?_,hshort⟩
  · have hp := mul_le_mul_of_nonneg_left hjU hWpos.le
    have hwt := mul_le_mul_of_nonneg_right hW ht₀.le
    linarith only [hp,hwt,hxWide,hxm,ht2]
  · linarith only [hmLogLoss,hlogH,hxLog,
      show 2 * (j : ℝ) * (log x - log (m : ℝ)) =
        2 * (j : ℝ) * log x - 2 * (j : ℝ) * log (m : ℝ) by ring]

theorem uniform_order_parameters (H : ℕ → ℕ) (A K c η : ℝ) (hA : 1 ≤ A) (hK : 0 ≤ K)
    (hc : 0 < c) (hη : 0 < η) (m₀ : ℕ)
    (hH : ∀ j : ℕ, 1 ≤ j → 1 ≤ H j ∧ (H j : ℝ) ≤ A * (j : ℝ)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ m j : ℕ,
      1 ≤ m ∧ m₀ ≤ m ∧ Odd m ∧ 1 ≤ j ∧ H j * m ^ (2 * j) ≤ n ∧
      (n : ℝ) ^ 2 * exp (-(2 * sqrt c + η) * sqrt (log n)) ≤
        exp (-c * (j : ℝ)) * (m : ℝ) ^ (4 * j) /
          (27 * (1 + K * (j : ℝ) * (m : ℝ) ^ 2)) := by
  let C := 27 * (1 + K)
  have hC₀ : 0 < C := by dsimp [C]; positivity
  let b := 2 * log A + 2 + 2 * c + log C
  obtain ⟨T₂,hT₂,h₂⟩ := log_linear_error 3 b (η * sqrt c) (by norm_num)
    (mul_pos hη (sqrt_pos.mpr hc))
  let M := max m₀ ⌈T₂⌉₊
  obtain ⟨N,hN⟩ := rounded_order_witness H A c hA hc 10 (by norm_num) M hH
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨m,j,hm₁,hmM,hmOdd,hj₁,horder,_,hn₀,htM,hjU,hLt,hround,hshort⟩ := hN n hn
  let L := log (n : ℝ)
  let t := sqrt (L / c)
  change (M : ℝ) + 2 ≤ t at htM
  change (j : ℝ) ≤ t at hjU
  change L = c * t^2 at hLt
  change 2 * (L - 2 * (j : ℝ) * log (m : ℝ)) ≤ 2*(log A + log t + 1) at hround
  change _ ≤ c*(t+2) at hshort
  have hM : T₂ ≤ (M : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right m₀ ⌈T₂⌉₊))
  have ht₀ : 0 < t := by linarith
  have hjpos : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm₁
  have hmpos : 0 < (m : ℝ) := by linarith
  have hm₀ := (le_max_left m₀ ⌈T₂⌉₊).trans hmM
  have hsqrt : sqrt L = sqrt c * t := by rw [hLt, sqrt_mul hc.le, sqrt_sq ht₀.le]
  have hjLog : log (j : ℝ) ≤ log t := (log_le_log_iff hjpos ht₀).mpr hjU
  let D := 27 * (1 + K * (j : ℝ) * (m : ℝ) ^ 2)
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hDLog : log D ≤ log C + log (j : ℝ) + 2 * log (m : ℝ) := by
    have hm2 : 1 ≤ (m : ℝ)^2 := by
      nlinarith only [mul_nonneg (show 0 ≤ (m:ℝ)-1 by linarith) (show 0 ≤ (m:ℝ)+1 by positivity)]
    have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj₁
    have hmul : 1 ≤ (j : ℝ) * (m : ℝ)^2 :=
      one_le_mul_of_one_le_of_one_le hjR hm2
    have hD : D ≤ C * (j : ℝ) * (m : ℝ)^2 := by
      dsimp [D,C]
      linarith only [hmul, show 27 * (1 + K) * (j : ℝ) * (m : ℝ) ^ 2 -
        27 * (1 + K * (j : ℝ) * (m : ℝ) ^ 2) =
        27 * ((j : ℝ) * (m : ℝ)^2 - 1) by ring]
    have h := (log_le_log_iff hDpos (show 0 < C * (j : ℝ) * (m : ℝ)^2 by positivity)).mpr hD
    rw [log_mul (by positivity : C * (j : ℝ) ≠ 0) (pow_ne_zero _ hmpos.ne'),
      log_mul hC₀.ne' hjpos.ne', log_pow] at h
    norm_num at h
    exact h
  have herror := h₂ t (by linarith only [htM,hM])
  have hcoef := mul_le_mul_of_nonneg_left hjU hc.le
  have hloss : 2 * (L - 2 * (j : ℝ) * log (m : ℝ)) +
      c * (j : ℝ) + log D ≤ (2 * sqrt c + η) * sqrt L := by
    rw [hsqrt]
    have heq := sq_sqrt hc.le
    have hright : (2 * sqrt c + η) * (sqrt c * t) = 2*c*t + (η * sqrt c) * t := by
      calc
        _ = 2 * (sqrt c)^2 * t + (η * sqrt c) * t := by ring
        _ = _ := by rw [heq]
    rw [hright]
    dsimp [b] at herror
    linarith only [herror,hcoef,hDLog,hjLog,hround,hshort]
  refine ⟨m,j,hm₁,hm₀,hmOdd,hj₁,horder,?_⟩
  change (n : ℝ)^2 * exp (-(2 * sqrt c + η) * sqrt L) ≤ exp (-c * (j : ℝ)) * (m : ℝ)^(4*j) / D
  apply (log_le_log_iff (by positivity) (by positivity)).mp
  rw [log_mul (pow_ne_zero _ hn₀.ne') (exp_pos _).ne', log_pow, log_exp,
    log_div (by positivity : exp (-c * (j : ℝ)) * (m : ℝ) ^ (4*j) ≠ 0) hDpos.ne',
    log_mul (exp_pos _).ne' (pow_ne_zero _ hmpos.ne'), log_exp, log_pow]
  push_cast
  change 2 * L + -(2 * sqrt c + η) * sqrt L ≤
    -c * (j : ℝ) + (4 * (j : ℝ)) * log (m : ℝ) - log D
  linarith only [hloss]

end GapExtremal.R434
