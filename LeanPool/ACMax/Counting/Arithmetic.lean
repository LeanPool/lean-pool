/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren and OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren, OpenAI
-/
module

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Scalar certificates for the sharp Moore bound

Keeping these integer arguments independent of graph definitions lets them elaborate
while the graph infrastructure builds.
-/

@[expose] public section

namespace ACMax.Arithmetic

open Classical in
/-- **The sharp strip cubic.**  The single-variable inequality the `n ≥ 123` region arithmetic
bottoms out at, after `X` is pushed to its master maximum and `H` to the end of its range.
Substituting `N = 123 + u` makes every coefficient non-negative
(`1068496017 + 1122649307u + 11552736u² + 20700u³`), giving an explicit positive certificate. -/
theorem strip_cubic_sharp {N : ℤ} (hN : 123 ≤ N) :
    779812849 * N + 755972700 < 20700 * N ^ 3 + 3914436 * N ^ 2 := by
  have hu : (0 : ℤ) ≤ N - 123 := by linarith
  have hidentity :
      20700 * N ^ 3 + 3914436 * N ^ 2 - (779812849 * N + 755972700) =
        1068496017 + 1122649307 * (N - 123) +
          11552736 * (N - 123) ^ 2 + 20700 * (N - 123) ^ 3 := by ring
  apply sub_pos.mp
  rw [hidentity]
  positivity

open Classical in
/-- **The two-variable core.**  After both `X`-eliminations the target is a cubic in `(N, H)`:

  `4608000·(N−H)² < 38400·(N−H)·(Q+120) + 23·P·Q²`,  `P = 6N+160−23H`, `Q = 16N+7H−150`.

Every `H`-coefficient of the gap is negative at `N ≥ 123`, so the minimum is at `17H = 4N − 200`,
and `4913·gap − cubic` is *identically* `289(M−17H)(−c₁) + 17(M²−(17H)²)(−c₂) + (M³−(17H)³)·25921`
with `M = 4N − 200`, `−c₁ = 104512N² − 11944120N + 18478500 ≥ 0` (its larger root is `≈ 112.7`)
and `−c₂ = 111734N + 3585580 ≥ 0`.  So `linarith` closes on those three products plus the cubic. -/
theorem moore_strip_twovar_sharp {N H : ℤ} (hN : 123 ≤ N) (hH : 0 ≤ H)
    (hs : 17 * H ≤ 4 * N - 200) :
    4608000 * (N - H) ^ 2
      < 38400 * ((N - H) * (16 * N + 7 * H - 30))
        + 23 * ((6 * N + 160 - 23 * H) * (16 * N + 7 * H - 150) ^ 2) := by
  have hd : (0 : ℤ) ≤ (4 * N - 200) - 17 * H := by linarith
  have hHm : (0 : ℤ) ≤ 17 * H := by linarith
  have hnc1 : (0 : ℤ) ≤ 104512 * N ^ 2 - 11944120 * N + 18478500 := by
    have hidentity :
        104512 * N ^ 2 - 11944120 * N + 18478500 =
          104512 * (N - 123) ^ 2 + 13765832 * (N - 123) + 130513788 := by ring
    rw [hidentity]
    have hu : (0 : ℤ) ≤ N - 123 := sub_nonneg.mpr hN
    positivity
  have hnc2 : (0 : ℤ) ≤ 111734 * N + 3585580 := by linarith
  have hsq : (0 : ℤ) ≤ (4 * N - 200) ^ 2 + 17 * H * (4 * N - 200) + (17 * H) ^ 2 := by
    exact add_nonneg (add_nonneg (sq_nonneg _)
      (mul_nonneg hHm (by linarith only [hd, hHm]))) (sq_nonneg _)
  have e1 := mul_nonneg hd hnc1
  have e2 := mul_nonneg (mul_nonneg hd (by linarith : (0 : ℤ) ≤ (4 * N - 200) + 17 * H)) hnc2
  have e3 := mul_nonneg (mul_nonneg hd hsq) (by norm_num : (0 : ℤ) ≤ 25921)
  have hcub := strip_cubic_sharp hN
  linarith only [e1, e2, e3, hcub]

open Classical in
/-- **The `R`-free core of the sharp strip discharge.**  On the counting region
(`0 ≤ H ≤ X`, `10X + 7H ≤ 4N − 200`) at `N ≥ 123`,

  `4608·(N−H)² < 384·(N−H)·(2N−X−23) + 23·(N−4−X−3H)·(2N−X−35)²`.

Both `X`-dependent factors are pushed to the master maximum simultaneously — `10·t ≥ 6N+160−23H`
and `10·A ≥ 16N+7H−150`, equalities together at `X = X_max` — and `moore_strip_twovar_sharp`
closes what is left. -/
theorem moore_strip_core_sharp {N X H : ℤ} (hN : 123 ≤ N) (hH : 0 ≤ H) (hHX : H ≤ X)
    (hmaster : 10 * X + 7 * H ≤ 4 * N - 200) :
    4608 * (N - H) ^ 2
      < 384 * ((N - H) * (2 * N - X - 23))
        + 23 * ((N - 4 - X - 3 * H) * (2 * N - X - 35) ^ 2) := by
  have h17 : 17 * H ≤ 4 * N - 200 := by linarith
  have hvpos : (0 : ℤ) ≤ N - H := by linarith
  have hPpos : (0 : ℤ) ≤ 6 * N + 160 - 23 * H := by linarith
  have hQpos : (0 : ℤ) ≤ 16 * N + 7 * H - 150 := by linarith
  have hP : 6 * N + 160 - 23 * H ≤ 10 * (N - 4 - X - 3 * H) := by linarith
  have hQ : 16 * N + 7 * H - 150 ≤ 10 * (2 * N - X - 35) := by linarith
  -- the ball factor, pushed to the master maximum
  have hA : 38400 * ((N - H) * (16 * N + 7 * H - 30))
      ≤ 1000 * (384 * ((N - H) * (2 * N - X - 23))) := by
    convert mul_le_mul_of_nonneg_left (add_le_add_right hQ 120)
      (mul_nonneg (by norm_num : (0 : ℤ) ≤ 38400) hvpos) using 1 <;> ring
  -- the excess factor, pushed to the master maximum
  have hQ2 : (16 * N + 7 * H - 150) ^ 2 ≤ (10 * (2 * N - X - 35)) ^ 2 := by
    exact pow_le_pow_left₀ hQpos hQ 2
  have hmul : (6 * N + 160 - 23 * H) * (16 * N + 7 * H - 150) ^ 2
      ≤ (10 * (N - 4 - X - 3 * H)) * (10 * (2 * N - X - 35)) ^ 2 :=
    mul_le_mul hP hQ2 (sq_nonneg _) (by linarith)
  have hB : 23 * ((6 * N + 160 - 23 * H) * (16 * N + 7 * H - 150) ^ 2)
      ≤ 1000 * (23 * ((N - 4 - X - 3 * H) * (2 * N - X - 35) ^ 2)) := by
    convert mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℤ) ≤ 23) using 1; ring
  have htv := moore_strip_twovar_sharp hN hH h17
  linarith only [hA, hB, htv]

end ACMax.Arithmetic
