/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastLinearLedger

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastLinearDecay

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The linear level schedule's geometric conversion: `hdecay` at a law-free rate

second half.  The exact log-level recursion of the
squaring level schedule (`linY_succ`: `y_{j+1} = 2y_j − log₃(128A²)`, hence
`z := y − log₃(128A²)` doubles exactly), the per-round spacing bound
`s_j ≤ Cs·y_j` with the single explicit constant `linCs` (every logarithm
in the lags, memories, window counts, and pads is at most a multiple of
the level logarithm once `y_j ≥ 1`), and the telescoping
`r_{j+1} − r_0 ≤ 4·Cs·z_j` give

`F n ≤ ((3:ℝ)^(−linRate))^(n − nStart)` for `n ≥ nStart := linR … 0`,

with `linRate := 1/(4·linCs)` — an explicit function of
`(A, α, b₀, b_A, b₂, c_A, S₀)` only: LAW-FREE at the instantiation where
`S₀` is the dimension-only lag channel, and the start `nStart` linear in
`ns + log₃S₁/b_A + log₃S₂/b₂` — the one-time burn-in.
-/

namespace HCPolySupport.HighContrast.Quenched

noncomputable section

/-- The level logarithm. -/
@[expose]
def linY (A d0 : ℝ) (j : ℕ) : ℝ := Real.logb 3 (1 / linLam A d0 j)

/-- The centered level logarithm: doubles exactly. -/
@[expose]
def linZ (A d0 : ℝ) (j : ℕ) : ℝ :=
  linY A d0 j - Real.logb 3 (128 * A ^ 2)

/-- The single spacing constant. -/
@[expose]
def linCs (A alpha b0 bA b2 : ℝ) (cA : ℕ) (S0 : ℝ) : ℝ :=
  (Real.logb 3 S0 / b0 + 2 / b0 + 1) + (2 / alpha + 1) +
    (1 / Real.logb 3 ((2 * A + 1) / (2 * A)) + 1) * ((cA : ℝ) + 1) +
    (2 / bA + 2 / b2 + 2) + 1

/-- The law-free conclusion rate. -/
@[expose]
def linRate (A alpha b0 bA b2 : ℝ) (cA : ℕ) (S0 : ℝ) : ℝ :=
  1 / (4 * linCs A alpha b0 bA b2 cA S0)

theorem linY_succ {A d0 : ℝ} (hA : 1 ≤ A) (hd0 : 0 < d0) (j : ℕ) :
    linY A d0 (j + 1) = 2 * linY A d0 j - Real.logb 3 (128 * A ^ 2) := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA
  have hlam := linLam_pos hA hd0 j
  have hsplit : (1 : ℝ) / linLam A d0 (j + 1) =
      (128 * A ^ 2)⁻¹ * (1 / linLam A d0 j) ^ 2 := by
    rw [linLam_succ]
    field_simp
  rw [linY, linY, hsplit, Real.logb_mul (by positivity) (by positivity),
    Real.logb_inv, Real.logb_pow]
  push_cast
  ring

theorem linZ_succ {A d0 : ℝ} (hA : 1 ≤ A) (hd0 : 0 < d0) (j : ℕ) :
    linZ A d0 (j + 1) = 2 * linZ A d0 j := by
  rw [linZ, linZ, linY_succ hA hd0]
  ring

theorem linZ_eq {A d0 : ℝ} (hA : 1 ≤ A) (hd0 : 0 < d0) (j : ℕ) :
    linZ A d0 j = 2 ^ j * linZ A d0 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [linZ_succ hA hd0, ih, pow_succ]
      ring

/-- The base separation from the strengthened smallness. -/
theorem linZ_zero_ge {A d0 : ℝ} (hA : 1 ≤ A) (hd0 : 0 < d0)
    (hgs3 : (128 * A ^ 2) ^ 3 * d0 ≤ 1 / 3) :
    Real.logb 3 (128 * A ^ 2) + 1 ≤ linZ A d0 0 := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA
  have h128 : (1 : ℝ) ≤ 128 * A ^ 2 := by nlinarith only [hA]
  have hlogpos : 0 ≤ Real.logb 3 (128 * A ^ 2) :=
    Real.logb_nonneg (by norm_num) h128
  have hy0 : Real.logb 3 (3 * (128 * A ^ 2) ^ 3) ≤ linY A d0 0 := by
    rw [linY]
    refine Real.logb_le_logb_of_le (by norm_num) (by positivity) ?_
    show (3 : ℝ) * (128 * A ^ 2) ^ 3 ≤ 1 / linLam A d0 0
    have hlam0 : linLam A d0 0 = d0 := rfl
    rw [hlam0, le_div_iff₀ hd0]
    nlinarith only [hgs3, hd0]
  have hexpand : Real.logb 3 (3 * (128 * A ^ 2) ^ 3) =
      1 + 3 * Real.logb 3 (128 * A ^ 2) := by
    have h1 : (0 : ℝ) < 128 * A ^ 2 := by positivity
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow]
    have : Real.logb 3 3 = 1 := Real.logb_self_eq_one (by norm_num)
    rw [this]
    push_cast
    ring
  rw [linZ]
  rw [hexpand] at hy0
  linarith only [hy0, hlogpos]

theorem linZ_one_le {A d0 : ℝ} (hA : 1 ≤ A) (hd0 : 0 < d0)
    (hgs3 : (128 * A ^ 2) ^ 3 * d0 ≤ 1 / 3) (j : ℕ) :
    1 ≤ linZ A d0 j := by
  have h128 : (1 : ℝ) ≤ 128 * A ^ 2 := by nlinarith only [hA]
  have hlogpos : 0 ≤ Real.logb 3 (128 * A ^ 2) :=
    Real.logb_nonneg (by norm_num) h128
  have hz0 : 1 ≤ linZ A d0 0 := by
    have h1 := linZ_zero_ge hA hd0 hgs3
    linarith only [h1, hlogpos]
  have heq := linZ_eq hA hd0 j
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hz0one : (1 : ℝ) ≤ linZ A d0 0 := hz0
  nlinarith only [heq, h2j, hz0one]

theorem linY_ge_linZ {A d0 : ℝ} (hA : 1 ≤ A) (j : ℕ) :
    linZ A d0 j ≤ linY A d0 j := by
  have h128 : (1 : ℝ) ≤ 128 * A ^ 2 := by nlinarith only [hA]
  have hlogpos : 0 ≤ Real.logb 3 (128 * A ^ 2) :=
    Real.logb_nonneg (by norm_num) h128
  rw [linZ]
  linarith only [hlogpos]

theorem linY_le_two_linZ {A d0 : ℝ} (hA : 1 ≤ A) (hd0 : 0 < d0)
    (hgs3 : (128 * A ^ 2) ^ 3 * d0 ≤ 1 / 3) (j : ℕ) :
    linY A d0 j ≤ 2 * linZ A d0 j := by
  have hz0 := linZ_zero_ge hA hd0 hgs3
  have hcz : Real.logb 3 (128 * A ^ 2) ≤ linZ A d0 j := by
    have h1 : linZ A d0 0 ≤ linZ A d0 j := by
      have heq := linZ_eq hA hd0 j
      have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      have hlp : 0 ≤ Real.logb 3 (128 * A ^ 2) :=
        Real.logb_nonneg (by norm_num) (by nlinarith only [hA])
      have hz0pos : 0 ≤ linZ A d0 0 := by linarith only [hz0, hlp]
      nlinarith only [heq, h2j, hz0pos]
    have h2 : Real.logb 3 (128 * A ^ 2) ≤ linZ A d0 0 := by
      linarith only [hz0]
    linarith only [h1, h2]
  rw [linZ] at hcz ⊢
  linarith only [hcz]

/-- The level value in rpow form. -/
theorem linLam_eq_rpow {A d0 : ℝ} (hA : 1 ≤ A) (hd0 : 0 < d0) (j : ℕ) :
    linLam A d0 j = (3 : ℝ) ^ (-(linY A d0 j)) := by
  have hlam := linLam_pos hA hd0 j
  rw [linY, one_div, Real.logb_inv]
  rw [neg_neg]
  exact (Real.rpow_logb (by norm_num) (by norm_num) hlam).symm

/-! ## The spacing bound and the telescoping -/

theorem linCs_one_le {A alpha b0 bA b2 : ℝ} {cA : ℕ} {S0 : ℝ}
    (hA : 1 ≤ A) (halpha : 0 < alpha) (hb0 : 0 < b0) (hbA : 0 < bA)
    (hb2 : 0 < b2) (hS0 : 1 ≤ S0) :
    1 ≤ linCs A alpha b0 bA b2 cA S0 := by
  have hrate : 0 < Real.logb 3 ((2 * A + 1) / (2 * A)) := by
    have h1 : (1 : ℝ) < (2 * A + 1) / (2 * A) := by
      rw [lt_div_iff₀ (by positivity)]
      linarith only []
    exact Real.logb_pos (by norm_num) h1
  have h1 : 0 ≤ Real.logb 3 S0 := Real.logb_nonneg (by norm_num) hS0
  have h2 : (0 : ℝ) ≤ Real.logb 3 S0 / b0 := by positivity
  have h3 : (0 : ℝ) < 2 / b0 := by positivity
  have h4 : (0 : ℝ) < 2 / alpha := by positivity
  have h5 : (0 : ℝ) < 2 / bA := by positivity
  have h6 : (0 : ℝ) < 2 / b2 := by positivity
  have h7 : (0 : ℝ) <
      (1 / Real.logb 3 ((2 * A + 1) / (2 * A)) + 1) * ((cA : ℝ) + 1) := by
    have h8 : (0 : ℝ) < 1 / Real.logb 3 ((2 * A + 1) / (2 * A)) + 1 := by
      positivity
    have h9 : (0 : ℝ) < (cA : ℝ) + 1 := by positivity
    positivity
  rw [linCs]
  linarith only [h2, h3, h4, h5, h6, h7]

/-- The strengthened smallness implies the plain one. -/
theorem gs_of_gs3 {A d0 : ℝ} (hA : 1 ≤ A) (hd0 : 0 < d0)
    (hgs3 : (128 * A ^ 2) ^ 3 * d0 ≤ 1 / 3) :
    128 * A ^ 2 * d0 ≤ 1 := by
  have h128 : (1 : ℝ) ≤ 128 * A ^ 2 := by nlinarith only [hA]
  have hxd : (0 : ℝ) ≤ 128 * A ^ 2 * d0 := by positivity
  have hsq : (0 : ℝ) ≤ (128 * A ^ 2) ^ 2 - 1 := by nlinarith only [h128]
  have h3 : (0 : ℝ) ≤ (128 * A ^ 2 * d0) * ((128 * A ^ 2) ^ 2 - 1) :=
    mul_nonneg hxd hsq
  nlinarith only [hgs3, h3]


private theorem linear_source_spacing_bound {A b0 d0 S0 : ℝ} {j : ℕ}
    (hA : 1 ≤ A) (hb0 : 0 < b0)
     (hS0 : 1 ≤ S0) (hd0 : 0 < d0)
    (hA0 : (0 : ℝ) < A)
    (hgs : 128 * A ^ 2 * d0 ≤ 1)
    (hd01 : d0 ≤ 1)
    (hy1 : 1 ≤ (linY A d0 j))
    (hlamsq : Real.logb 3 (1 / linLam A d0 j ^ 2) = 2 * (linY A d0 j))
    : ((1 : ℝ) ≤ S0 / (2 * A * linLam A d0 j ^ 2)) ∧
    (Real.logb 3 (S0 / (2 * A * linLam A d0 j ^ 2)) / b0 ≤
      (Real.logb 3 S0 + 2 * (linY A d0 j)) / b0) ∧
    (((linL A b0 S0 (linLam A d0 j) : ℕ) : ℝ) ≤
      (linY A d0 j) * (Real.logb 3 S0 / b0 + 2 / b0 + 1)) := by
  classical
  have hlam := linLam_pos hA hd0 j
  have hlamd0 := linLam_le_floor hA hd0 hgs j
  set y : ℝ := linY A d0 j with hydef
  have hLarg : (1 : ℝ) ≤ S0 / (2 * A * linLam A d0 j ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    have h0 : linLam A d0 j ^ 2 ≤ d0 ^ 2 := by nlinarith only [hlamd0, hlam]
    have h1 : 2 * A * linLam A d0 j ^ 2 ≤ 2 * A * d0 ^ 2 := by
      nlinarith only [h0, hA0]
    have h2 : 2 * A * d0 ^ 2 ≤ d0 := by
      have h3 : 2 * A * d0 ≤ 1 := by
        have h4 : (0 : ℝ) ≤ A * d0 * (128 * A - 2) :=
          mul_nonneg (by positivity) (by nlinarith only [hA])
        nlinarith only [hgs, h4]
      nlinarith only [h3, hd0]
    linarith only [h1, h2, hd01, hS0]
  have hLx : Real.logb 3 (S0 / (2 * A * linLam A d0 j ^ 2)) / b0 ≤
      (Real.logb 3 S0 + 2 * y) / b0 := by
    refine div_le_div_of_nonneg_right ?_ hb0.le
    change Real.logb 3 (S0 / (2 * A * linLam A d0 j ^ 2)) ≤
        Real.logb 3 S0 + 2 * y
    have hbody : Real.logb 3 (S0 / (2 * A * linLam A d0 j ^ 2)) ≤
        Real.logb 3 S0 + 2 * y := by
      rw [Real.logb_div (by positivity) (by positivity)]
      have h2 : Real.logb 3 (1 / linLam A d0 j ^ 2) = 2 * y := hlamsq
      have h3 : Real.logb 3 (linLam A d0 j ^ 2) = -(2 * y) := by
        have := hlamsq
        rw [one_div, Real.logb_inv] at this
        linarith only [this]
      have h4 : Real.logb 3 (linLam A d0 j ^ 2) ≤
          Real.logb 3 (2 * A * linLam A d0 j ^ 2) := by
        refine Real.logb_le_logb_of_le (by norm_num) (by positivity) ?_
        nlinarith only [hA, sq_nonneg (linLam A d0 j), hlam]
      linarith only [h3, h4]
    exact hbody
  have hL : ((linL A b0 S0 (linLam A d0 j) : ℕ) : ℝ) ≤
      y * (Real.logb 3 S0 / b0 + 2 / b0 + 1) := by
    have hxpos : 0 ≤ Real.logb 3 (S0 / (2 * A * linLam A d0 j ^ 2)) / b0 := by
      have := Real.logb_nonneg (by norm_num : (1:ℝ) < 3) hLarg
      positivity
    have hceil : ((linL A b0 S0 (linLam A d0 j) : ℕ) : ℝ) ≤
        Real.logb 3 (S0 / (2 * A * linLam A d0 j ^ 2)) / b0 + 1 := by
      rw [linL]
      exact (Nat.ceil_lt_add_one hxpos).le
    have h1 : 0 ≤ Real.logb 3 S0 := Real.logb_nonneg (by norm_num) hS0
    have h2 : Real.logb 3 (S0 / (2 * A * linLam A d0 j ^ 2)) / b0 ≤
        Real.logb 3 S0 / b0 + 2 * y / b0 := by
      have := hLx
      calc Real.logb 3 (S0 / (2 * A * linLam A d0 j ^ 2)) / b0 ≤
          (Real.logb 3 S0 + 2 * y) / b0 := this
        _ = Real.logb 3 S0 / b0 + 2 * y / b0 := by ring
    have h3 : (0 : ℝ) < 2 / b0 := by positivity
    have h4 : (0 : ℝ) ≤ Real.logb 3 S0 / b0 := by positivity
    have hexp : y * (Real.logb 3 S0 / b0 + 2 / b0 + 1) =
        y * (Real.logb 3 S0 / b0) + 2 * y / b0 + y := by ring
    rw [hexp]
    have h5 : Real.logb 3 S0 / b0 ≤ y * (Real.logb 3 S0 / b0) := by
      nlinarith only [hy1, h4]
    linarith only [hceil, h2, h5, hy1]
  -- linT bound
  exact ⟨hLarg, hLx, hL⟩

private theorem linear_tolerance_spacing_bound {A alpha d0 : ℝ} {j : ℕ}
    (hA : 1 ≤ A) (halpha : 0 < alpha)
      (hd0 : 0 < d0)
    (hgs : 128 * A ^ 2 * d0 ≤ 1)
    (hd01 : d0 ≤ 1)
    (hy1 : 1 ≤ (linY A d0 j))
    (hlamsq : Real.logb 3 (1 / linLam A d0 j ^ 2) = 2 * (linY A d0 j))
    (h2d0 : 2 * d0 ≤ 1)
    : ((1 : ℝ) ≤ d0 / (2 * linLam A d0 j ^ 2)) ∧
    (((linT alpha d0 (linLam A d0 j) : ℕ) : ℝ) ≤ (linY A d0 j) * (2 / alpha + 1)) := by
  classical
  have hlam := linLam_pos hA hd0 j
  have hlamd0 := linLam_le_floor hA hd0 hgs j
  set y : ℝ := linY A d0 j with hydef
  have hTarg : (1 : ℝ) ≤ d0 / (2 * linLam A d0 j ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    have ha : 2 * linLam A d0 j ^ 2 ≤ 2 * d0 * linLam A d0 j := by
      nlinarith only [hlamd0, hlam]
    have hb : 2 * d0 * linLam A d0 j ≤ 2 * d0 * d0 := by
      nlinarith only [hlamd0, hd0]
    have hc : 2 * d0 * d0 ≤ d0 := by nlinarith only [h2d0, hd0]
    linarith only [ha, hb, hc]
  have hT : ((linT alpha d0 (linLam A d0 j) : ℕ) : ℝ) ≤ y * (2 / alpha + 1) := by
    have hxpos : 0 ≤ Real.logb 3 (d0 / (2 * linLam A d0 j ^ 2)) / alpha := by
      have := Real.logb_nonneg (by norm_num : (1:ℝ) < 3) hTarg
      positivity
    have hceil : ((linT alpha d0 (linLam A d0 j) : ℕ) : ℝ) ≤
        Real.logb 3 (d0 / (2 * linLam A d0 j ^ 2)) / alpha + 1 := by
      rw [linT]
      exact (Nat.ceil_lt_add_one hxpos).le
    have h1 : Real.logb 3 (d0 / (2 * linLam A d0 j ^ 2)) ≤ 2 * y := by
      rw [Real.logb_div (by positivity) (by positivity)]
      have h2 : Real.logb 3 d0 ≤ 0 :=
        Real.logb_nonpos (by norm_num) hd0.le hd01
      have h3 : Real.logb 3 (linLam A d0 j ^ 2) = -(2 * y) := by
        have := hlamsq
        rw [one_div, Real.logb_inv] at this
        linarith only [this]
      have h4 : Real.logb 3 (linLam A d0 j ^ 2) ≤
          Real.logb 3 (2 * linLam A d0 j ^ 2) := by
        refine Real.logb_le_logb_of_le (by norm_num) (by positivity) ?_
        nlinarith only [sq_nonneg (linLam A d0 j), hlam]
      linarith only [h2, h3, h4]
    have h5 : Real.logb 3 (d0 / (2 * linLam A d0 j ^ 2)) / alpha ≤
        2 * y / alpha := div_le_div_of_nonneg_right h1 halpha.le
    have hexp : y * (2 / alpha + 1) = 2 * y / alpha + y := by ring
    rw [hexp]
    linarith only [hceil, h5, hy1]
  -- linII bound
  exact ⟨hTarg, hT⟩
/-- The per-round spacing is at most `Cs` times the level logarithm. -/
theorem linSpacing_le {A alpha b0 bA b2 d0 S0 : ℝ} {cA j : ℕ}
    (hA : 1 ≤ A) (halpha : 0 < alpha) (hb0 : 0 < b0) (hbA : 0 < bA)
    (hb2 : 0 < b2) (hS0 : 1 ≤ S0) (hd0 : 0 < d0)
    (hgs3 : (128 * A ^ 2) ^ 3 * d0 ≤ 1 / 3) :
    ((max (linL A b0 S0 (linLam A d0 j)) (linT alpha d0 (linLam A d0 j)) +
      linII A (linLam A d0 j) * (cA + 1) +
      linPad A bA b2 (linLam A d0 j) + 1 : ℕ) : ℝ) ≤
      linCs A alpha b0 bA b2 cA S0 * linY A d0 j := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA
  have hlam := linLam_pos hA hd0 j
  have hgs : 128 * A ^ 2 * d0 ≤ 1 := gs_of_gs3 hA hd0 hgs3
  have hlamd0 := linLam_le_floor hA hd0 hgs j
  have hd01 : d0 ≤ 1 := by nlinarith only [hgs, hA]
  set y : ℝ := linY A d0 j with hydef
  have hy1 : 1 ≤ y := by
    have hz := linZ_one_le hA hd0 hgs3 j
    have hzy := linY_ge_linZ (d0 := d0) hA j
    rw [hydef]
    linarith only [hz, hzy]
  have hycs : Real.logb 3 (1 / linLam A d0 j) = y := by rw [hydef, linY]
  have hylam : Real.logb 3 (linLam A d0 j) = -y := by
    rw [← hycs, one_div, Real.logb_inv]
    ring
  have hcstar : Real.logb 3 (1 / (128 * A ^ 2 * linLam A d0 j)) =
      y - Real.logb 3 (128 * A ^ 2) := by
    rw [one_div, mul_inv, Real.logb_mul (by positivity) (by positivity),
      Real.logb_inv, Real.logb_inv, hylam]
    ring
  have hlamsq : Real.logb 3 (1 / linLam A d0 j ^ 2) = 2 * y := by
    rw [one_div, Real.logb_inv, Real.logb_pow, hylam]
    push_cast
    ring
  have hrate : 0 < Real.logb 3 ((2 * A + 1) / (2 * A)) := by
    have h1 : (1 : ℝ) < (2 * A + 1) / (2 * A) := by
      rw [lt_div_iff₀ (by positivity)]
      linarith only []
    exact Real.logb_pos (by norm_num) h1
  -- linL bound
  have h2d0 : 2 * d0 ≤ 1 := by
    have h5 : (0 : ℝ) ≤ d0 * (128 * A ^ 2 - 2) :=
      mul_nonneg hd0.le (by nlinarith only [hA])
    nlinarith only [hgs, h5]
  obtain ⟨hLarg, hLx, hL⟩ :=
    linear_source_spacing_bound hA hb0 hS0 hd0
      hA0 hgs hd01 hy1 hlamsq
  obtain ⟨hTarg, hT⟩ :=
    linear_tolerance_spacing_bound hA halpha hd0 hgs
      hd01 hy1 hlamsq h2d0
  have hIarg : (1 : ℝ) ≤ 1 / (16 * A ^ 2 * linLam A d0 j) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [hlamd0, hgs, hlam, hA0]
  have hII : ((linII A (linLam A d0 j) * (cA + 1) : ℕ) : ℝ) ≤
      y * ((1 / Real.logb 3 ((2 * A + 1) / (2 * A)) + 1) * ((cA : ℝ) + 1)) := by
    have hxpos : 0 ≤ Real.logb 3 (1 / (16 * A ^ 2 * linLam A d0 j)) /
        Real.logb 3 ((2 * A + 1) / (2 * A)) := by
      have := Real.logb_nonneg (by norm_num : (1:ℝ) < 3) hIarg
      positivity
    have hceil : ((linII A (linLam A d0 j) : ℕ) : ℝ) ≤
        Real.logb 3 (1 / (16 * A ^ 2 * linLam A d0 j)) /
          Real.logb 3 ((2 * A + 1) / (2 * A)) + 1 := by
      rw [linII]
      exact (Nat.ceil_lt_add_one hxpos).le
    have h1 : Real.logb 3 (1 / (16 * A ^ 2 * linLam A d0 j)) ≤ y := by
      rw [one_div, Real.logb_inv]
      have h2 : Real.logb 3 (linLam A d0 j) ≤
          Real.logb 3 (16 * A ^ 2 * linLam A d0 j) := by
        refine Real.logb_le_logb_of_le (by norm_num) hlam ?_
        have h2b : (0 : ℝ) ≤ linLam A d0 j * (16 * A ^ 2 - 1) :=
          mul_nonneg hlam.le (by nlinarith only [hA])
        nlinarith only [h2b]
      have h3 : Real.logb 3 (linLam A d0 j) = -y := by
        have := hycs
        rw [one_div, Real.logb_inv] at this
        linarith only [this]
      linarith only [h2, h3]
    have h4 : Real.logb 3 (1 / (16 * A ^ 2 * linLam A d0 j)) /
        Real.logb 3 ((2 * A + 1) / (2 * A)) ≤
        y / Real.logb 3 ((2 * A + 1) / (2 * A)) :=
      div_le_div_of_nonneg_right h1 hrate.le
    have h5 : ((linII A (linLam A d0 j) : ℕ) : ℝ) ≤
        y / Real.logb 3 ((2 * A + 1) / (2 * A)) + y := by
      linarith only [hceil, h4, hy1]
    have hcast : ((linII A (linLam A d0 j) * (cA + 1) : ℕ) : ℝ) =
        ((linII A (linLam A d0 j) : ℕ) : ℝ) * ((cA : ℝ) + 1) := by
      push_cast
      ring
    rw [hcast]
    have h6 : (0 : ℝ) ≤ (cA : ℝ) + 1 := by positivity
    have hexp : y * ((1 / Real.logb 3 ((2 * A + 1) / (2 * A)) + 1) *
        ((cA : ℝ) + 1)) =
        (y / Real.logb 3 ((2 * A + 1) / (2 * A)) + y) * ((cA : ℝ) + 1) := by
      field_simp
    rw [hexp]
    exact mul_le_mul_of_nonneg_right h5 h6
  -- linPad bound
  have hPadArg : 0 ≤ 2 * Real.logb 3 (1 / (128 * A ^ 2 * linLam A d0 j)) := by
    have h1 : (1 : ℝ) ≤ 1 / (128 * A ^ 2 * linLam A d0 j) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith only [hlamd0, hgs, hlam, hA0]
    have := Real.logb_nonneg (by norm_num : (1:ℝ) < 3) h1
    linarith only [this]
  have hPadY : Real.logb 3 (1 / (128 * A ^ 2 * linLam A d0 j)) ≤ y := by
    rw [hcstar]
    have h1 : 0 ≤ Real.logb 3 (128 * A ^ 2) :=
      Real.logb_nonneg (by norm_num) (by nlinarith only [hA])
    linarith only [h1]
  have hPad : ((linPad A bA b2 (linLam A d0 j) : ℕ) : ℝ) ≤
      y * (2 / bA + 2 / b2 + 2) := by
    have hceilA : ((⌈2 * Real.logb 3 (1 / (128 * A ^ 2 * linLam A d0 j)) /
        bA⌉₊ : ℕ) : ℝ) ≤
        2 * Real.logb 3 (1 / (128 * A ^ 2 * linLam A d0 j)) / bA + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    have hceilB : ((⌈2 * Real.logb 3 (1 / (128 * A ^ 2 * linLam A d0 j)) /
        b2⌉₊ : ℕ) : ℝ) ≤
        2 * Real.logb 3 (1 / (128 * A ^ 2 * linLam A d0 j)) / b2 + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    have h1 : 2 * Real.logb 3 (1 / (128 * A ^ 2 * linLam A d0 j)) / bA ≤
        2 * y / bA := by
      refine div_le_div_of_nonneg_right ?_ hbA.le
      linarith only [hPadY]
    have h2 : 2 * Real.logb 3 (1 / (128 * A ^ 2 * linLam A d0 j)) / b2 ≤
        2 * y / b2 := by
      refine div_le_div_of_nonneg_right ?_ hb2.le
      linarith only [hPadY]
    have hcast : ((linPad A bA b2 (linLam A d0 j) : ℕ) : ℝ) =
        ((⌈2 * Real.logb 3 (1 / (128 * A ^ 2 * linLam A d0 j)) / bA⌉₊ :
          ℕ) : ℝ) +
        ((⌈2 * Real.logb 3 (1 / (128 * A ^ 2 * linLam A d0 j)) / b2⌉₊ :
          ℕ) : ℝ) := by
      rw [linPad]
      push_cast
      ring
    rw [hcast]
    have hexp : y * (2 / bA + 2 / b2 + 2) =
        2 * y / bA + 2 * y / b2 + 2 * y := by ring
    rw [hexp]
    linarith only [hceilA, hceilB, h1, h2, hy1]
  -- assembly
  have hmax : ((max (linL A b0 S0 (linLam A d0 j))
      (linT alpha d0 (linLam A d0 j)) : ℕ) : ℝ) ≤
      ((linL A b0 S0 (linLam A d0 j) : ℕ) : ℝ) +
        ((linT alpha d0 (linLam A d0 j) : ℕ) : ℝ) := by
    have h1 : max (linL A b0 S0 (linLam A d0 j))
        (linT alpha d0 (linLam A d0 j)) ≤
        linL A b0 S0 (linLam A d0 j) + linT alpha d0 (linLam A d0 j) := by
      omega
    exact_mod_cast h1
  have hone : (1 : ℝ) ≤ y * 1 := by linarith only [hy1]
  have hcast2 : ((max (linL A b0 S0 (linLam A d0 j))
      (linT alpha d0 (linLam A d0 j)) +
      linII A (linLam A d0 j) * (cA + 1) +
      linPad A bA b2 (linLam A d0 j) + 1 : ℕ) : ℝ) =
      ((max (linL A b0 S0 (linLam A d0 j))
        (linT alpha d0 (linLam A d0 j)) : ℕ) : ℝ) +
      ((linII A (linLam A d0 j) * (cA + 1) : ℕ) : ℝ) +
      ((linPad A bA b2 (linLam A d0 j) : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  rw [hcast2, linCs]
  have hfinal : y * (Real.logb 3 S0 / b0 + 2 / b0 + 1) +
      y * (2 / alpha + 1) +
      y * ((1 / Real.logb 3 ((2 * A + 1) / (2 * A)) + 1) * ((cA : ℝ) + 1)) +
      y * (2 / bA + 2 / b2 + 2) + y * 1 =
      ((Real.logb 3 S0 / b0 + 2 / b0 + 1) + (2 / alpha + 1) +
        (1 / Real.logb 3 ((2 * A + 1) / (2 * A)) + 1) * ((cA : ℝ) + 1) +
        (2 / bA + 2 / b2 + 2) + 1) * y := by ring
  linarith only [hmax, hL, hT, hII, hPad, hone, hfinal.le, hfinal.ge]

/-- The telescoping: the round starts stay within `2Cs` centered levels. -/
theorem linR_telescope {ns cA : ℕ} {A alpha b0 bA b2 S0 S1 S2 d0 : ℝ}
    (hA : 1 ≤ A) (halpha : 0 < alpha) (hb0 : 0 < b0) (hbA : 0 < bA)
    (hb2 : 0 < b2) (hS0 : 1 ≤ S0) (hd0 : 0 < d0)
    (hgs3 : (128 * A ^ 2) ^ 3 * d0 ≤ 1 / 3) :
    ∀ j, ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℕ) : ℝ) ≤
      ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ) +
        2 * linCs A alpha b0 bA b2 cA S0 * (linZ A d0 j - linZ A d0 0) := by
  have hCs1 := linCs_one_le (cA := cA) hA halpha hb0 hbA hb2 hS0
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      have hsp := linSpacing_le (cA := cA) (j := j) (bA := bA) (b2 := b2)
        hA halpha hb0 hbA hb2 hS0 hd0 hgs3
      have hy2z : linY A d0 j ≤ 2 * linZ A d0 j :=
        linY_le_two_linZ hA hd0 hgs3 j
      have hzsucc : linZ A d0 (j + 1) = 2 * linZ A d0 j :=
        linZ_succ hA hd0 j
      have hcastR : ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 (j + 1) :
          ℕ) : ℝ) =
          ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℕ) : ℝ) +
          ((max (linL A b0 S0 (linLam A d0 j))
            (linT alpha d0 (linLam A d0 j)) +
            linII A (linLam A d0 j) * (cA + 1) +
            linPad A bA b2 (linLam A d0 j) + 1 : ℕ) : ℝ) := by
        rw [linR_succ]
        push_cast
        ring
      have hCs0 : (0 : ℝ) ≤ linCs A alpha b0 bA b2 cA S0 := by
        linarith only [hCs1]
      have hchain : ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 (j + 1) :
          ℕ) : ℝ) ≤
          ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ) +
          2 * linCs A alpha b0 bA b2 cA S0 * (linZ A d0 j - linZ A d0 0) +
          linCs A alpha b0 bA b2 cA S0 * (2 * linZ A d0 j) := by
        rw [hcastR]
        have h1 : linCs A alpha b0 bA b2 cA S0 * linY A d0 j ≤
            linCs A alpha b0 bA b2 cA S0 * (2 * linZ A d0 j) :=
          mul_le_mul_of_nonneg_left hy2z hCs0
        linarith only [ih, hsp, h1]
      rw [hzsucc]
      linarith only [hchain]

/-- The round starts grow at least linearly. -/
theorem linR_lower {ns cA : ℕ} {A alpha b0 bA b2 S0 S1 S2 d0 : ℝ} :
    ∀ j, linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 + j ≤
      linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j := by
  intro j
  induction j with
  | zero => omega
  | succ j ihj =>
      rw [linR_succ]
      omega

/-- **The corrected-model descent in `hdecay` shape.**  Law-free rate
`linRate` (a function of `A, α, b₀, b_A, b₂, c_A, S₀` only), threshold
linear in `ns` plus the one-time absolute burn-ins. -/
theorem linear_descent_hdecay {A alpha d0 S0 S1 S2 b0 bA b2 : ℝ}
    {F : ℕ → ℝ} {src : ℕ → ℕ → ℝ} {ns cA : ℕ}
    (hA : 1 ≤ A) (halpha : 0 < alpha)
    (hcA : 24 * A ≤ (3 : ℝ) ^ (alpha * (cA : ℝ)))
    (hd0 : 0 < d0) (hgs3 : (128 * A ^ 2) ^ 3 * d0 ≤ 1 / 3)
    (hS0 : 1 ≤ S0) (hS1 : 1 ≤ S1) (hS2 : 1 ≤ S2)
    (hb0 : 0 < b0) (hbA : 0 < bA) (hb2 : 0 < b2)
    (hFnn : ∀ n, 0 ≤ F n)
    (hFmono : ∀ p q : ℕ, p ≤ q → F q ≤ F p)
    (hFd0 : ∀ n, F n ≤ d0)
    (hfam : ∀ n m : ℕ, ns ≤ m → m ≤ n →
      F n ≤ A * iterationDropSum ((3 : ℝ) ^ (-alpha)) F n +
        A * F m ^ 2 + src n m)
    (hsrc : ∀ n m : ℕ, ns ≤ m → m ≤ n →
      src n m ≤ S1 * (3 : ℝ) ^ (-(bA * (m : ℝ))) +
        S0 * (3 : ℝ) ^ (-(b0 * ((n - m : ℕ) : ℝ))) +
        S2 * (3 : ℝ) ^ (-(b2 * (n : ℝ)))) :
    0 < linRate A alpha b0 bA b2 cA S0 ∧
    linRate A alpha b0 bA b2 cA S0 ≤ 1 ∧
    ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ) ≤
      (ns : ℝ) + Real.logb 3 (S1 / (A * d0 ^ 2)) / bA +
        Real.logb 3 (S2 / (A * d0 ^ 2)) / b2 + 2 ∧
    ∀ n : ℕ, linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 ≤ n →
      F n ≤ ((3 : ℝ) ^ (-(linRate A alpha b0 bA b2 cA S0))) ^
        (n - linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0) := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA
  have hgs : 128 * A ^ 2 * d0 ≤ 1 := gs_of_gs3 hA hd0 hgs3
  have hd0small : 9 * A * d0 ≤ 1 := by
    have h1 : (0 : ℝ) ≤ A * d0 * (128 * A - 9) :=
      mul_nonneg (by positivity) (by nlinarith only [hA])
    nlinarith only [hgs, h1]
  have hCs1 := linCs_one_le (cA := cA) hA halpha hb0 hbA hb2 hS0
  have hCs0 : (0 : ℝ) < linCs A alpha b0 bA b2 cA S0 := by
    linarith only [hCs1]
  have hrate0 : 0 < linRate A alpha b0 bA b2 cA S0 := by
    rw [linRate]
    positivity
  have hrate1 : linRate A alpha b0 bA b2 cA S0 ≤ 1 := by
    rw [linRate]
    rw [div_le_one (by positivity)]
    linarith only [hCs1]
  have hAd0 : A * d0 ≤ 1 := by
    have h1 : (0 : ℝ) ≤ A * d0 * (128 * A - 1) :=
      mul_nonneg (by positivity) (by nlinarith only [hA])
    nlinarith only [hgs, h1]
  have hthresh : ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ) ≤
      (ns : ℝ) + Real.logb 3 (S1 / (A * d0 ^ 2)) / bA +
        Real.logb 3 (S2 / (A * d0 ^ 2)) / b2 + 2 := by
    have hd01 : d0 ≤ 1 := by nlinarith only [hAd0, hA, hd0]
    have hAd0sq : A * d0 ^ 2 ≤ 1 := by nlinarith only [hAd0, hd01, hd0]
    have hargA : (1 : ℝ) ≤ S1 / (A * d0 ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      linarith only [hAd0sq, hS1]
    have hargB : (1 : ℝ) ≤ S2 / (A * d0 ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      linarith only [hAd0sq, hS2]
    have hxA : 0 ≤ Real.logb 3 (S1 / (A * d0 ^ 2)) / bA := by
      have := Real.logb_nonneg (by norm_num : (1:ℝ) < 3) hargA
      positivity
    have hxB : 0 ≤ Real.logb 3 (S2 / (A * d0 ^ 2)) / b2 := by
      have := Real.logb_nonneg (by norm_num : (1:ℝ) < 3) hargB
      positivity
    rw [linR_zero]
    push_cast
    have h1 := (Nat.ceil_lt_add_one hxA).le
    have h2 := (Nat.ceil_lt_add_one hxB).le
    linarith only [h1, h2]
  refine ⟨hrate0, hrate1, hthresh, ?_⟩
  have hdesc := linear_ledger_descent (src := src) (ns := ns) (cA := cA)
    hA halpha hcA hd0 hgs hd0small hS0 hS1 hS2 hb0 hbA hb2
    hFnn hFmono hFd0 hfam hsrc
  intro n hn
  set P : ℕ → Prop := fun j =>
    linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j ≤ n with hPdef
  have hP0 : P 0 := hn
  set js : ℕ := Nat.findGreatest P n with hjsdef
  have hble : linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 js ≤ n := by
    have := Nat.findGreatest_spec (P := P) (Nat.zero_le n) hP0
    exact this
  have hnb : n < linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 (js + 1) := by
    by_contra hcon
    push Not at hcon
    have hjn : js + 1 ≤ n := by
      have h1 := linR_lower (ns := ns) (cA := cA) (A := A) (alpha := alpha)
        (b0 := b0) (bA := bA) (b2 := b2) (S0 := S0) (S1 := S1) (S2 := S2)
        (d0 := d0) (js + 1)
      omega
    exact Nat.findGreatest_is_greatest (P := P)
      (Nat.lt_succ_self js) hjn hcon
  have hFval : F n ≤ linLam A d0 js := hdesc js n hble
  have hy := linLam_eq_rpow hA hd0 js
  have hzy := linY_ge_linZ (d0 := d0) hA js
  have hz1 := linZ_one_le hA hd0 hgs3 js
  have hz0nn : 0 ≤ linZ A d0 0 := by
    have := linZ_one_le hA hd0 hgs3 0
    linarith only [this]
  have htel := linR_telescope (ns := ns) (cA := cA) (S1 := S1) (S2 := S2)
    hA halpha hb0 hbA hb2 hS0 hd0 hgs3 (js + 1)
  have hzsucc := linZ_succ (d0 := d0) hA hd0 js
  have hexpbound : linRate A alpha b0 bA b2 cA S0 *
      ((n - linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ) ≤
      linZ A d0 js := by
    have hcast : ((n - linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ) =
        (n : ℝ) - ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ) := by
      exact Nat.cast_sub hn
    have hnlt : (n : ℝ) ≤
        ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 (js + 1) : ℕ) : ℝ) := by
      exact_mod_cast hnb.le
    have hdiff : (n : ℝ) -
        ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ) ≤
        4 * linCs A alpha b0 bA b2 cA S0 * linZ A d0 js := by
      have h1 : (n : ℝ) -
          ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ) ≤
          2 * linCs A alpha b0 bA b2 cA S0 *
            (linZ A d0 (js + 1) - linZ A d0 0) := by
        linarith only [hnlt, htel]
      have h2 : 2 * linCs A alpha b0 bA b2 cA S0 *
          (linZ A d0 (js + 1) - linZ A d0 0) ≤
          2 * linCs A alpha b0 bA b2 cA S0 * linZ A d0 (js + 1) := by
        have h3 : (0 : ℝ) ≤ 2 * linCs A alpha b0 bA b2 cA S0 := by
          linarith only [hCs0]
        nlinarith only [h3, hz0nn]
      rw [hzsucc] at h1 h2
      linarith only [h1, h2]
    rw [hcast]
    have hrateval : linRate A alpha b0 bA b2 cA S0 =
        1 / (4 * linCs A alpha b0 bA b2 cA S0) := rfl
    rw [hrateval]
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    calc (n : ℝ) - ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ) ≤
        4 * linCs A alpha b0 bA b2 cA S0 * linZ A d0 js := hdiff
      _ = linZ A d0 js * (4 * linCs A alpha b0 bA b2 cA S0) := by ring
  have hpowcast : ((3 : ℝ) ^ (-(linRate A alpha b0 bA b2 cA S0))) ^
      (n - linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0) =
      (3 : ℝ) ^ (-(linRate A alpha b0 bA b2 cA S0 *
        ((n - linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ))) := by
    rw [← Real.rpow_natCast
      ((3 : ℝ) ^ (-(linRate A alpha b0 bA b2 cA S0)))
      (n - linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  calc F n ≤ linLam A d0 js := hFval
    _ = (3 : ℝ) ^ (-(linY A d0 js)) := hy
    _ ≤ (3 : ℝ) ^ (-(linZ A d0 js)) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        linarith only [hzy]
    _ ≤ (3 : ℝ) ^ (-(linRate A alpha b0 bA b2 cA S0 *
        ((n - linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ))) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        linarith only [hexpbound]
    _ = ((3 : ℝ) ^ (-(linRate A alpha b0 bA b2 cA S0))) ^
        (n - linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0) := hpowcast.symm

end

end HCPolySupport.HighContrast.Quenched
