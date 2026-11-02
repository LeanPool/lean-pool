/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Probability.GeometricSums

/-!
# KickArith

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Arithmetic for the Step-1 annular kick family

ABK26, §4.2, Step 1 of `l.minimal.scale.sep`.  Two of the manuscript's Step-1
moves are pure real arithmetic that the printed text performs silently, and both
are load-bearing for the amplitudes:

* **the geometric closures.**  The union-bound penalties of the lattice annulus
  are `(j−i+1)^{1/σ}`, i.e. `√(j−i+1)` on the `Γ₂` lane and `(j−i+1)²` on the
  `Γ_{1/2}` lane.  Summed against the §4.2 weight `3^{−½s(j−i)}` these give
  `s^{−3/2}` and `s^{−3}`.  The `√` closure is the sharp one — the crude `√(r+1)
  ≤ r+1` gives `s^{−2}` and does **not** reproduce the printed `s^{−5/2}` — and
  is the proved `Probability.tsum_threePow_neg_sqrt_le`; its `(r+1)²` companion
  is proved here, and `geomTailConst_le` converts both closure constants into
  explicit powers of `s`.

* **the absorptions.**  The `s`-powers picked up on the `Γ_{1/2}` lane must
  disappear into the exponential, because prints the amplitude `C
  exp(−C^{−1}c⋆³γ^{−1})` with **no** power of `s` in front.  The manuscript
  says only "for `C` chosen sufficiently large".  `inv_cube_mul_exp_le`
  performs the `s^{−3}` absorption on the window `s ≥ 8γ`, and
  `exp_neg_eighth_le_sqrt` performs the absorption the Step-1 collapse needs,
  namely that the fourth root of the exponentially small amplitude is below the
  `Γ₂` amplitude `C c⋆^{−1}s^{−5/2}√γ`.  Both consume the regime `γ ≤
  C^{−10}c⋆^{10}` through the single lemma `pow_le_expArg_mul`, which reads the
  regime as a *lower* bound on the exponent `C^{−1}c⋆³γ^{−1}`.  Without such a
  lower bound the absorbed prefactor would carry `c⋆^{−9}`, which is not a
  dimensional constant: this is exactly where the regime is used.

## The regime, honestly

The absorptions are proved from `γ ≤ C^{−10}c⋆^{10}`, which is **the enclosing
lemma's own printed hypothesis** and is also what the proved producer of the
per-cube two-term display carries.

## Why there is no `nlinarith`

Every statement here involves `Real.exp`, `Real.log`, `Real.sqrt` or `Real.rpow`.
All transcendental content is concentrated in `pow_mul_exp_neg_half_le`
(`xⁿe^{−x/2} ≤ (2n)ⁿ`, itself only `x ≤ eˣ` raised to the `n`-th power); after
that every step is polynomial and closed by `linarith only`, `field_simp` or
`ring`.  The collapse absorption squares both sides, which removes every root
before any arithmetic happens.

## References

* ABK26, `l.minimal.scale.sep`, (the lemma's own hypotheses), Step 1.
-/

namespace Algsuperdiff.Section4.Provider.MinimalScale

open Algsuperdiff.Probability

noncomputable section

/-! ## 1. Two numerical facts -/

theorem one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
  have h := Real.exp_one_lt_d9
  linarith only [h]

theorem sqrt_three_le_two : Real.sqrt 3 ≤ 2 := by
  have h := Real.sqrt_le_sqrt (show (3 : ℝ) ≤ 2 ^ 2 by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at h

/-! ## 2. The geometric closure constant is at most `2/α` -/

/-- `3^{−α} ≥ ½` for `α ≤ ½`: the elementary bound that turns the exact closure
constant `(1 − 3^{−α})⁻¹` into the explicit `2/α`. -/
theorem half_le_three_rpow_neg {alpha : ℝ} (halpha : alpha ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ (3 : ℝ) ^ (-alpha) := by
  have hmono : (3 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (3 : ℝ) ^ (-alpha) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [halpha])
  have heq : (3 : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt 3)⁻¹ := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
  have hs : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hhalf : (1 / 2 : ℝ) ≤ (Real.sqrt 3)⁻¹ := by
    rw [← one_div]
    exact one_div_le_one_div_of_le hs sqrt_three_le_two
  rw [heq] at hmono
  exact hhalf.trans hmono

/-- **`(1 − 3^{−α})⁻¹ ≤ 2/α` for `0 < α ≤ ½`.**  The conversion of the proved
closure constants into explicit powers of the window parameter: at `α = ½s` it
reads `geomTailConst (½s) ≤ 4/s`. -/
theorem geomTailConst_le {alpha : ℝ} (h0 : 0 < alpha) (h1 : alpha ≤ 1 / 2) :
    geomTailConst alpha ≤ 2 / alpha := by
  have hlog : alpha ≤ alpha * Real.log 3 := by
    have hstep : alpha * 1 ≤ alpha * Real.log 3 :=
      mul_le_mul_of_nonneg_left (le_of_lt one_lt_log_three) h0.le
    rwa [mul_one] at hstep
  have hexp : (3 : ℝ) ^ (-alpha) = Real.exp (-(alpha * Real.log 3)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hE : Real.exp (alpha * Real.log 3) * Real.exp (-(alpha * Real.log 3)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hone : alpha * Real.log 3 + 1 ≤ Real.exp (alpha * Real.log 3) :=
    Real.add_one_le_exp _
  have hprod : (alpha * Real.log 3 + 1) * Real.exp (-(alpha * Real.log 3))
      ≤ Real.exp (alpha * Real.log 3) * Real.exp (-(alpha * Real.log 3)) :=
    mul_le_mul_of_nonneg_right hone (Real.exp_pos _).le
  have hstep : alpha * Real.log 3 * Real.exp (-(alpha * Real.log 3))
      ≤ 1 - Real.exp (-(alpha * Real.log 3)) := by
    linarith only [hprod, hE]
  have hhalf : (1 / 2 : ℝ) ≤ Real.exp (-(alpha * Real.log 3)) := by
    rw [← hexp]
    exact half_le_three_rpow_neg h1
  have hlow : alpha / 2 ≤ alpha * Real.log 3 * Real.exp (-(alpha * Real.log 3)) := by
    have hmul : alpha * (1 / 2 : ℝ)
        ≤ alpha * Real.log 3 * Real.exp (-(alpha * Real.log 3)) :=
      mul_le_mul hlog hhalf (by norm_num) (by linarith only [hlog, h0])
    calc alpha / 2 = alpha * (1 / 2 : ℝ) := by ring
      _ ≤ _ := hmul
  have hkey : alpha / 2 ≤ 1 - (3 : ℝ) ^ (-alpha) := by
    rw [hexp]
    linarith only [hlow, hstep]
  have hpos : (0 : ℝ) < alpha / 2 := by linarith only [h0]
  rw [geomTailConst, show (2 : ℝ) / alpha = (alpha / 2)⁻¹ from (inv_div alpha 2).symm]
  exact inv_anti₀ hpos hkey

/-! ## 3. The `(r+1)²` geometric closure -/

/-- The termwise comparison `(r+1)² ≤ 2·binom(r+2,2)`, which turns the `(r+1)²`
weighted series into Mathlib's binomial geometric series. -/
private theorem threePow_sq_succ_le_choose {alpha : ℝ} (r : ℕ) :
    (3 : ℝ) ^ (-(alpha * (r : ℝ))) * ((r : ℝ) + 1) ^ 2
      ≤ 2 * ((((r + 2).choose 2 : ℕ) : ℝ) * ((3 : ℝ) ^ (-alpha)) ^ r) := by
  have hnat : (r + 2) * (r + 1) = (r + 2).choose 2 * 2 := by
    have h := Nat.add_one_mul_choose_eq (r + 1) 1
    rw [Nat.choose_one_right] at h
    exact h
  have hcast : 2 * ((((r + 2).choose 2 : ℕ) : ℝ)) = ((r : ℝ) + 2) * ((r : ℝ) + 1) := by
    have h : (((r + 2) * (r + 1) : ℕ) : ℝ) = ((((r + 2).choose 2 * 2 : ℕ)) : ℝ) := by
      rw [hnat]
    push_cast at h
    linarith only [h]
  have hrnn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hsq : ((r : ℝ) + 1) ^ 2 ≤ ((r : ℝ) + 2) * ((r : ℝ) + 1) := by
    have h1 : ((r : ℝ) + 1) * ((r : ℝ) + 1) ≤ ((r : ℝ) + 2) * ((r : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right (by linarith only [hrnn]) (by linarith only [hrnn])
    calc ((r : ℝ) + 1) ^ 2 = ((r : ℝ) + 1) * ((r : ℝ) + 1) := by ring
      _ ≤ ((r : ℝ) + 2) * ((r : ℝ) + 1) := h1
  rw [threePow_neg_natMul alpha r]
  calc ((3 : ℝ) ^ (-alpha)) ^ r * ((r : ℝ) + 1) ^ 2
      ≤ ((3 : ℝ) ^ (-alpha)) ^ r * (((r : ℝ) + 2) * ((r : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 2 * ((((r + 2).choose 2 : ℕ) : ℝ) * ((3 : ℝ) ^ (-alpha)) ^ r) := by
        rw [← hcast]; ring

private theorem hasSum_choose_two_geometric {alpha : ℝ} (halpha : 0 < alpha) :
    HasSum (fun r : ℕ => 2 * ((((r + 2).choose 2 : ℕ) : ℝ) * ((3 : ℝ) ^ (-alpha)) ^ r))
      (2 * (1 / (1 - (3 : ℝ) ^ (-alpha)) ^ (2 + 1))) := by
  have hr0 : (0 : ℝ) < (3 : ℝ) ^ (-alpha) := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : (3 : ℝ) ^ (-alpha) < 1 := three_rpow_neg_lt_one halpha
  have habs : ‖(3 : ℝ) ^ (-alpha)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr0]
    exact hr1
  exact (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 habs).mul_left 2

/-- The `(r+1)²`-weighted geometric series is summable. -/
theorem summable_threePow_neg_sq_succ {alpha : ℝ} (halpha : 0 < alpha) :
    Summable fun r : ℕ => (3 : ℝ) ^ (-(alpha * (r : ℝ))) * ((r : ℝ) + 1) ^ 2 :=
  Summable.of_nonneg_of_le (fun r => by positivity)
    (fun r => threePow_sq_succ_le_choose r) (hasSum_choose_two_geometric halpha).summable

/-- **`∑_r (r+1)² 3^{−αr} ≤ 2(1 − 3^{−α})^{−3}`.**  The `Γ_{1/2}` companion of the
proved sharp `√` closure: the union-bound penalty at `σ = ½` is the square
`(j−i+1)²`, whose weighted sum is a cubic closure. -/
theorem tsum_threePow_neg_sq_succ_le {alpha : ℝ} (halpha : 0 < alpha) :
    ∑' r : ℕ, (3 : ℝ) ^ (-(alpha * (r : ℝ))) * ((r : ℝ) + 1) ^ 2
      ≤ 2 * geomTailConst alpha ^ 3 := by
  have hS := hasSum_choose_two_geometric halpha
  have hbound := Summable.tsum_le_tsum (fun r => threePow_sq_succ_le_choose r)
    (summable_threePow_neg_sq_succ halpha) hS.summable
  rw [hS.tsum_eq] at hbound
  refine hbound.trans (le_of_eq ?_)
  rw [geomTailConst, one_div, ← inv_pow]

/-! ## 4. The one transcendental inequality -/

/-- **`xⁿ e^{−x/2} ≤ (2n)ⁿ`** for `x ≥ 0`.  The single transcendental estimate
behind both absorptions: `e^{x/(2n)} ≥ x/(2n)` raised to the `n`-th power.  No
numeric tactic ever sees `Real.exp`. -/
theorem pow_mul_exp_neg_half_le (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ n * Real.exp (-(x / 2)) ≤ (2 * (n : ℝ)) ^ n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [pow_zero, one_mul]
    exact Real.exp_le_one_iff.2 (by linarith only [hx])
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · rw [← hx0, zero_pow (by omega : n ≠ 0), zero_mul]
    positivity
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have ha0 : (0 : ℝ) < x / (2 * (n : ℝ)) := by positivity
  have hexp : (x / (2 * (n : ℝ))) ^ n ≤ Real.exp (x / 2) := by
    have h1 : x / (2 * (n : ℝ)) ≤ Real.exp (x / (2 * (n : ℝ))) := by
      have h := Real.add_one_le_exp (x / (2 * (n : ℝ)))
      linarith only [h]
    have h2 : (x / (2 * (n : ℝ))) ^ n ≤ Real.exp (x / (2 * (n : ℝ))) ^ n :=
      pow_le_pow_left₀ ha0.le h1 n
    have h3 : Real.exp (x / (2 * (n : ℝ))) ^ n = Real.exp (x / 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    rwa [h3] at h2
  have hd : x ^ n * Real.exp (-(x / 2)) = x ^ n / Real.exp (x / 2) := by
    rw [Real.exp_neg]
    ring
  rw [hd]
  have hden : (0 : ℝ) < (x / (2 * (n : ℝ))) ^ n := pow_pos ha0 n
  have hstep : x ^ n / Real.exp (x / 2) ≤ x ^ n / (x / (2 * (n : ℝ))) ^ n :=
    div_le_div_of_nonneg_left (by positivity) hden hexp
  refine hstep.trans (le_of_eq ?_)
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  rw [div_pow]
  field_simp

/-! ## 5. The regime, read as a lower bound on the exponent -/

/-- **The printed regime `γ ≤ C^{−10}c⋆^{10}`, in exponent form.**  It says exactly
that the exponent `b = C^{−1}c⋆³γ^{−1}` of the `Γ_{1/2}` amplitude obeys
`b·c⋆⁷ ≥ C⁹`.  Both absorptions consume the regime only through this. -/
theorem pow_le_expArg_mul {C cstar gam : ℝ} (hC : 0 < C) (hcs : 0 < cstar)
    (hgam : 0 < gam) (hreg : gam ≤ C⁻¹ ^ 10 * cstar ^ 10) :
    C ^ 9 ≤ C⁻¹ * cstar ^ 3 * gam⁻¹ * cstar ^ 7 := by
  have hCne : C ≠ 0 := ne_of_gt hC
  have hcsne : cstar ≠ 0 := ne_of_gt hcs
  have hginv : (C⁻¹ ^ 10 * cstar ^ 10)⁻¹ ≤ gam⁻¹ := inv_anti₀ hgam hreg
  have hmul : (0 : ℝ) < C⁻¹ * cstar ^ 3 * cstar ^ 7 := by positivity
  have hstep : C⁻¹ * cstar ^ 3 * cstar ^ 7 * (C⁻¹ ^ 10 * cstar ^ 10)⁻¹
      ≤ C⁻¹ * cstar ^ 3 * cstar ^ 7 * gam⁻¹ :=
    mul_le_mul_of_nonneg_left hginv hmul.le
  have heq : C⁻¹ * cstar ^ 3 * cstar ^ 7 * (C⁻¹ ^ 10 * cstar ^ 10)⁻¹ = C ^ 9 := by
    field_simp
  have hfin : C⁻¹ * cstar ^ 3 * cstar ^ 7 * gam⁻¹
      = C⁻¹ * cstar ^ 3 * gam⁻¹ * cstar ^ 7 := by ring
  rw [heq, hfin] at hstep
  exact hstep

/-! ## 6. The two absorption cores, over abstract reals -/

/-- The `s^{−3}` absorption, at the exponent `b` alone: `b³C³c⋆^{−9}e^{−b/2}` is a
dimensional constant once `b c⋆⁷ ≥ C⁹`.  Split by `c⋆ ≥ 1` (where `c⋆^{−9} ≤ 1`)
and `c⋆ ≤ 1` (where `c⋆^{−9} ≤ c⋆^{−14} ≤ b²C^{−18}`). -/
private theorem cube_exp_core {C cstar b : ℝ} (hC : 0 < C) (hcs : 0 < cstar)
    (hb : 0 < b) (hreg : C ^ 9 ≤ b * cstar ^ 7) :
    b ^ 3 * C ^ 3 * (cstar ^ 9)⁻¹ * Real.exp (-(b / 2))
      ≤ 216 * C ^ 3 + 100000 * C⁻¹ ^ 15 := by
  have hCne : C ≠ 0 := ne_of_gt hC
  have hcsne : cstar ≠ 0 := ne_of_gt hcs
  have hE0 : (0 : ℝ) < Real.exp (-(b / 2)) := Real.exp_pos _
  rcases le_total 1 cstar with hcs1 | hcs1
  · have hinv9 : (cstar ^ 9)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hcs1)
    have hb3 : b ^ 3 * Real.exp (-(b / 2)) ≤ 216 := by
      refine (pow_mul_exp_neg_half_le 3 hb.le).trans (le_of_eq ?_)
      push_cast
      norm_num
    have hchain : b ^ 3 * C ^ 3 * (cstar ^ 9)⁻¹ * Real.exp (-(b / 2))
        ≤ b ^ 3 * C ^ 3 * 1 * Real.exp (-(b / 2)) := by
      refine mul_le_mul_of_nonneg_right ?_ hE0.le
      exact mul_le_mul_of_nonneg_left hinv9 (by positivity)
    have hfin : b ^ 3 * C ^ 3 * 1 * Real.exp (-(b / 2)) ≤ 216 * C ^ 3 := by
      have h := mul_le_mul_of_nonneg_right hb3 (le_of_lt (pow_pos hC 3))
      calc b ^ 3 * C ^ 3 * 1 * Real.exp (-(b / 2))
          = b ^ 3 * Real.exp (-(b / 2)) * C ^ 3 := by ring
        _ ≤ 216 * C ^ 3 := h
    have hpos : (0 : ℝ) ≤ 100000 * C⁻¹ ^ 15 := by positivity
    linarith only [hchain, hfin, hpos]
  · have h7pos : (0 : ℝ) < cstar ^ 7 := by positivity
    have hcs7 : (cstar ^ 7)⁻¹ ≤ b * C⁻¹ ^ 9 := by
      rw [← one_div, div_le_iff₀ h7pos]
      have hC9 : (0 : ℝ) < C ^ 9 := pow_pos hC 9
      have hmul := mul_le_mul_of_nonneg_right hreg (le_of_lt (inv_pos.2 hC9))
      rw [mul_inv_cancel₀ (ne_of_gt hC9)] at hmul
      refine hmul.trans (le_of_eq ?_)
      field_simp
    have hcs9 : (cstar ^ 9)⁻¹ ≤ (b * C⁻¹ ^ 9) ^ 2 := by
      have h14 : (0 : ℝ) < cstar ^ 14 := by positivity
      have hkey : cstar ^ 14 ≤ cstar ^ 9 := by
        have h5 : cstar ^ 5 ≤ 1 := pow_le_one₀ hcs.le hcs1
        have h9 : (0 : ℝ) < cstar ^ 9 := by positivity
        have h := mul_le_mul_of_nonneg_left h5 h9.le
        calc cstar ^ 14 = cstar ^ 9 * cstar ^ 5 := by ring
          _ ≤ cstar ^ 9 * 1 := h
          _ = cstar ^ 9 := by ring
      have hres : (cstar ^ 9)⁻¹ ≤ (cstar ^ 14)⁻¹ := inv_anti₀ h14 hkey
      refine hres.trans ?_
      have heq : ((cstar ^ 7)⁻¹) ^ 2 = (cstar ^ 14)⁻¹ := by
        rw [inv_pow]
        congr 1
        ring
      rw [← heq]
      exact pow_le_pow_left₀ (by positivity) hcs7 2
    have hb5 : b ^ 5 * Real.exp (-(b / 2)) ≤ 100000 := by
      refine (pow_mul_exp_neg_half_le 5 hb.le).trans (le_of_eq ?_)
      push_cast
      norm_num
    have hchain : b ^ 3 * C ^ 3 * (cstar ^ 9)⁻¹ ≤ b ^ 5 * C⁻¹ ^ 15 := by
      have hpos : (0 : ℝ) ≤ b ^ 3 * C ^ 3 := by positivity
      calc b ^ 3 * C ^ 3 * (cstar ^ 9)⁻¹
          ≤ b ^ 3 * C ^ 3 * (b * C⁻¹ ^ 9) ^ 2 := mul_le_mul_of_nonneg_left hcs9 hpos
        _ = b ^ 5 * C⁻¹ ^ 15 := by field_simp
    have hstep : b ^ 3 * C ^ 3 * (cstar ^ 9)⁻¹ * Real.exp (-(b / 2))
        ≤ b ^ 5 * C⁻¹ ^ 15 * Real.exp (-(b / 2)) :=
      mul_le_mul_of_nonneg_right hchain hE0.le
    have hfin : b ^ 5 * C⁻¹ ^ 15 * Real.exp (-(b / 2)) ≤ 100000 * C⁻¹ ^ 15 := by
      have h := mul_le_mul_of_nonneg_right hb5 (le_of_lt (pow_pos (inv_pos.2 hC) 15))
      calc b ^ 5 * C⁻¹ ^ 15 * Real.exp (-(b / 2))
          = b ^ 5 * Real.exp (-(b / 2)) * C⁻¹ ^ 15 := by ring
        _ ≤ 100000 * C⁻¹ ^ 15 := h
    have hpos : (0 : ℝ) ≤ 216 * C ^ 3 := by positivity
    linarith only [hstep, hfin, hpos]

/-- The collapse absorption, at the exponent `b` alone: `C b e^{−b/4} ≤ K²c⋆`
with `K² = 4C + 64C^{−8}`, given `b c⋆⁷ ≥ C⁹`. -/
private theorem exp_quarter_core {C cstar b : ℝ} (hC : 0 < C) (hcs : 0 < cstar)
    (hb : 0 < b) (hreg : C ^ 9 ≤ b * cstar ^ 7) :
    C * b * Real.exp (-(b / 4)) ≤ (4 * C + 64 * C⁻¹ ^ 8) * cstar := by
  have hCne : C ≠ 0 := ne_of_gt hC
  have hcsne : cstar ≠ 0 := ne_of_gt hcs
  have hbne : b ≠ 0 := ne_of_gt hb
  have hE : Real.exp (-(b / 2 / 2)) = Real.exp (-(b / 4)) := by
    congr 1
    ring
  have hb1 : b * Real.exp (-(b / 4)) ≤ 4 := by
    have h := pow_mul_exp_neg_half_le 1 (le_of_lt (half_pos hb))
    rw [hE] at h
    have h2 := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
    calc b * Real.exp (-(b / 4)) = 2 * ((b / 2) ^ 1 * Real.exp (-(b / 4))) := by ring
      _ ≤ 2 * (2 * ((1 : ℕ) : ℝ)) ^ 1 := h2
      _ = 4 := by push_cast; norm_num
  have hb2 : b ^ 2 * Real.exp (-(b / 4)) ≤ 64 := by
    have h := pow_mul_exp_neg_half_le 2 (le_of_lt (half_pos hb))
    rw [hE] at h
    have h2 := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 4)
    calc b ^ 2 * Real.exp (-(b / 4)) = 4 * ((b / 2) ^ 2 * Real.exp (-(b / 4))) := by ring
      _ ≤ 4 * (2 * ((2 : ℕ) : ℝ)) ^ 2 := h2
      _ = 64 := by push_cast; norm_num
  have hK0 : (0 : ℝ) < 4 * C + 64 * C⁻¹ ^ 8 := by positivity
  rcases le_total 1 cstar with hcs1 | hcs1
  · have hleft : C * b * Real.exp (-(b / 4)) ≤ 4 * C := by
      have h := mul_le_mul_of_nonneg_left hb1 hC.le
      calc C * b * Real.exp (-(b / 4)) = C * (b * Real.exp (-(b / 4))) := by ring
        _ ≤ C * 4 := h
        _ = 4 * C := by ring
    have hright : 4 * C ≤ (4 * C + 64 * C⁻¹ ^ 8) * cstar := by
      have h1 : (4 * C + 64 * C⁻¹ ^ 8) * 1 ≤ (4 * C + 64 * C⁻¹ ^ 8) * cstar :=
        mul_le_mul_of_nonneg_left hcs1 hK0.le
      have h2 : (0 : ℝ) ≤ 64 * C⁻¹ ^ 8 := by positivity
      calc 4 * C ≤ 4 * C + 64 * C⁻¹ ^ 8 := by linarith only [h2]
        _ = (4 * C + 64 * C⁻¹ ^ 8) * 1 := by ring
        _ ≤ (4 * C + 64 * C⁻¹ ^ 8) * cstar := h1
    exact hleft.trans hright
  · have h7 : cstar ^ 7 ≤ cstar := by
      have h6 : cstar ^ 6 ≤ 1 := pow_le_one₀ hcs.le hcs1
      have h := mul_le_mul_of_nonneg_left h6 hcs.le
      calc cstar ^ 7 = cstar * cstar ^ 6 := by ring
        _ ≤ cstar * 1 := h
        _ = cstar := by ring
    have hcslow : C ^ 9 ≤ b * cstar :=
      hreg.trans (mul_le_mul_of_nonneg_left h7 hb.le)
    have hstep : C * b * Real.exp (-(b / 4)) * b ≤ 64 * C := by
      have h := mul_le_mul_of_nonneg_left hb2 hC.le
      calc C * b * Real.exp (-(b / 4)) * b = C * (b ^ 2 * Real.exp (-(b / 4))) := by ring
        _ ≤ C * 64 := h
        _ = 64 * C := by ring
    have hdiv : C * b * Real.exp (-(b / 4)) ≤ 64 * C / b := by
      rw [le_div_iff₀ hb]
      exact hstep
    have hcmp : 64 * C / b ≤ (4 * C + 64 * C⁻¹ ^ 8) * cstar := by
      have hlow : C ^ 9 / b ≤ cstar := by
        rw [div_le_iff₀ hb]
        calc C ^ 9 ≤ b * cstar := hcslow
          _ = cstar * b := by ring
      have hmul : 64 * C⁻¹ ^ 8 * (C ^ 9 / b) ≤ 64 * C⁻¹ ^ 8 * cstar :=
        mul_le_mul_of_nonneg_left hlow (by positivity)
      have heq : 64 * C⁻¹ ^ 8 * (C ^ 9 / b) = 64 * C / b := by
        field_simp
      rw [heq] at hmul
      have hpos : (0 : ℝ) ≤ 4 * C * cstar := by positivity
      have hexp2 : 64 * C⁻¹ ^ 8 * cstar + 4 * C * cstar
          = (4 * C + 64 * C⁻¹ ^ 8) * cstar := by ring
      linarith only [hmul, hpos, hexp2]
    exact hdiv.trans hcmp

/-! ## 7. The two absorptions, at the printed exponent -/

/-- **The `s^{−3}` absorption.**  On the window `s ≥ 8γ` and in the regime `γ ≤
C^{−10}c⋆^{10}`,

`s^{−3} exp(−C^{−1}c⋆³γ^{−1}) ≤ (216C³ + 10⁵C^{−15}) exp(−½C^{−1}c⋆³γ^{−1})`,

so the `s^{−3}` of the `(j−i+1)²` union-bound penalty leaves no trace in the
printed `Γ_{1/2}` amplitude, at the cost of halving the exponent (equivalently, of
doubling the dimensional constant). -/
theorem inv_cube_mul_exp_le {C cstar gam s : ℝ} (hC : 0 < C) (hcs : 0 < cstar)
    (hgam : 0 < gam) (hreg : gam ≤ C⁻¹ ^ 10 * cstar ^ 10) (hs : 8 * gam ≤ s) :
    s⁻¹ ^ 3 * Real.exp (-(C⁻¹ * cstar ^ 3 * gam⁻¹))
      ≤ (216 * C ^ 3 + 100000 * C⁻¹ ^ 15) *
        Real.exp (-(C⁻¹ * cstar ^ 3 * gam⁻¹ / 2)) := by
  have hCne : C ≠ 0 := ne_of_gt hC
  have hcsne : cstar ≠ 0 := ne_of_gt hcs
  have hgne : gam ≠ 0 := ne_of_gt hgam
  have hb0 : (0 : ℝ) < C⁻¹ * cstar ^ 3 * gam⁻¹ := by positivity
  have hcore := cube_exp_core hC hcs hb0 (pow_le_expArg_mul hC hcs hgam hreg)
  have hgeq : gam⁻¹ ^ 3 = (C⁻¹ * cstar ^ 3 * gam⁻¹) ^ 3 * C ^ 3 * (cstar ^ 9)⁻¹ := by
    field_simp
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le (by linarith only [hgam]) hs
  have hsg : s⁻¹ ≤ gam⁻¹ := inv_anti₀ hgam (by linarith only [hs, hgam])
  have hcube : s⁻¹ ^ 3 ≤ gam⁻¹ ^ 3 :=
    pow_le_pow_left₀ (le_of_lt (inv_pos.2 hs0)) hsg 3
  have hE0 : (0 : ℝ) < Real.exp (-(C⁻¹ * cstar ^ 3 * gam⁻¹ / 2)) := Real.exp_pos _
  have hsplit : Real.exp (-(C⁻¹ * cstar ^ 3 * gam⁻¹))
      = Real.exp (-(C⁻¹ * cstar ^ 3 * gam⁻¹ / 2)) *
        Real.exp (-(C⁻¹ * cstar ^ 3 * gam⁻¹ / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hkey : gam⁻¹ ^ 3 * Real.exp (-(C⁻¹ * cstar ^ 3 * gam⁻¹ / 2))
      ≤ 216 * C ^ 3 + 100000 * C⁻¹ ^ 15 := by
    rw [hgeq]
    exact hcore
  calc s⁻¹ ^ 3 * Real.exp (-(C⁻¹ * cstar ^ 3 * gam⁻¹))
      = s⁻¹ ^ 3 * Real.exp (-(C⁻¹ * cstar ^ 3 * gam⁻¹ / 2)) *
          Real.exp (-(C⁻¹ * cstar ^ 3 * gam⁻¹ / 2)) := by rw [hsplit]; ring
    _ ≤ gam⁻¹ ^ 3 * Real.exp (-(C⁻¹ * cstar ^ 3 * gam⁻¹ / 2)) *
          Real.exp (-(C⁻¹ * cstar ^ 3 * gam⁻¹ / 2)) := by
        refine mul_le_mul_of_nonneg_right ?_ hE0.le
        exact mul_le_mul_of_nonneg_right hcube hE0.le
    _ ≤ (216 * C ^ 3 + 100000 * C⁻¹ ^ 15) *
          Real.exp (-(C⁻¹ * cstar ^ 3 * gam⁻¹ / 2)) :=
        mul_le_mul_of_nonneg_right hkey hE0.le

/-- **The collapse absorption.**  In the regime `γ ≤ C^{−10}c⋆^{10}`,

`exp(−⅛C^{−1}c⋆³γ^{−1}) ≤ √(4C + 64C^{−8}) · c⋆^{−1}√γ`,

i.e. the fourth root of the exponentially small `Γ_{1/2}` amplitude is below
the printed `Γ₂` amplitude `C c⋆^{−1}s^{−5/2}√γ`.  This is the numerical
content's "by `e.powerofGammasigma`, `s ≥ 8γ` and `γ ≤ C^{−1}c⋆⁵`".  Squaring
both sides removes every root, after which `exp_quarter_core` closes it. -/
theorem exp_neg_eighth_le_sqrt {C cstar gam : ℝ} (hC : 0 < C) (hcs : 0 < cstar)
    (hgam : 0 < gam) (hreg : gam ≤ C⁻¹ ^ 10 * cstar ^ 10) :
    Real.exp (-(C⁻¹ * cstar ^ 3 * gam⁻¹ / 8))
      ≤ Real.sqrt (4 * C + 64 * C⁻¹ ^ 8) * (cstar⁻¹ * Real.sqrt gam) := by
  have hCne : C ≠ 0 := ne_of_gt hC
  have hcsne : cstar ≠ 0 := ne_of_gt hcs
  have hgne : gam ≠ 0 := ne_of_gt hgam
  have hb0 : (0 : ℝ) < C⁻¹ * cstar ^ 3 * gam⁻¹ := by positivity
  have hK0 : (0 : ℝ) < 4 * C + 64 * C⁻¹ ^ 8 := by positivity
  have hcore := exp_quarter_core hC hcs hb0 (pow_le_expArg_mul hC hcs hgam hreg)
  have hL0 : (0 : ℝ) ≤ Real.exp (-(C⁻¹ * cstar ^ 3 * gam⁻¹ / 8)) := (Real.exp_pos _).le
  have hR0 : (0 : ℝ) ≤ Real.sqrt (4 * C + 64 * C⁻¹ ^ 8) * (cstar⁻¹ * Real.sqrt gam) := by
    refine mul_nonneg (Real.sqrt_nonneg _) ?_
    exact mul_nonneg (le_of_lt (inv_pos.2 hcs)) (Real.sqrt_nonneg _)
  have hLexp : Real.exp (-(C⁻¹ * cstar ^ 3 * gam⁻¹ / 8)) ^ 2
      = Real.exp (-(C⁻¹ * cstar ^ 3 * gam⁻¹ / 4)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hRexp : (Real.sqrt (4 * C + 64 * C⁻¹ ^ 8) * (cstar⁻¹ * Real.sqrt gam)) ^ 2
      = (4 * C + 64 * C⁻¹ ^ 8) * cstar / (C * (C⁻¹ * cstar ^ 3 * gam⁻¹)) := by
    have hKsq : Real.sqrt (4 * C + 64 * C⁻¹ ^ 8) ^ 2 = 4 * C + 64 * C⁻¹ ^ 8 :=
      Real.sq_sqrt hK0.le
    have hgsq : Real.sqrt gam ^ 2 = gam := Real.sq_sqrt hgam.le
    calc (Real.sqrt (4 * C + 64 * C⁻¹ ^ 8) * (cstar⁻¹ * Real.sqrt gam)) ^ 2
        = Real.sqrt (4 * C + 64 * C⁻¹ ^ 8) ^ 2 * (cstar⁻¹ ^ 2 * Real.sqrt gam ^ 2) := by
          ring
      _ = (4 * C + 64 * C⁻¹ ^ 8) * (cstar⁻¹ ^ 2 * gam) := by rw [hKsq, hgsq]
      _ = (4 * C + 64 * C⁻¹ ^ 8) * cstar / (C * (C⁻¹ * cstar ^ 3 * gam⁻¹)) := by
          field_simp
  have hsq : Real.exp (-(C⁻¹ * cstar ^ 3 * gam⁻¹ / 8)) ^ 2
      ≤ (Real.sqrt (4 * C + 64 * C⁻¹ ^ 8) * (cstar⁻¹ * Real.sqrt gam)) ^ 2 := by
    rw [hLexp, hRexp]
    have hCb0 : (0 : ℝ) < C * (C⁻¹ * cstar ^ 3 * gam⁻¹) := by positivity
    rw [le_div_iff₀ hCb0]
    calc Real.exp (-(C⁻¹ * cstar ^ 3 * gam⁻¹ / 4)) * (C * (C⁻¹ * cstar ^ 3 * gam⁻¹))
        = C * (C⁻¹ * cstar ^ 3 * gam⁻¹) *
            Real.exp (-(C⁻¹ * cstar ^ 3 * gam⁻¹ / 4)) := by ring
      _ ≤ (4 * C + 64 * C⁻¹ ^ 8) * cstar := hcore
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hL0, Real.sqrt_sq hR0] at h

/-! ## 8. Small utilities used by the tail split and the closed forms -/

/-- Comparison of nonnegative reals through their squares.  Used wherever a
`Real.sqrt` has to be removed before any arithmetic happens. -/
theorem le_of_sq_le_sq' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) :
    a ≤ b := by
  have hs := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq ha, Real.sqrt_sq hb] at hs

theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have h : Real.log 2 < 1 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)]
    have := Real.exp_one_gt_d9
    linarith only [this]
  linarith only [h]

/-- **The halving step of every union bound below**: an exponential whose argument
is `log 2` further out is at most half of the target exponential. -/
theorem exp_neg_le_half_exp_neg {a c : ℝ} (h : c + Real.log 2 ≤ a) :
    Real.exp (-a) ≤ Real.exp (-c) / 2 := by
  have h2 : Real.exp (-c) / 2 = Real.exp (-c - Real.log 2) := by
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [h2]
  exact Real.exp_le_exp.2 (by linarith only [h])

/-! ## 9. The two closure constants at the §4.2 rate `½s` -/

/-- **`geomTailConst (½s)³ ≤ 64 s^{−3}`**, the `Γ_{1/2}` closed form. -/
theorem geomTailConst_cube_le {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    geomTailConst (s / 2) ^ 3 ≤ 64 * s⁻¹ ^ 3 := by
  have halpha0 : (0 : ℝ) < s / 2 := by linarith only [hs0]
  have halpha1 : s / 2 ≤ 1 / 2 := by linarith only [hs1]
  have hgpos : 0 < geomTailConst (s / 2) := geomTailConst_pos halpha0
  have hg4 : geomTailConst (s / 2) ≤ 4 * s⁻¹ := by
    refine (geomTailConst_le halpha0 halpha1).trans (le_of_eq ?_)
    field_simp
    norm_num
  refine (pow_le_pow_left₀ hgpos.le hg4 3).trans (le_of_eq ?_)
  rw [mul_pow]
  norm_num

/-- **`geomSqrtConst (½s) ≤ 8 s^{−3/2}`**, the sharp `Γ₂` closed form, written with
`(√s)³` so that no `rpow` enters. -/
theorem geomSqrtConst_le {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    geomSqrtConst (s / 2) ≤ 8 * ((Real.sqrt s) ^ 3)⁻¹ := by
  have halpha0 : (0 : ℝ) < s / 2 := by linarith only [hs0]
  have hgpos : 0 < geomTailConst (s / 2) := geomTailConst_pos halpha0
  have hsq0 : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hL0 : (0 : ℝ) ≤ geomSqrtConst (s / 2) := (geomSqrtConst_pos halpha0).le
  have hR0 : (0 : ℝ) ≤ 8 * ((Real.sqrt s) ^ 3)⁻¹ := by
    have h1 : (0 : ℝ) < ((Real.sqrt s) ^ 3)⁻¹ := inv_pos.2 (pow_pos hsq0 3)
    linarith only [h1]
  refine le_of_sq_le_sq' hL0 hR0 ?_
  have hLsq : geomSqrtConst (s / 2) ^ 2 = geomTailConst (s / 2) ^ 3 := by
    rw [geomSqrtConst]
    exact Real.sq_sqrt (pow_nonneg hgpos.le 3)
  have hx : ((Real.sqrt s) ^ 3) ^ 2 = s ^ 3 := by
    rw [← pow_mul, show (3 : ℕ) * 2 = 2 * 3 from by norm_num, pow_mul,
      Real.sq_sqrt hs0.le]
  have hRsq : (8 * ((Real.sqrt s) ^ 3)⁻¹) ^ 2 = 64 * s⁻¹ ^ 3 := by
    rw [mul_pow, inv_pow, hx, ← inv_pow]
    norm_num
  rw [hLsq, hRsq]
  exact geomTailConst_cube_le hs0 hs1

end

end Algsuperdiff.Section4.Provider.MinimalScale
