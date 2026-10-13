/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# SmallGammaRpow

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Smallness of the amplitude `γ^{1/2}|log γ|^q`

The accuracy windows of the percolation estimates have a lower endpoint of the form

```text
  C γ^{1/2} |log γ|^q
```

with a real exponent `q`, and are useful only when that endpoint lies below the fixed
upper endpoints the estimates impose.  This file supplies the elementary fact that makes
those windows nonempty: for a fixed multiplier and a fixed exponent the amplitude falls
below any prescribed positive bound once the disorder parameter is small enough.

The proof is quantitative.  For `0 < r` and `0 < γ ≤ 1` the logarithm obeys

```text
  |log γ| ≤ r⁻¹ γ^{-r} ,
```

which is `log x ≤ x - 1` read at `x = γ^{-r}`.  Taking the `q`-th power with
`r = (4(q+1))⁻¹` and multiplying by `γ^{1/2}` gives

```text
  γ^{1/2} |log γ|^q ≤ (4(q+1))^q γ^{1/4} ,
```

so the threshold can be taken to be a fourth power.

## Main results

* `abs_log_le_inv_mul_rpow_neg` — the logarithm against a small negative power.
* `sqrt_mul_abs_log_rpow_le_rpow_quarter` — the amplitude against `γ^{1/4}`.
* `exists_sqrt_mul_abs_log_rpow_le` — any multiple of the amplitude is below any
  prescribed positive bound once `γ` is below an explicit threshold.
-/

namespace Algsuperdiff.Section5.Support

noncomputable section

/-- **The logarithm is dominated by any small negative power.**  For `0 < γ ≤ 1` and
`0 < r`,

```text
  |log γ| ≤ r⁻¹ γ^{-r} .
```

This is the inequality `log x ≤ x - 1` read at `x = γ^{-r}`. -/
theorem abs_log_le_inv_mul_rpow_neg {gamma r : ℝ} (hgamma : 0 < gamma)
    (hgamma1 : gamma ≤ 1) (hr : 0 < r) :
    |Real.log gamma| ≤ r⁻¹ * Real.rpow gamma (-r) := by
  show |Real.log gamma| ≤ r⁻¹ * gamma ^ (-r)
  have hlog : Real.log gamma ≤ 0 := Real.log_nonpos hgamma.le hgamma1
  have hu : (0 : ℝ) < gamma ^ r := Real.rpow_pos_of_pos hgamma r
  have hkey : Real.log ((gamma ^ r)⁻¹) ≤ (gamma ^ r)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (inv_pos.2 hu)
  rw [Real.log_inv, Real.log_rpow hgamma, ← Real.rpow_neg hgamma.le] at hkey
  rw [abs_of_nonpos hlog]
  have hrinv : (0 : ℝ) < r⁻¹ := inv_pos.2 hr
  have hmul := mul_le_mul_of_nonneg_left hkey hrinv.le
  have hsimp : r⁻¹ * -(r * Real.log gamma) = -Real.log gamma := by field_simp
  rw [hsimp] at hmul
  have hpos : (0 : ℝ) < gamma ^ (-r) := Real.rpow_pos_of_pos hgamma _
  nlinarith only [hmul, hrinv]

/-- **The amplitude `γ^{1/2}|log γ|^q` is a bounded multiple of `γ^{1/4}`.**  For every
real exponent `q ≥ 0` and every `0 < γ ≤ 1`,

```text
  γ^{1/2} |log γ|^q ≤ (4(q+1))^q γ^{1/4} .
```
-/
theorem sqrt_mul_abs_log_rpow_le_rpow_quarter {q : ℝ} (hq : 0 ≤ q) {gamma : ℝ}
    (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1) :
    Real.sqrt gamma * Real.rpow |Real.log gamma| q ≤
      Real.rpow (4 * (q + 1)) q * Real.rpow gamma (1 / 4) := by
  show Real.sqrt gamma * |Real.log gamma| ^ q ≤ (4 * (q + 1)) ^ q * gamma ^ (1 / 4 : ℝ)
  set r : ℝ := (4 * (q + 1))⁻¹ with hrdef
  have hq1 : (0 : ℝ) < 4 * (q + 1) := by linarith
  have hr : 0 < r := by rw [hrdef]; positivity
  have hrinv : r⁻¹ = 4 * (q + 1) := by rw [hrdef, inv_inv]
  have hlogbd : |Real.log gamma| ≤ r⁻¹ * gamma ^ (-r) :=
    abs_log_le_inv_mul_rpow_neg hgamma hgamma1 hr
  have hstep1 : |Real.log gamma| ^ q ≤ (r⁻¹ * gamma ^ (-r)) ^ q :=
    Real.rpow_le_rpow (abs_nonneg _) hlogbd hq
  have hstep2 : (r⁻¹ * gamma ^ (-r)) ^ q = r⁻¹ ^ q * gamma ^ (-r * q) := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hgamma.le _),
      ← Real.rpow_mul hgamma.le]
  have hrq : r * q ≤ 1 / 4 := by
    rw [hrdef, inv_mul_eq_div, div_le_iff₀ hq1]
    linarith
  have hstep3 : gamma ^ (-r * q) ≤ gamma ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hgamma hgamma1 (by linarith)
  have hsq : Real.sqrt gamma = gamma ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow gamma
  have hCpos : (0 : ℝ) < r⁻¹ ^ q := Real.rpow_pos_of_pos (by rw [hrinv]; linarith) q
  calc Real.sqrt gamma * |Real.log gamma| ^ q
      ≤ Real.sqrt gamma * (r⁻¹ ^ q * gamma ^ (-(1 / 4 : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        refine hstep1.trans ?_
        rw [hstep2]
        exact mul_le_mul_of_nonneg_left hstep3 hCpos.le
    _ = r⁻¹ ^ q * (gamma ^ (1 / 2 : ℝ) * gamma ^ (-(1 / 4 : ℝ))) := by
        rw [hsq]; ring
    _ = r⁻¹ ^ q * gamma ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_add hgamma]; norm_num
    _ = (4 * (q + 1)) ^ q * gamma ^ (1 / 4 : ℝ) := by rw [hrinv]

/-- **Any multiple of the amplitude `γ^{1/2}|log γ|^q` is uniformly small for small
disorder.**  For every nonnegative multiplier `K`, every real exponent `q ≥ 0` and every
prescribed positive bound `eps` there is a threshold below which

```text
  K γ^{1/2}|log γ|^q ≤ eps .
```

The threshold is explicit: with `C = (4(q+1))^q` and `B = K C + 1` it is
`min 1 ((eps / B)^4)`, because `γ^{1/2}|log γ|^q ≤ C γ^{1/4}`. -/
theorem exists_sqrt_mul_abs_log_rpow_le {K q eps : ℝ} (hK : 0 ≤ K) (hq : 0 ≤ q)
    (heps : 0 < eps) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ ∀ gamma : ℝ, 0 < gamma → gamma ≤ gamma0 →
      K * (Real.sqrt gamma * Real.rpow |Real.log gamma| q) ≤ eps := by
  set C : ℝ := Real.rpow (4 * (q + 1)) q with hCdef
  have hC : 0 < C := Real.rpow_pos_of_pos (by linarith) q
  set B : ℝ := K * C + 1 with hBdef
  have hB : 0 < B := by positivity
  refine ⟨min 1 ((eps / B) ^ (4 : ℕ)), lt_min zero_lt_one (by positivity), ?_⟩
  intro gamma hgamma hle
  have hg1 : gamma ≤ 1 := hle.trans (min_le_left _ _)
  have hg4 : gamma ≤ (eps / B) ^ (4 : ℕ) := hle.trans (min_le_right _ _)
  have hepsB : 0 ≤ eps / B := by positivity
  have hquarter : Real.rpow gamma (1 / 4) ≤ eps / B := by
    have h1 : Real.rpow gamma (1 / 4) ≤ Real.rpow ((eps / B) ^ (4 : ℕ)) (1 / 4) :=
      Real.rpow_le_rpow hgamma.le hg4 (by norm_num)
    refine h1.trans (le_of_eq ?_)
    show ((eps / B) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) = eps / B
    rw [← Real.rpow_natCast (eps / B) 4, ← Real.rpow_mul hepsB]
    norm_num
  have hmain := sqrt_mul_abs_log_rpow_le_rpow_quarter hq hgamma hg1
  have hKC : K * C ≤ B := by rw [hBdef]; linarith
  have hq0 : (0 : ℝ) ≤ Real.rpow gamma (1 / 4) := Real.rpow_nonneg hgamma.le _
  calc K * (Real.sqrt gamma * Real.rpow |Real.log gamma| q)
      ≤ K * (C * Real.rpow gamma (1 / 4)) := mul_le_mul_of_nonneg_left hmain hK
    _ = K * C * Real.rpow gamma (1 / 4) := by ring
    _ ≤ B * Real.rpow gamma (1 / 4) := mul_le_mul_of_nonneg_right hKC hq0
    _ ≤ B * (eps / B) := mul_le_mul_of_nonneg_left hquarter hB.le
    _ = eps := by field_simp

end

end Algsuperdiff.Section5.Support
