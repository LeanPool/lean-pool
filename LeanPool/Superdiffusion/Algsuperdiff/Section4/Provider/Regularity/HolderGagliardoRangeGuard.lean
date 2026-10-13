/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.HolderGagliardoEmbedding
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# HolderGagliardoRangeGuard

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `s < 1/2` range guard and the `(1-2s)^{-1/2}` constant

## The target

The `C^{0,1/2} ⊂ H^s` embedding used by `l.excess.decay.good.scales` and by
`t.regularity` Step 4 holds only for `s < 1/2`, with constant
`~ (1-2s)^{-1/2}·3^{(1/2-s)n}` — a factor absent from the printed excess-decay
constant.  This module makes that constant explicit and *machine-checked* in the
development's own carrier:

```text
  C_{S4.4}(d,s) := ( C_rad(d, d+2s-1) )^{1/2}
                 ≤ ( 2^{d+1} 3^{d} / (1-2s) )^{1/2}
                 = 2^{(d+1)/2} 3^{d/2} (1-2s)^{-1/2}          (0 < s < 1/2),
```

The `s`-free form at the §4.4/§4.5 gate `s ≤ 1/4`, where `1 - 2s ≥ 1/2` and the
right-hand side collapses to `( 2^{d+2} 3^{d} )^{1/2}`, is read off this bound
downstream, in the §4.5 data embedding.

The only analytic content is the elementary lower bound `1 - 3^{-t} ≥ t/2` on
`t ∈ [0,1]`, which is Bernoulli's inequality for exponents in `[0,1]` (the chord
bound for `t ↦ 3^{-t}`); `t := 1 - 2s` is exactly the gap to the endpoint.

## References

* ABK26, (`l.excess.decay.good.scales`, the printed range `s ∈ [8γ, 1/2]`),
  (the `s := 1/4` pin).
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The Step-4 seminorm constant -/

/-- `C_{S4.4}(d,s) = ( C_rad(d, d+2s-1) )^{1/2}`, the constant of the
`C^{0,1/2} ↪ H^s` atom once the scale weight `R^{1/2-s}` is factored out. -/
def stepFourGagliardoConst (d : ℕ) (s : ℝ) : ℝ :=
  Real.sqrt (radialKernelConst d (holderGagliardoBeta d s))

theorem stepFourGagliardoConst_nonneg (d : ℕ) (s : ℝ) : 0 ≤ stepFourGagliardoConst d s :=
  Real.sqrt_nonneg _

/-! ## 2. The elementary gap estimate `1 - 3^{-t} ≥ t/2` -/

private theorem one_div_three_rpow (t : ℝ) : ((1 : ℝ) / 3) ^ t = (3 : ℝ) ^ (-t) := by
  rw [one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 3),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]

/-- **The gap estimate.**  For `0 ≤ t ≤ 1`, `1 - 3^{-t} ≥ t/2`.

This is the quantitative form of "the Gagliardo integral converges with room at
`s < 1/2`": at `t = 1 - 2s` the left side is the denominator of
`radialKernelConst`, so the constant blows up at most like `2/(1-2s)`.  The
proof is Bernoulli's inequality for exponents in `[0,1]` (the chord bound for
the convex function `t ↦ 3^{-t}` on `[0,1]`, whose endpoints are `1` and
`1/3`); it needs no numerical bound on `log 3`. -/
theorem half_le_one_sub_three_rpow_neg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t / 2 ≤ 1 - (3 : ℝ) ^ (-t) := by
  have hb := rpow_one_add_le_one_add_mul_self (s := -(2 / 3 : ℝ)) (p := t)
    (by norm_num) ht0 ht1
  rw [show (1 : ℝ) + -(2 / 3 : ℝ) = 1 / 3 by norm_num, one_div_three_rpow] at hb
  linarith only [hb, ht0]

/-! ## 3. The constant at the Hölder exponent -/

private theorem one_div_three_rpow_neg (beta : ℝ) :
    ((1 : ℝ) / 3) ^ (-beta) = (3 : ℝ) ^ beta := by
  rw [one_div_three_rpow, neg_neg]

private theorem annulusRatio_holderGagliardoBeta {s : ℝ} :
    annulusRatio d (holderGagliardoBeta d s) = (3 : ℝ) ^ (-(1 - 2 * s)) := by
  have hd3 : (3 : ℝ) ^ d = (3 : ℝ) ^ ((d : ℕ) : ℝ) := (Real.rpow_natCast 3 d).symm
  rw [annulusRatio, hd3, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 3), holderGagliardoBeta]
  congr 1
  ring

theorem radialKernelConst_holderGagliardoBeta_le {s : ℝ} (hs0 : 0 < s) (hs : s < 1 / 2) :
    radialKernelConst d (holderGagliardoBeta d s) ≤
      (2 : ℝ) ^ (d + 1) * (3 : ℝ) ^ d / (1 - 2 * s) := by
  have ht0 : (0 : ℝ) < 1 - 2 * s := by linarith only [hs]
  have ht1 : (1 : ℝ) - 2 * s ≤ 1 := by linarith only [hs0]
  have hhalf : (0 : ℝ) < (1 - 2 * s) / 2 := by linarith only [ht0]
  have hgap : (1 - 2 * s) / 2 ≤ 1 - annulusRatio d (holderGagliardoBeta d s) := by
    rw [annulusRatio_holderGagliardoBeta]
    exact half_le_one_sub_three_rpow_neg ht0.le ht1
  have hden : (0 : ℝ) < 1 - annulusRatio d (holderGagliardoBeta d s) := by
    linarith only [hhalf, hgap]
  have hnum : ((1 : ℝ) / 3) ^ (-holderGagliardoBeta d s) * (2 : ℝ) ^ d ≤
      (3 : ℝ) ^ d * (2 : ℝ) ^ d := by
    have hb : (3 : ℝ) ^ holderGagliardoBeta d s ≤ (3 : ℝ) ^ d := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        (show holderGagliardoBeta d s ≤ ((d : ℕ) : ℝ) by
          rw [holderGagliardoBeta]; linarith only [hs])
      rwa [Real.rpow_natCast] at h
    rw [one_div_three_rpow_neg]
    exact mul_le_mul_of_nonneg_right hb (by positivity)
  have hnum0 : (0 : ℝ) ≤ ((1 : ℝ) / 3) ^ (-holderGagliardoBeta d s) * (2 : ℝ) ^ d := by
    have : (0 : ℝ) < ((1 : ℝ) / 3) ^ (-holderGagliardoBeta d s) :=
      Real.rpow_pos_of_pos (by norm_num) _
    positivity
  have hstep : radialKernelConst d (holderGagliardoBeta d s) ≤
      (3 : ℝ) ^ d * (2 : ℝ) ^ d / ((1 - 2 * s) / 2) := by
    rw [radialKernelConst, div_le_div_iff₀ hden hhalf]
    have hA : ((1 : ℝ) / 3) ^ (-holderGagliardoBeta d s) * (2 : ℝ) ^ d * ((1 - 2 * s) / 2) ≤
        (3 : ℝ) ^ d * (2 : ℝ) ^ d * ((1 - 2 * s) / 2) :=
      mul_le_mul_of_nonneg_right hnum hhalf.le
    have hB : (3 : ℝ) ^ d * (2 : ℝ) ^ d * ((1 - 2 * s) / 2) ≤
        (3 : ℝ) ^ d * (2 : ℝ) ^ d * (1 - annulusRatio d (holderGagliardoBeta d s)) :=
      mul_le_mul_of_nonneg_left hgap (by positivity)
    linarith only [hA, hB]
  refine hstep.trans (le_of_eq ?_)
  rw [pow_succ]
  field_simp

theorem stepFourGagliardoConst_le {s : ℝ} (hs0 : 0 < s) (hs : s < 1 / 2) :
    stepFourGagliardoConst d s ≤ Real.sqrt ((2 : ℝ) ^ (d + 1) * (3 : ℝ) ^ d / (1 - 2 * s)) := by
  rw [stepFourGagliardoConst]
  exact Real.sqrt_le_sqrt (radialKernelConst_holderGagliardoBeta_le hs0 hs)

end

end Algsuperdiff.Section4.Provider.Regularity
