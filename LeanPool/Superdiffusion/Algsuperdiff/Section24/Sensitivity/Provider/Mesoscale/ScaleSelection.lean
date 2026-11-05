/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# ScaleSelection

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The mesoscopic scale-selection arithmetic for the unconditional sensitivity estimates

The unconditional Section 2.4 sensitivity estimates (ABK26, Lemma
`l.J.sensitivity.no.conditions`) remove the smallness assumption of the
conditional estimates by choosing a *mesoscopic* scale `3^{-h}` as a function of
the dimensionless quantity
  `X = ||grad h||_{W^{1,infinity}(cube_0)} * lambda_{s,2}^{-1}(cube_0; a)`,

applying the conditional estimates on every triadic cube of that scale, and
reassembling.  The source's choice is
  `h := ceil ( (1 - 2 s)^{-1} log_3 u )`,  `u = 1 + >= 1`,

and the only property of `h` used afterwards is the two-sided bound
`e.another.way.to.say.h`
  `3^{(1-2s) h - 1} <= u <= 3^{(1-2s) h}`.

This module contains **only** that pure real-analysis arithmetic together with
the exponent bookkeeping it feeds:

* `mesoscaleDepth` and the two-sided bound
  `three_rpow_mesoscaleDepth_sub_one_le` / `le_three_rpow_mesoscaleDepth`;
* `three_rpow_two_mul_mesoscaleDepth_le` — the conversion of the per-cube
  rescaling factor `3^{2 t h}` into `3 * u^{2t/(1-2s)}`, which is where the
  literal factor `3` of the frozen constant `6 = 2 * 3` and the exponent
  `2t/(1-2s)` of `lambda_sensitivity_unconditional` come from (and, at `t := s`,
  the exponent `2s/(1-2s)` of `responseJ_sensitivity_unconditional`);
* `sub_one_mul_three_rpow_neg_mesoscaleDepth_le_one` — the statement that the
  smallness condition of the conditional estimates does hold at the mesoscopic
  scale, in dimensionless form;
* `sub_one_sq_mul_three_rpow_neg_two_mesoscaleDepth_le_min` and
  `min_one_sq_mul_le` — the `min {1, X}^2` bookkeeping of the fourth term of
  `responseJ_sensitivity_unconditional`;
* `three_rpow_neg_two_mul_one_sub_le` — the comparison `3^{-2(1-s)h} <=
  3^{-2(1-2s)h}` used by the Young-inequality step of the source.

Nothing here mentions a coefficient field, a cube, a gauge or a multiscale
quantity: every statement is about plain real numbers.  In particular this file
is gauge-free and is shared by the `lambda` and the `responseJ` halves of the
unconditional estimates.

Every declaration is an internal helper for the Section 2.4 sensitivity
providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Mesoscale

noncomputable section

/-- Bridge between CoarseGraining's explicit `Real.rpow` applications and the `^`
notation used by Mathlib's `rpow` lemmas. -/
private theorem rpow_eq_pow (x y : ℝ) : Real.rpow x y = x ^ y := rfl

/-! ## The mesoscopic depth -/

/-- The mesoscopic scale-separation parameter `h` of ABK26: the number of
triadic scales one descends before applying the conditional sensitivity
estimates.  Here `u` stands for the source's `1 + C ||grad h||_{W^{1,infinity}}
lambda_{s,2}^{-1}`. -/
def mesoscaleDepth (s u : ℝ) : ℕ := ⌈Real.logb 3 u / (1 - 2 * s)⌉₊

/-- The upper half of `e.another.way.to.say.h`: `u <= 3^{(1-2s) h}`. -/
theorem le_three_rpow_mesoscaleDepth {s u : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 4)
    (hu : 1 ≤ u) :
    u ≤ Real.rpow (3 : ℝ) ((1 - 2 * s) * (mesoscaleDepth s u : ℝ)) := by
  simp only [rpow_eq_pow, mesoscaleDepth]
  have hβ : (0 : ℝ) < 1 - 2 * s := by linarith
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hL0 : 0 ≤ Real.logb 3 u := Real.logb_nonneg (by norm_num) hu
  have hu3 : (3 : ℝ) ^ Real.logb 3 u = u :=
    Real.rpow_logb (by norm_num) (by norm_num) hupos
  have hle : Real.logb 3 u ≤ (1 - 2 * s) * (⌈Real.logb 3 u / (1 - 2 * s)⌉₊ : ℝ) := by
    have hceil := Nat.le_ceil (Real.logb 3 u / (1 - 2 * s))
    have := (div_le_iff₀ hβ).mp hceil
    linarith
  calc u = (3 : ℝ) ^ Real.logb 3 u := hu3.symm
    _ ≤ (3 : ℝ) ^ ((1 - 2 * s) * (⌈Real.logb 3 u / (1 - 2 * s)⌉₊ : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hle

/-- The lower half of `e.another.way.to.say.h`: `3^{(1-2s) h - 1} <= u`. -/
theorem three_rpow_mesoscaleDepth_sub_one_le {s u : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 4)
    (hu : 1 ≤ u) :
    Real.rpow (3 : ℝ) ((1 - 2 * s) * (mesoscaleDepth s u : ℝ) - 1) ≤ u := by
  simp only [rpow_eq_pow, mesoscaleDepth]
  have hβ : (0 : ℝ) < 1 - 2 * s := by linarith
  have hβ1 : 1 - 2 * s ≤ 1 := by linarith
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hL0 : 0 ≤ Real.logb 3 u := Real.logb_nonneg (by norm_num) hu
  have hu3 : (3 : ℝ) ^ Real.logb 3 u = u :=
    Real.rpow_logb (by norm_num) (by norm_num) hupos
  have hdiv0 : 0 ≤ Real.logb 3 u / (1 - 2 * s) := div_nonneg hL0 hβ.le
  have hlt : (⌈Real.logb 3 u / (1 - 2 * s)⌉₊ : ℝ) < Real.logb 3 u / (1 - 2 * s) + 1 :=
    Nat.ceil_lt_add_one hdiv0
  have hbh : (1 - 2 * s) * (⌈Real.logb 3 u / (1 - 2 * s)⌉₊ : ℝ)
      < Real.logb 3 u + (1 - 2 * s) := by
    have := mul_lt_mul_of_pos_left hlt hβ
    rwa [mul_add, mul_div_cancel₀ (Real.logb 3 u) (ne_of_gt hβ), mul_one] at this
  have hle : (1 - 2 * s) * (⌈Real.logb 3 u / (1 - 2 * s)⌉₊ : ℝ) - 1
      ≤ Real.logb 3 u := by linarith
  calc (3 : ℝ) ^ ((1 - 2 * s) * (⌈Real.logb 3 u / (1 - 2 * s)⌉₊ : ℝ) - 1)
      ≤ (3 : ℝ) ^ Real.logb 3 u :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
    _ = u := hu3

/-- Restatement of the lower half of `e.another.way.to.say.h`:
`3^{(1-2s) h} <= 3 u`. -/
theorem three_rpow_mesoscaleDepth_le_three_mul {s u : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 4)
    (hu : 1 ≤ u) :
    Real.rpow (3 : ℝ) ((1 - 2 * s) * (mesoscaleDepth s u : ℝ)) ≤ 3 * u := by
  have hlow := three_rpow_mesoscaleDepth_sub_one_le hs0 hs hu
  simp only [rpow_eq_pow] at hlow ⊢
  have hsplit : (3 : ℝ) ^ ((1 - 2 * s) * (mesoscaleDepth s u : ℝ))
      = (3 : ℝ) ^ ((1 - 2 * s) * (mesoscaleDepth s u : ℝ) - 1) * (3 : ℝ) ^ (1 : ℝ) := by
    rw [← Real.rpow_add (by norm_num)]
    congr 1
    ring
  rw [hsplit, Real.rpow_one]
  nlinarith [hlow]

/-! ## Exponent bookkeeping -/

/-- The per-cube rescaling factor `3^{2 t h}` at the mesoscopic depth is bounded
by `(3 u)^{2t/(1-2s)}`. -/
theorem three_rpow_two_mul_mesoscaleDepth_le_rpow {s u t : ℝ} (hs0 : 0 < s)
    (hs : s ≤ 1 / 4) (hu : 1 ≤ u) (ht : 0 ≤ t) :
    Real.rpow (3 : ℝ) (2 * t * (mesoscaleDepth s u : ℝ)) ≤
      Real.rpow (3 * u) (2 * t / (1 - 2 * s)) := by
  have hβ : (0 : ℝ) < 1 - 2 * s := by linarith
  have hstep := three_rpow_mesoscaleDepth_le_three_mul hs0 hs hu
  simp only [rpow_eq_pow] at hstep ⊢
  have hpos : (0 : ℝ) < (3 : ℝ) ^ ((1 - 2 * s) * (mesoscaleDepth s u : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hexp : 2 * t * (mesoscaleDepth s u : ℝ)
      = (1 - 2 * s) * (mesoscaleDepth s u : ℝ) * (2 * t / (1 - 2 * s)) := by
    field_simp
  have hcexp : 0 ≤ 2 * t / (1 - 2 * s) := div_nonneg (by linarith) hβ.le
  calc (3 : ℝ) ^ (2 * t * (mesoscaleDepth s u : ℝ))
      = (3 : ℝ) ^ ((1 - 2 * s) * (mesoscaleDepth s u : ℝ) * (2 * t / (1 - 2 * s))) := by
        rw [hexp]
    _ = ((3 : ℝ) ^ ((1 - 2 * s) * (mesoscaleDepth s u : ℝ))) ^ (2 * t / (1 - 2 * s)) :=
        Real.rpow_mul (by norm_num) _ _
    _ ≤ (3 * u) ^ (2 * t / (1 - 2 * s)) := Real.rpow_le_rpow hpos.le hstep hcexp

/-- **The exponent bookkeeping of the unconditional estimates.**  For
`s, t` in the frozen range `(0, 1/4]` the per-cube rescaling factor `3^{2 t h}`
at the mesoscopic depth is bounded by `3 * u^{2t/(1-2s)}`.

Taken with `t` and the factor `2` coming from the conditional `lambda`
sensitivity estimate at the mesoscopic cubes, this is the exact source of the
literal constant `6 = 2 * 3` and of the exponent `2t/(1-2s)` in
`lambda_sensitivity_unconditional`; taken with `t := s` it is the source of the
exponent `2s/(1-2s)` in `responseJ_sensitivity_unconditional`. -/
theorem three_rpow_two_mul_mesoscaleDepth_le {s u t : ℝ} (hs0 : 0 < s)
    (hs : s ≤ 1 / 4) (hu : 1 ≤ u) (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) :
    Real.rpow (3 : ℝ) (2 * t * (mesoscaleDepth s u : ℝ)) ≤
      3 * Real.rpow u (2 * t / (1 - 2 * s)) := by
  have hβ : (0 : ℝ) < 1 - 2 * s := by linarith
  have hu0 : (0 : ℝ) ≤ u := le_trans zero_le_one hu
  have hexp1 : 2 * t / (1 - 2 * s) ≤ 1 := by
    rw [div_le_one hβ]
    linarith
  have hexp0 : 0 ≤ 2 * t / (1 - 2 * s) := div_nonneg (by linarith) hβ.le
  refine (three_rpow_two_mul_mesoscaleDepth_le_rpow hs0 hs hu ht).trans ?_
  simp only [rpow_eq_pow]
  rw [Real.mul_rpow (by norm_num) hu0]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hu0 _)
  calc (3 : ℝ) ^ (2 * t / (1 - 2 * s)) ≤ (3 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp1
    _ = 3 := Real.rpow_one 3

/-! ## The smallness condition at the mesoscopic scale -/

/-- **The smallness condition holds at the mesoscopic scale.**  In dimensionless
form: the mesoscopic depth is chosen exactly so that `(u - 1) 3^{-(1-2s) h} <=
1`, where `u - 1` stands for the source's `C ||grad h||_{W^{1,infinity}(cube_0)}
lambda_{s,2}^{-1}(cube_0; a)`. -/
theorem sub_one_mul_three_rpow_neg_mesoscaleDepth_le_one {s u : ℝ} (hs0 : 0 < s)
    (hs : s ≤ 1 / 4) (hu : 1 ≤ u) :
    (u - 1) * Real.rpow (3 : ℝ) (-((1 - 2 * s) * (mesoscaleDepth s u : ℝ))) ≤ 1 := by
  have hup := le_three_rpow_mesoscaleDepth hs0 hs hu
  simp only [rpow_eq_pow] at hup ⊢
  have hpos : (0 : ℝ) < (3 : ℝ) ^ ((1 - 2 * s) * (mesoscaleDepth s u : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  rw [Real.rpow_neg (by norm_num)]
  rw [mul_inv_le_iff₀ hpos, one_mul]
  linarith

/-- The squared form of the previous bound. -/
theorem sub_one_sq_mul_three_rpow_neg_two_mesoscaleDepth_le_one {s u : ℝ}
    (hs0 : 0 < s) (hs : s ≤ 1 / 4) (hu : 1 ≤ u) :
    (u - 1) ^ 2 *
        Real.rpow (3 : ℝ) (-(2 * ((1 - 2 * s) * (mesoscaleDepth s u : ℝ)))) ≤ 1 := by
  have hone := sub_one_mul_three_rpow_neg_mesoscaleDepth_le_one hs0 hs hu
  have h0 : (0 : ℝ) ≤ (u - 1) *
      Real.rpow (3 : ℝ) (-((1 - 2 * s) * (mesoscaleDepth s u : ℝ))) := by
    have : (0 : ℝ) ≤ u - 1 := by linarith
    exact mul_nonneg this (Real.rpow_nonneg (by norm_num) _)
  have hsplit : Real.rpow (3 : ℝ) (-(2 * ((1 - 2 * s) * (mesoscaleDepth s u : ℝ))))
      = Real.rpow (3 : ℝ) (-((1 - 2 * s) * (mesoscaleDepth s u : ℝ))) *
        Real.rpow (3 : ℝ) (-((1 - 2 * s) * (mesoscaleDepth s u : ℝ))) := by
    simp only [rpow_eq_pow]
    rw [← Real.rpow_add (by norm_num)]
    congr 1
    ring
  rw [hsplit]
  nlinarith [hone, h0]

/-- The `3^{-2(1-2s)h}`-damped square is bounded by `min {1, (u-1)^2}`. -/
theorem sub_one_sq_mul_three_rpow_neg_two_mesoscaleDepth_le_min {s u : ℝ}
    (hs0 : 0 < s) (hs : s ≤ 1 / 4) (hu : 1 ≤ u) :
    (u - 1) ^ 2 *
        Real.rpow (3 : ℝ) (-(2 * ((1 - 2 * s) * (mesoscaleDepth s u : ℝ))))
      ≤ min 1 ((u - 1) ^ 2) := by
  refine le_min (sub_one_sq_mul_three_rpow_neg_two_mesoscaleDepth_le_one hs0 hs hu) ?_
  have hβ : (0 : ℝ) < 1 - 2 * s := by linarith
  have hle1 : Real.rpow (3 : ℝ) (-(2 * ((1 - 2 * s) * (mesoscaleDepth s u : ℝ)))) ≤ 1 := by
    simp only [rpow_eq_pow]
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    have : (0 : ℝ) ≤ (mesoscaleDepth s u : ℝ) := Nat.cast_nonneg _
    nlinarith
  nlinarith [sq_nonneg (u - 1), hle1]

/-- Repackaging of the `min` bookkeeping: with `u - 1 = C X` and `C, X >= 0`, `min
{1,^2}` is bounded by `max {1, C^2} * min {1, X}^2`.  This is the step that
turns the mesoscale bound into the fourth term `C * min 1 (gradientW1Infinity *
lambda_{s,2}^{-1}) ^ 2` of `responseJ_sensitivity_unconditional`. -/
theorem min_one_sq_mul_le (C X : ℝ) :
    min 1 ((C * X) ^ 2) ≤ max 1 (C ^ 2) * min 1 X ^ 2 := by
  rcases le_total X 1 with hX1 | hX1
  · have hmin : min 1 X = X := min_eq_right hX1
    rw [hmin]
    refine (min_le_right _ _).trans ?_
    have : C ^ 2 ≤ max 1 (C ^ 2) := le_max_right _ _
    nlinarith [sq_nonneg X]
  · have hmin : min 1 X = 1 := min_eq_left hX1
    rw [hmin]
    refine (min_le_left _ _).trans ?_
    have : (1 : ℝ) ≤ max 1 (C ^ 2) := le_max_left _ _
    nlinarith

/-! ## The Young-inequality comparison of damping exponents -/

/-- For `0 <= s` and `n : ℕ`, `3^{-2(1-s)n} <= 3^{-2(1-2s)n}`.  This is the
comparison used by the Young-inequality step of the source in ABK26, where the
`3^{-2(1-s)h}` damping of the gradient term is absorbed into the `min {1, .}^2`
term. -/
theorem three_rpow_neg_two_mul_one_sub_le {s : ℝ} (hs0 : 0 ≤ s) (n : ℕ) :
    Real.rpow (3 : ℝ) (-(2 * (1 - s) * (n : ℝ))) ≤
      Real.rpow (3 : ℝ) (-(2 * (1 - 2 * s) * (n : ℝ))) := by
  simp only [rpow_eq_pow]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  nlinarith

end

end Algsuperdiff.Section24.Sensitivity.Provider.Mesoscale
