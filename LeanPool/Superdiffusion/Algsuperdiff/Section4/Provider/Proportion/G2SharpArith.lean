/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G2ThresholdArith

/-!
# G2SharpArith

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `𝒢₂` `ε`-threshold at the LOG-QUANTILE reading of `θ^{-1/p}`

## What changes, and why

`RatioTailArith.threshold_le_inv` — the step that puts Appendix D's threshold
`9 s'^{-1} C⋆^{1/p} θ^{-1/p}` below the row normalizer's reciprocal — pays the
quantile factor `θ^{-1/p}` by the *crude* bound `θ^{-1/p} ≤ θ^{-1}`.  That single
step is where a whole polynomial power of `1/θ` enters the `𝒢₂` threshold: it is
the reason the crude reading of that threshold carries the divisor `θ` and the
reason its binding clause carries `θ²` rather than `θ`.

The honest reading is logarithmic: `θ^{-1/p} ≤ 3` as soon as
`log(1/θ) ≤ p log 3`, and `log(1/θ) ≤ 1/θ − 1`, so the *existing* moment exponent
already pays for it — `g2MomentExponent`'s rate branch is at least `64/θ`, which
dominates `1/θ`.  No new branch, no new hypothesis, no new parameter: the
quantile power of `1/θ` is simply *not there*.

## Contents

* `rpow_neg_inv_le_three` — `θ^{-1/p} ≤ 3` from `θ⁻¹ ≤ p` (the log-quantile step);
* `threshold_le_inv_sharp` — the sharp twin of `RatioTailArith.threshold_le_inv`,
  at the **`θ`-free** key condition `27 D (1+C⋆) ≤ s'`;
* `inv_theta_le_g2MomentExponent` — the proved moment exponent already exceeds
  `θ⁻¹`, so the sharp step is available with the lane's own `p`;
* `g2ThresholdSharp d r s θ c₁ = 108(1+C⋆)·D` — the **`θ`-free** `ε²`-threshold
  (contrast `g2Threshold … = 36(1+C⋆)·D/θ`);
* `g2ThresholdSharp_le_of` and `g2ThresholdSharp_le_of_gammaPow` — the sufficient
  parameter conditions, in two clauses.

## The two sharp clauses

Writing `κ₁(d)`, `κ₂(d)` for `G2ThresholdArith.g2ThresholdConstOne/Two`:

```
(1)   3κ₁(d) r² (1+c₁) C² γ              ≤ θ  c⋆² s⁵ ε²
(2)   3κ₂(d) r⁸ (1+c₁)⁴ exp(−2c⋆³/(Cγ))  ≤ θ⁴     s⁹ ε²
```

Each is the corresponding clause of the crude reading with **one power of `θ`
removed from the right-hand side** and the constant tripled.
That single power of `θ` is the whole content of the sharpening: against the
consumer's own coupling `ε² = s²θ`, clause (1) reads `γ ≲ θ²`, i.e.  `θ ≳
γ^{1/2}` — the printed Theorem-C range — where the old `θ²` form read `γ ≲ θ³`,
i.e. `θ ≳ γ^{1/3}`.

One polynomial power of `1/θ` does remain inside `D`, through the moment
exponent's rate branch `64r(log 3r + c₁r)/(sθ)`; it is *exactly* the power the
consumer's `ε² = s²θ` pays for, which is why `γ^{1/2}` and not `γ^{1/3}` is the
reachable exponent.  No third source of `1/θ` exists in the chain.

## Scope

Provider material: proved local helpers.  Every transcendental step is an
abstract-real private helper.

## References

* ABK26, `l.ratio.of.good.scales.for.mathcal.E`, in particular the
  constant-selection sentence; `p.concentration.for.scales`, (the threshold `9
  s⁻¹C^{1/p}θ^{-1/p}`).
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section4.Probability.ScalesConcentration

noncomputable section

variable {d : ℕ}

/-! ## 1. The log-quantile step -/

/-- `1 ≤ log 3`, i.e. `e ≤ 3`.  The only numeric fact the log-quantile step
needs. -/
private theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
  exact le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))

/-- **The exponentially small amplitude against a seventh power of `γ`.** `exp(−w)
≤ 5040/w⁷` at `w = 2u³/(xy)`.  (Re-derived: the proved copy in
`G2ThresholdArith` is private.) -/
private theorem exp_neg_two_cube_le_sharp {x u y : ℝ} (hx : 0 < x) (hu : 0 < u) (hy : 0 < y) :
    Real.exp (-(2 * (x⁻¹ * u ^ (3 : ℕ) * y⁻¹)))
      ≤ 315 / 8 * (x ^ (7 : ℕ) * y ^ (7 : ℕ)) / u ^ (21 : ℕ) := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hune : u ≠ 0 := ne_of_gt hu
  have hyne : y ≠ 0 := ne_of_gt hy
  have hw0 : (0 : ℝ) < 2 * (x⁻¹ * u ^ (3 : ℕ) * y⁻¹) := by
    have h := mul_pos (mul_pos (inv_pos.2 hx) (pow_pos hu 3)) (inv_pos.2 hy)
    linarith only [h]
  have hexp := exp_neg_le_seven hw0
  have hpow : (2 * (x⁻¹ * u ^ (3 : ℕ) * y⁻¹)) ^ (7 : ℕ)
      = 128 * u ^ (21 : ℕ) / (x ^ (7 : ℕ) * y ^ (7 : ℕ)) := by
    field_simp
    ring
  rw [hpow] at hexp
  refine le_trans hexp (le_of_eq ?_)
  field_simp
  ring

/-- `x^e ≤ 1 + x` for `x ≥ 0` and `e ∈ [0,1]`.  (Re-derived: the proved copy in
`RatioTailArith` is private.) -/
private theorem rpow_le_one_add_sharp {x e : ℝ} (hx : 0 ≤ x) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    x ^ e ≤ 1 + x := by
  rcases le_or_gt x 1 with h | h
  · have hle := Real.rpow_le_one hx h he0
    linarith only [hle, hx]
  · have hstep := Real.rpow_le_rpow_of_exponent_le h.le he1
    rw [Real.rpow_one] at hstep
    linarith only [hstep]

/-- **The log-quantile bound.**  `θ^{-1/p} ≤ 3` as soon as the moment exponent
clears `1/θ`.

This is the step the proved `RatioTailArith.threshold_le_inv` pays crudely as
`θ^{-1/p} ≤ θ⁻¹`.  The honest requirement is only `log(1/θ) ≤ p log 3`, and
`log(1/θ) ≤ 1/θ − 1 ≤ p − 1 ≤ p log 3`.  It is the only place the quantile
`rpow` is opened. -/
theorem rpow_neg_inv_le_three {theta p : ℝ} (ht0 : 0 < theta) (hp : 1 ≤ p)
    (hpth : theta⁻¹ ≤ p) : theta ^ (-1 / p) ≤ 3 := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hti0 : (0 : ℝ) < theta⁻¹ := inv_pos.2 ht0
  have hpinv0 : (0 : ℝ) < 1 / p := by positivity
  have hlog : Real.log theta⁻¹ ≤ theta⁻¹ - 1 := Real.log_le_sub_one_of_pos hti0
  have hkey : Real.log theta⁻¹ * (1 / p) ≤ Real.log 3 := by
    have h1 : Real.log theta⁻¹ ≤ p - 1 := by linarith only [hlog, hpth]
    have h2 : Real.log theta⁻¹ * (1 / p) ≤ (p - 1) * (1 / p) :=
      mul_le_mul_of_nonneg_right h1 hpinv0.le
    have h3 : (p - 1) * (1 / p) = 1 - 1 / p := by field_simp
    linarith only [h2, h3, hpinv0, one_le_log_three]
  have hrw : theta ^ (-1 / p) = theta⁻¹ ^ (1 / p) := by
    rw [Real.inv_rpow ht0.le, neg_div, Real.rpow_neg ht0.le]
  rw [hrw, Real.rpow_def_of_pos hti0]
  calc Real.exp (Real.log theta⁻¹ * (1 / p)) ≤ Real.exp (Real.log 3) :=
        Real.exp_le_exp.2 hkey
    _ = 3 := Real.exp_log (by norm_num)

/-- **The Appendix-D threshold below the row normalizer's reciprocal, at the
log-quantile reading.**

The sharp twin of `RatioTailArith.threshold_le_inv`: the key condition is
`27 D (1+C⋆) ≤ s'`, with **no `θ` on the right**, at the cost of the extra
requirement `θ⁻¹ ≤ p` on the moment exponent — which the lane's own `p` already
satisfies (`inv_theta_le_g2MomentExponent`). -/
theorem threshold_le_inv_sharp {sprime theta p D : ℝ}
    (hs : 0 < sprime) (ht0 : 0 < theta) (hp : 1 ≤ p) (hpth : theta⁻¹ ≤ p) (hD : 0 < D)
    (hkey : 27 * D * (1 + Cstar) ≤ sprime) :
    9 * sprime⁻¹ * Cstar ^ (1 / p) * theta ^ (-1 / p) ≤ D⁻¹ := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hpinv0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hpinv1 : 1 / p ≤ 1 := by
    rw [div_le_one hp0]
    exact hp
  have hCs : Cstar ^ (1 / p) ≤ 1 + Cstar :=
    rpow_le_one_add_sharp Cstar_pos.le hpinv0 hpinv1
  have hth : theta ^ (-1 / p) ≤ 3 := rpow_neg_inv_le_three ht0 hp hpth
  have h1 : (0 : ℝ) ≤ 9 * sprime⁻¹ := by positivity
  have h2 : (0 : ℝ) ≤ 9 * sprime⁻¹ * (1 + Cstar) :=
    mul_nonneg h1 (by linarith only [Cstar_pos])
  have hchain : 9 * sprime⁻¹ * Cstar ^ (1 / p) * theta ^ (-1 / p)
      ≤ 9 * sprime⁻¹ * (1 + Cstar) * 3 := by
    calc 9 * sprime⁻¹ * Cstar ^ (1 / p) * theta ^ (-1 / p)
        ≤ 9 * sprime⁻¹ * (1 + Cstar) * theta ^ (-1 / p) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCs h1)
            (Real.rpow_nonneg ht0.le _)
      _ ≤ 9 * sprime⁻¹ * (1 + Cstar) * 3 := mul_le_mul_of_nonneg_left hth h2
  refine hchain.trans ?_
  rw [show D⁻¹ = 1 / D from (one_div D).symm, le_div_iff₀ hD]
  rw [show 9 * sprime⁻¹ * (1 + Cstar) * 3 * D = 27 * D * (1 + Cstar) / sprime by
    field_simp; ring]
  rw [div_le_one hs]
  exact hkey

/-! ## 2. The proved moment exponent already clears `1/θ` -/

/-- **The lane's own moment exponent exceeds `θ⁻¹`.**

`g2MomentExponent`'s rate branch is `64r(log 3r + c₁r)/(sθ)`, and `log 3r ≥ 1`,
`r ≥ 1`, `s ≤ 1`, so it is at least `64/θ`.  Hence the log-quantile step
`rpow_neg_inv_le_three` is available at the *unchanged* moment exponent: the
sharp threshold costs no new branch and no new hypothesis. -/
theorem inv_theta_le_g2MomentExponent {r : ℕ} {s theta c1 : ℝ} (hr1 : 1 ≤ r)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hth0 : 0 < theta) (hc1 : 0 ≤ c1) :
    theta⁻¹ ≤ g2MomentExponent r s theta c1 := by
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hst0 : (0 : ℝ) < s * theta := mul_pos hs0 hth0
  have hlog3 : (1 : ℝ) ≤ Real.log (3 * (r : ℝ)) := by
    refine le_trans one_le_log_three ?_
    refine Real.log_le_log (by norm_num) ?_
    linarith only [hrR]
  have hL : (1 : ℝ) ≤ Real.log (3 * (r : ℝ)) + c1 * (r : ℝ) := by
    have hcr : (0 : ℝ) ≤ c1 * (r : ℝ) := mul_nonneg hc1 (by linarith only [hrR])
    linarith only [hlog3, hcr]
  have hnum : (64 : ℝ) ≤ 64 * (r : ℝ) * (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) := by
    have hstep := mul_le_mul hrR hL zero_le_one (by linarith only [hrR])
    linarith only [hstep]
  refine le_trans ?_ (rate_le_g2MomentExponent r s theta c1)
  rw [inv_eq_one_div, div_le_div_iff₀ hth0 hst0]
  have hsth : s * theta ≤ 64 * theta := by
    have hstep := mul_le_mul_of_nonneg_right hs1 hth0.le
    linarith only [hstep, hth0]
  have hbig : 64 * theta
      ≤ 64 * (r : ℝ) * (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * theta :=
    mul_le_mul_of_nonneg_right hnum hth0.le
  linarith only [hsth, hbig]

/-! ## 3. The sharp threshold and its two constants -/

/-- **The `θ`-free `ε²`-threshold of the `𝒢₂` proportion lane.**

`g2ThresholdSharp d r s θ c₁ = 108(1+C⋆)·D`, with `D = g2Normalizer …` the
lane's own Appendix-D normalizer, *unchanged*.  Compare the proved
`G2ThresholdArith.g2Threshold … = 36(1+C⋆)·D/θ`: the constant is tripled and
the divisor `θ` is gone.  The two are therefore related by `g2ThresholdSharp =
3θ · g2Threshold`, so the sharp threshold is the smaller one exactly when `θ <
1/3` — the small-level regime the printed Theorem-C range lives in. -/
def g2ThresholdSharp (d r : ℕ) (C : ℝ) (M : ABKModel d) (s theta c1 : ℝ) : ℝ :=
  108 * (1 + Cstar) * g2Normalizer d r C M s theta c1

/-- The `d`-only constant of the binding clause of the **sharp** threshold
condition: three times the proved `g2ThresholdConstOne`. -/
def g2SharpConstOne (d : ℕ) : ℝ := 3 * g2ThresholdConstOne d

/-- The `d`-only constant of the exponentially small clause of the **sharp**
threshold condition: three times the proved `g2ThresholdConstTwo`. -/
def g2SharpConstTwo (d : ℕ) : ℝ := 3 * g2ThresholdConstTwo d

theorem g2SharpConstTwo_pos (d : ℕ) : 0 < g2SharpConstTwo d := by
  rw [g2SharpConstTwo]
  have h := g2ThresholdConstTwo_pos d
  linarith only [h]

/-! ## 4. The sufficient parameter condition -/

private theorem cubeAmpOne_sq_sharp (C : ℝ) (M : ABKModel d) (s : ℝ) :
    cubeAmpOne d C M s ^ (2 : ℕ)
      = 3 * annulusPenalty d 2 1 ^ (2 : ℕ) * C ^ (2 : ℕ) * M.gamma
          / (Disorder.cstar M ^ (2 : ℕ) * s ^ (2 : ℕ)) := by
  have h3 : Real.sqrt 3 ^ (2 : ℕ) = 3 := Real.sq_sqrt (by norm_num)
  have hG : Real.sqrt M.gamma ^ (2 : ℕ) = M.gamma := Real.sq_sqrt M.shellPrefix.gamma_pos.le
  have hexpand : cubeAmpOne d C M s ^ (2 : ℕ)
      = Real.sqrt 3 ^ (2 : ℕ) * annulusPenalty d 2 1 ^ (2 : ℕ) * C ^ (2 : ℕ)
        * ((Disorder.cstar M)⁻¹) ^ (2 : ℕ) * (s⁻¹) ^ (2 : ℕ)
        * Real.sqrt M.gamma ^ (2 : ℕ) := by
    rw [cubeAmpOne]; ring
  rw [hexpand, h3, hG]
  ring

private theorem exp_neg_sq_sharp (x : ℝ) :
    Real.exp (-x) ^ (2 : ℕ) = Real.exp (-(2 * x)) := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

private theorem cubeAmpTwo_sq_sharp (C : ℝ) (M : ABKModel d) :
    cubeAmpTwo d C M ^ (2 : ℕ)
      = 3 * annulusPenalty d (1 / 2) 1 ^ (2 : ℕ)
          * Real.exp (-(2 * (C⁻¹ * Disorder.cstar M ^ (3 : ℕ) * M.gamma⁻¹))) := by
  have h3 : Real.sqrt 3 ^ (2 : ℕ) = 3 := Real.sq_sqrt (by norm_num)
  have hexpand : cubeAmpTwo d C M ^ (2 : ℕ)
      = Real.sqrt 3 ^ (2 : ℕ) * annulusPenalty d (1 / 2) 1 ^ (2 : ℕ)
        * Real.exp (-(C⁻¹ * Disorder.cstar M ^ (3 : ℕ) * M.gamma⁻¹)) ^ (2 : ℕ) := by
    rw [cubeAmpTwo]; ring
  rw [hexpand, h3, exp_neg_sq_sharp]

/-- **The sharp `ε`-threshold is met under two closed parameter conditions.**

```
(1)   3κ₁(d) r² (1+c₁) C² γ              ≤ θ  c⋆² s⁵ ε²
(2)   3κ₂(d) r⁸ (1+c₁)⁴ exp(−2c⋆³/(Cγ))  ≤ θ⁴     s⁹ ε²
```

Each clause is the corresponding clause of the crude reading with **one power
of `θ` removed from the right-hand side** and the constant tripled.  Clause (1) is the binding one;
at the consumer's coupling `ε² = s²θ`
it reads `γ ≲ θ²`, i.e. `θ ≳ γ^{1/2}` — the printed Theorem-C range — where the
proved `θ²` form read `γ ≲ θ³`. -/
theorem g2ThresholdSharp_le_of (M : ABKModel d) {C s theta c1 ep : ℝ} {r : ℕ}
    (hr1 : 1 ≤ r) (hC0 : 0 < C) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hth0 : 0 < theta) (hth1 : theta ≤ 1) (hc1 : 0 ≤ c1)
    (hcond1 : g2SharpConstOne d * (r : ℝ) ^ (2 : ℕ) * (1 + c1) * C ^ (2 : ℕ) * M.gamma
      ≤ theta * Disorder.cstar M ^ (2 : ℕ) * s ^ (5 : ℕ) * ep ^ (2 : ℕ))
    (hcond2 : g2SharpConstTwo d * (r : ℝ) ^ (8 : ℕ) * (1 + c1) ^ (4 : ℕ)
        * Real.exp (-(2 * (C⁻¹ * Disorder.cstar M ^ (3 : ℕ) * M.gamma⁻¹)))
      ≤ theta ^ (4 : ℕ) * s ^ (9 : ℕ) * ep ^ (2 : ℕ)) :
    g2ThresholdSharp d r C M s theta c1 ≤ ep ^ (2 : ℕ) := by
  have hCs : (0 : ℝ) < 1 + Cstar := by linarith only [Cstar_pos]
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hG0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hgmc1 : (0 : ℝ) < gammaMomentConst 1 := gammaMomentConst_pos (by norm_num)
  have hgmc4 : (0 : ℝ) < gammaMomentConst (1 / 4) := gammaMomentConst_pos (by norm_num)
  have hgtc1 : (0 : ℝ) < gammaTriangleConst (1 : ℝ) := gammaTriangleConst_pos
  have hgtc4 : (0 : ℝ) < gammaTriangleConst (1 / 4 : ℝ) := gammaTriangleConst_pos
  have hpen1 : (0 : ℝ) < annulusPenalty d 2 1 :=
    lt_of_lt_of_le zero_lt_one (one_le_annulusPenalty d (by norm_num) 1)
  have hpen2 : (0 : ℝ) < annulusPenalty d (1 / 2) 1 :=
    lt_of_lt_of_le zero_lt_one (one_le_annulusPenalty d (by norm_num) 1)
  have hE0 : (0 : ℝ) < Real.exp (-(2 * (C⁻¹ * Disorder.cstar M ^ (3 : ℕ) * M.gamma⁻¹))) :=
    Real.exp_pos _
  -- the first (binding) term
  have hT1 : 108 * (1 + Cstar) *
      (gammaMomentConst 1 * g2MomentExponent r s theta c1 *
        (gammaTriangleConst (1 : ℝ) *
          (xcalNormOne d / s ^ (2 : ℕ) * (2 * cubeAmpOne d C M s ^ (2 : ℕ)))))
      ≤ ep ^ (2 : ℕ) / 2 := by
    have hfac : (0 : ℝ) ≤ 648 * (1 + Cstar) * (gammaMomentConst 1 * gammaTriangleConst (1 : ℝ)
        * xcalNormOne d * annulusPenalty d 2 1 ^ (2 : ℕ)) * C ^ (2 : ℕ) * M.gamma
          / (Disorder.cstar M ^ (2 : ℕ) * s ^ (4 : ℕ)) := by
      refine div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith only [hCs])
        (le_of_lt (mul_pos (mul_pos (mul_pos hgmc1 hgtc1) (xcalNormOne_pos d))
          (pow_pos hpen1 2)))) (le_of_lt (pow_pos hC0 2))) hG0.le)
        (le_of_lt (mul_pos (pow_pos hcs0 2) (pow_pos hs0 4)))
    have hden : (0 : ℝ) < Disorder.cstar M ^ (2 : ℕ) * s ^ (5 : ℕ) * theta :=
      mul_pos (mul_pos (pow_pos hcs0 2) (pow_pos hs0 5)) hth0
    calc 108 * (1 + Cstar) *
          (gammaMomentConst 1 * g2MomentExponent r s theta c1 *
            (gammaTriangleConst (1 : ℝ) *
              (xcalNormOne d / s ^ (2 : ℕ) * (2 * cubeAmpOne d C M s ^ (2 : ℕ)))))
        = 648 * (1 + Cstar) * (gammaMomentConst 1 * gammaTriangleConst (1 : ℝ)
            * xcalNormOne d * annulusPenalty d 2 1 ^ (2 : ℕ)) * C ^ (2 : ℕ) * M.gamma
              / (Disorder.cstar M ^ (2 : ℕ) * s ^ (4 : ℕ))
            * g2MomentExponent r s theta c1 := by
          rw [cubeAmpOne_sq_sharp]; ring
      _ ≤ 648 * (1 + Cstar) * (gammaMomentConst 1 * gammaTriangleConst (1 : ℝ)
            * xcalNormOne d * annulusPenalty d 2 1 ^ (2 : ℕ)) * C ^ (2 : ℕ) * M.gamma
              / (Disorder.cstar M ^ (2 : ℕ) * s ^ (4 : ℕ))
            * (192 * (r : ℝ) ^ (2 : ℕ) * (1 + c1) / (s * theta)) :=
          mul_le_mul_of_nonneg_left (g2MomentExponent_le hr1 hs0 hs1 hth0 hth1 hc1) hfac
      _ = 124416 * (1 + Cstar) * (gammaMomentConst 1 * gammaTriangleConst (1 : ℝ)
            * xcalNormOne d * annulusPenalty d 2 1 ^ (2 : ℕ)) * (r : ℝ) ^ (2 : ℕ) * (1 + c1)
            * C ^ (2 : ℕ) * M.gamma
            / (Disorder.cstar M ^ (2 : ℕ) * s ^ (5 : ℕ) * theta) := by
          ring
      _ ≤ ep ^ (2 : ℕ) / 2 := by
          rw [div_le_iff₀ hden]
          rw [g2SharpConstOne, g2ThresholdConstOne] at hcond1
          linarith only [hcond1]
  -- the second (exponentially small) term
  have hT2 : 108 * (1 + Cstar) *
      (gammaMomentConst (1 / 4) * g2MomentExponent r s theta c1 ^ (4 : ℝ) *
        (gammaTriangleConst (1 / 4 : ℝ) *
          (xcalNormQuarter d / s ^ (5 : ℕ) * (2 * cubeAmpTwo d C M ^ (2 : ℕ)))))
      ≤ ep ^ (2 : ℕ) / 2 := by
    have hfac : (0 : ℝ) ≤ 648 * (1 + Cstar) * (gammaMomentConst (1 / 4)
        * gammaTriangleConst (1 / 4 : ℝ) * xcalNormQuarter d
        * annulusPenalty d (1 / 2) 1 ^ (2 : ℕ))
        * Real.exp (-(2 * (C⁻¹ * Disorder.cstar M ^ (3 : ℕ) * M.gamma⁻¹))) / s ^ (5 : ℕ) := by
      refine div_nonneg (mul_nonneg (mul_nonneg (by linarith only [hCs])
        (le_of_lt (mul_pos (mul_pos (mul_pos hgmc4 hgtc4) (xcalNormQuarter_pos d))
          (pow_pos hpen2 2)))) hE0.le) (le_of_lt (pow_pos hs0 5))
    have hden : (0 : ℝ) < s ^ (9 : ℕ) * theta ^ (4 : ℕ) :=
      mul_pos (pow_pos hs0 9) (pow_pos hth0 4)
    calc 108 * (1 + Cstar) *
          (gammaMomentConst (1 / 4) * g2MomentExponent r s theta c1 ^ (4 : ℝ) *
            (gammaTriangleConst (1 / 4 : ℝ) *
              (xcalNormQuarter d / s ^ (5 : ℕ) * (2 * cubeAmpTwo d C M ^ (2 : ℕ)))))
        = 648 * (1 + Cstar) * (gammaMomentConst (1 / 4) * gammaTriangleConst (1 / 4 : ℝ)
            * xcalNormQuarter d * annulusPenalty d (1 / 2) 1 ^ (2 : ℕ))
            * Real.exp (-(2 * (C⁻¹ * Disorder.cstar M ^ (3 : ℕ) * M.gamma⁻¹))) / s ^ (5 : ℕ)
            * g2MomentExponent r s theta c1 ^ (4 : ℝ) := by
          rw [cubeAmpTwo_sq_sharp]; ring
      _ ≤ 648 * (1 + Cstar) * (gammaMomentConst (1 / 4) * gammaTriangleConst (1 / 4 : ℝ)
            * xcalNormQuarter d * annulusPenalty d (1 / 2) 1 ^ (2 : ℕ))
            * Real.exp (-(2 * (C⁻¹ * Disorder.cstar M ^ (3 : ℕ) * M.gamma⁻¹))) / s ^ (5 : ℕ)
            * (1358954496 * (r : ℝ) ^ (8 : ℕ) * (1 + c1) ^ (4 : ℕ)
                / (s ^ (4 : ℕ) * theta ^ (4 : ℕ))) :=
          mul_le_mul_of_nonneg_left
            (g2MomentExponent_rpow_four_le hr1 hs0 hs1 hth0 hth1 hc1) hfac
      _ = 880602513408 * (1 + Cstar) * (gammaMomentConst (1 / 4)
            * gammaTriangleConst (1 / 4 : ℝ) * xcalNormQuarter d
            * annulusPenalty d (1 / 2) 1 ^ (2 : ℕ)) * (r : ℝ) ^ (8 : ℕ) * (1 + c1) ^ (4 : ℕ)
            * Real.exp (-(2 * (C⁻¹ * Disorder.cstar M ^ (3 : ℕ) * M.gamma⁻¹)))
            / (s ^ (9 : ℕ) * theta ^ (4 : ℕ)) := by
          ring
      _ ≤ ep ^ (2 : ℕ) / 2 := by
          rw [div_le_iff₀ hden]
          rw [g2SharpConstTwo, g2ThresholdConstTwo] at hcond2
          linarith only [hcond2]
  rw [g2ThresholdSharp, g2Normalizer]
  linarith only [hT1, hT2]

/-- **The second sharp clause in `γ`-power form.**  `exp(−w) ≤ 5040/w⁷` at
`w = 2c⋆³/(Cγ)` turns the exponentially small clause into

```
(2')  (945/8) κ₂(d) r⁸ (1+c₁)⁴ C⁷ γ⁷ ≤ θ⁴ c⋆²¹ s⁹ ε² ,
```

six powers of `γ` weaker than the binding clause (1), which is linear in `γ`. -/
theorem g2ThresholdSharp_le_of_gammaPow (M : ABKModel d) {C s theta c1 ep : ℝ} {r : ℕ}
    (hr1 : 1 ≤ r) (hC0 : 0 < C) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hth0 : 0 < theta) (hth1 : theta ≤ 1) (hc1 : 0 ≤ c1)
    (hcond1 : g2SharpConstOne d * (r : ℝ) ^ (2 : ℕ) * (1 + c1) * C ^ (2 : ℕ) * M.gamma
      ≤ theta * Disorder.cstar M ^ (2 : ℕ) * s ^ (5 : ℕ) * ep ^ (2 : ℕ))
    (hcond2 : 945 / 8 * g2ThresholdConstTwo d * (r : ℝ) ^ (8 : ℕ) * (1 + c1) ^ (4 : ℕ)
        * C ^ (7 : ℕ) * M.gamma ^ (7 : ℕ)
      ≤ theta ^ (4 : ℕ) * Disorder.cstar M ^ (21 : ℕ) * s ^ (9 : ℕ) * ep ^ (2 : ℕ)) :
    g2ThresholdSharp d r C M s theta c1 ≤ ep ^ (2 : ℕ) := by
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hG0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcspow : (0 : ℝ) < Disorder.cstar M ^ (21 : ℕ) := pow_pos hcs0 21
  have hexp := exp_neg_two_cube_le_sharp hC0 hcs0 hG0
  have hpre : (0 : ℝ) ≤ g2SharpConstTwo d * (r : ℝ) ^ (8 : ℕ) * (1 + c1) ^ (4 : ℕ) :=
    mul_nonneg (mul_nonneg (g2SharpConstTwo_pos d).le (pow_nonneg (Nat.cast_nonneg r) 8))
      (pow_nonneg (by linarith only [hc1]) 4)
  have hstep := mul_le_mul_of_nonneg_left hexp hpre
  have hfinal : 945 / 8 * g2ThresholdConstTwo d * (r : ℝ) ^ (8 : ℕ) * (1 + c1) ^ (4 : ℕ)
      * C ^ (7 : ℕ) * M.gamma ^ (7 : ℕ) / Disorder.cstar M ^ (21 : ℕ)
      ≤ theta ^ (4 : ℕ) * s ^ (9 : ℕ) * ep ^ (2 : ℕ) := by
    rw [div_le_iff₀ hcspow]
    linarith only [hcond2]
  refine g2ThresholdSharp_le_of M hr1 hC0 hs0 hs1 hth0 hth1 hc1 hcond1 (le_trans hstep ?_)
  calc g2SharpConstTwo d * (r : ℝ) ^ (8 : ℕ) * (1 + c1) ^ (4 : ℕ)
        * (315 / 8 * (C ^ (7 : ℕ) * M.gamma ^ (7 : ℕ)) / Disorder.cstar M ^ (21 : ℕ))
      = 945 / 8 * g2ThresholdConstTwo d * (r : ℝ) ^ (8 : ℕ) * (1 + c1) ^ (4 : ℕ)
          * C ^ (7 : ℕ) * M.gamma ^ (7 : ℕ) / Disorder.cstar M ^ (21 : ℕ) := by
        rw [g2SharpConstTwo]; ring
    _ ≤ theta ^ (4 : ℕ) * s ^ (9 : ℕ) * ep ^ (2 : ℕ) := hfinal


end

end Algsuperdiff.Section4.Provider.Proportion
