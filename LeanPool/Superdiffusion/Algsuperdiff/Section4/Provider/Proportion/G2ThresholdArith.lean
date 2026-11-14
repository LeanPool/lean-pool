/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G2RatioTail

/-!
# G2ThresholdArith

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The closed-form parameters of the `𝒢₂` proportion lane

ABK26, §4.1, the constant-selection sentence `e.K.and.p.choices` read as a
condition on `ε` rather than as a choice of `K₂`.

The `𝒢₂` lane endpoints deliver the tail *from a threshold on*: after
`(r, M, s, θ, c₁)` they produce some `ε₀ > 0` and assert the tail for every
`ε ≥ ε₀`.  The threshold is not an artefact — `Support.eventG2` grows with `ε`,
so the small-`ε` side is genuinely the hard one — but the existential hides
which condition on the parameters actually makes it hold.  This module puts the
parameters that condition is written in into closed form.

## Contents

* `g2MomentExponent` — the lane's moment exponent `p`, in closed form
  (`max{1, 4/s, 64rΛ/(sθ)}`, `Λ = log(3r) + c₁r`), chosen after `c₁`;
* `g2Normalizer` — the lane's Appendix-D normalizer `D`, in closed form: the
  two Step-2 Orlicz scales at the closed `s`-power evaluations of `G2Arith` and
  the two per-cube amplitudes of the Section 3 anchor;
* `g2MomentExponent_le` and `g2MomentExponent_rpow_four_le` — the closed
  majorants of the exponent and of its fourth power;
* `g2ThresholdConstOne`, `g2ThresholdConstTwo` — the two `d`-only constants
  `κ₁(d)`, `κ₂(d)` in which the lane's sufficient parameter condition is
  written (`G2SharpArith`).

## Scope

Provider material: proved local helpers.  Every transcendental step is an
abstract-real private helper.

## References

* ABK26, `l.ratio.of.good.scales.for.mathcal.E`, in particular the
  constant-selection sentence.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section4.Probability.ScalesConcentration

noncomputable section

variable {d : ℕ}

/-! ## 1. Abstract-real helpers -/

private theorem div_le_div_right_of_le {a b c : ℝ} (hab : a ≤ b) (hc : 0 ≤ c) :
    a / c ≤ b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hab (inv_nonneg.2 hc)

/-- `log(3r) ≤ 3r − 1`: the only place the logarithm of the rate is opened. -/
private theorem log_three_mul_le {r : ℝ} (hr : 1 ≤ r) : Real.log (3 * r) ≤ 3 * r - 1 :=
  Real.log_le_sub_one_of_pos (by linarith only [hr])

/-- `x^(4:ℝ) = x^(4:ℕ)`: the only place the fourth-moment `rpow` is opened. -/
private theorem rpow_four (x : ℝ) : x ^ (4 : ℝ) = x ^ (4 : ℕ) := by
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-! ## 2. The three closed-form lane parameters -/

/-- **The `𝒢₂` lane's moment exponent, in closed form.**  This is the `p` the
proved endpoint constructs inside its existential: `max{1, 4/s, 64rΛ/(sθ)}`
with `Λ = log(3r) + c₁r`.  It is chosen *after* the rate `c₁`, which is why the
lane carries no rate ceiling. -/
def g2MomentExponent (r : ℕ) (s theta c1 : ℝ) : ℝ :=
  max 1 (max (4 / s) (64 * (r : ℝ) * (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) / (s * theta)))

/-- **The `𝒢₂` lane's Appendix-D normalizer, in closed form.**  This is the `D` the
proved endpoint constructs inside its existential: the two Step-2 Orlicz scales
at the closed `s`-power evaluations `xcalNormOne d · s^{−2}` and
`xcalNormQuarter d · s^{−5}` of `G2Arith`, at the two per-cube amplitudes
`cubeAmpOne`, `cubeAmpTwo` of the Section 3 anchor. -/
def g2Normalizer (d r : ℕ) (C : ℝ) (M : ABKModel d) (s theta c1 : ℝ) : ℝ :=
  gammaMomentConst 1 * g2MomentExponent r s theta c1 *
      (gammaTriangleConst (1 : ℝ) *
        (xcalNormOne d / s ^ (2 : ℕ) * (2 * cubeAmpOne d C M s ^ (2 : ℕ)))) +
    gammaMomentConst (1 / 4) * g2MomentExponent r s theta c1 ^ (4 : ℝ) *
      (gammaTriangleConst (1 / 4 : ℝ) *
        (xcalNormQuarter d / s ^ (5 : ℕ) * (2 * cubeAmpTwo d C M ^ (2 : ℕ))))

/-! ## 3. Positivity -/

theorem one_le_g2MomentExponent (r : ℕ) (s theta c1 : ℝ) :
    1 ≤ g2MomentExponent r s theta c1 := le_max_left _ _

theorem g2MomentExponent_pos (r : ℕ) (s theta c1 : ℝ) :
    0 < g2MomentExponent r s theta c1 :=
  lt_of_lt_of_le zero_lt_one (one_le_g2MomentExponent r s theta c1)

theorem four_div_le_g2MomentExponent (r : ℕ) (s theta c1 : ℝ) :
    4 / s ≤ g2MomentExponent r s theta c1 :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem rate_le_g2MomentExponent (r : ℕ) (s theta c1 : ℝ) :
    64 * (r : ℝ) * (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) / (s * theta)
      ≤ g2MomentExponent r s theta c1 :=
  le_trans (le_max_right _ _) (le_max_right _ _)

/-- Positivity of the `Γ₂`-lane per-cube amplitude.  (The proved lanes keep their
own copies private, so this one is re-derived rather than reused.) -/
theorem cubeAmpOne_pos_of {C : ℝ} (hC : 0 < C) (M : ABKModel d) {s : ℝ} (hs : 0 < s) :
    0 < cubeAmpOne d C M s := by
  have hpen : (0 : ℝ) < annulusPenalty d 2 1 :=
    lt_of_lt_of_le zero_lt_one (one_le_annulusPenalty d (by norm_num) 1)
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hcs : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hg : (0 : ℝ) < Real.sqrt M.gamma := Real.sqrt_pos.2 M.shellPrefix.gamma_pos
  rw [cubeAmpOne]
  exact mul_pos h3 (mul_pos hpen
    (mul_pos (mul_pos (mul_pos hC (inv_pos.2 hcs)) (inv_pos.2 hs)) hg))

/-- Positivity of the `Γ_{1/2}`-lane per-cube amplitude. -/
theorem cubeAmpTwo_pos_of (C : ℝ) (M : ABKModel d) : 0 < cubeAmpTwo d C M := by
  have hpen : (0 : ℝ) < annulusPenalty d (1 / 2) 1 :=
    lt_of_lt_of_le zero_lt_one (one_le_annulusPenalty d (by norm_num) 1)
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [cubeAmpTwo]
  exact mul_pos h3 (mul_pos hpen (Real.exp_pos _))

theorem g2Normalizer_pos {C s : ℝ} (hC : 0 < C) (M : ABKModel d) (r : ℕ) (hs : 0 < s)
    (theta c1 : ℝ) : 0 < g2Normalizer d r C M s theta c1 := by
  have hgmc1 : (0 : ℝ) < gammaMomentConst 1 := gammaMomentConst_pos (by norm_num)
  have hgmc4 : (0 : ℝ) < gammaMomentConst (1 / 4) := gammaMomentConst_pos (by norm_num)
  have hgtc1 : (0 : ℝ) < gammaTriangleConst (1 : ℝ) := gammaTriangleConst_pos
  have hgtc4 : (0 : ℝ) < gammaTriangleConst (1 / 4 : ℝ) := gammaTriangleConst_pos
  have hp0 : (0 : ℝ) < g2MomentExponent r s theta c1 := g2MomentExponent_pos r s theta c1
  have hprpow : (0 : ℝ) < g2MomentExponent r s theta c1 ^ (4 : ℝ) :=
    Real.rpow_pos_of_pos hp0 _
  have hA1 : 0 < cubeAmpOne d C M s := cubeAmpOne_pos_of hC M hs
  have hA2 : 0 < cubeAmpTwo d C M := cubeAmpTwo_pos_of C M
  rw [g2Normalizer]
  refine add_pos (mul_pos (mul_pos hgmc1 hp0) (mul_pos hgtc1 ?_))
    (mul_pos (mul_pos hgmc4 hprpow) (mul_pos hgtc4 ?_))
  · exact mul_pos (div_pos (xcalNormOne_pos d) (pow_pos hs 2))
      (mul_pos two_pos (pow_pos hA1 2))
  · exact mul_pos (div_pos (xcalNormQuarter_pos d) (pow_pos hs 5))
      (mul_pos two_pos (pow_pos hA2 2))

/-! ## 4. The closed majorant of the moment exponent -/

/-- **The moment exponent is at most `192 r²(1+c₁)/(sθ)`.**  All three branches of
the `max` are paid by that single monomial: the constant branch by `sθ ≤ 1`, the
`4/s` branch by `θ ≤ 1`, and the rate branch by `log(3r) ≤ 3r − 1`. -/
theorem g2MomentExponent_le {r : ℕ} {s theta c1 : ℝ} (hr1 : 1 ≤ r) (hs0 : 0 < s)
    (hs1 : s ≤ 1) (hth0 : 0 < theta) (hth1 : theta ≤ 1) (hc1 : 0 ≤ c1) :
    g2MomentExponent r s theta c1 ≤ 192 * (r : ℝ) ^ (2 : ℕ) * (1 + c1) / (s * theta) := by
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hst0 : (0 : ℝ) < s * theta := mul_pos hs0 hth0
  have hst1 : s * theta ≤ 1 := by
    have h := mul_le_mul hs1 hth1 hth0.le zero_le_one
    linarith only [h]
  have hr2 : (1 : ℝ) ≤ (r : ℝ) ^ (2 : ℕ) := one_le_pow₀ hrR
  have hc1' : (1 : ℝ) ≤ 1 + c1 := by linarith only [hc1]
  have hbig : (192 : ℝ) ≤ 192 * (r : ℝ) ^ (2 : ℕ) * (1 + c1) := by
    have h := mul_le_mul hr2 hc1' (by norm_num) (by linarith only [hr2])
    linarith only [h]
  refine max_le ?_ (max_le ?_ ?_)
  · rw [le_div_iff₀ hst0]
    linarith only [hst1, hbig]
  · rw [div_le_div_iff₀ hs0 hst0]
    have hts : s * theta ≤ s := by
      have h := mul_le_mul_of_nonneg_left hth1 hs0.le
      linarith only [h]
    have hmul := mul_le_mul_of_nonneg_right hbig hs0.le
    linarith only [hts, hmul, hs0]
  · refine div_le_div_right_of_le ?_ hst0.le
    have hlog := log_three_mul_le hrR
    have h1 : Real.log (3 * (r : ℝ)) + c1 * (r : ℝ) ≤ 3 * (r : ℝ) + c1 * (r : ℝ) := by
      linarith only [hlog]
    have h2 : 64 * (r : ℝ) * (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ))
        ≤ 64 * (r : ℝ) * (3 * (r : ℝ) + c1 * (r : ℝ)) :=
      mul_le_mul_of_nonneg_left h1 (by linarith only [hrR])
    have h3 : (0 : ℝ) ≤ 128 * c1 * (r : ℝ) ^ (2 : ℕ) :=
      mul_nonneg (mul_nonneg (by norm_num) hc1) (by positivity)
    linarith only [h2, h3]

/-- The fourth power of the majorant of the moment exponent, expanded. -/
theorem g2MomentExponent_rpow_four_le {r : ℕ} {s theta c1 : ℝ} (hr1 : 1 ≤ r) (hs0 : 0 < s)
    (hs1 : s ≤ 1) (hth0 : 0 < theta) (hth1 : theta ≤ 1) (hc1 : 0 ≤ c1) :
    g2MomentExponent r s theta c1 ^ (4 : ℝ)
      ≤ 1358954496 * (r : ℝ) ^ (8 : ℕ) * (1 + c1) ^ (4 : ℕ)
          / (s ^ (4 : ℕ) * theta ^ (4 : ℕ)) := by
  have hple := g2MomentExponent_le hr1 hs0 hs1 hth0 hth1 hc1
  have hp0 : (0 : ℝ) < g2MomentExponent r s theta c1 := g2MomentExponent_pos r s theta c1
  have hpow : g2MomentExponent r s theta c1 ^ (4 : ℕ)
      ≤ (192 * (r : ℝ) ^ (2 : ℕ) * (1 + c1) / (s * theta)) ^ (4 : ℕ) :=
    pow_le_pow_left₀ hp0.le hple 4
  have hexpand : (192 * (r : ℝ) ^ (2 : ℕ) * (1 + c1) / (s * theta)) ^ (4 : ℕ)
      = 1358954496 * (r : ℝ) ^ (8 : ℕ) * (1 + c1) ^ (4 : ℕ)
          / (s ^ (4 : ℕ) * theta ^ (4 : ℕ)) := by
    rw [div_pow, mul_pow, mul_pow, mul_pow, ← pow_mul]
    norm_num
  rw [rpow_four, ← hexpand]
  exact hpow

/-! ## 6. The two threshold constants -/

/-- The `d`-only constant of the binding (`Γ₂`-lane) clause of the `𝒢₂`
threshold condition. -/
def g2ThresholdConstOne (d : ℕ) : ℝ :=
  82944 * (1 + Cstar) * gammaMomentConst 1 * gammaTriangleConst (1 : ℝ)
    * xcalNormOne d * annulusPenalty d 2 1 ^ (2 : ℕ)

/-- The `d`-only constant of the exponentially small (`Γ_{1/2}`-lane) clause of
the `𝒢₂` threshold condition. -/
def g2ThresholdConstTwo (d : ℕ) : ℝ :=
  587068342272 * (1 + Cstar) * gammaMomentConst (1 / 4) * gammaTriangleConst (1 / 4 : ℝ)
    * xcalNormQuarter d * annulusPenalty d (1 / 2) 1 ^ (2 : ℕ)

theorem g2ThresholdConstOne_pos (d : ℕ) : 0 < g2ThresholdConstOne d := by
  have hCs : (0 : ℝ) < 1 + Cstar := by linarith only [Cstar_pos]
  have hgmc1 : (0 : ℝ) < gammaMomentConst 1 := gammaMomentConst_pos (by norm_num)
  have hgtc1 : (0 : ℝ) < gammaTriangleConst (1 : ℝ) := gammaTriangleConst_pos
  have hpen : (0 : ℝ) < annulusPenalty d 2 1 :=
    lt_of_lt_of_le zero_lt_one (one_le_annulusPenalty d (by norm_num) 1)
  rw [g2ThresholdConstOne]
  exact mul_pos (mul_pos (mul_pos (mul_pos (by linarith only [hCs]) hgmc1) hgtc1)
    (xcalNormOne_pos d)) (pow_pos hpen 2)

theorem g2ThresholdConstTwo_pos (d : ℕ) : 0 < g2ThresholdConstTwo d := by
  have hCs : (0 : ℝ) < 1 + Cstar := by linarith only [Cstar_pos]
  have hgmc4 : (0 : ℝ) < gammaMomentConst (1 / 4) := gammaMomentConst_pos (by norm_num)
  have hgtc4 : (0 : ℝ) < gammaTriangleConst (1 / 4 : ℝ) := gammaTriangleConst_pos
  have hpen : (0 : ℝ) < annulusPenalty d (1 / 2) 1 :=
    lt_of_lt_of_le zero_lt_one (one_le_annulusPenalty d (by norm_num) 1)
  rw [g2ThresholdConstTwo]
  exact mul_pos (mul_pos (mul_pos (mul_pos (by linarith only [hCs]) hgmc4) hgtc4)
    (xcalNormQuarter_pos d)) (pow_pos hpen 2)

end

end Algsuperdiff.Section4.Provider.Proportion
