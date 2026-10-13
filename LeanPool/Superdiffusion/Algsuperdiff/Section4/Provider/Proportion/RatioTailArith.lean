/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.Concentration

/-!
# RatioTailArith

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The parameter arithmetic of the `𝒢₀` proportion tail

ABK26, §4.1, the three numerical steps of `l.good.scales.ratio.lambda` that the
manuscript performs in one line each: the `γ^{-4}` normalizer, the regime
bookkeeping behind the `s`-window of `p.cg.ellipticity.bounds` and behind the
`p`-choice, and the threshold identification.

Everything here is abstract-real: no ABK carrier, no measure, no random
variable.  Per the elaboration discipline every transcendental atom
(`Real.exp`, `Real.log`, `Real.rpow`) is confined to a dedicated helper and no
numeric tactic ever sees one:

* `exp_neg_le_factorial_div` — `exp(−w) ≤ n!/wⁿ`, the single opening of the
  exponential, specialised at `n = 2` and `n = 7`;
* `one_sub_three_rpow_ge` — `1 − 3^{−γ/4} ≥ γ/8`, the spectral gap of the
  geometric weight;
* `rpow_le_one_add` — `x^e ≤ 1 + x` for `e ∈ [0,1]`.

## Main results

* `tsum_weightThird_mul_annulusPenaltyThird_le` — the `γ^{-4}` closed form
  `Σ_j 3^{−¼γ j}(1 + d(j+3)log 3)³ ≤ penaltyNormalizer d · γ^{-4}`, from the
  cubic penalty bound, `Σ_j binom(j+3,3)wʲ = (1−w)^{-4}` and the spectral gap.
* `regime_core` — the three power inequalities the printed regime `γ ≤
  C^{−10}c⋆^{10}` yields for the atom-tail exponent `u = c⋆²/(C_cg C² γ)` at
  the budget `E = C c⋆^{−1}`, using the proved `c⋆ ≤ 3/2`.
* `threshold_le_inv` — the Appendix-D threshold `9 s'^{-1}C^{1/p}θ^{-1/p}` sits
  below `D^{-1}` as soon as `9 D (1 + C_⋆) ≤ s' θ`.
* `exists_dependence_range` — an `r ≥ 1` with `3 + (2/3)√d ≤ 3^r` exists in
  every dimension.

## Scope

Provider material: proved local helpers.

## References

* ABK26, `l.good.scales.ratio.lambda`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability
open Algsuperdiff.Section4.Probability.ScalesConcentration
open Algsuperdiff.Section4.Probability.IndicatorDensity

noncomputable section

/-! ## 1. Abstract-real transcendental helpers -/

/-- `exp(−w) ≤ n!/wⁿ` for `w > 0`.  The only place the exponential is opened. -/
private theorem exp_neg_le_factorial_div (n : ℕ) {w : ℝ} (hw : 0 < w) :
    Real.exp (-w) ≤ ((Nat.factorial n : ℕ) : ℝ) / w ^ n := by
  have hbase := Real.pow_div_factorial_le_exp (x := w) hw.le n
  have hfac : (0 : ℝ) < ((Nat.factorial n : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hwn : (0 : ℝ) < w ^ n := pow_pos hw n
  rw [Real.exp_neg]
  have h := inv_anti₀ (div_pos hwn hfac) hbase
  rwa [inv_div] at h

/-- `exp(−w) ≤ 2/w²`. -/
theorem exp_neg_le_two_div_sq {w : ℝ} (hw : 0 < w) :
    Real.exp (-w) ≤ 2 / w ^ (2 : ℕ) := by
  have h := exp_neg_le_factorial_div 2 hw
  have hfac : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
  rwa [hfac] at h

/-- `exp(−w) ≤ 5040/w⁷`. -/
theorem exp_neg_le_seven {w : ℝ} (hw : 0 < w) :
    Real.exp (-w) ≤ 5040 / w ^ (7 : ℕ) := by
  have h := exp_neg_le_factorial_div 7 hw
  have hfac : ((Nat.factorial 7 : ℕ) : ℝ) = 5040 := by norm_num [Nat.factorial]
  rwa [hfac] at h

/-- `x^e ≤ 1 + x` for `x ≥ 0` and `e ∈ [0,1]`. -/
private theorem rpow_le_one_add {x e : ℝ} (hx : 0 ≤ x) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    x ^ e ≤ 1 + x := by
  rcases le_or_gt x 1 with h | h
  · have hle := Real.rpow_le_one hx h he0
    linarith only [hle, hx]
  · have hle := Real.rpow_le_rpow_of_exponent_le h.le he1
    rw [Real.rpow_one] at hle
    linarith only [hle]

/-- `1 − 3^{−γ/4} ≥ γ/8` for `γ ∈ (0,1/4]`: the spectral gap of the geometric
weight, in the form the `γ^{-4}` closed form needs. -/
private theorem one_sub_three_rpow_ge {gamma : ℝ} (h0 : 0 < gamma) (h4 : gamma ≤ 1 / 4) :
    gamma / 8 ≤ 1 - (3 : ℝ) ^ (-(gamma / 4)) := by
  have hlog1 : (1 : ℝ) < Real.log 3 := log_three_gt_one
  have hlog2 : Real.log 3 < 2 := log_three_lt_two
  have hy0 : (0 : ℝ) < gamma / 4 * Real.log 3 := by
    have : (0 : ℝ) < gamma / 4 := by linarith only [h0]
    exact mul_pos this (by linarith only [hlog1])
  have hy1 : gamma / 4 * Real.log 3 ≤ 1 := by
    have hq : gamma / 4 ≤ 1 / 16 := by linarith only [h4]
    have hstep : gamma / 4 * Real.log 3 ≤ (1 / 16 : ℝ) * 2 :=
      mul_le_mul hq hlog2.le (by linarith only [hlog1]) (by norm_num)
    linarith only [hstep]
  have hrw : (3 : ℝ) ^ (-(gamma / 4)) = Real.exp (-(gamma / 4 * Real.log 3)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have h1y : (0 : ℝ) < 1 + gamma / 4 * Real.log 3 := by linarith only [hy0]
  have hexpy : 1 + gamma / 4 * Real.log 3 ≤ Real.exp (gamma / 4 * Real.log 3) := by
    linarith only [Real.add_one_le_exp (gamma / 4 * Real.log 3)]
  have hinv : Real.exp (-(gamma / 4 * Real.log 3)) ≤ 1 / (1 + gamma / 4 * Real.log 3) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le h1y hexpy
  have hsq : (gamma / 4 * Real.log 3) * (gamma / 4 * Real.log 3) ≤ gamma / 4 * Real.log 3 := by
    calc (gamma / 4 * Real.log 3) * (gamma / 4 * Real.log 3)
        ≤ 1 * (gamma / 4 * Real.log 3) := mul_le_mul_of_nonneg_right hy1 hy0.le
      _ = gamma / 4 * Real.log 3 := one_mul _
  have hfrac : 1 / (1 + gamma / 4 * Real.log 3) ≤ 1 - (gamma / 4 * Real.log 3) / 2 := by
    rw [div_le_iff₀ h1y]
    have hexpand : (1 - (gamma / 4 * Real.log 3) / 2) * (1 + gamma / 4 * Real.log 3)
        = 1 + (gamma / 4 * Real.log 3) / 2
          - ((gamma / 4 * Real.log 3) * (gamma / 4 * Real.log 3)) / 2 := by ring
    rw [hexpand]
    linarith only [hsq]
  have hhalf : gamma / 8 ≤ (gamma / 4 * Real.log 3) / 2 := by
    have hstep : gamma / 4 * 1 ≤ gamma / 4 * Real.log 3 :=
      mul_le_mul_of_nonneg_left hlog1.le (by linarith only [h0])
    linarith only [hstep]
  rw [hrw]
  linarith only [hinv, hfrac, hhalf]

/-! ## 2. The `γ^{-4}` closed form of the `𝒴`-normalizer -/

/-- **The dimensional constant of the `𝒴`-normalizer.**  With it, `Σ_j 3^{−¼γ
j}(1+d(j+3)log 3)³ ≤ penaltyNormalizer d · γ^{-4}`, which is the manuscript's
`γ^{-4}` in closed form (: the normalization is a lane prefactor, so this is a
bound on the tail scale, not a rescaling of the score field). -/
def penaltyNormalizer (d : ℕ) : ℝ := 24576 * (1 + 3 * (d : ℝ) * Real.log 3) ^ (3 : ℕ)

theorem penaltyNormalizer_pos (d : ℕ) : 0 < penaltyNormalizer d := by
  have hlog : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hbase : (0 : ℝ) < 1 + 3 * (d : ℝ) * Real.log 3 := by positivity
  rw [penaltyNormalizer]
  positivity

private theorem annulusPenaltyThird_le_cube (d : ℕ) (j : ℕ) :
    annulusPenaltyThird d (j + 2)
      ≤ (1 + 3 * (d : ℝ) * Real.log 3) ^ (3 : ℕ) * (((j : ℝ) + 1) ^ (3 : ℕ)) := by
  have hlog : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hbase : 1 + (d : ℝ) * (((j + 2 : ℕ) : ℝ) + 1) * Real.log 3
      ≤ (1 + 3 * (d : ℝ) * Real.log 3) * ((j : ℝ) + 1) := by
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hcast : ((j + 2 : ℕ) : ℝ) = (j : ℝ) + 2 := by push_cast; ring
    rw [hcast]
    have hprod : (0 : ℝ) ≤ (d : ℝ) * Real.log 3 * (j : ℝ) := by positivity
    linarith only [hprod, hj]
  have hnn : (0 : ℝ) ≤ 1 + (d : ℝ) * (((j + 2 : ℕ) : ℝ) + 1) * Real.log 3 := by positivity
  calc annulusPenaltyThird d (j + 2)
      ≤ ((1 + 3 * (d : ℝ) * Real.log 3) * ((j : ℝ) + 1)) ^ (3 : ℕ) :=
        pow_le_pow_left₀ hnn hbase 3
    _ = (1 + 3 * (d : ℝ) * Real.log 3) ^ (3 : ℕ) * (((j : ℝ) + 1) ^ (3 : ℕ)) := by
        rw [mul_pow]

private theorem cube_le_choose (j : ℕ) :
    (((j : ℝ) + 1) ^ (3 : ℕ)) ≤ 6 * ((((j + 3).choose 3 : ℕ)) : ℝ) := by
  have hd : (j + 3).descFactorial 3 = 6 * ((j + 3).choose 3) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    norm_num [Nat.factorial]
  have hval : (j + 3).descFactorial 3 = (j + 1) * ((j + 2) * (j + 3)) := by
    have e1 : j + 3 - 2 = j + 1 := by omega
    have e2 : j + 3 - 1 = j + 2 := by omega
    have e3 : j + 3 - 0 = j + 3 := by omega
    simp only [Nat.descFactorial, e1, e2, e3, Nat.mul_one]
  have hnat : (j + 1) ^ 3 ≤ 6 * ((j + 3).choose 3) := by
    rw [← hd, hval]
    calc (j + 1) ^ 3 = (j + 1) * ((j + 1) * (j + 1)) := by ring
      _ ≤ (j + 1) * ((j + 2) * (j + 3)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have hcast := (Nat.cast_le (α := ℝ)).2 hnat
  push_cast at hcast
  exact hcast

/-- **The `γ^{-4}` closed form.**  The weighted lattice penalties of the `𝒴`-tail
sum to at most `penaltyNormalizer d · γ^{-4}` at the manuscript's rate `s' = γ/4`.
The three ingredients are the cubic penalty bound, the identity
`Σ_j binom(j+3,3) w^j = (1−w)^{-4}`, and the spectral gap `1 − 3^{−γ/4} ≥ γ/8`. -/
theorem tsum_weightThird_mul_annulusPenaltyThird_le (d : ℕ) {gamma : ℝ}
    (h0 : 0 < gamma) (h4 : gamma ≤ 1 / 4) :
    ∑' j : ℕ, weightThird (gamma / 4) j * annulusPenaltyThird d (j + 2)
      ≤ penaltyNormalizer d / gamma ^ (4 : ℕ) := by
  have hw0 : (0 : ℝ) < (3 : ℝ) ^ (-(gamma / 4)) := Real.rpow_pos_of_pos (by norm_num) _
  have hgap : gamma / 8 ≤ 1 - (3 : ℝ) ^ (-(gamma / 4)) := one_sub_three_rpow_ge h0 h4
  have hg8 : (0 : ℝ) < gamma / 8 := by linarith only [h0]
  have hw1 : (3 : ℝ) ^ (-(gamma / 4)) < 1 := by linarith only [hgap, hg8]
  have hnorm : ‖(3 : ℝ) ^ (-(gamma / 4))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hw0.le]
    exact hw1
  have hlog : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hB0 : (0 : ℝ) ≤ (1 + 3 * (d : ℝ) * Real.log 3) ^ (3 : ℕ) := by positivity
  have hterm : ∀ j : ℕ, weightThird (gamma / 4) j * annulusPenaltyThird d (j + 2)
      ≤ 6 * (1 + 3 * (d : ℝ) * Real.log 3) ^ (3 : ℕ) *
        (((((j + 3).choose 3 : ℕ)) : ℝ) * ((3 : ℝ) ^ (-(gamma / 4))) ^ j) := by
    intro j
    have hwj : weightThird (gamma / 4) j = ((3 : ℝ) ^ (-(gamma / 4))) ^ j := rfl
    have hpow : (0 : ℝ) ≤ ((3 : ℝ) ^ (-(gamma / 4))) ^ j := pow_nonneg hw0.le j
    calc weightThird (gamma / 4) j * annulusPenaltyThird d (j + 2)
        = ((3 : ℝ) ^ (-(gamma / 4))) ^ j * annulusPenaltyThird d (j + 2) := by rw [hwj]
      _ ≤ ((3 : ℝ) ^ (-(gamma / 4))) ^ j *
            ((1 + 3 * (d : ℝ) * Real.log 3) ^ (3 : ℕ) * (((j : ℝ) + 1) ^ (3 : ℕ))) :=
          mul_le_mul_of_nonneg_left (annulusPenaltyThird_le_cube d j) hpow
      _ ≤ ((3 : ℝ) ^ (-(gamma / 4))) ^ j *
            ((1 + 3 * (d : ℝ) * Real.log 3) ^ (3 : ℕ) *
              (6 * ((((j + 3).choose 3 : ℕ)) : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (cube_le_choose j) hB0) hpow
      _ = 6 * (1 + 3 * (d : ℝ) * Real.log 3) ^ (3 : ℕ) *
            (((((j + 3).choose 3 : ℕ)) : ℝ) * ((3 : ℝ) ^ (-(gamma / 4))) ^ j) := by ring
  have hsumL : Summable fun j : ℕ =>
      weightThird (gamma / 4) j * annulusPenaltyThird d (j + 2) := by
    refine (summable_weight_mul_annulusPenaltyThird d (sprime := gamma / 4) (A := 1)
      (by linarith only [h0]) zero_le_one).congr fun j => ?_
    ring
  have hsumR : Summable fun j : ℕ =>
      6 * (1 + 3 * (d : ℝ) * Real.log 3) ^ (3 : ℕ) *
        (((((j + 3).choose 3 : ℕ)) : ℝ) * ((3 : ℝ) ^ (-(gamma / 4))) ^ j) :=
    (summable_choose_mul_geometric_of_norm_lt_one 3 hnorm).mul_left _
  calc ∑' j : ℕ, weightThird (gamma / 4) j * annulusPenaltyThird d (j + 2)
      ≤ ∑' j : ℕ, 6 * (1 + 3 * (d : ℝ) * Real.log 3) ^ (3 : ℕ) *
          (((((j + 3).choose 3 : ℕ)) : ℝ) * ((3 : ℝ) ^ (-(gamma / 4))) ^ j) :=
        hsumL.tsum_le_tsum hterm hsumR
    _ = 6 * (1 + 3 * (d : ℝ) * Real.log 3) ^ (3 : ℕ) *
          ∑' j : ℕ, (((((j + 3).choose 3 : ℕ)) : ℝ) * ((3 : ℝ) ^ (-(gamma / 4))) ^ j) :=
        tsum_mul_left
    _ = 6 * (1 + 3 * (d : ℝ) * Real.log 3) ^ (3 : ℕ) *
          (1 / (1 - (3 : ℝ) ^ (-(gamma / 4))) ^ (3 + 1)) := by
        rw [tsum_choose_mul_geometric_of_norm_lt_one 3 hnorm]
    _ ≤ 6 * (1 + 3 * (d : ℝ) * Real.log 3) ^ (3 : ℕ) * (1 / (gamma / 8) ^ (3 + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine one_div_le_one_div_of_le (by positivity) ?_
        exact pow_le_pow_left₀ hg8.le hgap (3 + 1)
    _ = penaltyNormalizer d / gamma ^ (4 : ℕ) := by
        rw [penaltyNormalizer]
        field_simp
        ring

/-! ## 3. The regime core: two power inequalities -/

/-- **The abstract-real core of the parameter arithmetic.**  With the atom-tail
exponent `u = c⋆²/(C_cg C² γ)` at the budget `E = C c⋆^{−1}`, the printed
regime `γ ≤ C^{−10}c⋆^{10}` and the proved `c⋆ ≤ 3/2` give the two lower bounds
the `s`-window and the `p`-choice consume.  No transcendental atom appears. -/
theorem regime_core {gamma cs Ccg C u : ℝ}
    (hg : 0 < gamma) (hcs : 0 < cs) (hcs32 : cs ≤ 3 / 2) (hCcg : 0 < Ccg) (hC : 0 < C)
    (hreg : gamma ≤ (C⁻¹) ^ (10 : ℕ) * cs ^ (10 : ℕ))
    (hu : u = Ccg⁻¹ * ((C * cs⁻¹)⁻¹) ^ (2 : ℕ) * gamma⁻¹) :
    C ^ (6 : ℕ) ≤ 12 * Ccg ^ (2 : ℕ) * (gamma * u ^ (2 : ℕ)) ∧
      C ^ (6 : ℕ) ≤ 12 * Ccg ^ (7 : ℕ) * (gamma ^ (5 : ℕ) * u ^ (7 : ℕ)) ∧
        C ^ (4 : ℕ) ≤ 6 * Ccg ^ (3 : ℕ) * (gamma ^ (2 : ℕ) * u ^ (3 : ℕ)) := by
  have hC10 : (0 : ℝ) < C ^ (10 : ℕ) := pow_pos hC 10
  have hkey : C ^ (10 : ℕ) * gamma ≤ cs ^ (10 : ℕ) := by
    have h := mul_le_mul_of_nonneg_left hreg hC10.le
    rw [inv_pow, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hC10), one_mul] at h
    exact h
  have hcs6 : cs ^ (6 : ℕ) ≤ 12 := by
    calc cs ^ (6 : ℕ) ≤ (3 / 2 : ℝ) ^ (6 : ℕ) := pow_le_pow_left₀ hcs.le hcs32 6
      _ ≤ 12 := by norm_num
  have hcs4 : cs ^ (4 : ℕ) ≤ 6 := by
    calc cs ^ (4 : ℕ) ≤ (3 / 2 : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ hcs.le hcs32 4
      _ ≤ 6 := by norm_num
  have hu' : u = cs ^ (2 : ℕ) / (Ccg * C ^ (2 : ℕ) * gamma) := by
    rw [hu]
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · have hval : 12 * Ccg ^ (2 : ℕ) * (gamma * u ^ (2 : ℕ))
        = 12 * cs ^ (4 : ℕ) / (C ^ (4 : ℕ) * gamma) := by
      rw [hu']
      field_simp
    rw [hval, le_div_iff₀ (by positivity)]
    calc C ^ (6 : ℕ) * (C ^ (4 : ℕ) * gamma) = C ^ (10 : ℕ) * gamma := by ring
      _ ≤ cs ^ (10 : ℕ) := hkey
      _ = cs ^ (4 : ℕ) * cs ^ (6 : ℕ) := by ring
      _ ≤ cs ^ (4 : ℕ) * 12 := mul_le_mul_of_nonneg_left hcs6 (pow_nonneg hcs.le 4)
      _ = 12 * cs ^ (4 : ℕ) := by ring
  · have hval : 12 * Ccg ^ (7 : ℕ) * (gamma ^ (5 : ℕ) * u ^ (7 : ℕ))
        = 12 * cs ^ (14 : ℕ) / (C ^ (14 : ℕ) * gamma ^ (2 : ℕ)) := by
      rw [hu']
      field_simp
    rw [hval, le_div_iff₀ (by positivity)]
    have hsq : (C ^ (10 : ℕ) * gamma) ^ (2 : ℕ) ≤ (cs ^ (10 : ℕ)) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hkey 2
    calc C ^ (6 : ℕ) * (C ^ (14 : ℕ) * gamma ^ (2 : ℕ)) = (C ^ (10 : ℕ) * gamma) ^ (2 : ℕ) := by
          ring
      _ ≤ (cs ^ (10 : ℕ)) ^ (2 : ℕ) := hsq
      _ = cs ^ (14 : ℕ) * cs ^ (6 : ℕ) := by ring
      _ ≤ cs ^ (14 : ℕ) * 12 := mul_le_mul_of_nonneg_left hcs6 (pow_nonneg hcs.le 14)
      _ = 12 * cs ^ (14 : ℕ) := by ring
  · have hval : 6 * Ccg ^ (3 : ℕ) * (gamma ^ (2 : ℕ) * u ^ (3 : ℕ))
        = 6 * cs ^ (6 : ℕ) / (C ^ (6 : ℕ) * gamma) := by
      rw [hu']
      field_simp
    rw [hval, le_div_iff₀ (by positivity)]
    calc C ^ (4 : ℕ) * (C ^ (6 : ℕ) * gamma) = C ^ (10 : ℕ) * gamma := by ring
      _ ≤ cs ^ (10 : ℕ) := hkey
      _ = cs ^ (6 : ℕ) * cs ^ (4 : ℕ) := by ring
      _ ≤ cs ^ (6 : ℕ) * 6 := mul_le_mul_of_nonneg_left hcs4 (pow_nonneg hcs.le 6)
      _ = 6 * cs ^ (6 : ℕ) := by ring

/-! ## 5. The threshold identification -/

/-- **The Appendix-D threshold sits below `D^{-1}`.**  The manuscript's threshold
identification: `C^{1/p} ≤ 1 + C` and `θ^{-1/p} ≤ θ^{-1}` for `p ≥ 1` and
`θ ∈ (0,1]`, so the whole level is controlled by the single inequality
`9 D (1 + C_⋆) ≤ s' θ`. -/
theorem threshold_le_inv {sprime theta p D : ℝ}
    (hs : 0 < sprime) (ht0 : 0 < theta) (ht1 : theta ≤ 1) (hp : 1 ≤ p) (hD : 0 < D)
    (hkey : 9 * D * (1 + Cstar) ≤ sprime * theta) :
    9 * sprime⁻¹ * Cstar ^ (1 / p) * theta ^ (-1 / p) ≤ D⁻¹ := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hpinv0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hpinv1 : 1 / p ≤ 1 := by
    rw [div_le_one hp0]
    exact hp
  have hCs : Cstar ^ (1 / p) ≤ 1 + Cstar :=
    rpow_le_one_add Cstar_pos.le hpinv0 hpinv1
  have hth : theta ^ (-1 / p) ≤ theta⁻¹ := by
    have hexp : (-1 : ℝ) ≤ -1 / p := by
      rw [neg_div, neg_le_neg_iff]
      exact hpinv1
    have h := Real.rpow_le_rpow_of_exponent_ge ht0 ht1 hexp
    rwa [Real.rpow_neg_one] at h
  have h1 : (0 : ℝ) ≤ 9 * sprime⁻¹ := by positivity
  have h2 : (0 : ℝ) ≤ 9 * sprime⁻¹ * (1 + Cstar) :=
    mul_nonneg h1 (by linarith only [Cstar_pos])
  have hchain : 9 * sprime⁻¹ * Cstar ^ (1 / p) * theta ^ (-1 / p)
      ≤ 9 * sprime⁻¹ * (1 + Cstar) * theta⁻¹ := by
    calc 9 * sprime⁻¹ * Cstar ^ (1 / p) * theta ^ (-1 / p)
        ≤ 9 * sprime⁻¹ * (1 + Cstar) * theta ^ (-1 / p) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCs h1)
            (Real.rpow_nonneg ht0.le _)
      _ ≤ 9 * sprime⁻¹ * (1 + Cstar) * theta⁻¹ := mul_le_mul_of_nonneg_left hth h2
  refine hchain.trans ?_
  rw [show D⁻¹ = 1 / D from (one_div D).symm, le_div_iff₀ hD]
  have hst : (0 : ℝ) < sprime * theta := mul_pos hs ht0
  rw [show 9 * sprime⁻¹ * (1 + Cstar) * theta⁻¹ * D = 9 * D * (1 + Cstar) / (sprime * theta) by
    field_simp]
  rw [div_le_one hst]
  exact hkey

/-! ## 6. The dependence range -/

theorem exists_dependence_range (d : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧
      3 + 2 * (3 : ℝ) ^ (1 - (2 : ℤ)) * Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (r : ℕ) := by
  obtain ⟨r0, hr0⟩ := pow_unbounded_of_one_lt
    (3 + 2 * (3 : ℝ) ^ (1 - (2 : ℤ)) * Real.sqrt (d : ℝ)) (by norm_num : (1 : ℝ) < 3)
  refine ⟨max r0 1, le_max_right _ _, hr0.le.trans ?_⟩
  exact pow_le_pow_right₀ (by norm_num) (le_max_left _ _)


end

end Algsuperdiff.Section4.Provider.Proportion
