/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# TriadicRadii

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Triadic radii and the geometric weight of a triadic Campanato telescope

The cubes of the underlying regularity theory have side `3 ^ j`, so the
Campanato telescope that reads a Hölder modulus out of an oscillation decay
must step by the factor `3`, not by the factor `2` of the textbook dyadic
construction.  This file collects the radius arithmetic of that telescope:
the radii `R 3 ^ (-k)`, the geometric ratio `3 ^ (-α)` they contribute to a
sum of `α`-weighted oscillations, and the sum of the resulting geometric
series.

The exponent `α` is a free real parameter.  Everything below needs only
`0 < α`, and the tail constant is kept in the exact closed form
`(1 - 3 ^ (-α))⁻¹`; the numerical bound `≤ 3` is recorded separately for the
range `1/2 ≤ α`, where it is available, and is never used to define anything.

## Main definitions

* `triadicRadius R k` — the radius `R 3 ^ (-k)`.
* `campanatoRatio α` — the geometric ratio `3 ^ (-α) = (1/3) ^ α`.
* `campanatoTailConstant α` — the sum `(1 - 3 ^ (-α))⁻¹` of the geometric
  series.

## Main results

* `triadicRadius_rpow` — the factorisation
  `(R 3 ^ (-k)) ^ α = R ^ α (3 ^ (-α)) ^ k`.
* `exists_triadicRadius_bracket` — every separation below `R` is bracketed by
  two consecutive radii.
* `tendsto_triadicRadius_zero` — the radii decrease to `0` from above.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Campanato

open Filter Topology

noncomputable section

/-! ## 1. The radii -/

/-- **The triadic radius** `R 3 ^ (-k)`. -/
def triadicRadius (R : ℝ) (k : ℕ) : ℝ := R * (1 / 3 : ℝ) ^ k

@[simp] theorem triadicRadius_zero (R : ℝ) : triadicRadius R 0 = R := by
  simp [triadicRadius]

theorem triadicRadius_pos {R : ℝ} (hR : 0 < R) (k : ℕ) : 0 < triadicRadius R k :=
  mul_pos hR (by positivity)

theorem triadicRadius_succ (R : ℝ) (k : ℕ) :
    triadicRadius R (k + 1) = triadicRadius R k / 3 := by
  rw [triadicRadius, triadicRadius, pow_succ]
  ring

theorem triadicRadius_le {R : ℝ} (hR : 0 ≤ R) (k : ℕ) : triadicRadius R k ≤ R := by
  have hpow : (1 / 3 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  simpa only [triadicRadius, mul_one] using mul_le_mul_of_nonneg_left hpow hR

/-! ## 2. The geometric ratio -/

/-- **The geometric ratio** `3 ^ (-α)` of the `α`-weighted triadic telescope. -/
def campanatoRatio (alpha : ℝ) : ℝ := (1 / 3 : ℝ) ^ alpha

theorem campanatoRatio_lt_one {alpha : ℝ} (halpha : 0 < alpha) :
    campanatoRatio alpha < 1 :=
  Real.rpow_lt_one (by norm_num) (by norm_num) halpha

theorem one_sub_campanatoRatio_pos {alpha : ℝ} (halpha : 0 < alpha) :
    0 < 1 - campanatoRatio alpha :=
  sub_pos.mpr (campanatoRatio_lt_one halpha)

/-- **The factorisation of the `α`-weight along the telescope.** -/
theorem triadicRadius_rpow {R alpha : ℝ} (hR : 0 ≤ R) (k : ℕ) :
    triadicRadius R k ^ alpha = R ^ alpha * campanatoRatio alpha ^ k := by
  rw [triadicRadius, Real.mul_rpow hR (by positivity)]
  congr 1
  rw [campanatoRatio, ← Real.rpow_natCast ((1 / 3 : ℝ) ^ alpha) k,
    ← Real.rpow_natCast (1 / 3 : ℝ) k,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 3),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  congr 1
  ring

/-! ## 3. The geometric tail -/

/-- **The sum of the geometric series** of ratio `3 ^ (-α)`.  It is the only
constant of the telescope that depends on the exponent, and it is kept in
closed form. -/
def campanatoTailConstant (alpha : ℝ) : ℝ := (1 - campanatoRatio alpha)⁻¹

theorem campanatoTailConstant_pos {alpha : ℝ} (halpha : 0 < alpha) :
    0 < campanatoTailConstant alpha :=
  inv_pos.mpr (one_sub_campanatoRatio_pos halpha)

/-- On the exponent range `1/2 ≤ α` the tail constant is below the numerical
value `3`.  Recorded for a consumer that prefers a numeral; the closed form is
what the telescope uses. -/
theorem campanatoTailConstant_le_three {alpha : ℝ} (halpha : (1 / 2 : ℝ) ≤ alpha) :
    campanatoTailConstant alpha ≤ 3 := by
  have hmono : campanatoRatio alpha ≤ (1 / 3 : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) halpha
  have hsq : ((1 / 3 : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = 1 / 3 := by
    rw [← Real.rpow_natCast ((1 / 3 : ℝ) ^ (1 / 2 : ℝ)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 3)]
    norm_num
  have hnonneg : (0 : ℝ) ≤ (1 / 3 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hroot : (1 / 3 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 / 3 := by
    refine (sq_le_sq₀ hnonneg (by norm_num : (0 : ℝ) ≤ 2 / 3)).mp ?_
    rw [hsq]
    norm_num
  have halpha0 : 0 < alpha := lt_of_lt_of_le (by norm_num) halpha
  have hden : (1 : ℝ) / 3 ≤ 1 - campanatoRatio alpha := by
    linarith only [hmono, hroot]
  have hpos : (0 : ℝ) < 1 / 3 := by norm_num
  have h := (inv_le_inv₀ (one_sub_campanatoRatio_pos halpha0) hpos).2 hden
  rw [campanatoTailConstant]
  simpa only [one_div, inv_inv] using h

/-! ## 4. Bracketing and the limit -/

/-- Every separation in `(0, R]` lies between two consecutive triadic radii. -/
theorem exists_triadicRadius_bracket {R s : ℝ} (hR : 0 < R) (hs : 0 < s) (hsR : s ≤ R) :
    ∃ k : ℕ, triadicRadius R (k + 1) < s ∧ s ≤ triadicRadius R k := by
  have hx0 : 0 < s / R := div_pos hs hR
  have hx1 : s / R ≤ 1 := (div_le_one hR).2 hsR
  obtain ⟨k, hklow, hkhigh⟩ := exists_nat_pow_near_of_lt_one
    hx0 hx1 (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num : (1 / 3 : ℝ) < 1)
  refine ⟨k, ?_, ?_⟩
  · have h := (lt_div_iff₀ hR).1 hklow
    simpa only [triadicRadius, mul_comm] using h
  · have h := (div_le_iff₀ hR).1 hkhigh
    simpa only [triadicRadius, mul_comm] using h

/-- The telescope radii tend to `0` through positive values. -/
theorem tendsto_triadicRadius_zero {R : ℝ} (hR : 0 < R) :
    Tendsto (triadicRadius R) atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
  have hfull : Tendsto (triadicRadius R) atTop (nhds (0 : ℝ)) := by
    have h : Tendsto (fun k : ℕ => R * (1 / 3 : ℝ) ^ k) atTop (nhds (R * 0)) :=
      tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one (𝕜 := ℝ) (r := (1 / 3 : ℝ))
          (by norm_num) (by norm_num))
    simpa only [triadicRadius, mul_zero] using! h
  exact tendsto_inf.2
    ⟨hfull, tendsto_principal.2 (Eventually.of_forall fun k => triadicRadius_pos hR k)⟩

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Campanato
