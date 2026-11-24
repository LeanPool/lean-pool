/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Suzuki cubic cancellation parameter

The sum of cubes of the five Strang coefficients is `4p³ + (1 - 4p)³`.
Its vanishing is an algebraic condition over any commutative ring. Over the
reals it has the unique solution `1 / (4 - 4^(1/3))`.

## Main definitions

* `suzukiCubicCoeff`: the cubic coefficient sum.
* `IsSuzukiCubic`: its vanishing condition.
* `suzukiP`: the canonical real Suzuki parameter.

## Main results

* `isSuzukiCubic_suzukiP`: the canonical parameter satisfies the condition.
* `isSuzukiCubic_iff_eq_suzukiP`: uniqueness over the reals.
* `suzukiP_mem_rational_interval`: the source rational enclosure.
* `suzukiP_mem_tight_rational_interval`: a certified fifteen-decimal enclosure.
-/

@[expose] public noncomputable section

namespace FQFP.BCH

/-- The sum of cubes of the five Strang coefficients. -/
def suzukiCubicCoeff {K : Type*} [CommRing K] (p : K) : K :=
  4 * p ^ 3 + (1 - 4 * p) ^ 3

/-- The five Strang coefficients satisfy the Suzuki cubic cancellation condition. -/
def IsSuzukiCubic {K : Type*} [CommRing K] (p : K) : Prop := suzukiCubicCoeff p = 0

/-- The canonical real Suzuki parameter. -/
def suzukiP : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))

private lemma cube_root_four_cubed : ((4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 4 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

private lemma cube_root_four_lt_two : (4 : ℝ) ^ ((1 : ℝ) / 3) < 2 := by
  apply (Odd.pow_lt_pow (by decide : Odd 3)).mp
  rw [cube_root_four_cubed]
  norm_num

/-- The canonical Suzuki parameter satisfies cubic cancellation. -/
theorem isSuzukiCubic_suzukiP : IsSuzukiCubic suzukiP := by
  have hd : 4 - (4 : ℝ) ^ ((1 : ℝ) / 3) ≠ 0 := by
    linarith only [cube_root_four_lt_two]
  unfold IsSuzukiCubic suzukiCubicCoeff suzukiP
  calc
    _ = (4 - ((4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3) /
        (4 - (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := by
      field_simp
      ring
    _ = 0 := by rw [cube_root_four_cubed, sub_self, zero_div]

/-- The canonical parameter is the unique real solution of cubic cancellation. -/
theorem isSuzukiCubic_iff_eq_suzukiP (p : ℝ) : IsSuzukiCubic p ↔ p = suzukiP := by
  constructor
  · intro hp
    have hc : (1 - 4 * p) ^ 3 = (-((4 : ℝ) ^ ((1 : ℝ) / 3)) * p) ^ 3 := by
      rw [mul_pow, neg_pow, cube_root_four_cubed]
      dsimp [IsSuzukiCubic, suzukiCubicCoeff] at hp
      linarith only [hp]
    have heq := (Odd.pow_injective (by decide : Odd 3)) hc
    unfold suzukiP
    apply (eq_div_iff (by linarith only [cube_root_four_lt_two])).mpr
    linarith only [heq]
  · rintro rfl
    exact isSuzukiCubic_suzukiP

/-- The cubic relation in monic form over the rationals. -/
theorem suzukiP_cubic_relation :
    60 * suzukiP ^ 3 - 48 * suzukiP ^ 2 + 12 * suzukiP - 1 = 0 := by
  have h := isSuzukiCubic_suzukiP
  unfold IsSuzukiCubic suzukiCubicCoeff at h
  nlinarith only [h]

/-- A certified fifteen-decimal interval for the canonical Suzuki parameter. -/
theorem suzukiP_mem_tight_rational_interval :
    (414490771794375 : ℝ) / 10 ^ 15 < suzukiP ∧
      suzukiP < (414490771794376 : ℝ) / 10 ^ 15 := by
  have hd : 0 < 4 - (4 : ℝ) ^ ((1 : ℝ) / 3) := by
    linarith only [cube_root_four_lt_two]
  have hlo : (4 : ℝ) - 10 ^ 15 / 414490771794375 <
      (4 : ℝ) ^ ((1 : ℝ) / 3) := by
    apply (Odd.pow_lt_pow (by decide : Odd 3)).mp
    rw [cube_root_four_cubed]
    norm_num
  have hhi : (4 : ℝ) ^ ((1 : ℝ) / 3) <
      4 - 10 ^ 15 / 414490771794376 := by
    apply (Odd.pow_lt_pow (by decide : Odd 3)).mp
    rw [cube_root_four_cubed]
    norm_num
  constructor
  · rw [suzukiP, lt_div_iff₀ hd]
    linarith only [hlo]
  · rw [suzukiP, div_lt_iff₀ hd]
    linarith only [hhi]

/-- The source rational enclosure of the canonical real Suzuki parameter. -/
theorem suzukiP_mem_rational_interval :
    41449 / 100000 < suzukiP ∧ suzukiP < 41450 / 100000 := by
  obtain ⟨hlo, hhi⟩ := suzukiP_mem_tight_rational_interval
  exact ⟨lt_trans (by norm_num) hlo, lt_trans hhi (by norm_num)⟩

end FQFP.BCH
