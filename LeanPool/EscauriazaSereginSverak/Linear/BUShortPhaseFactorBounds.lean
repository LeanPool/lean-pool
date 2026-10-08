/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortPhaseFactor

/-!
# Growth bounds for the phase transition factor

The derivatives of the normal phase transition have polynomial growth
on the active half-space strip.
-/

public section


open CKN

noncomputable section

namespace ESS

private theorem buShort_sqrt_le_one_add {y : ℝ} (hy : 1 ≤ y) :
    y ^ (1 / 2 : ℝ) ≤ 1 + y := by
  have h := Real.rpow_le_rpow_of_exponent_le hy
    (show (1 / 2 : ℝ) ≤ 1 by norm_num)
  have h' : y ^ (1 / 2 : ℝ) ≤ y := by simpa using h
  linarith only [h']

private theorem buShort_inv_sqrt_le_one_add {y : ℝ} (hy : 1 ≤ y) :
    y ^ (-(1 / 2 : ℝ)) ≤ 1 + y := by
  have h := Real.rpow_le_one_of_one_le_of_nonpos hy
    (show -(1 / 2 : ℝ) ≤ 0 by norm_num)
  linarith only [h, hy]

private theorem buShort_three_half_le_one_add_sq {y : ℝ} (hy : 1 ≤ y) :
    y ^ (3 / 2 : ℝ) ≤ (1 + y) ^ 2 := by
  have h := buShort_height_rpow_le_sq hy
    (show (3 / 2 : ℝ) ≤ 2 by norm_num)
  nlinarith only [h, hy]

/-- The phase transition has first height derivative growing at most
linearly in height on the active strip. -/
theorem buShortPhaseFactor_deriv_height_bound
    {scale y s : ℝ} (hscale : 0 < scale)
    (hy : 2 < y) (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1) :
    |deriv (fun r : ℝ => buShortPhaseFactor scale r s) y| ≤
      (48 * (12 / buShortB scale)) * (1 + y) := by
  let K := 12 / buShortB scale
  have hK : 0 ≤ K := (div_pos (by norm_num) (buShortB_pos hscale)).le
  have hF := buShortFExt_deriv_height_bound hy hs hs1
  rw [buShortPhaseFactor_deriv_height, abs_mul, abs_mul,
    abs_of_nonneg hK]
  have hp := smoothTransitionProfile.abs_deriv_le_eight
    (buShortPhaseArgument scale y s)
  have hyPow : 0 ≤ y ^ (1 / 2 : ℝ) := by positivity
  have hyUpper := buShort_sqrt_le_one_add (by linarith only [hy])
  have hprod :
      |deriv smoothTransitionProfile (buShortPhaseArgument scale y s)| *
        (K * |deriv (fun r : ℝ => buShortFExt r s) y|) ≤
      8 * (K * (6 * y ^ (1 / 2 : ℝ))) := by
    gcongr
  calc
    _ ≤ 8 * (K * (6 * y ^ (1 / 2 : ℝ))) := hprod
    _ = (48 * K) * y ^ (1 / 2 : ℝ) := by ring
    _ ≤ (48 * K) * (1 + y) := by gcongr

/-- The phase transition has time derivative with quadratic height
growth on the active strip. -/
theorem buShortPhaseFactor_deriv_time_bound
    {scale y s : ℝ} (hscale : 0 < scale)
    (hy : 2 < y) (hs : 1 / 2 < s) (hs1 : s ≤ 1) :
    |deriv (fun t : ℝ => buShortPhaseFactor scale y t) s| ≤
      (56 * (12 / buShortB scale)) * (1 + y) ^ 2 := by
  let K := 12 / buShortB scale
  have hK : 0 ≤ K := (div_pos (by norm_num) (buShortB_pos hscale)).le
  have hF := buShortFExt_deriv_time_bound hy.le hs hs1
  rw [buShortPhaseFactor_deriv_time, abs_mul, abs_mul,
    abs_of_nonneg hK]
  have hp := smoothTransitionProfile.abs_deriv_le_eight
    (buShortPhaseArgument scale y s)
  have hyUpper := buShort_three_half_le_one_add_sq (by linarith only [hy])
  have hprod :
      |deriv smoothTransitionProfile (buShortPhaseArgument scale y s)| *
        (K * |deriv (fun t : ℝ => buShortFExt y t) s|) ≤
      8 * (K * (7 * y ^ (3 / 2 : ℝ))) := by
    gcongr
  calc
    _ ≤ 8 * (K * (7 * y ^ (3 / 2 : ℝ))) := hprod
    _ = (56 * K) * y ^ (3 / 2 : ℝ) := by ring
    _ ≤ (56 * K) * (1 + y) ^ 2 := by gcongr

/-- The second height derivative of the phase transition grows at most
quadratically in height on the active strip. -/
theorem buShortPhaseFactor_deriv_height_twice_bound
    {scale y s C₂ : ℝ} (hscale : 0 < scale)
    (hy : 2 < y) (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1)
    (hC₂ : 0 ≤ C₂)
    (hprofile : ∀ x : ℝ,
      |deriv (deriv smoothTransitionProfile) x| ≤ C₂) :
    |deriv (fun r : ℝ =>
      deriv (fun q : ℝ => buShortPhaseFactor scale q s) r) y| ≤
      (36 * C₂ * (12 / buShortB scale) ^ 2 +
        24 * (12 / buShortB scale)) * (1 + y) ^ 2 := by
  let K := 12 / buShortB scale
  let P := buShortPhaseArgument scale y s
  let D := deriv (fun r : ℝ => buShortFExt r s) y
  let DD := deriv (fun r : ℝ =>
    deriv (fun q : ℝ => buShortFExt q s) r) y
  have hK : 0 ≤ K := (div_pos (by norm_num) (buShortB_pos hscale)).le
  have hD := buShortFExt_deriv_height_bound hy hs hs1
  have hDD := buShortFExt_deriv_height_twice_bound hy hs hs1
  have hpow : 0 ≤ 1 + y := by linarith only [hy]
  have hsq : 1 + y ≤ (1 + y) ^ 2 := by nlinarith only [hy]
  have hroot := buShort_sqrt_le_one_add (by linarith only [hy])
  have hinv := buShort_inv_sqrt_le_one_add (by linarith only [hy])
  have hD' : |D| ≤ 6 * (1 + y) := by
    have hroot0 : 0 ≤ y ^ (1 / 2 : ℝ) := by positivity
    exact hD.trans (by gcongr)
  have hDD' : |DD| ≤ 3 * (1 + y) :=
    hDD.trans (by gcongr)
  have hterm1 :
      |deriv (deriv smoothTransitionProfile) P * (K * D) ^ 2| ≤
        (36 * C₂ * K ^ 2) * (1 + y) ^ 2 := by
    rw [abs_mul, abs_pow, abs_mul, abs_of_nonneg hK]
    calc
      |deriv (deriv smoothTransitionProfile) P| * (K * |D|) ^ 2 ≤
          C₂ * (K * (6 * (1 + y))) ^ 2 := by
            gcongr
            exact hprofile P
      _ = (36 * C₂ * K ^ 2) * (1 + y) ^ 2 := by ring
  have hterm2 :
      |deriv smoothTransitionProfile P * (K * DD)| ≤
        (24 * K) * (1 + y) ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hK]
    calc
      |deriv smoothTransitionProfile P| * (K * |DD|) ≤
          8 * (K * (3 * (1 + y))) := by
            gcongr
            exact smoothTransitionProfile.abs_deriv_le_eight P
      _ = (24 * K) * (1 + y) := by ring
      _ ≤ (24 * K) * (1 + y) ^ 2 := by gcongr
  rw [buShortPhaseFactor_deriv_height_twice hy hs]
  have htri := abs_add_le
    (deriv (deriv smoothTransitionProfile) P * (K * D) ^ 2)
    (deriv smoothTransitionProfile P * (K * DD))
  change |deriv (deriv smoothTransitionProfile) P * (K * D) ^ 2 +
    deriv smoothTransitionProfile P * (K * DD)| ≤
    (36 * C₂ * K ^ 2 + 24 * K) * (1 + y) ^ 2
  calc
    _ ≤ |deriv (deriv smoothTransitionProfile) P * (K * D) ^ 2| +
        |deriv smoothTransitionProfile P * (K * DD)| := htri
    _ ≤ (36 * C₂ * K ^ 2) * (1 + y) ^ 2 +
        (24 * K) * (1 + y) ^ 2 := add_le_add hterm1 hterm2
    _ = _ := by ring

end ESS
