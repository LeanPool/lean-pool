/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCurvedGeometry
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Derivatives of the normal phase

Explicit derivatives of the normal Carleman phase supply polynomial
bounds for the smooth transition cutoff.
-/

public section

open Filter
open scoped Topology

noncomputable section

namespace ESS

/-- The first height derivative of the normal phase. -/
theorem buShortF_deriv_height
    {y s : ℝ} (hy : 0 < y) :
    deriv (fun r : ℝ => buShortF r s) y =
      (3 / 2 : ℝ) * (1 - s) * y ^ (1 / 2 : ℝ) *
        s ^ (-(3 / 4 : ℝ)) := by
  have hp : HasDerivAt (fun r : ℝ => r ^ (3 / 2 : ℝ))
      ((3 / 2 : ℝ) * y ^ (1 / 2 : ℝ)) y := by
    convert Real.hasDerivAt_rpow_const (p := (3 / 2 : ℝ))
      (Or.inl hy.ne') using 1; norm_num
  have h := hp.const_mul ((1 - s) * s ^ (-(3 / 4 : ℝ)))
  have hfun : (fun r : ℝ => buShortF r s) =
      (fun r => ((1 - s) * s ^ (-(3 / 4 : ℝ))) * r ^ (3 / 2 : ℝ)) := by
    funext r
    dsimp [buShortF]
    ring
  rw [hfun]
  rw [h.deriv]
  ring

/-- The second height derivative of the normal phase. -/
theorem buShortF_deriv_height_twice
    {y s : ℝ} (hy : 0 < y) :
    deriv (fun r : ℝ =>
      deriv (fun q : ℝ => buShortF q s) r) y =
      (3 / 4 : ℝ) * (1 - s) * y ^ (-(1 / 2 : ℝ)) *
        s ^ (-(3 / 4 : ℝ)) := by
  have hfun :
      (fun r : ℝ => deriv (fun q : ℝ => buShortF q s) r) =ᶠ[𝓝 y]
      (fun r => (3 / 2 : ℝ) * (1 - s) *
        r ^ (1 / 2 : ℝ) * s ^ (-(3 / 4 : ℝ))) := by
    filter_upwards [Ioi_mem_nhds hy] with r hr
    exact buShortF_deriv_height hr
  rw [hfun.deriv_eq]
  have hp : HasDerivAt (fun r : ℝ => r ^ (1 / 2 : ℝ))
      ((1 / 2 : ℝ) * y ^ (-(1 / 2 : ℝ))) y := by
    convert Real.hasDerivAt_rpow_const (p := (1 / 2 : ℝ))
      (Or.inl hy.ne') using 1; norm_num
  have h := hp.const_mul ((3 / 2 : ℝ) * (1 - s) * s ^ (-(3 / 4 : ℝ)))
  have hfun' : (fun r : ℝ =>
      (3 / 2 : ℝ) * (1 - s) * r ^ (1 / 2 : ℝ) *
        s ^ (-(3 / 4 : ℝ))) =
      (fun r => ((3 / 2 : ℝ) * (1 - s) * s ^ (-(3 / 4 : ℝ))) *
        r ^ (1 / 2 : ℝ)) := by funext r; ring
  rw [hfun', h.deriv]
  ring

/-- The time derivative of the normal phase. -/
theorem buShortF_deriv_time
    {y s : ℝ} (hs : 0 < s) :
    deriv (fun t : ℝ => buShortF y t) s =
      -(y ^ (3 / 2 : ℝ) * s ^ (-(3 / 4 : ℝ))) -
        (3 / 4 : ℝ) * (1 - s) * y ^ (3 / 2 : ℝ) *
          s ^ (-(7 / 4 : ℝ)) := by
  have hp : HasDerivAt (fun t : ℝ => t ^ (-(3 / 4 : ℝ)))
      (-(3 / 4 : ℝ) * s ^ (-(7 / 4 : ℝ))) s := by
    convert Real.hasDerivAt_rpow_const (p := -(3 / 4 : ℝ))
      (Or.inl hs.ne') using 1; norm_num
  have hlin : HasDerivAt (fun t : ℝ => 1 - t) (-1) s := by
    convert (hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s) using 1
    · funext t
      rfl
    · norm_num
  have hprod := hlin.mul (hp.const_mul (y ^ (3 / 2 : ℝ)))
  have hfun : (fun t : ℝ => buShortF y t) =
      (fun t => (1 - t) *
        (y ^ (3 / 2 : ℝ) * t ^ (-(3 / 4 : ℝ)))) := by
    funext t
    dsimp [buShortF]
    ring
  rw [hfun]
  convert hprod.deriv using 1
  ring

/-- On the active time interval, every power between `s⁻²` and one is
bounded by four. -/
theorem buShort_time_rpow_le_four
    {s p : ℝ} (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1)
    (hp : -(2 : ℝ) ≤ p) :
    s ^ p ≤ 4 := by
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hpow : s ^ p ≤ s ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hs0 hs1 hp
  have hinv : s⁻¹ ≤ 2 := by
    rw [← one_div]
    apply (div_le_iff₀ hs0).2
    linarith only [hs]
  have hinv0 : 0 ≤ s⁻¹ := inv_nonneg.mpr hs0.le
  have hsq : (s⁻¹) ^ 2 ≤ (2 : ℝ) ^ 2 := by
    exact (sq_le_sq₀ hinv0 (by norm_num)).2 hinv
  have hpowEq : s ^ (-(2 : ℝ)) = (s⁻¹) ^ 2 := by
    rw [Real.rpow_neg hs0.le, inv_pow]
    norm_num
  rw [hpowEq] at hpow
  exact hpow.trans (by nlinarith only [hsq])

/-- Any height power of exponent at most two is bounded by the square
above height one. -/
theorem buShort_height_rpow_le_sq
    {y p : ℝ} (hy : 1 ≤ y) (hp : p ≤ 2) :
    y ^ p ≤ y ^ 2 := by
  have h := Real.rpow_le_rpow_of_exponent_le hy hp
  simpa [Real.rpow_natCast] using h

/-- The first height derivative has square-root height growth on the
active half-space strip. -/
theorem buShortF_deriv_height_bound
    {y s : ℝ} (hy : 1 ≤ y) (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1) :
    |deriv (fun r : ℝ => buShortF r s) y| ≤
      6 * y ^ (1 / 2 : ℝ) := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have htime := buShort_time_rpow_le_four hs hs1
    (show -(2 : ℝ) ≤ -(3 / 4 : ℝ) by norm_num)
  have htime0 : 0 ≤ s ^ (-(3 / 4 : ℝ)) := by positivity
  have hheight0 : 0 ≤ y ^ (1 / 2 : ℝ) := by positivity
  have hfactor0 : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  have hfactor1 : 1 - s ≤ 1 := by linarith only [hs]
  rw [buShortF_deriv_height hy0,
    abs_of_nonneg (by positivity :
      0 ≤ (3 / 2 : ℝ) * (1 - s) * y ^ (1 / 2 : ℝ) *
        s ^ (-(3 / 4 : ℝ)))]
  calc
    (3 / 2 : ℝ) * (1 - s) * y ^ (1 / 2 : ℝ) *
        s ^ (-(3 / 4 : ℝ)) ≤
      (3 / 2 : ℝ) * 1 * y ^ (1 / 2 : ℝ) * 4 := by
        gcongr
    _ = 6 * y ^ (1 / 2 : ℝ) := by ring

/-- The second height derivative decays as the inverse square root of
height on the active half-space strip. -/
theorem buShortF_deriv_height_twice_bound
    {y s : ℝ} (hy : 1 ≤ y) (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1) :
    |deriv (fun r : ℝ =>
      deriv (fun q : ℝ => buShortF q s) r) y| ≤
      3 * y ^ (-(1 / 2 : ℝ)) := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have htime := buShort_time_rpow_le_four hs hs1
    (show -(2 : ℝ) ≤ -(3 / 4 : ℝ) by norm_num)
  have htime0 : 0 ≤ s ^ (-(3 / 4 : ℝ)) := by positivity
  have hheight0 : 0 ≤ y ^ (-(1 / 2 : ℝ)) := by positivity
  have hfactor0 : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  have hfactor1 : 1 - s ≤ 1 := by linarith only [hs]
  rw [buShortF_deriv_height_twice hy0,
    abs_of_nonneg (by positivity :
      0 ≤ (3 / 4 : ℝ) * (1 - s) * y ^ (-(1 / 2 : ℝ)) *
        s ^ (-(3 / 4 : ℝ)))]
  calc
    (3 / 4 : ℝ) * (1 - s) * y ^ (-(1 / 2 : ℝ)) *
        s ^ (-(3 / 4 : ℝ)) ≤
      (3 / 4 : ℝ) * 1 * y ^ (-(1 / 2 : ℝ)) * 4 := by
        gcongr
    _ = 3 * y ^ (-(1 / 2 : ℝ)) := by ring

/-- The time derivative has three-halves power height growth on the
active half-space strip. -/
theorem buShortF_deriv_time_bound
    {y s : ℝ} (hy : 1 ≤ y) (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1) :
    |deriv (fun t : ℝ => buShortF y t) s| ≤
      7 * y ^ (3 / 2 : ℝ) := by
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have htime₁ := buShort_time_rpow_le_four hs hs1
    (show -(2 : ℝ) ≤ -(3 / 4 : ℝ) by norm_num)
  have htime₂ := buShort_time_rpow_le_four hs hs1
    (show -(2 : ℝ) ≤ -(7 / 4 : ℝ) by norm_num)
  have hfactor0 : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  have hfactor1 : 1 - s ≤ 1 := by linarith only [hs]
  let A := y ^ (3 / 2 : ℝ) * s ^ (-(3 / 4 : ℝ))
  let B := (3 / 4 : ℝ) * (1 - s) * y ^ (3 / 2 : ℝ) *
    s ^ (-(7 / 4 : ℝ))
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hA : A ≤ 4 * y ^ (3 / 2 : ℝ) := by
    dsimp [A]
    calc
      y ^ (3 / 2 : ℝ) * s ^ (-(3 / 4 : ℝ)) ≤
          y ^ (3 / 2 : ℝ) * 4 := by
        gcongr
      _ = 4 * y ^ (3 / 2 : ℝ) := by ring
  have hB : B ≤ 3 * y ^ (3 / 2 : ℝ) := by
    dsimp [B]
    calc
      (3 / 4 : ℝ) * (1 - s) * y ^ (3 / 2 : ℝ) *
          s ^ (-(7 / 4 : ℝ)) ≤
        (3 / 4 : ℝ) * 1 * y ^ (3 / 2 : ℝ) * 4 := by
          gcongr
      _ = 3 * y ^ (3 / 2 : ℝ) := by ring
  rw [buShortF_deriv_time hs0]
  change |-A - B| ≤ 7 * y ^ (3 / 2 : ℝ)
  have habs : |-A - B| = A + B := by
    rw [show -A - B = -(A + B) by ring, abs_neg,
      abs_of_nonneg (add_nonneg hA0 hB0)]
  rw [habs]
  linarith only [hA, hB]

end ESS
