/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.ClosedBallVolumeRatio

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.GenerationSelection

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# the large-scale C¹ slope approximation clause (b2), third step: the generation selection, log-free

What remains for `ExactRootGaugeTerminal` is to match the terminal's
continuous radii `r ∈ Icc rStart R` to the cube row's generations
`q ∈ Finset.Icc n m`, with `Quenched.triadicCeilingIndex x ≤ n` and `n + 2 ≤ m`.

This is bookkeeping, but carrying it out uncovers one structural fact worth
recording, and it is not the one the rounded template suggests:

* the case split is on **`r` against `R / (108 √d)`**, not on `R` against
  `rStart`.  Above that threshold the canonical outer cube of `r` overshoots the
  inner cube of `R` — `3 ^ q(r)` is only `< 12 r`, while `3 ^ m` is only
  `> R / (3 √d)` — so the cube row does not apply there, **at any `R`**.  That
  band is exactly what the near-terminal branch must cover, and
  `r / R > 1 / (108 √d)` is what makes that branch law-free;
* the row's `n + 2 ≤ m` is then automatic on the far branch, because
  `3 ^ m ≥ 36 · rStart > 3 ^ (n + 1)`.

Everything below is comparison of triadic powers: **no logarithm monotonicity,
no measure theory, and no estimate.**  `outerTriadicGeneration` is used only
through its two scale bounds.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-! ## Comparing triadic powers -/

theorem three_zpow_le_of_le {m n : ℤ} (h : m ≤ n) :
    (3 : ℝ) ^ m ≤ (3 : ℝ) ^ n :=
  zpow_le_zpow_right₀ (by norm_num) h

theorem lt_of_three_zpow_lt {m n : ℤ} (h : (3 : ℝ) ^ m < (3 : ℝ) ^ n) : m < n := by
  by_contra hc
  push Not at hc
  exact absurd h (not_lt.mpr (three_zpow_le_of_le hc))

theorem three_zpow_succ (m : ℤ) :
    (3 : ℝ) ^ (m + 1) = 3 * (3 : ℝ) ^ m := by
  rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
  ring

/-! ## The inner generation: the largest triadic scale below `R` -/

/-- The largest triadic generation whose scale does not exceed `R`. -/
@[expose]
def innerTriadicGeneration (R : ℝ) (_hR : 0 < R) : ℤ := ⌊Real.logb 3 R⌋

theorem innerTriadicGeneration_scale_le {R : ℝ} (hR : 0 < R) :
    (3 : ℝ) ^ innerTriadicGeneration R hR ≤ R := by
  have hfloor : ((innerTriadicGeneration R hR : ℤ) : ℝ) ≤ Real.logb 3 R := by
    rw [innerTriadicGeneration]
    exact Int.floor_le _
  have h1 : (3 : ℝ) ^ ((innerTriadicGeneration R hR : ℤ) : ℝ) ≤
      (3 : ℝ) ^ (Real.logb 3 R) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hfloor
  rw [Real.rpow_logb (by norm_num) (by norm_num) hR] at h1
  simpa only [Real.rpow_intCast] using h1

theorem lt_three_mul_innerTriadicGeneration_scale {R : ℝ} (hR : 0 < R) :
    R < 3 * (3 : ℝ) ^ innerTriadicGeneration R hR := by
  have hfloor : Real.logb 3 R < ((innerTriadicGeneration R hR : ℤ) : ℝ) + 1 := by
    rw [innerTriadicGeneration]
    exact Int.lt_floor_add_one _
  have h1 : (3 : ℝ) ^ (Real.logb 3 R) <
      (3 : ℝ) ^ (((innerTriadicGeneration R hR : ℤ) : ℝ) + 1) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hfloor
  rw [Real.rpow_logb (by norm_num) (by norm_num) hR,
    Real.rpow_add (by norm_num), Real.rpow_one, Real.rpow_intCast] at h1
  linarith only [h1]

/-! ## The far branch: the outer generation of `r` lands in `Icc n m` -/

/-- **The outer generation is bounded by a given inner one.**  If
`12 r ≤ 3 ^ m` then the canonical cube enclosing the ball of radius `2 r` sits
at a generation at most `m`. -/
theorem outerTriadicGeneration_le_of_twelve_mul_le {r : ℝ} (hr : 0 < r) {m : ℤ}
    (h : 12 * r ≤ (3 : ℝ) ^ m) :
    outerTriadicGeneration (2 * (2 * r)) (by positivity) ≤ m := by
  have hscale := outerTriadicGeneration_scale_lt_three_mul
    (by positivity : (0 : ℝ) < 2 * (2 * r))
  have hlt : (3 : ℝ) ^ outerTriadicGeneration (2 * (2 * r)) (by positivity) <
      (3 : ℝ) ^ m := by
    calc (3 : ℝ) ^ outerTriadicGeneration (2 * (2 * r)) (by positivity)
        < 3 * (2 * (2 * r)) := hscale
      _ = 12 * r := by ring
      _ ≤ (3 : ℝ) ^ m := h
  exact le_of_lt (lt_of_three_zpow_lt hlt)

/-- **The outer generation is monotone in the radius, log-free.**  The proof
compares scales: `3 ^ n < 12 · rStart ≤ 12 · r = 3 · (4 r) ≤ 3 · 3 ^ q`. -/
theorem outerTriadicGeneration_le_outerTriadicGeneration {rStart r : ℝ}
    (hrStart : 0 < rStart) (hr : rStart ≤ r) :
    outerTriadicGeneration (2 * (2 * rStart)) (by positivity) ≤
      outerTriadicGeneration (2 * (2 * r)) (by linarith only [hrStart, hr]) := by
  have hr0 : 0 < r := lt_of_lt_of_le hrStart hr
  have hstart := outerTriadicGeneration_scale_lt_three_mul
    (by positivity : (0 : ℝ) < 2 * (2 * rStart))
  have hbig := le_outerTriadicGeneration_scale
    (by positivity : (0 : ℝ) < 2 * (2 * r))
  have hlt : (3 : ℝ) ^ outerTriadicGeneration (2 * (2 * rStart)) (by positivity) <
      (3 : ℝ) ^ (outerTriadicGeneration (2 * (2 * r)) (by positivity) + 1) := by
    rw [three_zpow_succ]
    calc (3 : ℝ) ^ outerTriadicGeneration (2 * (2 * rStart)) (by positivity)
        < 3 * (2 * (2 * rStart)) := hstart
      _ ≤ 3 * (2 * (2 * r)) := by linarith only [hr]
      _ ≤ 3 * (3 : ℝ) ^ outerTriadicGeneration (2 * (2 * r)) (by positivity) := by
          linarith only [hbig]
  have := lt_of_three_zpow_lt hlt
  omega

/-- **The row's gap `n + 2 ≤ m` is automatic on the far branch.**  If
`36 · rStart ≤ 3 ^ m` then the canonical outer generation of `rStart` is at
least two below `m`. -/
theorem outerTriadicGeneration_add_two_le_of_thirtysix_mul_le {rStart : ℝ}
    (hrStart : 0 < rStart) {m : ℤ} (h : 36 * rStart ≤ (3 : ℝ) ^ m) :
    outerTriadicGeneration (2 * (2 * rStart)) (by positivity) + 2 ≤ m := by
  have hstart := outerTriadicGeneration_scale_lt_three_mul
    (by positivity : (0 : ℝ) < 2 * (2 * rStart))
  have hlt : (3 : ℝ) ^
      (outerTriadicGeneration (2 * (2 * rStart)) (by positivity) + 1) <
      (3 : ℝ) ^ m := by
    rw [three_zpow_succ]
    calc 3 * (3 : ℝ) ^ outerTriadicGeneration (2 * (2 * rStart)) (by positivity)
        < 3 * (3 * (2 * (2 * rStart))) := by linarith only [hstart]
      _ = 36 * rStart := by ring
      _ ≤ (3 : ℝ) ^ m := h
  have := lt_of_three_zpow_lt hlt
  omega

/-! ## The threshold, and the two bounds the far branch needs -/

/-- **The far/near threshold, discharged.**  With `m` an inner generation for
`R` in the sense `R ≤ 3 ^ m * (3 √d)`, every radius below `R / (108 √d)` has its
canonical outer cube at a generation in `Icc n m`, and the gap `n + 2 ≤ m` holds
as soon as `rStart` is below that threshold too. -/
theorem farBranch_bounds [NeZero d] {rStart r R : ℝ} {m : ℤ}
    (hrStart : 0 < rStart) (hr : rStart ≤ r)
    (hmR : R ≤ (3 : ℝ) ^ m * (3 * Real.sqrt d))
    (hthr : 108 * (Real.sqrt d * r) ≤ R)
    (hstart : 108 * (Real.sqrt d * rStart) ≤ R) :
    outerTriadicGeneration (2 * (2 * rStart)) (by positivity) ≤
        outerTriadicGeneration (2 * (2 * r)) (by linarith only [hrStart, hr]) ∧
      outerTriadicGeneration (2 * (2 * r)) (by linarith only [hrStart, hr]) ≤ m ∧
      outerTriadicGeneration (2 * (2 * rStart)) (by positivity) + 2 ≤ m := by
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hsq : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have hpos : (0 : ℝ) < 3 * Real.sqrt d := by positivity
  have hr0 : 0 < r := lt_of_lt_of_le hrStart hr
  have key : ∀ t : ℝ, 0 < t → 108 * (Real.sqrt d * t) ≤ R →
      36 * t ≤ (3 : ℝ) ^ m := by
    intro t ht hle
    have hA : 36 * t * (3 * Real.sqrt d) ≤ (3 : ℝ) ^ m * (3 * Real.sqrt d) := by
      calc 36 * t * (3 * Real.sqrt d) = 108 * (Real.sqrt d * t) := by ring
        _ ≤ R := hle
        _ ≤ (3 : ℝ) ^ m * (3 * Real.sqrt d) := hmR
    exact le_of_mul_le_mul_right hA hpos
  refine ⟨outerTriadicGeneration_le_outerTriadicGeneration hrStart hr, ?_, ?_⟩
  · refine outerTriadicGeneration_le_of_twelve_mul_le hr0 ?_
    have h36 := key r hr0 hthr
    linarith only [h36, hr0]
  · exact outerTriadicGeneration_add_two_le_of_thirtysix_mul_le hrStart
      (key rStart hrStart hstart)

end

end CorrectorComposition
end HighContrast
end HCPolySupport
