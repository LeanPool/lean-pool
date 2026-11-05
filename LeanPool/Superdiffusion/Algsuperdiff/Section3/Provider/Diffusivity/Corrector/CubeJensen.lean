/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Deterministic.ConstantCoefficientDirichletBesov.Basic

/-!
# CubeJensen

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
Binder descriptions below are an informal inventory only, NOT a source
certification; certification vocabulary is reserved for frozen source-facing
declarations.

# Portable: cube-average Jensen at the fourth and eighth powers

This file contains **generic mathematics only**.  It imports nothing but
Mathlib and `Homogenization.*`, mentions no ABK26 object, and is a candidate
for relocation into CoarseGraining beside the `p = 2` statements it consumes.

## What is here, and what was already upstream

CoarseGraining already proves the scalar `p = 2` normalized cube-average Jensen
inequality, `Homogenization.sq_cubeAverage_le_cubeAverage_sq_of_memLp`:

```
  (cubeAverage Q f)^2 <= cubeAverage Q (f^2)   for f in L^2(normalizedCubeMeasure Q),
```

together with its coordinatewise vector consequence
`vecNormSq_cubeAverageVec_le_sum_cubeAverage_sq_of_memLp`.  What is *not*
upstream, and is supplied here, is the higher-power form needed whenever a
volume-normalized `L^4` quantity has to be compared with a volume-normalized
`L^8` quantity on the same cube:

* `sq_cubeAverage_pow_four_le_cubeAverage_pow_eight_of_memLp` -- the
  volume-normalized `L^4 <= L^8` comparison, in the form
  `(cubeAverage Q (f^4))^2 <= cubeAverage Q (f^8)`.

It is the same convexity fact, the `p = 2` statement applied to `f^4`.  The
membership bookkeeping (`f` in `L^8` implies `f^4` in `L^2` on the normalized
cube, a finite measure) is done once in the private helper below.

## Note on hypotheses

The statement carries exactly the membership its own proof needs and nothing
more, `MemLp f 8`.  The normalized cube measure is finite, so the weaker
memberships used inside are derived, not assumed.

## Main results

* `sq_cubeAverage_pow_four_le_cubeAverage_pow_eight_of_memLp`
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open MeasureTheory
open HCPolySupport
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Membership bookkeeping on the normalized cube -/

private theorem memLp_pow_four_two_of_memLp_eight (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : MemLp f 8 (normalizedCubeMeasure Q)) :
    MemLp (fun x => f x ^ (4 : ℕ)) 2 (normalizedCubeMeasure Q) := by
  have h := (memLp_norm_rpow_iff (μ := normalizedCubeMeasure Q) (f := f)
      (p := (8 : ℝ≥0∞)) (q := (4 : ℝ≥0∞)) hf.aestronglyMeasurable
      (by norm_num) (by norm_num)).2 hf
  have hdiv : (8 : ℝ≥0∞) / 4 = 2 := by
    rw [show (8 : ℝ≥0∞) = 2 * 4 by norm_num]
    rw [mul_div_assoc, ENNReal.div_self (by norm_num) (by norm_num), mul_one]
  rw [hdiv] at h
  have hfun : (fun x => ‖f x‖ ^ ((4 : ℝ≥0∞).toReal)) = fun x => f x ^ (4 : ℕ) := by
    funext x
    rw [show ((4 : ℝ≥0∞).toReal) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, ← abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ f x ^ (4 : ℕ))]
  rwa [hfun] at h

/-! ## The volume-normalized `L^4 <= L^8` comparison -/

/-- **The volume-normalized `L^4 <= L^8` comparison on a triadic cube.**
Equivalently `(avg (f^4))^{1/4} <= (avg (f^8))^{1/8}`: on a normalized (hence
probability) cube measure the `L^4` average never exceeds the `L^8` one. -/
theorem sq_cubeAverage_pow_four_le_cubeAverage_pow_eight_of_memLp (Q : TriadicCube d)
    (f : Vec d → ℝ) (hf : MemLp f 8 (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x => f x ^ (4 : ℕ)) ^ (2 : ℕ) ≤
      cubeAverage Q (fun x => f x ^ (8 : ℕ)) := by
  have hsq : MemLp (fun x => f x ^ (4 : ℕ)) 2 (normalizedCubeMeasure Q) :=
    memLp_pow_four_two_of_memLp_eight Q hf
  have h := sq_cubeAverage_le_cubeAverage_sq_of_memLp Q (fun x => f x ^ (4 : ℕ)) hsq
  refine h.trans (le_of_eq ?_)
  refine congrArg (cubeAverage Q) ?_
  funext x
  ring

end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
