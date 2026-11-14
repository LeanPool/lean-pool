/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.GaussianConvexity.GaussianComparison
public import LeanPool.EhrhardGaussian.GaussianConvexity.StrictCumulant
public import LeanPool.EhrhardGaussian.GaussianConvexity.ConvexityAcrossZero
public import LeanPool.EhrhardGaussian.GaussianConvexity.Derivative
public import LeanPool.EhrhardGaussian.EhrhardType.Moments
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The finite-domain log-MGF comparison follows from strict-CDF crossing geometry, two matching
Gaussian moments and continuity at zero. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace EhrhardGaussian.GaussianConvexity

/-- Two strictly increasing values determine a unique positive variance and an affine Gaussian
chord. -/
theorem exists_matching_gaussian_chord {x z A B : ℝ} (hxz : x < z) (hAB : A < B) :
    ∃ m σ : ℝ, 0 < σ ∧ m + σ ^ 2 * x / 2 = A ∧ m + σ ^ 2 * z / 2 = B := by
  let v := 2 * (B - A) / (z - x)
  have hv : 0 < v := div_pos (mul_pos (by norm_num) (sub_pos.mpr hAB)) (sub_pos.mpr hxz)
  refine ⟨A - v * x / 2, Real.sqrt v, Real.sqrt_pos.mpr hv, ?_, ?_⟩
  · rw [Real.sq_sqrt hv.le]
    ring
  · rw [Real.sq_sqrt hv.le]
    have heq : v * (z - x) = 2 * (B - A) := div_mul_cancel₀ _ (sub_ne_zero.mpr hxz.ne')
    nlinarith only [heq]

/-- The affine Gaussian graph equals its barycentric chord at every intermediate point. -/
theorem matching_gaussian_chord_eq (m σ x y z : ℝ) (hxz : x < z) :
    ((z - y) * (m + σ ^ 2 * x / 2) + (y - x) * (m + σ ^ 2 * z / 2)) / (z - x) =
      m + σ ^ 2 * y / 2 := by
  apply (div_eq_iff (sub_ne_zero.mpr hxz.ne')).mpr
  ring

/-- The normalized log-MGF is convex on its finite moment domain, including parameter zero. -/
theorem convexOn_logMGFRatio_of_isEhrhardType_of_positive_moment {μ : Measure ℝ}
    (hμ : IsEhrhardType μ) {r : ℝ} (hr : 0 < r)
    (hexp : Integrable (fun x => Real.exp (r * x)) μ) :
    ConvexOn ℝ (integrableExpSet id μ) (logMGFRatio μ id) := by
  have := hμ.1
  by_cases hn : ∃ c, μ = Measure.dirac c
  · obtain ⟨c, rfl⟩ := hn
    have hc := convexOn_logMGFRatio_gaussianReal c 0
    rw [gaussianReal_zero_var] at hc
    exact hc.subset (subset_univ _) convex_integrableExpSet
  have h0 := EhrhardType.zero_mem_interior_integrableExpSet_of_positive_moment hμ hr hexp
  apply convexOn_of_nonzero_chords convex_integrableExpSet h0
    (hasDerivAt_logMGFRatio_zero μ id h0).continuousAt
  intro x y z hx hz hxy hyz hx0 hy0 hz0
  have hy : y ∈ integrableExpSet id μ :=
    (convex_iff_ordConnected.mp (convex_integrableExpSet (X := id) (μ := μ))).out hx hz ⟨hxy.le,
      hyz.le⟩
  have hΛ := logMGFRatio_lt_of_nonconstant hn (hxy.trans hyz) hx hz hx0 hz0
  obtain ⟨m, σ, hσ, hmx, hmz⟩ := exists_matching_gaussian_chord (hxy.trans hyz) hΛ
  have hbound := logMGFRatio_le_matching_gaussian hμ hn m hσ hxy hyz hx0 hy0 hz0 hx hy hz
    hmx.symm hmz.symm
  calc
    logMGFRatio μ id y ≤ m + σ ^ 2 * y / 2 := hbound
    _ = ((z - y) * logMGFRatio μ id x + (y - x) * logMGFRatio μ id z) / (z - x) := by
      rw [← hmx, ← hmz]
      exact (matching_gaussian_chord_eq m σ x y z (hxy.trans hyz)).symm

/-- The order-one specialization used by the normalized moment bounds. -/
theorem convexOn_logMGFRatio_of_isEhrhardType {μ : Measure ℝ} (hμ : IsEhrhardType μ)
    (hexp : Integrable (fun x => Real.exp x) μ) :
    ConvexOn ℝ (integrableExpSet id μ) (logMGFRatio μ id) := by
  apply convexOn_logMGFRatio_of_isEhrhardType_of_positive_moment hμ (show (0 : ℝ) < 1 from
    zero_lt_one)
  simpa only [one_mul] using hexp

end EhrhardGaussian.GaussianConvexity
