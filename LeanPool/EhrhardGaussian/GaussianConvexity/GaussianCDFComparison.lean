/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.EhrhardType.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Concavity of the Gaussian quantile of the strict distribution function determines the crossing
set with a Gaussian law. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace EhrhardGaussian.GaussianConvexity

/-- An affine standard normal has the expected mean and squared scale as variance. -/
theorem map_standardGaussian_affine (m σ : ℝ) :
    (gaussianReal 0 1).map (fun z => σ * z + m) = gaussianReal m ⟨σ ^ 2, sq_nonneg σ⟩ := by
  have hcomp : (fun z => σ * z + m) = (fun z => z + m) ∘ (fun z => σ * z) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_add_const]
  simp only [mul_zero, mul_one, zero_add]
  congr 1

/-- The strict CDF of a nondegenerate Gaussian, in the normalization used by FMP25. -/
theorem strictCDF_gaussianReal_scale (m : ℝ) {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    (gaussianReal m ⟨σ ^ 2, sq_nonneg σ⟩).real (Iio t) =
      cdf (gaussianReal 0 1) ((t - m) / σ) := by
  rw [← map_standardGaussian_affine m σ, Measure.real,
    Measure.map_apply (by fun_prop) measurableSet_Iio]
  have hpre : (fun z : ℝ => σ * z + m) ⁻¹' Iio t = Iio ((t - m) / σ) := by
    ext z
    simp only [mem_preimage, mem_Iio]
    rw [lt_div_iff₀ hσ]
    constructor <;> intro hz <;> nlinarith only [hz]
  rw [hpre]
  exact EhrhardType.strictCDF_standardGaussian _

/-- For a nonconstant Ehrhard law, the set where its strict CDF exceeds a Gaussian CDF is convex. -/
theorem convex_positive_strictCDF_sub_gaussian_of_nonconstant {μ : Measure ℝ}
    (hμ : IsEhrhardType μ) (hn : ¬ ∃ c, μ = Measure.dirac c)
    (m : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Convex ℝ {t | 0 < μ.real (Iio t) -
      (gaussianReal m ⟨σ ^ 2, sq_nonneg σ⟩).real (Iio t)} := by
  have := hμ.1
  rcases hμ.2 with hconst | ⟨_, g, hg, heq⟩
  · exact (hn hconst).elim
  have hiff : ∀ t, (0 < μ.real (Iio t) -
      (gaussianReal m ⟨σ ^ 2, sq_nonneg σ⟩).real (Iio t)) ↔
      0 < μ (Iio t) ∧ (t - m) / σ < g t := by
    intro t
    rw [strictCDF_gaussianReal_scale m hσ t, sub_pos]
    constructor
    · intro ht
      have hp : 0 < μ (Iio t) := by
        apply pos_iff_ne_zero.mpr
        intro hzero
        have hz : μ.real (Iio t) = 0 := by rw [Measure.real, hzero, ENNReal.toReal_zero]
        exact (ht.trans_le hz.le).not_ge (cdf_nonneg _ _)
      refine ⟨hp, ?_⟩
      change cdf (gaussianReal 0 1) ((t - m) / σ) < (μ (Iio t)).toReal at ht
      rw [heq t hp] at ht
      exact EhrhardType.strictMono_standardGaussian_cdf.lt_iff_lt.mp ht
    · rintro ⟨hp, ht⟩
      change cdf (gaussianReal 0 1) ((t - m) / σ) < (μ (Iio t)).toReal
      rw [heq t hp]
      exact EhrhardType.strictMono_standardGaussian_cdf ht
  intro x hx y hy a b ha hb hab
  obtain ⟨hxD, hxg⟩ := (hiff x).mp hx
  obtain ⟨hyD, hyg⟩ := (hiff y).mp hy
  apply (hiff (a • x + b • y)).mpr
  refine ⟨hg.1 hxD hyD ha hb hab, ?_⟩
  have hstrict : a * ((x - m) / σ) + b * ((y - m) / σ) < a * g x + b * g y := by
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith only [hab, ha0]
      simpa only [ha0, hb1, zero_mul, one_mul, zero_add] using hyg
    · exact add_lt_add_of_lt_of_le
        (mul_lt_mul_of_pos_left hxg (lt_of_le_of_ne ha (Ne.symm ha0)))
        (mul_le_mul_of_nonneg_left hyg.le hb)
  have hconc := hg.2 hxD hyD ha hb hab
  have hlin : (a * x + b * y - m) / σ = a * ((x - m) / σ) + b * ((y - m) / σ) := by
    calc
      _ = (a * x + b * y - (a + b) * m) / σ := by rw [hab, one_mul]
      _ = _ := by ring
  change (a * x + b * y - m) / σ < g (a * x + b * y)
  rw [hlin]
  exact hstrict.trans_le hconc

end EhrhardGaussian.GaussianConvexity
