/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.EhrhardType.Quantile
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The monotone convex Gaussian representative of an Ehrhard law

This is the constructive direction of the Gaussian-image representation, following LX26 Lemma 2.5
with
strict distribution functions. The quantile is finite everywhere, monotone,
measurable, and has exactly the original law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace EhrhardGaussian.EhrhardType

/-- The finite quantile of a point mass is its atom, for every probability in `(0,1)`. -/
theorem quantile_dirac (c : ℝ) (p : Ioo (0 : ℝ) 1) :
    quantile (Measure.dirac c) p = c := by
  apply (quantile_unique (Measure.dirac c) p ?_).symm
  intro a
  by_cases hca : c < a
  · rw [Measure.real, Measure.dirac_apply_of_mem (show c ∈ Iio a from hca), ENNReal.toReal_one]
    exact iff_of_true hca p.property.2
  · rw [Measure.real, Measure.dirac_apply' _ measurableSet_Iio,
      indicator_of_notMem (show c ∉ Iio a from hca), ENNReal.toReal_zero]
    exact iff_of_false hca (not_lt.mpr p.property.1.le)

/-- The canonical Gaussian quantile transport of every Ehrhard law is convex. -/
theorem convexOn_gaussianQuantileTransport {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ :
  IsEhrhardType μ) :
    ConvexOn ℝ univ (gaussianQuantileTransport μ) := by
  rcases hμ.2 with ⟨c, rfl⟩ | ⟨_, g, hg, hCDF⟩
  · have heq : gaussianQuantileTransport (Measure.dirac c) = fun _ => c :=
      funext fun _ => quantile_dirac c _
    rw [heq]
    exact convexOn_const c convex_univ
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  change gaussianQuantileTransport μ (a * x + b * y) ≤
    a * gaussianQuantileTransport μ x + b * gaussianQuantileTransport μ y
  apply le_of_forall_pos_le_add
  intro ε hε
  let u := gaussianQuantileTransport μ x + ε
  let v := gaussianQuantileTransport μ y + ε
  have hux : cdf (gaussianReal 0 1) x < μ.real (Iio u) :=
    (gaussianQuantileTransport_lt_iff μ x u).mp (by dsimp [u]; linarith only [hε])
  have hvy : cdf (gaussianReal 0 1) y < μ.real (Iio v) :=
    (gaussianQuantileTransport_lt_iff μ y v).mp (by dsimp [v]; linarith only [hε])
  have hu : 0 < μ (Iio u) := by
    apply pos_iff_ne_zero.mpr
    intro hzero
    have hz : μ.real (Iio u) = 0 := by rw [Measure.real, hzero, ENNReal.toReal_zero]
    exact (hux.trans_le hz.le).not_ge (cdf_nonneg _ _)
  have hv : 0 < μ (Iio v) := by
    apply pos_iff_ne_zero.mpr
    intro hzero
    have hz : μ.real (Iio v) = 0 := by rw [Measure.real, hzero, ENNReal.toReal_zero]
    exact (hvy.trans_le hz.le).not_ge (cdf_nonneg _ _)
  have hgu : x < g u := by
    change cdf (gaussianReal 0 1) x < (μ (Iio u)).toReal at hux
    rw [hCDF u hu] at hux
    exact strictMono_standardGaussian_cdf.lt_iff_lt.mp hux
  have hgv : y < g v := by
    change cdf (gaussianReal 0 1) y < (μ (Iio v)).toReal at hvy
    rw [hCDF v hv] at hvy
    exact strictMono_standardGaussian_cdf.lt_iff_lt.mp hvy
  have hw : 0 < μ (Iio (a * u + b * v)) := hg.1 hu hv ha hb hab
  have hgc : a * g u + b * g v ≤ g (a * u + b * v) := hg.2 hu hv ha hb hab
  have hstrict : a * x + b * y < a * g u + b * g v := by
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith only [hab, ha0]
      rw [ha0, hb1, zero_mul, zero_mul, zero_add, zero_add, one_mul, one_mul]
      exact hgv
    · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hgu (lt_of_le_of_ne ha (Ne.symm ha0)))
        (mul_le_mul_of_nonneg_left hgv.le hb)
  have hq : gaussianQuantileTransport μ (a * x + b * y) < a * u + b * v := by
    apply (gaussianQuantileTransport_lt_iff μ _ _).mpr
    change cdf (gaussianReal 0 1) (a * x + b * y) < (μ (Iio (a * u + b * v))).toReal
    rw [hCDF _ hw]
    exact strictMono_standardGaussian_cdf (hstrict.trans_le hgc)
  have heq : a * u + b * v =
      a * gaussianQuantileTransport μ x + b * gaussianQuantileTransport μ y + ε := by
    dsimp [u, v]
    calc
      _ = a * gaussianQuantileTransport μ x + b * gaussianQuantileTransport μ y +
          (a + b) * ε := by ring
      _ = _ := by rw [hab, one_mul]
  exact hq.le.trans_eq heq

/-- Every Ehrhard-type law has a monotone convex standard-Gaussian representative. -/
theorem exists_monotone_convex_representative {μ : Measure ℝ} (hμ : IsEhrhardType μ) :
    ∃ h : ℝ → ℝ, Monotone h ∧ ConvexOn ℝ univ h ∧ μ = (gaussianReal 0 1).map h := by
  have := hμ.1
  exact ⟨gaussianQuantileTransport μ, monotone_gaussianQuantileTransport μ,
    convexOn_gaussianQuantileTransport hμ, (map_gaussianQuantileTransport μ).symm⟩

end EhrhardGaussian.EhrhardType
