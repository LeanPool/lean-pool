/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.EhrhardType.QuantileConvex
public import LeanPool.EhrhardGaussian.EhrhardType.ConvexInverse
import Mathlib.Tactic.Linarith

/-! A probability law is of Ehrhard type exactly when it is the law of a finite monotone convex
function of a standard Gaussian, including constant laws. -/

@[expose] public section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set

namespace EhrhardGaussian.EhrhardType

/-- A finite monotone convex image of a standard Gaussian has an Ehrhard-type law. -/
theorem isEhrhardType_map_of_monotone_convex {h : ℝ → ℝ}
    (hh : Monotone h) (hc : ConvexOn ℝ univ h) :
    IsEhrhardType ((gaussianReal 0 1).map h) := by
  have hcont : Continuous h := continuousOn_univ.mp (hc.continuousOn isOpen_univ)
  by_cases hn : ∀ x, h x = h 0
  · have heq : h = fun _ => h 0 := funext hn
    rw [heq, Measure.map_const, measure_univ, one_smul]
    exact isEhrhardType_dirac _
  have hopen : ∀ t, IsOpen {z | h z < t} := fun _ => isOpen_lt hcont continuous_const
  have := isOpenPosMeasure_gaussianReal 0 (v := 1) one_ne_zero
  have hpos : ∀ t, 0 < ((gaussianReal 0 1).map h) (Iio t) ↔ ∃ z, h z < t := by
    intro t
    rw [Measure.map_apply hh.measurable measurableSet_Iio]
    exact (hopen t).measure_pos_iff _
  have hdom : {t | 0 < ((gaussianReal 0 1).map h) (Iio t)} = {t | ∃ z, h z < t} :=
    Set.ext hpos
  refine ⟨inferInstance, Or.inr ⟨?_, fun t => sSup {z | h z < t}, ?_, ?_⟩⟩
  · intro t
    obtain ⟨z, hz⟩ := exists_lt_monotone_convex hh hc hn t
    have hsub : h ⁻¹' Iio t ⊆ Iio z := by
      intro x hx
      by_contra hxz
      have hzx : z ≤ x := le_of_not_gt hxz
      exact (hz.trans_le (hh hzx)).not_ge hx.le
    have hnormal : (gaussianReal 0 1) (Iio z) < 1 := by
      apply (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.one_ne_top).mp
      rw [ENNReal.toReal_one, strictCDF_standardGaussian]
      exact (standardGaussian_cdf_mem_Ioo z).2
    rw [Measure.map_apply hh.measurable measurableSet_Iio]
    exact (measure_mono hsub).trans_lt hnormal
  · rw [hdom]
    exact concaveOn_sublevelSup hh hc hn
  · intro t ht
    rw [Measure.map_apply hh.measurable measurableSet_Iio]
    have hsub := sublevel_eq_Iio_sSup hh hcont ((hpos t).mp ht)
      (exists_lt_monotone_convex hh hc hn t)
    change ((gaussianReal 0 1) {z | h z < t}).toReal = _
    rw [hsub]
    exact strictCDF_standardGaussian _

/-- An Ehrhard-type law is exactly a monotone convex image of the standard Gaussian law. -/
theorem isEhrhardType_iff_exists_monotone_convex (ν : Measure ℝ)
    (_hν : IsProbabilityMeasure ν) :
    IsEhrhardType ν ↔ ∃ h : ℝ → ℝ, Monotone h ∧ ConvexOn ℝ univ h ∧
      ν = (gaussianReal 0 1).map h := by
  constructor
  · exact exists_monotone_convex_representative
  · rintro ⟨h, hh, hc, rfl⟩
    exact isEhrhardType_map_of_monotone_convex hh hc

end EhrhardGaussian.EhrhardType
