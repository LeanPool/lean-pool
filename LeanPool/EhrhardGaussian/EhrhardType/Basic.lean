/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Definitions.IsEhrhardType
public import LeanPool.EhrhardGaussian.EhrhardType.NormalCDF
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Order.UpperLower.Basic
import Mathlib.Tactic.Linarith

/-! Ehrhard-type laws include constants and use the strict distribution function, allowing an atom
at the lower endpoint. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace EhrhardGaussian.EhrhardType


/-- Constants are Ehrhard type, including the degenerate weak-limit case. -/
theorem isEhrhardType_dirac (c : ℝ) : IsEhrhardType (Measure.dirac c) :=
  ⟨inferInstance, Or.inl ⟨c, rfl⟩⟩

/-- The positive strict-CDF domain is an upper set, without an atomlessness assumption. -/
theorem isUpperSet_positive_strictCDF (μ : Measure ℝ) :
    IsUpperSet {a : ℝ | 0 < μ (Iio a)} := by
  intro a b hab ha
  exact ha.trans_le (measure_mono (Iio_subset_Iio hab))

/-- Consequently the domain used in the concavity definition is convex. -/
theorem convex_positive_strictCDF (μ : Measure ℝ) :
    Convex ℝ {a : ℝ | 0 < μ (Iio a)} :=
  convex_iff_ordConnected.mpr (isUpperSet_positive_strictCDF μ).ordConnected




/-- The standard normal law itself satisfies the strict-CDF definition. -/
theorem isEhrhardType_standardGaussian : IsEhrhardType (gaussianReal 0 1) := by
  refine ⟨inferInstance, Or.inr ⟨?_, id, concaveOn_id (convex_positive_strictCDF _), ?_⟩⟩
  · intro a
    apply (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.one_ne_top).mp
    rw [ENNReal.toReal_one, strictCDF_standardGaussian]
    exact (standardGaussian_cdf_mem_Ioo a).2
  · intro a _
    exact strictCDF_standardGaussian a






end EhrhardGaussian.EhrhardType
