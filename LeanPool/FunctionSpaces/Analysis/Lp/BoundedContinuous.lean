/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Lp.Inclusion
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.UniformSpace.CompleteSeparated

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Bounded continuous functions in `L_p`

Mathlib's `BoundedContinuousFunction.toLp p μ 𝕜` regards a bounded continuous function on a
finite measure space as an element of `L_p(μ)`.  This file adds:

* compatibility with the inclusion `L_r ↪ L_p`: including the `L_r` class of `a` gives its
  `L_p` class (`BoundedContinuousFunction.inclusionOfExponentLe_toLp`);
* `‖toLp p μ 𝕜 a‖ = ‖a‖_{L_p}` written with `eLpNorm` (`norm_toLp_eq_toReal_eLpNorm`);
* for a measure giving positive mass to nonempty open sets, the sup norm equals the `L_∞`
  norm (`norm_toLp_top`), so `toLp ∞` is an isometry and its range is closed
  (`isClosed_range_toLp_top`).

The last point is what lets a limit of continuous functions in `L_∞` be continuous: it is the
step from "`f ∈ L_∞`" to "`f` has a continuous representative" in the embeddings into `C(Ω)`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BoundedContinuousFunction

variable {α E 𝕜 : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
  [TopologicalSpace α] [BorelSpace α] [NormedAddCommGroup E] [SecondCountableTopologyEither α E]
  [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [IsFiniteMeasure μ] {p r : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ r)]

/-- The `L_p` class of `a` is the inclusion of its `L_r` class. -/
@[simp]
theorem inclusionOfExponentLe_toLp (hpr : p ≤ r) (a : α →ᵇ E) :
    Lp.inclusionOfExponentLe (𝕜 := 𝕜) μ hpr (toLp (E := E) r μ 𝕜 a) = toLp (E := E) p μ 𝕜 a := by
  ext1
  filter_upwards [Lp.coeFn_inclusionOfExponentLe (𝕜 := 𝕜) hpr (toLp (E := E) r μ 𝕜 a),
    coeFn_toLp (E := E) r μ 𝕜 a, coeFn_toLp (E := E) p μ 𝕜 a] with x h1 h2 h3
  rw [h1, h2, h3]

/-- The `L_p` norm of the class of a bounded continuous function is its `eLpNorm`: the bounded
continuous analogue of Mathlib's `MeasureTheory.Lp.norm_toLp`, proved from
`MeasureTheory.Lp.norm_def` with the class `toLp p μ 𝕜 a` equal to `a` almost everywhere
(`BoundedContinuousFunction.coeFn_toLp`). -/
theorem norm_toLp_eq_toReal_eLpNorm (a : α →ᵇ E) :
    ‖toLp (E := E) p μ 𝕜 a‖ = (eLpNorm a p μ).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_toLp (E := E) p μ 𝕜 a)]

/-- For a measure that charges every nonempty open set, the `L_∞` norm of a bounded
continuous function is its sup norm. -/
theorem norm_toLp_top [μ.IsOpenPosMeasure] (a : α →ᵇ E) : ‖toLp (E := E) ∞ μ 𝕜 a‖ = ‖a‖ := by
  apply le_antisymm
  · have := Lp.norm_le_of_ae_bound (f := toLp (E := E) ∞ μ 𝕜 a) (norm_nonneg a)
      ((coeFn_toLp (E := E) ∞ μ 𝕜 a).mono fun x hx => by rw [hx]; exact a.norm_coe_le_norm x)
    simpa using this
  · -- the open set where `‖a x‖` exceeds the `L_∞` norm is null, hence empty
    set F := toLp (E := E) ∞ μ 𝕜 a
    have hae : ∀ᵐ x ∂μ, ‖a x‖ₑ ≤ ‖F‖ₑ := by
      filter_upwards [coeFn_toLp (E := E) ∞ μ 𝕜 a,
        ae_le_eLpNormEssSup (f := (F : α → E)) (μ := μ)] with x h1 h2
      rw [← h1, Lp.eNorm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable F)]
      exact h2
    have hU : IsOpen {x | ‖F‖ₑ < ‖a x‖ₑ} :=
      isOpen_lt continuous_const (continuous_eNorm.comp a.continuous)
    have hU0 : μ {x | ‖F‖ₑ < ‖a x‖ₑ} = 0 := by
      simpa [not_le] using ae_iff.1 hae
    rw [hU.measure_eq_zero_iff μ] at hU0
    refine (norm_le (norm_nonneg _)).2 fun x => ?_
    have hx : ‖a x‖ₑ ≤ ‖F‖ₑ := by
      by_contra h
      exact (Set.eq_empty_iff_forall_notMem.1 hU0 x) (not_le.1 h)
    rw [← toReal_eNorm, ← toReal_eNorm]
    exact ENNReal.toReal_mono eNorm_ne_top hx

/-- For a measure that charges every nonempty open set, `toLp ∞` is an isometry. -/
theorem isometry_toLp_top [μ.IsOpenPosMeasure] :
    Isometry (toLp (E := E) ∞ μ 𝕜 : (α →ᵇ E) → Lp E ∞ μ) :=
  (AddMonoidHomClass.isometry_iff_norm _).2 (norm_toLp_top (μ := μ) (𝕜 := 𝕜))

/-- For a measure that charges every nonempty open set, the bounded continuous functions form
a closed subspace of `L_∞`. -/
theorem isClosed_range_toLp_top [μ.IsOpenPosMeasure] [CompleteSpace E] :
    IsClosed (Set.range (toLp (E := E) ∞ μ 𝕜 : (α →ᵇ E) → Lp E ∞ μ)) :=
  ((isometry_toLp_top (μ := μ) (𝕜 := 𝕜)).isUniformInducing.isComplete_range).isClosed

end BoundedContinuousFunction
