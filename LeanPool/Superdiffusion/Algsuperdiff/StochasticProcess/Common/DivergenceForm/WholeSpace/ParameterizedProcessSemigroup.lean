/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.MarkovProcess.MarkovProcess.Kernel.OnePointKilled
public import LeanPool.MarkovProcess.MarkovProcess.Parameterized.ContinuousProcess

/-!
# ParameterizedProcessSemigroup

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The retraction of the one-point compactification onto the live space

A process on the one-point compactification `OnePoint X` is read back on `X` through a
retraction that sends the added point to a chosen base point and is the identity on the live
part.  This module supplies that map and its measurability, which is what a quenched
observable on the live space needs before it can be integrated against the law of the
compactified process.

Measurability is not automatic: the retraction is not continuous at the added point.  It is
obtained instead from the two facts that the coercion `X → OnePoint X` is an open measurable
embedding and that the added point is a closed, hence measurable, singleton.
-/

namespace DivergenceFormProcess.Form

open MeasureTheory ProbabilityTheory Set
open MarkovProcess MarkovProcess.Semigroup
open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

section Retract

variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

/-- The retraction of a one-point compactification onto its live space which sends the added
point to a prescribed base point. -/
def onePointRetract (x0 : X) : OnePoint X → X := OnePoint.rec x0 id

omit [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
@[simp] theorem onePointRetract_coe (x0 x : X) :
    onePointRetract x0 (x : OnePoint X) = x := rfl

omit [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
@[simp] theorem onePointRetract_infty (x0 : X) :
    onePointRetract x0 (OnePoint.infty : OnePoint X) = x0 := rfl

omit [T2Space X] in
/-- The retraction onto the live space is measurable: the live part is a measurable embedding
and the added point is a measurable singleton. -/
theorem measurable_onePointRetract (x0 : X) : Measurable (onePointRetract (X := X) x0) := by
  intro A hA
  by_cases hx0 : x0 ∈ A
  · have hpre : onePointRetract (X := X) x0 ⁻¹' A =
        ((↑) : X → OnePoint X) '' A ∪ {OnePoint.infty} := by
      ext z
      induction z using OnePoint.rec with
      | infty => simp only [Set.mem_preimage, onePointRetract_infty, hx0, Set.mem_union,
          OnePoint.infty_notMem_image_coe, Set.mem_singleton_iff, or_true]
      | coe x => simp only [Set.mem_preimage, onePointRetract_coe, Set.mem_union, Set.mem_image,
          OnePoint.coe_eq_coe, exists_eq_right, OnePoint.coe_ne_infty, Set.mem_singleton_iff,
          or_false]
    rw [hpre]
    exact (OnePoint.isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr hA).union
      OnePoint.isClosed_infty.measurableSet
  · have hpre : onePointRetract (X := X) x0 ⁻¹' A = ((↑) : X → OnePoint X) '' A := by
      ext z
      induction z using OnePoint.rec with
      | infty => simp only [Set.mem_preimage, onePointRetract_infty, hx0,
          OnePoint.infty_notMem_image_coe]
      | coe x => simp only [Set.mem_preimage, onePointRetract_coe, Set.mem_image,
          OnePoint.coe_eq_coe, exists_eq_right]
    rw [hpre]
    exact OnePoint.isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr hA

end Retract

end

end DivergenceFormProcess.Form
