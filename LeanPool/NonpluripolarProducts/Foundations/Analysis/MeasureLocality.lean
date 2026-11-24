/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Almost-everywhere locality on metric balls
-/

@[expose] public section

open Set Filter MeasureTheory Metric
open scoped Topology

namespace SGPT.Foundations.Analysis.MeasureLocality

/-- A property that holds almost everywhere on a ball about each point of a set
holds almost everywhere on the set. -/
theorem ae_of_forall_ball {E : Type*} [PseudoMetricSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] {μ : Measure E} {U : Set E} {Q : E → Prop}
    (h : ∀ z ∈ U, ∃ r > 0, ∀ᵐ x ∂μ, x ∈ ball z r → Q x) :
    ∀ᵐ x ∂μ, x ∈ U → Q x := by
  classical
  choose! r hr hQ using h
  obtain ⟨S, hSc, hSU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun z : U ↦ ball (z : E) (r z)) (fun _ ↦ isOpen_ball)
  have hS : ∀ᵐ x ∂μ, ∀ z ∈ S,
      x ∈ ball ((z : U) : E) (r z) → Q x :=
    (ae_ball_iff hSc).mpr fun z _ ↦ hQ z z.2
  filter_upwards [hS] with x hx hxU
  have hx' : x ∈ ⋃ z : U, ball (z : E) (r z) :=
    mem_iUnion.mpr ⟨⟨x, hxU⟩, mem_ball_self (hr x hxU)⟩
  rw [← hSU] at hx'
  obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp hx'
  exact hx z hz hxz

end SGPT.Foundations.Analysis.MeasureLocality
