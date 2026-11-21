/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# Compactness of genuinely bounded Lipschitz smoothing families

Arzelà--Ascoli gives compact closure for actual continuous functions on a
compact metric domain; the actual continuous inclusion into L² transfers
that compactness to genuine equivalence classes. No Sobolev embedding or
compact resolvent is assumed.
-/

public section

namespace CutoffRigidity

open MeasureTheory Set
open scoped BoundedContinuousFunction

variable {K : Type*} [PseudoMetricSpace K] [CompactSpace K]

/-- Uniform bounds and a uniform actual Lipschitz constant give compact
closure in the supremum norm on a compact domain. -/
theorem isCompact_closure_of_uniform_bound_lipschitz
    (A : Set (K →ᵇ ℝ)) (B : ℝ) (L : NNReal)
    (hbound : ∀ f ∈ A, ∀ x, |f x| ≤ B)
    (hLip : ∀ f ∈ A, LipschitzWith L f) :
    IsCompact (closure A) := by
  apply BoundedContinuousFunction.arzela_ascoli (Icc (-B) B) isCompact_Icc A
  · intro f x hf
    exact abs_le.mp (hbound f hf x)
  · exact (LipschitzWith.uniformEquicontinuous (fun f : A => (f : K → ℝ)) L
      (fun f => hLip f f.property)).equicontinuous

/-- The L² image of a uniformly bounded Lipschitz family has compact
closure under any actual finite Borel measure on the compact domain. -/
theorem isCompact_closure_toLp_of_uniform_bound_lipschitz
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (A : Set (K →ᵇ ℝ)) (B : ℝ) (L : NNReal)
    (hbound : ∀ f ∈ A, ∀ x, |f x| ≤ B)
    (hLip : ∀ f ∈ A, LipschitzWith L f) :
    IsCompact (closure ((BoundedContinuousFunction.toLp 2 μ ℝ) '' A)) := by
  have hc := (isCompact_closure_of_uniform_bound_lipschitz A B L hbound hLip).image
    (BoundedContinuousFunction.toLp 2 μ ℝ).continuous
  apply hc.closure_of_subset
  exact image_mono subset_closure

/-- Uniform approximation by genuinely totally bounded families transfers
total boundedness to the original family. This is the final metric step
after spatial cutoff and smoothing estimates have been proved. -/
theorem totallyBounded_of_uniform_precompact_approximation
    {X : Type*} [PseudoMetricSpace X] (S : Set X)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ T : Set X, TotallyBounded T ∧
      ∀ x ∈ S, ∃ y ∈ T, dist x y < ε) : TotallyBounded S := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨T, hT, hnear⟩ := happrox (ε / 2) (half_pos hε)
  obtain ⟨F, hF, hcover⟩ := Metric.totallyBounded_iff.mp hT (ε / 2) (half_pos hε)
  refine ⟨F, hF, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hnear x hx
  obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp (hcover hy)
  apply mem_iUnion₂.mpr
  refine ⟨z, hz, ?_⟩
  change dist x z < ε
  have hdist : dist y z < ε / 2 := hyz
  exact lt_of_le_of_lt (dist_triangle x y z) (by linarith)

/-- In a complete metric space the resulting closure is actually compact. -/
theorem isCompact_closure_of_uniform_precompact_approximation
    {X : Type*} [MetricSpace X] [CompleteSpace X] (S : Set X)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ T : Set X, TotallyBounded T ∧
      ∀ x ∈ S, ∃ y ∈ T, dist x y < ε) : IsCompact (closure S) :=
  (totallyBounded_of_uniform_precompact_approximation S happrox).closure.isCompact_of_isClosed
    isClosed_closure

end CutoffRigidity
