/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.KernelEquivariance
public import LeanPool.MarkovProcess.MarkovProcess.Kernel.OnePointKilled
public import LeanPool.MarkovProcess.MarkovProcess.Main

/-!
# LiveRestrictionMarginals

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Post-composition of continuous paths, and the live embedding

`pathPostcomp` is the post-composition of a continuous path with a continuous map of the state
space.  It is continuous, and it reads at a finite set of times as the coordinatewise state map.

`liveEmbedding` is the coercion of a state space into its one-point compactification, read as a
map into path space; the coercion itself is injective.

Nothing here constructs a process: every statement is about a deterministic operation on path
space.
-/

namespace DivergenceFormProcess.LiveRestriction

open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

section Path

variable {alpha beta : Type*} [TopologicalSpace alpha] [TopologicalSpace beta]

/-- Post-compose a continuous path with a continuous map of the state space. -/
def pathPostcomp (f : C(alpha, beta)) (omega : ContinuousPath alpha) : ContinuousPath beta :=
  f.comp omega

@[simp]
theorem pathPostcomp_apply (f : C(alpha, beta)) (omega : ContinuousPath alpha) (t : NNReal) :
    pathPostcomp f omega t = f (omega t) := rfl

/-- Post-composition is continuous for the compact-open topology. -/
theorem continuous_pathPostcomp (f : C(alpha, beta)) :
    Continuous (pathPostcomp f : ContinuousPath alpha → ContinuousPath beta) :=
  ContinuousMap.continuous_postcomp f

/-- The exit time from the image of a set, read on a post-composed path, is the exit time from the
set itself, whenever the state map is injective.  The exit time is the infimum of the times at
which the path is outside the set, so only the injectivity of the state map is used. -/
theorem exitTime_image_pathPostcomp (f : C(alpha, beta)) (hf : Function.Injective f)
    (U : Set alpha) (omega : ContinuousPath alpha) :
    ContinuousPath.exitTime (f '' U) (pathPostcomp f omega) =
      ContinuousPath.exitTime U omega := by
  refine congrArg sInf ?_
  ext s
  constructor
  · rintro ⟨t, hst, ht⟩
    exact ⟨t, hst, fun hmem ↦ ht ⟨omega t, hmem, rfl⟩⟩
  · rintro ⟨t, hst, ht⟩
    refine ⟨t, hst, fun hmem ↦ ht ?_⟩
    obtain ⟨z, hz, hfz⟩ := hmem
    exact hf hfz ▸ hz

end Path

section Marginals

end Marginals

section OnePointEmbedding

/-- The coercion of a state space into its one-point compactification, as a continuous map. -/
def liveEmbedding (X : Type*) [TopologicalSpace X] : C(X, OnePoint X) :=
  ⟨((↑) : X → OnePoint X), OnePoint.continuous_coe⟩

@[simp]
theorem liveEmbedding_apply {X : Type*} [TopologicalSpace X] (x : X) :
    liveEmbedding X x = (x : OnePoint X) := rfl

/-- The coercion into the one-point compactification is injective. -/
theorem injective_liveCoe {X : Type*} : Function.Injective ((↑) : X → OnePoint X) :=
  Option.some_injective X

end OnePointEmbedding

end

end DivergenceFormProcess.LiveRestriction
