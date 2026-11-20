/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
module

public import Mathlib.Topology.Bases

/-!
# A dense countable subset of a second-countable topological space

-/

@[expose] public section

/-- A countable dense subset of a second-countable topological space. -/
noncomputable def denseCountable (T : Type*) [TopologicalSpace T] [SecondCountableTopology T] :
    Set T :=
  (TopologicalSpace.exists_countable_dense T).choose

lemma dense_denseCountable {T : Type*} [TopologicalSpace T] [SecondCountableTopology T] :
    Dense (denseCountable T) :=
  (TopologicalSpace.exists_countable_dense T).choose_spec.2

lemma countable_denseCountable {T : Type*} [TopologicalSpace T] [SecondCountableTopology T] :
    (denseCountable T).Countable :=
  (TopologicalSpace.exists_countable_dense T).choose_spec.1
