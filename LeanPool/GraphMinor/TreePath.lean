/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Vertices on the path in a tree

A vertex lies on a path between two endpoints if it lies on every simple path between them.
When the graph is a tree there is a unique simple path. The basic facts also apply to
arbitrary simple graphs.
-/

@[expose] public section

namespace GraphMinor.TreePath

open SimpleGraph

variable {ι : Type*}

/-- Every path from `a` to `b` passes through `v`. -/
def OnTreePath (T : SimpleGraph ι) (a b v : ι) : Prop :=
  ∀ p : T.Walk a b, p.IsPath → v ∈ p.support

/-- The start vertex lies on every path. -/
theorem left (T : SimpleGraph ι) (a b : ι) : OnTreePath T a b a :=
  fun p _ ↦ p.start_mem_support

/-- The end vertex lies on every path. -/
theorem right (T : SimpleGraph ι) (a b : ι) : OnTreePath T a b b :=
  fun p _ ↦ p.end_mem_support

/-- Reversing the endpoints preserves the vertex-on-path property. -/
theorem symm {T : SimpleGraph ι} {a b v : ι} (h : OnTreePath T a b v) : OnTreePath T b a v := by
  intro p hp
  have hm := h p.reverse hp.reverse
  rwa [Walk.support_reverse, List.mem_reverse] at hm

/-- The trivial path contains only its endpoint. -/
theorem self_iff {T : SimpleGraph ι} {a v : ι} : OnTreePath T a a v ↔ v = a := by
  constructor
  · intro h
    simpa using h Walk.nil Walk.IsPath.nil
  · rintro rfl
    exact left T _ _

/-- A vertex on every simple path lies on every walk between the same endpoints. -/
theorem mem_support {T : SimpleGraph ι} {a b v : ι} (h : OnTreePath T a b v)
    (w : T.Walk a b) : v ∈ w.support := by
  classical
  exact w.support_bypass_subset_support (h w.bypass w.bypass_isPath)

end GraphMinor.TreePath
