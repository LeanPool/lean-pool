/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColorDegreeBounds

public import LeanPool.GoldbergSeymour.MaximumDegree
public import LeanPool.GoldbergSeymour.MissingColors
public import Mathlib.Data.Fintype.EquivFin

/-!
# Missing Colors Nonempty Of Maximum Degree

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

lemma MissingColorsNonemptyOfMaximumDegree
    {V E : Type*} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k : Nat}
    (phi : PartialEdgeColoring E k)
    (hdegree : MaximumDegree G + 1 <= k) (v : V) :
    (MissingColors G phi v).Nonempty := by
  classical
  have hdeg : Degree G v <= MaximumDegree G := by
    unfold MaximumDegree
    exact Finset.le_max' _ _ (Finset.mem_insert.mpr (Or.inr
      (Finset.mem_image.mpr <| Exists.intro v (by simp))))
  apply MissingColors.nonempty_of_degree_lt G phi v
  omega

end GoldbergSeymour

end
