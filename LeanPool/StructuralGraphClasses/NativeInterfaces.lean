/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.StructuralGraphClasses.CotreeCompleteness
public import LeanPool.StructuralGraphClasses.Threshold
public import LeanPool.StructuralGraphClasses.InducedPathFour

/-!
# Structural classes through native induced containment

Consumers can use Mathlib's path graph and induced embeddings directly, without
unfolding the local edge/nonedge predicate used in the proofs.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Cograph membership is native induced `P₄` exclusion. -/
theorem isCograph_iff_not_pathGraph_four_isIndContained :
    G.IsCograph ↔ ¬(pathGraph 4).IsIndContained G :=
  isP4Free_iff_not_pathGraph_four_isIndContained

/-- Native induced `P₄` exclusion is exactly finite cotree representability. -/
theorem nonempty_cotreeRepresentation_iff_not_pathGraph_four_isIndContained [Finite V] :
    Nonempty (CotreeRepresentation G) ↔ ¬(pathGraph 4).IsIndContained G :=
  (isCograph_iff_nonempty_cotreeRepresentation (G := G)).symm.trans
    isCograph_iff_not_pathGraph_four_isIndContained

/-- Threshold membership combines a split certificate with native induced `P₄` exclusion. -/
theorem isThreshold_iff_isSplit_and_not_pathGraph_four_isIndContained :
    G.IsThreshold ↔ G.IsSplit ∧ ¬(pathGraph 4).IsIndContained G := by
  rw [isThreshold_iff_isSplit_and_isP4Free, isP4Free_iff_not_pathGraph_four_isIndContained]

end SimpleGraph
