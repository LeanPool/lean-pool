/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Walks

/-!
# Point sets of concatenated trace walks

For the assembly in XII (2.1), Case 1, page 244, concatenating
walks unions their point sets. A single edge step adds its closure,
and a two-edge region visit has precisely the union of its two edge
closures as point set. These identities identify the circle assembled
from the deformed region paths with the trace drawing's point set.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- The point set of a concatenated walk is the union of the point
sets of the two walks. -/
theorem walkDrawing_U_append
    {S : Type*} [TopologicalSpace S] [T1Space S] (K : Drawing S) {u v w : S}
    (P : GraphWalk K.toGraph u v) (Q : GraphWalk K.toGraph v w) :
    (walkDrawing K (P.append Q)).U = (walkDrawing K P).U ∪ (walkDrawing K Q).U :=
  GraphWalk.drawing_U_append K P Q

/-- A zero-edge walk has just its vertex as point set. -/
theorem walkDrawing_U_nil
    {S : Type*} [TopologicalSpace S] [T1Space S] (K : Drawing S) {u : S} (hu : u ∈ K.V) :
    (walkDrawing K (GraphWalk.nil hu)).U = {u} :=
  GraphWalk.drawing_U_nil K hu

/-- An edge step adds exactly its edge closure to the point set. -/
theorem walkDrawing_U_cons
    {S : Type*} [TopologicalSpace S] [T1Space S] (K : Drawing S) {u v w : S} {e : Set S}
    (hl : K.toGraph.IsLink e u v) (P : GraphWalk K.toGraph v w) :
    (walkDrawing K (GraphWalk.cons hl P)).U = closure e ∪ (walkDrawing K P).U :=
  GraphWalk.drawing_U_cons K hl P

/-- A two-edge region visit has the two edge closures as its whole
point set. -/
theorem walkDrawing_U_two_edges
    {S : Type*} [TopologicalSpace S] [T1Space S] (K : Drawing S)
    {u v w : S} {e e' : Set S} (hl : K.toGraph.IsLink e u v) (hl' : K.toGraph.IsLink e' v w) :
    (walkDrawing K (GraphWalk.cons hl (GraphWalk.cons hl' (.nil hl'.right_mem)))).U =
      closure e ∪ closure e' :=
  GraphWalk.drawing_U_two_edges K hl hl'

end GraphMinor.GM12
