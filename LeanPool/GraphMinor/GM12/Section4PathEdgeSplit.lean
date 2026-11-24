/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM11.Walks

/-!
# The two path portions on either side of an edge

Claim (1) in XII (4.3), pages 249--250, removes one edge of a
path and uses the two remaining portions. Split the path walk at
that edge. Since the original vertex list has no repetitions, the
supports of the two portions are disjoint.
-/

public section

namespace GraphMinor.GM12

open Set Surface Graph

/-- Removing an edge of a simple path separates its vertex list
into disjoint portions, as used in XII (4.3), claim (1). -/
theorem exists_path_edge_split
    {α β : Type*} {G : Graph α β} {x y : α} (W : GraphWalk G x y)
    (hW : W.IsSimple) {f : β} (hf : f ∈ W.edges) :
    ∃ (a b : α) (P : GraphWalk G x a) (Q : GraphWalk G b y) (hl : G.IsLink f a b),
      W = P.append (.cons hl Q) ∧
        Disjoint {z | z ∈ P.support} {z | z ∈ Q.support} := by
  induction W with
  | nil hx => exact False.elim (List.not_mem_nil hf)
  | @cons x z y e he R ih =>
    have hsimple : (x :: R.support).Nodup := hW
    have hxR : x ∉ R.support := (List.nodup_cons.mp hsimple).1
    have hR : R.IsSimple := (List.nodup_cons.mp hsimple).2
    by_cases hef : e = f
    · subst f
      refine ⟨x, z, .nil he.left_mem, R, he, rfl, ?_⟩
      apply Set.disjoint_left.mpr
      intro v hvP hvQ
      have hvx : v = x := List.mem_singleton.mp hvP
      exact hxR (hvx ▸ hvQ)
    · have hfR : f ∈ R.edges := (List.mem_cons.mp hf).resolve_left (Ne.symm hef)
      obtain ⟨a, b, P, Q, hl, hsplit, hdis⟩ := ih hR hfR
      refine ⟨a, b, .cons he P, Q, hl, ?_, ?_⟩
      · rw [hsplit]
        rfl
      · apply Set.disjoint_left.mpr
        intro v hvP hvQ
        rcases List.mem_cons.mp hvP with rfl | hvP
        · apply hxR
          rw [hsplit, GraphWalk.mem_support_append]
          exact Or.inr (List.mem_cons_of_mem _ hvQ)
        · exact Set.disjoint_left.mp hdis hvP hvQ

end GraphMinor.GM12
