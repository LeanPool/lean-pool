/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Statements.Defs

/-!
# Finite plane trees and marked fringe counts

Finite rooted ordered trees, as in Section 2.1 of the paper. The list of fringe
trees records one entry for each vertex in depth-first order. Equal subtrees at
different vertices remain separate entries, so counting does not lose multiplicity.

The definitions `PlaneTree`, `children`, `rootDegree`, `fringeTrees`, `vertexCount`,
`markCount` and `declumpedMark` are in `PoissonDeclumping.Statements.Defs` (shared verbatim
with `Challenge.lean`); this file proves their basic properties.
-/

@[expose] public section

namespace PoissonDeclumping

namespace PlaneTree

/-- The propagation hypothesis in Lemma `lem:declump_to_raw`, for a fixed mark. -/
def PropagatesOutside (B : Set ℕ) (G : PlaneTree → Prop) : Prop :=
  ∀ (T U : PlaneTree), U ∈ T.children → G U → T.rootDegree ∉ B → G T

@[simp] theorem children_node (ts : List PlaneTree) : (node ts).children = ts := rfl

@[simp] theorem rootDegree_node (ts : List PlaneTree) :
    (node ts).rootDegree = ts.length := rfl

@[simp] theorem fringeTrees_node (ts : List PlaneTree) :
    (node ts).fringeTrees = node ts :: ts.flatMap fringeTrees := by
  rw [fringeTrees]

/-- The root contributes its own fringe tree. -/
theorem self_mem_fringeTrees (T : PlaneTree) : T ∈ T.fringeTrees := by
  cases T with
  | node ts => simp

/-- A child fringe occurrence remains a fringe occurrence in the parent. -/
theorem mem_fringeTrees_of_mem_child {T U V : PlaneTree}
    (hU : U ∈ T.children) (hV : V ∈ U.fringeTrees) : V ∈ T.fringeTrees := by
  cases T with
  | node ts =>
    rw [fringeTrees_node]
    exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨U, hU, hV⟩)

/-- Every child itself occurs among the parent's fringe trees. -/
theorem child_mem_fringeTrees {T U : PlaneTree} (hU : U ∈ T.children) :
    U ∈ T.fringeTrees :=
  mem_fringeTrees_of_mem_child hU (self_mem_fringeTrees U)

/-- A positive marked count is exactly the existence of a marked vertex. -/
theorem markCount_pos_iff (G : PlaneTree → Prop) (T : PlaneTree) :
    0 < markCount G T ↔ ∃ U ∈ T.fringeTrees, G U := by
  classical
  simp [markCount, List.countP_pos_iff]

/-- A zero marked count is exactly the absence of a marked vertex. -/
theorem markCount_eq_zero_iff (G : PlaneTree → Prop) (T : PlaneTree) :
    markCount G T = 0 ↔ ∀ U ∈ T.fringeTrees, ¬G U := by
  classical
  simp [markCount, List.countP_eq_zero]

/-- Marking the root ensures that the raw count is positive. -/
theorem markCount_pos_of_root {G : PlaneTree → Prop} {T : PlaneTree}
    (h : G T) : 0 < markCount G T :=
  (markCount_pos_iff G T).mpr ⟨T, self_mem_fringeTrees T, h⟩

/-- A positive count in a child ensures a positive count in the parent. -/
theorem markCount_pos_of_child {G : PlaneTree → Prop} {T U : PlaneTree}
    (hU : U ∈ T.children) (h : 0 < markCount G U) : 0 < markCount G T := by
  obtain ⟨V, hV, hG⟩ := (markCount_pos_iff G U).mp h
  exact (markCount_pos_iff G T).mpr ⟨V, mem_fringeTrees_of_mem_child hU hV, hG⟩

/-- Structural induction with an induction hypothesis for every child. -/
theorem induction_children {P : PlaneTree → Prop}
    (step : ∀ T, (∀ U ∈ T.children, P U) → P T) (T : PlaneTree) : P T := by
  apply step T
  intro U hU
  exact induction_children step U
termination_by sizeOf T
decreasing_by
  cases T with
  | node ts =>
    have h := List.sizeOf_lt_of_mem hU
    simp_all only [children_node, PlaneTree.node.sizeOf_spec]
    omega

/-- Fringe containment is transitive. -/
theorem mem_fringeTrees_trans {T U V : PlaneTree}
    (hU : U ∈ T.fringeTrees) (hV : V ∈ U.fringeTrees) : V ∈ T.fringeTrees := by
  induction T using induction_children generalizing U V with
  | step T ih =>
    cases T with
    | node ts =>
      rw [fringeTrees_node] at hU
      rcases List.mem_cons.mp hU with hU | hU
      · subst U
        exact hV
      · obtain ⟨W, hW, hU⟩ := List.mem_flatMap.mp hU
        exact mem_fringeTrees_of_mem_child hW (ih W hW hU hV)

/-- Any marked vertex is either the root or belongs to a child tree. -/
theorem markCount_pos_iff_root_or_child (G : PlaneTree → Prop) (T : PlaneTree) :
    0 < markCount G T ↔ G T ∨ ∃ U ∈ T.children, 0 < markCount G U := by
  constructor
  · intro h
    obtain ⟨V, hV, hG⟩ := (markCount_pos_iff G T).mp h
    cases T with
    | node ts =>
      rw [fringeTrees_node] at hV
      rcases List.mem_cons.mp hV with hV | hV
      · subst V
        exact Or.inl hG
      · obtain ⟨U, hU, hV⟩ := List.mem_flatMap.mp hV
        exact Or.inr ⟨U, hU, (markCount_pos_iff G U).mpr ⟨V, hV, hG⟩⟩
  · rintro (h | ⟨U, hU, h⟩)
    · exact markCount_pos_of_root h
    · exact markCount_pos_of_child hU h

end PlaneTree
end PoissonDeclumping
