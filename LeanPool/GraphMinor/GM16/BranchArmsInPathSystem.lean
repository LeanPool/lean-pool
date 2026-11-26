/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.GraphPathSystemUnion
public import LeanPool.GraphMinor.GM01.Defs

/-!
# The chosen arms and edges occur in the path union

For an arm toward a neighbor, take that source edge's replacing
path. Its chosen orientation is either the given order or its
reverse. In either case the exact vertex and edge union formulas
put the arm inside the path. The same formulas retain every
chosen model edge. These are the subgraph checks for the minor
inside the subdivision in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Graph
universe u v w

private theorem arm_eq_of_ends_eq {α : Type u} {β : Type v} {ν : Type w}
    {H : SimpleGraph ν} (arm : ∀ v, H.neighborSet v → Graph α β)
    {a b v w : ν} (hab : H.Adj a b) (hvw : H.Adj v w) (ha : a = v) (hb : b = w) :
    arm a ⟨b,hab⟩ = arm v ⟨w,hvw⟩ := by
  subst v w
  rfl

/-- The union of the replacing paths contains all arms and all
chosen source-edge images. -/
theorem branch_arms_le_pathSystemGraph
    {α : Type u} {β : Type v} {ν : Type w} {H : SimpleGraph ν} {G : Graph α β}
    (C : Set α) (arm : ∀ v, H.neighborSet v → Graph α β)
    (P : H.edgeSet → Graph α β) (a b : H.edgeSet → ν) (ηe : Sym2 ν → β)
    (hEq : ∀ e, e.val = s(a e, b e)) (hAdj : ∀ e, H.Adj (a e) (b e))
    (hArmG : ∀ v i, arm v i ≤ G) (hPG : ∀ e, P e ≤ G)
    (hV : ∀ e, V(P e) = V(arm (a e) ⟨b e, hAdj e⟩) ∪ V(arm (b e) ⟨a e, (hAdj e).symm⟩))
    (hE : ∀ e, E(P e) = (E(arm (a e) ⟨b e, hAdj e⟩) ∪ {ηe e.val}) ∪
      E(arm (b e) ⟨a e, (hAdj e).symm⟩)) :
    (∀ v i, arm v i ≤ pathSystemGraph G C P) ∧
      (∀ e ∈ H.edgeSet, ηe e ∈ E(pathSystemGraph G C P)) := by
  constructor
  · intro v i
    let e : H.edgeSet := ⟨s(v,i.val),i.property⟩
    have hPair : s(a e,b e)=s(v,i.val) := (hEq e).symm
    have hSets : V(arm v i) ⊆ V(P e) ∧ E(arm v i) ⊆ E(P e) := by
      rcases Sym2.eq_iff.mp hPair with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · have hArmEq := arm_eq_of_ends_eq arm (hAdj e) i.property ha hb
        refine ⟨?_,?_⟩
        · rw [hV e]
          exact fun _ hx => Or.inl (hArmEq.symm ▸ hx)
        · rw [hE e]
          exact fun _ hx => Or.inl (Or.inl (hArmEq.symm ▸ hx))
      · have hArmEq := arm_eq_of_ends_eq arm (hAdj e).symm i.property hb ha
        refine ⟨?_,?_⟩
        · rw [hV e]
          exact fun _ hx => Or.inr (hArmEq.symm ▸ hx)
        · rw [hE e]
          exact fun _ hx => Or.inr (hArmEq.symm ▸ hx)
    have hArmP : arm v i ≤ P e :=
      (Compatible.of_le_le (hArmG v i) (hPG e)).le_iff.mpr hSets
    exact hArmP.trans (le_pathSystemGraph hPG e)
  · intro e he
    let e₀ : H.edgeSet := ⟨e,he⟩
    apply (le_pathSystemGraph hPG e₀).edgeSet_mono
    rw [hE e₀]
    exact Or.inl (Or.inr (mem_singleton _))

end GraphMinor.GM16
