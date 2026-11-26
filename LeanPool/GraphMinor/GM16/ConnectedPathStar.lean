/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.GraphPathSystemUnion
public import LeanPool.GraphMinor.GM09.Defs
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM11.Walks

/-!
# A union of paths from one centre is connected

Every vertex on an arm can reach the centre along a subpath of
that arm. These walks lie in the union graph. Joining two such
walks at the centre proves graph connectivity. Keeping the centre
as a separate vertex also covers the case of no arms. This is
the branch graph used for the subdivision minor in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Graph Surface GM09
universe u v w

private theorem walk_reflTransGen_adj {α : Type u} {β : Type v} {G : Graph α β}
    {a b : α} (W : GraphWalk G a b) : Relation.ReflTransGen G.Adj a b := by
  induction W with
  | nil _ => exact .refl
  | @cons a c b e h W ih => exact (Relation.ReflTransGen.single ⟨e,h⟩).trans ih

/-- The union of paths with a common initial vertex is connected,
including when the index type is empty. -/
theorem graphConnected_pathSystemGraph_star
    {α : Type u} {β : Type v} {ι : Type w} {G : Graph α β}
    {a : α} {P : ι → Graph α β} {b : ι → α}
    (hP : ∀ i, IsGraphPathWithEnds G (P i) a (b i)) :
    GraphConnected (pathSystemGraph G {a} P) := by
  let K := pathSystemGraph G {a} P
  have hPK : ∀ i, P i ≤ K := le_pathSystemGraph (fun i => (hP i).le)
  have haK : a ∈ V(K) := Or.inl (mem_singleton a)
  have hToA (x : α) (hx : x ∈ V(K)) : Nonempty (GraphWalk K x a) := by
    change x ∈ ({a} : Set α) ∪ ⋃ i, V(P i) at hx
    rcases hx with hx | hx
    · rw [mem_singleton_iff] at hx
      subst x
      exact ⟨.nil haK⟩
    · obtain ⟨i,hxi⟩ := mem_iUnion.mp hx
      obtain ⟨Q,hQP,hQ,_⟩ := (hP i).exists_subpath hxi (hP i).left_mem
      obtain ⟨W,_,_,_⟩ := hQ.2
      obtain ⟨W',_,_⟩ := exists_walk_up_of_le (hQP.trans (hPK i)) W
      exact ⟨W'⟩
  refine ⟨⟨a,haK⟩,?_⟩
  intro x hx y hy
  obtain ⟨W⟩ := hToA x hx
  obtain ⟨W'⟩ := hToA y hy
  exact walk_reflTransGen_adj (W.append W'.reverse)

end GraphMinor.GM16
