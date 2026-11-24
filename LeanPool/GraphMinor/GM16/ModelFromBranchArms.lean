/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Minor.Model
public import LeanPool.GraphMinor.GM09.Defs
public import LeanPool.GraphMinor.GM01.Defs
import LeanPool.GraphMinor.GM16.ConnectedPathStar
import LeanPool.GraphMinor.GM09.Basic

/-!
# Retaining a subcubic minor inside the subdivision subgraph

The smaller branch set consists of its centre and its chosen
arms. These sets stay inside the original disjoint branch sets.
Their arms are connected and avoid the chosen model edges. Each
chosen edge still joins its two attachment points in the new
subgraph. Thus the same edge map, with these smaller branch sets,
is a minor model in the subdivision. This is the parenthetical
minor assertion about `N₄` in XVI (4.2), page 54.
-/

public section
namespace GraphMinor.GM16
open Set Graph Surface GM09
universe u v w

/-- A subgraph containing all chosen branch arms and chosen edges
retains the original simple-graph minor with the same edge map. -/
theorem minorModel_from_branch_arms
    {α : Type u} {β : Type v} {ν : Type w} {H : SimpleGraph ν} {G N : Graph α β}
    {ηv : ν → Set α} {ηe : Sym2 ν → β}
    (hModel : IsMinorModel (Graph.ofSimpleGraph H) G ηv ηe) (hNG : N ≤ G)
    (c : ν → α) (attach : ∀ v, H.neighborSet v → α)
    (arm : ∀ v, H.neighborSet v → Graph α β)
    (hc : ∀ v, c v ∈ ηv v) (hcN : ∀ v, c v ∈ V(N))
    (hAttach : ∀ v i, G.Inc (ηe s(v, i.val)) (attach v i))
    (hPath : ∀ v i, IsGraphPathWithEnds G (arm v i) (c v) (attach v i))
    (hArmN : ∀ v i, arm v i ≤ N)
    (hArmSub : ∀ v i, V(arm v i) ⊆ ηv v)
    (hArmAvoid : ∀ v i, Disjoint E(arm v i) (ηe '' H.edgeSet))
    (hChosenN : ∀ e ∈ H.edgeSet, ηe e ∈ E(N)) :
    IsMinorModel (Graph.ofSimpleGraph H) N (fun v => {c v} ∪ ⋃ i, V(arm v i)) ηe := by
  have hSub (v : ν) : {c v} ∪ ⋃ i, V(arm v i) ⊆ ηv v := by
    rintro x (hx | hx)
    · exact (mem_singleton_iff.mp hx).symm ▸ hc v
    · obtain ⟨i,hxi⟩ := mem_iUnion.mp hx
      exact hArmSub v i hxi
  have hIncN {e : β} (he : e ∈ E(N)) {x : α} (hx : G.Inc e x) : N.Inc e x := by
    obtain ⟨y,hLink⟩ := hx
    exact ⟨y,hNG.isLink_iff'.mpr ⟨hLink,he⟩⟩
  refine ⟨?_,?_,?_,?_,hModel.edge_injOn,?_,?_,?_⟩
  · intro v _
    exact ⟨c v,Or.inl (mem_singleton _)⟩
  · intro v _ x hx
    rcases hx with hx | hx
    · exact (mem_singleton_iff.mp hx).symm ▸ hcN v
    · obtain ⟨i,hxi⟩ := mem_iUnion.mp hx
      exact (hArmN v i).vertexSet_mono hxi
  · intro e he
    exact hChosenN e he
  · intro a ha b hb hab
    exact (hModel.vertex_disjoint a ha b hb hab).mono (hSub a) (hSub b)
  · intro v _ e he
    constructor
    · rintro ⟨w,heq,heMem⟩
      have hAdj : H.Adj v w := by
        have h : s(v,w) ∈ H.edgeSet := heq ▸ heMem
        exact h
      let i : H.neighborSet v := ⟨w,hAdj⟩
      have hPort : G.Inc (ηe e) (attach v i) := by
        rw [heq]
        exact hAttach v i
      exact ⟨attach v i,Or.inr (mem_iUnion_of_mem i (hPath v i).right_mem),hIncN
        (hChosenN e he) hPort⟩
    · rintro ⟨x,hx,y,hLink⟩
      exact (hModel.inc_iff v (mem_univ _) e he).mpr ⟨x,hSub v hx,y,hNG.isLink_mono hLink⟩
  · intro v _ e he
    constructor
    · rintro ⟨heq,heMem⟩
      have hMem : s(v,v) ∈ H.edgeSet := heq ▸ heMem
      have hAdj : H.Adj v v := hMem
      exact (hAdj.ne rfl).elim
    · intro hall
      apply (hModel.isLoopAt_iff v (mem_univ _) e he).mpr
      intro x hx
      exact hSub v (hall x (hIncN (hChosenN e he) hx))
  · intro v _
    let F := ηe '' H.edgeSet
    have hArmDel (i : H.neighborSet v) : arm v i ≤ N.deleteEdges F := by
      refine ⟨(hArmN v i).vertexSet_mono,?_⟩
      intro e x y hLink
      exact ⟨(hArmN v i).isLink_mono hLink,
        fun he => (disjoint_left.mp (hArmAvoid v i)) hLink.edge_mem he⟩
    let K := pathSystemGraph (N.deleteEdges F) {c v} (arm v)
    have hRoot : ({c v} : Set α) ⊆ V(N.deleteEdges F) := by
      rintro x hx
      exact (mem_singleton_iff.mp hx).symm ▸ hcN v
    refine ⟨K,pathSystemGraph_le hRoot hArmDel,rfl,?_⟩
    exact graphConnected_pathSystemGraph_star (fun i => (hPath v i).of_le (hArmDel i))

end GraphMinor.GM16
