/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.ModelBranchArms
import LeanPool.GraphMinor.GM09.Basic

/-!
# Choosing centres throughout a subcubic model

Apply the branch-arm construction at every vertex of the minor.
Centres in different branch sets are distinct. Every arm stays in
its own branch set and avoids every chosen model edge. These facts
are the global compatibility needed in XVI (4.2), page 54.
-/

public section
namespace GraphMinor.GM16
open Set Graph SimpleGraph Function GraphMinor.Surface GraphMinor.GM09
universe u v w

/-- The centres and arms for a finite simple subcubic minor model,
as used to construct the subdivision in XVI (4.2), page 54. -/
theorem exists_model_branch_centres {α : Type u} {β : Type v} {ν : Type w} [Finite ν]
    {H : SimpleGraph ν} {G : Graph α β} {ηv : ν → Set α} {ηe : Sym2 ν → β}
    (h : IsMinorModel (Graph.ofSimpleGraph H) G ηv ηe)
    (hDeg : ∀ v, (H.neighborSet v).ncard ≤ 3) :
    ∃ (c : ν → α) (attach : ∀ v, H.neighborSet v → α)
      (arm : ∀ v, H.neighborSet v → Graph α β),
      Injective c ∧
      (∀ v, c v ∈ ηv v) ∧
      (∀ v i, attach v i ∈ ηv v ∧ G.Inc (ηe s(v,i.val)) (attach v i)) ∧
      (∀ v i, IsGraphPathWithEnds G (arm v i) (c v) (attach v i)) ∧
      (∀ v i, V(arm v i) ⊆ ηv v ∧ Disjoint E(arm v i) (ηe '' H.edgeSet)) ∧
      (∀ v i j, i ≠ j → V(arm v i) ∩ V(arm v j) = {c v}) := by
  classical
  choose K hK hVK c attach arm hc hAttach hPath hInter using
    fun v => model_vertex_arms h v (Set.toFinite _) (hDeg v)
  have hCentres : ∀ v, c v ∈ ηv v := fun v => hVK v ▸ hc v
  have hKG : ∀ v, K v ≤ G := fun v => (hK v).trans Graph.deleteEdges_le
  refine ⟨c, attach, arm, ?_, hCentres, ?_, ?_, ?_, hInter⟩
  · intro v w heq
    by_contra hne
    have hd := h.vertex_disjoint v (mem_univ _) w (mem_univ _) hne
    exact (disjoint_left.mp hd) (hCentres v) (heq.symm ▸ hCentres w)
  · intro v i
    exact ⟨hVK v ▸ (hAttach v i).1, (hAttach v i).2⟩
  · intro v i
    exact (hPath v i).mono (hKG v)
  · intro v i
    refine ⟨?_, disjoint_left.mpr ?_⟩
    · intro x hx
      exact hVK v ▸ (hPath v i).le.vertexSet_mono hx
    · intro e he heChosen
      have hDel := ((hPath v i).le.trans (hK v)).edgeSet_mono he
      exact hDel.2 heChosen

/-- A chosen model edge joins any of its incident points in the two
corresponding branch sets. The branch sets make these points distinct. -/
theorem model_edge_between_branch_points {α : Type u} {β : Type v} {ν : Type w}
    {H : SimpleGraph ν} {G : Graph α β} {ηv : ν → Set α} {ηe : Sym2 ν → β}
    (h : IsMinorModel (Graph.ofSimpleGraph H) G ηv ηe)
    {u v : ν} (huv : H.Adj u v) {x y : α}
    (hx : x ∈ ηv u) (hy : y ∈ ηv v)
    (hix : G.Inc (ηe s(u, v)) x) (hiy : G.Inc (ηe s(u, v)) y) :
    G.IsLink (ηe s(u,v)) x y := by
  have hxy : x ≠ y := (h.vertex_disjoint u (mem_univ _) v (mem_univ _) huv.ne).ne_of_mem hx hy
  obtain ⟨z, hxz⟩ := hix
  have hyz : y = z := hiy.eq_of_isLink_of_ne_left hxz hxy.symm
  exact hyz.symm ▸ hxz

end GraphMinor.GM16
