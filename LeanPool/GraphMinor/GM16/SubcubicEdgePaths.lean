/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.ModelBranchCentres
public import LeanPool.GraphMinor.GM16.TwoBranchArmsPath
public import LeanPool.GraphMinor.GM16.GraphPathSystemUnion
import LeanPool.GraphMinor.GM16.BranchArmsInPathSystem
import LeanPool.GraphMinor.GM16.ModelFromBranchArms
import LeanPool.GraphMinor.GM16.SubcubicArmIntersections
import LeanPool.GraphMinor.GM09.Basic

/-!
# The edge paths of a subcubic minor

Construct a branch centre and arms at every vertex. For each source
edge, join the two corresponding arms through its chosen model edge.
The resulting path has exactly the vertices of those two arms. Paths
for different source edges meet only at branch centres. This proves
the path-system part of the subdivision assertion in XVI (4.2), page 54.
-/

public section
namespace GraphMinor.GM16
open Set Graph SimpleGraph Function GraphMinor.Surface GraphMinor.GM09
universe u v w

/-- Construct the paths replacing all edges of a finite simple
subcubic minor in XVI (4.2), page 54. -/
theorem exists_subcubic_edge_paths_with_minor {α : Type u} {β : Type v} {ν : Type w} [Finite ν]
    {H : SimpleGraph ν} {G : Graph α β} {ηv : ν → Set α} {ηe : Sym2 ν → β}
    (h : IsMinorModel (Graph.ofSimpleGraph H) G ηv ηe)
    (hDeg : ∀ v, (H.neighborSet v).ncard ≤ 3) :
    ∃ (c : ν → α) (P : H.edgeSet → Graph α β),
      Injective c ∧ (∀ v, c v ∈ ηv v) ∧
      (∀ e : H.edgeSet, ∃ a b, e.val = s(a,b) ∧ H.Adj a b ∧
        IsGraphPathWithEnds G (P e) (c a) (c b) ∧ ηe e.val ∈ E(P e) ∧
        V(P e) ∩ range c = {c a,c b}) ∧
      (∀ e f : H.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c) ∧
      ∃ ηv' : ν → Set α, IsMinorModel (Graph.ofSimpleGraph H)
        (pathSystemGraph G (range c) P) ηv' ηe := by
  classical
  obtain ⟨c, attach, arm, hcInj, hc, hAttach, hPath, hSub, hInter⟩ := exists_model_branch_centres h
    hDeg
  have hEnds (e : H.edgeSet) : ∃ a b, e.val = s(a,b) ∧ H.Adj a b := by
    obtain ⟨a, b, heq, he⟩ := (Graph.ofSimpleGraph H).exists_isLink_of_mem_edgeSet e.property
    exact ⟨a, b, heq, by rw [heq] at he; exact he⟩
  choose a b hEq hAdj using hEnds
  have hPaths (e : H.edgeSet) : ∃ Q : Graph α β,
      IsGraphPathWithEnds G Q (c (a e)) (c (b e)) ∧
      V(Q) = V(arm (a e) ⟨b e,hAdj e⟩) ∪ V(arm (b e) ⟨a e,(hAdj e).symm⟩) ∧
      E(Q) = (E(arm (a e) ⟨b e,hAdj e⟩) ∪ {ηe e.val}) ∪
        E(arm (b e) ⟨a e,(hAdj e).symm⟩) := by
    have hDisj : Disjoint V(arm (a e) ⟨b e,hAdj e⟩) V(arm (b e) ⟨a e,(hAdj e).symm⟩) :=
      (h.vertex_disjoint _ (mem_univ _) _ (mem_univ _) (hAdj e).ne).mono
        (hSub _ _).1 (hSub _ _).1
    have hi := (hAttach (b e) ⟨a e,(hAdj e).symm⟩).2
    have hswap : s(b e,a e) = s(a e,b e) := Sym2.eq_swap
    rw [hswap] at hi
    have hLink := model_edge_between_branch_points h (hAdj e)
      (hAttach (a e) ⟨b e,hAdj e⟩).1 (hAttach (b e) ⟨a e,(hAdj e).symm⟩).1
      (hAttach (a e) ⟨b e,hAdj e⟩).2 hi
    rw [← hEq e] at hLink
    exact exists_path_between_branch_arms (hPath _ _) (hPath _ _) hDisj hLink
  choose P hP hVP hEP using hPaths
  have hAtBranch (e : H.edgeSet) (x : α) (hx : x ∈ V(P e)) :
      x ∈ ηv (a e) ∪ ηv (b e) := by
    rw [hVP e] at hx
    exact hx.elim (fun h => Or.inl ((hSub _ _).1 h)) (fun h => Or.inr ((hSub _ _).1 h))
  have hRange (e : H.edgeSet) : V(P e) ∩ range c = {c (a e),c (b e)} := by
    apply Subset.antisymm
    · rintro x ⟨hxP, z, rfl⟩
      rcases hAtBranch e (c z) hxP with hx | hx
      · by_cases hza : z = a e
        · exact hza ▸ mem_insert _ _
        · exact ((disjoint_left.mp (h.vertex_disjoint z (mem_univ _) (a e) (mem_univ _) hza))
            (hc z) hx).elim
      · by_cases hzb : z = b e
        · exact hzb ▸ mem_insert_of_mem _ (mem_singleton _)
        · exact ((disjoint_left.mp (h.vertex_disjoint z (mem_univ _) (b e) (mem_univ _) hzb))
            (hc z) hx).elim
    · intro x hx
      rcases hx with rfl | hx
      · exact ⟨(hP e).left_mem, mem_range_self _⟩
      · rw [mem_singleton_iff] at hx
        subst x
        exact ⟨(hP e).right_mem, mem_range_self _⟩
  have hPG : ∀ e, P e ≤ G := fun e => (hP e).le
  have hCG : range c ⊆ V(G) := by
    rintro x ⟨v,rfl⟩
    exact h.vertex_subset v (mem_univ _) (hc v)
  have hNG := pathSystemGraph_le hCG hPG
  have hcN (v : ν) : c v ∈ V(pathSystemGraph G (range c) P) := Or.inl (mem_range_self v)
  obtain ⟨hArmN,hChosenN⟩ := branch_arms_le_pathSystemGraph (range c) arm P a b ηe hEq hAdj
    (fun v i => (hPath v i).le) hPG hVP hEP
  have hModelN := minorModel_from_branch_arms h hNG c attach arm hc hcN
    (fun v i => (hAttach v i).2) hPath hArmN
    (fun v i => (hSub v i).1) (fun v i => (hSub v i).2) hChosenN
  refine ⟨c, P, hcInj, hc, ?_, ?_,_,hModelN⟩
  · intro e
    refine ⟨a e, b e, hEq e, hAdj e, hP e, ?_, hRange e⟩
    rw [hEP e]
    exact Or.inl (Or.inr (mem_singleton _))
  · intro e f hne x hx
    have hEdgeNe : e.val ≠ f.val := fun heq => hne (Subtype.ext heq)
    have h1 : s(a e,b e) ≠ s(a f,b f) := fun heq => hEdgeNe ((hEq e).trans (heq.trans (hEq f).symm))
    have h2 : s(a e,b e) ≠ s(b f,a f) := by
      rw [Sym2.eq_swap (a := b f) (b := a f)]
      exact h1
    have h3 : s(b e,a e) ≠ s(a f,b f) := by
      rw [Sym2.eq_swap (a := b e) (b := a e)]
      exact h1
    have h4 : s(b e,a e) ≠ s(b f,a f) := by
      rw [Sym2.eq_swap (a := b e) (b := a e)]
      exact h2
    rw [hVP e] at hx
    rw [hVP f] at hx
    rcases hx with ⟨hx₁ | hx₁, hx₂ | hx₂⟩
    · exact arm_intersection_subset_centres h c arm (fun v i => (hSub v i).1) hInter
        (hAdj e) (hAdj f) h1 ⟨hx₁,hx₂⟩
    · exact arm_intersection_subset_centres h c arm (fun v i => (hSub v i).1) hInter
        (hAdj e) (hAdj f).symm h2 ⟨hx₁,hx₂⟩
    · exact arm_intersection_subset_centres h c arm (fun v i => (hSub v i).1) hInter
        (hAdj e).symm (hAdj f) h3 ⟨hx₁,hx₂⟩
    · exact arm_intersection_subset_centres h c arm (fun v i => (hSub v i).1) hInter
        (hAdj e).symm (hAdj f).symm h4 ⟨hx₁,hx₂⟩

/-- The replacing-path part of the subcubic subdivision construction. -/
theorem exists_subcubic_edge_paths {α : Type u} {β : Type v} {ν : Type w} [Finite ν]
    {H : SimpleGraph ν} {G : Graph α β} {ηv : ν → Set α} {ηe : Sym2 ν → β}
    (h : IsMinorModel (Graph.ofSimpleGraph H) G ηv ηe)
    (hDeg : ∀ v, (H.neighborSet v).ncard ≤ 3) :
    ∃ (c : ν → α) (P : H.edgeSet → Graph α β),
      Injective c ∧ (∀ v, c v ∈ ηv v) ∧
      (∀ e : H.edgeSet, ∃ a b, e.val = s(a,b) ∧ H.Adj a b ∧
        IsGraphPathWithEnds G (P e) (c a) (c b) ∧ ηe e.val ∈ E(P e) ∧
        V(P e) ∩ range c = {c a,c b}) ∧
      (∀ e f : H.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c) := by
  obtain ⟨c,P,hcInj,hc,hPaths,hInter,_⟩ := exists_subcubic_edge_paths_with_minor h hDeg
  exact ⟨c,P,hcInj,hc,hPaths,hInter⟩

end GraphMinor.GM16
