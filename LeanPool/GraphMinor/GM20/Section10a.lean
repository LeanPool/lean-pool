/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section7b

/-!
# Graph Minors XX, Section 10, (10.1)

For a free patchwork and a subgraph `C` of the 1-skeleton there is a realization that has exactly
the
connections of `C`. So every grouping given by the connections of such a `C` is feasible. This is
what (10.2) uses.

The second part of the file proves that disjoint paths between the two sides of a border cell give
the pairing that the definition of hulled patchworks asks for.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v} {Ω : Type*}

/-- The grouping on `U` in which two distinct vertices are adjacent if `C` connects them. -/
def reachGrouping (C : SimpleGraph α) (U : Set α) : (⊤ : SimpleGraph α).Subgraph where
  verts := U
  Adj x y := x ∈ U ∧ y ∈ U ∧ x ≠ y ∧ C.Reachable x y
  adj_sub h := h.2.2.1
  edge_vert h := h.1
  symm := ⟨fun _ _ h ↦ ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.symm⟩⟩

theorem isGrouping_reachGrouping (C : SimpleGraph α) (U : Set α) :
    IsGrouping U (reachGrouping C U) :=
  isGrouping_iff.mpr ⟨le_rfl, fun _ _ _ hac hab hbc ↦
    ⟨hab.1, hbc.2.1, hac, hab.2.2.2.trans hbc.2.2.2⟩⟩

theorem reachable_of_sameComponent {H : (⊤ : SimpleGraph α).Subgraph} {C : SimpleGraph α}
    (h : ∀ a b, H.Adj a b → C.Reachable a b) {x y : α} (hxy : sameComponent H x y) :
    C.Reachable x y := by
  obtain ⟨hp, hq, hr⟩ := sameComponent_iff.mp hxy
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  suffices ∀ z : H.verts, Relation.ReflTransGen H.coe.Adj ⟨x, hp⟩ z → C.Reachable x z.1 from
    this ⟨y, hq⟩ hr
  intro z hz
  induction hz with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail a b _ hab ih => exact ih.trans (h a.1 b.1 hab)

/-- Graph Minors XX, (10.1) (page 353): "Let* $P = (G, \mu, \Delta)$ *be a free patchwork, and let*
$C$ *be a subgraph of* $sk(G)$.
*Then there is a realization* $H$ *of* $P$ *such that for all* $x, y \in V(C)$, $x$ *and*
$y$ *are connected in* $C$ *if and only if they are connected in* $H$." A vertex of `G` outside
`V(C)` is
here a vertex of `C` with no edges, so the statement covers all of `V(G)`. -/
theorem theorem_10_1_proof {P : Patchwork Ω α β} (hfree : IsFree P) {C : SimpleGraph α}
    (hC : C ≤ P.G.toHypergraph.skeleton) :
    ∃ H, P.IsRealization H ∧ ∀ x ∈ P.G.vertexSet, ∀ y ∈ P.G.vertexSet,
      sameComponent H x y ↔ C.Reachable x y := by
  let δ : β → (⊤ : SimpleGraph α).Subgraph := fun e ↦ reachGrouping C (P.G.ends e)
  have hδ : ∀ e ∈ P.G.edgeSet, δ e ∈ P.Δ e := fun e he ↦ by
    refine hfree e he _ ?_ ?_
    · rw [P.Δ_verts e he]
      exact isGrouping_reachGrouping C _
    · rw [P.Δ_verts e he]
      rfl
  have hreal : P.IsRealization (realizationOf P.G.toHypergraph δ) := ⟨δ, hδ, rfl⟩
  refine ⟨_, hreal, fun x hx y hy ↦ ⟨reachable_of_sameComponent fun a b hab ↦ ?_, fun h ↦ ?_⟩⟩
  · obtain ⟨e, -, h₁⟩ := realizationOf_adj.mp hab
    exact h₁.2.2.2
  · have hv : (realizationOf P.G.toHypergraph δ).verts = P.G.vertexSet := hreal.verts_eq
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact sameComponent_iff.mpr ⟨hv ▸ hx, hv ▸ hx, SimpleGraph.Reachable.refl _⟩
    | @tail a b _ hab ih =>
      obtain ⟨hne, e, h₁, h₂⟩ := hC hab
      have ih' := ih
      refine (ih' (P.G.vertex_mem_of_inc h₁)).trans (sameComponent_of_adj ?_)
      exact realizationOf_adj.mpr ⟨e, P.G.edge_mem_of_inc h₁, h₁, h₂, hne, hab.reachable⟩

/-- A grouping given by the connections of a subgraph of `sk(A⁻)` is feasible in `P|A`. -/
theorem feasible_reachGrouping {P : Patchwork Ω α β} (hfree : IsFree P) {A : RootedHypergraph α β}
    (hA : A.toHypergraph ≤ P.G.toHypergraph) {C : SimpleGraph α}
    (hC : C ≤ A.toHypergraph.skeleton) :
    IsFeasibleGrouping (P.restrict A) (reachGrouping C A.rootSet) := by
  obtain ⟨H, hH, hc⟩ := theorem_10_1_proof (isFree_restrict hfree hA) hC
  refine ⟨isGrouping_reachGrouping C _, rfl, H, hH, fun x hx y hy hne ↦ ?_⟩
  rw [← sameComponent_iff_connectedIn, hc x (A.roots_subset x hx) y (A.roots_subset y hy)]
  exact ⟨fun h ↦ ⟨hx, hy, hne, h⟩, fun h ↦ h.2.2.2⟩

/-! ### Disjoint paths give a pairing -/

section Paths

variable {K : SimpleGraph α} {X Y : Set α} {ι : Type*}

/-- The union of a family of paths, as a graph on `α`. -/
def unionPaths (L : ι → PathFromTo K X Y) : SimpleGraph α where
  Adj x y := ∃ i, s(x, y) ∈ (L i).walk.edges
  symm := ⟨fun x y ⟨i, h⟩ ↦ ⟨i, by rwa [Sym2.eq_swap]⟩⟩
  loopless := ⟨fun x ⟨i, h⟩ ↦ (L i).walk.adj_of_mem_edges h |>.ne rfl⟩

variable {L : ι → PathFromTo K X Y}

theorem unionPaths_le : unionPaths L ≤ K := fun _ _ ⟨i, h⟩ ↦ (L i).walk.adj_of_mem_edges h

/-- Two vertices of one path are connected in the union. -/
theorem reachable_of_mem_support (i : ι) {x y : α} (hx : x ∈ (L i).walk.support)
    (hy : y ∈ (L i).walk.support) : (unionPaths L).Reachable x y := by
  classical
  have hfirst : ∀ z ∈ (L i).walk.support, (unionPaths L).Reachable (L i).first z := by
    intro z hz
    have hmem : ∀ e ∈ ((L i).walk.takeUntil z hz).edges, e ∈ (unionPaths L).edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | _ a b =>
        exact ⟨i, (L i).walk.edges_takeUntil_subset_edges hz he⟩
    exact ⟨((L i).walk.takeUntil z hz).transfer _ hmem⟩
  exact (hfirst x hx).symm.trans (hfirst y hy)

/-- Vertices connected in the union of disjoint paths are on one path. -/
theorem eq_or_mem_support_of_reachable
    (hL : Pairwise fun i j ↦ Disjoint {z | z ∈ (L i).walk.support} {z | z ∈ (L j).walk.support})
    {x y : α} (h : (unionPaths L).Reachable x y) :
    x = y ∨ ∃ i, x ∈ (L i).walk.support ∧ y ∈ (L i).walk.support := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl rfl
  | @tail a b _ hab ih =>
    obtain ⟨j, hj⟩ := hab
    have ha := (L j).walk.fst_mem_support_of_mem_edges hj
    have hb := (L j).walk.snd_mem_support_of_mem_edges hj
    rcases ih with rfl | ⟨i, hx, hai⟩
    · exact Or.inr ⟨j, ha, hb⟩
    · have hij : i = j := by
        by_contra hne
        exact Set.disjoint_left.mp (hL hne) hai ha
      subst hij
      exact Or.inr ⟨i, hx, hb⟩

theorem first_mem_support (i : ι) : (L i).first ∈ (L i).walk.support :=
  (L i).walk.start_mem_support

theorem last_mem_support (i : ι) : (L i).last ∈ (L i).walk.support :=
  (L i).walk.end_mem_support

/-- With as many disjoint paths as `X` has members, every member of `X` starts a path. -/
theorem exists_first_eq
    (hL : Pairwise fun i j ↦ Disjoint {z | z ∈ (L i).walk.support} {z | z ∈ (L j).walk.support})
    (hX : X.Finite) (hcard : X.ncard ≤ Nat.card ι) {x : α} (hx : x ∈ X) :
    ∃ i, (L i).first = x := by
  have hinj : Function.Injective fun i ↦ (L i).first := fun i j h ↦ by
    by_contra hne
    refine Set.disjoint_left.mp (hL hne) (first_mem_support i) ?_
    change (L i).first ∈ (L j).walk.support
    rw [show (L i).first = (L j).first from h]
    exact first_mem_support j
  have hsub : range (fun i ↦ (L i).first) ⊆ X := by
    rintro _ ⟨i, rfl⟩
    exact (L i).first_mem
  have hc : (range fun i ↦ (L i).first).ncard = Nat.card ι := by
    rw [← image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ]
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hc]; exact hcard) hX
  rw [← heq] at hx
  exact hx

theorem exists_last_eq
    (hL : Pairwise fun i j ↦ Disjoint {z | z ∈ (L i).walk.support} {z | z ∈ (L j).walk.support})
    (hY : Y.Finite) (hcard : Y.ncard ≤ Nat.card ι) {x : α} (hx : x ∈ Y) :
    ∃ i, (L i).last = x := by
  have hinj : Function.Injective fun i ↦ (L i).last := fun i j h ↦ by
    by_contra hne
    refine Set.disjoint_left.mp (hL hne) (last_mem_support i) ?_
    change (L i).last ∈ (L j).walk.support
    rw [show (L i).last = (L j).last from h]
    exact last_mem_support j
  have hsub : range (fun i ↦ (L i).last) ⊆ Y := by
    rintro _ ⟨i, rfl⟩
    exact (L i).last_mem
  have hc : (range fun i ↦ (L i).last).ncard = Nat.card ι := by
    rw [← image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ]
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hc]; exact hcard) hY
  rw [← heq] at hx
  exact hx

/-- A vertex of `X` on a path is the first vertex of that path, when every member of `X` starts a
path. -/
theorem eq_first_of_mem
    (hL : Pairwise fun i j ↦ Disjoint {z | z ∈ (L i).walk.support} {z | z ∈ (L j).walk.support})
    (hX : X.Finite) (hcard : X.ncard ≤ Nat.card ι) {x : α} (hx : x ∈ X) {i : ι}
    (hi : x ∈ (L i).walk.support) : x = (L i).first := by
  obtain ⟨j, rfl⟩ := exists_first_eq hL hX hcard hx
  have hij : j = i := by
    by_contra hne
    exact Set.disjoint_left.mp (hL hne) (first_mem_support j) hi
  rw [hij]

theorem eq_last_of_mem
    (hL : Pairwise fun i j ↦ Disjoint {z | z ∈ (L i).walk.support} {z | z ∈ (L j).walk.support})
    (hY : Y.Finite) (hcard : Y.ncard ≤ Nat.card ι) {x : α} (hx : x ∈ Y) {i : ι}
    (hi : x ∈ (L i).walk.support) : x = (L i).last := by
  obtain ⟨j, rfl⟩ := exists_last_eq hL hY hcard hx
  have hij : j = i := by
    by_contra hne
    exact Set.disjoint_left.mp (hL hne) (last_mem_support j) hi
  rw [hij]

end Paths

end GraphMinor.GM20
