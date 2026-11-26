/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section10a

/-!
# Graph Minors XX, Section 10, (10.2)

A shelled place has a hulled heart. Inside the heart every patch of an internal cell is free, by
(10.1), since each grouping there comes from connections of `sk(A⁻)`. For a border cell the disjoint
paths of the definition of shelled give the pairing `M_c`, and (10.1) makes it feasible.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set Topology GraphMinor.Surface GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v} {Ω : Type*}

section Pairing

variable {K : SimpleGraph α} {X Y : Set α} {ι : Type*} [Finite ι] {L : ι → PathFromTo K X Y}

omit [Finite ι] in
/-- Facts about the grouping given by `|X| = |Y| = |ι|` disjoint paths from `X` to `Y`. -/
theorem reachGrouping_paths
    (hL : Pairwise fun i j ↦ Disjoint {z | z ∈ (L i).walk.support} {z | z ∈ (L j).walk.support})
    (hX : X.Finite) (hY : Y.Finite) (hcX : X.ncard ≤ Nat.card ι) (hcY : Y.ncard ≤ Nat.card ι) :
    (∀ a b c, (reachGrouping (unionPaths L) (X ∪ Y)).Adj a b →
      (reachGrouping (unionPaths L) (X ∪ Y)).Adj a c → b = c) ∧
    ∀ D, IsComponent (reachGrouping (unionPaths L) (X ∪ Y)) D →
      (D.verts ∩ X).ncard = 1 ∧ (D.verts ∩ Y).ncard = 1 := by
  have hends : ∀ {z i}, z ∈ X ∪ Y → z ∈ (L i).walk.support → z = (L i).first ∨ z = (L i).last := by
    rintro z i (hz | hz) hi
    · exact Or.inl (eq_first_of_mem hL hX hcX hz hi)
    · exact Or.inr (eq_last_of_mem hL hY hcY hz hi)
  have hsame : ∀ {a b}, (reachGrouping (unionPaths L) (X ∪ Y)).Adj a b →
      ∃ i, a ∈ (L i).walk.support ∧ b ∈ (L i).walk.support := fun {a b} h ↦
    (eq_or_mem_support_of_reachable hL h.2.2.2).resolve_left h.2.2.1
  have huniq : ∀ {z i j}, z ∈ (L i).walk.support → z ∈ (L j).walk.support → i = j := by
    intro z i j hi hj
    by_contra hne
    exact Set.disjoint_left.mp (hL hne) hi hj
  constructor
  · intro a b c hab hac
    obtain ⟨i, hai, hbi⟩ := hsame hab
    obtain ⟨j, haj, hcj⟩ := hsame hac
    obtain rfl := huniq hai haj
    have hne₁ := hab.2.2.1
    have hne₂ := hac.2.2.1
    rcases hends hab.1 hai with h₁ | h₁ <;> rcases hends hab.2.1 hbi with h₂ | h₂ <;>
      rcases hends hac.2.1 hcj with h₃ | h₃
    all_goals first
      | exact h₂.trans h₃.symm
      | exact absurd (h₁.trans h₂.symm) hne₁
      | exact absurd (h₁.trans h₃.symm) hne₂
  · rintro D ⟨x, rfl⟩
    have hx : x.1 ∈ X ∪ Y := x.2
    have hxsupp : ∃ i, x.1 ∈ (L i).walk.support := by
      rcases hx with h | h
      · obtain ⟨i, hi⟩ := exists_first_eq hL hX hcX h
        exact ⟨i, hi ▸ first_mem_support i⟩
      · obtain ⟨i, hi⟩ := exists_last_eq hL hY hcY h
        exact ⟨i, hi ▸ last_mem_support i⟩
    obtain ⟨i, hi⟩ := hxsupp
    have hmem : ∀ {y}, y ∈ (component (reachGrouping (unionPaths L) (X ∪ Y)) x).verts →
        y ∈ (L i).walk.support := by
      intro y hy
      have hsc : sameComponent (reachGrouping (unionPaths L) (X ∪ Y)) x.1 y := by
        rw [sameComponent_iff_connectedIn]
        exact ⟨_, ⟨x, rfl⟩, self_mem_componentVerts _ x, hy⟩
      rcases eq_or_mem_support_of_reachable hL
        (reachable_of_sameComponent (H := reachGrouping (unionPaths L) (X ∪ Y))
          (fun a b h ↦ h.2.2.2) hsc) with h | ⟨j, h₁, h₂⟩
      · exact h ▸ hi
      · obtain rfl := huniq hi h₁
        exact h₂
    have hin : ∀ {y}, y ∈ X ∪ Y → y ∈ (L i).walk.support →
        y ∈ (component (reachGrouping (unionPaths L) (X ∪ Y)) x).verts := by
      intro y hy hyi
      have hsc : sameComponent (reachGrouping (unionPaths L) (X ∪ Y)) x.1 y := by
        by_cases hxy : x.1 = y
        · rw [← hxy, sameComponent_iff]
          exact ⟨x.2, x.2, SimpleGraph.Reachable.refl _⟩
        · exact sameComponent_of_adj ⟨hx, hy, hxy, reachable_of_mem_support i hi hyi⟩
      obtain ⟨hp, hq, hr⟩ := sameComponent_iff.mp hsc
      exact ⟨hq, hr⟩
    constructor
    · rw [show _ ∩ X = {(L i).first} from ?_, Set.ncard_singleton]
      ext y
      refine ⟨fun h ↦ eq_first_of_mem hL hX hcX h.2 (hmem h.1), ?_⟩
      rintro rfl
      exact ⟨hin (Or.inl (L i).first_mem) (first_mem_support i), (L i).first_mem⟩
    · rw [show _ ∩ Y = {(L i).last} from ?_, Set.ncard_singleton]
      ext y
      refine ⟨fun h ↦ eq_last_of_mem hL hY hcY h.2 (hmem h.1), ?_⟩
      rintro rfl
      exact ⟨hin (Or.inr (L i).last_mem) (last_mem_support i), (L i).last_mem⟩

end Pairing

section Cuff

variable {S : Type} [TopologicalSpace S]

/-- A node of a border cell lies on every cuff that the cell meets. -/
theorem node_mem_cuff (Γ : Painting S) {c : Set S} (hc : c ∈ Γ.C) {Θ : Set S} (hΘ : Θ ∈ cuffs S)
    (hcΘ : (c ∩ Θ).Nonempty) {n : S} (hn : n ∈ tilde c) : n ∈ Θ := by
  obtain ⟨x, hxc, hxΘ⟩ := hcΘ
  obtain ⟨p, hp, rfl⟩ := hΘ
  have hxbd : x ∈ bd S := connectedComponentIn_subset _ _ hxΘ
  obtain ⟨hcard, ⟨hL⟩, hends⟩ := Γ.border_cell c hc ⟨x, hxc, hxbd⟩
  have hnL : n ∈ closure c ∩ bd S := by
    rw [← hends] at hn
    obtain ⟨v, f, hf, -⟩ := hn
    exact hf ▸ (f 0).2
  have hconn : IsPreconnected (closure c ∩ bd S) := by
    have := (isPreconnected_univ (α := unitInterval)).image (fun t ↦ (hL t).1)
      (continuous_subtype_val.comp hL.continuous).continuousOn
    have himg : (fun t ↦ (hL t).1) '' univ = closure c ∩ bd S := by
      ext y
      constructor
      · rintro ⟨t, -, rfl⟩
        exact (hL t).2
      · intro hy
        exact ⟨hL.symm ⟨y, hy⟩, trivial, by simp⟩
    rwa [himg] at this
  rw [connectedComponentIn_eq hxΘ]
  exact hconn.subset_connectedComponentIn ⟨subset_closure hxc, hxbd⟩ inter_subset_right hnL

theorem exists_cuff_of_isBorder {c : Set S} (hb : Painting.IsBorder c) :
    ∃ Θ ∈ cuffs S, (c ∩ Θ).Nonempty := by
  obtain ⟨x, hxc, hx⟩ := hb
  exact ⟨_, ⟨x, hx, rfl⟩, x, hxc, mem_connectedComponentIn hx⟩

end Cuff

/-- A path from `X` to `Y` is also a path from a larger `X'` to a larger `Y'`, in a larger graph. -/
def _root_.GraphMinor.PathFromTo.widen {K K' : SimpleGraph α} {X Y X' Y' : Set α}
  (L : PathFromTo K X Y)
    (hK : K ≤ K') (hX : X ⊆ X') (hY : Y ⊆ Y') : PathFromTo K' X' Y' where
  first := L.first
  last := L.last
  walk := L.walk.mapLe hK
  isPath := L.isPath.mapLe hK
  first_mem := hX L.first_mem
  last_mem := hY L.last_mem

section Cell

variable {X : GradedSurface} {Γ : Painting X.S} {G : Hypergraph α β} (h : Hull Γ G)

/-- Disjoint paths between the two sides of a cell give a pairing as in the definition of hulled. -/
theorem isCellPairing_of_paths {K : SimpleGraph α} {n₁ n₂ : X.S} {r : ℕ}
  (hne : h.node n₁ ≠ h.node n₂)
    (hc₁ : h.border n₁ ⊆ G.vertexSet) (hc₂ : h.border n₂ ⊆ G.vertexSet)
    (hr₁ : (h.border n₁).ncard = r) (hr₂ : (h.border n₂).ncard = r)
    (L : Option (Fin r) → PathFromTo K (h.border n₁ ∪ {h.node n₁}) (h.border n₂ ∪ {h.node n₂}))
    (hL : Pairwise fun i j ↦ Disjoint {z | z ∈ (L i).walk.support} {z | z ∈ (L j).walk.support})
    (h₁ : (L none).first = h.node n₁) (h₂ : (L none).last = h.node n₂) :
    IsCellPairing h n₁ n₂ (reachGrouping (unionPaths L)
      ((h.border n₁ ∪ {h.node n₁}) ∪ (h.border n₂ ∪ {h.node n₂}))) := by
  have hf₁ : (h.border n₁).Finite := G.vertexSet_finite.subset hc₁
  have hf₂ : (h.border n₂).Finite := G.vertexSet_finite.subset hc₂
  have hcard : Nat.card (Option (Fin r)) = r + 1 := by simp
  have hX : (h.border n₁ ∪ {h.node n₁}).ncard ≤ Nat.card (Option (Fin r)) := by
    rw [hcard, ← hr₁, ← Set.ncard_singleton (h.node n₁)]
    exact Set.ncard_union_le _ _
  have hY : (h.border n₂ ∪ {h.node n₂}).ncard ≤ Nat.card (Option (Fin r)) := by
    rw [hcard, ← hr₂, ← Set.ncard_singleton (h.node n₂)]
    exact Set.ncard_union_le _ _
  obtain ⟨hp, hcomp⟩ := reachGrouping_paths hL (hf₁.union (finite_singleton _))
    (hf₂.union (finite_singleton _)) hX hY
  have hfin : ((h.border n₁ ∪ {h.node n₁}) ∪ (h.border n₂ ∪ {h.node n₂})).Finite :=
    (hf₁.union (finite_singleton _)).union (hf₂.union (finite_singleton _))
  refine ⟨(isPairing_iff hfin).mpr ⟨le_rfl, hp⟩, ?_, ?_, hcomp⟩
  · ext v
    change v ∈ (h.border n₁ ∪ {h.node n₁}) ∪ (h.border n₂ ∪ {h.node n₂}) ↔ _
    simp only [mem_union, mem_singleton_iff, mem_insert_iff]
    tauto
  · have hm₁ : ∀ z, z = (L none).first → z ∈ (L none).walk.support := by
      rintro _ rfl
      exact first_mem_support none
    have hm₂ : ∀ z, z = (L none).last → z ∈ (L none).walk.support := by
      rintro _ rfl
      exact last_mem_support none
    exact ⟨Or.inl (Or.inr rfl), Or.inr (Or.inr rfl), hne,
      reachable_of_mem_support none (hm₁ _ h₁.symm) (hm₂ _ h₂.symm)⟩

end Cell

theorem _root_.GraphMinor.PathFromTo.support_widen {K K' : SimpleGraph α} {X Y X' Y' : Set α}
  (L : PathFromTo K X Y)
    (hK : K ≤ K') (hX : X ⊆ X') (hY : Y ⊆ Y') :
    (L.widen hK hX hY).walk.support = L.walk.support :=
  SimpleGraph.Walk.support_mapLe_eq_support _ _

theorem _root_.GraphMinor.PathFromTo.edges_widen {K K' : SimpleGraph α} {X Y X' Y' : Set α}
  (L : PathFromTo K X Y)
    (hK : K ≤ K') (hX : X ⊆ X') (hY : Y ⊆ Y') :
    (L.widen hK hX hY).walk.edges = L.walk.edges :=
  SimpleGraph.Walk.edges_mapLe_eq_edges _ _

/-- The path of one edge joining `a` and `b` in the complete graph. -/
def edgePath {X Y : Set α} {a b : α} (hab : a ≠ b) (ha : a ∈ X) (hb : b ∈ Y) :
    PathFromTo (⊤ : SimpleGraph α) X Y where
  first := a
  last := b
  walk := SimpleGraph.Walk.cons hab SimpleGraph.Walk.nil
  isPath := by simpa [SimpleGraph.Walk.cons_isPath_iff] using hab
  first_mem := ha
  last_mem := hb

/-- A heart of a free patchwork: the patch of `e(A)` is free if every grouping comes from `sk(A⁻)`.
-/
theorem isFree_feasibleGroupings {P : UnlabeledPatchwork α β} (hfree : IsFree P)
    {A : RootedHypergraph α β} (hA : A.toHypergraph ≤ P.G.toHypergraph)
    (hK : ∀ K : (⊤ : SimpleGraph α).Subgraph, IsGrouping A.rootSet K → K.verts = A.rootSet →
      ∃ C : SimpleGraph α, C ≤ A.toHypergraph.skeleton ∧ ∀ x ∈ K.verts, ∀ y ∈ K.verts, x ≠ y →
        (C.Reachable x y ↔ K.Adj x y)) :
    (feasibleGroupings (P.restrict A)).IsFree := by
  intro K hg hv
  replace hv : K.verts = A.rootSet := hv
  obtain ⟨C, hC, hc⟩ := hK K hg hv
  have hfe := feasible_reachGrouping hfree hA hC
  have hKeq : K = reachGrouping C A.rootSet := by
    refine SimpleGraph.Subgraph.ext hv ?_
    ext x y
    constructor
    · intro h
      have h₁ := K.edge_vert h
      have h₂ := K.edge_vert h.symm
      have hne : x ≠ y := h.ne
      exact ⟨hv ▸ h₁, hv ▸ h₂, hne, (hc x h₁ y h₂ hne).mpr h⟩
    · rintro ⟨h₁, h₂, hne, hr⟩
      exact (hc x (hv ▸ h₁) y (hv ▸ h₂) hne).mp hr
  rw [hKeq]
  exact hfe

/-- Graph Minors XX, (10.2) (page 354): "Let* $(P, \mathcal{L})$ *be* $(\Sigma, \rho)$*-shelled.
Then it has a heart which is*
$(\Sigma, \rho)$*-hulled." -/
theorem theorem_10_2_proof {X : GradedSurface} {P : UnlabeledPatchwork α β} (hfree : IsFree P)
    (hroot : P.G.roots = []) {ℒ : Set (RootedHypergraph α β)} (hs : IsShelled X P ℒ) :
    ∃ P', HasPatchworkHeart P ℒ P' ∧ IsHulled X P' := by
  obtain ⟨hfine, e, P', Γ, h, hheart, hE, h3, hint, hbord⟩ := hs
  refine ⟨P', ⟨e, hheart⟩, Γ, h, ?_⟩
  have hcell : ∀ c ∈ Γ.C, ∃ A ∈ ℒ, h.cell c = e A := fun c hc ↦ by
    have h₁ := h.cell_bijOn.mapsTo hc
    rw [hE] at h₁
    obtain ⟨A, hA, hAe⟩ := h₁
    exact ⟨A, hA, hAe.symm⟩
  have hle : ∀ {A}, A ∈ ℒ → A.toHypergraph ≤ P.G.toHypergraph := fun hA ↦
    (hheart.isRootedLocation.isComplemented hA).le
  have hends : ∀ {A}, A ∈ ℒ → P'.G.ends (e A) = A.rootSet := fun hA ↦ hheart.ends_newEdge hA
  refine ⟨h3, fun c hc hb ↦ ?_, fun c hc hb n₁ hn₁ n₂ hn₂ hne ↦ ?_, ?_, ?_, fun c hc hb ↦ ?_⟩
  · obtain ⟨A, hA, hcA⟩ := hcell c hc
    rw [hcA, hheart.Δ_newEdge hA]
    obtain ⟨-, hK⟩ := hint c hc A hA hcA hb
    have hZ : A.rootSet = h.node '' tilde c := by
      rw [← hends hA, ← hcA, h.ends_internal c hc hb]
    exact isFree_feasibleGroupings hfree (hle hA) fun K hg hv ↦ hK K (hZ ▸ hg) (hZ ▸ hv)
  · obtain ⟨A, hA, hcA⟩ := hcell c hc
    obtain ⟨Θ, hΘ, hcΘ⟩ := exists_cuff_of_isBorder hb
    obtain ⟨L, hd, hnot, hor⟩ := hbord c hc A hA hcA Θ hΘ hcΘ n₁ hn₁ n₂ hn₂ hne
    have hN : ∀ {n}, n ∈ tilde c → n ∈ Γ.N := fun {n} hn ↦ by
      rw [← Γ.closure_inter c hc] at hn
      exact hn.2
    have hbdΘ : Θ ⊆ bd X.S := by
      obtain ⟨p, -, rfl⟩ := hΘ
      exact connectedComponentIn_subset _ _
    have hmem₁ : n₁ ∈ Γ.N ∩ Θ := ⟨hN hn₁, node_mem_cuff Γ hc hΘ hcΘ hn₁⟩
    have hmem₂ : n₂ ∈ Γ.N ∩ Θ := ⟨hN hn₂, node_mem_cuff Γ hc hΘ hcΘ hn₂⟩
    have hr₁ := h.border_ncard Θ hΘ n₁ hmem₁
    have hr₂ := h.border_ncard Θ hΘ n₂ hmem₂
    have hsub₁ := h.border_subset n₁ ⟨hmem₁.1, hbdΘ hmem₁.2⟩
    have hsub₂ := h.border_subset n₂ ⟨hmem₂.1, hbdΘ hmem₂.2⟩
    have hnode : h.node n₁ ≠ h.node n₂ := fun h' ↦ hne (h.node_injOn (hN hn₁) (hN hn₂) h')
    have hfint := (Γ.cell_size c hc).1
    have hb' : (c ∩ bd X.S).Nonempty := hb
    have hsize := (Γ.border_cell c hc hb').1
    have htilde : tilde c = {n₁, n₂} := (Set.eq_of_subset_of_ncard_le
      (by rintro x (rfl | rfl) <;> assumption) (by rw [Set.ncard_pair hne, hsize]) hfint).symm
    have hZ : A.rootSet = (h.border n₁ ∪ {h.node n₁}) ∪ (h.border n₂ ∪ {h.node n₂}) := by
      rw [← hends hA, ← hcA, h.ends_border c hc hb, htilde]
      ext v
      simp only [image_insert_eq, image_singleton, mem_union, mem_insert_iff, mem_singleton_iff,
        mem_iUnion, exists_prop, exists_eq_or_imp, exists_eq_left]
      tauto
    have hfe : ∀ {C : SimpleGraph α}, C ≤ A.toHypergraph.skeleton → reachGrouping C
        ((h.border n₁ ∪ {h.node n₁}) ∪ (h.border n₂ ∪ {h.node n₂})) ∈ P'.Δ (h.cell c) := by
      intro C hC
      have h₁ := feasible_reachGrouping hfree (hle hA) hC
      rw [hZ] at h₁
      rw [hcA, hheart.Δ_newEdge hA]
      exact h₁
    let W : Fin (X.ρ Θ) → PathFromTo A.toHypergraph.skeleton (h.border n₁ ∪ {h.node n₁})
        (h.border n₂ ∪ {h.node n₂}) := fun i ↦
      (L i).widen le_rfl subset_union_left subset_union_left
    have hWs : ∀ i, (W i).walk.support = (L i).walk.support := fun i ↦
      PathFromTo.support_widen _ _ subset_union_left subset_union_left
    rcases hor with ⟨L₀, hd₀⟩ | ⟨c', hc', hbc', h₁', h₂'⟩
    · let L' : Option (Fin (X.ρ Θ)) → PathFromTo A.toHypergraph.skeleton
          (h.border n₁ ∪ {h.node n₁}) (h.border n₂ ∪ {h.node n₂}) := fun o ↦
        o.elim (L₀.widen le_rfl subset_union_right subset_union_right) W
      have hLs : ∀ i, (L' (some i)).walk.support = (L i).walk.support := hWs
      have hLn : (L' none).walk.support = L₀.walk.support :=
        PathFromTo.support_widen _ _ subset_union_right subset_union_right
      have hdis : Pairwise fun i j ↦
          Disjoint {z | z ∈ (L' i).walk.support} {z | z ∈ (L' j).walk.support} := by
        rintro (_ | i) (_ | j) hij
        · exact absurd rfl hij
        · simp only [hLn, hLs]
          exact hd₀ j
        · simp only [hLn, hLs]
          exact (hd₀ i).symm
        · simp only [hLs]
          exact hd (fun h ↦ hij (congrArg some h))
      refine ⟨_, isCellPairing_of_paths h hnode hsub₁ hsub₂ hr₁ hr₂ L' hdis
        (mem_singleton_iff.mp L₀.first_mem) (mem_singleton_iff.mp L₀.last_mem), Or.inl
          (hfe unionPaths_le)⟩
    · let L' : Option (Fin (X.ρ Θ)) → PathFromTo (⊤ : SimpleGraph α)
          (h.border n₁ ∪ {h.node n₁}) (h.border n₂ ∪ {h.node n₂}) := fun o ↦
        o.elim (edgePath hnode (Or.inr rfl) (Or.inr rfl))
          fun i ↦ (W i).widen le_top subset_rfl subset_rfl
      have hLs : ∀ i, (L' (some i)).walk.support = (L i).walk.support := fun i ↦
        (PathFromTo.support_widen _ _ subset_rfl subset_rfl).trans (hWs i)
      have hLn : ∀ z, z ∈ (L' none).walk.support ↔ z = h.node n₁ ∨ z = h.node n₂ := fun z ↦ by
        change z ∈ [h.node n₁, h.node n₂] ↔ _
        simp
      have hdis : Pairwise fun i j ↦
          Disjoint {z | z ∈ (L' i).walk.support} {z | z ∈ (L' j).walk.support} := by
        rintro (_ | i) (_ | j) hij
        · exact absurd rfl hij
        · simp only [hLs]
          refine Set.disjoint_left.mpr fun z hz hzj ↦ ?_
          rcases (hLn z).mp hz with rfl | rfl
          · exact (hnot j).1 hzj
          · exact (hnot j).2 hzj
        · simp only [hLs]
          refine Set.disjoint_left.mpr fun z hzj hz ↦ ?_
          rcases (hLn z).mp hz with rfl | rfl
          · exact (hnot i).1 hzj
          · exact (hnot i).2 hzj
        · simp only [hLs]
          exact hd (fun h ↦ hij (congrArg some h))
      refine ⟨_, isCellPairing_of_paths h hnode hsub₁ hsub₂ hr₁ hr₂ L' hdis rfl rfl, Or.inr ?_⟩
      refine ⟨?_, c', hc', hbc', h₁', h₂'⟩
      have hdisW : Pairwise fun i j ↦
          Disjoint {z | z ∈ (W i).walk.support} {z | z ∈ (W j).walk.support} := by
        intro i j hij
        simp only [hWs]
        exact hd hij
      have heq : (reachGrouping (unionPaths L')
          ((h.border n₁ ∪ {h.node n₁}) ∪ (h.border n₂ ∪ {h.node n₂}))).deleteEdges
            {s(h.node n₁, h.node n₂)} = reachGrouping (unionPaths W)
          ((h.border n₁ ∪ {h.node n₁}) ∪ (h.border n₂ ∪ {h.node n₂})) := by
        refine SimpleGraph.Subgraph.ext rfl ?_
        ext x y
        rw [SimpleGraph.Subgraph.deleteEdges_adj]
        constructor
        · rintro ⟨⟨hx, hy, hxy, hr⟩, hns⟩
          refine ⟨hx, hy, hxy, ?_⟩
          obtain ⟨(_ | i), h₁, h₂⟩ := (eq_or_mem_support_of_reachable hdis hr).resolve_left hxy
          · exfalso
            apply hns
            rcases (hLn x).mp h₁ with rfl | rfl <;> rcases (hLn y).mp h₂ with rfl | rfl
            · exact absurd rfl hxy
            · rfl
            · exact Sym2.eq_swap
            · exact absurd rfl hxy
          · rw [hLs, ← hWs] at h₁ h₂
            exact reachable_of_mem_support i h₁ h₂
        · rintro ⟨hx, hy, hxy, hr⟩
          obtain ⟨i, h₁, h₂⟩ := (eq_or_mem_support_of_reachable hdisW hr).resolve_left hxy
          have h₁' := h₁
          have h₂' := h₂
          rw [hWs] at h₁' h₂'
          have hx' : x ∈ (L' (some i)).walk.support := by rw [hLs]; exact h₁'
          have hy' : y ∈ (L' (some i)).walk.support := by rw [hLs]; exact h₂'
          refine ⟨⟨hx, hy, hxy, reachable_of_mem_support (some i) hx' hy'⟩, ?_⟩
          intro hs
          have hs' := Sym2.eq_iff.mp hs
          rcases hs' with ⟨rfl, -⟩ | ⟨rfl, -⟩
          · exact (hnot i).1 h₁'
          · exact (hnot i).2 h₁'
      rw [heq]
      exact hfe (unionPaths_le)
  · rw [hheart.roots_eq, hroot]
  · rw [hheart.dom_eq_image hfine, hheart.edgeSet_eq_image hfine]
  · obtain ⟨A, hA, hcA⟩ := hcell c hc
    rw [hcA, hheart.μ_newEdge hA]
    exact (hint c hc A hA hcA hb).1

end GraphMinor.GM20
