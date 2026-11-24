/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.RuralExtend

/-!
# Graph Minors IX, (6.1): smaller societies

The proof of (6.1) takes a counterexample with `|V(G)| + |E(G)|` as small as possible and shows that
`G` is simple, that no vertex of `ΩBar` is isolated, and that consecutive vertices of `ΩBar` are not
adjacent. Each time the paper says that a smaller society is a smaller counterexample. To check
this we must see that the smaller society keeps the connectivity and has no new crooked
transaction, and that a composition of the smaller society with a rural neighborhood gives one for
`(G, Ω)` with no larger sophistication. That is what this file does.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM06

universe u v

variable {α : Type u} {β : Type v}

/-- The subgraph `H` of `G` with the edge `e` added. -/
def addEdgeTo (G H : Graph α β) (e : β) : Graph α β := (G.induce V(H)).restrict (insert e E(H))

section AddEdge

variable {G H : Graph α β} {e : β} {u w : α}

theorem addEdgeTo_le (hH : H ≤ G) : addEdgeTo G H e ≤ G :=
  restrict_le.trans (G.induce_le hH.vertexSet_mono)

@[simp] theorem vertexSet_addEdgeTo : V(addEdgeTo G H e) = V(H) := by simp [addEdgeTo]

theorem edgeSet_addEdgeTo (hH : H ≤ G) (hl : G.IsLink e u w) (hu : u ∈ V(H)) (hw : w ∈ V(H)) :
    E(addEdgeTo G H e) = insert e E(H) := by
  unfold addEdgeTo
  rw [edgeSet_restrict, inter_eq_right]
  rintro f (rfl | hf)
  · exact ⟨u, w, hl, hu, hw⟩
  · obtain ⟨x, y, hxy⟩ := H.exists_isLink_of_mem_edgeSet hf
    exact ⟨x, y, hxy.mono hH, hxy.left_mem, hxy.right_mem⟩

theorem le_addEdgeTo (hH : H ≤ G) : H ≤ addEdgeTo G H e := by
  refine ⟨by simp, fun {f x y} hl => ?_⟩
  exact ⟨Or.inr hl.edge_mem, hl.mono hH, hl.left_mem, hl.right_mem⟩

theorem isLink_addEdgeTo (hl : G.IsLink e u w) (hu : u ∈ V(H)) (hw : w ∈ V(H)) :
    (addEdgeTo G H e).IsLink e u w := ⟨Or.inl rfl, hl, hu, hw⟩

/-- A separation of `G` with `e` deleted gives one of `G`, if the ends of `e` are in the first
side. -/
theorem IsGraphSeparation.addEdge_left {G' G₁ G₂ : Graph α β} (h : IsGraphSeparation G' G₁ G₂)
    (hle : G' ≤ G) (hV : V(G') = V(G)) (hE : E(G) = insert e E(G')) (he : e ∉ E(G'))
    (hl : G.IsLink e u w) (hu : u ∈ V(G₁)) (hw : w ∈ V(G₁)) :
    IsGraphSeparation G (addEdgeTo G G₁ e) G₂ := by
  obtain ⟨h₁, h₂, hVu, hEu, hd⟩ := h
  have h₁G := h₁.trans hle
  refine ⟨addEdgeTo_le h₁G, h₂.trans hle, by rw [vertexSet_addEdgeTo, hVu, hV], ?_, ?_⟩
  · rw [edgeSet_addEdgeTo h₁G hl hu hw, insert_union, hEu, hE]
  · rw [edgeSet_addEdgeTo h₁G hl hu hw, disjoint_insert_left]
    exact ⟨fun h' => he (h₂.edgeSet_mono h'), hd⟩

theorem IsGraphSeparation.addEdge_right {G' G₁ G₂ : Graph α β} (h : IsGraphSeparation G' G₁ G₂)
    (hle : G' ≤ G) (hV : V(G') = V(G)) (hE : E(G) = insert e E(G')) (he : e ∉ E(G'))
    (hl : G.IsLink e u w) (hu : u ∈ V(G₂)) (hw : w ∈ V(G₂)) :
    IsGraphSeparation G G₁ (addEdgeTo G G₂ e) :=
  IsGraphSeparation.symm
    (IsGraphSeparation.addEdge_left (IsGraphSeparation.symm h) hle hV hE he hl hu hw)

/-- If `e` is a loop or parallel to an edge of `H`, then a path of `H` with `e` added may be
replaced by a path of `H` with the same ends and the same vertices. -/
theorem exists_path_of_addEdge {G' H' P : Graph α β} {a b : α} (hle : H' ≤ G') (hV : V(H') = V(G'))
    (hE : E(G') = insert e E(H')) (hl : G'.IsLink e u w) (hred : u = w ∨ ∃ f, H'.IsLink f u w)
    (hP : IsGraphPathWithEnds G' P a b) :
    ∃ P', IsGraphPathWithEnds H' P' a b ∧ V(P') = V(P) := by
  obtain ⟨hPG, W, hs, hVP, -⟩ := hP
  have key : ∀ {x y : α} (W : GraphWalk P x y), W.IsSimple →
      ∃ W' : GraphWalk H' x y, W'.support = W.support := by
    intro x y W
    induction W with
    | nil hv =>
      intro _
      exact ⟨.nil (hV ▸ hPG.vertexSet_mono hv), rfl⟩
    | @cons x z y f hlink rest ih =>
      intro hs'
      have hnd : x ∉ rest.support ∧ rest.IsSimple := by
        have : (x :: rest.support).Nodup := hs'
        exact ⟨(List.nodup_cons.mp this).1, (List.nodup_cons.mp this).2⟩
      obtain ⟨R, hR⟩ := ih hnd.2
      have hlG : G'.IsLink f x z := hlink.mono hPG
      have hlk : ∃ g, H'.IsLink g x z := by
        by_cases hfe : f = e
        · subst hfe
          have hxz : x ≠ z := fun h => hnd.1 (h ▸ GraphWalk.start_mem_support rest)
          rcases hred with rfl | ⟨g, hg⟩
          · rcases hlG.eq_and_eq_or_eq_and_eq hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
              exact (hxz rfl).elim
          · rcases hlG.eq_and_eq_or_eq_and_eq hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact ⟨g, hg⟩
            · exact ⟨g, hg.symm⟩
        · have hfH : f ∈ E(H') := by
            have := hlG.edge_mem
            rw [hE] at this
            exact this.resolve_left hfe
          exact ⟨f, (hle.isLink_iff hfH).mpr hlG⟩
      obtain ⟨g, hg⟩ := hlk
      exact ⟨.cons hg R, by simp only [GraphWalk.support, hR]⟩
  obtain ⟨W', hW'⟩ := key W hs
  have hs' : W'.IsSimple := by
    change W'.support.Nodup
    rw [hW']
    exact hs
  refine ⟨walkSubgraph W', isGraphPathWithEnds_walkSubgraph hs', ?_⟩
  rw [vertexSet_walkSubgraph, hVP, hW']

end AddEdge

/-- The subgraph `H` of `G` with the vertex `v` added. -/
def addVertexTo (G H : Graph α β) (v : α) : Graph α β :=
  (G.induce (insert v V(H))).restrict E(H)

section AddVertex

variable {G H : Graph α β} {v : α}

theorem addVertexTo_le (hH : H ≤ G) (hv : v ∈ V(G)) : addVertexTo G H v ≤ G :=
  restrict_le.trans (G.induce_le (insert_subset hv hH.vertexSet_mono))

@[simp] theorem vertexSet_addVertexTo : V(addVertexTo G H v) = insert v V(H) := by
  simp [addVertexTo]

theorem edgeSet_addVertexTo (hH : H ≤ G) : E(addVertexTo G H v) = E(H) := by
  unfold addVertexTo
  rw [edgeSet_restrict, inter_eq_right]
  intro f hf
  obtain ⟨x, y, hxy⟩ := H.exists_isLink_of_mem_edgeSet hf
  exact ⟨x, y, hxy.mono hH, Or.inr hxy.left_mem, Or.inr hxy.right_mem⟩

theorem le_addVertexTo (hH : H ≤ G) : H ≤ addVertexTo G H v := by
  refine ⟨fun x hx => by simp [hx], fun {f x y} hl => ?_⟩
  exact ⟨hl.edge_mem, hl.mono hH, Or.inr hl.left_mem, Or.inr hl.right_mem⟩

end AddVertex

namespace Neighborhood

/-- The neighborhood `N` with the edge `e` of `G` added. -/
def addEdge (N : Neighborhood α β) (G : Graph α β) (e : β) : Neighborhood α β where
  G := addEdgeTo G N.G e
  Ω := N.Ω
  Ω₀ := N.Ω₀
  finite_V := by simpa using N.finite_V
  finite_E := (N.finite_E.insert e).subset inter_subset_right
  bar_subset := by simpa using N.bar_subset
  bar₀_subset := by simpa using N.bar₀_subset

end Neighborhood

namespace Society

variable (S : Society α β)

/-- The society `S` with the edge `e` deleted. -/
def deleteEdge (e : β) : Society α β :=
  ⟨S.G.restrict (E(S.G) \ {e}), S.Ω, S.finite_V, S.finite_E.subset restrict_le.edgeSet_mono,
    S.bar_subset⟩

/-- The society on the subgraph `G` with the edge `e` of `G'` added. -/
def addEdge (G : Graph α β) (e : β) : Society α β where
  G := addEdgeTo G S.G e
  Ω := S.Ω
  finite_V := by simpa using S.finite_V
  finite_E := (S.finite_E.insert e).subset inter_subset_right
  bar_subset := by simpa using S.bar_subset

variable {S}

theorem deleteEdge_le (e : β) : (S.deleteEdge e).G ≤ S.G := restrict_le

theorem vertexSet_deleteEdge (e : β) : V((S.deleteEdge e).G) = V(S.G) := vertexSet_restrict _ _

theorem edgeSet_deleteEdge (e : β) : E((S.deleteEdge e).G) = E(S.G) \ {e} := by
  change E(S.G.restrict (E(S.G) \ {e})) = _
  rw [edgeSet_restrict, inter_eq_right]
  exact sdiff_subset

theorem notMem_edgeSet_deleteEdge (e : β) : e ∉ E((S.deleteEdge e).G) := by
  rw [edgeSet_deleteEdge]
  exact fun h => h.2 rfl

theorem insert_edgeSet_deleteEdge {e : β} (he : e ∈ E(S.G)) :
    E(S.G) = insert e E((S.deleteEdge e).G) := by
  rw [edgeSet_deleteEdge, insert_sdiff_singleton, insert_eq_of_mem he]

theorem ncard_deleteEdge {e : β} (he : e ∈ E(S.G)) :
    V((S.deleteEdge e).G).ncard + E((S.deleteEdge e).G).ncard + 1 =
      V(S.G).ncard + E(S.G).ncard := by
  rw [vertexSet_deleteEdge, edgeSet_deleteEdge, ncard_sdiff_singleton_of_mem he]
  have : 0 < E(S.G).ncard := (ncard_pos S.finite_E).mpr ⟨e, he⟩
  omega

/-- A crooked transaction with `e` deleted is a crooked transaction. -/
theorem IsCrookedTransaction.of_deleteEdge {e : β} {P_set : Set (Graph α β)}
    (h : (S.deleteEdge e).IsCrookedTransaction P_set) : S.IsCrookedTransaction P_set := by
  have hle : ∀ P ∈ P_set, P ≤ (S.deleteEdge e).G := by
    intro P hP
    obtain ⟨A, B, hf⟩ := h.1
    obtain ⟨a, b, hab⟩ := hf.1.1 P hP
    exact hab.1.le
  exact isCrookedTransaction_of_omega_eq (S₁ := S.deleteEdge e) (S₂ := S) rfl hle
    (fun P hP => (hle P hP).trans restrict_le) h

/-- A separation of the society with `e` deleted gives one of the society, if the ends of `e` are
on one side. -/
theorem exists_separation_of_deleteEdge {e : β} {u w : α} (hl : S.G.IsLink e u w)
    {G₁ G₂ : Graph α β} (hs : (S.deleteEdge e).IsSocietySeparation G₁ G₂)
    (hside : (u ∈ V(G₁) ∧ w ∈ V(G₁)) ∨ (u ∈ V(G₂) ∧ w ∈ V(G₂))) :
    ∃ G₁' G₂', S.IsSocietySeparation G₁' G₂' ∧ V(G₁') = V(G₁) ∧ V(G₂') = V(G₂) := by
  have hle := deleteEdge_le (S := S) e
  have hV := vertexSet_deleteEdge (S := S) e
  have hE := insert_edgeSet_deleteEdge hl.edge_mem
  have he := notMem_edgeSet_deleteEdge (S := S) e
  rcases hside with ⟨hu, hw⟩ | ⟨hu, hw⟩
  · exact ⟨addEdgeTo S.G G₁ e, G₂, ⟨IsGraphSeparation.addEdge_left hs.1 hle hV hE he hl hu hw,
      hs.2⟩,
      vertexSet_addEdgeTo, rfl⟩
  · refine ⟨G₁, addEdgeTo S.G G₂ e, ⟨IsGraphSeparation.addEdge_right hs.1 hle hV hE he hl hu hw,
      ?_⟩,
      rfl, vertexSet_addEdgeTo⟩
    rw [vertexSet_addEdgeTo]
    exact hs.2

/-- Connectivity passes to the society with `e` deleted, if every separation has the ends of `e`
on one side. -/
theorem connected_deleteEdge {e : β} {u w : α} (hl : S.G.IsLink e u w) {k₁ k₂ : ℕ}
    (hconn : S.IsKConnected k₁) (hint : S.IsInternallyKConnected k₂)
    (hside : ∀ G₁ G₂, (S.deleteEdge e).IsSocietySeparation G₁ G₂ →
      (u ∈ V(G₁) ∧ w ∈ V(G₁)) ∨ (u ∈ V(G₂) ∧ w ∈ V(G₂))) :
    (S.deleteEdge e).IsKConnected k₁ ∧ (S.deleteEdge e).IsInternallyKConnected k₂ := by
  have hV := vertexSet_deleteEdge (S := S) e
  constructor
  · intro k hk G₁ G₂ hs
    obtain ⟨G₁', G₂', h, h₁, h₂⟩ := exists_separation_of_deleteEdge hl hs.1 (hside _ _ hs.1)
    exact hconn k hk G₁' G₂' ⟨h, by rw [h₁, h₂]; exact hs.2.1, by rw [h₂, ← hV]; exact hs.2.2⟩
  · intro k hk G₁ G₂ hs
    obtain ⟨G₁', G₂', h, h₁, h₂⟩ := exists_separation_of_deleteEdge hl hs.1.1 (hside _ _ hs.1.1)
    exact hint k hk G₁' G₂' ⟨⟨h, by rw [h₁, h₂]; exact hs.1.2.1, by rw [h₂, ← hV]; exact hs.1.2.2⟩,
      by rw [h₂, ← hV]; exact hs.2⟩

/-- If `e` is a loop or parallel to another edge, every separation has its ends on one side. -/
theorem side_of_redundant {e : β} {u w : α} (hl : S.G.IsLink e u w)
    (hred : u = w ∨ ∃ f, f ≠ e ∧ S.G.IsLink f u w) {G₁ G₂ : Graph α β}
    (hs : (S.deleteEdge e).IsSocietySeparation G₁ G₂) :
    (u ∈ V(G₁) ∧ w ∈ V(G₁)) ∨ (u ∈ V(G₂) ∧ w ∈ V(G₂)) := by
  obtain ⟨⟨h₁, h₂, hVu, hEu, -⟩, -⟩ := hs
  rcases hred with rfl | ⟨f, hne, hf⟩
  · have hm : u ∈ V(G₁) ∪ V(G₂) := by
      rw [hVu, vertexSet_deleteEdge]
      exact hl.left_mem
    rcases hm with h | h
    · exact Or.inl ⟨h, h⟩
    · exact Or.inr ⟨h, h⟩
  · have hf' : f ∈ E((S.deleteEdge e).G) := by
      rw [edgeSet_deleteEdge]
      exact ⟨hf.edge_mem, hne⟩
    have hfl : (S.deleteEdge e).G.IsLink f u w := (restrict_le.isLink_iff hf').mpr hf
    have hm : f ∈ E(G₁) ∪ E(G₂) := hEu ▸ hf'
    rcases hm with h | h
    · have := (h₁.isLink_iff h).mpr hfl
      exact Or.inl ⟨this.left_mem, this.right_mem⟩
    · have := (h₂.isLink_iff h).mpr hfl
      exact Or.inr ⟨this.left_mem, this.right_mem⟩

/-- A transaction of a society with a redundant edge added gives a transaction of the same size
of the society. -/
theorem exists_transaction_of_addEdge {S₁ : Society α β} {G : Graph α β} {e : β} {u w : α}
    (hG : S₁.G ≤ G) (hl : G.IsLink e u w) (hu : u ∈ V(S₁.G)) (hw : w ∈ V(S₁.G))
    (hred : u = w ∨ ∃ f, S₁.G.IsLink f u w) {P_set : Set (Graph α β)}
    (h : (S₁.addEdge G e).IsTransaction P_set) :
    ∃ P_set', S₁.IsTransaction P_set' ∧ P_set'.ncard = P_set.ncard := by
  classical
  have : Nonempty (Graph α β) := ⟨S₁.G⟩
  obtain ⟨A, B, hd, hfence, hends⟩ := h
  have hle : S₁.G ≤ (S₁.addEdge G e).G := le_addEdgeTo hG
  have hV : V(S₁.G) = V((S₁.addEdge G e).G) := vertexSet_addEdgeTo.symm
  have hE : E((S₁.addEdge G e).G) = insert e E(S₁.G) := edgeSet_addEdgeTo hG hl hu hw
  have hl' : (S₁.addEdge G e).G.IsLink e u w := isLink_addEdgeTo hl hu hw
  have hrep : ∀ R ∈ P_set, ∃ R', (∃ a ∈ A, ∃ b ∈ B, S₁.IsOmegaPathWithEnds R' a b) ∧
      V(R') = V(R) := by
    intro R hR
    obtain ⟨a, ha, b, hb, hR⟩ := hends R hR
    obtain ⟨R', hR', hVR⟩ := exists_path_of_addEdge hle hV hE hl' hred hR.1
    exact ⟨R', ⟨a, ha, b, hb, hR', hR.2.1, hR.2.2.1, hR.2.2.2⟩, hVR⟩
  choose! f hf using hrep
  have hne : ∀ R ∈ P_set, V(R).Nonempty := by
    intro R hR
    obtain ⟨a, -, b, -, hab⟩ := hends R hR
    exact ⟨a, hab.1.left_mem⟩
  have hinj : InjOn f P_set := by
    intro R hR R' hR' he
    by_contra hneq
    have hdis := hd.2 hR hR' hneq
    obtain ⟨x, hx⟩ := hne R hR
    rw [← (hf R hR).2, he, (hf R' hR').2] at hx
    exact disjoint_left.mp hdis (by
      rw [← (hf R hR).2, he, (hf R' hR').2]
      exact hx) hx
  refine ⟨f '' P_set, ⟨A, B, ⟨?_, ?_⟩, hfence, ?_⟩, hinj.ncard_image⟩
  · rintro _ ⟨R, hR, rfl⟩
    obtain ⟨a, -, b, -, hab⟩ := (hf R hR).1
    exact ⟨a, b, hab⟩
  · rintro _ ⟨R, hR, rfl⟩ _ ⟨R', hR', rfl⟩ hneq
    have hn : R ≠ R' := fun h => hneq (by rw [h])
    change Disjoint V(f R) V(f R')
    rw [(hf R hR).2, (hf R' hR').2]
    exact hd.2 hR hR' hn
  · rintro _ ⟨R, hR, rfl⟩
    exact (hf R hR).1

/-- The composition with `e` added to the rural neighborhood. -/
theorem hasSophisticationLE_add_outer {e : β} {u w : α} (hl : S.G.IsLink e u w) {k : ℕ}
    {S₁ : Society α β} {N : Neighborhood α β} (hc : (S.deleteEdge e).IsComposition S₁ N)
    (hu : u ∈ V(N.G)) (hw : w ∈ V(N.G)) (hr : (N.addEdge S.G e).IsRural)
    (hk : ∀ P_set : Set (Graph α β), S₁.IsTransaction P_set → P_set.ncard ≤ k) :
    S.HasSophisticationLE k := by
  have hle := deleteEdge_le (S := S) e
  have hV := vertexSet_deleteEdge (S := S) e
  have hE := insert_edgeSet_deleteEdge hl.edge_mem
  have he := notMem_edgeSet_deleteEdge (S := S) e
  obtain ⟨⟨hsep, hbar⟩, hΩ, hΩ₀, hb⟩ := hc
  refine ⟨S₁, N.addEdge S.G e, ⟨⟨IsGraphSeparation.addEdge_right hsep hle hV hE he hl hu hw, ?_⟩,
    hΩ, hΩ₀, ?_⟩, hr, hk⟩
  · change S.Ω.bar ⊆ V(addEdgeTo S.G N.G e)
    rw [vertexSet_addEdgeTo]
    exact hbar
  · change S₁.Ω.bar = V(S₁.G) ∩ V(addEdgeTo S.G N.G e)
    rw [vertexSet_addEdgeTo]
    exact hb

/-- The composition with a redundant `e` added to the inner society. -/
theorem hasSophisticationLE_add_inner {e : β} {u w : α} (hl : S.G.IsLink e u w) {k : ℕ}
    {S₁ : Society α β} {N : Neighborhood α β} (hc : (S.deleteEdge e).IsComposition S₁ N)
    (hu : u ∈ V(S₁.G)) (hw : w ∈ V(S₁.G)) (hred : u = w ∨ ∃ f, S₁.G.IsLink f u w)
    (hr : N.IsRural)
    (hk : ∀ P_set : Set (Graph α β), S₁.IsTransaction P_set → P_set.ncard ≤ k) :
    S.HasSophisticationLE k := by
  have hle := deleteEdge_le (S := S) e
  have hV := vertexSet_deleteEdge (S := S) e
  have hE := insert_edgeSet_deleteEdge hl.edge_mem
  have he := notMem_edgeSet_deleteEdge (S := S) e
  obtain ⟨⟨hsep, hbar⟩, hΩ, hΩ₀, hb⟩ := hc
  have hG : S₁.G ≤ S.G := hsep.1.trans hle
  refine ⟨S₁.addEdge S.G e, N, ⟨⟨IsGraphSeparation.addEdge_left hsep hle hV hE he hl hu hw, hbar⟩,
    hΩ, hΩ₀, ?_⟩, hr, fun P_set hP => ?_⟩
  · change S₁.Ω.bar = V(addEdgeTo S.G S₁.G e) ∩ V(N.G)
    rw [vertexSet_addEdgeTo]
    exact hb
  · obtain ⟨P', hP', hn⟩ := exists_transaction_of_addEdge hG hl hu hw hred hP
    rw [← hn]
    exact hk P' hP'

/-- The rural neighborhood with `e` added has `e` in its edges. -/
private theorem addEdge_facts {e : β} {u w : α} (hl : S.G.IsLink e u w) {N : Neighborhood α β}
    (hN : N.G ≤ (S.deleteEdge e).G) (hu : u ∈ V(N.G)) (hw : w ∈ V(N.G)) :
    N.G ≤ (N.addEdge S.G e).G ∧ V((N.addEdge S.G e).G) = V(N.G) ∧
      E((N.addEdge S.G e).G) = insert e E(N.G) ∧ e ∉ E(N.G) ∧
      (N.addEdge S.G e).G.IsLink e u w := by
  have hNG : N.G ≤ S.G := hN.trans (deleteEdge_le e)
  exact ⟨le_addEdgeTo hNG, vertexSet_addEdgeTo, edgeSet_addEdgeTo hNG hl hu hw,
    fun h => notMem_edgeSet_deleteEdge (S := S) e (hN.edgeSet_mono h), isLink_addEdgeTo hl hu hw⟩

/-- Claim (1) of (6.1), for an edge parallel to another edge. -/
theorem hasSophisticationLE_of_deleteEdge_parallel {e f : β} {u w : α} (hl : S.G.IsLink e u w)
    (hne : f ≠ e) (hf : S.G.IsLink f u w) (huw : u ≠ w) {k : ℕ}
    (h : (S.deleteEdge e).HasSophisticationLE k) : S.HasSophisticationLE k := by
  obtain ⟨S₁, N, hc, hr, hk⟩ := h
  have hc' := hc
  obtain ⟨⟨⟨h₁, h₂, -, hEu, -⟩, -⟩, -, -, -⟩ := hc'
  have hf' : f ∈ E((S.deleteEdge e).G) := by
    rw [edgeSet_deleteEdge]
    exact ⟨hf.edge_mem, hne⟩
  have hfl : (S.deleteEdge e).G.IsLink f u w := (restrict_le.isLink_iff hf').mpr hf
  have hm : f ∈ E(S₁.G) ∪ E(N.G) := hEu ▸ hf'
  rcases hm with hm | hm
  · have hl₁ := (h₁.isLink_iff hm).mpr hfl
    exact hasSophisticationLE_add_inner hl hc hl₁.left_mem hl₁.right_mem (Or.inr ⟨f, hl₁⟩) hr hk
  · have hl₂ := (h₂.isLink_iff hm).mpr hfl
    obtain ⟨a, b, c, d, g⟩ := addEdge_facts hl h₂ hl₂.left_mem hl₂.right_mem
    exact hasSophisticationLE_add_outer hl hc hl₂.left_mem hl₂.right_mem
      (hr.add_parallel rfl rfl a b c d g hl₂ huw) hk

/-- Claim (1) of (6.1), for a loop. -/
theorem hasSophisticationLE_of_deleteEdge_loop {e : β} {u : α} (hl : S.G.IsLink e u u) {k : ℕ}
    (h : (S.deleteEdge e).HasSophisticationLE k) : S.HasSophisticationLE k := by
  obtain ⟨S₁, N, hc, hr, hk⟩ := h
  have hc' := hc
  obtain ⟨⟨⟨h₁, h₂, hVu, -, -⟩, -⟩, -, hΩ₀, hb⟩ := hc'
  by_cases hu₁ : u ∈ V(S₁.G)
  · exact hasSophisticationLE_add_inner hl hc hu₁ hu₁ (Or.inl rfl) hr hk
  · have hu₂ : u ∈ V(N.G) := by
      have hm : u ∈ V(S₁.G) ∪ V(N.G) := by
        rw [hVu, vertexSet_deleteEdge]
        exact hl.left_mem
      exact hm.resolve_left hu₁
    have hu₀ : u ∉ N.Ω₀.bar := by
      rw [hΩ₀, hb]
      exact fun h' => hu₁ h'.1
    obtain ⟨a, b, c, d, g⟩ := addEdge_facts hl h₂ hu₂ hu₂
    exact hasSophisticationLE_add_outer hl hc hu₂ hu₂ (hr.add_loop rfl rfl a b c d g hu₂ hu₀) hk

/-- Claim (4) of (6.1). -/
theorem hasSophisticationLE_of_deleteEdge_boundary {e : β} {u w : α} (hl : S.G.IsLink e u w)
    (hu : u ∈ S.Ω.bar) (hw : w ∈ S.Ω.bar) (huw : u ≠ w) (hgap : S.Ω.interval u w = ∅) {k : ℕ}
    (h : (S.deleteEdge e).HasSophisticationLE k) : S.HasSophisticationLE k := by
  obtain ⟨S₁, N, hc, hr, hk⟩ := h
  have hc' := hc
  obtain ⟨⟨⟨-, h₂, -, -, -⟩, hbar⟩, hΩ, -, -⟩ := hc'
  have hΩ' : N.Ω = S.Ω := hΩ
  have hu₂ : u ∈ V(N.G) := hbar hu
  have hw₂ : w ∈ V(N.G) := hbar hw
  obtain ⟨a, b, c, d, g⟩ := addEdge_facts hl h₂ hu₂ hw₂
  exact hasSophisticationLE_add_outer hl hc hu₂ hw₂ (hr.add_boundary_edge rfl rfl a b c d g
    (hΩ' ▸ hu) (hΩ' ▸ hw) huw (hΩ' ▸ hgap)) hk

variable (S)

/-- The society `S` with the vertex `v` of `ΩBar` deleted. -/
noncomputable def deleteBarVertex (v : α) : Society α β where
  G := deleteVertices S.G {v}
  Ω := S.Ω.restrict (S.Ω.bar \ {v}) sdiff_subset
  finite_V := S.finite_V.subset (deleteVertices_le S.G {v}).vertexSet_mono
  finite_E := S.finite_E.subset (deleteVertices_le S.G {v}).edgeSet_mono
  bar_subset := by
    rw [S.Ω.restrict_bar]
    rintro x ⟨hx, hne⟩
    exact ⟨S.bar_subset hx, hne⟩

variable {S}

theorem vertexSet_deleteBarVertex (v : α) : V((S.deleteBarVertex v).G) = V(S.G) \ {v} := by
  change V(S.G.induce (V(S.G) \ {v})) = _
  simp

theorem edgeSet_deleteBarVertex {v : α} (hno : ∀ e x, ¬ S.G.IsLink e v x) :
    E((S.deleteBarVertex v).G) = E(S.G) := by
  refine Subset.antisymm (deleteVertices_le S.G {v}).edgeSet_mono fun e he => ?_
  obtain ⟨x, y, hxy⟩ := S.G.exists_isLink_of_mem_edgeSet he
  refine ⟨x, y, hxy, ⟨hxy.left_mem, ?_⟩, ⟨hxy.right_mem, ?_⟩⟩
  · rintro rfl
    exact hno _ _ hxy
  · rintro rfl
    exact hno _ _ hxy.symm

theorem ncard_deleteBarVertex {v : α} (hv : v ∈ S.Ω.bar) (hno : ∀ e x, ¬ S.G.IsLink e v x) :
    V((S.deleteBarVertex v).G).ncard + E((S.deleteBarVertex v).G).ncard + 1 =
      V(S.G).ncard + E(S.G).ncard := by
  have hvG := S.bar_subset hv
  rw [vertexSet_deleteBarVertex, edgeSet_deleteBarVertex hno, ncard_sdiff_singleton_of_mem hvG]
  have : 0 < V(S.G).ncard := (ncard_pos S.finite_V).mpr ⟨v, hvG⟩
  omega

/-- A crooked transaction with `v` deleted is a crooked transaction. -/
theorem IsCrookedTransaction.of_deleteBarVertex {v : α} {P_set : Set (Graph α β)}
    (h : (S.deleteBarVertex v).IsCrookedTransaction P_set) : S.IsCrookedTransaction P_set := by
  have hle : ∀ P ∈ P_set, P ≤ (S.deleteBarVertex v).G := by
    intro P hP
    obtain ⟨A, B, hf⟩ := h.1
    obtain ⟨a, b, hab⟩ := hf.1.1 P hP
    exact hab.1.le
  have h₂ : (S.restrictOmega (S.Ω.bar \ {v}) sdiff_subset).IsCrookedTransaction P_set :=
    isCrookedTransaction_of_omega_eq (S₁ := S.deleteBarVertex v) rfl hle
      (fun P hP => (hle P hP).trans (deleteVertices_le S.G {v})) h
  exact ((S.isCrookedTransaction_restrictOmega_iff sdiff_subset).mp h₂).1

/-- A separation of the society with the isolated vertex `v` deleted gives one of the society, with
`v` added to the second side. -/
theorem exists_separation_of_deleteBarVertex {v : α} (hv : v ∈ S.Ω.bar)
    (hno : ∀ e x, ¬ S.G.IsLink e v x) {G₁ G₂ : Graph α β}
    (hs : (S.deleteBarVertex v).IsSocietySeparation G₁ G₂) :
    S.IsSocietySeparation G₁ (addVertexTo S.G G₂ v) ∧ v ∉ V(G₁) ∧ v ∉ V(G₂) := by
  obtain ⟨⟨h₁, h₂, hVu, hEu, hd⟩, hbar⟩ := hs
  have hle := deleteVertices_le S.G {v}
  have hvG := S.bar_subset hv
  have hG₂ : G₂ ≤ S.G := h₂.trans hle
  have hoff : ∀ {H : Graph α β}, H ≤ (S.deleteBarVertex v).G → v ∉ V(H) := by
    intro H hH h
    have := hH.vertexSet_mono h
    rw [vertexSet_deleteBarVertex] at this
    exact this.2 rfl
  refine ⟨⟨⟨h₁.trans hle, addVertexTo_le hG₂ hvG, ?_, ?_, ?_⟩, ?_⟩, hoff h₁, hoff h₂⟩
  · rw [vertexSet_addVertexTo, union_insert, hVu, vertexSet_deleteBarVertex, insert_sdiff_singleton,
      insert_eq_of_mem hvG]
  · rw [edgeSet_addVertexTo hG₂, hEu, edgeSet_deleteBarVertex hno]
  · rwa [edgeSet_addVertexTo hG₂]
  · rw [vertexSet_addVertexTo]
    intro x hx
    by_cases hxv : x = v
    · exact Or.inl hxv
    · refine Or.inr (hbar ?_)
      change x ∈ (S.Ω.restrict (S.Ω.bar \ {v}) sdiff_subset).bar
      rw [S.Ω.restrict_bar]
      exact ⟨hx, hxv⟩

/-- Connectivity passes to the society with the isolated vertex `v` deleted. -/
theorem connected_deleteBarVertex {v : α} (hv : v ∈ S.Ω.bar) (hno : ∀ e x, ¬ S.G.IsLink e v x)
    {k₁ k₂ : ℕ} (hconn : S.IsKConnected k₁) (hint : S.IsInternallyKConnected k₂) :
    (S.deleteBarVertex v).IsKConnected k₁ ∧ (S.deleteBarVertex v).IsInternallyKConnected k₂ := by
  have hvG := S.bar_subset hv
  have key : ∀ {G₁ G₂ : Graph α β} {k : ℕ}, (S.deleteBarVertex v).IsKSeparation k G₁ G₂ →
      S.IsKSeparation k G₁ (addVertexTo S.G G₂ v) ∧
        V(addVertexTo S.G G₂ v).ncard = V(G₂).ncard + 1 := by
    intro G₁ G₂ k hs
    obtain ⟨hs', hv₁, hv₂⟩ := exists_separation_of_deleteBarVertex hv hno hs.1
    have hfin : V(G₂).Finite := S.finite_V.subset (hs.1.1.2.1.trans
      (deleteVertices_le S.G {v})).vertexSet_mono
    refine ⟨⟨hs', ?_, ?_⟩, ?_⟩
    · rw [vertexSet_addVertexTo, inter_insert_of_notMem hv₁]
      exact hs.2.1
    · rw [vertexSet_addVertexTo]
      intro he
      apply hs.2.2
      rw [vertexSet_deleteBarVertex, ← he, insert_sdiff_of_mem _ (mem_singleton v),
        sdiff_singleton_eq_self hv₂]
    · rw [vertexSet_addVertexTo, ncard_insert_of_notMem hv₂ hfin]
  constructor
  · intro k hk G₁ G₂ hs
    exact hconn k hk _ _ (key hs).1
  · intro k hk G₁ G₂ hs
    refine hint k hk _ _ ⟨(key hs.1).1, ?_⟩
    have h₂ := hs.2
    rw [(key hs.1).2]
    rw [vertexSet_deleteBarVertex, ncard_sdiff_singleton_of_mem hvG] at h₂
    omega

/-- Claim (2) of (6.1). -/
theorem hasSophisticationLE_of_deleteBarVertex {v : α} (hv : v ∈ S.Ω.bar)
    (hno : ∀ e x, ¬ S.G.IsLink e v x) {k : ℕ} (h : (S.deleteBarVertex v).HasSophisticationLE k) :
    S.HasSophisticationLE k := by
  obtain ⟨S₁, N, ⟨hs, hΩ, hΩ₀, hb⟩, hr, hk⟩ := h
  obtain ⟨hs', hv₁, hv₂⟩ := exists_separation_of_deleteBarVertex hv hno hs
  have hvG := S.bar_subset hv
  have hNG : N.G ≤ S.G := hs.1.2.1.trans (deleteVertices_le S.G {v})
  let N' : Neighborhood α β :=
    { G := addVertexTo S.G N.G v
      Ω := S.Ω
      Ω₀ := N.Ω₀
      finite_V := S.finite_V.subset (addVertexTo_le hNG hvG).vertexSet_mono
      finite_E := S.finite_E.subset (addVertexTo_le hNG hvG).edgeSet_mono
      bar_subset := hs'.2
      bar₀_subset := by
        rw [vertexSet_addVertexTo]
        exact fun x hx => Or.inr (N.bar₀_subset hx) }
  have hNΩ : N.Ω = S.Ω.restrict (S.Ω.bar \ {v}) sdiff_subset := hΩ
  refine ⟨S₁, N', ⟨hs', rfl, hΩ₀, ?_⟩, ?_, hk⟩
  · change S₁.Ω.bar = V(S₁.G) ∩ V(addVertexTo S.G N.G v)
    rw [vertexSet_addVertexTo, inter_insert_of_notMem hv₁]
    exact hb
  · refine hr.add_boundary_vertex rfl (le_addVertexTo hNG) hv₂ vertexSet_addVertexTo
      (edgeSet_addVertexTo hNG) hv ?_ ?_
    · change N.Ω.bar = S.Ω.bar \ {v}
      rw [hNΩ, S.Ω.restrict_bar]
    · intro v₁ v₂ v₃ h h₁ h₂ h₃
      rw [hNΩ, S.Ω.isClockwise3_restrict_iff]
      have hm := CyclicPerm.isClockwise3_iff.mp (show S.Ω.IsClockwise3 v₁ v₂ v₃ from h)
      exact ⟨⟨hm.2.2.2.1, h₁⟩, ⟨hm.2.2.2.2.1, h₂⟩, ⟨hm.2.2.2.2.2.1, h₃⟩, h⟩

variable (S)

/-- Adding the vertex `r` of `G` between two consecutive vertices of `Ω`. -/
theorem exists_extension {a b r : α} (ha : a ∈ S.Ω.bar) (hb : b ∈ S.Ω.bar) (hab : a ≠ b)
    (hr : r ∈ V(S.G)) (hrb : r ∉ S.Ω.bar) (hgap : S.Ω.interval a b = ∅) :
    ∃ S₀ : Society α β, S₀.G = S.G ∧ S₀.Ω.bar = S.Ω.bar ∪ {r} ∧
      S₀.Ω.IsRestriction S.Ω.bar S.Ω ∧ S₀.Ω.IsClockwise3 a r b := by
  classical
  obtain ⟨L, hL, hL0⟩ := S.Ω.exists_isOrbitList_starting_at hb
  have hpos : 0 < L.length := List.length_pos_of_ne_nil hL.2.1
  have haL : a ∈ L := by
    have : a ∈ {v | v ∈ L} := hL.2.2.1 ▸ ha
    exact this
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp haL
  have hi0 : 0 < i := by
    refine Nat.pos_of_ne_zero fun h => hab ?_
    subst h
    exact hL0 hi
  have hilast : i = L.length - 1 := by
    by_contra hne
    have hlt : i < L.length - 1 := by omega
    have hin := S.Ω.isOrbitList_mem_interval_of_lt hL hi0 hlt (by omega)
    rw [hL0 hpos] at hin
    have hrot := S.Ω.mem_interval_rotate_left hin
    rw [hgap] at hrot
    exact hrot
  have hnd : (L ++ [r]).Nodup := by
    rw [List.nodup_append]
    refine ⟨hL.1, List.nodup_singleton r, ?_⟩
    intro x hx y hy
    rw [List.mem_singleton] at hy
    subst hy
    rintro rfl
    exact hrb (hL.2.2.1 ▸ hx)
  have hne : L ++ [r] ≠ [] := by simp
  let Ω₀ := CyclicPerm.ofNodupList (L ++ [r]) hnd hne
  have hL₀ : Ω₀.IsOrbitList (L ++ [r]) := CyclicPerm.isOrbitList_ofNodupList _ hnd hne
  have hbar : Ω₀.bar = S.Ω.bar ∪ {r} := by
    rw [← hL₀.2.2.1, ← hL.2.2.1]
    ext x
    simp [or_comm]
  have hlen : (L ++ [r]).length = L.length + 1 := by simp
  have hget : ∀ j (hj : j < L.length), (L ++ [r])[j]'(by omega) = L[j] := fun j hj =>
    List.getElem_append_left hj
  have hgetr : (L ++ [r])[L.length]'(by omega) = r := by simp
  have hnext : ∀ j (hj : j < L.length) (hj' : j + 1 < L.length),
      Ω₀.toFun (L[j]) = L[j + 1] := by
    intro j hj hj'
    have := hL₀.2.2.2 j (by omega)
    rw [hget j hj] at this
    rw [this]
    simp only [hlen]
    have he : (j + 1) % (L.length + 1) = j + 1 := Nat.mod_eq_of_lt (by omega)
    simp only [he]
    exact hget (j + 1) hj'
  refine ⟨⟨S.G, Ω₀, S.finite_V, S.finite_E, ?_⟩, rfl, hbar, ⟨?_, ?_⟩, ?_⟩
  · rw [hbar]
    exact union_subset S.bar_subset (singleton_subset_iff.mpr hr)
  · rw [hbar, inter_eq_right.mpr subset_union_left]
  · intro x hx
    have hxL : x ∈ L := by
      have : x ∈ {v | v ∈ L} := hL.2.2.1 ▸ hx
      exact this
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hxL
    have hstep := hL.2.2.2 j hj
    rw [show S.Ω (L[j]) = S.Ω.toFun (L[j]) from rfl, hstep]
    by_cases hj' : j + 1 < L.length
    · have he : (j + 1) % L.length = j + 1 := Nat.mod_eq_of_lt hj'
      simp only [he]
      refine ⟨1, le_rfl, ?_, ?_, fun k h₁ h₂ => by omega⟩
      · simpa using hnext j hj hj'
      · exact hL.2.2.1 ▸ List.getElem_mem hj'
    · have hjlast : j + 1 = L.length := by omega
      have he : (j + 1) % L.length = 0 := by rw [hjlast, Nat.mod_self]
      simp only [he]
      have h₁ : Ω₀.toFun (L[j]) = r := by
        have := hL₀.2.2.2 j (by omega)
        rw [hget j hj] at this
        rw [this]
        simp only [hlen]
        have he' : (j + 1) % (L.length + 1) = L.length := by
          rw [hjlast]
          exact Nat.mod_eq_of_lt (by omega)
        simp only [he']
        exact hgetr
      have h₂ : Ω₀.toFun r = L[0] := by
        have := hL₀.2.2.2 L.length (by omega)
        rw [hgetr] at this
        rw [this]
        simp only [hlen]
        have he' : (L.length + 1) % (L.length + 1) = 0 := Nat.mod_self _
        simp only [he']
        exact hget 0 hpos
      refine ⟨2, by omega, ?_, hL.2.2.1 ▸ List.getElem_mem hpos, fun k hk₁ hk₂ => ?_⟩
      · simp only [Function.iterate_succ, Function.iterate_zero, comp_apply, id_eq, h₁, h₂]
      · obtain rfl : k = 1 := by omega
        simpa [h₁] using hrb
  · have hin := Ω₀.isOrbitList_mem_interval_of_lt hL₀ (i := 0) (j := i) (k := L.length) hi0
      (by omega) (by omega)
    have hrot := Ω₀.mem_interval_rotate_right hin
    have e₁ : (L ++ [r])[i]'(by omega) = L[i] := hget i hi
    have e₂ : (L ++ [r])[0]'(by omega) = b := (hget 0 hpos).trans (hL0 hpos)
    rw [e₁, e₂, hgetr] at hin
    exact Ω₀.isClockwise3_rotate hin.2

variable {S}

/-- Sophistication does not grow when we pass to a smaller outer cyclic permutation. -/
theorem HasSophisticationLE.of_extension {S₀ : Society α β} (hG : S₀.G = S.G)
    (hbar : S.Ω.bar ⊆ S₀.Ω.bar) (hres : S₀.Ω.IsRestriction S.Ω.bar S.Ω) {k : ℕ}
    (h : S₀.HasSophisticationLE k) : S.HasSophisticationLE k := by
  obtain ⟨S₁, N, ⟨⟨hsep, hb⟩, hΩ, hΩ₀, hc⟩, hr, hk⟩ := h
  have hΩ' : N.Ω = S₀.Ω := hΩ
  let N' : Neighborhood α β := ⟨N.G, S.Ω, N.Ω₀, N.finite_V, N.finite_E, hbar.trans hb,
    N.bar₀_subset⟩
  refine ⟨S₁, N', ⟨⟨hG ▸ hsep, hbar.trans hb⟩, rfl, hΩ₀, hc⟩, ?_, hk⟩
  refine hr.restrict_outer rfl rfl (hΩ' ▸ hbar) fun v₁ v₂ v₃ h => ?_
  rw [hΩ']
  exact (hres.isClockwise3_iff.mp h).2.2.2

/-- Connectivity passes to a larger outer cyclic permutation on the same graph. -/
theorem connected_of_extension {S₀ : Society α β} (hG : S₀.G = S.G)
    (hbar : S.Ω.bar ⊆ S₀.Ω.bar) {k₁ k₂ : ℕ} (hconn : S.IsKConnected k₁)
    (hint : S.IsInternallyKConnected k₂) :
    S₀.IsKConnected k₁ ∧ S₀.IsInternallyKConnected k₂ := by
  have key : ∀ {G₁ G₂ : Graph α β} {k : ℕ}, S₀.IsKSeparation k G₁ G₂ → S.IsKSeparation k G₁ G₂ := by
    rintro G₁ G₂ k ⟨⟨hs, hb⟩, h₁, h₂⟩
    exact ⟨⟨hG ▸ hs, hbar.trans hb⟩, h₁, hG ▸ h₂⟩
  exact ⟨fun k hk G₁ G₂ h => hconn k hk _ _ (key h),
    fun k hk G₁ G₂ h => hint k hk _ _ ⟨key h.1, hG ▸ h.2⟩⟩

end Society

end GraphMinor.GM09
