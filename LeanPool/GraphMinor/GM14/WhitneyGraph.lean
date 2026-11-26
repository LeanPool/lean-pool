/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM11.Walks

/-!
# Separations of a subdivision of a 3-connected graph

This file is the graph part of the proof of Whitney's theorem. Let `G` be a subdivision of a simple
3-connected graph `G₀`. Think of the edges of `G` as cut into two sets `A` and `E(G) \ A`, and let
`bdry G A` be the set of vertices that meet both sets. We show that if `bdry G A` lies in `V(G₀)`
and is not empty of edges on either side, then it has at least two vertices, and if it has exactly
two then one side is one of the paths that replace an edge of `G₀`.

Such facts need the vertices of `V(G₀)`. So we also show that a vertex that meets three edges of `G`
is in `V(G₀)`, and that each vertex meets at least two edges.
-/

@[expose] public section

namespace GraphMinor.GM14.Whitney

open Set Graph GraphMinor.GM09 GraphMinor.Surface

universe u v

variable {α : Type u} {β : Type v}

/-! ## 1. Simple walks -/

section Walks

variable {P : Graph α β}

/-- An end of an edge of a walk is on the walk. -/
theorem inc_mem_support {a b : α} (W : GraphWalk P a b) {e : β} {x : α} (he : e ∈ W.edges)
    (hx : P.Inc e x) : x ∈ W.support := by
  induction W with
  | nil _ => simp [GraphWalk.edges] at he
  | @cons u v w f hlink rest ih =>
    simp only [GraphWalk.edges, List.mem_cons] at he
    simp only [GraphWalk.support, List.mem_cons]
    rcases he with rfl | he
    · obtain ⟨y, hy⟩ := hx
      rcases P.eq_or_eq_of_isLink_of_isLink hy hlink with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rest.start_mem_support
    · exact Or.inr (ih he)

/-- At most one edge of a simple walk meets its first vertex. -/
theorem eq_of_inc_start {a b : α} (W : GraphWalk P a b) (hW : W.IsSimple) {e f : β}
    (he : e ∈ W.edges) (hf : f ∈ W.edges) (hea : P.Inc e a) (hfa : P.Inc f a) : e = f := by
  cases W with
  | nil _ => simp [GraphWalk.edges] at he
  | @cons _ v _ g hlink rest =>
    have hnd : a ∉ rest.support := (List.nodup_cons.mp hW).1
    simp only [GraphWalk.edges, List.mem_cons] at he hf
    rcases he with rfl | he
    · rcases hf with rfl | hf
      · rfl
      · exact (hnd (inc_mem_support rest hf hfa)).elim
    · exact (hnd (inc_mem_support rest he hea)).elim

/-- A simple walk has no three distinct edges at one vertex. -/
theorem not_three_edges {a b : α} (W : GraphWalk P a b) (hW : W.IsSimple) {x : α} {e₁ e₂ e₃ : β}
    (h₁ : e₁ ∈ W.edges) (h₂ : e₂ ∈ W.edges) (h₃ : e₃ ∈ W.edges) (hx₁ : P.Inc e₁ x)
    (hx₂ : P.Inc e₂ x) (hx₃ : P.Inc e₃ x) (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃) :
    False := by
  induction W with
  | nil _ => simp [GraphWalk.edges] at h₁
  | @cons u v w g hlink rest ih =>
    have hs : rest.IsSimple := (List.nodup_cons.mp hW).2
    by_cases hxu : x = u
    · subst hxu
      exact h12 (eq_of_inc_start _ hW h₁ h₂ hx₁ hx₂)
    have hrest : ∀ {e : β}, e ∈ (GraphWalk.cons hlink rest).edges → P.Inc e x → e ≠ g →
        e ∈ rest.edges := by
      intro e he _ hne
      simp only [GraphWalk.edges, List.mem_cons] at he
      exact he.resolve_left hne
    have hgv : e₁ = g ∨ e₂ = g ∨ e₃ = g → x = v := by
      intro hg
      have hinc : P.Inc g x := by
        rcases hg with rfl | rfl | rfl <;> assumption
      obtain ⟨y, hy⟩ := hinc
      rcases P.eq_or_eq_of_isLink_of_isLink hy hlink with h | h
      · exact (hxu h).elim
      · exact h
    by_cases hg₁ : e₁ = g
    · have hv := hgv (Or.inl hg₁)
      subst hv
      exact h23 (eq_of_inc_start rest hs (hrest h₂ hx₂ (hg₁ ▸ h12.symm))
        (hrest h₃ hx₃ (hg₁ ▸ h13.symm)) hx₂ hx₃)
    by_cases hg₂ : e₂ = g
    · have hv := hgv (Or.inr (Or.inl hg₂))
      subst hv
      exact h13 (eq_of_inc_start rest hs (hrest h₁ hx₁ hg₁)
        (hrest h₃ hx₃ (hg₂ ▸ h23.symm)) hx₁ hx₃)
    by_cases hg₃ : e₃ = g
    · have hv := hgv (Or.inr (Or.inr hg₃))
      subst hv
      exact h12 (eq_of_inc_start rest hs (hrest h₁ hx₁ hg₁) (hrest h₂ hx₂ hg₂) hx₁ hx₂)
    exact ih hs (hrest h₁ hx₁ hg₁) (hrest h₂ hx₂ hg₂) (hrest h₃ hx₃ hg₃)

/-- A walk between two distinct vertices has an edge at its first vertex. -/
theorem exists_edge_at_start {a b : α} (W : GraphWalk P a b) (hab : a ≠ b) :
    ∃ e ∈ W.edges, P.Inc e a := by
  cases W with
  | nil _ => exact (hab rfl).elim
  | @cons _ v _ g hlink rest => exact ⟨g, by simp [GraphWalk.edges], v, hlink⟩

/-- A simple walk has two distinct edges at each inner vertex. -/
theorem exists_two_edges_at_inner {a b : α} (W : GraphWalk P a b) (hW : W.IsSimple) {x : α}
    (hx : x ∈ W.support) (hxa : x ≠ a) (hxb : x ≠ b) :
    ∃ e ∈ W.edges, ∃ f ∈ W.edges, e ≠ f ∧ P.Inc e x ∧ P.Inc f x := by
  induction W with
  | nil _ => exact (hxa (by simpa [GraphWalk.support] using hx)).elim
  | @cons u v w g hlink rest ih =>
    have hs : rest.IsSimple := (List.nodup_cons.mp hW).2
    have hnd : u ∉ rest.support := (List.nodup_cons.mp hW).1
    have hxr : x ∈ rest.support := by
      simp only [GraphWalk.support, List.mem_cons] at hx
      exact hx.resolve_left hxa
    by_cases hxv : x = v
    · subst hxv
      obtain ⟨f, hf, hfx⟩ := exists_edge_at_start rest hxb
      refine ⟨g, by simp [GraphWalk.edges], f, by simp [GraphWalk.edges, hf], ?_,
        ⟨u, hlink.symm⟩, hfx⟩
      rintro rfl
      obtain ⟨y, hy⟩ := hfx
      have huy := P.eq_or_eq_of_isLink_of_isLink hlink hy
      rcases huy with rfl | rfl
      · exact hxa rfl
      · exact hnd (inc_mem_support rest hf ⟨x, hy.symm⟩)
    · obtain ⟨e, he, f, hf, hne, h₁, h₂⟩ := ih hs hxr hxv hxb
      exact ⟨e, by simp [GraphWalk.edges, he], f, by simp [GraphWalk.edges, hf], hne, h₁, h₂⟩

/-- If at each inner vertex of a simple walk the edges of the walk are on the same side of a set
`A`, then all edges of the walk are on the same side. -/
theorem walk_pure {a b : α} (W : GraphWalk P a b) (hW : W.IsSimple) {A : Set β}
    (hA : ∀ x ∈ W.support, x ≠ a → x ≠ b → ∀ e ∈ W.edges, ∀ f ∈ W.edges, P.Inc e x → P.Inc f x →
      (e ∈ A ↔ f ∈ A)) :
    ∀ e ∈ W.edges, ∀ f ∈ W.edges, e ∈ A ↔ f ∈ A := by
  induction W with
  | nil _ => intro e he; simp [GraphWalk.edges] at he
  | @cons u v w g hlink rest ih =>
    have hs : rest.IsSimple := (List.nodup_cons.mp hW).2
    have hnd : u ∉ rest.support := (List.nodup_cons.mp hW).1
    have hsub : ∀ {e : β}, e ∈ rest.edges → e ∈ (GraphWalk.cons hlink rest).edges := fun h => by
      simp [GraphWalk.edges, h]
    have hir : ∀ e ∈ rest.edges, ∀ f ∈ rest.edges, e ∈ A ↔ f ∈ A := by
      refine ih hs fun x hx hxv hxw e he f hf => ?_
      refine hA x (by simp [GraphWalk.support, hx]) ?_ hxw e (hsub he) f (hsub hf)
      rintro rfl
      exact hnd hx
    have hgr : ∀ f ∈ rest.edges, g ∈ A ↔ f ∈ A := by
      intro f hf
      have hvw : v ≠ w := by
        rintro rfl
        have := GraphWalk.IsSimple.length_eq_zero hs
        have hne : rest.edges ≠ [] := List.ne_nil_of_mem hf
        exact hne (List.length_eq_zero_iff.mp this)
      obtain ⟨f', hf', hinc⟩ := exists_edge_at_start rest hvw
      have hvu : v ≠ u := by
        rintro rfl
        exact hnd rest.start_mem_support
      have h₁ : g ∈ A ↔ f' ∈ A :=
        hA v (by simp [GraphWalk.support, rest.start_mem_support]) hvu hvw g
          (by simp [GraphWalk.edges]) f' (hsub hf') ⟨u, hlink.symm⟩ hinc
      exact h₁.trans (hir f' hf' f hf)
    intro e he f hf
    simp only [GraphWalk.edges, List.mem_cons] at he hf
    rcases he with rfl | he <;> rcases hf with rfl | hf
    · rfl
    · exact hgr f hf
    · exact (hgr e he).symm
    · exact hir e he f hf

end Walks

/-! ## 2. Separations of the simple graph -/

section ThreeConnected

variable {G₀ : Graph α β}

/-- The form of 3-connectivity that we use: a separation given by sets. -/
theorem IsSimpleThreeConnected.sep (hG : IsSimpleThreeConnectedGraph G₀) {Vx Vy : Set α}
    {Ex Ey : Set β} (hV : Vx ∪ Vy = V(G₀)) (hE : Ex ∪ Ey = E(G₀)) (hd : Disjoint Ex Ey)
    (hlx : ∀ e ∈ Ex, ∀ x y, G₀.IsLink e x y → x ∈ Vx ∧ y ∈ Vx)
    (hly : ∀ e ∈ Ey, ∀ x y, G₀.IsLink e x y → x ∈ Vy ∧ y ∈ Vy)
    (hc : (Vx ∩ Vy).ncard < 3) : Vx = V(G₀) ∨ Vy = V(G₀) := by
  have hE' : ∀ {T Z : Set β} {W : Set α}, T ⊆ E(G₀) →
      (∀ e ∈ T, ∀ x y, G₀.IsLink e x y → x ∈ W ∧ y ∈ W) → Z = T →
      E((G₀.induce W).restrict Z) = T := by
    intro T Z W hT hl hZ
    subst hZ
    rw [edgeSet_restrict, inter_eq_right]
    intro e he
    obtain ⟨x, y, hxy⟩ := G₀.exists_isLink_of_mem_edgeSet (hT he)
    obtain ⟨h₁, h₂⟩ := hl e he x y hxy
    exact ⟨x, y, hxy, h₁, h₂⟩
  have hsx : Vx ⊆ V(G₀) := hV ▸ subset_union_left
  have hsy : Vy ⊆ V(G₀) := hV ▸ subset_union_right
  have hTx : Ex ⊆ E(G₀) := hE ▸ subset_union_left
  have hTy : Ey ⊆ E(G₀) := hE ▸ subset_union_right
  have hex := hE' (Z := Ex) hTx hlx rfl
  have hey := hE' (Z := Ey) hTy hly rfl
  refine hG.2.2 ((G₀.induce Vx).restrict Ex) ((G₀.induce Vy).restrict Ey) ⟨?_, ?_, hV, ?_, ?_⟩ hc
  · exact restrict_le.trans (induce_le hsx)
  · exact restrict_le.trans (induce_le hsy)
  · rw [hex, hey]
    exact hE
  · rw [hex, hey]
    exact hd

/-- Each vertex of a simple 3-connected graph meets at least three edges. -/
theorem IsSimpleThreeConnected.exists_three_edges (hG : IsSimpleThreeConnectedGraph G₀) {v : α}
    (hv : v ∈ V(G₀)) :
    ∃ e f g, e ≠ f ∧ e ≠ g ∧ f ≠ g ∧ G₀.Inc e v ∧ G₀.Inc f v ∧ G₀.Inc g v := by
  classical
  by_contra hno
  push Not at hno
  have hcard4 := hG.2.1
  have hfin : V(G₀).Finite := by
    by_contra hinf
    rw [Set.Infinite.ncard hinf] at hcard4
    omega
  let N : Set α := {w | ∃ e, G₀.IsLink e v w}
  have hNfin : N.Finite := hfin.subset fun w ⟨e, he⟩ => he.right_mem
  have hN : N.ncard ≤ 2 := by
    by_contra hlt
    obtain ⟨a, b, c, ⟨e₁, h₁⟩, ⟨e₂, h₂⟩, ⟨e₃, h₃⟩, hab, hac, hbc⟩ :=
      (Set.two_lt_ncard_iff hNfin).mp (by omega)
    have hne : ∀ {e f x y}, G₀.IsLink e v x → G₀.IsLink f v y → x ≠ y → e ≠ f := by
      rintro e f x y hx hy hxy rfl
      apply hxy
      rcases G₀.eq_or_eq_of_isLink_of_isLink hx.symm hy with h | h
      · subst h
        exact (hG.1.1 e hx.edge_mem x hx).elim
      · exact h
    exact hno e₁ e₂ e₃ (hne h₁ h₂ hab) (hne h₁ h₃ hac) (hne h₂ h₃ hbc) ⟨a, h₁⟩ ⟨b, h₂⟩ ⟨c, h₃⟩
  have hle3 : ({v} ∪ N).ncard ≤ 3 :=
    (Set.ncard_union_le _ _).trans (by rw [Set.ncard_singleton]; omega)
  have hs := IsSimpleThreeConnected.sep hG (Vx := {v} ∪ N) (Vy := V(G₀) \ {v})
    (Ex := {e | G₀.Inc e v}) (Ey := E(G₀) \ {e | G₀.Inc e v}) ?_ ?_ disjoint_sdiff_right ?_ ?_ ?_
  · rcases hs with hs | hs
    · rw [hs] at hle3
      omega
    · have hvv : v ∈ V(G₀) \ {v} := by rw [hs]; exact hv
      exact hvv.2 rfl
  · ext y
    constructor
    · rintro ((hy | ⟨e, hy⟩) | hy)
      · rw [mem_singleton_iff.mp hy]
        exact hv
      · exact hy.right_mem
      · exact hy.1
    · intro hy
      by_cases hyv : y = v
      · exact Or.inl (Or.inl hyv)
      · exact Or.inr ⟨hy, hyv⟩
  · ext e
    constructor
    · rintro (he | he)
      · exact Graph.Inc.edge_mem he
      · exact he.1
    · intro he
      by_cases hev : G₀.Inc e v
      · exact Or.inl hev
      · exact Or.inr ⟨he, hev⟩
  · rintro e ⟨z, hz⟩ x y hxy
    have hmem : ∀ t, t = v ∨ t = z → t ∈ ({v} ∪ N) := by
      rintro t (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr ⟨e, hz⟩
    exact ⟨hmem x (G₀.eq_or_eq_of_isLink_of_isLink hxy hz),
      hmem y (G₀.eq_or_eq_of_isLink_of_isLink hxy.symm hz)⟩
  · rintro e he x y hxy
    refine ⟨⟨hxy.left_mem, ?_⟩, ⟨hxy.right_mem, ?_⟩⟩
    · rintro rfl
      exact he.2 ⟨y, hxy⟩
    · rintro rfl
      exact he.2 ⟨x, hxy.symm⟩
  · have hsub : ({v} ∪ N) ∩ (V(G₀) \ {v}) ⊆ N := by
      rintro y ⟨hy | hy, -, hyv⟩
      · exact (hyv hy).elim
      · exact hy
    have := Set.ncard_le_ncard hsub hNfin
    omega

/-- Each vertex of a simple 3-connected graph meets at least two edges. -/
theorem IsSimpleThreeConnected.exists_two_edges (hG : IsSimpleThreeConnectedGraph G₀) {v : α}
    (hv : v ∈ V(G₀)) : ∃ e f, e ≠ f ∧ G₀.Inc e v ∧ G₀.Inc f v := by
  classical
  by_contra hno
  push Not at hno
  have huniq : ∀ e f, G₀.Inc e v → G₀.Inc f v → e = f := by
    intro e f he hf
    by_contra hne
    exact hno e f hne he hf
  let Vx : Set α := {v} ∪ {w | ∃ e, G₀.IsLink e v w}
  have hVx : ∃ w, Vx ⊆ {v, w} := by
    by_cases hex : ∃ e w, G₀.IsLink e v w
    · obtain ⟨e, w, hw⟩ := hex
      refine ⟨w, ?_⟩
      rintro y (rfl | ⟨e', hy⟩)
      · exact Or.inl rfl
      · have hee : e' = e := huniq _ _ ⟨y, hy⟩ ⟨w, hw⟩
        subst hee
        rcases G₀.eq_or_eq_of_isLink_of_isLink hy.symm hw with h | h
        · exact Or.inl h
        · exact Or.inr h
    · refine ⟨v, ?_⟩
      rintro y (rfl | ⟨e', hy⟩)
      · exact Or.inl rfl
      · exact (hex ⟨e', y, hy⟩).elim
  obtain ⟨w, hw⟩ := hVx
  have hcard4 := hG.2.1
  have hfin : V(G₀).Finite := by
    by_contra hinf
    rw [Set.Infinite.ncard hinf] at hcard4
    omega
  have hle2 : Vx.ncard ≤ 2 :=
    (Set.ncard_le_ncard hw (Set.toFinite _)).trans (Set.ncard_insert_le v {w} |>.trans (by simp))
  have hs := IsSimpleThreeConnected.sep hG (Vx := Vx) (Vy := V(G₀) \ {v})
    (Ex := {e | G₀.Inc e v}) (Ey := E(G₀) \ {e | G₀.Inc e v}) ?_ ?_ disjoint_sdiff_right ?_ ?_ ?_
  · rcases hs with hs | hs
    · rw [hs] at hle2
      omega
    · have hvv : v ∈ V(G₀) \ {v} := by rw [hs]; exact hv
      exact hvv.2 rfl
  · ext y
    constructor
    · rintro ((hy | ⟨e, hy⟩) | hy)
      · rw [mem_singleton_iff.mp hy]
        exact hv
      · exact hy.right_mem
      · exact hy.1
    · intro hy
      by_cases hyv : y = v
      · exact Or.inl (Or.inl hyv)
      · exact Or.inr ⟨hy, hyv⟩
  · ext e
    constructor
    · rintro (he | he)
      · exact Graph.Inc.edge_mem he
      · exact he.1
    · intro he
      by_cases hev : G₀.Inc e v
      · exact Or.inl hev
      · exact Or.inr ⟨he, hev⟩
  · rintro e ⟨z, hz⟩ x y hxy
    have hmem : ∀ t, t = v ∨ t = z → t ∈ Vx := by
      rintro t (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr ⟨e, hz⟩
    exact ⟨hmem x (G₀.eq_or_eq_of_isLink_of_isLink hxy hz),
      hmem y (G₀.eq_or_eq_of_isLink_of_isLink hxy.symm hz)⟩
  · rintro e he x y hxy
    refine ⟨⟨hxy.left_mem, ?_⟩, ⟨hxy.right_mem, ?_⟩⟩
    · rintro rfl
      exact he.2 ⟨y, hxy⟩
    · rintro rfl
      exact he.2 ⟨x, hxy.symm⟩
  · have hsub : Vx ∩ (V(G₀) \ {v}) ⊆ {w} := by
      rintro y ⟨hy, -, hyv⟩
      rcases hw hy with h | h
      · exact (hyv h).elim
      · exact h
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton] at this
    omega

end ThreeConnected

/-! ## 3. Subdivisions -/

/-- The set of vertices that meet an edge of `A`. -/
def verts (G : Graph α β) (A : Set β) : Set α := {v | ∃ e ∈ A, G.Inc e v}

/-- The vertices that meet an edge of `A` and an edge of `G` outside `A`. -/
def bdry (G : Graph α β) (A : Set β) : Set α := verts G A ∩ verts G (E(G) \ A)

theorem bdry_compl {G : Graph α β} {A : Set β} (hA : A ⊆ E(G)) :
    bdry G (E(G) \ A) = bdry G A := by
  unfold bdry
  rw [sdiff_sdiff_eq_self hA, inter_comm]

/-- The data of a subdivision, as a structure. -/
structure SubData (G G₀ : Graph α β) (P : β → Graph α β) : Prop where
  simple : IsSimpleThreeConnectedGraph G₀
  sub : V(G₀) ⊆ V(G)
  path : ∀ e ∈ E(G₀), ∃ u v : α, G₀.IsLink e u v ∧ IsGraphPathWithEnds G (P e) u v ∧
    E(P e).Nonempty ∧ V(P e) ∩ V(G₀) = {u, v}
  disj : ∀ e₁ ∈ E(G₀), ∀ e₂ ∈ E(G₀), e₁ ≠ e₂ →
    Disjoint E(P e₁) E(P e₂) ∧ V(P e₁) ∩ V(P e₂) ⊆ V(G₀)
  vunion : V(G) = V(G₀) ∪ (⋃ e ∈ E(G₀), V(P e))
  eunion : E(G) = ⋃ e ∈ E(G₀), E(P e)

theorem exists_subData {G : Graph α β} (h : IsSubdivisionOfSimpleThreeConnected G) :
    ∃ G₀ P, SubData G G₀ P := by
  obtain ⟨G₀, hs, hsub, P, h₁, h₂, h₃, h₄⟩ := h
  exact ⟨G₀, P, hs, hsub, h₁, h₂, h₃, h₄⟩

namespace SubData

variable {G G₀ : Graph α β} {P : β → Graph α β} (h : SubData G G₀ P)
include h

theorem ne_of_link {e : β} {u v : α} (hl : G₀.IsLink e u v) : u ≠ v := by
  rintro rfl
  exact h.simple.1.1 e hl.edge_mem u hl

theorem finite_V₀ : V(G₀).Finite := by
  by_contra hinf
  have := h.simple.2.1
  rw [Set.Infinite.ncard hinf] at this
  omega

/-- An inner vertex of a path is not in `V(G₀)`, so the edges of the path are on one side of any
set whose boundary lies in `V(G₀)`. -/
theorem pure {e : β} (he : e ∈ E(G₀)) {A : Set β} (hbd : bdry G A ⊆ V(G₀)) :
    E(P e) ⊆ A ∨ Disjoint E(P e) A := by
  obtain ⟨u, v, -, ⟨hle, W, hs, hV, hE⟩, -, hcap⟩ := h.path e he
  have hall : ∀ e' ∈ W.edges, ∀ f' ∈ W.edges, e' ∈ A ↔ f' ∈ A := by
    refine walk_pure W hs fun x hx hxu hxv e' he' f' hf' hi hi' => ?_
    have hxV : x ∉ V(G₀) := by
      intro hx₀
      have hm : x ∈ V(P e) ∩ V(G₀) := ⟨hV ▸ hx, hx₀⟩
      rw [hcap] at hm
      rcases hm with hm | hm
      · exact hxu hm
      · exact hxv hm
    have hmemE : ∀ {g}, g ∈ W.edges → g ∈ E(G) := fun {g} hg => by
      have : g ∈ E(P e) := by rw [hE]; exact hg
      exact hle.edgeSet_mono this
    have hincG : ∀ {g}, P e |>.Inc g x → G.Inc g x := fun ⟨y, hy⟩ => ⟨y, hy.mono hle⟩
    constructor
    · intro h₁
      by_contra h₂
      exact hxV (hbd ⟨⟨e', h₁, hincG hi⟩, f', ⟨hmemE hf', h₂⟩, hincG hi'⟩)
    · intro h₁
      by_contra h₂
      exact hxV (hbd ⟨⟨f', h₁, hincG hi'⟩, e', ⟨hmemE he', h₂⟩, hincG hi⟩)
  by_cases hex : ∃ e' ∈ W.edges, e' ∈ A
  · obtain ⟨e', he', hA⟩ := hex
    left
    intro f hf
    rw [hE] at hf
    exact (hall e' he' f hf).mp hA
  · right
    rw [Set.disjoint_left]
    intro f hf hA
    rw [hE] at hf
    exact hex ⟨f, hf, hA⟩

/-- A path has an edge at each of its two ends. -/
theorem exists_edge_at_ends {e : β} {u v : α} (hl : G₀.IsLink e u v) :
    (∃ g ∈ E(P e), G.Inc g u) ∧ ∃ g ∈ E(P e), G.Inc g v := by
  obtain ⟨u', v', hl', ⟨hle, W, hs, -, hE⟩, -, -⟩ := h.path e hl.edge_mem
  have huv := h.ne_of_link hl'
  obtain ⟨g₁, hg₁, y₁, hy₁⟩ := exists_edge_at_start W huv
  obtain ⟨g₂, hg₂, y₂, hy₂⟩ := exists_edge_at_start W.reverse huv.symm
  have hg₂' : g₂ ∈ W.edges := by
    rw [GraphWalk.edges_reverse] at hg₂
    exact List.mem_reverse.mp hg₂
  have hm₁ : g₁ ∈ E(P e) := by rw [hE]; exact hg₁
  have hm₂ : g₂ ∈ E(P e) := by rw [hE]; exact hg₂'
  have hu : (∃ g ∈ E(P e), G.Inc g u') ∧ ∃ g ∈ E(P e), G.Inc g v' :=
    ⟨⟨g₁, hm₁, y₁, hy₁.mono hle⟩, ⟨g₂, hm₂, y₂, hy₂.mono hle⟩⟩
  have hc : (u = u' ∧ v = v') ∨ (u = v' ∧ v = u') := by
    rcases G₀.eq_or_eq_of_isLink_of_isLink hl hl' with rfl | rfl
    · left
      refine ⟨rfl, ?_⟩
      rcases G₀.eq_or_eq_of_isLink_of_isLink hl.symm hl' with h' | h'
      · exact (h.ne_of_link hl h'.symm).elim
      · exact h'
    · right
      refine ⟨rfl, ?_⟩
      rcases G₀.eq_or_eq_of_isLink_of_isLink hl.symm hl' with h' | h'
      · exact h'
      · exact (h.ne_of_link hl h'.symm).elim
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hu
  · exact ⟨hu.2, hu.1⟩

/-- A vertex of `V(G₀)` meets two paths. -/
theorem exists_other_edge {e : β} {u v : α} (hl : G₀.IsLink e u v) :
    ∃ g, g ∈ E(G) ∧ g ∉ E(P e) ∧ G.Inc g u := by
  obtain ⟨e₁, e₂, hne, h₁, h₂⟩ := IsSimpleThreeConnected.exists_two_edges h.simple hl.left_mem
  have hkey : ∀ {f : β}, f ≠ e → G₀.Inc f u → ∃ g, g ∈ E(G) ∧ g ∉ E(P e) ∧ G.Inc g u := by
    rintro f hfe ⟨w, hw⟩
    obtain ⟨g, hg, hinc⟩ := (h.exists_edge_at_ends hw).1
    refine ⟨g, ?_, ?_, hinc⟩
    · rw [h.eunion]
      exact mem_iUnion₂.mpr ⟨f, hw.edge_mem, hg⟩
    · intro hg'
      exact Set.disjoint_left.mp (h.disj f hw.edge_mem e hl.edge_mem hfe).1 hg hg'
  by_cases he₁ : e₁ = e
  · exact hkey (fun h' => hne (he₁.trans h'.symm)) h₂
  · exact hkey he₁ h₁

/-- The ends of a path are on the boundary of its edge set. -/
theorem ends_mem_bdry {e : β} {u v : α} (hl : G₀.IsLink e u v) :
    u ∈ bdry G E(P e) ∧ v ∈ bdry G E(P e) := by
  obtain ⟨⟨g₁, hg₁, hi₁⟩, g₂, hg₂, hi₂⟩ := h.exists_edge_at_ends hl
  obtain ⟨f₁, hf₁, hn₁, hj₁⟩ := h.exists_other_edge hl
  obtain ⟨f₂, hf₂, hn₂, hj₂⟩ := h.exists_other_edge hl.symm
  exact ⟨⟨⟨g₁, hg₁, hi₁⟩, f₁, ⟨hf₁, hn₁⟩, hj₁⟩, ⟨g₂, hg₂, hi₂⟩, f₂, ⟨hf₂, hn₂⟩, hj₂⟩

/-- One half of `sep`: if the vertices of the side outside `A` are all on the boundary, then that
side is one path. -/
theorem sep_aux {A : Set β} (hbd : bdry G A ⊆ V(G₀)) (hc : (bdry G A).ncard ≤ 2)
    (hne : (E(G) \ A).Nonempty) (hV : V(G₀) ⊆ bdry G A ∪ (V(G₀) ∩ verts G A)) :
    ∃ e ∈ E(G₀), E(G) \ A = E(P e) := by
  have hEdge : ∀ f ∈ E(G) \ A, ∃ e ∈ E(G₀), ∃ u v, G₀.IsLink e u v ∧ f ∈ E(P e) ∧
      Disjoint E(P e) A ∧ u ∈ bdry G A ∧ v ∈ bdry G A := by
    intro f hf
    have hf' := hf.1
    rw [h.eunion] at hf'
    obtain ⟨e, he, hfe⟩ := mem_iUnion₂.mp hf'
    obtain ⟨u, v, hl, -, -, -⟩ := h.path e he
    have hd : Disjoint E(P e) A := by
      rcases h.pure he hbd with h' | h'
      · exact (hf.2 (h' hfe)).elim
      · exact h'
    have hmem : ∀ {x y}, G₀.IsLink e x y → x ∈ bdry G A := by
      intro x y hxy
      obtain ⟨g, hg, hinc⟩ := (h.exists_edge_at_ends hxy).1
      have hgE : g ∈ E(G) := by
        rw [h.eunion]
        exact mem_iUnion₂.mpr ⟨e, he, hg⟩
      have hgA : g ∉ A := Set.disjoint_left.mp hd hg
      rcases hV hxy.left_mem with hb | ⟨-, hv⟩
      · exact hb
      · exact ⟨hv, g, ⟨hgE, hgA⟩, hinc⟩
    exact ⟨e, he, u, v, hl, hfe, hd, hmem hl, hmem hl.symm⟩
  obtain ⟨f, hf⟩ := hne
  obtain ⟨e, he, u, v, hl, hfe, hd, hu, hv⟩ := hEdge f hf
  refine ⟨e, he, Subset.antisymm ?_ ?_⟩
  · intro f' hf'
    obtain ⟨e', he', u', v', hl', hfe', -, hu', hv'⟩ := hEdge f' hf'
    have huv := h.ne_of_link hl
    have hfin : (bdry G A).Finite := h.finite_V₀.subset hbd
    have heqb : bdry G A = {u, v} := by
      symm
      refine Set.eq_of_subset_of_ncard_le ?_ ?_ hfin
      · rintro x (rfl | rfl)
        · exact hu
        · exact hv
      · rw [Set.ncard_pair huv]
        exact hc
    rw [heqb] at hu' hv'
    have huv' := h.ne_of_link hl'
    have hee : e' = e := by
      rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
      · exact (huv' rfl).elim
      · exact h.simple.1.2 e' hl'.edge_mem e hl.edge_mem _ _ hl' hl
      · exact h.simple.1.2 e' hl'.edge_mem e hl.edge_mem _ _ hl' hl.symm
      · exact (huv' rfl).elim
    exact hee ▸ hfe'
  · intro g hg
    have hgE : g ∈ E(G) := by
      rw [h.eunion]
      exact mem_iUnion₂.mpr ⟨e, he, hg⟩
    exact ⟨hgE, Set.disjoint_left.mp hd hg⟩

/-- A separation of `G` of order at most two at vertices of `V(G₀)` has a path as one side. -/
theorem sep {A : Set β} (hA : A ⊆ E(G)) (hbd : bdry G A ⊆ V(G₀)) (hc : (bdry G A).ncard ≤ 2)
    (hne : A.Nonempty) (hne' : (E(G) \ A).Nonempty) :
    ∃ e ∈ E(G₀), A = E(P e) ∨ E(G) \ A = E(P e) := by
  have hat : ∀ {x}, x ∈ V(G₀) → x ∈ verts G A ∨ x ∈ verts G (E(G) \ A) := by
    intro x hx
    obtain ⟨e, -, -, ⟨y, hy⟩, -⟩ := IsSimpleThreeConnected.exists_two_edges h.simple hx
    obtain ⟨g, hg, hinc⟩ := (h.exists_edge_at_ends hy).1
    have hgE : g ∈ E(G) := by
      rw [h.eunion]
      exact mem_iUnion₂.mpr ⟨e, hy.edge_mem, hg⟩
    by_cases hgA : g ∈ A
    · exact Or.inl ⟨g, hgA, hinc⟩
    · exact Or.inr ⟨g, ⟨hgE, hgA⟩, hinc⟩
  let Vx : Set α := bdry G A ∪ (V(G₀) ∩ verts G A)
  let Vy : Set α := bdry G A ∪ (V(G₀) ∩ verts G (E(G) \ A))
  have hVx : ∀ {e u v}, G₀.IsLink e u v → E(P e) ⊆ A → u ∈ Vx := by
    intro e u v hl hs
    obtain ⟨g, hg, hinc⟩ := (h.exists_edge_at_ends hl).1
    exact Or.inr ⟨hl.left_mem, g, hs hg, hinc⟩
  have hVy : ∀ {e u v}, G₀.IsLink e u v → Disjoint E(P e) A → u ∈ Vy := by
    intro e u v hl hs
    obtain ⟨g, hg, hinc⟩ := (h.exists_edge_at_ends hl).1
    have hgE : g ∈ E(G) := by
      rw [h.eunion]
      exact mem_iUnion₂.mpr ⟨e, hl.edge_mem, hg⟩
    exact Or.inr ⟨hl.left_mem, g, ⟨hgE, Set.disjoint_left.mp hs hg⟩, hinc⟩
  have hs := IsSimpleThreeConnected.sep h.simple (Vx := Vx) (Vy := Vy) (Ex
    := {e ∈ E(G₀) | E(P e) ⊆ A})
    (Ey := {e ∈ E(G₀) | Disjoint E(P e) A}) ?_ ?_ ?_ ?_ ?_ ?_
  · rcases hs with hs | hs
    · obtain ⟨e, he, heq⟩ := h.sep_aux hbd hc hne' hs.symm.subset
      exact ⟨e, he, Or.inr heq⟩
    · have hbd' : bdry G (E(G) \ A) ⊆ V(G₀) := by rwa [bdry_compl hA]
      have hc' : (bdry G (E(G) \ A)).ncard ≤ 2 := by rwa [bdry_compl hA]
      have hne'' : (E(G) \ (E(G) \ A)).Nonempty := by rwa [sdiff_sdiff_eq_self hA]
      obtain ⟨e, he, heq⟩ := h.sep_aux hbd' hc' hne'' (by
        rw [bdry_compl hA]
        exact hs.symm.subset)
      rw [sdiff_sdiff_eq_self hA] at heq
      exact ⟨e, he, Or.inl heq⟩
  · ext x
    constructor
    · rintro ((hx | hx) | (hx | hx))
      · exact hbd hx
      · exact hx.1
      · exact hbd hx
      · exact hx.1
    · intro hx
      rcases hat hx with hv | hv
      · exact Or.inl (Or.inr ⟨hx, hv⟩)
      · exact Or.inr (Or.inr ⟨hx, hv⟩)
  · ext e
    constructor
    · rintro (he | he) <;> exact he.1
    · intro he
      rcases h.pure he hbd with hp | hp
      · exact Or.inl ⟨he, hp⟩
      · exact Or.inr ⟨he, hp⟩
  · rw [Set.disjoint_left]
    rintro e ⟨he, h₁⟩ ⟨-, h₂⟩
    obtain ⟨u, v, -, -, ⟨g, hg⟩, -⟩ := h.path e he
    exact Set.disjoint_left.mp h₂ hg (h₁ hg)
  · rintro e ⟨-, hs⟩ x y hxy
    exact ⟨hVx hxy hs, hVx hxy.symm hs⟩
  · rintro e ⟨-, hs⟩ x y hxy
    exact ⟨hVy hxy hs, hVy hxy.symm hs⟩
  · have hsub : Vx ∩ Vy ⊆ bdry G A := by
      rintro x ⟨hx | ⟨-, hx⟩, hy | ⟨-, hy⟩⟩
      · exact hx
      · exact hx
      · exact hy
      · exact ⟨hx, hy⟩
    have := Set.ncard_le_ncard hsub (h.finite_V₀.subset hbd)
    omega

/-- A cut with at most one vertex, at a vertex of `V(G₀)`, does not exist: such a boundary has at
least two vertices. -/
theorem two_le_bdry {A : Set β} (hA : A ⊆ E(G)) (hbd : bdry G A ⊆ V(G₀)) (hne : A.Nonempty)
    (hne' : (E(G) \ A).Nonempty) : 2 ≤ (bdry G A).ncard := by
  by_contra hlt
  push Not at hlt
  obtain ⟨e, he, heq | heq⟩ := h.sep hA hbd (by omega) hne hne'
  · obtain ⟨u, v, hl, -⟩ := h.path e he
    obtain ⟨hu, hv⟩ := h.ends_mem_bdry hl
    rw [← heq] at hu hv
    have huv := h.ne_of_link hl
    have hsub : ({u, v} : Set α) ⊆ bdry G A := by
      rintro x (rfl | rfl)
      · exact hu
      · exact hv
    have := Set.ncard_le_ncard hsub (h.finite_V₀.subset hbd)
    rw [Set.ncard_pair huv] at this
    omega
  · obtain ⟨u, v, hl, -⟩ := h.path e he
    obtain ⟨hu, hv⟩ := h.ends_mem_bdry hl
    rw [← heq, bdry_compl hA] at hu hv
    have huv := h.ne_of_link hl
    have hsub : ({u, v} : Set α) ⊆ bdry G A := by
      rintro x (rfl | rfl)
      · exact hu
      · exact hv
    have := Set.ncard_le_ncard hsub (h.finite_V₀.subset hbd)
    rw [Set.ncard_pair huv] at this
    omega

omit h in
/-- An edge of a path of `G` at a vertex gives a link in the path. -/
theorem inc_path {e g : β} {x : α} (hle : P e ≤ G) (hg : g ∈ E(P e)) (hx : G.Inc g x) :
    (P e).Inc g x := by
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, (hle.isLink_iff hg).mpr hy⟩

/-- Two edges of one path `P e` at a vertex of `V(G₀)` are equal. -/
theorem eq_of_end {e a b : β} {x : α} (he : e ∈ E(G₀)) (hx : x ∈ V(G₀)) (ha : a ∈ E(P e))
    (hb : b ∈ E(P e)) (hax : G.Inc a x) (hbx : G.Inc b x) : a = b := by
  obtain ⟨u, v, -, ⟨hle, W, hs, hV, hE⟩, -, hcap⟩ := h.path e he
  have hia := SubData.inc_path hle ha hax
  have hib := SubData.inc_path hle hb hbx
  have hmem : x ∈ V(P e) ∩ V(G₀) := ⟨hia.vertex_mem, hx⟩
  rw [hcap] at hmem
  have ha' : a ∈ W.edges := by rw [hE] at ha; exact ha
  have hb' : b ∈ W.edges := by rw [hE] at hb; exact hb
  rcases hmem with rfl | hmem
  · exact eq_of_inc_start W hs ha' hb' hia hib
  · obtain rfl : x = v := hmem
    refine eq_of_inc_start W.reverse hs.reverse ?_ ?_ hia hib
    · rw [GraphWalk.edges_reverse, List.mem_reverse]; exact ha'
    · rw [GraphWalk.edges_reverse, List.mem_reverse]; exact hb'

/-- A vertex that meets three edges of `G` is in `V(G₀)`. -/
theorem mem_V₀_of_three {x : α} {e₁ e₂ e₃ : β} (h₁ : e₁ ∈ E(G)) (h₂ : e₂ ∈ E(G)) (h₃ : e₃ ∈ E(G))
    (hx₁ : G.Inc e₁ x) (hx₂ : G.Inc e₂ x) (hx₃ : G.Inc e₃ x) (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃)
    (h23 : e₂ ≠ e₃) : x ∈ V(G₀) := by
  by_contra hx
  have hfind : ∀ g, g ∈ E(G) → G.Inc g x → ∃ e ∈ E(G₀), g ∈ E(P e) ∧ x ∈ V(P e) := by
    intro g hg hi
    rw [h.eunion] at hg
    obtain ⟨e, he, hge⟩ := mem_iUnion₂.mp hg
    obtain ⟨u, v, -, hp, -, -⟩ := h.path e he
    obtain ⟨y, hy⟩ := hi
    exact ⟨e, he, hge, ((hp.le.isLink_iff hge).mpr hy).left_mem⟩
  obtain ⟨a₁, ha₁, hm₁, hv₁⟩ := hfind e₁ h₁ hx₁
  obtain ⟨a₂, ha₂, hm₂, hv₂⟩ := hfind e₂ h₂ hx₂
  obtain ⟨a₃, ha₃, hm₃, hv₃⟩ := hfind e₃ h₃ hx₃
  have hsame : ∀ {a b}, a ∈ E(G₀) → b ∈ E(G₀) → x ∈ V(P a) → x ∈ V(P b) → a = b := by
    intro a b ha hb hxa hxb
    by_contra hne
    exact hx ((h.disj a ha b hb hne).2 ⟨hxa, hxb⟩)
  obtain rfl := hsame ha₁ ha₂ hv₁ hv₂
  obtain rfl := hsame ha₁ ha₃ hv₁ hv₃
  obtain ⟨u, v, -, ⟨hle, W, hs, -, hE⟩, -, -⟩ := h.path a₁ ha₁
  rw [hE] at hm₁ hm₂ hm₃
  have hm₁' : e₁ ∈ E(P a₁) := by rw [hE]; exact hm₁
  have hm₂' : e₂ ∈ E(P a₁) := by rw [hE]; exact hm₂
  have hm₃' : e₃ ∈ E(P a₁) := by rw [hE]; exact hm₃
  exact not_three_edges W hs hm₁ hm₂ hm₃ (SubData.inc_path hle hm₁' hx₁)
    (SubData.inc_path hle hm₂' hx₂)
    (SubData.inc_path hle hm₃' hx₃) h12 h13 h23

/-- Each vertex of `G` meets at least two edges. -/
theorem exists_two_edges {x : α} (hx : x ∈ V(G)) :
    ∃ e ∈ E(G), ∃ f ∈ E(G), e ≠ f ∧ G.Inc e x ∧ G.Inc f x := by
  by_cases hx₀ : x ∈ V(G₀)
  · obtain ⟨e, -, -, ⟨y, hy⟩, -⟩ := IsSimpleThreeConnected.exists_two_edges h.simple hx₀
    obtain ⟨g, hg, hinc⟩ := (h.exists_edge_at_ends hy).1
    obtain ⟨f, hf, hn, hj⟩ := h.exists_other_edge hy
    have hgE : g ∈ E(G) := by
      rw [h.eunion]
      exact mem_iUnion₂.mpr ⟨e, hy.edge_mem, hg⟩
    exact ⟨g, hgE, f, hf, fun heq => hn (heq ▸ hg), hinc, hj⟩
  · rw [h.vunion] at hx
    rcases hx with hx | hx
    · exact (hx₀ hx).elim
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      obtain ⟨u, v, -, ⟨hle, W, hs, hV, hE⟩, -, hcap⟩ := h.path e he
      have hne : ∀ {t}, t ∈ ({u, v} : Set α) → x ≠ t := by
        intro t ht hxt
        rw [← hcap] at ht
        exact hx₀ (hxt ▸ ht.2)
      obtain ⟨a, ha, b, hb, hab, h₁, h₂⟩ := exists_two_edges_at_inner W hs
        (by rw [hV] at hxe; exact hxe) (hne (Or.inl rfl)) (hne (Or.inr rfl))
      have hm : ∀ {g}, g ∈ W.edges → g ∈ E(G) := fun {g} hg => by
        have : g ∈ E(P e) := by rw [hE]; exact hg
        exact hle.edgeSet_mono this
      obtain ⟨y₁, hy₁⟩ := h₁
      obtain ⟨y₂, hy₂⟩ := h₂
      exact ⟨a, hm ha, b, hm hb, hab, ⟨y₁, hy₁.mono hle⟩, ⟨y₂, hy₂.mono hle⟩⟩

end SubData

/-! ## 4. Bridges -/

section Bridges

variable {G : Graph α β} {B : Set α} {M : Set β}

/-- Two edges of `M` that share a vertex outside `B`. -/
def adj (G : Graph α β) (B : Set α) (M : Set β) (e f : β) : Prop :=
  e ∈ M ∧ f ∈ M ∧ ∃ w, w ∉ B ∧ G.Inc e w ∧ G.Inc f w

/-- The bridge of `e`: the edges of `M` joined to `e` through vertices outside `B`. -/
def cls (G : Graph α β) (B : Set α) (M : Set β) (e : β) : Set β :=
  {f | Relation.ReflTransGen (adj G B M) e f}

theorem mem_cls_self {e : β} : e ∈ cls G B M e := Relation.ReflTransGen.refl

theorem cls_step {e f g : β} (hf : f ∈ cls G B M e) (h : adj G B M f g) : g ∈ cls G B M e :=
  Relation.ReflTransGen.tail hf h

theorem cls_subset {e : β} (he : e ∈ M) : cls G B M e ⊆ M := by
  intro f hf
  induction hf with
  | refl => exact he
  | tail _ h _ => exact h.2.1

theorem cls_symm {e f : β} (hf : f ∈ cls G B M e) : e ∈ cls G B M f := by
  induction hf with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih =>
    obtain ⟨h₁, h₂, w, hw, i₁, i₂⟩ := h
    exact Relation.ReflTransGen.head ⟨h₂, h₁, w, hw, i₂, i₁⟩ ih

theorem cls_trans {e f g : β} (hf : f ∈ cls G B M e) (hg : g ∈ cls G B M f) : g ∈ cls G B M e :=
  Relation.ReflTransGen.trans hf hg

/-- A bridge meets the rest of the graph only in `B`, if each edge outside `M` has its ends in
`B`. -/
theorem bdry_cls {e : β} (he : e ∈ M) (hB : ∀ v, v ∉ B → ∀ h ∈ E(G), G.Inc h v → h ∈ M) :
    bdry G (cls G B M e) ⊆ B := by
  rintro v ⟨⟨f, hf, hv⟩, h, ⟨hE, hn⟩, hi⟩
  by_contra hvB
  exact hn (cls_step hf ⟨cls_subset he hf, hB v hvB h hE hi, v, hvB, hv, hi⟩)

/-- Walks inside a bridge. -/
theorem exists_walk_in_cls {e f₀ : β} (_he : e ∈ M) (hf₀ : f₀ ∈ cls G B M e) {a m : α}
    (hl : G.IsLink f₀ a m) {f : β} (hf : f ∈ cls G B M f₀) {p : α} (hp : G.Inc f p) :
    ∃ W : GraphWalk G a p, (∀ g ∈ W.edges, g ∈ cls G B M e) ∧
      ∀ x ∈ W.support, x ∉ B ∨ x = a ∨ x = p := by
  induction hf generalizing p with
  | refl =>
    obtain ⟨y, hy⟩ := hp
    rcases G.eq_or_eq_of_isLink_of_isLink hy hl with rfl | rfl
    · refine ⟨.nil hl.left_mem, by simp [GraphWalk.edges], ?_⟩
      intro x hx
      simp only [GraphWalk.support, List.mem_singleton] at hx
      exact Or.inr (Or.inl hx)
    · refine ⟨.cons hl (.nil hl.right_mem), ?_, ?_⟩
      · intro g hg
        simp only [GraphWalk.edges, List.mem_cons, List.not_mem_nil, or_false] at hg
        exact hg ▸ hf₀
      · intro x hx
        simp only [GraphWalk.support, List.mem_cons, List.not_mem_nil,
          or_false] at hx
        rcases hx with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
  | @tail f g hfr hadj ih =>
    have hgc : g ∈ cls G B M e := cls_trans hf₀ (Relation.ReflTransGen.tail hfr hadj)
    obtain ⟨-, -, w, hw, hfw, hgw⟩ := hadj
    obtain ⟨W, hE, hS⟩ := ih hfw
    obtain ⟨y, hy⟩ := hp
    obtain ⟨z, hz⟩ := hgw
    rcases G.eq_or_eq_of_isLink_of_isLink hy hz with rfl | rfl
    · refine ⟨W, hE, fun x hx => ?_⟩
      rcases hS x hx with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inl (h ▸ hw)
    · refine ⟨W.append (.cons hz (.nil hz.right_mem)), ?_, ?_⟩
      · intro g' hg'
        rw [GraphWalk.edges_append] at hg'
        rcases List.mem_append.mp hg' with h | h
        · exact hE g' h
        · simp only [GraphWalk.edges, List.mem_cons, List.not_mem_nil, or_false] at h
          exact h ▸ hgc
      · intro x hx
        rw [GraphWalk.mem_support_append] at hx
        rcases hx with hx | hx
        · rcases hS x hx with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inl (h ▸ hw)
        · simp only [GraphWalk.support, List.mem_cons, List.not_mem_nil,
            or_false] at hx
          rcases hx with rfl | rfl
          · exact Or.inl hw
          · exact Or.inr (Or.inr rfl)

end Bridges

namespace SubData

variable {G G₀ : Graph α β} {P : β → Graph α β} (h : SubData G G₀ P)
include h

/-- An ear. Let `Hs` be a nonempty set of edges with its ends in `Hv`, and let `g` be another edge.
If the vertices of `Hv` that meet edges outside `Hs` are in `V(G₀)`, then the bridge of `g` has a
path between two distinct vertices of `Hv`, with no other vertex in `Hv`. -/
theorem exists_ear {Hv : Set α} {Hs : Set β} (hHs : Hs ⊆ E(G)) (hne : Hs.Nonempty)
    (hinc : ∀ e ∈ Hs, ∀ v, G.Inc e v → v ∈ Hv)
    (hV₀ : ∀ v ∈ Hv, ∀ f ∈ E(G), f ∉ Hs → G.Inc f v → v ∈ V(G₀)) {g : β} (hg : g ∈ E(G))
    (hgH : g ∉ Hs) :
    ∃ (x y : α) (W : GraphWalk G x y), x ≠ y ∧ W.IsSimple ∧ x ∈ Hv ∧ y ∈ Hv ∧ x ∈ V(G₀) ∧
      y ∈ V(G₀) ∧ (∀ e ∈ W.edges, e ∈ cls G Hv (E(G) \ Hs) g) ∧
      ∀ z ∈ W.support, z ∉ Hv ∨ z = x ∨ z = y := by
  have hgM : g ∈ E(G) \ Hs := ⟨hg, hgH⟩
  set c := cls G Hv (E(G) \ Hs) g with hc
  have hcsub : c ⊆ E(G) \ Hs := cls_subset hgM
  have hbd : bdry G c ⊆ Hv := bdry_cls hgM fun v hv f hf hi =>
    ⟨hf, fun hfH => hv (hinc f hfH v hi)⟩
  have hbd₀ : bdry G c ⊆ V(G₀) := by
    rintro v hv
    obtain ⟨⟨f, hf, hi⟩, -⟩ := id hv
    exact hV₀ v (hbd hv) f (hcsub hf).1 (hcsub hf).2 hi
  obtain ⟨t, ht⟩ := hne
  have htc : t ∉ c := fun h' => (hcsub h').2 ht
  have h2 := h.two_le_bdry (A := c) (fun e he => (hcsub he).1) hbd₀ ⟨g, mem_cls_self⟩
    ⟨t, hHs ht, htc⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := (Set.one_lt_ncard (h.finite_V₀.subset hbd₀)).mp (by omega)
  obtain ⟨⟨f₀, hf₀, a, hl⟩, -⟩ := id hx
  obtain ⟨⟨f₁, hf₁, hy'⟩, -⟩ := id hy
  obtain ⟨W, hE, hS⟩ := exists_walk_in_cls hgM hf₀ hl (cls_trans (cls_symm hf₀) hf₁) hy'
  obtain ⟨W', hs, hsupp, hedges⟩ := GM09.exists_isSimple_subwalk W
  exact ⟨x, y, W', hxy, hs, hbd hx, hbd hy, hbd₀ hx, hbd₀ hy, fun e he => hE e (hedges e he),
    fun z hz => hS z (hsupp z hz)⟩

/-- `G` has two paths with the same ends and no other common vertex, and no common edge. -/
theorem exists_two_paths {e : β} (he : e ∈ E(G₀)) :
    ∃ (x y : α) (W₁ W₂ : GraphWalk G x y), x ≠ y ∧ W₁.IsSimple ∧ W₂.IsSimple ∧
      (∀ z, z ∈ W₁.support → z ∈ W₂.support → z = x ∨ z = y) ∧
      ∀ a ∈ W₁.edges, a ∉ W₂.edges := by
  obtain ⟨u, v, hl, ⟨hle, W, hs, hV, hE⟩, hne, hcap⟩ := h.path e he
  have hedges : ∀ {f}, f ∈ E(G₀) → E(P f) ⊆ E(G) := fun {f} hf a ha => by
    rw [h.eunion]
    exact mem_iUnion₂.mpr ⟨f, hf, ha⟩
  have hin₀ : ∀ z ∈ V(P e), z ∉ V(G₀) → z ≠ u ∧ z ≠ v := by
    refine fun z _ hz => ⟨fun h' => hz (h' ▸ hl.left_mem), fun h' => hz (h' ▸ hl.right_mem)⟩
  obtain ⟨g, hgE, hgn⟩ : ∃ g ∈ E(G), g ∉ E(P e) := by
    obtain ⟨a, b, hab, ia, ib⟩ := IsSimpleThreeConnected.exists_two_edges h.simple hl.left_mem
    obtain ⟨f, hf, hfe⟩ : ∃ f ∈ E(G₀), f ≠ e := by
      by_cases hae : a = e
      · exact ⟨b, ib.edge_mem, fun h' => hab (hae.trans h'.symm)⟩
      · exact ⟨a, ia.edge_mem, hae⟩
    obtain ⟨u', v', -, -, ⟨g, hg⟩, -⟩ := h.path f hf
    exact ⟨g, hedges hf hg, Set.disjoint_right.mp (h.disj e he f hf hfe.symm).1 hg⟩
  obtain ⟨x, y, W₂, hxy, hs₂, hx, hy, hx₀, hy₀, hE₂, hin⟩ := h.exists_ear (Hv := V(P e))
    (Hs := E(P e)) (hedges he) hne (fun a ha z hz => (SubData.inc_path hle ha hz).vertex_mem)
    (by
      intro z hz f hf hfn hif
      by_contra hz₀
      obtain ⟨hzu, hzv⟩ := hin₀ z hz hz₀
      obtain ⟨a, ha, b, hb, hab, ia, ib⟩ := exists_two_edges_at_inner W hs
        (by rw [hV] at hz; exact hz) hzu hzv
      have ha' : a ∈ E(P e) := by rw [hE]; exact ha
      have hb' : b ∈ E(P e) := by rw [hE]; exact hb
      have hia : G.Inc a z := by obtain ⟨w, hw⟩ := ia; exact ⟨w, hw.mono hle⟩
      have hib : G.Inc b z := by obtain ⟨w, hw⟩ := ib; exact ⟨w, hw.mono hle⟩
      exact hz₀ (h.mem_V₀_of_three (hedges he ha') (hedges he hb') hf hia hib hif hab
        (fun h' => hfn (h' ▸ ha')) (fun h' => hfn (h' ▸ hb'))))
    hgE hgn
  obtain ⟨W₀, hw₀, he₀⟩ := W.exists_transfer (G' := G) (fun a p q _ hlk => hlk.mono hle)
    (fun z hz => hle.vertexSet_mono (W.mem_vertexSet_of_mem_support hz))
  have hs₀ : W₀.IsSimple := by unfold GraphWalk.IsSimple; rw [hw₀]; exact hs
  have hmemV : ∀ z, z ∈ W₀.support → z ∈ V(P e) := fun z hz => by
    rw [hV, ← hw₀]; exact hz
  have hmemE : ∀ a, a ∈ W₀.edges → a ∈ E(P e) := fun a ha => by
    rw [hE, ← he₀]; exact ha
  have hE₂' : ∀ a ∈ W₂.edges, a ∉ E(P e) := fun a ha =>
    (cls_subset (G := G) (B := V(P e)) (M := E(G) \ E(P e)) ⟨hgE, hgn⟩ (hE₂ a ha)).2
  have hcapmem : ∀ z, z ∈ V(P e) → z ∈ V(G₀) → z = u ∨ z = v := fun z h₁ h₂ => by
    have : z ∈ V(P e) ∩ V(G₀) := ⟨h₁, h₂⟩
    rw [hcap] at this
    exact this
  rcases hcapmem x hx hx₀ with rfl | rfl <;> rcases hcapmem y hy hy₀ with rfl | rfl
  · exact (hxy rfl).elim
  · refine ⟨x, y, W₀, W₂, hxy, hs₀, hs₂, fun z h₁ h₂ => ?_, fun a ha ha' => hE₂' a ha' (hmemE a ha)⟩
    rcases hin z h₂ with h' | h'
    · exact (h' (hmemV z h₁)).elim
    · exact h'
  · refine ⟨x, y, W₀.reverse, W₂, hxy, hs₀.reverse, hs₂, fun z h₁ h₂ => ?_, fun a ha ha' => ?_⟩
    · rw [GraphWalk.support_reverse, List.mem_reverse] at h₁
      rcases hin z h₂ with h' | h'
      · exact (h' (hmemV z h₁)).elim
      · exact h'
    · rw [GraphWalk.edges_reverse, List.mem_reverse] at ha
      exact hE₂' a ha' (hmemE a ha)
  · exact (hxy rfl).elim

/-- A simple walk between two vertices of `V(G₀)` with all its edges in one path `P e` uses all
edges
of that path. -/
theorem thread_subset {e : β} (he : e ∈ E(G₀)) {x y : α} (hx : x ∈ V(G₀)) (hy : y ∈ V(G₀))
    (hxy : x ≠ y) (W' : GraphWalk G x y) (hs' : W'.IsSimple) (hE' : ∀ a ∈ W'.edges, a ∈ E(P e)) :
    E(P e) ⊆ {a | a ∈ W'.edges} := by
  obtain ⟨u, v, -, ⟨hle, W, hs, hV, hE⟩, -, hcap⟩ := h.path e he
  have hinner : ∀ z ∈ W.support, z ≠ u → z ≠ v → z ∉ V(G₀) := by
    intro z hz hzu hzv hz₀
    have hm : z ∈ V(P e) ∩ V(G₀) := ⟨by rw [hV]; exact hz, hz₀⟩
    rw [hcap] at hm
    rcases hm with hm | hm
    · exact hzu hm
    · exact hzv hm
  have hmemP : ∀ {a}, a ∈ W.edges → a ∈ E(P e) := fun {a} ha => by rw [hE]; exact ha
  have hall := walk_pure W hs (A := {a | a ∈ W'.edges}) (by
    intro z hz hzu hzv e₁ he₁ e₂ he₂ hi₁ hi₂
    have key : ∀ {e₁ e₂ : β}, e₁ ∈ W.edges → e₂ ∈ W.edges → (P e).Inc e₁ z → (P e).Inc e₂ z →
        e₁ ∈ W'.edges → e₂ ∈ W'.edges := by
      intro e₁ e₂ he₁ he₂ hi₁ hi₂ hin
      by_contra hno
      have hiG : ∀ {a}, (P e).Inc a z → G.Inc a z := fun ⟨w, hw⟩ => ⟨w, hw.mono hle⟩
      have hzW' : z ∈ W'.support := inc_mem_support W' hin (hiG hi₁)
      have hzx : z ≠ x := fun h' => hinner z hz hzu hzv (h' ▸ hx)
      have hzy : z ≠ y := fun h' => hinner z hz hzu hzv (h' ▸ hy)
      obtain ⟨a, ha, b, hb, hab, ia, ib⟩ := exists_two_edges_at_inner W' hs' hzW' hzx hzy
      have hconv : ∀ {c}, c ∈ W'.edges → G.Inc c z → (P e).Inc c z ∧ c ∈ W.edges := by
        intro c hc hi
        have hcP := hE' c hc
        refine ⟨SubData.inc_path hle hcP hi, ?_⟩
        rw [hE] at hcP
        exact hcP
      exact not_three_edges W hs (hconv ha ia).2 (hconv hb ib).2 he₂ (hconv ha ia).1 (hconv hb ib).1
        hi₂ hab (fun h' => hno (h' ▸ ha)) (fun h' => hno (h' ▸ hb))
    exact ⟨key he₁ he₂ hi₁ hi₂, key he₂ he₁ hi₂ hi₁⟩)
  have hx' : x ≠ y := hxy
  obtain ⟨a, ha, -⟩ := exists_edge_at_start W' hx'
  have haW : a ∈ W.edges := by
    have := hE' a ha
    rw [hE] at this
    exact this
  intro b hb
  rw [hE] at hb
  exact (hall a haW b hb).mp ha

end SubData

end GraphMinor.GM14.Whitney

namespace GraphMinor.GM14

open Set Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM14.Whitney

universe u v u' v'

/-- Push forward a simple walk along vertex and edge maps `f : α → α'` and `g : β → β'`. -/
theorem exists_walk_map_het {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {P : Graph α β} {P' : Graph α' β'} {f : α → α'} {g : β → β'}
    (hV : ∀ x ∈ V(P), f x ∈ V(P'))
    (hL : ∀ e x y, P.IsLink e x y → P'.IsLink (g e) (f x) (f y)) :
    ∀ {a b : α} (W : Surface.GraphWalk P a b),
      ∃ W' : Surface.GraphWalk P' (f a) (f b),
        W'.support = W.support.map f ∧ W'.edges = W.edges.map g
  | _, _, .nil ha => ⟨.nil (hV _ ha), rfl, rfl⟩
  | _, _, .cons hl rest => by
    obtain ⟨W', h₁, h₂⟩ := exists_walk_map_het hV hL rest
    refine ⟨.cons (hL _ _ _ hl) W', ?_, ?_⟩
    · simp [Surface.GraphWalk.support, h₁]
    · simp [Surface.GraphWalk.edges, h₂]

/-- Push forward a graph `G₀ : Graph α β` along `f : α → α'` and `g₀ : β → β'` when `g₀` is
injective on `E(G₀)`. -/
def mapGraphOn {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    (f : α → α') (g₀ : β → β') (G₀ : Graph α β) (hg₀ : InjOn g₀ E(G₀)) : Graph α' β' where
  vertexSet := f '' V(G₀)
  edgeSet := g₀ '' E(G₀)
  IsLink e' x' y' := ∃ e x y, G₀.IsLink e x y ∧ g₀ e = e' ∧ f x = x' ∧ f y = y'
  isLink_symm _ _ := ⟨fun _ _ ⟨e, x, y, hl, he, hx, hy⟩ => ⟨e, y, x, hl.symm, he, hy, hx⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro _ _ _ _ _ ⟨e₁, x₁, y₁, hl₁, rfl, rfl, rfl⟩ ⟨e₂, x₂, y₂, hl₂, he, rfl, rfl⟩
    have he12 : e₁ = e₂ := hg₀ hl₁.edge_mem hl₂.edge_mem he.symm
    subst he12
    rcases G₀.eq_or_eq_of_isLink_of_isLink hl₁ hl₂ with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  edge_mem_iff_exists_isLink e' := by
    constructor
    · rintro ⟨e, he, rfl⟩
      obtain ⟨x, y, hl⟩ := G₀.exists_isLink_of_mem_edgeSet he
      exact ⟨f x, f y, e, x, y, hl, rfl, rfl, rfl⟩
    · rintro ⟨_, _, e, x, y, hl, rfl, rfl, rfl⟩
      exact ⟨e, hl.edge_mem, rfl⟩
  left_mem_of_isLink := by
    rintro _ _ _ ⟨e, x, y, hl, rfl, rfl, rfl⟩
    exact ⟨x, hl.left_mem, rfl⟩

/-- `mapGraphOn` preserves `IsSimpleThreeConnectedGraph` when `f` is injective on `V(G₀)` and
`g₀` is injective on `E(G₀)`. -/
theorem isSimpleThreeConnectedGraph_mapGraphOn
    {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {f : α → α'} {g₀ : β → β'} {G₀ : Graph α β}
    (hsimple : IsSimpleThreeConnectedGraph G₀) (hVfin : V(G₀).Finite)
    (hfi₀ : InjOn f V(G₀)) (hg₀ : InjOn g₀ E(G₀)) :
    IsSimpleThreeConnectedGraph (mapGraphOn f g₀ G₀ hg₀) := by
  let G₀' := mapGraphOn f g₀ G₀ hg₀
  obtain ⟨hs, h4, _⟩ := id hsimple
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rintro _ - _ ⟨e, x, y, hxy, rfl, rfl, hyx⟩
    have := hfi₀ hxy.left_mem hxy.right_mem hyx.symm
    subst this
    exact hs.1 e hxy.edge_mem x hxy
  · rintro _ - _ - _ _ ⟨e₁, x, y, hxy, rfl, rfl, rfl⟩ ⟨e₂, x', y', hxy', rfl, hx, hy⟩
    have h₁ := hfi₀ hxy'.left_mem hxy.left_mem hx
    have h₂ := hfi₀ hxy'.right_mem hxy.right_mem hy
    subst h₁ h₂
    exact congrArg g₀ (hs.2 e₁ hxy.edge_mem e₂ hxy'.edge_mem _ _ hxy hxy')
  · change 4 ≤ (f '' V(G₀)).ncard
    rw [hfi₀.ncard_image]
    exact h4
  · rintro G₁ G₂ ⟨hle₁, hle₂, hVU, hEU, hdisj⟩ hcard
    have hmem : ∀ {H : Graph α' β'} {e x y}, H ≤ G₀' → g₀ e ∈ E(H) → G₀.IsLink e x y →
        f x ∈ V(H) ∧ f y ∈ V(H) := by
      intro H e x y hH he hxy
      have hl : H.IsLink (g₀ e) (f x) (f y) :=
        (hH.isLink_iff he).mpr ⟨e, x, y, hxy, rfl, rfl, rfl⟩
      exact ⟨hl.left_mem, hl.right_mem⟩
    have hsep := IsSimpleThreeConnected.sep hsimple
      (Vx := V(G₀) ∩ f ⁻¹' V(G₁)) (Vy := V(G₀) ∩ f ⁻¹' V(G₂))
      (Ex := E(G₀) ∩ g₀ ⁻¹' E(G₁)) (Ey := E(G₀) ∩ g₀ ⁻¹' E(G₂)) ?_ ?_ ?_
      (fun e he x y hxy => ⟨⟨hxy.left_mem, (hmem hle₁ he.2 hxy).1⟩,
        ⟨hxy.right_mem, (hmem hle₁ he.2 hxy).2⟩⟩)
      (fun e he x y hxy => ⟨⟨hxy.left_mem, (hmem hle₂ he.2 hxy).1⟩,
        ⟨hxy.right_mem, (hmem hle₂ he.2 hxy).2⟩⟩) ?_
    · have hup : ∀ {H : Graph α' β'}, H ≤ G₀' → V(G₀) ∩ f ⁻¹' V(H) = V(G₀) → V(H) = V(G₀') := by
        intro H hH heq
        refine Subset.antisymm hH.vertexSet_mono ?_
        rintro _ ⟨x, hx, rfl⟩
        rw [← heq] at hx
        exact hx.2
      rcases hsep with h' | h'
      · exact Or.inl (hup hle₁ h')
      · exact Or.inr (hup hle₂ h')
    · ext x
      constructor
      · rintro (hx | hx) <;> exact hx.1
      · intro hx
        have hfx : f x ∈ V(G₀') := ⟨x, hx, rfl⟩
        rw [← hVU] at hfx
        rcases hfx with h' | h'
        · exact Or.inl ⟨hx, h'⟩
        · exact Or.inr ⟨hx, h'⟩
    · ext e
      constructor
      · rintro (he | he) <;> exact he.1
      · intro he
        have hge : g₀ e ∈ E(G₀') := ⟨e, he, rfl⟩
        rw [← hEU] at hge
        rcases hge with h' | h'
        · exact Or.inl ⟨he, h'⟩
        · exact Or.inr ⟨he, h'⟩
    · rw [Set.disjoint_left]
      rintro e ⟨_, he₁⟩ ⟨_, he₂⟩
      exact Set.disjoint_left.mp hdisj he₁ he₂
    · have hsub : f '' ((V(G₀) ∩ f ⁻¹' V(G₁)) ∩ (V(G₀) ∩ f ⁻¹' V(G₂))) ⊆ V(G₁) ∩ V(G₂) := by
        rintro _ ⟨x, ⟨⟨-, h₁⟩, -, h₂⟩, rfl⟩
        exact ⟨h₁, h₂⟩
      have hfin : (V(G₁) ∩ V(G₂)).Finite :=
        (hVfin.image f).subset fun y hy => hle₁.vertexSet_mono hy.1
      have hle := Set.ncard_le_ncard hsub hfin
      have hsub₀ : (V(G₀) ∩ f ⁻¹' V(G₁)) ∩ (V(G₀) ∩ f ⁻¹' V(G₂)) ⊆ V(G₀) :=
        fun _ hx => hx.1.1
      rw [(hfi₀.mono hsub₀).ncard_image] at hle
      omega

/-- Transport a subdivision using ambient maps agreeing with a graph isomorphism. -/
theorem isSubdivision_of_iso_with_maps
    {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {G : Graph α β} {G' : Graph α' β'}
    (h : IsSubdivisionOfSimpleThreeConnected G) (ι : Iso G G') (f : α → α') (g : β → β')
    (hfv : ∀ x : V(G), f x.1 = (ι.vertexEquiv x).1)
    (hge : ∀ e : E(G), g e.1 = (ι.edgeEquiv e).1) :
    IsSubdivisionOfSimpleThreeConnected G' := by
  classical
  obtain ⟨G₀, P, hd⟩ := exists_subData h
  have hfm : ∀ {x}, x ∈ V(G) → f x ∈ V(G') := fun {x} hx => by
    rw [hfv ⟨x, hx⟩]; exact (ι.vertexEquiv _).2
  have hfi : InjOn f V(G) := by
    intro x hx y hy hxy
    rw [hfv ⟨x, hx⟩, hfv ⟨y, hy⟩] at hxy
    exact congrArg Subtype.val (ι.vertexEquiv.injective (Subtype.ext hxy))
  have hgi : InjOn g E(G) := by
    intro x hx y hy hxy
    rw [hge ⟨x, hx⟩, hge ⟨y, hy⟩] at hxy
    exact congrArg Subtype.val (ι.edgeEquiv.injective (Subtype.ext hxy))
  have hlink : ∀ {e x y}, G.IsLink e x y → G'.IsLink (g e) (f x) (f y) := by
    intro e x y hxy
    have := (ι.isLink_iff ⟨e, hxy.edge_mem⟩ ⟨x, hxy.left_mem⟩ ⟨y, hxy.right_mem⟩).mp hxy
    rw [hge ⟨e, hxy.edge_mem⟩, hfv ⟨x, hxy.left_mem⟩, hfv ⟨y, hxy.right_mem⟩]
    exact this
  have hVim : V(G') = f '' V(G) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx⟩ := ι.vertexEquiv.surjective ⟨y, hy⟩
      exact ⟨x.1, x.2, by rw [hfv x, hx]⟩
    · rintro ⟨x, hx, rfl⟩; exact hfm hx
  have hEim : E(G') = g '' E(G) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx⟩ := ι.edgeEquiv.surjective ⟨y, hy⟩
      exact ⟨x.1, x.2, by rw [hge x, hx]⟩
    · rintro ⟨x, hx, rfl⟩
      rw [hge ⟨x, hx⟩]; exact (ι.edgeEquiv _).2
  have hPV : ∀ e, ∀ {x}, e ∈ E(G₀) → x ∈ V(P e) → x ∈ V(G) := by
    intro e x he hx
    obtain ⟨u, v, -, hp, -⟩ := hd.path e he
    exact hp.le.vertexSet_mono hx
  have hPE : ∀ e, ∀ {x}, e ∈ E(G₀) → x ∈ E(P e) → x ∈ E(G) := by
    intro e x he hx
    obtain ⟨u, v, -, hp, -⟩ := hd.path e he
    exact hp.le.edgeSet_mono hx
  let rep : β → β := fun e =>
    if he : e ∈ E(G₀) then (hd.path e he).choose_spec.choose_spec.2.2.1.some else e
  have hrep_mem : ∀ {e}, e ∈ E(G₀) → rep e ∈ E(P e) := by
    intro e he
    simp only [rep, he, ↓reduceDIte]
    exact (hd.path e he).choose_spec.choose_spec.2.2.1.some_mem
  let g₀ : β → β' := fun e => g (rep e)
  have hg₀ : InjOn g₀ E(G₀) := by
    intro e₁ he₁ e₂ he₂ heq
    by_contra hne
    have hrep_eq : rep e₁ = rep e₂ :=
      hgi (hPE e₁ he₁ (hrep_mem he₁)) (hPE e₂ he₂ (hrep_mem he₂)) heq
    exact Set.disjoint_left.mp (hd.disj e₁ he₁ e₂ he₂ hne).1 (hrep_mem he₁) (hrep_eq ▸ hrep_mem he₂)
  have hV₀ := hd.sub
  have hfi₀ : InjOn f V(G₀) := hfi.mono hV₀
  let G₀' : Graph α' β' := mapGraphOn f g₀ G₀ hg₀
  have hsimple' : IsSimpleThreeConnectedGraph G₀' :=
    isSimpleThreeConnectedGraph_mapGraphOn hd.simple hd.finite_V₀ hfi₀ hg₀
  let P₀ : β → Graph α' β' := fun e => (G'.induce (f '' V(P e))).restrict (g '' E(P e))
  let P' : β' → Graph α' β' := fun e' =>
    if h : ∃ e ∈ E(G₀), g₀ e = e' then P₀ (Classical.choose h) else ⊥
  have hP'eq : ∀ {e}, e ∈ E(G₀) → P' (g₀ e) = P₀ e := by
    intro e he
    have hex : ∃ e₁ ∈ E(G₀), g₀ e₁ = g₀ e := ⟨e, he, rfl⟩
    have heq : Classical.choose hex = e := hg₀ (Classical.choose_spec hex).1 he
      (Classical.choose_spec hex).2
    simp only [P', hex, ↓reduceDIte, heq]
  have hP₀link : ∀ {e a x y}, e ∈ E(G₀) → (P e).IsLink a x y → (P₀ e).IsLink (g a) (f x) (f y) := by
    intro e a x y he hl
    obtain ⟨u, v, -, hp, -⟩ := hd.path e he
    exact ⟨⟨a, hl.edge_mem, rfl⟩, hlink (hl.mono hp.le), ⟨x, hl.left_mem, rfl⟩,
      ⟨y, hl.right_mem, rfl⟩⟩
  have hP₀E : ∀ {e}, e ∈ E(G₀) → E(P₀ e) = g '' E(P e) := by
    intro e he
    change E((G'.induce (f '' V(P e))).restrict (g '' E(P e))) = _
    rw [Graph.edgeSet_restrict, inter_eq_right]
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨x, y, hxy⟩ := (P e).exists_isLink_of_mem_edgeSet ha
    exact (show (G'.induce (f '' V(P e))).IsLink _ _ _ from (hP₀link he hxy).2).edge_mem
  have hP₀V : ∀ e, V(P₀ e) = f '' V(P e) := fun _ => rfl
  have hle' : ∀ {e}, e ∈ E(G₀) → P₀ e ≤ G' := by
    intro e he
    refine Graph.restrict_le.trans (Graph.induce_le ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact hfm (hPV e he hx)
  refine ⟨G₀', hsimple', ?_, P', ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hfm (hV₀ hx)
  · rintro _ ⟨e, he, rfl⟩
    rw [hP'eq he]
    obtain ⟨u, v, hl, ⟨hle, W, hs, hV, hE⟩, hne, hcap⟩ := hd.path e he
    obtain ⟨W', h₁, h₂⟩ := exists_walk_map_het (P := P e) (P' := P₀ e) (f := f) (g := g)
      (fun x hx => ⟨x, hx, rfl⟩) (fun a x y h' => hP₀link he h') W
    refine ⟨f u, f v, ⟨e, u, v, hl, rfl, rfl, rfl⟩, ⟨hle' he, W', ?_, ?_, ?_⟩, ?_, ?_⟩
    · change W'.support.Nodup
      rw [h₁]
      refine (List.nodup_map_iff_inj_on hs).mpr fun x hx y hy hxy => ?_
      exact hfi (hPV e he (hV ▸ hx)) (hPV e he (hV ▸ hy)) hxy
    · rw [hP₀V, hV]; ext y; simp [h₁]
    · rw [hP₀E he, hE]; ext y; simp [h₂]
    · rw [hP₀E he]; exact hne.image g
    · change f '' V(P e) ∩ f '' V(G₀) = _
      have hsubP : V(P e) ⊆ V(G) := fun x hx => hPV e he hx
      rw [← hfi.image_inter hsubP hV₀, hcap, image_pair]
  · rintro _ ⟨e₁, he₁, rfl⟩ _ ⟨e₂, he₂, rfl⟩ hne
    have hne₀ : e₁ ≠ e₂ := fun h0 => hne (congrArg g₀ h0)
    rw [hP'eq he₁, hP'eq he₂]
    have hd₁ := hd.disj e₁ he₁ e₂ he₂ hne₀
    refine ⟨?_, ?_⟩
    · rw [hP₀E he₁, hP₀E he₂, Set.disjoint_left]
      rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
      have := hgi (hPE e₂ he₂ hb) (hPE e₁ he₁ ha) hab
      exact Set.disjoint_left.mp hd₁.1 ha (this ▸ hb)
    · rintro _ ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
      have := hfi (hPV e₂ he₂ hb) (hPV e₁ he₁ ha) hab
      exact ⟨a, hd₁.2 ⟨ha, this ▸ hb⟩, rfl⟩
  · rw [hVim, hd.vunion, image_union, image_iUnion₂]
    change f '' V(G₀) ∪ ⋃ e ∈ E(G₀), f '' V(P e) =
      f '' V(G₀) ∪ ⋃ e' ∈ g₀ '' E(G₀), V(P' e')
    rw [biUnion_image]
    refine congrArg (f '' V(G₀) ∪ ·) (iUnion₂_congr fun e he => ?_)
    rw [hP'eq he, hP₀V]
  · rw [hEim, hd.eunion, image_iUnion₂]
    change (⋃ e ∈ E(G₀), g '' E(P e)) = ⋃ e' ∈ g₀ '' E(G₀), E(P' e')
    rw [biUnion_image]
    refine iUnion₂_congr fun e he => ?_
    rw [hP'eq he, hP₀E he]

/-- Heterogeneous version of `Whitney.isSubdivision_of_iso`: a graph `G' : Graph α' β'`
isomorphic to a subdivision `G : Graph α β` of a simple 3-connected graph is one too. -/
theorem isSubdivision_of_iso_het {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    [Nonempty α'] [Nonempty β'] {G : Graph α β} {G' : Graph α' β'}
    (h : IsSubdivisionOfSimpleThreeConnected G) (ι : Iso G G') :
    IsSubdivisionOfSimpleThreeConnected G' := by
  classical
  let a₀ : α' := Classical.arbitrary α'
  let b₀ : β' := Classical.arbitrary β'
  let f : α → α' := fun x => if hx : x ∈ V(G) then (ι.vertexEquiv ⟨x, hx⟩).1 else a₀
  let g : β → β' := fun e => if he : e ∈ E(G) then (ι.edgeEquiv ⟨e, he⟩).1 else b₀
  have hfv : ∀ x : V(G), f x.1 = (ι.vertexEquiv x).1 := fun x => by simp [f]
  have hge : ∀ e : E(G), g e.1 = (ι.edgeEquiv e).1 := fun e => by simp [g]
  exact isSubdivision_of_iso_with_maps h ι f g hfv hge

end GraphMinor.GM14

namespace GraphMinor.GM14.Whitney

open Set Graph GraphMinor.Surface

universe u v

variable {α : Type u} {β : Type v}

/-! ## 5. Moving a subdivision along an isomorphism -/

/-- A walk moves along a map of links. -/
theorem exists_walk_map {P P' : Graph α β} {f : α → α} {g : β → β}
    (hv : ∀ x ∈ V(P), f x ∈ V(P'))
    (hl : ∀ e x y, P.IsLink e x y → P'.IsLink (g e) (f x) (f y)) {a b : α}
    (W : GraphWalk P a b) :
    ∃ W' : GraphWalk P' (f a) (f b), W'.support = W.support.map f ∧
      W'.edges = W.edges.map g :=
  GraphMinor.GM14.exists_walk_map_het hv hl W

/-- A graph isomorphic to a subdivision of a simple 3-connected graph is one too. -/
theorem isSubdivision_of_iso {G G' : Graph α β} (h : IsSubdivisionOfSimpleThreeConnected G)
    (ι : Iso G G') : IsSubdivisionOfSimpleThreeConnected G' := by
  classical
  let f : α → α := fun x => if hx : x ∈ V(G) then (ι.vertexEquiv ⟨x, hx⟩).1 else x
  let g : β → β := fun e => if he : e ∈ E(G) then (ι.edgeEquiv ⟨e, he⟩).1 else e
  have hfv : ∀ x : V(G), f x.1 = (ι.vertexEquiv x).1 := fun x => by simp [f]
  have hge : ∀ e : E(G), g e.1 = (ι.edgeEquiv e).1 := fun e => by simp [g]
  exact GraphMinor.GM14.isSubdivision_of_iso_with_maps h ι f g hfv hge

end GraphMinor.GM14.Whitney
