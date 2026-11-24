/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Basic
public import LeanPool.GraphMinor.GM11.Defs

/-!
# Moving paths and circuits along a graph isomorphism

`GMap G G' f g` says that the maps `f` on vertices and `g` on edges are an isomorphism from `G` to
`G'`. We use total maps, since the maps in hand (`η.vMap` and the maps of a homeomorphism) are
total.
A subgraph `Q` of `G` goes to `GMap.sub`, and paths and circuits go to paths and circuits.
-/


@[expose] public section

namespace GraphMinor.GM14

open Set Graph GraphMinor GraphMinor.GM09 GraphMinor.Surface

universe u v u' v'

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}

/-- `f` and `g` are an isomorphism from `G` to `G'`. -/
structure GMap (G : Graph α β) (G' : Graph α' β') (f : α → α') (g : β → β') : Prop where
  bijV : BijOn f V(G) V(G')
  bijE : BijOn g E(G) E(G')
  link : ∀ {e x y}, e ∈ E(G) → x ∈ V(G) → y ∈ V(G) →
    (G.IsLink e x y ↔ G'.IsLink (g e) (f x) (f y))

variable {G : Graph α β} {G' : Graph α' β'} {f : α → α'} {g : β → β'}

/-- The inverse of an isomorphism. -/
theorem GMap.symm [Nonempty α] [Nonempty β] (m : GMap G G' f g) :
    GMap G' G (Function.invFunOn f V(G)) (Function.invFunOn g E(G)) := by
  have hV := m.bijV.invOn_invFunOn
  have hE := m.bijE.invOn_invFunOn
  refine ⟨(bijOn_comm hV).mpr m.bijV, (bijOn_comm hE).mpr m.bijE, ?_⟩
  intro e x y he hx hy
  have he' := ((bijOn_comm hE).mpr m.bijE).mapsTo he
  have hx' := ((bijOn_comm hV).mpr m.bijV).mapsTo hx
  have hy' := ((bijOn_comm hV).mpr m.bijV).mapsTo hy
  rw [m.link he' hx' hy', hE.2 he, hV.2 hx, hV.2 hy]

/-- A walk goes to a walk. -/
theorem exists_walk_image (hl : ∀ {e x y}, G.IsLink e x y → G'.IsLink (g e) (f x) (f y))
    (hv : ∀ x ∈ V(G), f x ∈ V(G')) {a b : α} (W : GraphWalk G a b) :
    ∃ W' : GraphWalk G' (f a) (f b), W'.support = W.support.map f ∧ W'.edges = W.edges.map g := by
  induction W with
  | nil h => exact ⟨.nil (hv _ h), rfl, rfl⟩
  | cons hlink _ ih =>
    obtain ⟨W', h₁, h₂⟩ := ih
    exact ⟨.cons (hl hlink) W', by simp [GraphWalk.support, h₁], by simp [GraphWalk.edges, h₂]⟩

/-- The image of a subgraph. -/
def GMap.sub (_ : GMap G G' f g) (Q : Graph α β) : Graph α' β' :=
  (G'.induce (f '' V(Q))).restrict (g '' E(Q))

theorem mem_of_mem_walk {Q : Graph α β} {a b : α} (W : GraphWalk Q a b) {x : α}
    (hx : x ∈ W.support) : x ∈ V(Q) := by
  induction W with
  | nil h =>
    simp only [GraphWalk.support, List.mem_singleton] at hx
    exact hx ▸ h
  | cons hlink _ ih =>
    simp only [GraphWalk.support, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hlink.left_mem
    · exact ih hx

variable (m : GMap G G' f g) {Q : Graph α β}

include m in
theorem GMap.image_V_subset (hQ : Q ≤ G) : f '' V(Q) ⊆ V(G') :=
  (image_mono hQ.vertexSet_mono).trans m.bijV.mapsTo.image_subset

theorem GMap.sub_le (hQ : Q ≤ G) : m.sub Q ≤ G' :=
  restrict_le.trans (induce_le (m.image_V_subset hQ))

theorem GMap.vertexSet_sub : V(m.sub Q) = f '' V(Q) := rfl

theorem GMap.sub_isLink (hQ : Q ≤ G) {e x y} (h : Q.IsLink e x y) :
    (m.sub Q).IsLink (g e) (f x) (f y) := by
  have hG := h.mono hQ
  have hl := (m.link hG.edge_mem hG.left_mem hG.right_mem).mp hG
  exact ⟨mem_image_of_mem g h.edge_mem,
    ⟨hl, mem_image_of_mem f h.left_mem, mem_image_of_mem f h.right_mem⟩⟩

theorem GMap.edgeSet_sub (hQ : Q ≤ G) : E(m.sub Q) = g '' E(Q) := by
  ext a
  constructor
  · intro h
    exact ((edgeSet_restrict _ _).subset h).2
  · rintro ⟨e, he, rfl⟩
    obtain ⟨x, y, hl⟩ := Q.exists_isLink_of_mem_edgeSet he
    exact (m.sub_isLink hQ hl).edge_mem

/-- The walk of the image of `Q`. -/
theorem GMap.exists_walk_sub (hQ : Q ≤ G) {a b : α} (W : GraphWalk Q a b) :
    ∃ W' : GraphWalk (m.sub Q) (f a) (f b), W'.support = W.support.map f ∧
      W'.edges = W.edges.map g :=
  exists_walk_image (m.sub_isLink hQ) (fun _ h => mem_image_of_mem f h) W

/-- A path goes to a path. -/
theorem GMap.path {a b : α} (hP : IsGraphPathWithEnds G Q a b) :
    IsGraphPathWithEnds G' (m.sub Q) (f a) (f b) := by
  obtain ⟨hle, W, hs, hV, hE⟩ := hP
  obtain ⟨W', h₁, h₂⟩ := m.exists_walk_sub hle W
  refine ⟨m.sub_le hle, W', ?_, ?_, ?_⟩
  · change W'.support.Nodup
    rw [h₁]
    refine hs.map_on fun x hx y hy hxy => ?_
    exact m.bijV.injOn (hle.vertexSet_mono (mem_of_mem_walk W hx))
      (hle.vertexSet_mono (mem_of_mem_walk W hy)) hxy
  · rw [m.vertexSet_sub, hV, h₁]
    ext x
    simp
  · rw [m.edgeSet_sub hle, hE, h₂]
    ext x
    simp

/-- A circuit goes to a circuit. -/
theorem GMap.circuit (hC : IsGraphCircuit G Q) : IsGraphCircuit G' (m.sub Q) := by
  obtain ⟨hle, u, W, ⟨hs, hd⟩, hlen, hV, hE⟩ := hC
  obtain ⟨W', h₁, h₂⟩ := m.exists_walk_sub hle W
  have hinjV : ∀ l : List α, (∀ x ∈ l, x ∈ V(Q)) → l.Nodup → (l.map f).Nodup := by
    intro l hl hn
    refine hn.map_on fun x hx y hy hxy => ?_
    exact m.bijV.injOn (hle.vertexSet_mono (hl x hx)) (hle.vertexSet_mono (hl y hy)) hxy
  refine ⟨m.sub_le hle, f u, W', ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [h₁, ← List.map_tail]
    exact hinjV _ (fun x hx => mem_of_mem_walk W (List.mem_of_mem_tail hx)) hs
  · rw [h₂]
    refine hd.map_on fun x hx y hy hxy => ?_
    have hxE : x ∈ E(Q) := hE ▸ hx
    have hyE : y ∈ E(Q) := hE ▸ hy
    exact m.bijE.injOn (hle.edgeSet_mono hxE) (hle.edgeSet_mono hyE) hxy
  · change 0 < W'.edges.length
    rw [h₂, List.length_map]
    exact hlen
  · rw [m.vertexSet_sub, hV, h₁]
    ext x
    simp
  · rw [m.edgeSet_sub hle, hE, h₂]
    ext x
    simp

/-- A path from `X` to `Y` goes to a path from `f(X)` to `f(Y)`. -/
theorem GMap.fromTo {X Y : Set α} (hX : X ⊆ V(G)) (hY : Y ⊆ V(G)) {a b : α}
    (hP : IsFromToPathWithEnds G Q X Y a b) :
    IsFromToPathWithEnds G' (m.sub Q) (f '' X) (f '' Y) (f a) (f b) := by
  obtain ⟨hp, h₁, h₂⟩ := hP
  have hcap : ∀ Z : Set α, Z ⊆ V(G) → f '' V(Q) ∩ f '' Z = f '' (V(Q) ∩ Z) := fun Z hZ =>
    ((m.bijV.injOn.mono (union_subset hp.1.vertexSet_mono hZ)).image_inter subset_union_left
      subset_union_right).symm
  refine ⟨m.path hp, ?_, ?_⟩
  · rw [m.vertexSet_sub, hcap X hX, h₁, image_singleton]
  · rw [m.vertexSet_sub, hcap Y hY, h₂, image_singleton]

end GraphMinor.GM14
