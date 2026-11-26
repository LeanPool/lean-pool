/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section5d

/-!
# Splitting a member of a rooted location

In the proof of (5.4) of Graph Minors XX, each member `C` of a rooted location is cut into pieces. A
grouping feasible in `P | C` should then be feasible in the part of the new heart that has one edge
for each piece.

The file proves this in `feasible_of_split`. Take a realization `H` of `P | C`. Replace the part of
`H` in each piece `L` by the grouping `K_L` on `πBar(L)` that records which roots are connected in
that
part. Two roots of `C` connected in `H` are still connected: follow a path in `H`, and each time it
leaves a piece it does so at a root of that piece, where `K_L` gives a jump.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04 SimpleGraph

universe u v

variable {α : Type u} {β : Type v}

/-- The grouping on `V` in which distinct vertices are adjacent if and only if they are connected
in `H`. -/
def connGrouping (H : (⊤ : SimpleGraph α).Subgraph) (V : Set α) : (⊤ : SimpleGraph α).Subgraph where
  verts := V
  Adj u v := u ∈ V ∧ v ∈ V ∧ u ≠ v ∧ sameComponent H u v
  adj_sub h := h.2.2.1
  edge_vert h := h.1
  symm := ⟨fun _ _ h ↦ ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.symm⟩⟩

theorem isGrouping_connGrouping (H : (⊤ : SimpleGraph α).Subgraph) (V : Set α) :
    IsGrouping V (connGrouping H V) :=
  isGrouping_iff.mpr ⟨subset_rfl, fun _ _ _ hac hab hbc ↦
    ⟨hab.1, hbc.2.1, hac, hab.2.2.2.trans hbc.2.2.2⟩⟩

theorem feasible_connGrouping {Ω : Type*} {P : Patchwork Ω α β} {H : (⊤ : SimpleGraph α).Subgraph}
    (hH : P.IsRealization H) : IsFeasibleGrouping P (connGrouping H P.G.rootSet) := by
  refine ⟨isGrouping_connGrouping _ _, rfl, H, hH, fun x hx y hy hne ↦ ?_⟩
  rw [← sameComponent_iff_connectedIn]
  exact ⟨fun h ↦ ⟨hx, hy, hne, h⟩, fun h ↦ h.2.2.2⟩

theorem sameComponent_emptySubgraph {V : Set α} {p q : α}
    (h : sameComponent (emptySubgraph V) p q) : p = q := by
  obtain ⟨hp, hq, hr⟩ := sameComponent_iff.mp h
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  suffices ∀ y : (emptySubgraph V).verts, Relation.ReflTransGen (emptySubgraph V).coe.Adj ⟨p, hp⟩ y
    →
      p = y.1 from this ⟨q, hq⟩ hr
  intro y hy
  induction hy with
  | refl => rfl
  | @tail b c _ hab _ => exact (not_emptySubgraph_adj (V := V) (u := b.1) (v := c.1) hab).elim

/-- Graph Minors XX, proof of (5.4), last paragraph: the heart of a removable patchwork at a fine
location is removable. -/
theorem heart_isRemovable {P Q : UnlabeledPatchwork α β} {ℒ : Set (RootedHypergraph α β)}
    {e : RootedHypergraph α β → β} (hP : P.IsRemovable) (hfine : IsFine P.G ℒ)
    (h : IsPatchworkHeart P ℒ e Q) : Q.IsRemovable := by
  intro g hg
  rw [h.edgeSet_eq_image hfine] at hg
  obtain ⟨C, hC, rfl⟩ := hg
  have hc := h.isRootedLocation.isComplemented hC
  rw [Patchwork.IsRemovableEdge, h.ends_newEdge hC, h.Δ_newEdge hC]
  have hrem : (P.restrict C).IsRemovable := hP.restrict hc.le
  refine ⟨isGrouping_iff.mpr ⟨subset_rfl, fun a _ _ _ hab _ ↦ ?_⟩, rfl, _,
    hrem.emptySubgraph_isRealization, fun x _ y _ hne ↦ ?_⟩
  · exact (not_emptySubgraph_adj hab).elim
  · rw [← sameComponent_iff_connectedIn]
    exact ⟨fun h' ↦ absurd (sameComponent_emptySubgraph h') hne,
      fun h' ↦ (not_emptySubgraph_adj h').elim⟩

section Split

variable {P Q' : UnlabeledPatchwork α β} {C R : RootedHypergraph α β}
  {𝒮 : Set (RootedHypergraph α β)} {e' : RootedHypergraph α β → β}

/-- A grouping feasible in `P | C` is feasible in the part `R` of the heart that has one edge for
each piece of `C`. -/
theorem feasible_of_split (hRroots : R.roots = C.roots) (hRE : R.edgeSet = e' '' 𝒮)
    (hle : R.toHypergraph ≤ Q'.G.toHypergraph)
    (hΔ : ∀ L ∈ 𝒮, Q'.Δ (e' L) = feasibleGroupings (P.restrict L)) (hinj : InjOn e' 𝒮)
    (hC : C.toHypergraph ≤ P.G.toHypergraph) (hL : ∀ L ∈ 𝒮, L.toHypergraph ≤ C.toHypergraph)
    (hroot : ∀ L ∈ 𝒮, ∀ v, v ∈ L.rootSet ↔ v ∈ C.rootSet ∧ v ∈ L.vertexSet)
    (hsep : ∀ L ∈ 𝒮, ∀ L' ∈ 𝒮, L ≠ L' → ∀ v, v ∈ L.vertexSet → v ∈ L'.vertexSet → v ∈ L.rootSet)
    (hedge : ∀ g ∈ C.edgeSet, ∃ L ∈ 𝒮, g ∈ L.edgeSet) (hVR : R.vertexSet = C.rootSet)
    {K : (⊤ : SimpleGraph α).Subgraph} (hK : IsFeasibleGrouping (P.restrict C) K) :
    IsFeasibleGrouping (Q'.restrict R) K := by
  classical
  obtain ⟨hg, hv, H, ⟨δ, hδ, rfl⟩, hconn₀⟩ := hK
  have hconn : ∀ x ∈ C.rootSet, ∀ y ∈ C.rootSet, x ≠ y →
      (ConnectedIn (realizationOf C.toHypergraph δ) x y ↔ K.Adj x y) := hconn₀
  have hrs : R.rootSet = C.rootSet := by
    change {v | v ∈ R.roots} = {v | v ∈ C.roots}
    rw [hRroots]
  have : Nonempty (RootedHypergraph α β) := ⟨C⟩
  have hLG : ∀ L ∈ 𝒮, L.toHypergraph ≤ P.G.toHypergraph := fun L h ↦ (hL L h).trans hC
  set HL : RootedHypergraph α β → (⊤ : SimpleGraph α).Subgraph :=
    fun L ↦ realizationOf L.toHypergraph δ with hHL
  have hreal : ∀ L ∈ 𝒮, (P.restrict L).IsRealization (HL L) := by
    intro L hLm
    refine ⟨δ, fun g hg' ↦ ?_, rfl⟩
    rw [Patchwork.restrict_Δ (hLG L hLm) hg']
    have hgC : g ∈ C.edgeSet := (hL L hLm).edgeSet_subset hg'
    have := hδ g hgC
    rwa [Patchwork.restrict_Δ hC hgC] at this
  have hHLverts : ∀ L ∈ 𝒮, (HL L).verts = L.vertexSet := fun L h ↦ (hreal L h).verts_eq
  let inv : β → RootedHypergraph α β := Function.invFunOn e' 𝒮
  have hinv : ∀ {L}, L ∈ 𝒮 → inv (e' L) = L := fun hm ↦
    hinj (Function.invFunOn_mem ⟨_, hm, rfl⟩) hm (Function.invFunOn_eq ⟨_, hm, rfl⟩)
  let δ' : β → (⊤ : SimpleGraph α).Subgraph :=
    fun g ↦ connGrouping (HL (inv g)) (inv g).rootSet
  have hδ'' : ∀ {L}, L ∈ 𝒮 → δ' (e' L) = connGrouping (HL L) L.rootSet := fun hm ↦ by
    simp only [δ', hinv hm]
  have hmemE : ∀ {L}, L ∈ 𝒮 → e' L ∈ R.edgeSet := fun {L} hm ↦ by
    rw [hRE]
    exact ⟨L, hm, rfl⟩
  have hreal' : (Q'.restrict R).IsRealization (realizationOf R.toHypergraph δ') := by
    refine ⟨δ', fun g hg' ↦ ?_, rfl⟩
    have hg₂ := hg'
    rw [Patchwork.restrict_G, hRE] at hg₂
    obtain ⟨L, hm, rfl⟩ := hg₂
    rw [Patchwork.restrict_Δ hle hg', hΔ L hm, hδ'' hm]
    exact feasible_connGrouping (hreal L hm)
  set H' := realizationOf R.toHypergraph δ' with hH'
  have hH'verts : H'.verts = C.rootSet := by
    rw [hreal'.verts_eq, Patchwork.restrict_G, hVR]
  -- A jump inside a piece.
  have hjump : ∀ {L}, L ∈ 𝒮 → ∀ {a b}, a ∈ L.rootSet → b ∈ L.rootSet →
      sameComponent (HL L) a b → sameComponent H' a b := by
    intro L hm a b ha hb hab
    by_cases hne : a = b
    · subst hne
      have haC : a ∈ H'.verts := by
        rw [hH'verts]
        exact ((hroot L hm a).mp ha).1
      exact sameComponent_iff.mpr ⟨haC, haC, SimpleGraph.Reachable.refl _⟩
    · refine sameComponent_of_adj ?_
      rw [hH', realizationOf_adj]
      exact ⟨e' L, hmemE hm, by rw [hδ'' hm]; exact ⟨ha, hb, hne, hab⟩⟩
  have hHLadj : ∀ {L}, L ∈ 𝒮 → ∀ {a b}, (HL L).Adj a b →
      (realizationOf C.toHypergraph δ).Adj a b := by
    intro L hm a b hab
    rw [hHL, realizationOf_adj] at hab
    obtain ⟨g, hg', h'⟩ := hab
    exact realizationOf_adj.mpr ⟨g, (hL L hm).edgeSet_subset hg', h'⟩
  have hreal₀ : (P.restrict C).IsRealization (realizationOf C.toHypergraph δ) := ⟨δ, hδ, rfl⟩
  have hHverts : (realizationOf C.toHypergraph δ).verts = C.vertexSet := hreal₀.verts_eq
  have hsub : ∀ {L}, L ∈ 𝒮 → ∀ {a b}, sameComponent (HL L) a b →
      sameComponent (realizationOf C.toHypergraph δ) a b := by
    intro L hm a b hab
    refine sameComponent_of_forall_adj ?_ (fun _ _ h' ↦ sameComponent_of_adj (hHLadj hm h')) hab
    rw [hHLverts L hm, hHverts]
    exact (hL L hm).vertexSet_subset
  refine ⟨?_, ?_, H', hreal', ?_⟩
  · rw [Patchwork.restrict_G, hrs]
    exact hg
  · rw [Patchwork.restrict_G, hrs]
    exact hv
  intro x hx y hy hne
  rw [Patchwork.restrict_G, hrs] at hx hy
  rw [← hconn x hx y hy hne, ← sameComponent_iff_connectedIn, ← sameComponent_iff_connectedIn]
  constructor
  · intro hxy
    refine sameComponent_of_forall_adj ?_ ?_ hxy
    · rw [hH'verts]
      intro v hv'
      rw [hHverts]
      exact C.roots_subset v hv'
    · intro a b hab
      rw [hH', realizationOf_adj, hRE] at hab
      obtain ⟨_, ⟨L, hm, rfl⟩, h'⟩ := hab
      rw [hδ'' hm] at h'
      exact hsub hm h'.2.2.2
  · intro hxy
    obtain ⟨hxV, hyV, hr⟩ := sameComponent_iff.mp hxy
    rw [SimpleGraph.reachable_iff_reflTransGen] at hr
    have hxH' : x ∈ H'.verts := by rw [hH'verts]; exact hx
    suffices hS : ∀ w : (realizationOf C.toHypergraph δ).verts,
        Relation.ReflTransGen (realizationOf C.toHypergraph δ).coe.Adj ⟨x, hxV⟩ w →
        ∃ r, r ∈ C.rootSet ∧ sameComponent H' x r ∧
          (w.1 = r ∨ ∃ L ∈ 𝒮, r ∈ L.vertexSet ∧ sameComponent (HL L) r w.1) by
      obtain ⟨r, hrC, hxr, h'⟩ := hS ⟨y, hyV⟩ hr
      rcases h' with h' | ⟨L, hm, hrL, h'⟩
      · exact (show y = r from h') ▸ hxr
      · have hyL : y ∈ L.vertexSet := by
          rw [← hHLverts L hm]
          exact (sameComponent_iff.mp h').2.1
        exact hxr.trans (hjump hm ((hroot L hm r).mpr ⟨hrC, hrL⟩)
          ((hroot L hm y).mpr ⟨hy, hyL⟩) h')
    intro w hw
    induction hw with
    | refl => exact ⟨x, hx, sameComponent_iff.mpr ⟨hxH', hxH', SimpleGraph.Reachable.refl _⟩,
        Or.inl rfl⟩
    | @tail w w' _ hadj ih =>
      obtain ⟨r, hrC, hxr, h'⟩ := ih
      have hadj' : (realizationOf C.toHypergraph δ).Adj w.1 w'.1 := hadj
      obtain ⟨g, hgC, hg'⟩ := realizationOf_adj.mp hadj'
      obtain ⟨L', hm', hgL'⟩ := hedge g hgC
      have hadjL' : (HL L').Adj w.1 w'.1 := realizationOf_adj.mpr ⟨g, hgL', hg'⟩
      have hwL' : w.1 ∈ L'.vertexSet := by
        rw [← hHLverts L' hm']
        exact (HL L').edge_vert hadjL'
      rcases h' with h' | ⟨L, hm, hrL, h'⟩
      · refine ⟨r, hrC, hxr, Or.inr ⟨L', hm', h' ▸ hwL', ?_⟩⟩
        rw [← h']
        exact sameComponent_of_adj hadjL'
      · by_cases hLL : L = L'
        · subst hLL
          exact ⟨r, hrC, hxr, Or.inr ⟨L, hm, hrL, h'.trans (sameComponent_of_adj hadjL')⟩⟩
        · have hwL : w.1 ∈ L.vertexSet := by
            rw [← hHLverts L hm]
            exact (sameComponent_iff.mp h').2.1
          have hwroot : w.1 ∈ L.rootSet := hsep L hm L' hm' hLL _ hwL hwL'
          refine ⟨w.1, ((hroot L hm _).mp hwroot).1,
            hxr.trans (hjump hm ((hroot L hm r).mpr ⟨hrC, hrL⟩) hwroot h'),
            Or.inr ⟨L', hm', hwL', sameComponent_of_adj hadjL'⟩⟩

end Split

end GraphMinor.GM20
