/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Overfull.VAL
public import LeanPool.BalancedEdgeColourings.Balanced.Basic

/-!
# A strengthened Vizing theorem

`class_one_of_le_two`: a graph with at most two vertices of maximum degree has a proper edge
colouring with `Δ` colours (Vizing 1965). A minimal class-two subgraph `H` (on the same vertices,
with the same `Δ`) has every edge-deleted subgraph `Δ`-colourable, and Vizing's adjacency lemma
(`Overfull.val`) applied to an edge at a vertex of degree `Δ`, in both directions, gives three
vertices of degree `Δ` in `H`, hence in `G`.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.SV

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull Balanced

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_min {α : Type*} (P : α → Prop) (f : α → ℕ) (h : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, P y → f x ≤ f y := by
  classical
  have hex : ∃ m, ∃ x, P x ∧ f x = m := let ⟨x, hx⟩ := h; ⟨f x, x, hx, rfl⟩
  obtain ⟨x, hx, hfx⟩ := Nat.find_spec hex
  exact ⟨x, hx, fun y hy => hfx ▸ Nat.find_min' hex ⟨y, hy, rfl⟩⟩

omit [DecidableEq V] [Fintype V] in
/-- A colouring of the line graph gives a total partial edge colouring. -/
theorem exists_total_of_colorable {H : SimpleGraph V} {n : ℕ} (h : H.lineGraph.Colorable n) :
    ∃ c : PEC H (Fin n), Total c := by
  classical
  obtain ⟨C⟩ := h
  refine ⟨⟨fun u v => if hh : H.Adj u v then some (C ⟨s(u, v), hh⟩) else none, ?_, ?_, ?_⟩, ?_⟩
  · intro u v
    by_cases hh : H.Adj u v
    · rw [dite_eq_left hh, dite_eq_left hh.symm]
      congr 2
      exact Subtype.ext Sym2.eq_swap
    · rw [dite_eq_right hh, dite_eq_right (fun h => hh h.symm)]
  · intro u v γ h
    by_contra hh
    rw [dite_eq_right hh] at h
    cases h
  · intro u v w γ h1 h2
    by_cases hv : H.Adj u v
    swap
    · rw [dite_eq_right hv] at h1; cases h1
    by_cases hw : H.Adj u w
    swap
    · rw [dite_eq_right hw] at h2; cases h2
    rw [dite_eq_left hv] at h1
    rw [dite_eq_left hw] at h2
    by_contra hvw
    have hadj : H.lineGraph.Adj ⟨s(u, v), hv⟩ ⟨s(u, w), hw⟩ := by
      rw [lineGraph_adj_iff_exists]
      refine ⟨fun e => hvw ?_, u, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
      have := congrArg Subtype.val e
      exact Sym2.congr_right.1 this
    exact C.valid hadj (Option.some_injective _ (h1.trans h2.symm))
  · intro u v huv
    simp only
    rw [dite_eq_left huv]
    exact Option.some_ne_none _

omit [DecidableEq V] in
/-- **Vizing: at most two vertices of maximum degree give class one.** -/
theorem class_one_of_le_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : #(univ.filter fun v => G.degree v = G.maxDegree) ≤ 2) :
    ∃ c : PEC G (Fin G.maxDegree), Total c := by
  classical
  by_contra hno
  set D := G.maxDegree with hD
  -- a minimal subgraph without a total `D`-colouring
  obtain ⟨H, ⟨hHG, hHno⟩, hmin⟩ := exists_min
    (fun H : SimpleGraph V => H ≤ G ∧ ¬ ∃ c : PEC H (Fin D), Total c)
    (fun H => H.edgeSet.ncard) ⟨G, le_rfl, hno⟩
  -- `Δ(H) = D`
  have hdegle : ∀ v, H.degree v ≤ G.degree v := fun v => by
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
    exact card_le_card fun w hw => by
      rw [mem_neighborFinset] at hw ⊢; exact hHG hw
  have hΔle : H.maxDegree ≤ D := by
    apply maxDegree_le_of_forall_degree_le
    intro v; exact (hdegle v).trans (G.degree_le_maxDegree v)
  have hΔ : H.maxDegree = D := by
    by_contra hne
    apply hHno
    exact exists_total (G := H) (C := Fin D) (by rw [Fintype.card_fin]; omega)
  -- `H` is of class two
  have hcl : IsClassTwo H := by
    intro hcol
    obtain ⟨c, hc⟩ := exists_total_of_colorable hcol
    apply hHno
    refine ⟨⟨fun u v => (c.col u v).map (Fin.cast hΔ), fun u v => by rw [c.col_symm],
      fun {u v γ} h => ?_, fun {u v w γ} h1 h2 => ?_⟩, fun u v huv => ?_⟩
    · obtain ⟨δ, hδ, -⟩ := Option.map_eq_some_iff.1 h
      exact c.col_adj hδ
    · obtain ⟨δ, hδ, e⟩ := Option.map_eq_some_iff.1 h1
      obtain ⟨δ', hδ', e'⟩ := Option.map_eq_some_iff.1 h2
      have : δ = δ' := Fin.cast_injective hΔ (e.trans e'.symm)
      subst this
      exact c.col_proper hδ hδ'
    · simp only [ne_eq, Option.map_eq_none_iff]
      exact hc u v huv
  -- a vertex of degree `D` and an edge at it
  have hDpos : 0 < D := by
    by_contra h0
    apply hno
    refine ⟨PEC.empty G (Fin D), fun u v huv => ?_⟩
    have := G.degree_le_maxDegree u
    have : 0 < G.degree u := by
      rw [← card_neighborFinset_eq_degree]; exact card_pos.2 ⟨v, (mem_neighborFinset _ _ _).2 huv⟩
    omega
  have : Nonempty V := by
    by_contra hV
    rw [not_nonempty_iff] at hV
    exact hno ⟨PEC.empty G _, fun u => hV.elim u⟩
  obtain ⟨y, hy⟩ := H.exists_maximal_degree_vertex
  rw [hΔ] at hy
  obtain ⟨x, hx⟩ : ∃ x, H.Adj y x := by
    have : 0 < H.degree y := by omega
    rw [← card_neighborFinset_eq_degree] at this
    obtain ⟨x, hx⟩ := card_pos.1 this
    exact ⟨x, (mem_neighborFinset _ _ _).1 hx⟩
  -- `H - xy` is `D`-colourable
  set H' := H.deleteEdges {s(x, y)}
  have hH'G : H' ≤ G := (deleteEdges_le _).trans hHG
  have hlt : H'.edgeSet.ncard < H.edgeSet.ncard := by
    rw [edgeSet_deleteEdges]
    exact Set.ncard_sdiff_singleton_lt_of_mem (s := H.edgeSet) (a := s(x, y)) hx.symm
  have hH'col : ∃ c : PEC H' (Fin D), Total c := by
    by_contra hn
    exact absurd (hmin H' ⟨hH'G, hn⟩) (by omega)
  obtain ⟨c', hc'⟩ := hH'col
  -- the colouring of `H` with `xy` uncoloured
  let cH : PEC H (Fin H.maxDegree) :=
    ⟨fun u v => (c'.col u v).map (Fin.cast hΔ.symm), fun u v => by rw [c'.col_symm],
      fun {u v γ} h => by
        obtain ⟨δ, hδ, -⟩ := Option.map_eq_some_iff.1 h
        exact (deleteEdges_le _) (c'.col_adj hδ),
      fun {u v w γ} h1 h2 => by
        obtain ⟨δ, hδ, e⟩ := Option.map_eq_some_iff.1 h1
        obtain ⟨δ', hδ', e'⟩ := Option.map_eq_some_iff.1 h2
        have : δ = δ' := Fin.cast_injective hΔ.symm (e.trans e'.symm)
        subst this
        exact c'.col_proper hδ hδ'⟩
  have hcm : ∀ a b, s(a, b) = s(x, y) → H.Adj a b → IsColMinus cH a b := by
    intro a b hab hadj
    refine ⟨hadj, ?_, fun u v huv hne => ?_⟩
    · change (c'.col a b).map _ = none
      rw [Option.map_eq_none_iff]
      by_contra hne
      obtain ⟨δ, hδ⟩ := Option.ne_none_iff_exists'.1 hne
      have := c'.col_adj hδ
      rw [deleteEdges_adj] at this
      exact this.2 (by rw [Set.mem_singleton_iff, hab])
    · change (c'.col u v).map _ ≠ none
      rw [ne_eq, Option.map_eq_none_iff]
      exact hc' u v (deleteEdges_adj.2 ⟨huv, by rw [Set.mem_singleton_iff, ← hab]; exact hne⟩)
  have hv1 := val hcl (hcm x y rfl hx.symm)
  have hv2 := val hcl (hcm y x Sym2.eq_swap hx)
  rw [hΔ] at hv1 hv2
  -- three vertices of degree `D`
  have hthree : 3 ≤ #(univ.filter fun v => H.degree v = D) := by
    obtain ⟨z, hz⟩ := card_pos.1 (show 0 < #((H.neighborFinset x).filter
      fun z => z ≠ y ∧ H.degree z = D) by omega)
    have hz' := mem_filter.1 hz
    have hzx : H.Adj x z := (mem_neighborFinset _ _ _).1 hz'.1
    obtain ⟨hzy, hzD⟩ := hz'.2
    by_cases hxD : H.degree x = D
    · have hsub : ({x, y, z} : Finset V) ⊆ univ.filter fun v => H.degree v = D := by
        intro w hw
        simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · exact mem_filter.2 ⟨mem_univ _, hxD⟩
        · exact mem_filter.2 ⟨mem_univ _, hy.symm⟩
        · exact mem_filter.2 ⟨mem_univ _, hzD⟩
      have := card_le_card hsub
      rw [card_insert_of_notMem, card_pair] at this
      · exact this
      · exact hzy.symm
      · simp only [mem_insert, mem_singleton, not_or]
        exact ⟨hx.ne.symm, hzx.ne⟩
    · have hle := H.degree_le_maxDegree x
      rw [hΔ] at hle
      have h2 : 2 ≤ #((H.neighborFinset y).filter fun z => z ≠ x ∧ H.degree z = D) := by omega
      have hsub : insert y ((H.neighborFinset y).filter fun z => z ≠ x ∧ H.degree z = D) ⊆
          univ.filter fun v => H.degree v = D := by
        intro w hw
        rcases mem_insert.1 hw with rfl | hw
        · exact mem_filter.2 ⟨mem_univ _, hy.symm⟩
        · exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hw).2.2⟩
      have := card_le_card hsub
      rw [card_insert_of_notMem (fun h => by
        have := (mem_neighborFinset _ _ _).1 (mem_filter.1 h).1
        exact H.loopless.irrefl y this)] at this
      omega
  have hsubG : (univ.filter fun v => H.degree v = D) ⊆ univ.filter fun v => G.degree v = D := by
    intro v hv
    have h1 := (mem_filter.1 hv).2
    have h2 := hdegle v
    have h3 := G.degree_le_maxDegree v
    exact mem_filter.2 ⟨mem_univ _, by omega⟩
  have := card_le_card hsubG
  omega
end Bkls.SV

end LeanPool.BalancedEdgeColourings
