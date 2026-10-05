/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.StructuralGraphClasses.PathFour
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Fintype.Card

/-!
# The decomposition step for cographs

Deleting a vertex from a connected `P₄`-free graph cannot leave several
components unless that vertex is adjacent to every remaining vertex. This
local statement will be used for the finite disconnection theorem.
-/

@[expose] public section

namespace SimpleGraph

universe u

variable {V : Type*} {G : SimpleGraph V}

/-- Every component after deletion meets the neighborhood of the deleted vertex. -/
theorem Preconnected.exists_neighbor_in_deleted_component (hc : G.Preconnected)
    (v : V) (x : {u : V // u ≠ v}) :
    ∃ y : {u : V // u ≠ v}, (G.induce {u | u ≠ v}).Reachable x y ∧ G.Adj v y := by
  classical
  let H := G.induce {u | u ≠ v}
  let S : Set V := {u | ∃ hu : u ≠ v, H.Reachable x ⟨u, hu⟩}
  obtain ⟨p⟩ := hc x.val v
  have hx : x.val ∈ S := ⟨x.property, Reachable.refl x⟩
  have hv : v ∉ S := by rintro ⟨hne, _⟩; exact hne rfl
  obtain ⟨d, _, hdS, hdOut⟩ := p.exists_boundary_dart S hx hv
  obtain ⟨hdv, hdReach⟩ := hdS
  have hend : d.snd = v := by
    by_contra hn
    apply hdOut
    exact ⟨hn, hdReach.trans (Adj.reachable (show H.Adj ⟨d.fst, hdv⟩ ⟨d.snd, hn⟩
      from d.adj))⟩
  refine ⟨⟨d.fst, hdv⟩, hdReach, ?_⟩
  simpa only [hend] using d.adj.symm

/-- An outside neighbor prevents a change of adjacency to the deleted vertex
along a connected component: such a change would form an induced `P₄`. -/
theorem IsP4Free.adj_of_deleted_reachable (hp : G.IsP4Free) (v : V)
    (x y z : {u : V // u ≠ v})
    (hxy : (G.induce {u | u ≠ v}).Reachable x y)
    (hxz : ¬(G.induce {u | u ≠ v}).Reachable x z)
    (hvx : G.Adj v x) (hvz : G.Adj v z) : G.Adj v y := by
  let H := G.induce {u | u ≠ v}
  have hr := (H.reachable_iff_reflTransGen x y).mp hxy
  induction hr with
  | refl => exact hvx
  | @tail a b hab hadj ih =>
    have hx_a : H.Reachable x a := (H.reachable_iff_reflTransGen x a).mpr hab
    have haz : ¬G.Adj a.val z.val := by
      intro h
      exact hxz (hx_a.trans (Adj.reachable (show H.Adj a z from h)))
    have hbz : ¬G.Adj b.val z.val := by
      intro h
      exact hxz (hx_a.trans hadj.reachable |>.trans
        (Adj.reachable (show H.Adj b z from h)))
    by_contra hvb
    exact hp b.val a.val v z.val hadj.symm (ih hx_a).symm hvz
      (fun h => hvb h.symm) hbz haz

/-- A disconnected vertex deletion in a connected `P₄`-free graph makes the
deleted vertex universal. No finiteness hypothesis is needed. -/
theorem IsP4Free.adj_all_of_not_preconnected_delete (hp : G.IsP4Free)
    (hc : G.Preconnected) (v : V)
    (hd : ¬(G.induce {u | u ≠ v}).Preconnected) : ∀ x, x ≠ v → G.Adj v x := by
  classical
  let H := G.induce {u | u ≠ v}
  have hd' : ¬∀ a b, H.Reachable a b := hd
  obtain ⟨a, ha⟩ := not_forall.mp hd'
  obtain ⟨b, hab⟩ := not_forall.mp ha
  intro x hx
  let x' : {u : V // u ≠ v} := ⟨x, hx⟩
  have hout : ∃ z, ¬H.Reachable x' z := by
    by_cases hxa : H.Reachable x' a
    · exact ⟨b, fun hxb => hab (hxa.symm.trans hxb)⟩
    · exact ⟨a, hxa⟩
  obtain ⟨z, hxz⟩ := hout
  obtain ⟨y, hxy, hvy⟩ := hc.exists_neighbor_in_deleted_component v x'
  obtain ⟨w, hzw, hvw⟩ := hc.exists_neighbor_in_deleted_component v z
  have hyw : ¬H.Reachable y w := by
    intro h
    exact hxz (hxy.trans h |>.trans hzw.symm)
  exact hp.adj_of_deleted_reachable v y x' w hxy.symm hyw hvy hvw

/-- A universal vertex is isolated in the complement, so that complement cannot
be preconnected when there is another vertex. -/
theorem not_preconnected_compl_of_universal [Nontrivial V] (v : V)
    (hv : ∀ x, x ≠ v → G.Adj v x) : ¬Gᶜ.Preconnected := by
  intro hc
  obtain ⟨x, hx⟩ := hc.exists_adj_of_nontrivial v
  exact hx.2 (hv x hx.1.symm)

/-- Complementation commutes with induced restriction. -/
theorem compl_induce_eq_induce_compl (s : Set V) : (G.induce s)ᶜ = Gᶜ.induce s := by
  ext a b
  simp [compl_adj, Subtype.ext_iff]

private theorem not_both_preconnected_of_card_le (n : ℕ) :
    ∀ (W : Type u) [Fintype W] [Nontrivial W] (H : SimpleGraph W),
      Fintype.card W ≤ n → H.IsP4Free → H.Preconnected → ¬Hᶜ.Preconnected := by
  classical
  induction n with
  | zero =>
    intro W _ _ H hcard hp hc hcc
    have : 0 < Fintype.card W := Fintype.card_pos
    omega
  | succ n ih =>
    intro W _ _ H hcard hp hc hcc
    let v : W := Classical.arbitrary W
    let D := {x : W // x ≠ v}
    let K := H.induce {x | x ≠ v}
    have hsmall : Fintype.card D ≤ n := by
      have : Fintype.card D < Fintype.card W :=
        Fintype.card_lt_of_injective_of_notMem (f := fun x : D => x.val) (b := v)
          Subtype.val_injective (by rintro ⟨x, hx⟩; exact x.property hx)
      omega
    have hk : K.Preconnected := by
      by_contra hn
      exact not_preconnected_compl_of_universal v
        (hp.adj_all_of_not_preconnected_delete hc v hn) hcc
    have hkc : Kᶜ.Preconnected := by
      have hdel : (Hᶜ.induce {x | x ≠ v}).Preconnected := by
        by_contra hn
        have hall := hp.compl.adj_all_of_not_preconnected_delete hcc v hn
        have hnot := not_preconnected_compl_of_universal v hall
        exact hnot (by simpa only [compl_compl] using hc)
      rwa [compl_induce_eq_induce_compl]
    by_cases hs : Subsingleton D
    · let _ := hs
      obtain ⟨y, hy⟩ := hc.exists_adj_of_nontrivial v
      have hall : ∀ x, x ≠ v → H.Adj v x := by
        intro x hx
        have he : (⟨y, hy.ne.symm⟩ : D) = ⟨x, hx⟩ := Subsingleton.elim _ _
        have hev : y = x := congrArg Subtype.val he
        simpa only [hev] using hy
      exact not_preconnected_compl_of_universal v hall hcc
    · let _ : Nontrivial D := not_subsingleton_iff_nontrivial.mp hs
      exact ih D K hsmall (hp.induce {x | x ≠ v}) hk hkc

/-- Seinsche's decomposition theorem: a nontrivial finite `P₄`-free graph is
disconnected or has disconnected complement. -/
theorem IsP4Free.not_preconnected_or_compl [Finite V] [Nontrivial V]
    (hp : G.IsP4Free) : ¬G.Preconnected ∨ ¬Gᶜ.Preconnected := by
  classical
  let _ := Fintype.ofFinite V
  by_cases hc : G.Preconnected
  · exact Or.inr (not_both_preconnected_of_card_le (Fintype.card V) V G le_rfl hp hc)
  · exact Or.inl hc

/-- A disconnected graph has a nonempty proper vertex cut with no cross edges. -/
theorem exists_separated_cut_of_not_preconnected (hn : ¬G.Preconnected) :
    ∃ s : Set V, s.Nonempty ∧ sᶜ.Nonempty ∧ ∀ u ∈ s, ∀ v ∉ s, ¬G.Adj u v := by
  classical
  obtain ⟨a, ha⟩ := not_forall.mp hn
  obtain ⟨b, hab⟩ := not_forall.mp ha
  refine ⟨{x | G.Reachable a x}, ⟨a, Reachable.refl a⟩, ⟨b, hab⟩, ?_⟩
  intro u hu v hv hadj
  exact hv (hu.trans hadj.reachable)

end SimpleGraph
