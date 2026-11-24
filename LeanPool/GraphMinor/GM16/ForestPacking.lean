/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Card

/-!
# Packing subtrees of a forest

The proof of XVI (5.3), page 56, uses the packing and covering theorem for
subtrees of a forest. We prove it by removing a leaf. If the family contains
the singleton leaf, choose it and cover it by that leaf. Otherwise remove
the leaf from every member. Two members containing the leaf also contain
its only neighbor, so removing it preserves disjointness.
-/

public section
namespace GraphMinor.GM16

open Set SimpleGraph

universe u v

/-- A nonempty connected vertex set, representing a subtree in the forest
argument of Graph Minors XVI, (5.3), page 56. Connectivity is expressed by
paths whose vertices stay in the set. -/
@[expose] def IsSubtreeSet {V : Type u} (G : SimpleGraph V) (A : Set V) : Prop :=
  A.Nonempty ∧ ∀ a ∈ A, ∀ b ∈ A,
    ∃ p : G.Walk a b, p.IsPath ∧ ∀ x ∈ p.support, x ∈ A

/-- A finite nonempty forest has a vertex with at most one neighbor.
An end of a longest path has this property: a further neighbor either
extends the path or contradicts uniqueness of paths in a forest. -/
theorem exists_leaf_of_finite_forest {V : Type u} [Finite V] [Nonempty V]
    {G : SimpleGraph V} (hG : G.IsAcyclic) :
    ∃ x, (G.neighborSet x).Subsingleton := by
  classical
  obtain ⟨a, b, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  refine ⟨a, ?_⟩
  have hneighbor : ∀ x, G.Adj a x → x = p.snd := by
    intro x hx
    by_cases hxp : x ∈ p.support
    · exact hG.eq_snd_of_adj_start hp hx hxp
    · have hlong := hmax x b (p.cons hx.symm) (hp.cons hxp)
      simp only [Walk.length_cons] at hlong
      omega
  intro x hx y hy
  exact (hneighbor x hx).trans (hneighbor y hy).symm

/-- Removing a leaf preserves a nonempty connected set unless that set
is the singleton leaf. Paths between the remaining vertices cannot visit
the deleted leaf. -/
theorem IsSubtreeSet.remove_leaf {V : Type u} {G : SimpleGraph V} {A : Set V}
    (hA : IsSubtreeSet G A) {x : V} (hx : (G.neighborSet x).Subsingleton)
    (hne : A ≠ {x}) :
    IsSubtreeSet (G.induce {x}ᶜ) {a | a.val ∈ A} := by
  classical
  constructor
  · obtain ⟨a, ha⟩ := hA.1
    by_cases hax : a = x
    · subst a
      have hex : ∃ b ∈ A, b ≠ x := by
        by_contra h
        apply hne
        apply Set.Subset.antisymm
        · intro b hb
          by_contra hbx
          exact h ⟨b, hb, fun he => hbx (mem_singleton_iff.mpr he)⟩
        · exact singleton_subset_iff.mpr ha
      obtain ⟨b, hb, hbx⟩ := hex
      exact ⟨⟨b, hbx⟩, hb⟩
    · exact ⟨⟨a, hax⟩, ha⟩
  · intro a ha b hb
    obtain ⟨p, hp, hsupport⟩ := hA.2 a.val ha b.val hb
    have havoid : ∀ z ∈ p.support, z ∈ ({x}ᶜ : Set V) := by
      intro z hz hzx
      have hzx' : z = x := mem_singleton_iff.mp hzx
      subst z
      exact hp.isTrail.notMem_support_of_subsingleton_neighborSet
        (fun h => a.property (mem_singleton_iff.mpr h.symm))
        (fun h => b.property (mem_singleton_iff.mpr h.symm)) hx hz
    refine ⟨p.induce {x}ᶜ havoid, ?_, ?_⟩
    · apply Walk.IsPath.of_map (f := (Embedding.induce {x}ᶜ).toHom)
      simpa using hp
    · intro z hz
      rw [Walk.support_induce] at hz
      obtain ⟨w, hw, hzw⟩ := List.mem_pmap.mp hz
      have hval := congrArg Subtype.val hzw
      change z.val ∈ A
      exact hval ▸ hsupport w hw

/-- A connected set containing a leaf and another vertex contains a
neighbor of the leaf. -/
theorem IsSubtreeSet.exists_neighbor {V : Type u} {G : SimpleGraph V} {A : Set V}
    (hA : IsSubtreeSet G A) {x : V} (hx : x ∈ A) (hne : A ≠ {x}) :
    ∃ y ∈ A, G.Adj x y := by
  classical
  have hex : ∃ b ∈ A, b ≠ x := by
    by_contra h
    apply hne
    apply Set.Subset.antisymm
    · intro b hb
      by_contra hbx
      exact h ⟨b, hb, fun he => hbx (mem_singleton_iff.mpr he)⟩
    · exact singleton_subset_iff.mpr hx
  obtain ⟨b, hb, hbx⟩ := hex
  obtain ⟨p, _, hsupport⟩ := hA.2 x hx b hb
  have hn : ¬p.Nil := Walk.not_nil_of_ne hbx.symm
  exact ⟨p.snd, hsupport _ (p.getVert_mem_support 1), p.adj_snd hn⟩

/-- For two nonsingleton subtrees, deleting a leaf preserves
vertex-disjointness. If they both contain the leaf, they both contain its
unique neighbor. -/
theorem disjoint_of_disjoint_remove_leaf
    {V : Type u} {G : SimpleGraph V} {A B : Set V} {x : V}
    (hA : IsSubtreeSet G A) (hB : IsSubtreeSet G B)
    (hx : (G.neighborSet x).Subsingleton) (hAx : A ≠ {x}) (hBx : B ≠ {x})
    (hd : Disjoint {a : ({x}ᶜ : Set V) | a.val ∈ A}
      {a : ({x}ᶜ : Set V) | a.val ∈ B}) : Disjoint A B := by
  apply Set.disjoint_left.mpr
  intro z hzA hzB
  by_cases hzx : z = x
  · subst z
    obtain ⟨a, ha, hxa⟩ := hA.exists_neighbor hzA hAx
    obtain ⟨b, hb, hxb⟩ := hB.exists_neighbor hzB hBx
    have hab : a = b := hx hxa hxb
    have hbA : b ∈ A := hab ▸ ha
    exact (Set.disjoint_left.mp hd)
      (show (⟨b, by simpa using hxb.ne.symm⟩ : ({x}ᶜ : Set V)).val ∈ A from hbA) hb
  · exact (Set.disjoint_left.mp hd)
      (show (⟨z, by simpa using hzx⟩ : ({x}ᶜ : Set V)).val ∈ A from hzA) hzB

private theorem forest_packing_cover_aux (n : ℕ) :
    ∀ {V : Type u} [Fintype V], Fintype.card V = n →
      ∀ {ι : Type v} (G : SimpleGraph V) (A : ι → Set V),
        G.IsAcyclic → (∀ i, IsSubtreeSet G (A i)) →
        ∃ (I : Finset ι) (X : Finset V), X.card = I.card ∧
          (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (A i) (A j)) ∧
          ∀ i, ∃ x ∈ X, x ∈ A i := by
  classical
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro V _ hn ι G A hG hA
    by_cases hnon : Nonempty V
    · let := hnon
      obtain ⟨x, hx⟩ := exists_leaf_of_finite_forest hG
      let W := ({x}ᶜ : Set V)
      let : Fintype W := Fintype.ofFinite W
      have hcard : Fintype.card W < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (x := x) (by simp [W])
      let eV : W ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
      have hnotX : ∀ X : Finset W, x ∉ X.map eV := by
        intro X hmem
        obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hmem
        exact y.property (mem_singleton_iff.mpr hy)
      by_cases hsing : ∃ i, A i = {x}
      · obtain ⟨i₀, hi₀⟩ := hsing
        let J := {i : ι // x ∉ A i}
        let eI : J ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
        have hJ : ∀ j : J, A j.val ≠ {x} := by
          intro j h
          exact j.property (h ▸ mem_singleton x)
        obtain ⟨I, X, hsize, hdisj, hcover⟩ :=
          ih (Fintype.card W) hcard rfl (G.induce W)
            (fun j : J => {w | w.val ∈ A j.val})
            (hG.induce W) (fun j => (hA j.val).remove_leaf hx (hJ j))
        have hnotI : i₀ ∉ I.map eI := by
          intro hmem
          obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hmem
          have hj₀ : j.val = i₀ := hj
          exact j.property (hj₀.symm ▸ (hi₀ ▸ mem_singleton x))
        refine ⟨insert i₀ (I.map eI), insert x (X.map eV), ?_, ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem (hnotX X),
            Finset.card_insert_of_notMem hnotI, Finset.card_map, Finset.card_map, hsize]
        · intro i hi j hj hij
          rcases Finset.mem_insert.mp hi with rfl | hi
          · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp
              ((Finset.mem_insert.mp hj).resolve_left (Ne.symm hij))
            rw [hi₀, disjoint_singleton_left]
            exact j.property
          · obtain ⟨i, hiI, rfl⟩ := Finset.mem_map.mp hi
            rcases Finset.mem_insert.mp hj with rfl | hj
            · rw [hi₀, disjoint_singleton_right]
              exact i.property
            · obtain ⟨j, hjI, rfl⟩ := Finset.mem_map.mp hj
              apply disjoint_of_disjoint_remove_leaf (hA i.val) (hA j.val) hx (hJ i) (hJ j)
              exact hdisj i hiI j hjI (fun h => hij (congrArg Subtype.val h))
        · intro i
          by_cases hxi : x ∈ A i
          · exact ⟨x, Finset.mem_insert_self _ _, hxi⟩
          · obtain ⟨w, hw, hwA⟩ := hcover ⟨i, hxi⟩
            exact ⟨w.val, Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨w, hw, rfl⟩), hwA⟩
      · have hne : ∀ i, A i ≠ {x} := by
          intro i hi
          exact hsing ⟨i, hi⟩
        obtain ⟨I, X, hsize, hdisj, hcover⟩ :=
          ih (Fintype.card W) hcard rfl (G.induce W)
            (fun i : ι => {w | w.val ∈ A i})
            (hG.induce W) (fun i => (hA i).remove_leaf hx (hne i))
        refine ⟨I, X.map eV, ?_, ?_, ?_⟩
        · rw [Finset.card_map, hsize]
        · intro i hi j hj hij
          exact disjoint_of_disjoint_remove_leaf (hA i) (hA j) hx (hne i) (hne j)
            (hdisj i hi j hj hij)
        · intro i
          obtain ⟨w, hw, hwA⟩ := hcover i
          exact ⟨w.val, Finset.mem_map.mpr ⟨w, hw, rfl⟩, hwA⟩
    · refine ⟨∅, ∅, rfl, ?_, ?_⟩
      · intro i hi
        exact False.elim (Finset.notMem_empty i hi)
      · intro i
        obtain ⟨x, _⟩ := (hA i).1
        exact False.elim (hnon ⟨x⟩)

/-- The elementary subtree packing theorem used in Graph Minors XVI,
proof of (5.3), page 56. A family of nonempty subtrees of a finite forest
has a disjoint subfamily and a vertex cover of the same size. -/
theorem forest_packing_cover {V : Type u} [Finite V] {ι : Type v}
    (G : SimpleGraph V) (A : ι → Set V)
    (hG : G.IsAcyclic) (hA : ∀ i, IsSubtreeSet G (A i)) :
    ∃ (I : Finset ι) (X : Finset V), X.card = I.card ∧
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (A i) (A j)) ∧
      ∀ i, ∃ x ∈ X, x ∈ A i := by
  classical
  let := Fintype.ofFinite V
  exact forest_packing_cover_aux (Fintype.card V) rfl G A hG hA

end GraphMinor.GM16
