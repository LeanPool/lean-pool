/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.TightPieces
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Abel

/-! Triangle decompositions of saturated tripartite pieces. -/

@[expose] public section

open Finset

namespace GapExtremal.R434

section

variable {V : Type} [DecidableEq V]

/-- A candidate triangle represented by an ordered triple of vertices. -/
abbrev OrderedTriangle (V : Type) := V × V × V

/-- The unordered pairs of vertices belonging to an ordered triangle. -/
def triangleEdges (t : OrderedTriangle V) : Finset (Sym2 V) :=
  {s(t.1,t.2.1), s(t.2.1,t.2.2), s(t.1,t.2.2)}

theorem triangleEdges_card_le (t : OrderedTriangle V) : (triangleEdges t).card ≤ 3 := by
  unfold triangleEdges
  have h₁ := card_insert_le (s := ({s(t.2.1,t.2.2), s(t.1,t.2.2)} : Finset (Sym2 V)))
    (a := s(t.1,t.2.1))
  have h₂ := card_insert_le (s := ({s(t.1,t.2.2)} : Finset (Sym2 V))) (a := s(t.2.1,t.2.2))
  simp only [card_singleton] at h₂
  omega

variable [Fintype V] (B : SimpleGraph V) [DecidableRel B.Adj]

theorem triangulate_uniform_piece (c : V → Fin 3)
    (hc : ∀ ⦃u v⦄, B.Adj u v → c u ≠ c v) (Q : Finset V) (k : ℕ) [NeZero k]
    (hparts : ∀ i, (partOf c Q i).card = k)
    (hcomplete : ∀ ⦃x y⦄, x ∈ Q → y ∈ Q → c x ≠ c y → B.Adj x y) :
    ∃ T : Finset (OrderedTriangle V),
      (∀ t ∈ T, c t.1 = 0 ∧ c t.2.1 = 1 ∧ c t.2.2 = 2) ∧
      (T : Set (OrderedTriangle V)).PairwiseDisjoint triangleEdges ∧
      T.biUnion triangleEdges = (inducedOn B Q).edgeFinset := by
  classical
  let p (i : Fin 3) : ZMod k ≃ partOf c Q i :=
    (ZMod.finEquiv k).toEquiv.symm.trans (Finset.equivFinOfCardEq (hparts i)).symm
  let u (i : Fin 3) (x : ZMod k) : V := (p i x).val
  have hQ (i : Fin 3) (x : ZMod k) : u i x ∈ Q :=
    (mem_filter.mp (p i x).prop).1
  have hC (i : Fin 3) (x : ZMod k) : c (u i x) = i :=
    (mem_filter.mp (p i x).prop).2
  have hinj (i : Fin 3) : Function.Injective (u i) :=
    fun _ _ h => (p i).injective (Subtype.ext h)
  have hex (i : Fin 3) {v : V} (hv : v ∈ Q) (hc : c v = i) : ∃ x, u i x = v := by
    obtain ⟨x, hx⟩ := (p i).surjective ⟨v, mem_filter.mpr ⟨hv, hc⟩⟩
    exact ⟨x, congrArg Subtype.val hx⟩
  let tri (a : ZMod k × ZMod k) : OrderedTriangle V :=
    (u 0 a.1, u 1 a.2, u 2 (a.1 + a.2))
  let tp (a : ZMod k × ZMod k) : Finset (V × V) :=
    {(u 0 a.1, u 1 a.2), (u 1 a.2, u 2 (a.1 + a.2)), (u 0 a.1, u 2 (a.1 + a.2))}
  have htp {a : ZMod k × ZMod k} {x : V × V} (hx : x ∈ tp a) : x ∈ crossPairs c Q := by
    simp only [tp, mem_insert, mem_singleton] at hx
    apply crossPairs_iff.mpr
    rcases hx with rfl | rfl | rfl <;> exact ⟨hQ _ _, hQ _ _, by
      simp only [hC]
      decide⟩
  let f (x : V × V) : Sym2 V := s(x.1,x.2)
  have he (a : ZMod k × ZMod k) : triangleEdges (tri a) = (tp a).image f := by
    simp [triangleEdges, tri, tp, f]
  have huniq {a b : ZMod k × ZMod k} {x : V × V} (hx : x ∈ tp a) (hy : x ∈ tp b) :
      a = b := by
    simp only [tp, mem_insert, mem_singleton] at hx hy
    have himp (i j : Fin 3) (t s : ZMod k) (h : u i t = u j s) : i = j := by
      simpa only [hC] using congrArg c h
    rcases hx with rfl | rfl | rfl <;> rcases hy with hy | hy | hy
    · exact Prod.ext (hinj 0 (congrArg Prod.fst hy)) (hinj 1 (congrArg Prod.snd hy))
    · exact ((by decide : (0 : Fin 3) ≠ 1) (himp 0 1 _ _ (congrArg Prod.fst hy))).elim
    · exact ((by decide : (1 : Fin 3) ≠ 2) (himp 1 2 _ _ (congrArg Prod.snd hy))).elim
    · exact ((by decide : (1 : Fin 3) ≠ 0) (himp 1 0 _ _ (congrArg Prod.fst hy))).elim
    · have hb := hinj 1 (congrArg Prod.fst hy)
      have hab := hinj 2 (congrArg Prod.snd hy)
      rw [hb] at hab
      exact Prod.ext (add_right_cancel hab) hb
    · exact ((by decide : (1 : Fin 3) ≠ 0) (himp 1 0 _ _ (congrArg Prod.fst hy))).elim
    · exact ((by decide : (2 : Fin 3) ≠ 1) (himp 2 1 _ _ (congrArg Prod.snd hy))).elim
    · exact ((by decide : (0 : Fin 3) ≠ 1) (himp 0 1 _ _ (congrArg Prod.fst hy))).elim
    · have ha := hinj 0 (congrArg Prod.fst hy)
      have hab := hinj 2 (congrArg Prod.snd hy)
      rw [ha] at hab
      exact Prod.ext ha (add_left_cancel hab)
  have hdisj : (((univ : Finset (ZMod k × ZMod k)).image tri : Set (OrderedTriangle V))
      ).PairwiseDisjoint triangleEdges := by
    intro t ht t' ht' hn
    obtain ⟨a, _, rfl⟩ := mem_image.mp ht
    obtain ⟨b, _, rfl⟩ := mem_image.mp ht'
    change Disjoint (triangleEdges (tri a)) (triangleEdges (tri b))
    rw [he, he, Finset.disjoint_left]
    intro e ha hb
    obtain ⟨x, hx, hx'⟩ := mem_image.mp ha
    obtain ⟨y, hy, hy'⟩ := mem_image.mp hb
    have hxy : x = y := crossPairs_injOn c Q (htp hx) (htp hy) (hx'.trans hy'.symm)
    subst y
    exact hn (congrArg tri (huniq hx hy))
  have htri : ((univ : Finset (ZMod k × ZMod k)).image tri).biUnion triangleEdges =
      (crossPairs c Q).image f := by
    ext e
    constructor
    · intro he'
      obtain ⟨t, ht, het⟩ := mem_biUnion.mp he'
      obtain ⟨a, _, rfl⟩ := mem_image.mp ht
      rw [he] at het
      obtain ⟨x, hx, rfl⟩ := mem_image.mp het
      exact mem_image.mpr ⟨x, htp hx, rfl⟩
    · intro he'
      obtain ⟨⟨x,y⟩, hx, rfl⟩ := mem_image.mp he'
      obtain ⟨hxQ, hyQ, hlt⟩ := crossPairs_iff.mp hx
      have hc' : (c x = 0 ∧ c y = 1) ∨ (c x = 0 ∧ c y = 2) ∨ (c x = 1 ∧ c y = 2) := by
        have split_lt (i j : Fin 3) : i < j →
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by
          decide +revert +kernel
        exact split_lt _ _ hlt
      have inc (a : ZMod k × ZMod k) (ha : (x,y) ∈ tp a) :
          f (x,y) ∈ ((univ : Finset (ZMod k × ZMod k)).image tri).biUnion triangleEdges :=
        mem_biUnion.mpr ⟨tri a, mem_image.mpr ⟨a, mem_univ _, rfl⟩,
          (he a).symm ▸ mem_image.mpr ⟨(x,y), ha, rfl⟩⟩
      rcases hc' with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · obtain ⟨a, ha⟩ := hex 0 hxQ h₁
        obtain ⟨b, hb⟩ := hex 1 hyQ h₂
        exact inc (a,b) (by simp [tp, ha, hb])
      · obtain ⟨a, ha⟩ := hex 0 hxQ h₁
        obtain ⟨b, hb⟩ := hex 2 hyQ h₂
        exact inc (a,b-a) (by simp [tp, ha, show a + (b-a) = b by abel, hb])
      · obtain ⟨a, ha⟩ := hex 1 hxQ h₁
        obtain ⟨b, hb⟩ := hex 2 hyQ h₂
        exact inc (b-a,a) (by simp [tp, ha, show (b-a) + a = b by abel, hb])
  have hsat : (crossPairs c Q).image f ⊆ (inducedOn B Q).edgeFinset := by
    intro e he'
    obtain ⟨⟨x,y⟩, hx, rfl⟩ := mem_image.mp he'
    obtain ⟨hxQ, hyQ, hlt⟩ := crossPairs_iff.mp hx
    exact SimpleGraph.mem_edgeFinset.mpr ⟨hcomplete hxQ hyQ (ne_of_lt hlt), hxQ, hyQ⟩
  refine ⟨univ.image tri, ?_, hdisj, ?_⟩
  · intro t ht
    obtain ⟨a, _, rfl⟩ := mem_image.mp ht
    exact ⟨hC _ _, hC _ _, hC _ _⟩
  · rw [htri]
    exact Subset.antisymm hsat (induced_edges_subset_crossPairs B c hc Q)

end

end GapExtremal.R434
