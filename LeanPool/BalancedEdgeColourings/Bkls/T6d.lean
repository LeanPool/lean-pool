/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.T6c
public import LeanPool.BalancedEdgeColourings.Bkls.L3L

/-!
# Theorem 6, part (d): opposite vertices and the pendant edges between hexagons

`Opp x y`: `y` is opposite to `x` on a bad hexagon; the opposite vertex is unique (`opp_unique`,
from the hypothesis that no three vertices of degree three share a key). Hexagon vertices see all
three colours; the edge of colour `2` at a vertex is unique (`two_unique`).

`pendant_colour`: the edges of colour `2` joining two hexagon vertices can be coloured with three
colours so that the edges at opposite vertices get different colours (the conflict graph has
maximum degree two; Lemma 3 with no matched pairs).
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.T6

open Finset SimpleGraph LeanPool.BalancedEdgeColourings.Bkls.Comp

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {c : Sym2 V → Fin 3} {κ : Type*} {key : V → κ}

theorem add_three_add_three (k : ZMod 6) : k + 3 + 3 = k := by
  have : (3 : ZMod 6) + 3 = 0 := by decide
  rw [add_assoc, this, add_zero]

variable (G c key) in
/-- `y` is opposite to `x` on a bad hexagon. -/
def Opp (x y : V) : Prop := ∃ w, BadHex G c key w ∧ ∃ k, w k = x ∧ w (k + 3) = y

omit [DecidableEq V] in
theorem Opp.symm {x y : V} (h : Opp G c key x y) : Opp G c key y x := by
  classical
  obtain ⟨w, hw, k, rfl, rfl⟩ := h
  exact ⟨w, hw, k + 3, rfl, by rw [add_three_add_three]⟩

omit [DecidableEq V] in
theorem Opp.hex {x y : V} (h : Opp G c key x y) : IsHex G c key x := by
  classical
  obtain ⟨w, hw, k, hx, -⟩ := h
  exact ⟨w, hw, k, hx⟩

omit [DecidableEq V] in
theorem Opp.ne {x y : V} (h : Opp G c key x y) : x ≠ y := by
  classical
  obtain ⟨w, hw, k, rfl, rfl⟩ := h
  intro e
  have := hw.1 e
  have h' : ∀ a : ZMod 6, a ≠ a + 3 := by decide
  exact h' k this

omit [DecidableEq V] in
theorem Opp.key_eq {x y : V} (h : Opp G c key x y) : key x = key y := by
  classical
  obtain ⟨w, hw, k, rfl, rfl⟩ := h
  exact (hw.2.2 k).1

omit [DecidableEq V] in
theorem opp_of_hex {w : ZMod 6 → V} (hw : BadHex G c key w) (k : ZMod 6) :
    Opp G c key (w k) (w (k + 3)) := by
  classical
  exact ⟨w, hw, k, rfl, rfl⟩

omit [DecidableEq V] in
theorem exists_two {x : V} (h : (2 : Fin 3) ∈ Sc G c x) : ∃ y, G.Adj x y ∧ c s(x, y) = 2 := by
  classical
  obtain ⟨e, he, hce⟩ := mem_image.1 h
  rw [C4.mem_inc] at he
  obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.1 he.2
  have ha := he.1
  rw [mem_edgeSet] at ha
  exact ⟨y, ha, hce⟩

omit [DecidableEq V] in
theorem two_unique (hc : ProperOn G c) {x y y' : V} (hy : G.Adj x y) (hcy : c s(x, y) = 2)
    (hy' : G.Adj x y') (hcy' : c s(x, y') = 2) : y = y' := by
  classical
  by_contra hne
  exact hc x s(x, y) s(x, y') ((C4.mem_inc G).2 ⟨hy, Sym2.mem_mk_left _ _⟩)
    ((C4.mem_inc G).2 ⟨hy', Sym2.mem_mk_left _ _⟩) (fun e => hne (Sym2.congr_right.1 e))
    (hcy.trans hcy'.symm)

omit [DecidableEq V] in
/-- Two edges of colour `2` at the same vertex coincide. -/
theorem two_edge_unique (hc : ProperOn G c) {x : V} {e e' : Sym2 V} (he : e ∈ G.edgeSet)
    (hxe : x ∈ e) (hce : c e = 2) (he' : e' ∈ G.edgeSet) (hxe' : x ∈ e') (hce' : c e' = 2) :
    e = e' := by
  classical
  by_contra hne
  exact hc x e e' ((C4.mem_inc G).2 ⟨he, hxe⟩) ((C4.mem_inc G).2 ⟨he', hxe'⟩) hne
    (hce.trans hce'.symm)
section Hyp

variable (hc : ProperOn G c)
  (h1 : ∀ u v, key u = key v → u ≠ v → G.degree u = G.degree v → Sc G c u = Sc G c v →
    G.degree u = 3)
  (h2 : ∀ u v w, key u = key v → key v = key w → G.degree u = 3 → G.degree v = 3 →
    G.degree w = 3 → u = v ∨ v = w ∨ u = w)

include hc h1 in
omit [DecidableEq V] in
theorem hex_deg3' {x : V} (hx : IsHex G c key x) : G.degree x = 3 := by
  classical
  obtain ⟨w, hw, k, rfl⟩ := hx
  exact hex_deg3 hc h1 hw k

include hc h1 in
omit [DecidableEq V] in
theorem two_mem_of_hex {x : V} (hx : IsHex G c key x) : (2 : Fin 3) ∈ Sc G c x := by
  classical
  have : Sc G c x = univ := eq_univ_of_card _ (by rw [card_Sc hc, hex_deg3' hc h1 hx]; rfl)
  rw [this]; exact mem_univ _

include hc h1 h2 in
omit [DecidableEq V] in
/-- **The opposite vertex is unique.** -/
theorem opp_unique {x y z : V} (hy : Opp G c key x y) (hz : Opp G c key x z) : y = z := by
  classical
  rcases h2 x y z hy.key_eq (hy.key_eq.symm.trans hz.key_eq) (hex_deg3' hc h1 hy.hex)
    (hex_deg3' hc h1 hy.symm.hex) (hex_deg3' hc h1 hz.symm.hex) with h | h | h
  · exact absurd h hy.ne
  · exact h
  · exact absurd h hz.ne
end Hyp

variable (G c key) in
/-- Edges of colour `2` joining two hexagon vertices. -/
def PH (e : Sym2 V) : Prop := e ∈ G.edgeSet ∧ c e = 2 ∧ ∀ y ∈ e, IsHex G c key y

variable (G c key) in
/-- Conflicts between such edges: they meet opposite vertices. -/
def LP : SimpleGraph (Sym2 V) where
  Adj e e' := e ≠ e' ∧ PH G c key e ∧ PH G c key e' ∧ ∃ x ∈ e, ∃ x' ∈ e', Opp G c key x x'
  symm := ⟨fun _ _ ⟨h, a, b, x, hx, x', hx', o⟩ => ⟨Ne.symm h, b, a, x', hx', x, hx, o.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

omit [DecidableEq V] in
/-- **The pendant edges between hexagons.** -/
theorem pendant_colour (hc : ProperOn G c)
    (h1 : ∀ u v, key u = key v → u ≠ v → G.degree u = G.degree v → Sc G c u = Sc G c v →
      G.degree u = 3)
    (h2 : ∀ u v w, key u = key v → key v = key w → G.degree u = 3 → G.degree v = 3 →
      G.degree w = 3 → u = v ∨ v = w ∨ u = w) :
    ∃ lg : Sym2 V → Fin 3, ∀ e e', (LP G c key).Adj e e' → lg e ≠ lg e' := by
  classical
  have hdeg : ∀ e, (LP G c key).degree e ≤ 2 := by
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
    let f : V → Sym2 V := fun x =>
      if h : ∃ e', PH G c key e' ∧ ∃ x' ∈ e', Opp G c key x x' then h.choose else s(a, b)
    have hf : ∀ x e', PH G c key e' → (∃ x' ∈ e', Opp G c key x x') → e' = f x := by
      intro x e' he' hx
      have hex : ∃ e', PH G c key e' ∧ ∃ x' ∈ e', Opp G c key x x' := ⟨e', he', hx⟩
      change e' = (if h : ∃ e', PH G c key e' ∧ ∃ x' ∈ e', Opp G c key x x' then h.choose
        else s(a, b))
      rw [dite_eq_left hex]
      obtain ⟨he2, x2, hx2, o2⟩ := hex.choose_spec
      obtain ⟨x1, hx1, o1⟩ := hx
      have := opp_unique hc h1 h2 o1 o2
      subst this
      exact two_edge_unique hc he'.1 hx1 he'.2.1 he2.1 hx2 he2.2.1
    rw [← card_neighborFinset_eq_degree]
    calc #((LP G c key).neighborFinset s(a, b)) ≤ #({f a, f b} : Finset (Sym2 V)) := by
          apply card_le_card
          intro e' he'
          rw [mem_neighborFinset] at he'
          obtain ⟨-, -, hpe', x, hx, x', hx', o⟩ := he'
          rcases Sym2.mem_iff.1 hx with rfl | rfl
          · rw [hf x e' hpe' ⟨x', hx', o⟩]; exact mem_insert_self _ _
          · rw [hf x e' hpe' ⟨x', hx', o⟩]; exact mem_insert_of_mem (mem_singleton_self _)
      _ ≤ 2 := card_le_two
  obtain ⟨g, hg, -⟩ := L3L.lemma3L (L := LP G c key) hdeg (fun _ => none)
    (fun e e' h => by simp at h) (fun _ _ _ _ _ _ => Or.inl rfl)
    (fun p _ _ h => by have := h 0; simp at this)
  exact ⟨g, hg⟩
end Bkls.T6

end LeanPool.BalancedEdgeColourings
