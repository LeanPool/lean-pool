/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.T6f
public import LeanPool.BalancedEdgeColourings.Bkls.Hexagon

/-!
# Theorem 6, part (g): recolouring one bad hexagon (Lemma 5)

`hex_step`: given a colouring in which the pendant edges at opposite vertices of a bad hexagon `w`
(not joined to each other) have different colours, recolour the six hexagon edges and the
diagonals (edges between opposite vertices) by Lemma 5: the result is proper at the hexagon
vertices, separates opposite vertices, and changes no other edge.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.T6

open Finset SimpleGraph _root_.LeanPool.BalancedEdgeColourings.Bkls.Comp

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {c : Sym2 V → Fin 3} {κ : Type*} {key : V → κ}

/-- The colouring with the hexagon `w` recoloured by `h` (hexagon edges) and `q` (diagonals). -/
noncomputable def hexUpd (w : ZMod 6 → V) (D : Finset (ZMod 6)) (h q : ZMod 6 → Fin 4)
    (col : Sym2 V → Fin 4) (e : Sym2 V) : Fin 4 := by
  classical
  exact if h1 : ∃ k, e = s(w k, w (k + 1)) then h h1.choose
    else if h2 : ∃ i ∈ D, e = s(w i, w (i + 3)) then q h2.choose else col e

theorem zmod6_aux1 : ∀ k k' : ZMod 6, k = k' + 1 → k + 1 = k' → False := by decide
theorem zmod6_aux2 : ∀ i k : ZMod 6, i = k → i + 3 = k + 1 → False := by decide
theorem zmod6_aux3 : ∀ i k : ZMod 6, i = k + 1 → i + 3 = k → False := by decide

omit [DecidableEq V] in
/-- **One hexagon.** -/
theorem hex_step (hc : ProperOn G c)
    (h1 : ∀ u v, key u = key v → u ≠ v → G.degree u = G.degree v → Sc G c u = Sc G c v →
      G.degree u = 3)
    {w : ZMod 6 → V} (hw : BadHex G c key w) (col : Sym2 V → Fin 4)
    (hpend : ∀ i, ¬ G.Adj (w i) (w (i + 3)) → ∀ y y', G.Adj (w i) y → c s(w i, y) = 2 →
      G.Adj (w (i + 3)) y' → c s(w (i + 3), y') = 2 → col s(w i, y) ≠ col s(w (i + 3), y')) :
    ∃ col' : Sym2 V → Fin 4,
      (∀ e, (∀ k, e ≠ s(w k, w (k + 1))) → (∀ i, G.Adj (w i) (w (i + 3)) →
        e ≠ s(w i, w (i + 3))) → col' e = col e) ∧
      ∀ i, (∀ e e', e ∈ G.incidenceFinset (w i) → e' ∈ G.incidenceFinset (w i) → e ≠ e' →
        col' e ≠ col' e') ∧ Sc G col' (w i) ≠ Sc G col' (w (i + 3)) := by
  classical
  have hpy : ∀ i, ∃ y, G.Adj (w i) y ∧ c s(w i, y) = 2 := fun i =>
    exists_two (two_mem_of_hex hc h1 ⟨w, hw, i, rfl⟩)
  choose py hpy using hpy
  obtain ⟨D, hDdef⟩ : ∃ D : Finset (ZMod 6), ∀ i, i ∈ D ↔ G.Adj (w i) (w (i + 3)) :=
    ⟨univ.filter (fun i => G.Adj (w i) (w (i + 3))), fun i => by simp⟩
  have hD : ∀ i, i ∈ D ↔ i + 3 ∈ D := by
    intro i
    rw [hDdef, hDdef, add_three_add_three]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  obtain ⟨h, q, hq1, hq2, hpr, hS⟩ := Hex.hexagon D hD (fun i => col s(w i, py i))
    (fun i hi => hpend i (fun h => hi ((hDdef i).2 h)) _ _ (hpy i).1 (hpy i).2 (hpy (i + 3)).1
      (hpy (i + 3)).2)
  set col' := hexUpd w D h q col with hcol'
  have hE1 : ∀ k, col' s(w k, w (k + 1)) = h k := by
    intro k
    have hex : ∃ k', s(w k, w (k + 1)) = s(w k', w (k' + 1)) := ⟨k, rfl⟩
    rw [hcol', hexUpd, dite_eq_left hex]
    congr 1
    rcases Sym2.eq_iff.1 hex.choose_spec with ⟨a, -⟩ | ⟨a, b⟩
    · exact (hw.1 a).symm
    · exact (zmod6_aux1 _ _ (hw.1 a) (hw.1 b)).elim
  have hE2 : ∀ i ∈ D, col' s(w i, w (i + 3)) = q i := by
    intro i hi
    have hn : ¬ ∃ k, s(w i, w (i + 3)) = s(w k, w (k + 1)) := by
      rintro ⟨k, e⟩
      rcases Sym2.eq_iff.1 e with ⟨a, b⟩ | ⟨a, b⟩
      · exact zmod6_aux2 _ _ (hw.1 a) (hw.1 b)
      · exact zmod6_aux3 _ _ (hw.1 a) (hw.1 b)
    have hex : ∃ j ∈ D, s(w i, w (i + 3)) = s(w j, w (j + 3)) := ⟨i, hi, rfl⟩
    have key' : ∀ j, j ∈ D → s(w i, w (i + 3)) = s(w j, w (j + 3)) → q j = q i := by
      intro j hj e
      rcases Sym2.eq_iff.1 e with ⟨a, -⟩ | ⟨a, -⟩
      · rw [hw.1 a]
      · have a' := hw.1 a
        subst a'
        exact hq2 j hj
    rw [hcol', hexUpd, dite_eq_right hn, dite_eq_left hex]
    exact key' _ hex.choose_spec.1 hex.choose_spec.2
  have hE3 : ∀ i, i ∉ D → col' s(w i, py i) = q i := by
    intro i hi
    have hn1 : ¬ ∃ k, s(w i, py i) = s(w k, w (k + 1)) := by
      rintro ⟨k, e⟩
      have := (hw.2.1 k).2
      rw [← e] at this
      exact this (hpy i).2
    have hn2 : ¬ ∃ j ∈ D, s(w i, py i) = s(w j, w (j + 3)) := by
      rintro ⟨j, hj, e⟩
      rcases Sym2.eq_iff.1 e with ⟨a, -⟩ | ⟨a, -⟩
      · exact hi (hw.1 a ▸ hj)
      · exact hi (hw.1 a ▸ (hD j).1 hj)
    rw [hcol', hexUpd, dite_eq_right hn1, dite_eq_right hn2]
    exact (hq1 i hi).symm
  -- the three edges at a hexagon vertex
  have hclass : ∀ i e, e ∈ G.incidenceFinset (w i) →
      e = s(w i, w (i + 1)) ∨ e = s(w (i - 1), w i) ∨ e = s(w i, py i) := by
    intro i e he
    rw [C4.mem_inc] at he
    obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.1 he.2
    have hz : G.Adj (w i) z := by have := he.1; rwa [mem_edgeSet] at this
    by_cases hcz : c s(w i, z) = 2
    · right; right; rw [two_unique hc hz hcz (hpy i).1 (hpy i).2]
    · rcases hex_nbr hc hw i (show (G01 G c).Adj (w i) z from ⟨hz, hcz⟩) with rfl | rfl
      · right; left; exact Sym2.eq_swap
      · left; rfl
  have memA : ∀ i, s(w i, w (i + 1)) ∈ G.incidenceFinset (w i) := fun i =>
    (C4.mem_inc G).2 ⟨(hw.2.1 i).1, Sym2.mem_mk_left _ _⟩
  have memB : ∀ i, s(w (i - 1), w i) ∈ G.incidenceFinset (w i) := by
    intro i
    have := (hw.2.1 (i - 1)).1
    rw [sub_add_cancel] at this
    exact (C4.mem_inc G).2 ⟨this, Sym2.mem_mk_right _ _⟩
  have memC : ∀ i, s(w i, py i) ∈ G.incidenceFinset (w i) := fun i =>
    (C4.mem_inc G).2 ⟨(hpy i).1, Sym2.mem_mk_left _ _⟩
  have hcolB : ∀ i, col' s(w (i - 1), w i) = h (i - 1) := by
    intro i
    have := hE1 (i - 1)
    rwa [sub_add_cancel] at this
  have hcolC : ∀ i, col' s(w i, py i) = q i := by
    intro i
    by_cases hi : i ∈ D
    · have hadj : G.Adj (w i) (w (i + 3)) := (hDdef i).1 hi
      have hc2 : c s(w i, w (i + 3)) = 2 := by
        by_contra hne
        rcases hex_nbr hc hw i (show (G01 G c).Adj (w i) (w (i + 3)) from ⟨hadj, hne⟩) with h' | h'
        · exact (by decide : ∀ a : ZMod 6, a + 3 ≠ a - 1) i (hw.1 h')
        · exact (by decide : ∀ a : ZMod 6, a + 3 ≠ a + 1) i (hw.1 h')
      rw [← two_unique hc hadj hc2 (hpy i).1 (hpy i).2]
      exact hE2 i hi
    · exact hE3 i hi
  have hSc : ∀ i, Sc G col' (w i) = Hex.S h q i := by
    intro i
    ext y
    simp only [Sc, mem_image, Hex.S, mem_insert, mem_singleton]
    constructor
    · rintro ⟨e, he, rfl⟩
      rcases hclass i e he with rfl | rfl | rfl
      · right; left; exact hE1 i
      · left; exact hcolB i
      · right; right; exact hcolC i
    · rintro (rfl | rfl | rfl)
      · exact ⟨_, memB i, hcolB i⟩
      · exact ⟨_, memA i, hE1 i⟩
      · exact ⟨_, memC i, hcolC i⟩
  refine ⟨col', fun e hA hB => ?_, fun i => ⟨fun e e' he he' hne => ?_, ?_⟩⟩
  · rw [hcol', hexUpd, dite_eq_right (fun ⟨k, hk⟩ => hA k hk),
      dite_eq_right (fun ⟨i, hi, hk⟩ => hB i ((hDdef i).1 hi) hk)]
  · obtain ⟨a1, a2, a3⟩ := hpr i
    rcases hclass i e he with rfl | rfl | rfl <;> rcases hclass i e' he' with rfl | rfl | rfl
    · exact absurd rfl hne
    · rw [hE1, hcolB]; exact a1.symm
    · rw [hE1, hcolC]; exact a3
    · rw [hE1, hcolB]; exact a1
    · exact absurd rfl hne
    · rw [hcolB, hcolC]; exact a2
    · rw [hE1, hcolC]; exact a3.symm
    · rw [hcolB, hcolC]; exact a2.symm
    · exact absurd rfl hne
  · rw [hSc, hSc]; exact hS i
end Bkls.T6

end LeanPool.BalancedEdgeColourings
