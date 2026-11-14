/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.T6a

/-!
# Theorem 6, part (b): Corollary 4 outside the bad hexagons

Hexagon vertices have degree three (`hex_deg3`), and the `G01`-neighbours of a vertex off the
hexagons are off the hexagons (`nonhex_nbr`). On `G2` (the edges of colours `0, 1` off the
hexagons) the relation `Rel` (same key, degree and `2`-status) is a matching (`rel_unique`), and
Corollary 4 recolours `G2` with three colours separating `Rel`-pairs (`step_cor4`).
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.T6

open Finset SimpleGraph LeanPool.BalancedEdgeColourings.Bkls.Comp

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {c : Sym2 V → Fin 3} {κ : Type*} {key : V → κ}

section Hyp

variable (hc : ProperOn G c)
  (h1 : ∀ u v, key u = key v → u ≠ v → G.degree u = G.degree v → Sc G c u = Sc G c v →
    G.degree u = 3)
  (h2 : ∀ u v w, key u = key v → key v = key w → G.degree u = 3 → G.degree v = 3 →
    G.degree w = 3 → u = v ∨ v = w ∨ u = w)

include hc in
omit [DecidableEq V] in
theorem degree_le_three (v : V) : G.degree v ≤ 3 := by
  classical
  rw [← card_Sc hc]
  exact (card_le_univ _).trans (by simp)

include hc h1 in
omit [DecidableEq V] in
/-- Hexagon vertices have degree three. -/
theorem hex_deg3 {w : ZMod 6 → V} (hw : BadHex G c key w) (k : ZMod 6) :
    G.degree (w k) = 3 := by
  classical
  -- the two hexagon edges at a vertex have colours `0` and `1`
  have two : ∀ j : ZMod 6, ({0, 1} : Finset (Fin 3)) ⊆ Sc G c (w j) := by
    intro j
    have a1 : (G01 G c).Adj (w j) (w (j + 1)) := hw.2.1 j
    have a2 : (G01 G c).Adj (w j) (w (j - 1)) := by
      have := hw.2.1 (j - 1); rw [sub_add_cancel] at this; exact this.symm
    have hne : s(w j, w (j + 1)) ≠ s(w j, w (j - 1)) := fun e => by
      rcases Sym2.eq_iff.1 e with ⟨-, h⟩ | ⟨h, -⟩
      · have := hw.1 h
        have h' : ∀ a : ZMod 6, a + 1 ≠ a - 1 := by decide
        exact h' j this
      · have := hw.1 h
        have h' : ∀ a : ZMod 6, a ≠ a - 1 := by decide
        exact h' j this
    have i1 : s(w j, w (j + 1)) ∈ G.incidenceFinset (w j) :=
      (C4.mem_inc G).2 ⟨a1.1, Sym2.mem_mk_left _ _⟩
    have i2 : s(w j, w (j - 1)) ∈ G.incidenceFinset (w j) :=
      (C4.mem_inc G).2 ⟨a2.1, Sym2.mem_mk_left _ _⟩
    have c1 := a1.2
    have c2 := a2.2
    have cne := hc _ _ _ i1 i2 hne
    have m1 : c s(w j, w (j + 1)) ∈ Sc G c (w j) := mem_image_of_mem _ i1
    have m2 : c s(w j, w (j - 1)) ∈ Sc G c (w j) := mem_image_of_mem _ i2
    intro x hx
    have : x = 0 ∨ x = 1 := by simpa using hx
    have hc1 : c s(w j, w (j + 1)) = 0 ∨ c s(w j, w (j + 1)) = 1 := by omega
    have hc2 : c s(w j, w (j - 1)) = 0 ∨ c s(w j, w (j - 1)) = 1 := by omega
    rcases this with rfl | rfl <;> rcases hc1 with e1 | e1 <;> rcases hc2 with e2 | e2 <;>
      simp_all
  have hd := degree_le_three hc (w k)
  have hge : 2 ≤ G.degree (w k) := by
    rw [← card_Sc hc]; exact (card_le_card (two k)).trans' (by decide)
  by_contra hne
  have hd2 : G.degree (w k) = 2 := by omega
  have hd2' : G.degree (w (k + 3)) = 2 := by rw [← (hw.2.2 k).2]; exact hd2
  have e1 : Sc G c (w k) = {0, 1} := (eq_of_subset_of_card_le (two k)
    (by rw [card_Sc hc, hd2]; decide)).symm
  have e2 : Sc G c (w (k + 3)) = {0, 1} := (eq_of_subset_of_card_le (two (k + 3))
    (by rw [card_Sc hc, hd2']; decide)).symm
  have hne' : w k ≠ w (k + 3) := fun e => by
    have := hw.1 e
    have h' : ∀ a : ZMod 6, a ≠ a + 3 := by decide
    exact h' k this
  have := h1 _ _ (hw.2.2 k).1 hne' (hw.2.2 k).2 (by rw [e1, e2])
  omega

include hc in
omit [DecidableEq V] in
/-- The `G01`-neighbours of a vertex off the hexagons are off the hexagons. -/
theorem nonhex_nbr {u x : V} (hu : ¬ IsHex G c key u)
    (hx : (G01 G c).Adj u x) : ¬ IsHex G c key x := by
  classical
  rintro ⟨w, hw, k, rfl⟩
  rcases hex_nbr hc hw k hx.symm with h | h
  · exact hu ⟨w, hw, _, h.symm⟩
  · exact hu ⟨w, hw, _, h.symm⟩
end Hyp

variable (G c key) in
/-- Vertices off the hexagons that could end up with equal colour sets. -/
def Rel (u v : V) : Prop :=
  u ≠ v ∧ key u = key v ∧ G.degree u = G.degree v ∧ (2 ∈ Sc G c u ↔ 2 ∈ Sc G c v) ∧
    ¬ IsHex G c key u ∧ ¬ IsHex G c key v

omit [DecidableEq V] in
theorem Rel.symm {u v : V} (h : Rel G c key u v) : Rel G c key v u := by
  classical
  obtain ⟨a, b, d, e, f, g⟩ := h
  exact ⟨Ne.symm a, b.symm, d.symm, e.symm, g, f⟩

omit [DecidableEq V] in
/-- **`Rel` is a matching.** -/
theorem rel_unique (hc : ProperOn G c)
    (h1 : ∀ u v, key u = key v → u ≠ v → G.degree u = G.degree v → Sc G c u = Sc G c v →
      G.degree u = 3)
    (h2 : ∀ u v w, key u = key v → key v = key w → G.degree u = 3 → G.degree v = 3 →
      G.degree w = 3 → u = v ∨ v = w ∨ u = w)
    {u v w : V} (hv : Rel G c key u v) (hw : Rel G c key u w) : v = w := by
  classical
  by_contra hvw
  obtain ⟨huv, kv, dv, sv, -, -⟩ := hv
  obtain ⟨huw, kw, dw, sw, -, -⟩ := hw
  by_cases h3 : G.degree u = 3
  · rcases h2 u v w kv (kv.symm.trans kw) h3 (dv ▸ h3) (dw ▸ h3) with h | h | h
    · exact huv h
    · exact hvw h
    · exact huw h
  · have hd := degree_le_three hc u
    rcases pigeon3 (Sc G c u) (Sc G c v) (Sc G c w)
      (by rw [card_Sc hc, card_Sc hc, dv]) (by rw [card_Sc hc, card_Sc hc, ← dv, dw])
      (by rw [card_Sc hc]; omega) sv (sv.symm.trans sw) with h | h | h
    · exact h3 (h1 u v kv huv dv h)
    · exact h3 (by rw [dv]; exact h1 v w (kv.symm.trans kw) hvw (by rw [← dv, dw]) h)
    · exact h3 (h1 u w kw huw dw h)
end Bkls.T6

end LeanPool.BalancedEdgeColourings
