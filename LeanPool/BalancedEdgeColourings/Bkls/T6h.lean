/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.T6g

/-!
# Balister–Kostochka–Li–Schelp 2004, Theorem 6

`G` is properly edge-coloured with three colours by `c`, and `key` is a relation on the vertices
(`key u = key v`) such that

* (1) two distinct vertices with the same key, the same degree and the same colour set have
  degree three;
* (2) no three distinct vertices of degree three share a key.

Then `G` has a proper edge-colouring with four colours in which distinct vertices with the same key
see different colour sets (`thm6`).

The proof: recolour the edges of colours `0, 1` off the bad hexagons by Corollary 4 (`step_cor4`),
colour the edges of colour `2` (`col2`), then fix the bad hexagons one at a time by Lemma 5
(`fix_hexagons`).
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.T6

open Finset SimpleGraph _root_.LeanPool.BalancedEdgeColourings.Bkls.Comp

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {c : Sym2 V → Fin 3} {κ : Type*} {key : V → κ}

variable (G c key) in
/-- Hexagon edges and diagonals of bad hexagons. -/
def HexInternal (e : Sym2 V) : Prop :=
  ∃ w, BadHex G c key w ∧ ∃ k, e = s(w k, w (k + 1)) ∨
    (G.Adj (w k) (w (k + 3)) ∧ e = s(w k, w (k + 3)))

variable (G c key) in
/-- `col` is proper at `z` and separates `z` from its opposite vertex (if `z` is on a hexagon). -/
def GoodAt (col : Sym2 V → Fin 4) (z : V) : Prop :=
  IsHex G c key z → (∀ e e', e ∈ G.incidenceFinset z → e' ∈ G.incidenceFinset z → e ≠ e' →
    col e ≠ col e') ∧ ∀ z', Opp G c key z z' → Sc G col z ≠ Sc G col z'

section Hyp

variable (hc : ProperOn G c)
  (h1 : ∀ u v, key u = key v → u ≠ v → G.degree u = G.degree v → Sc G c u = Sc G c v →
    G.degree u = 3)
  (h2 : ∀ u v w, key u = key v → key v = key w → G.degree u = 3 → G.degree v = 3 →
    G.degree w = 3 → u = v ∨ v = w ∨ u = w)

include hc h1 h2 in
omit [DecidableEq V] in
theorem pend_not_internal {x x' y : V} (o : Opp G c key x x') (hna : ¬ G.Adj x x')
    (hy : G.Adj x y) (hcy : c s(x, y) = 2) : ¬ HexInternal G c key s(x, y) := by
  classical
  rintro ⟨w, hw, k, h | ⟨-, h⟩⟩
  · have := (hw.2.1 k).2
    rw [← h] at this
    exact this hcy
  · rcases Sym2.eq_iff.1 h with ⟨a, b⟩ | ⟨a, b⟩
    · have : x' = y := opp_unique hc h1 h2 o (by rw [a, b]; exact opp_of_hex hw k)
      exact hna (by rw [this]; exact hy)
    · have : x' = y := opp_unique hc h1 h2 o (by rw [a, b]; exact (opp_of_hex hw k).symm)
      exact hna (by rw [this]; exact hy)

include hc h1 h2 in
omit [DecidableEq V] in
/-- **Fixing the hexagons one at a time.** -/
theorem fix_hexagons (col2 : Sym2 V → Fin 4)
    (hpend : ∀ x x' y y', Opp G c key x x' → ¬ G.Adj x x' → G.Adj x y → c s(x, y) = 2 →
      G.Adj x' y' → c s(x', y') = 2 → col2 s(x, y) ≠ col2 s(x', y')) :
    ∃ col, (∀ e, ¬ HexInternal G c key e → col e = col2 e) ∧ ∀ z, GoodAt G c key col z := by
  classical
  suffices H : ∀ T : Finset V, ∃ col, (∀ e, ¬ HexInternal G c key e → col e = col2 e) ∧
      ∀ z ∈ T, GoodAt G c key col z by
    obtain ⟨col, h, h'⟩ := H univ
    exact ⟨col, h, fun z => h' z (mem_univ z)⟩
  intro T
  induction T using Finset.induction_on with
  | empty => exact ⟨col2, fun _ _ => rfl, fun z hz => absurd hz (notMem_empty z)⟩
  | @insert z T hzT ih =>
    obtain ⟨col, hinv, hgood⟩ := ih
    by_cases hz : IsHex G c key z
    swap
    · refine ⟨col, hinv, fun z' hz' => ?_⟩
      rcases mem_insert.1 hz' with rfl | h
      · exact fun h => absurd h hz
      · exact hgood z' h
    obtain ⟨w, hw, k, rfl⟩ := hz
    have hpend' : ∀ i, ¬ G.Adj (w i) (w (i + 3)) → ∀ y y', G.Adj (w i) y → c s(w i, y) = 2 →
        G.Adj (w (i + 3)) y' → c s(w (i + 3), y') = 2 →
        col s(w i, y) ≠ col s(w (i + 3), y') := by
      intro i hna y y' hy hcy hy' hcy'
      rw [hinv _ (pend_not_internal hc h1 h2 (opp_of_hex hw i) hna hy hcy),
        hinv _ (pend_not_internal hc h1 h2 (opp_of_hex hw i).symm (fun h => hna h.symm) hy' hcy')]
      exact hpend _ _ _ _ (opp_of_hex hw i) hna hy hcy hy' hcy'
    obtain ⟨col', hsame, hloc⟩ := hex_step hc h1 hw col hpend'
    -- edges at a vertex off this hexagon are unchanged
    have hun : ∀ x, (¬ ∃ j, w j = x) → ∀ e ∈ G.incidenceFinset x, col' e = col e := by
      intro x hx e he
      rw [C4.mem_inc] at he
      apply hsame
      · intro k' hk
        rw [hk] at he
        rcases Sym2.mem_iff.1 he.2 with h | h
        · exact hx ⟨k', h.symm⟩
        · exact hx ⟨k' + 1, h.symm⟩
      · intro i _ hk
        rw [hk] at he
        rcases Sym2.mem_iff.1 he.2 with h | h
        · exact hx ⟨i, h.symm⟩
        · exact hx ⟨i + 3, h.symm⟩
    have hSc : ∀ x, (¬ ∃ j, w j = x) → Sc G col' x = Sc G col x := fun x hx =>
      image_congr (fun e he => hun x hx e (mem_coe.1 he))
    refine ⟨col', fun e he => ?_, fun z' hz' => ?_⟩
    · rw [hsame e (fun k' hk => he ⟨w, hw, k', Or.inl hk⟩)
        (fun i hi hk => he ⟨w, hw, i, Or.inr ⟨hi, hk⟩⟩)]
      exact hinv e he
    · intro hz'hex
      by_cases hin : ∃ j, w j = z'
      · obtain ⟨j, rfl⟩ := hin
        refine ⟨(hloc j).1, fun z'' o => ?_⟩
        rw [opp_unique hc h1 h2 o (opp_of_hex hw j)]
        exact (hloc j).2
      · have hz'T : z' ∈ T := by
          rcases mem_insert.1 hz' with h | h
          · exact absurd ⟨k, h.symm⟩ hin
          · exact h
        obtain ⟨hp, hs⟩ := hgood z' hz'T hz'hex
        refine ⟨fun e e' he he' hne => ?_, fun z'' o => ?_⟩
        · rw [hun z' hin e he, hun z' hin e' he']
          exact hp e e' he he' hne
        · have hz'' : ¬ ∃ j, w j = z'' := by
            rintro ⟨j, rfl⟩
            exact hin ⟨j + 3, (opp_unique hc h1 h2 o.symm (opp_of_hex hw j)).symm⟩
          rw [hSc z' hin, hSc z'' hz'']
          exact hs z'' o
end Hyp

omit [DecidableEq V] in
/-- **Theorem 6.** -/
theorem thm6 (hc : ProperOn G c)
    (h1 : ∀ u v, key u = key v → u ≠ v → G.degree u = G.degree v → Sc G c u = Sc G c v →
      G.degree u = 3)
    (h2 : ∀ u v w, key u = key v → key v = key w → G.degree u = 3 → G.degree v = 3 →
      G.degree w = 3 → u = v ∨ v = w ∨ u = w) :
    ∃ col : Sym2 V → Fin 4, ProperOn G col ∧
      ∀ u v, u ≠ v → key u = key v → Sc G col u ≠ Sc G col v := by
  classical
  obtain ⟨col01, hcol01', hrel⟩ := step_cor4 hc h1 h2
  have hcol01 : ∀ x, ¬ IsHex G c key x → ∀ e e', e ∈ inc01 G c x → e' ∈ inc01 G c x →
      e ≠ e' → col01 e ≠ col01 e' := fun x hx e e' => hcol01' x e e' hx
  obtain ⟨lg, hlg⟩ := pendant_colour hc h1 h2
  obtain ⟨kk, hkk⟩ := exists_kk hc h1 hcol01
  obtain ⟨gb, hgQ, hgR⟩ := exists_gb hc h1 h2
  have hkk2 : ∀ u, kk u ≠ 2 := fun u => (hkk u).1
  have hkkA : ∀ u, ¬ IsHex G c key u → (2 : Fin 3) ∈ Sc G c u → kk u ∉ Aset G c col01 u :=
    fun u hu h2u => ((hkk u).2 hu h2u).1
  have hkkS : ∀ u, ¬ IsHex G c key u → (2 : Fin 3) ∈ Sc G c u → ∀ v, v ≠ u → key v = key u →
      G.degree v = G.degree u → (2 : Fin 3) ∉ Sc G c v →
      insert (kk u) (Aset G c col01 u) ≠ Aset G c col01 v :=
    fun u hu h2u => ((hkk u).2 hu h2u).2
  obtain ⟨col, hinv, hgood⟩ := fix_hexagons hc h1 h2 (col2 G c key col01 lg kk gb)
    (fun x x' y y' o hna hy hcy hy' hcy' =>
      col2_pend hc h1 h2 hlg hkk2 hgQ o hna hy hcy hy' hcy')
  have hoff : ∀ x, ¬ IsHex G c key x → ∀ e ∈ G.incidenceFinset x,
      col e = col2 G c key col01 lg kk gb e := by
    intro x hx e he
    apply hinv
    rintro ⟨w, hw, k, h | ⟨-, h⟩⟩
    · rw [C4.mem_inc, h] at he
      rcases Sym2.mem_iff.1 he.2 with rfl | rfl
      · exact hx ⟨w, hw, _, rfl⟩
      · exact hx ⟨w, hw, _, rfl⟩
    · rw [C4.mem_inc, h] at he
      rcases Sym2.mem_iff.1 he.2 with rfl | rfl
      · exact hx ⟨w, hw, _, rfl⟩
      · exact hx ⟨w, hw, _, rfl⟩
  have hSoff : ∀ x, ¬ IsHex G c key x → Sc G col x = Sc G (col2 G c key col01 lg kk gb) x :=
    fun x hx => image_congr (fun e he => hoff x hx e (mem_coe.1 he))
  have hprop : ProperOn G col := by
    intro x e e' he he' hne
    by_cases hx : IsHex G c key x
    · exact (hgood x hx).1 e e' he he' hne
    · rw [hoff x hx e he, hoff x hx e' he']
      exact col2_proper hc hcol01 hkkA hx e e' he he' hne
  have hexcase : ∀ u v, u ≠ v → key u = key v → IsHex G c key u → Sc G col u ≠ Sc G col v := by
    intro u v huv hk hu
    by_cases hd : G.degree v = 3
    · obtain ⟨w, hw, k, rfl⟩ := hu
      have o := opp_of_hex hw k
      rcases h2 (w k) (w (k + 3)) v o.key_eq (o.key_eq.symm.trans hk)
        (hex_deg3' hc h1 o.hex) (hex_deg3' hc h1 o.symm.hex) hd with h | h | h
      · exact absurd h o.ne
      · subst h
        exact (hgood _ o.hex).2 _ o
      · exact absurd h huv
    · intro h
      apply hd
      rw [← card_Sc hprop v, ← h, card_Sc hprop, hex_deg3' hc h1 hu]
  refine ⟨col, hprop, fun u v huv hk => ?_⟩
  by_cases hu : IsHex G c key u
  · exact hexcase u v huv hk hu
  by_cases hv : IsHex G c key v
  · exact (hexcase v u (Ne.symm huv) hk.symm hv).symm
  rw [hSoff u hu, hSoff v hv]
  exact col2_sep hc hcol01 hrel hkk2 hkkA hkkS hgR hu hv huv hk
end Bkls.T6

end LeanPool.BalancedEdgeColourings
