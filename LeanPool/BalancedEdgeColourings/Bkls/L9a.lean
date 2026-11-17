/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.L7b
public import LeanPool.BalancedEdgeColourings.Bkls.L8e

/-!
# Balister–Kostochka–Li–Schelp 2004, Lemma 9, part (a): one stage

`Up T`: `S₋ ∪ {γ} ⊆ T`; `Out T`: `S₋ ⊆ T`, `γ ∉ T`. In an optimal colouring with all `n_T ≤ 2`
and every 2-pile in `[S₋, [k]]`, `stage_engine` moves the 2-piles of `Out` into `Up` one at a time:
an E1 move onto an empty square `S₀ - y + γ` when one exists, after a Lemma 7 recolouring
otherwise; the 1-piles of `Up` and of `Out` at each degree are kept. The per-degree room is a
hypothesis (`hroom`) in terms of the numbers `g1` (1-piles in `Up`), `h1` (1-piles in `Out`) and
`y2` (2-piles) of the starting colouring.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.L9

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull Balanced Bkls


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}

section Defs

variable (Sm : Finset (Fin k)) (γ : Fin k) (c : PEC G (Fin k))

open Classical in
/-- 1-piles in `[S₋ ∪ {γ}, [k]]_d`. -/
noncomputable def g1 (d : ℕ) : ℕ :=
  #(univ.filter fun T => (Sm ⊆ T ∧ γ ∈ T ∧ #T = d) ∧ cnt c T = 1)

open Classical in
/-- 1-piles in `[S₋, [k] \ {γ}]_d`. -/
noncomputable def h1 (d : ℕ) : ℕ :=
  #(univ.filter fun T => (Sm ⊆ T ∧ γ ∉ T ∧ #T = d) ∧ cnt c T = 1)

open Classical in
/-- 2-piles of degree `d`. -/
noncomputable def y2 (d : ℕ) : ℕ := #(univ.filter fun T => #T = d ∧ cnt c T = 2)

open Classical in
/-- 2-piles still to be moved. -/
noncomputable def bad : ℕ := #(univ.filter fun T => (Sm ⊆ T ∧ γ ∉ T) ∧ cnt c T = 2)

end Defs

open Classical in
theorem card_supersets (A : Finset (Fin k)) {d : ℕ} (hd : #A ≤ d) :
    #(univ.filter fun T : Finset (Fin k) => A ⊆ T ∧ #T = d) = (k - #A).choose (d - #A) := by
  have h1 : #(univ \ A) = k - #A := by rw [card_sdiff_of_subset (subset_univ A), card_fin]
  rw [← h1, ← card_powersetCard]
  refine card_bij (fun T _ => T \ A) (fun T hT => ?_) (fun T hT T' hT' h => ?_) (fun U hU => ?_)
  · obtain ⟨hA, hc⟩ := (mem_filter.1 hT).2
    rw [mem_powersetCard]
    refine ⟨sdiff_subset_sdiff (subset_univ T) le_rfl, ?_⟩
    have := card_sdiff_add_card_eq_card hA
    omega
  · obtain ⟨hA, -⟩ := (mem_filter.1 hT).2
    obtain ⟨hA', -⟩ := (mem_filter.1 hT').2
    rw [← sdiff_union_of_subset hA, ← sdiff_union_of_subset hA', h]
  · rw [mem_powersetCard] at hU
    obtain ⟨hU1, hU2⟩ := hU
    have hdisj : Disjoint U A := by
      rw [Finset.disjoint_left]; intro x hx hxA; exact (mem_sdiff.1 (hU1 hx)).2 hxA
    refine ⟨U ∪ A, mem_filter.2 ⟨mem_univ _, subset_union_right, ?_⟩, ?_⟩
    · rw [card_union_of_disjoint hdisj, hU2]; omega
    · show (U ∪ A) \ A = U
      rw [union_sdiff_right, sdiff_eq_self_of_disjoint hdisj]

variable {Sm : Finset (Fin k)} {γ : Fin k}

open Classical in
/-- The invariant along a stage. -/
def Inv (Sm : Finset (Fin k)) (γ : Fin k) (c c' : PEC G (Fin k)) : Prop :=
  Rec (univ \ Sm) c c' ∧ (∀ d, g1 Sm γ c' d = g1 Sm γ c d) ∧ (∀ d, h1 Sm γ c' d = h1 Sm γ c d)

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem rec_cnt_le {R : Finset (Fin k)} {c c' : PEC G (Fin k)} (h : Rec R c c')
    (hn : ∀ T, cnt c T ≤ 2) (T : Finset (Fin k)) : cnt c' T ≤ 2 := by
  classical
  obtain ⟨-, π, -, e⟩ := h; rw [e]; exact hn _

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem rec_y2 {R : Finset (Fin k)} {c c' : PEC G (Fin k)} (h : Rec R c c') (d : ℕ) :
    y2 c' d = y2 c d := by
  classical
  have := h.card_filter (fun T => #T = d) (fun T T' hc _ => by rw [hc]) 2
  unfold y2
  convert this using 3

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem rec_sub {R : Finset (Fin k)} (hR : R ⊆ univ \ Sm) {c c' : PEC G (Fin k)} (h : Rec R c c')
    (hall : ∀ T, cnt c T = 2 → Sm ⊆ T) : ∀ T, cnt c' T = 2 → Sm ⊆ T := by
  classical
  obtain ⟨-, π, hπ, e⟩ := h
  intro T hT
  rw [e] at hT
  have := hall _ hT
  intro x hx
  have hxR : x ∉ R := fun h' => (mem_sdiff.1 (hR h')).2 hx
  exact (hπ.2 T x hxR).1 (this hx)

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Moving one 2-pile onto an empty `S₀ - y + γ`. -/
theorem e1_step (hγ : γ ∉ Sm) {c c' : PEC G (Fin k)} (hinv : Inv Sm γ c c')
    {S0 : Finset (Fin k)} (hS0 : Sm ⊆ S0) (hγS0 : γ ∉ S0) (h2 : cnt c' S0 = 2) {y : Fin k}
    (hy : y ∈ S0) (hyS : y ∉ Sm) (h0 : cnt c' (swapSet y γ S0) = 0) :
    ∃ c'', Inv Sm γ c c'' ∧ bad Sm γ c'' + 1 = bad Sm γ c' := by
  classical
  have hyγ : y ≠ γ := fun e => hγS0 (e ▸ hy)
  obtain ⟨c'', hrec, e1, e2, e3⟩ := rec_two hinv.1.opt hyγ (R := univ \ Sm)
    (mem_sdiff.2 ⟨mem_univ _, hyS⟩) (mem_sdiff.2 ⟨mem_univ _, hγ⟩) (S := S0) (by rw [h0, h2])
  set T := swapSet y γ S0 with hTdef
  have hγT : γ ∈ T := by rw [hTdef, mem_swapSet, Equiv.swap_apply_right]; exact hy
  have hTS : T ≠ S0 := fun e => hγS0 (e ▸ hγT)
  have hone : ∀ X, cnt c'' X = 1 ↔ cnt c' X = 1 := by
    intro X
    by_cases h1 : X = S0
    · subst h1; rw [e1, h0, h2]; simp
    by_cases h3 : X = T
    · subst h3; rw [e2, h0, h2]; simp
    rw [e3 X h1 h3]
  refine ⟨c'', ⟨hinv.1.trans hrec, fun d => ?_, fun d => ?_⟩, ?_⟩
  · rw [← hinv.2.1 d]; unfold g1; apply L8.cfilter_congr; intro X; rw [hone]
  · rw [← hinv.2.2 d]; unfold h1; apply L8.cfilter_congr; intro X; rw [hone]
  · unfold bad
    have hS0mem : S0 ∈ univ.filter fun X => (Sm ⊆ X ∧ γ ∉ X) ∧ cnt c' X = 2 :=
      mem_filter.2 ⟨mem_univ _, ⟨hS0, hγS0⟩, h2⟩
    rw [← card_erase_add_one hS0mem]
    congr 1
    congr 1
    ext X
    simp only [mem_filter, mem_univ, true_and, mem_erase]
    constructor
    · rintro ⟨⟨h1, h3⟩, h4⟩
      have hXS : X ≠ S0 := fun e => by rw [e, e1, h0] at h4; omega
      have hXT : X ≠ T := fun e => h3 (e ▸ hγT)
      exact ⟨hXS, ⟨h1, h3⟩, by rw [← e3 X hXS hXT]; exact h4⟩
    · rintro ⟨hXS, ⟨h1, h3⟩, h4⟩
      have hXT : X ≠ T := fun e => h3 (e ▸ hγT)
      exact ⟨⟨h1, h3⟩, by rw [e3 X hXS hXT]; exact h4⟩
end Bkls.L9

end LeanPool.BalancedEdgeColourings
