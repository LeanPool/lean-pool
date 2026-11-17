/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.L8b

/-!
# Balister–Kostochka–Li–Schelp 2004, Lemma 8, part (c): 1-piles after an exchange

If `c'` is `c` with the pairs `{T, i T}` marked by `tc` interchanged, the number of 1-piles in
`[S₋ ∪ {x}, S₊]_d` changes by `#(touched InA y x) - #(touched InA x y)` (`g_after`): only the pairs
holding exactly one 1-pile move it to the other side.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.L8

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull Balanced Bkls


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
variable {Sm Sp : Finset (Fin k)} {c c' : PEC G (Fin k)} {x y : Fin k}

open Classical in
theorem csplit {α : Type*} [Fintype α] (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    #(univ.filter p) = #(univ.filter fun t => p t ∧ q t) + #(univ.filter fun t => p t ∧ ¬ q t) := by
  rw [← card_union_of_disjoint]
  · congr 1; ext t; simp only [mem_filter, mem_univ, true_and, mem_union]; tauto
  · rw [Finset.disjoint_left]; intro t h1 h2; exact (mem_filter.1 h2).2.2 (mem_filter.1 h1).2.2

open Classical in
theorem cfilter_congr {α : Type*} [Fintype α] {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (h : ∀ t, p t ↔ q t) :
    #(univ.filter p) = #(univ.filter q) := by
  congr 1; ext t; simp only [mem_filter, mem_univ, true_and]; exact h t

open Classical in
theorem sub_swap_iff (hxS : x ∉ Sm) (hyS : y ∉ Sm) (T : Finset (Fin k)) :
    Sm ⊆ swapSet x y T ↔ Sm ⊆ T := by
  constructor
  · intro h z hz
    have hzx : z ≠ x := fun e => hxS (e ▸ hz)
    have hzy : z ≠ y := fun e => hyS (e ▸ hz)
    have := h hz
    rwa [mem_swapSet, Equiv.swap_apply_of_ne_of_ne hzx hzy] at this
  · intro h z hz
    have hzx : z ≠ x := fun e => hxS (e ▸ hz)
    have hzy : z ≠ y := fun e => hyS (e ▸ hz)
    rw [mem_swapSet, Equiv.swap_apply_of_ne_of_ne hzx hzy]; exact h hz

open Classical in
theorem swap_sub_iff (hx : x ∈ Sp) (hy : y ∈ Sp) (T : Finset (Fin k)) :
    swapSet x y T ⊆ Sp ↔ T ⊆ Sp := by
  have key : ∀ T : Finset (Fin k), T ⊆ Sp → swapSet x y T ⊆ Sp := by
    intro T h z hz
    rw [mem_swapSet] at hz
    by_cases hzx : z = x
    · rw [hzx]; exact hx
    by_cases hzy : z = y
    · rw [hzy]; exact hy
    rw [Equiv.swap_apply_of_ne_of_ne hzx hzy] at hz; exact h hz
  constructor
  · intro h; rw [← swapSet_swapSet x y T]; exact key _ h
  · exact key T

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **1-piles after an exchange.** -/
theorem g_after (hx : x ∈ Sp) (hy : y ∈ Sp) (hxS : x ∉ Sm) (hyS : y ∉ Sm)
    (tc : Finset (Fin k) → Prop) [DecidablePred tc] (htc : ∀ T, tc (swapSet x y T) ↔ tc T)
    (hc' : ∀ T, cnt c' T = cnt c (if tc T then swapSet x y T else T)) (d : ℕ) :
    (g Sm Sp c' x d : ℤ) = g Sm Sp c x d - #(univ.filter fun T => InA Sm Sp c x y d T ∧ tc T) +
      #(univ.filter fun T => InA Sm Sp c y x d T ∧ tc T) := by
  classical
  have hg : ∀ c : PEC G (Fin k), (g Sm Sp c x d : ℤ) =
      #(univ.filter fun T => (Sm ⊆ T ∧ T ⊆ Sp ∧ x ∈ T ∧ #T = d ∧ cnt c T = 1) ∧ y ∈ T) +
      #(univ.filter fun T => ((Sm ⊆ T ∧ T ⊆ Sp ∧ x ∈ T ∧ #T = d ∧ cnt c T = 1) ∧ ¬ y ∈ T) ∧
        tc T) +
      #(univ.filter fun T => ((Sm ⊆ T ∧ T ⊆ Sp ∧ x ∈ T ∧ #T = d ∧ cnt c T = 1) ∧ ¬ y ∈ T) ∧
        ¬ tc T) := by
    intro c
    have h1 := csplit (fun T => Sm ⊆ T ∧ T ⊆ Sp ∧ x ∈ T ∧ #T = d ∧ cnt c T = 1) (fun T => y ∈ T)
    have h2 := csplit (fun T => (Sm ⊆ T ∧ T ⊆ Sp ∧ x ∈ T ∧ #T = d ∧ cnt c T = 1) ∧ ¬ y ∈ T) tc
    beta_reduce at h1 h2
    unfold g
    rw [h1, h2]
    push_cast
    ring
  have e1 : #(univ.filter fun T => (Sm ⊆ T ∧ T ⊆ Sp ∧ x ∈ T ∧ #T = d ∧ cnt c' T = 1) ∧ y ∈ T) =
      #(univ.filter fun T => (Sm ⊆ T ∧ T ⊆ Sp ∧ x ∈ T ∧ #T = d ∧ cnt c T = 1) ∧ y ∈ T) := by
    apply cfilter_congr
    intro T
    have hcT : y ∈ T → x ∈ T → cnt c' T = cnt c T := by
      intro hyT hxT
      rw [hc']
      split_ifs
      · rw [swapSet_eq_of_iff (by tauto)]
      · rfl
    constructor
    · rintro ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩
      exact ⟨⟨h1, h2, h3, h4, by rw [← hcT h6 h3]; exact h5⟩, h6⟩
    · rintro ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩
      exact ⟨⟨h1, h2, h3, h4, by rw [hcT h6 h3]; exact h5⟩, h6⟩
  have e2 : #(univ.filter fun T => ((Sm ⊆ T ∧ T ⊆ Sp ∧ x ∈ T ∧ #T = d ∧ cnt c' T = 1) ∧
      ¬ y ∈ T) ∧ ¬ tc T) = #(univ.filter fun T => ((Sm ⊆ T ∧ T ⊆ Sp ∧ x ∈ T ∧ #T = d ∧
      cnt c T = 1) ∧ ¬ y ∈ T) ∧ ¬ tc T) := by
    apply cfilter_congr
    intro T
    constructor
    · rintro ⟨⟨⟨h1, h2, h3, h4, h5⟩, h6⟩, h7⟩
      rw [hc', ite_eq_right h7] at h5; exact ⟨⟨⟨h1, h2, h3, h4, h5⟩, h6⟩, h7⟩
    · rintro ⟨⟨⟨h1, h2, h3, h4, h5⟩, h6⟩, h7⟩
      refine ⟨⟨⟨h1, h2, h3, h4, ?_⟩, h6⟩, h7⟩
      rw [hc', ite_eq_right h7]; exact h5
  -- the touched `x`-only 1-piles, before and after
  have e3 : #(univ.filter fun T => ((Sm ⊆ T ∧ T ⊆ Sp ∧ x ∈ T ∧ #T = d ∧ cnt c T = 1) ∧
      ¬ y ∈ T) ∧ tc T) =
      #(univ.filter fun T => (((Sm ⊆ T ∧ T ⊆ Sp ∧ x ∈ T ∧ #T = d ∧ cnt c T = 1) ∧ ¬ y ∈ T) ∧
        tc T) ∧ cnt c (swapSet x y T) = 1) +
      #(univ.filter fun T => InA Sm Sp c x y d T ∧ tc T) := by
    rw [csplit (fun T => ((Sm ⊆ T ∧ T ⊆ Sp ∧ x ∈ T ∧ #T = d ∧ cnt c T = 1) ∧ ¬ y ∈ T) ∧ tc T)
      (fun T => cnt c (swapSet x y T) = 1)]
    congr 1
    apply cfilter_congr; intro T; unfold InA; tauto
  have hc'' : ∀ T, tc T → cnt c' T = cnt c (swapSet x y T) := fun T h => by rw [hc', ite_eq_left h]
  have e4 : #(univ.filter fun T => ((Sm ⊆ T ∧ T ⊆ Sp ∧ x ∈ T ∧ #T = d ∧ cnt c' T = 1) ∧
      ¬ y ∈ T) ∧ tc T) =
      #(univ.filter fun T => (((Sm ⊆ T ∧ T ⊆ Sp ∧ x ∈ T ∧ #T = d ∧ cnt c T = 1) ∧ ¬ y ∈ T) ∧
        tc T) ∧ cnt c (swapSet x y T) = 1) +
      #(univ.filter fun T => InA Sm Sp c y x d T ∧ tc T) := by
    rw [csplit (fun T => ((Sm ⊆ T ∧ T ⊆ Sp ∧ x ∈ T ∧ #T = d ∧ cnt c' T = 1) ∧ ¬ y ∈ T) ∧ tc T)
      (fun T => cnt c T = 1)]
    congr 1
    · apply cfilter_congr; intro T
      constructor
      · rintro ⟨⟨⟨⟨h1, h2, h3, h4, h5⟩, h6⟩, h7⟩, h8⟩
        rw [hc'' T h7] at h5; exact ⟨⟨⟨⟨h1, h2, h3, h4, h8⟩, h6⟩, h7⟩, h5⟩
      · rintro ⟨⟨⟨⟨h1, h2, h3, h4, h8⟩, h6⟩, h7⟩, h5⟩
        exact ⟨⟨⟨⟨h1, h2, h3, h4, by rw [hc'' T h7]; exact h5⟩, h6⟩, h7⟩, h8⟩
    · -- `T ↦ i T`
      refine card_bij (fun T _ => swapSet x y T) (fun T hT => ?_) (fun T _ T' _ h => ?_)
        (fun T hT => ?_)
      · obtain ⟨⟨⟨⟨h1, h2, h3, h4, h5⟩, h6⟩, h7⟩, h8⟩ := (mem_filter.1 hT).2
        rw [hc'' T h7] at h5
        refine mem_filter.2 ⟨mem_univ _, ⟨(sub_swap_iff hxS hyS T).2 h1,
          (swap_sub_iff hx hy T).2 h2, ?_, ?_, by rw [card_swapSet]; exact h4, h5, ?_⟩,
          (htc T).2 h7⟩
        · rw [mem_swapSet, Equiv.swap_apply_right]; exact h3
        · rw [mem_swapSet, Equiv.swap_apply_left]; exact h6
        · rw [swapSet_comm, swapSet_swapSet]; exact h8
      · rw [← swapSet_swapSet x y T, h, swapSet_swapSet]
      · obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8⟩ := (mem_filter.1 hT).2
        refine ⟨swapSet x y T, mem_filter.2 ⟨mem_univ _, ⟨⟨⟨⟨(sub_swap_iff hxS hyS T).2 h1,
          (swap_sub_iff hx hy T).2 h2, ?_, by rw [card_swapSet]; exact h5, ?_⟩, ?_⟩,
          (htc T).2 h8⟩, ?_⟩⟩, swapSet_swapSet x y T⟩
        · rw [mem_swapSet, Equiv.swap_apply_left]; exact h3
        · rw [hc'' _ ((htc T).2 h8), swapSet_swapSet]; exact h6
        · rw [mem_swapSet, Equiv.swap_apply_right]; exact h4
        · rw [swapSet_comm] at h7; exact h7
  have hgc := hg c
  have hgc' := hg c'
  rw [e1, e2, e4] at hgc'
  rw [e3] at hgc
  push_cast at hgc hgc'
  linarith
end Bkls.L8

end LeanPool.BalancedEdgeColourings
