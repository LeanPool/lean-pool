/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.L9b

/-!
# Balister–Kostochka–Li–Schelp 2004, Lemma 9, part (d): a full stage

`stage`: Lemma 8 (with `d₀ = k - 1`) followed by `stage_engine`. The room is checked degree by
degree: at most one pile and no 1-pile when `d ≤ 4` (`hsmall`); the single square of degree
`k - 1` outside, emptied of 1-piles by the second part of Lemma 8, when `d = k - 1` (`hkm1`); the
inequality of Lemma 7 for `5 ≤ d ≤ k - 2` (`hgen`, given the Lemma 8 bound). The bound of Lemma 8
on the new 1-piles is exported for the next stage.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.L9

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull Balanced Bkls


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
variable {Sm : Finset (Fin k)} {γ : Fin k}

open Classical in
/-- 1-piles of degree `d`. -/
noncomputable def x1 (c : PEC G (Fin k)) (d : ℕ) : ℕ :=
  #(univ.filter fun T : Finset (Fin k) => #T = d ∧ cnt c T = 1)

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem rec_x1 {R : Finset (Fin k)} {c c' : PEC G (Fin k)} (h : Rec R c c') (d : ℕ) :
    x1 c' d = x1 c d := by
  classical
  have := h.card_filter (fun T => #T = d) (fun T T' hc _ => by rw [hc]) 1
  unfold x1; convert this using 3

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem g1_eq_g (c : PEC G (Fin k)) (d : ℕ) : g1 Sm γ c d = L8.g Sm univ c γ d := by
  classical
  unfold g1 L8.g
  apply L8.cfilter_congr
  intro T
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨h1, subset_univ _, h2, h3, h4⟩
  · rintro ⟨h1, -, h2, h3, h4⟩; exact ⟨⟨h1, h2, h3⟩, h4⟩

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem Gd_eq (c : PEC G (Fin k)) (d : ℕ) :
    L8.Gd Sm univ c d = g1 Sm γ c d + h1 Sm γ c d := by
  classical
  unfold L8.Gd g1 h1
  rw [L8.csplit (fun T => Sm ⊆ T ∧ T ⊆ univ ∧ #T = d ∧ cnt c T = 1) (fun T => γ ∈ T)]
  congr 1
  · apply L8.cfilter_congr; intro T
    constructor
    · rintro ⟨⟨h1, -, h3, h4⟩, h2⟩; exact ⟨⟨h1, h2, h3⟩, h4⟩
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨⟨h1, subset_univ _, h3, h4⟩, h2⟩
  · apply L8.cfilter_congr; intro T
    constructor
    · rintro ⟨⟨h1, -, h3, h4⟩, h2⟩; exact ⟨⟨h1, h2, h3⟩, h4⟩
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨⟨h1, subset_univ _, h3, h4⟩, h2⟩

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem g1_le_x1 (c : PEC G (Fin k)) (d : ℕ) : g1 Sm γ c d ≤ x1 c d := by
  classical
  unfold g1 x1
  apply card_le_card
  intro T hT
  obtain ⟨⟨-, -, h3⟩, h4⟩ := (mem_filter.1 hT).2
  exact mem_filter.2 ⟨mem_univ _, h3, h4⟩
open Classical in
theorem card_out_top (_ : γ ∉ Sm) :
    #(univ.filter fun T : Finset (Fin k) => Sm ⊆ T ∧ γ ∉ T ∧ #T = k) = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro T - ⟨-, hγT, hT⟩
  have : T = univ := eq_univ_of_card T (by rw [hT, Fintype.card_fin])
  exact hγT (this ▸ mem_univ γ)

open Classical in
theorem card_out_km1 (hγ : γ ∉ Sm) (_ : 1 ≤ k) :
    #(univ.filter fun T : Finset (Fin k) => Sm ⊆ T ∧ γ ∉ T ∧ #T = k - 1) = 1 := by
  rw [card_eq_one]
  refine ⟨univ.erase γ, ?_⟩
  ext T
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨-, hγT, hT⟩
    have hsub : T ⊆ univ.erase γ := fun z hz => mem_erase.2 ⟨fun e => hγT (e ▸ hz), mem_univ _⟩
    refine eq_of_subset_of_card_le hsub ?_
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, hT]
  · rintro rfl
    refine ⟨fun z hz => mem_erase.2 ⟨fun e => hγ (e ▸ hz), mem_univ _⟩, fun h => ?_, ?_⟩
    · exact (mem_erase.1 h).1 rfl
    · rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem y2_zero_of_gt (c : PEC G (Fin k)) {d : ℕ} (hd : k < d) : y2 c d = 0 := by
  classical
  unfold y2
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro T - ⟨hT, -⟩
  have := card_le_univ T
  rw [Fintype.card_fin] at this
  omega

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **One stage.** -/
theorem stage (hγ : γ ∉ Sm) (hSm2 : #Sm ≤ 2) {c : PEC G (Fin k)} (hopt : IsOptimal c)
    (hn2 : ∀ T, cnt c T ≤ 2) (hall : ∀ T, cnt c T = 2 → Sm ⊆ T)
    (hsmall : ∀ d, 1 ≤ y2 c d → d ≤ 4 → 3 ≤ d ∧ x1 c d = 0 ∧ y2 c d = 1)
    (hkm1 : 5 ≤ k - 1 → y2 c (k - 1) + #Sm + 1 ≤ k)
    (hgen : ∀ d, 5 ≤ d → d + 2 ≤ k → 1 ≤ y2 c d → ∀ g : ℕ,
      (k - #Sm) * g ≤ (d - #Sm) * L8.Gd Sm univ c d + (k - #Sm - 1) →
      (((k - #Sm - 1).choose (d - #Sm - 1) : ℕ) : ℚ) / (((d - #Sm : ℕ) : ℚ) - 1) - 1 ≤
        (((k - #Sm - 1).choose (d - #Sm - 1) : ℕ) : ℚ) - g - ((y2 c d - 1 : ℕ) : ℚ)) :
    ∃ c', Rec (univ \ Sm) c c' ∧ (∀ T, cnt c' T ≤ 2) ∧ (∀ T, cnt c' T = 2 → Sm ⊆ T ∧ γ ∈ T) ∧
      ∀ d, (k - #Sm) * g1 Sm γ c' d ≤ (d - #Sm) * L8.Gd Sm univ c d + (k - #Sm - 1) := by
  classical
  have hγS : γ ∈ univ \ Sm := mem_sdiff.2 ⟨mem_univ _, hγ⟩
  obtain ⟨c1, hrec1, hb1, hb2⟩ := L8.lemma8 (Sp := univ) hopt hn2 (subset_univ Sm) hγS (k - 1)
  have hk : #(univ : Finset (Fin k)) = k := by rw [card_univ, Fintype.card_fin]
  rw [hk] at hb1 hb2
  have hopt1 := hrec1.opt
  have hn21 := rec_cnt_le hrec1 hn2
  have hall1 := rec_sub (subset_refl _) hrec1 hall
  have hy2 : ∀ d, y2 c1 d = y2 c d := rec_y2 hrec1
  have hx1 : ∀ d, x1 c1 d = x1 c d := rec_x1 hrec1
  have hGd : ∀ d, L8.Gd Sm univ c1 d = L8.Gd Sm univ c d := by
    intro d
    have := hrec1.card_filter (fun T => Sm ⊆ T ∧ #T = d) (fun T T' hc h => by
      have hS : ∀ z ∈ Sm, z ∉ univ \ Sm := fun z hz h' => (mem_sdiff.1 h').2 hz
      constructor
      · rintro ⟨a1, a2⟩; exact ⟨fun z hz => (h z (hS z hz)).1 (a1 hz), hc ▸ a2⟩
      · rintro ⟨a1, a2⟩; exact ⟨fun z hz => (h z (hS z hz)).2 (a1 hz), hc ▸ a2⟩) 1
    unfold L8.Gd
    convert this using 3 <;> simp only [subset_univ, true_and] <;> tauto
  obtain ⟨c2, hinv, hfin⟩ := stage_engine hγ hopt1 hn21 hall1 (fun d hy1 hout => by
    rw [hy2] at hy1 ⊢
    by_cases hd4 : d ≤ 4
    · obtain ⟨h3, hx0, hy1'⟩ := hsmall d hy1 hd4
      left
      have := g1_le_x1 (Sm := Sm) (γ := γ) c1 d
      rw [hx1, hx0] at this
      omega
    by_cases hdk : k < d
    · rw [y2_zero_of_gt c hdk] at hy1; omega
    by_cases hdk' : d = k
    · subst hdk'; rw [card_out_top hγ] at hout; omega
    by_cases hdk1 : d = k - 1
    · subst hdk1
      left
      rw [card_out_km1 hγ (by omega)] at hout
      have hh0 : h1 Sm γ c1 (k - 1) = 0 := by omega
      have := hb2
      rw [g1_eq_g] at *
      have hG := Gd_eq (Sm := Sm) (γ := γ) c1 (k - 1)
      rw [hGd, hh0, add_zero, g1_eq_g] at hG
      rw [hG] at this
      have hg0 : L8.g Sm univ c1 γ (k - 1) = 0 := by
        by_contra hne
        have hpos : 0 < L8.g Sm univ c1 γ (k - 1) := Nat.pos_of_ne_zero hne
        have : (k - #Sm) * L8.g Sm univ c1 γ (k - 1) > (k - 1 - #Sm) * L8.g Sm univ c1 γ (k - 1) :=
          Nat.mul_lt_mul_of_pos_right (by omega) hpos
        omega
      rw [hg0]
      have := hkm1 (by omega)
      omega
    · right
      refine ⟨by omega, ?_⟩
      have := hgen d (by omega) (by omega) hy1 (g1 Sm γ c1 d) (by rw [g1_eq_g]; exact hb1 d)
      exact this)
  refine ⟨c2, hrec1.trans hinv.1, rec_cnt_le hinv.1 hn21, hfin, fun d => ?_⟩
  rw [hinv.2.1 d, g1_eq_g]
  exact hb1 d
end Bkls.L9

end LeanPool.BalancedEdgeColourings
