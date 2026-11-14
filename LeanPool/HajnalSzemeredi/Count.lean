/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.HajnalSzemeredi.CountDefinitions
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting inequalities for equitable recolouring

Split from the upstream counting module to let the structural lemmas build independently.
-/

@[expose] public section

noncomputable section

open Finset

namespace HajnalSzemeredi

variable {V : Type*} {G : SimpleGraph V}

namespace CountHyp

variable {S : Finset V} {c : V → ℕ} {PA PB TU : Finset ℕ} {r s : ℕ}

open Classical in
private theorem mem_part' {Q : Finset ℕ} {v : V} : v ∈ part S c Q ↔ v ∈ S ∧ c v ∈ Q := by
  simp [part]

open Classical in
private theorem card_nbr_split (h : CountHyp G S c PA PB TU r s) (v : V) :
    (nbr G S v).card = (nbr G (part S c PA) v).card + (nbr G (part S c PB) v).card := by
  rw [← card_union_of_disjoint]
  · congr 1
    ext w
    simp only [mem_union, mem_nbr, mem_part']
    constructor
    · rintro ⟨hw, ha⟩
      rcases mem_union.1 (h.cover w hw) with h1 | h1
      · exact Or.inl ⟨⟨hw, h1⟩, ha⟩
      · exact Or.inr ⟨⟨hw, h1⟩, ha⟩
    · rintro (⟨⟨hw, _⟩, ha⟩ | ⟨⟨hw, _⟩, ha⟩) <;> exact ⟨hw, ha⟩
  · rw [disjoint_left]
    intro w h1 h2
    simp only [mem_nbr, mem_part'] at h1 h2
    exact disjoint_left.1 h.disj h1.1.2 h2.1.2

open Classical in
private theorem card_nbr_part (v : V) (Q : Finset ℕ) :
    (nbr G (part S c Q) v).card = ∑ X ∈ Q, (nIn G S c v X).card := by
  rw [← card_biUnion]
  · congr 1
    ext w
    simp only [mem_nbr, mem_part', mem_biUnion, nIn, mem_inter, mem_cls]
    constructor
    · rintro ⟨⟨hw, hc⟩, ha⟩
      exact ⟨c w, hc, ⟨hw, ha⟩, hw, rfl⟩
    · rintro ⟨X, hX, ⟨hw, ha⟩, _, rfl⟩
      exact ⟨⟨hw, hX⟩, ha⟩
  · intro i _ j _ hij
    exact (cls_disjoint hij).mono inter_subset_right inter_subset_right

open Classical in
private theorem card_le_nbr_part {v : V} {Q : Finset ℕ} (hQ : Q ⊆ PA)
    (hne : ∀ X ∈ Q, (nIn G S c v X).Nonempty) : Q.card ≤ (nbr G (part S c PA) v).card := by
  rw [card_nbr_part]
  calc Q.card = ∑ X ∈ Q, 1 := by simp
    _ ≤ ∑ X ∈ Q, (nIn G S c v X).card := sum_le_sum fun X hX => (hne X hX).card_pos
    _ ≤ _ := sum_le_sum_of_subset hQ

open Classical in
private theorem two_le_nIn_add (h : CountHyp G S c PA PB TU r s) {y : V}
    (hy : y ∈ part S c PB) {W : ℕ} (hW : W ∈ TU) :
    2 ≤ (nIn G S c y W).card +
      ((cls S c W).filter fun z => IsSolo G S c TU (part S c PB) z y).card := by
  have hpos := (h.h21 y hy W (h.sub hW)).card_pos
  by_cases h2 : 2 ≤ (nIn G S c y W).card
  · omega
  · have h1 : (nIn G S c y W).card = 1 := by omega
    obtain ⟨a, ha⟩ := card_eq_one.1 h1
    have haW : a ∈ cls S c W := by
      have : a ∈ nIn G S c y W := by rw [ha]; exact mem_singleton_self a
      exact (mem_inter.1 this).2
    rw [mem_cls] at haW
    have : 0 < ((cls S c W).filter fun z => IsSolo G S c TU (part S c PB) z y).card := by
      refine card_pos.2 ⟨a, mem_filter.2 ⟨mem_cls.2 haW, haW.1, haW.2 ▸ hW, hy, ?_⟩⟩
      rw [haW.2]; exact ha
    omega

open Classical in
private theorem nIn_eq_filter (y : V) (W : ℕ) :
    nIn G S c y W = (cls S c W).filter fun z => G.Adj y z := by
  ext z
  simp only [nIn, mem_inter, mem_nbr, mem_filter, mem_cls]
  tauto

open Classical in
/-- Desigualdad (2.3): `|S^y| ≥ t - q + 1 + d_B(y)`. -/
theorem card_Sy (h : CountHyp G S c PA PB TU r s) {y : V} (hy : y ∈ part S c PB) :
    TU.card + 1 + (nbr G (part S c PB) y).card ≤
      (Sy G S c TU (part S c PB) y).card + PB.card := by
  have hsum : ∑ X ∈ TU, ((cls S c X).filter fun z => IsSolo G S c TU (part S c PB) z y).card ≤
      (Sy G S c TU (part S c PB) y).card := by
    rw [← card_biUnion]
    · apply card_le_card
      intro z hz
      simp only [mem_biUnion, mem_filter, mem_cls] at hz
      obtain ⟨X, _, ⟨hzS, _⟩, hs⟩ := hz
      exact mem_filter.2 ⟨hzS, hs⟩
    · intro i _ j _ hij
      exact (cls_disjoint hij).mono (filter_subset _ _) (filter_subset _ _)
  have hTU : ∑ X ∈ TU, 2 ≤ ∑ X ∈ TU, ((nIn G S c y X).card +
      ((cls S c X).filter fun z => IsSolo G S c TU (part S c PB) z y).card) :=
    sum_le_sum fun X hX => h.two_le_nIn_add hy hX
  rw [sum_add_distrib, sum_const, smul_eq_mul] at hTU
  have hrest : (PA \ TU).card ≤ ∑ X ∈ PA \ TU, (nIn G S c y X).card := by
    calc (PA \ TU).card = ∑ X ∈ PA \ TU, 1 := by simp
      _ ≤ _ := sum_le_sum fun X hX => (h.h21 y hy X (mem_sdiff.1 hX).1).card_pos
  have hA := card_nbr_part (G := G) (S := S) (c := c) y PA
  rw [← sum_sdiff h.sub] at hA
  have hc := card_sdiff_add_card_eq_card h.sub
  have h1 := h.card_nbr_split y
  have h3 := h.deg y (mem_part'.1 hy).1
  have := h.card_r
  omega

open Classical in
/-- (2.1), forma de grado: `d_B(y) ≤ q - 1` para `y ∈ B`. -/
theorem deg_B (h : CountHyp G S c PA PB TU r s) {y : V} (hy : y ∈ part S c PB) :
    (nbr G (part S c PB) y).card + 1 ≤ PB.card := by
  have h1 := h.card_nbr_split y
  have h2 := card_le_nbr_part (G := G) (S := S) (c := c) (v := y) (subset_refl PA) (h.h21 y hy)
  have h3 := h.deg y (mem_part'.1 hy).1
  have := h.card_r
  omega

open Classical in
/-- **Lema 2.2.** Si ningún vértice solo de `W ∈ TU` es movible a otra clase de `PA`, entonces
`q + 1 ≤ t` y todo `y ∈ B` es solo. -/
theorem lemma_2_2 (h : CountHyp G S c PA PB TU r s) {W : ℕ} (hW : W ∈ TU)
    (hW' : ∀ z ∈ cls S c W, (Sz G S c TU (part S c PB) z).Nonempty →
      ∀ X ∈ PA, X ≠ W → ¬ Movable G S c z X) :
    PB.card + 1 ≤ TU.card ∧ ∀ y ∈ part S c PB, (Sy G S c TU (part S c PB) y).Nonempty := by
  have hq : PB.card + 1 ≤ TU.card := by
    by_contra hlt
    have hz : ∀ z ∈ cls S c W, (Sz G S c TU (part S c PB) z).card +
        (nbr G (part S c PB) z).card ≤ 2 * PB.card := by
      intro z hz
      have hzS := (mem_cls.1 hz).1
      have hzc := (mem_cls.1 hz).2
      have h1 := h.card_nbr_split z
      have h3 := h.deg z hzS
      have := h.card_r
      by_cases hne : (Sz G S c TU (part S c PB) z).Nonempty
      · have hA : (PA.erase W).card ≤ (nbr G (part S c PA) z).card := by
          apply card_le_nbr_part (erase_subset _ _)
          intro X hX
          obtain ⟨hXW, hXP⟩ := mem_erase.1 hX
          have hm := hW' z hz hne X hXP hXW
          simp only [Movable, not_forall, not_not] at hm
          obtain ⟨w, hw, hadj⟩ := hm
          exact ⟨w, mem_inter.2 ⟨mem_nbr.2 ⟨(mem_cls.1 hw).1, hadj⟩, hw⟩⟩
        have hsub : Sz G S c TU (part S c PB) z ⊆ nbr G (part S c PB) z := by
          intro y hy
          obtain ⟨hyB, hs⟩ := mem_filter.1 hy
          have : z ∈ nIn G S c y (c z) := by rw [hs.2.2.2]; exact mem_singleton_self z
          exact mem_nbr.2 ⟨hyB, ((mem_nbr.1 (mem_inter.1 this).1).2).symm⟩
        have := card_le_card hsub
        have := card_erase_of_mem (h.sub hW)
        have := card_pos.2 ⟨W, h.sub hW⟩
        omega
      · rw [not_nonempty_iff_eq_empty.1 hne, card_empty]
        have := h.h22 z hzS (hzc ▸ hW)
        omega
    have hupper := sum_le_sum hz
    rw [sum_const, smul_eq_mul, h.size W hW, sum_add_distrib] at hupper
    have hlow : ∑ y ∈ part S c PB, 2 ≤ ∑ y ∈ part S c PB, ((nIn G S c y W).card +
        ((cls S c W).filter fun z => IsSolo G S c TU (part S c PB) z y).card) :=
      sum_le_sum fun y hy => h.two_le_nIn_add hy hW
    rw [sum_const, smul_eq_mul, h.card_B, sum_add_distrib] at hlow
    have e1 : ∑ z ∈ cls S c W, (nbr G (part S c PB) z).card =
        ∑ y ∈ part S c PB, (nIn G S c y W).card := by
      simp only [nIn_eq_filter, nbr, card_filter]
      rw [sum_comm]
      refine sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
      simp only [G.adj_comm]
    have e2 : ∑ z ∈ cls S c W, (Sz G S c TU (part S c PB) z).card =
        ∑ y ∈ part S c PB,
          ((cls S c W).filter fun z => IsSolo G S c TU (part S c PB) z y).card := by
      simp only [Sz, card_filter]
      rw [sum_comm]
    rw [e1, e2] at hupper
    rw [Nat.mul_left_comm s 2 PB.card, Nat.mul_comm s PB.card] at hupper
    omega
  refine ⟨hq, fun y hy => ?_⟩
  have := h.card_Sy hy
  exact card_pos.1 (by omega)

open Classical in
/-- **Lema 2.3.** Existe un vértice solo `z` (con color en `TU`) que es movible a otra clase de
`PA`, o que tiene dos vecinos especiales distintos no adyacentes. -/
theorem lemma_2_3 (h : CountHyp G S c PA PB TU r s) :
    ∃ z ∈ S, c z ∈ TU ∧ (Sz G S c TU (part S c PB) z).Nonempty ∧
      ((∃ X ∈ PA, X ≠ c z ∧ Movable G S c z X) ∨
        ∃ y₁ ∈ Sz G S c TU (part S c PB) z, ∃ y₂ ∈ Sz G S c TU (part S c PB) z,
          y₁ ≠ y₂ ∧ ¬ G.Adj y₁ y₂) := by
  by_contra hcon
  have hnm : ∀ z ∈ S, c z ∈ TU → (Sz G S c TU (part S c PB) z).Nonempty →
      ∀ X ∈ PA, X ≠ c z → ¬ Movable G S c z X :=
    fun z hz hc hne X hX hXz hm => hcon ⟨z, hz, hc, hne, Or.inl ⟨X, hX, hXz, hm⟩⟩
  have hcl : ∀ z ∈ S, c z ∈ TU → ∀ y₁ ∈ Sz G S c TU (part S c PB) z,
      ∀ y₂ ∈ Sz G S c TU (part S c PB) z, y₁ ≠ y₂ → G.Adj y₁ y₂ :=
    fun z hz hc y₁ h₁ y₂ h₂ hne =>
      by_contra fun ha => hcon ⟨z, hz, hc, ⟨y₁, h₁⟩, Or.inr ⟨y₁, h₁, y₂, h₂, hne, ha⟩⟩
  obtain ⟨W, hW⟩ := h.ne
  obtain ⟨hq, -⟩ := h.lemma_2_2 hW fun z hz hne X hX hXW =>
    hnm z (mem_cls.1 hz).1 ((mem_cls.1 hz).2 ▸ hW) hne X hX (by rw [(mem_cls.1 hz).2]; exact hXW)
  have hswap : ∑ y ∈ part S c PB, ∑ z ∈ Sy G S c TU (part S c PB) y,
      ((PB.card : ℚ) / (Sz G S c TU (part S c PB) z).card) =
      ∑ z ∈ S.filter (fun z => c z ∈ TU), ∑ y ∈ Sz G S c TU (part S c PB) z,
        ((PB.card : ℚ) / (Sz G S c TU (part S c PB) z).card) := by
    apply sum_comm'
    intro y z
    simp only [Sy, Sz, mem_filter]
    constructor
    · rintro ⟨hy, hzS, hs⟩
      exact ⟨⟨hy, hs⟩, hzS, hs.2.1⟩
    · rintro ⟨⟨hy, hs⟩, hzS, _⟩
      exact ⟨hy, hzS, hs⟩
  have hup : ∑ z ∈ S.filter (fun z => c z ∈ TU), ∑ y ∈ Sz G S c TU (part S c PB) z,
      ((PB.card : ℚ) / (Sz G S c TU (part S c PB) z).card) ≤
      ∑ z ∈ S.filter (fun z => c z ∈ TU), (PB.card : ℚ) := by
    apply sum_le_sum
    intro z _
    rw [sum_const, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos (Sz G S c TU (part S c PB) z).card with h0 | h0
    · rw [h0]; simp
    · apply le_of_eq
      have : ((Sz G S c TU (part S c PB) z).card : ℚ) ≠ 0 := by positivity
      field_simp
  have hA' : (S.filter fun z => c z ∈ TU).card = TU.card * s := by
    rw [card_eq_sum_card_fiberwise (f := c) (s := S.filter fun z => c z ∈ TU) (t := TU)
      (fun z hz => (mem_filter.1 hz).2)]
    rw [sum_congr rfl (g := fun _ => s)]
    · simp
    intro X hX
    rw [← h.size X hX]
    congr 1
    ext z
    simp only [mem_filter, mem_cls]
    constructor
    · rintro ⟨⟨a, _⟩, b⟩; exact ⟨a, b⟩
    · rintro ⟨a, b⟩; exact ⟨⟨a, b ▸ hX⟩, b⟩
  have hlo : ∀ y ∈ part S c PB, (TU.card : ℚ) ≤ ∑ z ∈ Sy G S c TU (part S c PB) y,
      ((PB.card : ℚ) / (Sz G S c TU (part S c PB) z).card) := by
    intro y hy
    have hSy := h.card_Sy hy
    have hdB := h.deg_B hy
    have hle : ∀ z ∈ Sy G S c TU (part S c PB) y, (Sz G S c TU (part S c PB) z).card ≤
        (nbr G (part S c PB) y).card + 1 ∧ 0 < (Sz G S c TU (part S c PB) z).card := by
      intro z hz
      obtain ⟨hzS, hs⟩ := mem_filter.1 hz
      have hyz : y ∈ Sz G S c TU (part S c PB) z := mem_filter.2 ⟨hy, hs⟩
      refine ⟨?_, card_pos.2 ⟨y, hyz⟩⟩
      have hsub : Sz G S c TU (part S c PB) z ⊆ insert y (nbr G (part S c PB) y) := by
        intro y' hy'
        by_cases e : y' = y
        · rw [e]; exact mem_insert_self _ _
        · exact mem_insert_of_mem (mem_nbr.2 ⟨(mem_filter.1 hy').1,
            hcl z hzS hs.2.1 y hyz y' hy' (Ne.symm e)⟩)
      exact (card_le_card hsub).trans (card_insert_le _ _)
    have hSyq : (TU.card : ℚ) + 1 + (nbr G (part S c PB) y).card ≤
        (Sy G S c TU (part S c PB) y).card + PB.card := by exact_mod_cast hSy
    have hdBq : ((nbr G (part S c PB) y).card : ℚ) + 1 ≤ PB.card := by exact_mod_cast hdB
    have hqq : (PB.card : ℚ) + 1 ≤ TU.card := by exact_mod_cast hq
    calc (TU.card : ℚ) ≤ (Sy G S c TU (part S c PB) y).card *
          ((PB.card : ℚ) / ((nbr G (part S c PB) y).card + 1)) := by
          rw [mul_div_assoc', le_div_iff₀ (by positivity)]
          nlinarith [mul_nonneg (show (0:ℚ) ≤ TU.card - PB.card by linarith)
            (show (0:ℚ) ≤ PB.card - ((nbr G (part S c PB) y).card + 1) by linarith),
            mul_le_mul_of_nonneg_right hSyq (Nat.cast_nonneg (α := ℚ) PB.card)]
      _ = ∑ z ∈ Sy G S c TU (part S c PB) y,
          ((PB.card : ℚ) / ((nbr G (part S c PB) y).card + 1)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum fun z hz => div_le_div_of_nonneg_left (by positivity)
          (by exact_mod_cast (hle z hz).2) (by exact_mod_cast (hle z hz).1)
  have hL : (TU.card : ℚ) * (part S c PB).card ≤ ∑ y ∈ part S c PB,
      ∑ z ∈ Sy G S c TU (part S c PB) y,
        ((PB.card : ℚ) / (Sz G S c TU (part S c PB) z).card) := by
    calc
      _ = ∑ y ∈ part S c PB, (TU.card : ℚ) := by
        rw [sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ _ := sum_le_sum hlo
  rw [hswap] at hL
  have key := hL.trans hup
  rw [sum_const, nsmul_eq_mul, hA', h.card_B] at key
  push_cast at key
  have : (1 : ℚ) ≤ TU.card := by exact_mod_cast (show 1 ≤ TU.card by omega)
  nlinarith only [key, this]

end CountHyp

end HajnalSzemeredi
