/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.L9c
public import LeanPool.BalancedEdgeColourings.Bkls.L9d
public import Mathlib.Tactic.LinearCombination

/-!
# Balister–Kostochka–Li–Schelp 2004, Lemma 9 (part 2)

`lemma9`: if `G` has maximum degree at most `k`, a proper `k`-edge-colouring, and the numbers
`n_d` of vertices of degree `d` satisfy `n_0, n_1, n_2 ≤ 1`, `n_3, n_4, n_k ≤ 2`, `n_{k-1} ≤ k + 1`
and, for `5 ≤ d ≤ k - 2`, `n_d ≤ (d-4)/(d-3) · min(2 C(k-3, d-3), C(k, d)) - 2`, then for any three
colours `a, b, e` some optimal `k`-colouring uses every colour set at most twice and every
colour set
used twice contains `a, b, e`.

Three stages (`L9.stage`) with `S₋ = ∅, {a}, {a, b}`; the room comes from `roomA`, `roomB`,
`roomC` with the 1-pile bounds passed from stage to stage.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.L9

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull Balanced Bkls


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}

variable (G) in
open Classical in
/-- The number of vertices of degree `d`. -/
noncomputable def nd (d : ℕ) : ℕ := #(univ.filter fun v => G.degree v = d)

open Classical in
omit [DecidableEq V] in
theorem card_colSet {c : PEC G (Fin k)} (htot : Total c) (v : V) : #(colSet c v) = G.degree v := by
  classical
  rw [← card_neighborFinset_eq_degree]
  symm
  refine card_bij (fun w hw => (c.col v w).get (Option.isSome_iff_ne_none.2
    (htot v w ((mem_neighborFinset _ _ _).1 hw)))) (fun w hw => ?_) (fun w hw w' hw' h => ?_)
    (fun θ hθ => ?_)
  · rw [mem_colSet]
    intro hf
    exact hf w (Option.some_get _).symm
  · have e1 := (Option.some_get (Option.isSome_iff_ne_none.2
      (htot v w ((mem_neighborFinset _ _ _).1 hw)))).symm
    have e2 := (Option.some_get (Option.isSome_iff_ne_none.2
      (htot v w' ((mem_neighborFinset _ _ _).1 hw')))).symm
    rw [h] at e1
    exact c.col_proper e1 e2
  · rw [mem_colSet] at hθ
    simp only [IsFree, not_forall, not_not] at hθ
    obtain ⟨w, hw⟩ := hθ
    refine ⟨w, (mem_neighborFinset _ _ _).2 (c.col_adj hw), ?_⟩
    apply Option.some_injective
    rw [Option.some_get, hw]

open Classical in
omit [DecidableEq V] in
theorem nd_eq {c : PEC G (Fin k)} (htot : Total c) (d : ℕ) :
    nd G d = ∑ T ∈ univ.filter (fun T : Finset (Fin k) => #T = d), cnt c T := by
  classical
  unfold nd
  rw [card_eq_sum_card_fiberwise (f := colSet c) (t := univ.filter fun T : Finset (Fin k) => #T = d)
    (fun v hv => by
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
      rw [card_colSet htot, hv])]
  apply sum_congr rfl
  intro T hT
  unfold cnt
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    rw [← card_colSet htot, h]
    exact (mem_filter.1 hT).2

open Classical in
omit [DecidableEq V] in
theorem nd_x1_y2 {c : PEC G (Fin k)} (htot : Total c) (hn2 : ∀ T, cnt c T ≤ 2) (d : ℕ) :
    nd G d = x1 c d + 2 * y2 c d := by
  classical
  rw [nd_eq htot, x1, y2]
  rw [card_eq_sum_ones, card_eq_sum_ones, mul_sum, sum_filter, sum_filter, sum_filter, ←
      sum_add_distrib]
  apply sum_congr rfl
  intro T _
  have := hn2 T
  by_cases hT : #T = d
  · rcases (show cnt c T = 0 ∨ cnt c T = 1 ∨ cnt c T = 2 by omega) with h | h | h <;> simp [hT, h]
  · simp [hT]

open Classical in
omit [DecidableEq V] in
/-- **At most two vertices per colour set.** -/
theorem cnt_le_two {c : PEC G (Fin k)} (hopt : IsOptimal c)
    (hnd : ∀ d, nd G d ≤ k.choose d + 1) (T : Finset (Fin k)) : cnt c T ≤ 2 := by
  classical
  by_contra h
  push Not at h
  set d := #T
  have hall : ∀ T' : Finset (Fin k), #T' = d → 1 ≤ cnt c T' := by
    intro T' hT'
    have := theorem1 c hopt (P := T) (Q := T') hT'.symm
    omega
  have hsum := nd_eq (G := G) hopt.1 d
  have hT : T ∈ univ.filter (fun T : Finset (Fin k) => #T = d) := mem_filter.2 ⟨mem_univ _, rfl⟩
  rw [← sum_erase_add _ _ hT] at hsum
  have h1 : ∑ T' ∈ (univ.filter fun T : Finset (Fin k) => #T = d).erase T, cnt c T' ≥
      #((univ.filter fun T : Finset (Fin k) => #T = d).erase T) := by
    rw [card_eq_sum_ones]
    exact sum_le_sum fun T' hT' => hall T' (mem_filter.1 (mem_of_mem_erase hT')).2
  rw [card_erase_of_mem hT] at h1
  have h2 : #(univ.filter fun T : Finset (Fin k) => #T = d) = k.choose d := by
    rw [show (univ.filter fun T : Finset (Fin k) => #T = d) = powersetCard d univ by
      ext T'; simp [mem_powersetCard], card_powersetCard, card_univ, Fintype.card_fin]
  rw [h2] at h1
  have := hnd d
  have : 1 ≤ k.choose d := Nat.choose_pos (by
    have := card_le_univ T; rw [Fintype.card_fin] at this; exact this)
  omega
open Classical in
theorem room_of {m C g y : ℚ} (hm : 0 < m) (h : g + y ≤ (m - 1) / m * C + 2) :
    C / m - 1 ≤ C - g - (y - 1) := by
  have : (m - 1) / m * C = C - C / m := by field_simp
  linarith

open Classical in
omit [DecidableEq V] in
private theorem degree_counts_le_choose (hΔ : ∀ v, G.degree v ≤ k)
    (h012 : ∀ d, d ≤ 2 → nd G d ≤ 1) (h3 : nd G 3 ≤ 2) (h4 : nd G 4 ≤ 2)
    (hkk : nd G k ≤ 2) (hk1 : nd G (k - 1) ≤ k + 1)
    (h6 : ∀ d, 5 ≤ d → d + 2 ≤ k → (nd G d : ℚ) ≤
      ((d : ℚ) - 4) / ((d : ℚ) - 3) *
        min (2 * (((k - 3).choose (d - 3) : ℕ) : ℚ)) ((k.choose d : ℕ) : ℚ) - 2) :
    ∀ d, nd G d ≤ k.choose d + 1 := by
  classical
  have hnd0 : ∀ d, k < d → nd G d = 0 := by
    intro d hd
    unfold nd
    rw [card_eq_zero, filter_eq_empty_iff]
    intro v _ hv
    have := hΔ v
    omega
  intro d
  by_cases hdk : k < d
  · rw [hnd0 d hdk]; omega
  push Not at hdk
  have hpos : 1 ≤ k.choose d := Nat.choose_pos hdk
  by_cases hd2 : d ≤ 2
  · have := h012 d hd2; omega
  by_cases hd3 : d = 3
  · subst hd3; omega
  by_cases hd4 : d = 4
  · subst hd4; omega
  by_cases hdk' : d = k
  · subst hdk'; rw [Nat.choose_self]; omega
  by_cases hdk1 : d = k - 1
  · subst hdk1
    rw [Nat.choose_symm (by omega), Nat.choose_one_right]; omega
  have h := h6 d (by omega) (by omega)
  have hm : min (2 * (((k - 3).choose (d - 3) : ℕ) : ℚ)) ((k.choose d : ℕ) : ℚ) ≤ k.choose d :=
    min_le_right _ _
  have hr : ((d : ℚ) - 4) / ((d : ℚ) - 3) ≤ 1 := by
    have : (5 : ℚ) ≤ d := by exact_mod_cast (show 5 ≤ d by omega)
    rw [div_le_one (by linarith)]; linarith
  have hr0 : 0 ≤ ((d : ℚ) - 4) / ((d : ℚ) - 3) := by
    have : (5 : ℚ) ≤ d := by exact_mod_cast (show 5 ≤ d by omega)
    apply div_nonneg <;> linarith
  have hm0 : 0 ≤ min (2 * (((k - 3).choose (d - 3) : ℕ) : ℚ)) ((k.choose d : ℕ) : ℚ) :=
    le_min (by positivity) (by positivity)
  have : (nd G d : ℚ) ≤ k.choose d := by nlinarith [mul_nonneg (sub_nonneg.2 hr) hm0]
  have : nd G d ≤ k.choose d := by exact_mod_cast this
  omega

open Classical in
omit [DecidableEq V] in
/-- **Lemma 9 (part 2).** -/
theorem lemma9 (hk3 : 3 ≤ k) (hΔ : ∀ v, G.degree v ≤ k) {c0 : PEC G (Fin k)} (htot : Total c0)
    {a b e : Fin k} (hab : a ≠ b) (hae : a ≠ e) (hbe : b ≠ e)
    (h012 : ∀ d, d ≤ 2 → nd G d ≤ 1) (h3 : nd G 3 ≤ 2) (h4 : nd G 4 ≤ 2) (hkk : nd G k ≤ 2)
    (hk1 : nd G (k - 1) ≤ k + 1)
    (h6 : ∀ d, 5 ≤ d → d + 2 ≤ k → (nd G d : ℚ) ≤
      ((d : ℚ) - 4) / ((d : ℚ) - 3) * min (2 * (((k - 3).choose (d - 3) : ℕ) : ℚ)) ((k.choose
          d : ℕ) : ℚ) - 2) :
    ∃ c : PEC G (Fin k), IsOptimal c ∧ (∀ T, cnt c T ≤ 2) ∧
      ∀ T, cnt c T = 2 → a ∈ T ∧ b ∈ T ∧ e ∈ T := by
  classical
  -- an optimal colouring
  obtain ⟨c, hct, hcmin⟩ := L8.exists_min_nat (fun c : PEC G (Fin k) => Total c) (fun c => cost c)
    ⟨c0, htot⟩
  have hopt : IsOptimal c := ⟨hct, fun c' h => hcmin c' h⟩
  -- the degree counts
  have hnd := degree_counts_le_choose hΔ h012 h3 h4 hkk hk1 h6
  have hn2 : ∀ (c' : PEC G (Fin k)), IsOptimal c' → ∀ T, cnt c' T ≤ 2 :=
    fun c' h => cnt_le_two h hnd
  -- the facts used at every stage, for any optimal colouring
  have hsmall : ∀ c' : PEC G (Fin k), IsOptimal c' → ∀ d, 1 ≤ y2 c' d → d ≤ 4 →
      3 ≤ d ∧ x1 c' d = 0 ∧ y2 c' d = 1 := by
    intro c' h' d hy hd
    have hn := nd_x1_y2 h'.1 (hn2 c' h') d (G := G)
    by_cases hd2 : d ≤ 2
    · have := h012 d hd2; omega
    have : nd G d ≤ 2 := by
      rcases (show d = 3 ∨ d = 4 by omega) with rfl | rfl
      · exact h3
      · exact h4
    omega
  have hkm1 : ∀ c' : PEC G (Fin k), IsOptimal c' → ∀ s : ℕ, s ≤ 2 → 5 ≤ k - 1 →
      y2 c' (k - 1) + s + 1 ≤ k := by
    intro c' h' s hs hk5
    have hn := nd_x1_y2 h'.1 (hn2 c' h') (k - 1) (G := G)
    omega
  -- the hypothesis (6) in the form of `roomA`–`roomC`
  have h6' : ∀ c' : PEC G (Fin k), IsOptimal c' → ∀ d, 5 ≤ d → d + 2 ≤ k →
      2 * (y2 c' d : ℚ) + x1 c' d ≤ ((d : ℚ) - 4) / ((d : ℚ) - 3) *
        (2 * (((k - 3).choose (d - 3) : ℕ) : ℚ)) - 2 ∧
      2 * (y2 c' d : ℚ) + x1 c' d ≤ ((d : ℚ) - 4) / ((d : ℚ) - 3) * ((k.choose d : ℕ) : ℚ) - 2 := by
    intro c' h' d hd hdk
    have hn := nd_x1_y2 h'.1 (hn2 c' h') d (G := G)
    have h := h6 d hd hdk
    have hr0 : 0 ≤ ((d : ℚ) - 4) / ((d : ℚ) - 3) := by
      have : (5 : ℚ) ≤ d := by exact_mod_cast hd
      apply div_nonneg <;> linarith
    have hq : (nd G d : ℚ) = x1 c' d + 2 * y2 c' d := by exact_mod_cast hn
    constructor
    · have := mul_le_mul_of_nonneg_left (min_le_left (2 * (((k - 3).choose (d - 3) : ℕ) : ℚ))
        ((k.choose d : ℕ) : ℚ)) hr0
      linarith
    · have := mul_le_mul_of_nonneg_left (min_le_right (2 * (((k - 3).choose (d - 3) : ℕ) : ℚ))
        ((k.choose d : ℕ) : ℚ)) hr0
      linarith
  have hGd0 : ∀ c' : PEC G (Fin k), ∀ d, L8.Gd ∅ univ c' d = x1 c' d := by
    intro c' d
    unfold L8.Gd x1
    apply L8.cfilter_congr; intro T; simp
  -- stage A
  obtain ⟨cA, hrecA, hnA, hallA, hbA⟩ := stage (Sm := ∅) (γ := a) (notMem_empty a)
    (by simp) hopt (hn2 c hopt) (fun T _ => empty_subset T) (hsmall c hopt)
    (by simpa using hkm1 c hopt 0 (by omega))
    (fun d hd hdk hy g hg => by
      simp only [card_empty, Nat.sub_zero] at hg ⊢
      rw [hGd0] at hg
      obtain ⟨hnA', hnB'⟩ := h6' c hopt d hd hdk
      obtain ⟨e2, e1, e0⟩ := choose_rel (k := k) (d := d) (by omega) (by omega)
      have hK : (5 : ℚ) ≤ d := by exact_mod_cast hd
      have hDK : (d : ℚ) + 2 ≤ k := by exact_mod_cast hdk
      have hg' : (k : ℚ) * g ≤ d * x1 c d + k - 1 := by
        have : (k * g : ℕ) ≤ d * x1 c d + (k - 1) := hg
        have h' : ((k * g : ℕ) : ℚ) ≤ ((d * x1 c d + (k - 1) : ℕ) : ℚ) := by exact_mod_cast this
        push_cast [Nat.cast_sub (show 1 ≤ k by omega)] at h'; linarith
      have hr := roomA hK hDK (by positivity) (by positivity) (by positivity) e2 e1 e0 hnA' hnB'
        (chain1 (by linarith) hg')
      have hy' : ((y2 c d - 1 : ℕ) : ℚ) = (y2 c d : ℚ) - 1 := by rw [Nat.cast_sub hy]; simp
      rw [hy']
      apply room_of (by linarith)
      convert hr using 2
      ring)
  have hoptA := hrecA.opt
  -- stage B
  have hGd1 : ∀ c' : PEC G (Fin k), ∀ d, L8.Gd {a} univ c' d = g1 ∅ a c' d := by
    intro c' d
    unfold L8.Gd g1
    apply L8.cfilter_congr; intro T; simp only [singleton_subset_iff, subset_univ, true_and,
      empty_subset]; tauto
  have hx1A : ∀ d, x1 cA d = x1 c d := rec_x1 hrecA
  have hy2A : ∀ d, y2 cA d = y2 c d := rec_y2 hrecA
  obtain ⟨cB, hrecB, hnB, hallB, hbB⟩ := stage (Sm := {a}) (γ := b)
    (by simpa using Ne.symm hab) (by simp) hoptA hnA
    (fun T hT => singleton_subset_iff.2 (hallA T hT).2) (hsmall cA hoptA)
    (by simpa using hkm1 cA hoptA 1 (by omega))
    (fun d hd hdk hy g hg => by
      simp only [card_singleton] at hg ⊢
      rw [hGd1] at hg
      obtain ⟨hnA', hnB'⟩ := h6' cA hoptA d hd hdk
      obtain ⟨e2, e1, e0⟩ := choose_rel (k := k) (d := d) (by omega) (by omega)
      have hK : (5 : ℚ) ≤ d := by exact_mod_cast hd
      have hDK : (d : ℚ) + 2 ≤ k := by exact_mod_cast hdk
      have hgA := hbA d
      simp only [card_empty, Nat.sub_zero] at hgA
      rw [hGd0] at hgA
      have hg1 : (k : ℚ) * g1 ∅ a cA d ≤ d * x1 cA d + k - 1 := by
        have h' : ((k * g1 ∅ a cA d : ℕ) : ℚ) ≤ ((d * x1 c d + (k - 1) : ℕ) : ℚ) := by
          exact_mod_cast hgA
        rw [hx1A]
        push_cast [Nat.cast_sub (show 1 ≤ k by omega)] at h'; linarith
      have hg2 : ((k : ℚ) - 1) * g ≤ ((d : ℚ) - 1) * g1 ∅ a cA d + k - 2 := by
        have h' : (((k - 1) * g : ℕ) : ℚ) ≤ (((d - 1) * g1 ∅ a cA d + (k - 1 - 1) : ℕ) : ℚ) := by
          exact_mod_cast hg
        push_cast [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_sub (show 1 ≤ d by omega),
          Nat.cast_sub (show 1 ≤ k - 1 by omega)] at h'
        linarith
      have hc2 := chain2 (by linarith) (by linarith) (by positivity) (by linarith) hg1 hg2
      have hr := roomB hK hDK (by positivity) (by positivity) (by positivity) e2
        (by linear_combination ((d : ℚ) - 1) * e0 + (k : ℚ) * e1) hnA' hnB' hc2
      have hy' : ((y2 cA d - 1 : ℕ) : ℚ) = (y2 cA d : ℚ) - 1 := by rw [Nat.cast_sub hy]; simp
      rw [hy', Nat.cast_sub (show 1 ≤ d by omega), show k - 1 - 1 = k - 2 by omega,
        show d - 1 - 1 = d - 2 by omega]
      push_cast
      apply room_of (by linarith)
      convert hr using 2
      ring)
  have hoptB := hrecB.opt
  -- stage C
  have hGd2 : ∀ c' : PEC G (Fin k), ∀ d, L8.Gd {a, b} univ c' d = g1 {a} b c' d := by
    intro c' d
    unfold L8.Gd g1
    apply L8.cfilter_congr; intro T
    simp only [insert_subset_iff, singleton_subset_iff, subset_univ, true_and]; tauto
  have hx1B : ∀ d, x1 cB d = x1 c d := fun d => (rec_x1 hrecB d).trans (hx1A d)
  obtain ⟨cC, hrecC, hnC, hallC, -⟩ := stage (Sm := {a, b}) (γ := e)
    (by simp only [mem_insert, mem_singleton, not_or]; exact ⟨Ne.symm hae, Ne.symm hbe⟩)
    (by rw [card_pair hab]) hoptB hnB
    (fun T hT => by
      have := hallB T hT
      exact insert_subset (singleton_subset_iff.1 this.1) (singleton_subset_iff.2 this.2))
    (hsmall cB hoptB) (by rw [card_pair hab]; exact hkm1 cB hoptB 2 le_rfl)
    (fun d hd hdk hy g hg => by
      rw [card_pair hab] at hg ⊢
      rw [hGd2] at hg
      obtain ⟨hnA', hnB'⟩ := h6' cB hoptB d hd hdk
      obtain ⟨e2, e1, e0⟩ := choose_rel (k := k) (d := d) (by omega) (by omega)
      have hK : (5 : ℚ) ≤ d := by exact_mod_cast hd
      have hDK : (d : ℚ) + 2 ≤ k := by exact_mod_cast hdk
      have hgA := hbA d
      simp only [card_empty, Nat.sub_zero] at hgA
      rw [hGd0] at hgA
      have hgB := hbB d
      simp only [card_singleton] at hgB
      rw [hGd1] at hgB
      have hg1 : (k : ℚ) * g1 ∅ a cA d ≤ d * x1 cB d + k - 1 := by
        have h' : ((k * g1 ∅ a cA d : ℕ) : ℚ) ≤ ((d * x1 c d + (k - 1) : ℕ) : ℚ) := by
          exact_mod_cast hgA
        rw [hx1B]
        push_cast [Nat.cast_sub (show 1 ≤ k by omega)] at h'; linarith
      have hg2 : ((k : ℚ) - 1) * g1 {a} b cB d ≤ ((d : ℚ) - 1) * g1 ∅ a cA d + k - 2 := by
        have h' : (((k - 1) * g1 {a} b cB d : ℕ) : ℚ) ≤
            (((d - 1) * g1 ∅ a cA d + (k - 1 - 1) : ℕ) : ℚ) := by exact_mod_cast hgB
        push_cast [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_sub (show 1 ≤ d by omega),
          Nat.cast_sub (show 1 ≤ k - 1 by omega)] at h'
        linarith
      have hg3 : ((k : ℚ) - 2) * g ≤ ((d : ℚ) - 2) * g1 {a} b cB d + k - 3 := by
        have h' : (((k - 2) * g : ℕ) : ℚ) ≤ (((d - 2) * g1 {a} b cB d + (k - 2 - 1) : ℕ) : ℚ) := by
          exact_mod_cast hg
        push_cast [Nat.cast_sub (show 2 ≤ k by omega), Nat.cast_sub (show 2 ≤ d by omega),
          Nat.cast_sub (show 1 ≤ k - 2 by omega)] at h'
        linarith
      have hc2 := chain2 (by linarith) (by linarith) (by positivity) (by linarith) hg1 hg2
      have hc3 := chain3 (by linarith) (by linarith) (by positivity) (by linarith) hc2 hg3
      have hr := roomC hK hDK (by positivity) (by positivity) (by positivity)
        (by linear_combination ((d : ℚ) - 1) * ((d : ℚ) - 2) * e0 +
          (k : ℚ) * ((d : ℚ) - 2) * e1 + (k : ℚ) * ((k : ℚ) - 1) * e2) hnA' hnB' hc3
      have hy' : ((y2 cB d - 1 : ℕ) : ℚ) = (y2 cB d : ℚ) - 1 := by rw [Nat.cast_sub hy]; simp
      rw [hy', Nat.cast_sub (show 2 ≤ d by omega), show k - 2 - 1 = k - 3 by omega,
        show d - 2 - 1 = d - 3 by omega]
      push_cast
      apply room_of (by linarith)
      convert hr using 2
      ring)
  refine ⟨cC, hrecC.opt, hnC, fun T hT => ?_⟩
  obtain ⟨h1, h2⟩ := hallC T hT
  rw [insert_subset_iff, singleton_subset_iff] at h1
  exact ⟨h1.1, h1.2, h2⟩
end Bkls.L9

end LeanPool.BalancedEdgeColourings
