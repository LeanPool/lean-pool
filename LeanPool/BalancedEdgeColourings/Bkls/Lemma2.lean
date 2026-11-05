/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.Swap2

/-!
# Balister–Kostochka–Li–Schelp 2004, Lemma 2

For an optimal `k`-colouring (total, least `Σ_S n_S²`), colours `a, b` and `S' = i_ab S`:
* `lemma2_le`: `n_S ≤ n_{S'} + 2`;
* `lemma2_two`: if `n_S = n_{S'} + 2`, some optimal colouring has `n_S, n_{S'}` interchanged and all
  other counts unchanged;
* `lemma2_one`: if `n_S = n_{S'} + 1`, some optimal colouring has `n_S, n_{S'}` interchanged, and
  one other pair `n_U = n_{i_ab U} + 1` interchanged, all other counts unchanged.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull Balanced


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
variable {c : PEC G (Fin k)} {a b : Fin k}

open Classical in
/-- Exchange the values at `S` and `T`. -/
def swapAt (S T : Finset (Fin k)) (X : Finset (Fin k)) : Finset (Fin k) :=
  if X = S then T else if X = T then S else X

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem cost_eq_sum_cnt (c : PEC G (Fin k)) :
    (cost c : ℤ) = ∑ T : Finset (Fin k), ((cnt c T : ℤ)) ^ 2 := by
  classical
  unfold cost; push_cast; rfl
open Classical in
theorem sum_split {h : Finset (Fin k) → ℤ} {S T : Finset (Fin k)} (hST : S ≠ T) :
    ∑ X, h X ^ 2 = h S ^ 2 + h T ^ 2 + ∑ X ∈ (univ.erase S).erase T, h X ^ 2 := by
  rw [← sum_erase_add _ _ (mem_univ S), ← sum_erase_add _ _ (mem_erase.2 ⟨hST.symm, mem_univ T⟩)]
  ring

open Classical in
/-- Changing two counts by `∓ d`. -/
theorem sum_sq_update {f g : Finset (Fin k) → ℤ} {S T : Finset (Fin k)} (hST : S ≠ T) {d : ℤ}
    (hS : g S = f S - d) (hT : g T = f T + d) (hrest : ∀ X, X ≠ S → X ≠ T → g X = f X) :
    ∑ X, g X ^ 2 = ∑ X, f X ^ 2 + 2 * d * (f T - f S + d) := by
  rw [sum_split hST, sum_split (h := f) hST, sum_congr rfl fun X hX => by
    rw [hrest X (ne_of_mem_erase (mem_of_mem_erase hX)) (ne_of_mem_erase hX)], hS, hT]
  ring

open Classical in
/-- Changing four counts: `∓ 1` on two disjoint pairs. -/
theorem sum_sq_update4 {f g : Finset (Fin k) → ℤ} {S T S' T' : Finset (Fin k)}
    (h1 : S ≠ T) (h2 : S ≠ S') (h3 : S ≠ T') (h4 : T ≠ S') (h5 : T ≠ T') (h6 : S' ≠ T')
    (hS : g S = f S - 1) (hT : g T = f T + 1) (hS' : g S' = f S' - 1) (hT' : g T' = f T' + 1)
    (hrest : ∀ X, X ≠ S → X ≠ T → X ≠ S' → X ≠ T' → g X = f X) :
    ∑ X, g X ^ 2 = ∑ X, f X ^ 2 + 2 * (f T - f S + 1) + 2 * (f T' - f S' + 1) := by
  let h : Finset (Fin k) → ℤ := fun X => if X = S then f S - 1 else if X = T then f T + 1 else f X
  have hh1 := sum_sq_update (f := f) (g := h) (S := S) (T := T) h1 (d := 1)
    (by simp [h]) (by simp [h, h1.symm]) (fun X hX hX' => by simp [h, hX, hX'])
  have hh2 := sum_sq_update (f := h) (g := g) (S := S') (T := T') h6 (d := 1)
    (by simp [h, h2.symm, h4.symm, hS']) (by simp [h, h3.symm, h5.symm, hT'])
    (fun X hX hX' => by
      by_cases e1 : X = S
      · subst e1; simp [h, hS]
      by_cases e2 : X = T
      · subst e2; simp [h, h1.symm, hT]
      simp [h, e1, e2, hrest X e1 e2 hX hX'])
  have e1 : h S' = f S' := by simp [h, h2.symm, h4.symm]
  have e2 : h T' = f T' := by simp [h, h3.symm, h5.symm]
  rw [hh2, hh1, e1, e2]; ring

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The swap of Lemma 2, starting from a vertex of `V_S` of rank `n_{i S}`. -/
theorem lemma2_swap (hab : a ≠ b) (htot : Total c) {S : Finset (Fin k)}
    (hlt : cnt c (swapSet a b S) < cnt c S) :
    ∃ S' : Finset (Fin k), cnt c (swapSet a b S') < cnt c S' ∧ S' ≠ swapSet a b S ∧
      (S' = S → cnt c (swapSet a b S) + 2 ≤ cnt c S) ∧
      ∃ c' : PEC G (Fin k), Total c' ∧ ∀ T,
        cnt c' T + ind S T + ind S' T =
          cnt c T + ind (swapSet a b S) T + ind (swapSet a b S') T := by
  classical
  obtain ⟨u, hu, hur⟩ := exists_rank c hlt
  have hSne : swapSet a b S ≠ S := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
  have hue : IsEnd c a b u := by
    unfold IsEnd
    rw [hu]
    by_contra h
    apply hSne
    apply swapSet_eq_of_iff
    tauto
  have hm : ¬ JMatched c a b u := by unfold JMatched; rw [hur, hu]; exact lt_irrefl _
  obtain ⟨u', hne, hr, hue', hum, huniq⟩ := exists_unique_other_end hab hue hm
  obtain ⟨c', htot', hcnt⟩ := exists_swap hab htot hue hm hne hr hum huniq
  have hlt' : cnt c (swapSet a b (colSet c u')) < cnt c (colSet c u') := by
    have := rank_lt_cnt c u'
    unfold JMatched at hum
    omega
  refine ⟨colSet c u', hlt', fun h => ?_, fun h => ?_, c', htot', fun T => ?_⟩
  · rw [h, swapSet_swapSet] at hlt'
    exact lt_asymm hlt hlt'
  · have h1 := rank_lt_cnt c u'
    have h2 : rank c u' ≠ rank c u := fun e => hne (rank_injOn c (h.trans hu.symm) e)
    unfold JMatched at hum
    rw [h] at h1 hum
    omega
  · rw [← hu]; exact hcnt T

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem cnt_of_ind {c c' : PEC G (Fin k)} {S S' iS iS' : Finset (Fin k)}
    (h : ∀ T, cnt c' T + ind S T + ind S' T = cnt c T + ind iS T + ind iS' T) (T : Finset (Fin k)) :
    (cnt c' T : ℤ) = cnt c T + ind iS T + ind iS' T - ind S T - ind S' T := by
  classical
  have := h T; omega
open Classical in
theorem ind_self (S : Finset (Fin k)) : ind S S = 1 := by simp [ind]
open Classical in
theorem ind_ne {S T : Finset (Fin k)} (h : S ≠ T) : ind S T = 0 := by simp [ind, h]

open Classical in
/-- The four sets `S, i S, S', i S'` are distinct when `S' ∉ {S, i S}`. -/
theorem four_distinct {S S' : Finset (Fin k)} (_ : swapSet a b S ≠ S)
    (_ : S' ≠ swapSet a b S') (hS' : S' ≠ S) (hS'ne : S' ≠ swapSet a b S) :
    swapSet a b S' ≠ S ∧ swapSet a b S' ≠ swapSet a b S := by
  refine ⟨fun e => hS'ne (by rw [← e, swapSet_swapSet]), fun e => hS' ?_⟩
  have := congrArg (swapSet a b) e; rwa [swapSet_swapSet, swapSet_swapSet] at this

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The new counts after the swap, `S' = S`. -/
theorem counts_same {c c' : PEC G (Fin k)} {S : Finset (Fin k)} (hSne : swapSet a b S ≠ S)
    (h : ∀ T, cnt c' T + ind S T + ind S T =
      cnt c T + ind (swapSet a b S) T + ind (swapSet a b S) T) :
    (cnt c' S : ℤ) = cnt c S - 2 ∧ (cnt c' (swapSet a b S) : ℤ) = cnt c (swapSet a b S) + 2 ∧
      ∀ X, X ≠ S → X ≠ swapSet a b S → (cnt c' X : ℤ) = cnt c X := by
  classical
  refine ⟨?_, ?_, fun X h1 h2 => ?_⟩
  · have := cnt_of_ind h S; simp [ind, hSne] at this; linarith
  · have := cnt_of_ind h (swapSet a b S); simp [ind, Ne.symm hSne] at this; linarith
  · have := cnt_of_ind h X; simp [ind, Ne.symm h1, Ne.symm h2] at this; linarith

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The new counts after the swap, four distinct sets. -/
theorem counts_four {c c' : PEC G (Fin k)} {S S' : Finset (Fin k)} (hSne : swapSet a b S ≠ S)
    (h1 : S' ≠ swapSet a b S') (hS' : S' ≠ S) (hS'ne : S' ≠ swapSet a b S)
    (h : ∀ T, cnt c' T + ind S T + ind S' T =
      cnt c T + ind (swapSet a b S) T + ind (swapSet a b S') T) :
    (cnt c' S : ℤ) = cnt c S - 1 ∧ (cnt c' (swapSet a b S) : ℤ) = cnt c (swapSet a b S) + 1 ∧
      (cnt c' S' : ℤ) = cnt c S' - 1 ∧ (cnt c' (swapSet a b S') : ℤ) = cnt c (swapSet a b S') + 1 ∧
      ∀ X, X ≠ S → X ≠ swapSet a b S → X ≠ S' → X ≠ swapSet a b S' →
        (cnt c' X : ℤ) = cnt c X := by
  classical
  obtain ⟨h2, h3⟩ := four_distinct hSne h1 hS' hS'ne
  refine ⟨?_, ?_, ?_, ?_, fun X e1 e2 e3 e4 => ?_⟩
  · have := cnt_of_ind h S
    simp [ind, hSne, h2, hS'] at this; linarith
  · have := cnt_of_ind h (swapSet a b S)
    simp [ind, Ne.symm hSne, h3, hS'ne] at this; linarith
  · have := cnt_of_ind h S'
    simp [ind, Ne.symm hS', Ne.symm hS'ne, Ne.symm h1] at this; linarith
  · have := cnt_of_ind h (swapSet a b S')
    simp [ind, Ne.symm h3, Ne.symm h2, h1] at this; linarith
  · have := cnt_of_ind h X
    simp [ind, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4] at this; linarith

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem cost_le_of_opt (hopt : IsOptimal c) {c' : PEC G (Fin k)} (h : Total c') :
    ∑ X, ((cnt c X : ℤ)) ^ 2 ≤ ∑ X, ((cnt c' X : ℤ)) ^ 2 := by
  classical
  rw [← cost_eq_sum_cnt, ← cost_eq_sum_cnt]; exact_mod_cast hopt.2 c' h

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **Lemma 2, bound.** -/
theorem lemma2_le (hopt : IsOptimal c) (a b : Fin k) (S : Finset (Fin k)) :
    cnt c S ≤ cnt c (swapSet a b S) + 2 := by
  classical
  by_contra hgt
  push Not at hgt
  have hab : a ≠ b := by
    rintro rfl
    have : swapSet a a S = S := swapSet_eq_of_iff Iff.rfl
    rw [this] at hgt; omega
  have hSne : swapSet a b S ≠ S := fun h => by rw [h] at hgt; omega
  obtain ⟨S', hlt', hS'ne, -, c', htot', hcnt⟩ := lemma2_swap hab hopt.1 (S := S) (by omega)
  have hle := cost_le_of_opt hopt htot'
  by_cases hS' : S' = S
  · subst hS'
    obtain ⟨e1, e2, e3⟩ := counts_same hSne hcnt
    have := sum_sq_update (f := fun X => (cnt c X : ℤ)) (g := fun X => (cnt c' X : ℤ))
      (Ne.symm hSne) (d := 2) e1 e2 e3
    have : (cnt c (swapSet a b S') : ℤ) + 3 ≤ cnt c S' := by exact_mod_cast hgt
    nlinarith
  · have h1 : S' ≠ swapSet a b S' := fun e => by rw [← e] at hlt'; exact lt_irrefl _ hlt'
    obtain ⟨h2, h3⟩ := four_distinct hSne h1 hS' hS'ne
    obtain ⟨e1, e2, e3, e4, e5⟩ := counts_four hSne h1 hS' hS'ne hcnt
    have := sum_sq_update4 (f := fun X => (cnt c X : ℤ)) (g := fun X => (cnt c' X : ℤ))
      (Ne.symm hSne) (Ne.symm hS') (Ne.symm h2) (Ne.symm hS'ne) (Ne.symm h3) h1 e1 e2 e3 e4 e5
    have : (cnt c (swapSet a b S') : ℤ) + 1 ≤ cnt c S' := by exact_mod_cast hlt'
    have : (cnt c (swapSet a b S) : ℤ) + 3 ≤ cnt c S := by exact_mod_cast hgt
    linarith

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem isOptimal_of_cost_eq (hopt : IsOptimal c) {c' : PEC G (Fin k)} (h : Total c')
    (hc : ∑ X, ((cnt c' X : ℤ)) ^ 2 = ∑ X, ((cnt c X : ℤ)) ^ 2) : IsOptimal c' := by
  classical
  refine ⟨h, fun c'' h'' => ?_⟩
  have h1 := cost_le_of_opt hopt h''
  have : (cost c' : ℤ) ≤ cost c'' := by rw [cost_eq_sum_cnt, cost_eq_sum_cnt, hc]; exact h1
  exact_mod_cast this

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **Lemma 2, difference two.** -/
theorem lemma2_two (hopt : IsOptimal c) (hab : a ≠ b) {S : Finset (Fin k)}
    (h : cnt c S = cnt c (swapSet a b S) + 2) :
    ∃ c' : PEC G (Fin k), IsOptimal c' ∧ cnt c' S = cnt c (swapSet a b S) ∧
      cnt c' (swapSet a b S) = cnt c S ∧
      ∀ X, X ≠ S → X ≠ swapSet a b S → cnt c' X = cnt c X := by
  classical
  have hSne : swapSet a b S ≠ S := fun e => by rw [e] at h; omega
  obtain ⟨S', hlt', hS'ne, -, c', htot', hcnt⟩ := lemma2_swap hab hopt.1 (S := S) (by omega)
  have hle := cost_le_of_opt hopt htot'
  by_cases hS' : S' = S
  · subst hS'
    obtain ⟨e1, e2, e3⟩ := counts_same hSne hcnt
    have hsum := sum_sq_update (f := fun X => (cnt c X : ℤ)) (g := fun X => (cnt c' X : ℤ))
      (Ne.symm hSne) (d := 2) e1 e2 e3
    have hh : (cnt c S' : ℤ) = cnt c (swapSet a b S') + 2 := by exact_mod_cast h
    refine ⟨c', isOptimal_of_cost_eq hopt htot' (by rw [hsum, hh]; ring), by omega, by omega,
      fun X h1 h2 => by have := e3 X h1 h2; omega⟩
  · exfalso
    have h1 : S' ≠ swapSet a b S' := fun e => by rw [← e] at hlt'; exact lt_irrefl _ hlt'
    obtain ⟨h2, h3⟩ := four_distinct hSne h1 hS' hS'ne
    obtain ⟨e1, e2, e3, e4, e5⟩ := counts_four hSne h1 hS' hS'ne hcnt
    have := sum_sq_update4 (f := fun X => (cnt c X : ℤ)) (g := fun X => (cnt c' X : ℤ))
      (Ne.symm hSne) (Ne.symm hS') (Ne.symm h2) (Ne.symm hS'ne) (Ne.symm h3) h1 e1 e2 e3 e4 e5
    have : (cnt c (swapSet a b S') : ℤ) + 1 ≤ cnt c S' := by exact_mod_cast hlt'
    have : (cnt c S : ℤ) = cnt c (swapSet a b S) + 2 := by exact_mod_cast h
    linarith

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **Lemma 2, difference one.** -/
theorem lemma2_one (hopt : IsOptimal c) (hab : a ≠ b) {S : Finset (Fin k)}
    (h : cnt c S = cnt c (swapSet a b S) + 1) :
    ∃ U : Finset (Fin k), U ≠ S ∧ U ≠ swapSet a b S ∧ swapSet a b U ≠ S ∧
      swapSet a b U ≠ swapSet a b S ∧ cnt c U = cnt c (swapSet a b U) + 1 ∧
      ∃ c' : PEC G (Fin k), IsOptimal c' ∧ cnt c' S = cnt c (swapSet a b S) ∧
        cnt c' (swapSet a b S) = cnt c S ∧ cnt c' U = cnt c (swapSet a b U) ∧
        cnt c' (swapSet a b U) = cnt c U ∧
        ∀ X, X ≠ S → X ≠ swapSet a b S → X ≠ U → X ≠ swapSet a b U → cnt c' X = cnt c X := by
  classical
  have hSne : swapSet a b S ≠ S := fun e => by rw [e] at h; omega
  obtain ⟨S', hlt', hS'ne, hSS, c', htot', hcnt⟩ := lemma2_swap hab hopt.1 (S := S) (by omega)
  have hS' : S' ≠ S := fun e => by have := hSS e; omega
  have h1 : S' ≠ swapSet a b S' := fun e => by rw [← e] at hlt'; exact lt_irrefl _ hlt'
  obtain ⟨h2, h3⟩ := four_distinct hSne h1 hS' hS'ne
  obtain ⟨e1, e2, e3, e4, e5⟩ := counts_four hSne h1 hS' hS'ne hcnt
  have hsum := sum_sq_update4 (f := fun X => (cnt c X : ℤ)) (g := fun X => (cnt c' X : ℤ))
    (Ne.symm hSne) (Ne.symm hS') (Ne.symm h2) (Ne.symm hS'ne) (Ne.symm h3) h1 e1 e2 e3 e4 e5
  have hle := cost_le_of_opt hopt htot'
  have hlt'' : (cnt c (swapSet a b S') : ℤ) + 1 ≤ cnt c S' := by exact_mod_cast hlt'
  have hh : (cnt c S : ℤ) = cnt c (swapSet a b S) + 1 := by exact_mod_cast h
  have hS'1 : (cnt c S' : ℤ) = cnt c (swapSet a b S') + 1 := by linarith
  refine ⟨S', hS', hS'ne, h2, h3, by exact_mod_cast hS'1, c',
    isOptimal_of_cost_eq hopt htot' (by rw [hsum]; linarith), by omega, by omega, by omega,
    by omega, fun X f1 f2 f3 f4 => by have := e5 X f1 f2 f3 f4; omega⟩
end Bkls

end LeanPool.BalancedEdgeColourings
