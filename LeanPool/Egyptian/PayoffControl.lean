/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.BellmanArithmetic
public import LeanPool.Egyptian.BellmanDrift
public import LeanPool.Egyptian.PayoffTransition
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Positivity.Finset

/-! Both transition inequalities on actual legal control strings. -/

@[expose] public section

namespace Egyptian.Control

open Finset

theorem controls_take {σ s xs} (hc : Controls σ s xs) (k : ℕ) :
    Controls σ s (xs.take k) := by
  induction k generalizing s xs with
  | zero => simp [Controls]
  | succ k ih =>
    cases xs with
    | nil => trivial
    | cons x xs => exact ⟨hc.1, ih hc.2⟩

private theorem legal_order {σ s x} (h : Legal σ s x) : s.last ≤ x := by
  have hh := h.2.2
  cases σ with
  | weak => exact hh
  | strict => exact Nat.le_of_lt hh

theorem controls_bounds {σ s xs} (hc : Controls σ s xs) :
    ∀ d ∈ xs, s.last ≤ d ∧ 2 ≤ d := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨legal_order hc.1, hc.1.2.1⟩
    · have h := ih hc.2 d hd
      exact ⟨(legal_order hc.1).trans h.1, h.2⟩

theorem controls_sorted {σ s xs} (hc : Controls σ s xs) : xs.Pairwise (· ≤ ·) := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    exact List.pairwise_cons.mpr ⟨fun d hd => (controls_bounds hc.2 d hd).1, ih hc.2⟩

private noncomputable def terms (xs : List ℕ) (i : ℕ) : ℝ :=
  1 / (xs.getD i 1 : ℝ)

private theorem terms_sum (xs : List ℕ) {k : ℕ} (hk : k ≤ xs.length) :
    (∑ i ∈ range k, terms xs i) = (recipSum (xs.take k) : ℝ) := by
  induction k with
  | zero => simp [recipSum]
  | succ k ih =>
    have h : k < xs.length := by omega
    rw [sum_range_succ, ih (by omega), List.take_succ_eq_append_getElem h]
    simp only [terms, List.getD_eq_getElem _ _ h, recipSum, List.map_append,
      List.map_singleton, List.sum_append, List.sum_singleton, Rat.cast_add]
    simp [unit]

private theorem terms_prod (xs : List ℕ) {k : ℕ} (hk : k ≤ xs.length) :
    (∏ i ∈ range k, terms xs i) = 1 / ((xs.take k).prod : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : k < xs.length := by omega
    rw [prod_range_succ, ih (by omega), List.take_succ_eq_append_getElem h]
    simp only [terms, List.getD_eq_getElem _ _ h, List.prod_append, List.prod_singleton,
      Nat.cast_mul, one_div, mul_inv]

private theorem terms_order {σ s xs} (hc : Controls σ s xs) :
    (∀ i < xs.length, 0 < terms xs i) ∧
      ∀ i, i+1 < xs.length → terms xs (i+1) ≤ terms xs i := by
  have hden (i : ℕ) (hi : i < xs.length) : 0 < (xs[i] : ℝ) := by
    exact_mod_cast (by have := (controls_bounds hc _ (List.getElem_mem hi)).2; omega : 0 < xs[i])
  constructor
  · intro i hi
    simp only [terms, List.getD_eq_getElem _ _ hi]
    exact one_div_pos.mpr (hden _ hi)
  · intro i hi
    have hi' : i < xs.length := by omega
    simp only [terms, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi']
    apply one_div_le_one_div_of_le (hden _ hi')
    exact_mod_cast (List.pairwise_iff_getElem.mp (controls_sorted hc) i (i+1) hi' hi (by omega))

private theorem prefix_identity {σ s xs} (hv : Valid s) (hc : Controls σ s xs)
    {k : ℕ} (hk : k ≤ xs.length) :
    (∑ i ∈ range k, terms xs i) +
      ((finish s (xs.take k)).p : ℝ) / s.q * ∏ i ∈ range k, terms xs i =
      1 / inverseRemainder s := by
  let bs := xs.take k
  have hbs := controls_take hc k
  have hid := cleared_product hv hbs
  have hr : (s.p : ℝ) / s.q - (recipSum bs : ℝ) =
      ((finish s bs).p : ℝ) / (s.q * (bs.prod : ℝ)) := by
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, bs] using
      congrArg (fun r : ℚ => (r : ℝ)) hid
  rw [terms_sum xs hk, terms_prod xs hk, inverseRemainder]
  change (recipSum bs : ℝ) + _ = _
  simp only [one_div_div, mul_one_div, ← div_mul_eq_div_div]
  linarith

private theorem remainder_eq {σ s xs} (hv : Valid s) (hc : Controls σ s xs) :
    1 / inverseRemainder s - (∑ i ∈ range xs.length, terms xs i) =
      1 / inverseRemainder (finish s xs) := by
  rw [terms_sum xs le_rfl, List.take_length, inverseRemainder, inverseRemainder]
  simp only [one_div_div]
  simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_natCast] using
    congrArg (fun r : ℚ => (r : ℝ)) (finish_fraction hv hc).symm

private theorem noFall_prefix {σ s xs} (hv : Valid s) (hc : Controls σ s xs)
    {k : ℕ} (hk : k ≤ xs.length) (hf : s.p ≤ (finish s (xs.take k)).p) :
    (∑ i ∈ range k, terms xs i) + (1/inverseRemainder s) * ∏ i ∈ range k, terms xs i ≤
      1/inverseRemainder s := by
  have hq : (0 : ℝ) < s.q := by exact_mod_cast hv.2
  refine le_trans ?_ (prefix_identity hv hc hk).le
  gcongr 1
  apply mul_le_mul_of_nonneg_right
  · simpa [inverseRemainder, one_div_div] using
      (div_le_div_of_nonneg_right
        (show (s.p : ℝ) ≤ (finish s (xs.take k)).p by exact_mod_cast hf) hq.le)
  · exact prod_nonneg (fun i hi => ((terms_order hc).1 i ((mem_range.mp hi).trans_le hk)).le)

theorem noFall_bound {σ s xs} (hv : Valid s) (hsmall : s.p ≤ s.q)
    (hc : Controls σ s xs) (hpre : ∀ k, k ≤ xs.length → s.p ≤ (finish s (xs.take k)).p) :
    inverseRemainder (finish s xs) ≤ Payoff.orbit (inverseRemainder s) xs.length := by
  have ht := one_le_inverse hv hsmall
  have h := Payoff.no_decrease ht (terms xs) xs.length (terms_order hc).1 (terms_order hc).2
    (fun k _ hk => noFall_prefix hv hc hk (hpre k hk))
  rw [remainder_eq hv hc] at h
  exact le_of_one_div_le_one_div (lt_of_lt_of_le zero_lt_one (Payoff.one_le_orbit ht _)) h

theorem firstFall_bound {σ s xs} (hv : Valid s) (hsmall : s.p ≤ s.q)
    (hc : Controls σ s xs) (hpre : ∀ k, k < xs.length → s.p ≤ (finish s (xs.take k)).p)
    (hfall : (finish s xs).p < s.p) :
    inverseRemainder (finish s xs) <
      ((s.p : ℝ) / (finish s xs).p) * Payoff.orbit (inverseRemainder s) xs.length := by
  obtain ⟨m, hm⟩ : ∃ m, xs.length = m+1 := by
    cases xs with
    | nil => exact False.elim ((lt_irrefl _) hfall)
    | cons x xs => exact ⟨xs.length, rfl⟩
  let δ : ℝ := ((finish s xs).p : ℝ) / s.p
  have hp : (0 : ℝ) < s.p := by exact_mod_cast hv.1
  have hd : (0 : ℝ) < (finish s xs).p := by exact_mod_cast (finish_valid hv hc).1
  have hq : (0 : ℝ) < s.q := by exact_mod_cast hv.2
  have ht := one_le_inverse hv hsmall
  have hδ : 0 < δ := div_pos hd hp
  have hδ' : δ < 1 := (div_lt_one hp).mpr (by exact_mod_cast hfall)
  have ht' := terms_order hc
  rw [hm] at ht'
  have h := Payoff.first_decrease ht hδ hδ' (terms xs) m ht'.1 ht'.2
    (fun k _ hk => noFall_prefix hv hc (by omega) (hpre k (by omega))) (by
      rw [← hm]
      have hi := prefix_identity hv hc (le_refl xs.length)
      rw [List.take_length] at hi
      have he : δ / inverseRemainder s = ((finish s xs).p : ℝ) / s.q := by
        dsimp [δ, inverseRemainder]
        field_simp
      rw [he]
      exact hi.le)
  rw [← hm, remainder_eq hv hc] at h
  have ho : 0 < Payoff.orbit (inverseRemainder s) xs.length :=
    lt_of_lt_of_le zero_lt_one (Payoff.one_le_orbit ht _)
  have hf : 0 < inverseRemainder (finish s xs) :=
    div_pos (by exact_mod_cast (finish_valid hv hc).2) hd
  have hprod := (div_lt_div_iff₀ ho hf).mp h
  dsimp [δ] at hprod
  rw [div_mul_eq_mul_div] at hprod ⊢
  apply (lt_div_iff₀ hd).2
  linarith [(div_lt_iff₀ hp).1 hprod]

end Egyptian.Control
