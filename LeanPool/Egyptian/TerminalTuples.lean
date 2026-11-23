/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.Bellman
import Mathlib.Tactic.Positivity.Finset

/-!
# Terminal decompositions and ordered denominator tuples

The optimization uses cleared numerator–denominator states. The completion
argument sorts a list of denominators. These lemmas identify the two
descriptions without any coprimality assumption.
-/

public section

namespace Egyptian.Control

private theorem rel_trans {σ : Convention} {a b c : ℕ} (hab : σ.rel a b)
    (hbc : σ.rel b c) : σ.rel a c := by
  cases σ with
  | weak => exact Nat.le_trans hab hbc
  | strict => exact Nat.lt_trans hab hbc

private theorem rel_weak {σ : Convention} {a b : ℕ} (hab : σ.rel a b) : a ≤ b := by
  cases σ with
  | weak => exact hab
  | strict => exact hab.le

theorem controls_ordered {σ s ds} (hc : Controls σ s ds) :
    (∀ d ∈ ds, 2 ≤ d ∧ σ.rel s.last d ∧ d ≤ (finish s ds).last) ∧
      ds.Pairwise σ.rel ∧ s.last ≤ (finish s ds).last := by
  induction ds generalizing s with
  | nil => simp [finish]
  | cons x ds ih =>
    obtain ⟨hxs, ho, he⟩ := ih hc.2
    have hl := hc.1
    change x ≤ (finish (step s x) ds).last at he
    refine ⟨?_, List.pairwise_cons.mpr ⟨fun d hd => (hxs d hd).2.1, ho⟩,
      (rel_weak hl.2.2).trans he⟩
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨hl.2.1, hl.2.2, he⟩
    · obtain ⟨hd1, hd2, hd3⟩ := hxs d hd
      exact ⟨hd1, rel_trans hl.2.2 hd2, hd3⟩

theorem terminal_to_tuple {σ s ds T} (hv : Valid s) (ht : Terminal σ s ds T) :
    Admissible σ ((s.p : ℚ) / s.q) ds.length ds ∧
      (∀ d ∈ ds, d < T) ∧ (s.p : ℚ) / s.q = recipSum ds + unit T := by
  obtain ⟨hds, ho, _⟩ := controls_ordered ht.1
  have hsplit := terminal_identity hv ht
  have hpos : (0:ℚ) < unit T := one_div_pos.mpr (by exact_mod_cast (show 0 < T by
    have := ht.2.1; omega))
  exact ⟨⟨rfl, fun d hd => (hds d hd).1, ho, by linarith⟩,
    fun d hd => (hds d hd).2.2.trans_lt ht.2.2.1, hsplit⟩

private theorem recipSum_nonneg (ds : List ℕ) : 0 ≤ recipSum ds := by
  induction ds with
  | nil => simp [recipSum]
  | cons d ds ih =>
    have hu : 0 ≤ unit d := by unfold unit; positivity
    change 0 ≤ unit d + recipSum ds
    exact add_nonneg hu ih

/-- A sorted tuple with all entries below the final unit denominator supplies
a legal terminal decomposition from its starting state. -/
theorem terminal_of_tuple {σ s ds T} (hv : Valid s) (hT : 2 ≤ T)
    (hprev : s.last < T) (hmin : ∀ d ∈ ds, 2 ≤ d)
    (hstart : ∀ d ∈ ds, σ.rel s.last d) (horder : ds.Pairwise σ.rel)
    (hbound : ∀ d ∈ ds, d < T)
    (hsum : (s.p : ℚ) / s.q = recipSum ds + unit T) : Terminal σ s ds T := by
  induction ds generalizing s with
  | nil =>
    have hq : (s.q : ℚ) ≠ 0 := by exact_mod_cast hv.2.ne'
    have hT' : (T : ℚ) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
    simp only [recipSum, List.map_nil, List.sum_nil, zero_add, unit] at hsum
    field_simp at hsum
    exact ⟨trivial, hT, hprev, by exact_mod_cast hsum.symm⟩
  | cons d ds ih =>
    have hd := hmin d (by simp)
    have hord := List.pairwise_cons.mp horder
    have hTpos : (0:ℚ) < unit T := one_div_pos.mpr (by
      exact_mod_cast (show 0 < T by omega))
    have hdpos : (0:ℚ) < d := by exact_mod_cast (show 0 < d by omega)
    have hqpos : (0:ℚ) < s.q := by exact_mod_cast hv.2
    change (s.p : ℚ) / s.q = (unit d + recipSum ds) + unit T at hsum
    have hfrac : unit d < (s.p : ℚ) / s.q := by linarith [recipSum_nonneg ds]
    have hineq := (div_lt_div_iff₀ hdpos hqpos).1 hfrac
    have hlegal : Legal σ s d := ⟨by simpa only [one_mul, Nat.cast_lt, ← Nat.cast_mul] using hineq,
      hd, hstart d (by simp)⟩
    obtain ⟨hr, hterm⟩ := ih (step_valid hv hlegal) (hbound d (by simp))
      (fun x hx => hmin x (by simp [hx])) hord.1 hord.2
      (fun x hx => hbound x (by simp [hx]))
      (by rw [step_fraction hv hlegal]; linarith)
    exact ⟨⟨hlegal, hr⟩, hterm⟩

end Egyptian.Control
