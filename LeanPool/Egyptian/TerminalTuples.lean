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

theorem terminal_to_tuple {σ s ds T} (hv : Valid s) (ht : Terminal σ s ds T) :
    Admissible σ ((s.p : ℚ) / s.q) ds.length ds ∧
      (∀ d ∈ ds, d < T) ∧ (s.p : ℚ) / s.q = recipSum ds + unit T := by
  obtain ⟨hds, ho, _⟩ := controls_ordered ht.1
  have hsplit := terminal_identity hv ht
  have hpos : (0:ℚ) < unit T := one_div_pos.mpr (by exact_mod_cast (show 0 < T by
    have := ht.2.1; omega))
  exact ⟨⟨rfl, fun d hd => (hds d hd).1, ho, by linarith⟩,
    fun d hd => (hds d hd).2.2.trans_lt ht.2.2.1, hsplit⟩

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
