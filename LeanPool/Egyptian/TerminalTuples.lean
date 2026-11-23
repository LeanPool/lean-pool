/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.Bellman

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
  have hpositive : 0 < unit T := one_div_pos.mpr (by exact_mod_cast (show 0 < T by omega))
  have hc : Controls σ s ds := (controls_iff hv ds).mpr
    ⟨hmin, List.pairwise_cons.mpr ⟨hstart, horder⟩, by linarith⟩
  have hlast : (finish s ds).last < T := by
    have hb : (finish s ds).last ≤ T - 1 :=
      finish_last_le (by omega) (fun d hd => Nat.le_pred_of_lt (hbound d hd))
    omega
  have hf := finish_fraction hv hc
  rw [hsum, add_sub_cancel_left] at hf
  have hvf := finish_valid hv hc
  have hq : ((finish s ds).q : ℚ) ≠ 0 := by exact_mod_cast hvf.2.ne'
  have hT' : (T : ℚ) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
  unfold unit at hf
  field_simp at hf
  exact ⟨hc, hT, hlast, by exact_mod_cast hf.symm⟩

end Egyptian.Control
