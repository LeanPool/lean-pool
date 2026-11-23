/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.Bellman
import LeanPool.Egyptian.Assembly
import Mathlib.Analysis.PSeries

/-!
# Entering the small-remainder region

At a target larger than one, take consecutive denominators from 2 onwards
up to the last sum strictly below the target. The divergence of the harmonic
series ensures a first crossing. The remaining fraction at the preceding step
is at most the reciprocal of the next denominator.
-/

public section

namespace Egyptian.Control

/-- Denominator order, the lower bound two, and a strictly positive residual
are together equivalent to legality of the entire control path. -/
theorem controls_iff {σ : Convention} {s : State} (hv : Valid s) (xs : List ℕ) :
    Controls σ s xs ↔ (∀ d ∈ xs, 2 ≤ d) ∧ (s.last :: xs).Pairwise σ.rel ∧
      recipSum xs < (s.p : ℚ) / s.q := by
  refine ⟨fun hc => ?_, ?_⟩
  · obtain ⟨bounds, order, _⟩ := controls_ordered hc
    have ⟨hp, hq⟩ := finish_valid hv hc
    have positive : 0 < ((finish s xs).p : ℚ) / (finish s xs).q :=
      div_pos (by exact_mod_cast hp) (by exact_mod_cast hq)
    rw [finish_fraction hv hc] at positive
    exact ⟨fun d hd => (bounds d hd).1,
      List.pairwise_cons.mpr ⟨fun d hd => (bounds d hd).2.1, order⟩, sub_pos.mp positive⟩
  · induction xs generalizing s with
    | nil => exact fun _ => trivial
    | cons d ds ih =>
      have hq : (0 : ℚ) < s.q := by exact_mod_cast hv.2
      rintro ⟨hall, horder, hsum⟩
      obtain ⟨hfirst, hrest⟩ := List.pairwise_cons.mp horder
      have hd := hall d (by simp)
      have hdpos : (0 : ℚ) < d := by exact_mod_cast (show 0 < d by omega)
      change unit d + recipSum ds < _ at hsum
      have hu : (1 : ℚ) / d < (s.p : ℚ) / s.q := by
        change unit d < _
        linarith [recipSum_nonneg ds]
      have hcomp := (div_lt_div_iff₀ hdpos hq).mp hu
      simp only [one_mul] at hcomp
      have hlegal : Legal σ s d := ⟨by exact_mod_cast hcomp, hd, hfirst d (by simp)⟩
      refine ⟨hlegal, ih (step_valid hv hlegal)
        ⟨fun e he => hall e (by simp [he]), hrest, ?_⟩⟩
      rw [step_fraction hv hlegal]
      linarith

private theorem last_le {s : State} {xs : List ℕ} {K : ℕ}
    (hs : s.last ≤ K) (hx : ∀ e ∈ xs, e ≤ K) : (finish s xs).last ≤ K := by
  induction xs generalizing s with
  | nil => exact hs
  | cons d ds ih => exact ih (s := step s d) (hx d (by simp)) (fun e he => hx e (by simp [he]))

private def initial (n : ℕ) := prefixTuple (fun i => i + 2) n

private theorem initial_succ (n : ℕ) :
    recipSum (initial (n+1)) = recipSum (initial n) + unit (n+2) := by
  simp [initial, prefixTuple, List.range_succ, recipSum]

private theorem initial_sum (n : ℕ) :
    (recipSum (initial n) : ℝ) = ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 2) := by
  simpa [initial] using real_prefix_sum (fun i => i + 2) n

private theorem crosses (q : ℚ) : ∃ n, q ≤ recipSum (initial n) := by
  by_contra! hn
  have hsum : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) := by
    apply summable_of_sum_range_le (fun n => by positivity) (c := (q : ℝ))
    intro n
    rw [← initial_sum]
    exact_mod_cast (hn n).le
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 2).mp
  simpa using hsum

/-- Terminal paths exist for both conventions, including targets greater than one. -/
theorem terminal_exists (σ : Convention) (s : State) (hv : Valid s)
    (hi : Interior s) : ∃ xs T, Terminal σ s xs T := by
  classical
  by_cases hsmall : s.p ≤ s.q
  · exact terminal_exists_small σ s hv hi hsmall
  have hlast : s.last = 0 := by
    unfold Interior at hi
    by_contra! h
    exact (not_lt_of_ge (Nat.le_of_not_ge hsmall))
      (lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by omega)) hi)
  let q : ℚ := (s.p : ℚ) / s.q
  have hp : (0 : ℚ) < s.p := by exact_mod_cast hv.1
  have hq : (0 : ℚ) < s.q := by exact_mod_cast hv.2
  have hpos : 0 < q := div_pos hp hq
  let k := Nat.find (crosses q)
  have hcross : q ≤ recipSum (initial k) := Nat.find_spec (crosses q)
  have hk : k ≠ 0 := by
    intro hz
    simp [hz, initial, prefixTuple, recipSum] at hcross
    linarith
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hbefore : recipSum (initial n) < q := lt_of_not_ge
    (Nat.find_min (crosses q) (show n < k by omega))
  rw [hn, initial_succ] at hcross
  have hmem (d : ℕ) (hd : d ∈ initial n) : 2 ≤ d ∧ d ≤ n+1 := by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
    have hi' := List.mem_range.mp hi
    omega
  have hord : (initial n).Pairwise σ.rel := by
    apply List.pairwise_map.mpr
    apply List.pairwise_lt_range.imp
    intro a b hab
    cases σ <;> dsimp [Convention.rel] <;> omega
  have hcontrols := (controls_iff (σ := σ) hv (initial n)).mpr
    ⟨fun d hd => (hmem d hd).1, List.pairwise_cons.mpr ⟨fun d hd => by
      have hd2 := (hmem d hd).1
      rw [hlast]
      cases σ with
      | weak => exact Nat.zero_le d
      | strict => exact Nat.lt_of_lt_of_le (by decide : 0 < 2) hd2, hord⟩, hbefore⟩
  let v := finish s (initial n)
  have vv : Valid v := finish_valid hv hcontrols
  have vl : v.last ≤ n+1 := last_le (by simp [hlast]) (fun d hd => (hmem d hd).2)
  have hf := finish_fraction hv hcontrols
  change (v.p : ℚ) / v.q = q - recipSum (initial n) at hf
  have vmax : (v.p : ℚ) / v.q ≤ unit (n+2) := by linarith
  have hd : (0 : ℚ) < (n+2 : ℕ) := by positivity
  have hq' : (0 : ℚ) < v.q := by exact_mod_cast vv.2
  have hmul : v.p * (n+2) ≤ v.q := by
    unfold unit at vmax
    have hm := (div_le_div_iff₀ hq' hd).mp vmax
    rw [one_mul] at hm
    exact_mod_cast hm
  have vi : Interior v := by
    change v.last * v.p < v.q
    rw [Nat.mul_comm]
    exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left (by omega) vv.1) hmul
  have vs : v.p ≤ v.q := (Nat.le_mul_of_pos_right _ (by omega)).trans hmul
  obtain ⟨ds, T, ht⟩ := terminal_exists_small σ v vv vi vs
  exact ⟨initial n ++ ds, T, (terminal_append s (initial n) ds T).mpr ⟨hcontrols, ht⟩⟩

end Egyptian.Control
