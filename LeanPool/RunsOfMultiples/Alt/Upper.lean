/-
Copyright (c) 2026 Jason Hoelscher-Obermaier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hoelscher-Obermaier, Claude Opus 5.5
-/
module

-- Adapted for Lean Pool: module visibility, imports, and proof organization.

public import LeanPool.RunsOfMultiples.Alt.Chains
public import LeanPool.RunsOfMultiples.Alt.Radical

/-!
# The upper bound via compression

Compress `S` to a closed set `T` (`exists_closed`, Lemma 2), then bound the runs of `T` by the
radicals of its elements (`sum_L_le_of_closed`, Lemma 3 and equation (7)).
-/

open Finset Real

@[expose] public section

namespace RunsOfMultiples

/-- `∑_{a ∈ S} L S a = ∑_{t = 1}^{|S|} |A S t|`. -/
lemma sum_L_eq_sum_card_A (S : Finset ℕ) (hS : ∀ a ∈ S, 0 < a) :
    ∑ a ∈ S, L S a = ∑ t ∈ Icc 1 S.card, (A S t).card := by
  have hA : ∀ t, (A S t).card = ∑ a ∈ S, if t ≤ L S a then 1 else 0 := by
    intro t
    rw [← card_filter]
    congr 1
    ext a
    rw [mem_A_iff S hS, mem_filter]
  simp_rw [hA]
  rw [sum_comm]
  refine sum_congr rfl fun a ha => ?_
  rw [← card_filter]
  have : (Icc 1 S.card).filter (fun t => t ≤ L S a) = Icc 1 (L S a) := by
    ext t
    simp only [mem_filter, mem_Icc]
    have := L_le_card S hS ha
    omega
  rw [this, Nat.card_Icc]
  omega

/-- **Upper bound, second proof.** -/
theorem upper_bound_alt : ∃ C : ℝ, ∃ N : ℕ, ∀ S : Finset ℕ, (∀ a ∈ S, 0 < a) → N ≤ S.card →
    ((∑ a ∈ S, kVal S a : ℕ) : ℝ) ≤
      C * S.card * Real.log S.card * Real.log (Real.log S.card) := by
  obtain ⟨C, N, hCN⟩ := sum_L_le_of_closed
  refine ⟨C + 1, max N ⌈exp (exp 1)⌉₊, fun S hS hSN => ?_⟩
  obtain ⟨T, hT, hcard, hdiv, hshift, hA⟩ := exists_closed S hS
  have hTN : N ≤ T.card := by rw [hcard]; exact (le_max_left _ _).trans hSN
  have hT' := hCN T hT hdiv hshift hTN
  rw [hcard] at hT'
  -- `∑ L S ≤ ∑ L T`
  have hLL : (∑ a ∈ S, L S a : ℕ) ≤ ∑ a ∈ T, L T a := by
    rw [sum_L_eq_sum_card_A S hS, sum_L_eq_sum_card_A T hT, hcard]
    exact sum_le_sum fun t _ => hA t
  have hLLr : (∑ a ∈ S, (L S a : ℝ)) ≤ ∑ a ∈ T, (L T a : ℝ) := by
    exact_mod_cast hLL
  -- `log n · log log n ≥ 1`
  set n : ℝ := (S.card : ℝ) with hn
  have hn_big : exp (exp 1) ≤ n := by
    have := (le_max_right _ _).trans hSN
    exact (Nat.ceil_le.1 this)
  have hlog : exp 1 ≤ log n := by
    rw [le_log_iff_exp_le (lt_of_lt_of_le (exp_pos _) hn_big)]
    exact hn_big
  have hll : 1 ≤ log (log n) := by
    rw [le_log_iff_exp_le (lt_of_lt_of_le (exp_pos _) hlog)]
    exact hlog
  have hl1 : 1 ≤ log n := le_trans (by linarith [add_one_le_exp (1 : ℝ)]) hlog
  have hn1 : 1 ≤ n := le_trans (by linarith [add_one_le_exp (exp 1), exp_pos 1]) hn_big
  have hprod : n ≤ n * log n * log (log n) := by
    have : 1 ≤ log n * log (log n) := by nlinarith
    nlinarith
  have hk := sum_kVal_eq S hS
  have hk' : ((∑ a ∈ S, kVal S a : ℕ) : ℝ) = n + ∑ a ∈ S, (L S a : ℝ) := by
    rw [hk]; push_cast; rfl
  rw [hk']
  calc n + ∑ a ∈ S, (L S a : ℝ) ≤ n + C * n * log n * log (log n) := by linarith
    _ ≤ (C + 1) * n * log n * log (log n) := by nlinarith

end RunsOfMultiples
