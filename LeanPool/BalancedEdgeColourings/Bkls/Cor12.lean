/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.Thm10b
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Balister–Kostochka–Li–Schelp 2004, Corollary 12

`cor12`: if `G` has `n` vertices, `Δ(G) ≥ √(2n) + 4`, `δ(G) ≥ 5`, and `k` is the least integer with
`n_d ≤ C(k, d)` for all `d`, then `k ≤ χ'_s(G) ≤ k + 1`: some strong edge colouring uses `k + 1`
colours, and every strong edge colouring uses at least `k` colours.

The hypotheses of Theorem 10 (part 2) follow from `n ≤ (k - 4)² / 2` and `k ≥ 9` (`cor12_arith`;
the polynomial inequalities were certified by `certo nonneg`).
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.C12

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull Balanced Bkls


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

open Classical in
/-- Binomial coefficients grow towards the middle. -/
theorem choose_mid {m i j : ℕ} (hij : i ≤ j) (hjm : j + i ≤ m) : m.choose i ≤ m.choose j := by
  have up : ∀ j, i ≤ j → j ≤ m / 2 → m.choose i ≤ m.choose j := by
    intro j hj hjm'
    induction j with
    | zero => rw [Nat.le_zero.1 hj]
    | succ j ih =>
      rcases Nat.eq_or_lt_of_le hj with h | h
      · rw [h]
      · exact (ih (by omega) (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
  by_cases hj : j ≤ m / 2
  · exact up j hij hj
  · calc m.choose i ≤ m.choose (m - j) := up (m - j) (by omega) (by omega)
      _ = m.choose j := Nat.choose_symm (by omega)

open Classical in
theorem cast_choose_two' (n : ℕ) : ((n.choose 2 : ℕ) : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 :=
  Nat.cast_choose_two ℚ n

open Classical in
theorem cast_choose_three (n : ℕ) (hn : 2 ≤ n) :
    ((n.choose 3 : ℕ) : ℚ) = (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) / 6 := by
  have h := Nat.choose_succ_right_eq n 2
  have h' : ((n.choose 3 : ℕ) : ℚ) * 3 = ((n.choose 2 : ℕ) : ℚ) * ((n - 2 : ℕ) : ℚ) := by
    exact_mod_cast h
  rw [cast_choose_two', Nat.cast_sub hn] at h'
  push_cast at h'
  linarith

open Classical in
/-- **The arithmetic of Corollary 12.** -/
theorem cor12_arith {k d : ℕ} (hk : 9 ≤ k) (hd5 : 5 ≤ d) (hdk : d + 2 ≤ k) :
    ((k : ℚ) - 4) ^ 2 / 2 + 2 ≤ ((d : ℚ) - 4) / ((d : ℚ) - 3) *
      min (2 * (((k - 3).choose (d - 3) : ℕ) : ℚ)) ((k.choose d : ℕ) : ℚ) := by
  have hK : (9 : ℚ) ≤ k := by exact_mod_cast hk
  have hD : (5 : ℚ) ≤ d := by exact_mod_cast hd5
  have hDK : (d : ℚ) + 2 ≤ k := by exact_mod_cast hdk
  have hr0 : 0 ≤ ((d : ℚ) - 4) / ((d : ℚ) - 3) := by apply div_nonneg <;> linarith
  have hr2 : 1 / 2 ≤ ((d : ℚ) - 4) / ((d : ℚ) - 3) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
  rw [mul_min_of_nonneg _ _ hr0]
  apply le_min
  · -- the first term
    have hC3 : (k - 3).choose 2 ≤ (k - 3).choose (d - 3) := choose_mid (by omega) (by omega)
    have hC3' : (((k - 3).choose 2 : ℕ) : ℚ) ≤ (((k - 3).choose (d - 3) : ℕ) : ℚ) := by
      exact_mod_cast hC3
    rw [cast_choose_two', Nat.cast_sub (by omega)] at hC3'
    push_cast at hC3'
    have h0 : (0 : ℚ) ≤ (((k - 3).choose (d - 3) : ℕ) : ℚ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hr2 h0]
  · by_cases hcase : d + 5 ≤ k
    · have hC : k.choose 3 ≤ k.choose d := choose_mid (by omega) (by omega)
      have hC' : ((k.choose 3 : ℕ) : ℚ) ≤ ((k.choose d : ℕ) : ℚ) := by exact_mod_cast hC
      rw [cast_choose_three k (by omega)] at hC'
      have h0 : (0 : ℚ) ≤ ((k.choose d : ℕ) : ℚ) := by positivity
      have hp : ((k : ℚ) - 4) ^ 2 / 2 + 2 ≤ (k : ℚ) * ((k : ℚ) - 1) * ((k : ℚ) - 2) / 6 / 2 := by
        nlinarith [mul_nonneg (sub_nonneg.2 hK) (sub_nonneg.2 hK),
          mul_nonneg (mul_nonneg (sub_nonneg.2 hK) (sub_nonneg.2 hK)) (sub_nonneg.2 hK)]
      nlinarith [mul_le_mul_of_nonneg_right hr2 h0]
    · have hC : k.choose 2 ≤ k.choose d := choose_mid (by omega) (by omega)
      have hC' : ((k.choose 2 : ℕ) : ℚ) ≤ ((k.choose d : ℕ) : ℚ) := by exact_mod_cast hC
      rw [cast_choose_two'] at hC'
      have hr : ((k : ℚ) - 8) / ((k : ℚ) - 7) ≤ ((d : ℚ) - 4) / ((d : ℚ) - 3) := by
        have : (k : ℚ) ≤ d + 4 := by
          have : k ≤ d + 4 := by omega
          exact_mod_cast this
        rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
      have hr8 : 0 ≤ ((k : ℚ) - 8) / ((k : ℚ) - 7) := by apply div_nonneg <;> linarith
      have hp : ((k : ℚ) - 4) ^ 2 / 2 + 2 ≤ ((k : ℚ) - 8) / ((k : ℚ) - 7) *
          ((k : ℚ) * ((k : ℚ) - 1) / 2) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
        nlinarith [mul_nonneg (sub_nonneg.2 hK) (sub_nonneg.2 hK)]
      calc ((k : ℚ) - 4) ^ 2 / 2 + 2 ≤ ((k : ℚ) - 8) / ((k : ℚ) - 7) *
            ((k : ℚ) * ((k : ℚ) - 1) / 2) := hp
        _ ≤ ((d : ℚ) - 4) / ((d : ℚ) - 3) * ((k.choose d : ℕ) : ℚ) :=
            mul_le_mul hr hC' (by nlinarith) hr0

open Classical in
omit [DecidableEq V] in
/-- Degrees of a strong colouring: at most `C(m, d)` vertices of degree `d`. -/
theorem nd_le_of_strong {m : ℕ} {c : PEC G (Fin m)} (h : Strong c) (d : ℕ) :
    L9.nd G d ≤ m.choose d := by
  classical
  unfold L9.nd
  have hc : #(powersetCard d (univ : Finset (Fin m))) = m.choose d := by
    rw [card_powersetCard, card_univ, Fintype.card_fin]
  rw [← hc]
  refine card_le_card_of_injOn (colSet c) (fun v hv => ?_) (fun u _ v _ e => h.2 e)
  rw [mem_coe, mem_powersetCard]
  exact ⟨subset_univ _, by rw [L9.card_colSet h.1]; exact (mem_filter.1 (mem_coe.1 hv)).2⟩

open Classical in
omit [DecidableEq V] in
/-- **Corollary 12.** -/
theorem cor12 (hn : Real.sqrt (2 * Fintype.card V) + 4 ≤ G.maxDegree) (hδ : 5 ≤ G.minDegree)
    {k : ℕ} (hk : ∀ d, L9.nd G d ≤ k.choose d) (hkmin : ∀ k' < k, ∃ d, k'.choose d < L9.nd G d) :
    (∃ c : PEC G (Fin (k + 1)), Strong c) ∧ ∀ m (c : PEC G (Fin m)), Strong c → k ≤ m := by
  classical
  refine ⟨?_, fun m c hc => ?_⟩
  swap
  · by_contra hlt
    push Not at hlt
    obtain ⟨d, hd⟩ := hkmin m hlt
    have := nd_le_of_strong hc d
    omega
  set n := Fintype.card V
  set Δ := G.maxDegree
  -- `(Δ - 4)² ≥ 2n`, `Δ ≥ 9`
  have hΔ4 : (4 : ℝ) ≤ Δ := by have := Real.sqrt_nonneg (2 * (n : ℝ)); linarith
  have hsq : 2 * (n : ℝ) ≤ ((Δ : ℝ) - 4) ^ 2 := by
    have h1 : Real.sqrt (2 * (n : ℝ)) ≤ (Δ : ℝ) - 4 := by linarith
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * n by positivity)
    nlinarith [Real.sqrt_nonneg (2 * (n : ℝ))]
  have : Nonempty V := by
    by_contra hV
    rw [not_nonempty_iff] at hV
    have : Δ ≤ 0 := G.maxDegree_le_of_forall_degree_le 0 (fun v => isEmptyElim v)
    have : (Δ : ℝ) ≤ 0 := by exact_mod_cast this
    linarith
  obtain ⟨v0, hv0⟩ := G.exists_maximal_degree_vertex
  have hΔn : Δ + 1 ≤ n := by
    have := G.degree_lt_card_verts v0
    rw [← hv0] at this; omega
  have hΔ9 : 9 ≤ Δ := by
    by_contra h9
    push Not at h9
    have h8 : (Δ : ℝ) ≤ 8 := by exact_mod_cast (show Δ ≤ 8 by omega)
    have hn' : ((Δ : ℝ) + 1) ≤ n := by exact_mod_cast hΔn
    nlinarith [mul_nonneg (sub_nonneg.2 hΔ4) (sub_nonneg.2 h8)]
  -- `Δ ≤ k`
  have hΔk : Δ ≤ k := by
    by_contra hlt
    push Not at hlt
    have h1 := hk Δ
    rw [Nat.choose_eq_zero_of_lt hlt] at h1
    have : 0 < L9.nd G Δ := card_pos.2 ⟨v0, mem_filter.2 ⟨mem_univ _, hv0.symm⟩⟩
    omega
  -- `2n ≤ (k - 4)²`
  have hsqN : 2 * n ≤ (Δ - 4) ^ 2 := by
    have : ((Δ : ℝ) - 4) = ((Δ - 4 : ℕ) : ℝ) := by rw [Nat.cast_sub (by omega)]; norm_num
    rw [this] at hsq
    exact_mod_cast hsq
  have hsqK : 2 * n ≤ (k - 4) ^ 2 := hsqN.trans (Nat.pow_le_pow_left (by omega) 2)
  have hdeg : ∀ v, 5 ≤ G.degree v := fun v => hδ.trans (G.minDegree_le_degree v)
  have hnd0 : ∀ d, d < 5 → L9.nd G d = 0 := by
    intro d hd
    unfold L9.nd
    rw [card_eq_zero, filter_eq_empty_iff]
    intro v _ hv
    have := hdeg v; omega
  have hndn : ∀ d, L9.nd G d ≤ n := fun d => card_le_univ _
  refine T10.thm10_2 (by omega) hΔk (fun d hd => by rw [hnd0 d (by omega)]; omega)
    (by rw [hnd0 3 (by omega)]; omega) (by rw [hnd0 4 (by omega)]; omega)
    (by have := hk k; rw [Nat.choose_self] at this; omega)
    (by
      have := hk (k - 1)
      rw [Nat.choose_symm (by omega), Nat.choose_one_right] at this
      omega) (fun d hd hdk => ?_)
  have h1 := cor12_arith (by omega) hd hdk
  have h2 : (L9.nd G d : ℚ) ≤ n := by exact_mod_cast hndn d
  have h3 : (2 * (n : ℚ)) ≤ ((k - 4 : ℕ) : ℚ) ^ 2 := by exact_mod_cast hsqK
  rw [Nat.cast_sub (by omega)] at h3
  push_cast at h3
  linarith
end Bkls.C12

end LeanPool.BalancedEdgeColourings
