/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.DeficientCutExact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The exact 9/10 cut bound

Every source-sink cut in Dross's auxiliary network has capacity at least the
network demand. This is the cut-side half of the max-flow construction.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

public theorem cut_ge_M_exact (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree) (wΔ : ℝ) (hwΔ : 0 < wΔ)
    (hbal : ∑ e ∈ G.edgeFinset, ((triThrough G e : ℝ) * wΔ - 1) = 0)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 10) (hn20 : 20 ≤ Fintype.card V) (hmd2 : 2 ≤ G.minDegree)
    (hδ_eq : (Fintype.card V : ℝ) - G.minDegree = δ * (Fintype.card V : ℝ))
    (hmbound : 2 * (G.edgeFinset.card : ℝ)
      ≤ (1 - δ + 2 * δ ^ 2) * (Fintype.card V : ℝ) ^ 2 + 4 + (Fintype.card V : ℝ)
        - 6 * δ * (Fintype.card V : ℝ))
    (C : Contrib.MaxFlowMinCut.Cut (drossNet G wΔ)) :
    demand G wΔ ≤ C.capacity := by
  have hδ_deg : (Fintype.card V : ℝ) - G.minDegree ≤ δ * (Fintype.card V : ℝ) := le_of_eq hδ_eq
  by_contra hlt
  push Not at hlt
  -- capacity ≥ the three arc sums
  have hcap := capacity_lower_bound G wΔ C
  -- demand splits over the cut into A-side and B-side source excess
  have hdemand : demand G wΔ
      = (∑ e ∈ cutA G wΔ C, max ((triThrough G e : ℝ) * wΔ - 1) 0)
        + (∑ e ∈ cutB G wΔ C, max ((triThrough G e : ℝ) * wΔ - 1) 0) := by
    rw [demand, cutA, cutB]
    exact (Finset.sum_filter_add_sum_filter_not G.edgeFinset _ _).symm
  -- reduced deficient-cut inequality: sink(A) + K₄-arcs(A→B) < source-excess(A)
  have hred : (∑ e ∈ cutA G wΔ C, max (1 - (triThrough G e : ℝ) * wΔ) 0)
        + (∑ e ∈ cutA G wΔ C, ∑ e' ∈ cutB G wΔ C, if K4pair G e e' then max (cc G wΔ) 0 else 0)
      < ∑ e ∈ cutA G wΔ C, max ((triThrough G e : ℝ) * wΔ - 1) 0 := by
    rw [hdemand] at hlt
    linarith
  -- source excess − sink deficit = signed excess (z₊ − (−z)₊ = z)
  have hid : (∑ e ∈ cutA G wΔ C, max ((triThrough G e : ℝ) * wΔ - 1) 0)
        - (∑ e ∈ cutA G wΔ C, max (1 - (triThrough G e : ℝ) * wΔ) 0)
      = ∑ e ∈ cutA G wΔ C, ((triThrough G e : ℝ) * wΔ - 1) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    rcases le_total 0 ((triThrough G e : ℝ) * wΔ - 1) with hz | hz
    · rw [max_eq_left hz, max_eq_right (by linarith)]; ring
    · rw [max_eq_right hz, max_eq_left (by linarith)]; ring
  -- K₄-arc sum < signed source excess over A
  have hred2 : (∑ e ∈ cutA G wΔ C, ∑ e' ∈ cutB G wΔ C,
        if K4pair G e e' then max (cc G wΔ) 0 else 0)
      < ∑ e ∈ cutA G wΔ C, ((triThrough G e : ℝ) * wΔ - 1) := by
    linarith
  -- demand > 0 forces an edge, hence card ≥ 2, hence cc > 0
  have hcapnn : 0 ≤ C.capacity :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => (drossNet G wΔ).capNonneg u v
  have hdpos : 0 < demand G wΔ := lt_of_le_of_lt hcapnn hlt
  have hcard2 : 2 ≤ Fintype.card V := by
    by_contra hc
    push Not at hc
    have : G.edgeFinset = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      rw [SimpleGraph.mem_edgeFinset] at he
      induction e using Sym2.inductionOn with
      | hf a b =>
        have : a ≠ b := (show G.Adj a b from he).ne
        have h2 : 2 ≤ Fintype.card V :=
          Finset.one_lt_card.mpr ⟨a, Finset.mem_univ _, b, Finset.mem_univ _, this⟩
        omega
    rw [demand, this] at hdpos; simp at hdpos
  have hden_pos : 0 < 3 * (G.minDegree : ℝ) - 3 := by
    have : (2 : ℝ) ≤ (G.minDegree : ℝ) := by exact_mod_cast hmd2
    nlinarith
  have hcc_pos : 0 < cc G wΔ := by rw [cc]; positivity
  have hcc_nn : 0 ≤ cc G wΔ := le_of_lt hcc_pos
  -- S_K4 lower bound: each A-edge contributes ≥ cc·(T_e(T_e−δn)/2 − |A|)
  have hSK4 : cc G wΔ * (∑ e ∈ cutA G wΔ C,
        ((triThrough G e : ℝ) * ((triThrough G e : ℝ) - δ * (Fintype.card V : ℝ)) / 2
          - (cutA G wΔ C).card))
      ≤ ∑ e ∈ cutA G wΔ C, ∑ e' ∈ cutB G wΔ C, if K4pair G e e' then max (cc G wΔ) 0 else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    have he_edge : e ∈ G.edgeFinset := (Finset.mem_filter.mp he).1
    -- inner sum = cc · #(cutB K4-partners)
    have hinner : (∑ e' ∈ cutB G wΔ C, if K4pair G e e' then max (cc G wΔ) 0 else 0)
        = cc G wΔ * (((cutB G wΔ C).filter (fun e' => K4pair G e e')).card : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, max_eq_left hcc_nn, mul_comm]
    rw [hinner]
    rw [SimpleGraph.mem_edgeFinset] at he_edge
    induction e using Sym2.inductionOn with
    | hf u v =>
      have huv : G.Adj u v := he_edge
      have hk4 := k4count_cutB_ge G huv wΔ C
      have hnum := numK4_lower_delta G h δ hδ_deg huv
      apply mul_le_mul_of_nonneg_left _ hcc_nn
      linarith
  -- Dross (1) in sum form
  have hineq1 : cc G wΔ * (∑ e ∈ cutA G wΔ C,
        ((triThrough G e : ℝ) * ((triThrough G e : ℝ) - δ * (Fintype.card V : ℝ)) / 2
          - (cutA G wΔ C).card))
      < ∑ e ∈ cutA G wΔ C, ((triThrough G e : ℝ) * wΔ - 1) := by
    linarith
  -- ==================== B side (symmetric) ====================
  -- balance ⇒ total sink deficit = M, split over the cut
  have hsinktotal : demand G wΔ = ∑ e ∈ G.edgeFinset, max (1 - (triThrough G e : ℝ) * wΔ) 0 := by
    have hid_all : (∑ e ∈ G.edgeFinset, max ((triThrough G e : ℝ) * wΔ - 1) 0)
          - (∑ e ∈ G.edgeFinset, max (1 - (triThrough G e : ℝ) * wΔ) 0)
        = ∑ e ∈ G.edgeFinset, ((triThrough G e : ℝ) * wΔ - 1) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro e _
      rcases le_total 0 ((triThrough G e : ℝ) * wΔ - 1) with hz | hz
      · rw [max_eq_left hz, max_eq_right (by linarith)]; ring
      · rw [max_eq_right hz, max_eq_left (by linarith)]; ring
    rw [hbal] at hid_all
    rw [demand]; linarith
  have hsink : demand G wΔ
      = (∑ e ∈ cutA G wΔ C, max (1 - (triThrough G e : ℝ) * wΔ) 0)
        + (∑ e ∈ cutB G wΔ C, max (1 - (triThrough G e : ℝ) * wΔ) 0) := by
    rw [hsinktotal, cutA, cutB]
    exact (Finset.sum_filter_add_sum_filter_not G.edgeFinset _ _).symm
  -- B-side S_K4 lower bound
  have hSK4B : cc G wΔ * (∑ e ∈ cutB G wΔ C,
        ((triThrough G e : ℝ) * ((triThrough G e : ℝ) - δ * (Fintype.card V : ℝ)) / 2
          - (cutB G wΔ C).card))
      ≤ ∑ e ∈ cutA G wΔ C, ∑ e' ∈ cutB G wΔ C, if K4pair G e e' then max (cc G wΔ) 0 else 0 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e' he'
    have he'_edge : e' ∈ G.edgeFinset := (Finset.mem_filter.mp he').1
    have hinner : (∑ e ∈ cutA G wΔ C, if K4pair G e e' then max (cc G wΔ) 0 else 0)
        = cc G wΔ * (((cutA G wΔ C).filter (fun e => K4pair G e e')).card : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, max_eq_left hcc_nn, mul_comm]
    rw [hinner]
    rw [SimpleGraph.mem_edgeFinset] at he'_edge
    induction e' using Sym2.inductionOn with
    | hf u v =>
      have huv : G.Adj u v := he'_edge
      have hfilt : (cutA G wΔ C).filter (fun e => K4pair G e (s(u, v)))
          = (cutA G wΔ C).filter (fun e => K4pair G (s(u, v)) e) := by
        apply Finset.filter_congr; intro e _; rw [k4pair_symm]
      rw [hfilt]
      have hk4 := k4count_cutA_ge G huv wΔ C
      have hnum := numK4_lower_delta G h δ hδ_deg huv
      apply mul_le_mul_of_nonneg_left _ hcc_nn
      linarith
  -- Dross (2) in sum form
  have hidB : (∑ e ∈ cutB G wΔ C, max (1 - (triThrough G e : ℝ) * wΔ) 0)
        - (∑ e ∈ cutB G wΔ C, max ((triThrough G e : ℝ) * wΔ - 1) 0)
      = ∑ e ∈ cutB G wΔ C, (1 - (triThrough G e : ℝ) * wΔ) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    rcases le_total 0 ((triThrough G e : ℝ) * wΔ - 1) with hz | hz
    · rw [max_eq_left hz, max_eq_right (by linarith)]; ring
    · rw [max_eq_right hz, max_eq_left (by linarith)]; ring
  have hineq2 : cc G wΔ * (∑ e ∈ cutB G wΔ C,
        ((triThrough G e : ℝ) * ((triThrough G e : ℝ) - δ * (Fintype.card V : ℝ)) / 2
          - (cutB G wΔ C).card))
      < ∑ e ∈ cutB G wΔ C, (1 - (triThrough G e : ℝ) * wΔ) := by
    linarith
  -- ==================== finish: apply deficient_finish ====================
  rcases (cutA G wΔ C).eq_empty_or_nonempty with hAe | hAne
  · rw [hAe] at hineq1; simp at hineq1
  rcases (cutB G wΔ C).eq_empty_or_nonempty with hBe | hBne
  · rw [hBe] at hineq2; simp at hineq2
  have hccrel : 2 * wΔ = cc G wΔ * (3 * (Fintype.card V : ℝ) * (1 - δ) - 3) := by
    rw [cc, show 3 * (Fintype.card V : ℝ) * (1 - δ) - 3
          = 3 * (G.minDegree : ℝ) - 3 from by nlinarith [hδ_eq]]
    exact (div_mul_cancel₀ _ (ne_of_gt hden_pos)).symm
  have hTA : ∀ e ∈ cutA G wΔ C, (1 - 2 * δ) * (Fintype.card V : ℝ) ≤ (triThrough G e : ℝ)
      ∧ (triThrough G e : ℝ) ≤ (Fintype.card V : ℝ) := by
    intro e he
    have he_edge := (Finset.mem_filter.mp he).1
    rw [SimpleGraph.mem_edgeFinset] at he_edge
    induction e using Sym2.inductionOn with
    | hf u v => exact triThrough_bounds_delta G δ hδ_deg he_edge
  have hTB : ∀ e ∈ cutB G wΔ C, (1 - 2 * δ) * (Fintype.card V : ℝ) ≤ (triThrough G e : ℝ)
      ∧ (triThrough G e : ℝ) ≤ (Fintype.card V : ℝ) := by
    intro e he
    have he_edge := (Finset.mem_filter.mp he).1
    rw [SimpleGraph.mem_edgeFinset] at he_edge
    induction e using Sym2.inductionOn with
    | hf u v => exact triThrough_bounds_delta G δ hδ_deg he_edge
  have hcard_m : ((cutA G wΔ C).card : ℝ) + ((cutB G wΔ C).card : ℝ)
      = (G.edgeFinset.card : ℝ) := by
    rw [cutA, cutB]
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := G.edgeFinset)
      (fun e => Ghat.edge e ∈ C.S)
  have hn20R : (20 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn20
  exact deficient_finish_exact (cutA G wΔ C) (cutB G wΔ C) hAne hBne (fun e => (triThrough G e : ℝ))
    (Fintype.card V : ℝ) (G.edgeFinset.card : ℝ) (cc G wΔ) wΔ δ hδ0 hδ1 hn20R hcc_pos
    hccrel hcard_m hTA hTB hmbound hineq1 hineq2

end LeanPool.DrossFractionalTriangleDecomposition
