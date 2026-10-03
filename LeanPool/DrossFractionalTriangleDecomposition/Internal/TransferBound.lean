/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.K4PartnerCount
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bounded K₄ transfer

The partner count and arc capacities bound the total transfer from a
triangle by twice its initial weight. No enlarged heartbeat limit is needed.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- If no triangle has all three vertices of degree at least `δ(G)+2`,
the total rooted-K₄ flow transfer out of a triangle is at most `2 wΔ`. -/
public theorem triWeight_transfer_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (wΔ : ℝ) (hwΔ : 0 < wΔ) (hmd2 : 2 ≤ G.minDegree)
    (F : Contrib.MaxFlowMinCut.Flow (drossNet G wΔ))
    (hNoHDT : ∀ u v w : V, G.Adj u v → G.Adj u w → G.Adj v w →
      G.minDegree + 2 ≤ G.degree u → G.minDegree + 2 ≤ G.degree v →
      G.minDegree + 2 ≤ G.degree w → False)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    (∑ e ∈ triEdges t, ∑ e' : Sym2 V,
      (if K4pair G e e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e then
        F.f (Ghat.edge e) (Ghat.edge e') else 0)) ≤ 2 * wΔ := by
  have hmd2R : (2 : ℝ) ≤ (G.minDegree : ℝ) := by exact_mod_cast hmd2
  have hden : (0 : ℝ) < 3 * (G.minDegree : ℝ) - 3 := by nlinarith
  have hcc_nn : 0 ≤ cc G wΔ := by rw [cc]; positivity
  have hccval : (3 * ((G.minDegree : ℝ) - 1)) * cc G wΔ = 2 * wΔ := by
    have hne : (3 * (G.minDegree : ℝ) - 3) ≠ 0 := ne_of_gt hden
    rw [cc, show (3 * ((G.minDegree : ℝ) - 1)) =
      (3 * (G.minDegree : ℝ) - 3) from by ring,
      div_eq_mul_inv, mul_left_comm, mul_inv_cancel₀ hne, mul_one]
  have htcard : (triEdges t).card = 3 :=
    triEdges_card_of_isNClique G ((SimpleGraph.mem_cliqueFinset_iff).mp ht)
  obtain ⟨z, hzt, hzdeg⟩ : ∃ z ∈ t, G.degree z ≤ G.minDegree + 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, b, c, hab, hac, hbc, hts⟩ :=
      is3Clique_iff.mp ((SimpleGraph.mem_cliqueFinset_iff).mp ht)
    subst hts
    exact hNoHDT a b c hab hac hbc
      (by have := hcon a (by simp); omega)
      (by have := hcon b (by simp); omega)
      (by have := hcon c (by simp); omega)
  have hcount := k4_partner_count_le G t ht z hzt hzdeg
  have hper : ∀ e ∈ triEdges t,
      (∑ e' : Sym2 V, if K4pair G e e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e then
        F.f (Ghat.edge e) (Ghat.edge e') else 0) ≤
        ((G.minDegree : ℝ) - 1) * cc G wΔ := by
    intro e he
    set Se := (Finset.univ : Finset (Sym2 V)).filter
      (fun e' => K4pair G e e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e) with hSe
    calc
      (∑ e' : Sym2 V, if K4pair G e e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e then
            F.f (Ghat.edge e) (Ghat.edge e') else 0)
          = ∑ e' ∈ Se, F.f (Ghat.edge e) (Ghat.edge e') := by
              rw [hSe, Finset.sum_filter]
      _ ≤ ∑ _e' ∈ Se, cc G wΔ := by
          apply Finset.sum_le_sum
          intro e' he'
          have hk4 : K4pair G e e' := (Finset.mem_filter.mp he').2.1
          have hcap := F.capacitated (Ghat.edge e) (Ghat.edge e')
          simp only [drossNet, dcap, ite_eq_left hk4] at hcap
          rwa [max_eq_left hcc_nn] at hcap
      _ = (Se.card : ℝ) * cc G wΔ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((G.minDegree : ℝ) - 1) * cc G wΔ :=
        mul_le_mul_of_nonneg_right (hcount e he) hcc_nn
  calc
    (∑ e ∈ triEdges t, ∑ e' : Sym2 V,
        if K4pair G e e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e then
          F.f (Ghat.edge e) (Ghat.edge e') else 0)
        ≤ ∑ _e ∈ triEdges t, ((G.minDegree : ℝ) - 1) * cc G wΔ :=
          Finset.sum_le_sum hper
    _ = ((triEdges t).card : ℝ) * (((G.minDegree : ℝ) - 1) * cc G wΔ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = 2 * wΔ := by rw [htcard]; push_cast; linarith [hccval]

/-- Each reconstructed triangle weight is nonnegative. -/
public theorem triWeight_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (wΔ : ℝ) (hwΔ : 0 < wΔ) (hmd2 : 2 ≤ G.minDegree)
    (F : Contrib.MaxFlowMinCut.Flow (drossNet G wΔ))
    (hNoHDT : ∀ u v w : V, G.Adj u v → G.Adj u w → G.Adj v w →
      G.minDegree + 2 ≤ G.degree u → G.minDegree + 2 ≤ G.degree v →
      G.minDegree + 2 ≤ G.degree w → False)
    (t : Finset V) : 0 ≤ triWeight G wΔ F t := by
  rw [triWeight]
  split_ifs with ht
  · have hb := triWeight_transfer_le G wΔ hwΔ hmd2 F hNoHDT t ht
    linarith
  · exact le_refl 0

end LeanPool.DrossFractionalTriangleDecomposition
