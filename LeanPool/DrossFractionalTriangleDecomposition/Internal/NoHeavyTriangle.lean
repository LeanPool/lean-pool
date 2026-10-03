/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.EdgeCountBound
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Dross's theorem without a high-degree triangle

The small and complete cases are elementary. Otherwise the exact high-degree
and edge-count estimates imply the cut hypothesis, so the saturating flow
gives the desired fractional triangle decomposition.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact Dross decomposition when no triangle has all three vertices of
degree at least `minDegree + 2`. -/
public theorem dross_fractional_flow_noHDT_exact (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree)
    (hNoHDT : ∀ u v w : V, G.Adj u v → G.Adj u w → G.Adj v w →
      G.minDegree + 2 ≤ G.degree u → G.minDegree + 2 ≤ G.degree v →
      G.minDegree + 2 ≤ G.degree w → False) :
    FractionalTriangleDecomp G := by
  rcases lt_or_ge (Fintype.card V) 20 with hlt | hn20
  · exact dross_fractional_small G h hlt
  by_cases hm : G.edgeFinset = ∅
  · exact ⟨fun _ => 0, fun _ => le_refl 0,
      fun e he => absurd (hm ▸ he) (Finset.notMem_empty e)⟩
  · have hmne : G.edgeFinset.Nonempty := Finset.nonempty_iff_ne_empty.mpr hm
    have hT : 0 < (G.cliqueFinset 3).card := exists_triangle_of_edge G h hmne
    have hmpos : 0 < (G.edgeFinset.card : ℝ) := by
      have hc := Finset.card_pos.mpr hmne
      exact_mod_cast hc
    set wΔ : ℝ := (G.edgeFinset.card : ℝ) / (3 * (G.cliqueFinset 3).card) with hwΔeq
    have hwΔ : 0 < wΔ := by rw [hwΔeq]; positivity
    have hbal := balance G hT hwΔeq
    have hcardpos : 0 < Fintype.card V := by omega
    have hcardposR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hcardpos
    obtain ⟨v0⟩ := Fintype.card_pos_iff.mp hcardpos
    have hmle : G.minDegree ≤ Fintype.card V - 1 := by
      have hv := G.degree_lt_card_verts v0
      exact le_trans (G.minDegree_le_degree v0) (by omega)
    have hmclt : G.minDegree < Fintype.card V := by omega
    have hmd2 : 2 ≤ G.minDegree := by
      have h180 : 180 ≤ 10 * G.minDegree := le_trans (by omega) h
      omega
    set δ : ℝ := ((Fintype.card V : ℝ) - G.minDegree) / Fintype.card V with hδdef
    have hδ_eq : (Fintype.card V : ℝ) - G.minDegree = δ * (Fintype.card V : ℝ) := by
      rw [hδdef]
      field_simp
    have hδ0 : 0 < δ := by
      rw [hδdef]
      apply div_pos _ hcardposR
      have hc : (G.minDegree : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hmclt
      linarith
    have hδ1 : δ ≤ 1 / 10 := by
      rw [hδdef, div_le_iff₀ hcardposR]
      have hc : (9 : ℝ) * Fintype.card V ≤ 10 * G.minDegree := by exact_mod_cast h
      linarith
    rcases Nat.lt_or_ge (Fintype.card V - G.minDegree) 2 with hdef1 | hdef2
    · have hmin_eq : G.minDegree = Fintype.card V - 1 := by omega
      exact complete_fractional G hmin_eq (by omega)
    · have hδn2 : (2 : ℝ) ≤ δ * (Fintype.card V : ℝ) := by
        rw [← hδ_eq]
        have hc : (2 : ℝ) ≤ ((Fintype.card V - G.minDegree : ℕ) : ℝ) := by
          exact_mod_cast hdef2
        rwa [Nat.cast_sub (show G.minDegree ≤ Fintype.card V by omega)] at hc
      have hmbound : 2 * (G.edgeFinset.card : ℝ)
          ≤ (1 - δ + 2 * δ ^ 2) * (Fintype.card V : ℝ) ^ 2 + 4
            + (Fintype.card V : ℝ) - 6 * δ * (Fintype.card V : ℝ) := by
        have hnb_nat := nb_bound_tight G h hn20 hdef2 hNoHDT
        have hcast :
            ((Finset.univ.filter (fun v => G.minDegree + 2 ≤ G.degree v)).card : ℝ)
              ≤ 2 * δ * (Fintype.card V : ℝ) - 4 := by
          have hnb_R :
              ((Finset.univ.filter (fun v => G.minDegree + 2 ≤ G.degree v)).card : ℝ)
                ≤ ((2 * (Fintype.card V - G.minDegree) - 4 : ℕ) : ℝ) := by
            exact_mod_cast hnb_nat
          have hcastR : ((2 * (Fintype.card V - G.minDegree) - 4 : ℕ) : ℝ)
              = 2 * ((Fintype.card V : ℝ) - G.minDegree) - 4 := by
            rw [Nat.cast_sub (show 4 ≤ 2 * (Fintype.card V - G.minDegree) by omega),
              Nat.cast_mul, Nat.cast_sub (show G.minDegree ≤ Fintype.card V by omega)]
            push_cast
            ring
          rw [hcastR] at hnb_R
          nlinarith [hnb_R, hδ_eq]
        exact mbound_tight G δ h hn20 hδ_eq hδn2 hcast
      obtain ⟨F, hF⟩ :=
        exists_flow_M_exact G h wΔ hwΔ hbal δ hδ0 hδ1 hn20 hmd2 hδ_eq hmbound
      exact decomp_of_maxflowM G wΔ hwΔ hmd2 hbal F hF hNoHDT

end LeanPool.DrossFractionalTriangleDecomposition
