/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.CutCapacity
import Mathlib.Tactic.Linarith

/-!
# K₄ partners across a cut

The partners of a graph edge split disjointly between the two cut sides.
One partition identity supplies both directional lower bounds.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The K₄ partners of an edge are partitioned by the cut. -/
public theorem k4count_cut_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (huv : G.Adj u v) (wΔ : ℝ)
    (C : Contrib.MaxFlowMinCut.Cut (drossNet G wΔ)) :
    numK4Through G u v =
      ((cutA G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')).card +
      ((cutB G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')).card := by
  have hpart : G.edgeFinset.filter (fun e' => K4pair G (s(u, v)) e') =
      (cutA G wΔ C).filter (fun e' => K4pair G (s(u, v)) e') ∪
      (cutB G wΔ C).filter (fun e' => K4pair G (s(u, v)) e') := by
    unfold cutA cutB
    rw [Finset.filter_filter, Finset.filter_filter, ← Finset.filter_or]
    apply Finset.filter_congr
    intro e' _
    tauto
  have hdisj : Disjoint
      ((cutA G wΔ C).filter (fun e' => K4pair G (s(u, v)) e'))
      ((cutB G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')) := by
    rw [Finset.disjoint_left]
    intro e he he'
    rw [Finset.mem_filter, cutA, Finset.mem_filter] at he
    rw [Finset.mem_filter, cutB, Finset.mem_filter] at he'
    exact he'.1.2 he.1.2
  rw [← k4pair_count_eq G huv, hpart, Finset.card_union_of_disjoint hdisj]

/-- An A-side edge has at least its total partner count minus |A| partners in B. -/
public theorem k4count_cutB_ge (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (huv : G.Adj u v) (wΔ : ℝ)
    (C : Contrib.MaxFlowMinCut.Cut (drossNet G wΔ)) :
    (numK4Through G u v : ℝ) - ((cutA G wΔ C).card : ℝ) ≤
      (((cutB G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')).card : ℝ) := by
  have hAle : ((cutA G wΔ C).filter (fun e' =>
      K4pair G (s(u, v)) e')).card ≤ (cutA G wΔ C).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hcard := k4count_cut_partition G huv wΔ C
  have hAle' : (((cutA G wΔ C).filter (fun e' =>
      K4pair G (s(u, v)) e')).card : ℝ) ≤ ((cutA G wΔ C).card : ℝ) := by
    exact_mod_cast hAle
  have hcard' : (numK4Through G u v : ℝ) =
      (((cutA G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')).card : ℝ) +
      (((cutB G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')).card : ℝ) := by
    exact_mod_cast hcard
  linarith

/-- A B-side edge has at least its total partner count minus |B| partners in A. -/
public theorem k4count_cutA_ge (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (huv : G.Adj u v) (wΔ : ℝ)
    (C : Contrib.MaxFlowMinCut.Cut (drossNet G wΔ)) :
    (numK4Through G u v : ℝ) - ((cutB G wΔ C).card : ℝ) ≤
      (((cutA G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')).card : ℝ) := by
  have hBle : ((cutB G wΔ C).filter (fun e' =>
      K4pair G (s(u, v)) e')).card ≤ (cutB G wΔ C).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hcard := k4count_cut_partition G huv wΔ C
  have hBle' : (((cutB G wΔ C).filter (fun e' =>
      K4pair G (s(u, v)) e')).card : ℝ) ≤ ((cutB G wΔ C).card : ℝ) := by
    exact_mod_cast hBle
  have hcard' : (numK4Through G u v : ℝ) =
      (((cutA G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')).card : ℝ) +
      (((cutB G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')).card : ℝ) := by
    exact_mod_cast hcard
  linarith

end LeanPool.DrossFractionalTriangleDecomposition
