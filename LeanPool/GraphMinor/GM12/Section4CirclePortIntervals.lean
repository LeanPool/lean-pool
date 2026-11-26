/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CircleMove
public import Mathlib.Order.Fin.Basic
import LeanPool.GraphMinor.GM12.Section4OrderedPortIntervals

/-!
# Ordered circle arcs in prescribed vertex neighborhoods

The circle centers of the vertex blocks in XII (4.5), page 253,
are chosen within one full turn. Pull the open vertex neighborhoods
back to the angle line, and choose ordered intervals there. Every
choice of a port inside its interval stays in its vertex
neighborhood and keeps the prescribed order.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Choose ordered port intervals inside the assigned open vertex
neighborhoods, with all intervals in one full turn. These intervals
can be passed to the general-position chord selection for XII (4.5),
page 253. -/
theorem exists_ordered_circle_port_intervals {n : ℕ} (c : Fin n → ℝ)
    (hc : Monotone c) (hc01 : ∀ i, c i ∈ Ioo 0 1)
    (O : Fin n → Set ℂ) (hO : ∀ i, IsOpen (O i))
    (hcO : ∀ i, (ee (c i) : ℂ) ∈ O i) :
    ∃ u v : Fin n → ℝ,
      (∀ i, 0 ≤ u i ∧ u i < v i ∧ v i ≤ 1 ∧
        ∀ t ∈ Ioo (u i) (v i), (ee t : ℂ) ∈ O i) ∧
      ∀ i j, i < j → v i < u j := by
  let U : Fin n → Set ℝ := fun i => Ioo 0 1 ∩ (fun t : ℝ => (ee t : ℂ)) ⁻¹' O i
  have hU : ∀ i, IsOpen (U i) := fun i =>
    isOpen_Ioo.inter ((hO i).preimage continuous_ee.subtype_val)
  have hcU : ∀ i, c i ∈ U i := fun i => ⟨hc01 i, hcO i⟩
  obtain ⟨u, v, huv, horder⟩ := exists_ordered_port_intervals c hc U hU hcU
  refine ⟨u, v, ?_, horder⟩
  intro i
  have hsub : Ioo (u i) (v i) ⊆ Ioo (0 : ℝ) 1 :=
    (huv i).2.trans inter_subset_left
  have hbounds := (Ioo_subset_Ioo_iff (huv i).1).mp hsub
  exact ⟨hbounds.1, (huv i).1, hbounds.2, fun t ht => ((huv i).2 ht).2⟩

end GraphMinor.GM12
