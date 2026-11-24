/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4LocalCrossDiscs
import Mathlib.Topology.Separation.Hausdorff

/-!
# Disjoint discs around all crossings

For XII (4.5), claim (1), page 253, separate the finitely many
crossing points by disjoint open neighborhoods. Intersect each
with its local straight-line neighborhood, then choose the small
coordinate disc there. The discs are disjoint, and each retains
the exact two opposite boundary contacts for both crossing arcs.
-/

public section

namespace GraphMinor.GM12

open Set Surface

universe u

/-- A finite family of locally straight crossings has disjoint
small closed discs with the prescribed opposite boundary pairs,
as used in XII (4.5), claim (1), page 253. -/
theorem exists_local_cross_disc_family {ι : Type u} [Finite ι]
    (x : ι → ℂ) (hinj : Function.Injective x) (A : ι → ℂ ≃L[ℝ] ℂ)
    (E F U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i)) (hx : ∀ i, x i ∈ U i)
    (hE : ∀ i, E i ∩ U i = (line[ℝ, x i, x i + A i 1] : Set ℂ) ∩ U i)
    (hF : ∀ i, F i ∩ U i = (line[ℝ, x i, x i + A i Complex.I] : Set ℂ) ∩ U i) :
    ∃ r : ι → ℝ, (∀ i, 0 < r i) ∧ ∃ D : ι → Set ℂ,
      (∀ i, IsClosedDisc (D i)) ∧ (∀ i, D i ⊆ U i) ∧
      (∀ i j, i ≠ j → Disjoint (D i) (D j)) ∧
      (∀ i, E i ∩ discBd (D i) =
        {x i + A i (r i • (1 : ℂ)), x i + A i ((-r i) • (1 : ℂ))}) ∧
      (∀ i, F i ∩ discBd (D i) =
        {x i + A i (r i • Complex.I), x i + A i ((-r i) • Complex.I)}) ∧
      (∀ i, D i = (fun z => x i + A i z) '' Metric.closedBall 0 (r i)) := by
  classical
  obtain ⟨W, hW, hWdisj⟩ := (finite_range x).t2_separation
  have hex : ∀ i, ∃ r : ℝ, 0 < r ∧ ∃ D : Set ℂ,
      IsClosedDisc D ∧ D ⊆ U i ∩ W (x i) ∧
      E i ∩ discBd D = {x i + A i (r • (1 : ℂ)), x i + A i ((-r) • (1 : ℂ))} ∧
      F i ∩ discBd D = {x i + A i (r • Complex.I), x i + A i ((-r) • Complex.I)} ∧
      D = (fun z => x i + A i z) '' Metric.closedBall 0 r := by
    intro i
    apply exists_local_cross_disc (A i) (x i) ((hU i).inter (hW (x i)).2)
      ⟨hx i, (hW (x i)).1⟩
    · rw [← inter_assoc, hE i, inter_assoc]
    · rw [← inter_assoc, hF i, inter_assoc]
  choose r hr D hD hsub hEM hFM hcoord using hex
  refine ⟨r, hr, D, hD, (fun i z hz => (hsub i hz).1), ?_, hEM, hFM, hcoord⟩
  intro i j hij
  exact (hWdisj (mem_range_self i) (mem_range_self j) (fun h => hij (hinj h))).mono
    (fun z hz => (hsub i hz).2) (fun z hz => (hsub j hz).2)

end GraphMinor.GM12
