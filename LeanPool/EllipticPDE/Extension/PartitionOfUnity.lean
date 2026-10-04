/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Extension.C1Boundary
public import Mathlib.Geometry.Manifold.PartitionOfUnity


/-!
# Partition of unity over a finite cover of the boundary

Guo's third step covers the boundary with finitely many chart neighbourhoods and glues the local
extensions with a partition of unity. This file supplies the partition, and bundles it with the
cover into the data that step consumes.

Mathlib states its smooth partitions of unity for a manifold, and a normed space is a manifold
over itself, so the statement applies here once the smoothness of a bundled map is read back as
`ContDiff`. `exists_smooth_partition` does that reading, so nothing downstream of this file meets
a manifold.

The index of the partition is an `Option`: the piece indexed `none` sits inside the domain, away
from the boundary, and the piece indexed `some x` sits in the ball of the chart at the boundary
point `x`. The pieces add to one on the closure of the domain, as the sum of the local
extensions requires.

## Main declarations

* `EllipticPdes.Extension.exists_smooth_partition`: a smooth partition of unity subordinate to a
  finite open cover, stated with `ContDiff`.
* `EllipticPdes.Extension.exists_cutoff_one_on_ball`: a smooth cutoff between two balls.
* `EllipticPdes.Extension.BoundaryPartition`: the cover and the partition together.
* `EllipticPdes.Extension.nonempty_boundaryPartition`: every bounded domain with `C¹` boundary
  admits one.

## References

Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem III.2.2
(p. 20), proof step 3 (p. 21); L. C. Evans, *Partial Differential Equations* (2nd ed.),
§5.4 Theorem 1 (p. 253).
-/

@[expose] public section

open Metric Set
open scoped Manifold

noncomputable section

namespace EllipticPdes.Extension

variable {d : ℕ}

/-- **Smooth partition of unity subordinate to a finite open cover**, with the smoothness of
each piece stated as `ContDiff` rather than through the manifold structure Mathlib proves it
in. -/
theorem exists_smooth_partition {ι : Type} [Fintype ι]
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : IsClosed s)
    (U : ι → Set (EuclideanSpace ℝ (Fin d))) (ho : ∀ i, IsOpen (U i)) (hU : s ⊆ ⋃ i, U i) :
    ∃ ζ : ι → EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (ζ i)) ∧ (∀ i x, 0 ≤ ζ i x) ∧
      (∀ i, tsupport (ζ i) ⊆ U i) ∧ (∀ x ∈ s, ∑ i, ζ i x = 1) := by
  obtain ⟨f, hfU⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d))) hs U ho hU
  refine ⟨fun i => (f i : EuclideanSpace ℝ (Fin d) → ℝ), ?_, ?_, ?_, ?_⟩
  · intro i
    exact contMDiff_iff_contDiff.mp (f i).contMDiff
  · exact f.nonneg
  · exact hfU
  · intro x hx
    rw [← finsum_eq_sum_of_fintype]
    exact f.sum_eq_one hx


/-- **Smooth cutoff equal to one on a closed ball and supported in a larger one.** Guo's third
step asks the support of each piece of the partition to sit compactly inside its neighbourhood,
and the local extension of step 2 reads the class on a neighbourhood of that support, so a
cutoff between two balls is what mediates the two. -/
theorem exists_cutoff_one_on_ball (x : EuclideanSpace ℝ (Fin d)) {r R : ℝ} (hrR : r < R) :
    ∃ ξ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ξ ∧
      (∀ y ∈ closedBall x r, ξ y = 1) ∧ tsupport ξ ⊆ ball x R := by
  obtain ⟨t, hrt, htR⟩ := exists_between hrR
  obtain ⟨f, hf0, hf1, -⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
      (isOpen_ball (x := x) (ε := t)).isClosed_compl
      (isClosed_closedBall (x := x) (ε := r))
      (by
        rw [Set.disjoint_compl_left_iff_subset]
        exact closedBall_subset_ball hrt)
  refine ⟨fun y => f y, contMDiff_iff_contDiff.mp f.contMDiff, fun y hy => hf1 hy, ?_⟩
  refine (closure_minimal ?_ (isClosed_closedBall (x := x) (ε := t))).trans
    (closedBall_subset_ball htR)
  intro y hy
  by_contra hc
  exact hy (hf0 fun hcc => hc (ball_subset_closedBall hcc))

/-- **Data Guo's third step glues with.** A finite family of boundary charts whose balls
cover the boundary, and a smooth partition of unity subordinate to those balls together with the
domain itself. The index `none` is the piece supported inside the domain, away from the
boundary; each `some x` is the piece supported in the ball of the chart at `x`. -/
structure BoundaryPartition (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) where
  /-- The boundary points the charts are taken at. -/
  centres : Finset (EuclideanSpace ℝ (Fin d))
  /-- The chart at each of them. -/
  chart : EuclideanSpace ℝ (Fin d) → C1Chart d
  /-- The pieces of the partition. -/
  part : Option {x // x ∈ centres} → EuclideanSpace ℝ (Fin d) → ℝ
  /-- Every centre is a boundary point. -/
  centres_mem : ∀ x ∈ centres, x ∈ frontier Ω
  /-- The chart at a centre describes the domain there. -/
  chart_fits : ∀ x ∈ centres, (chart x).Fits Ω x
  /-- Every piece is smooth. -/
  part_contDiff : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (part i)
  /-- Every piece is nonnegative. -/
  part_nonneg : ∀ i x, 0 ≤ part i x
  /-- The interior piece is supported inside the domain. -/
  part_interior : tsupport (part none) ⊆ Ω
  /-- Each boundary piece is supported in its chart's ball. -/
  part_boundary : ∀ x : {x // x ∈ centres},
    tsupport (part (some x)) ⊆ Metric.ball (x : EuclideanSpace ℝ (Fin d)) (chart x).radius
  /-- The pieces add to one on the closure of the domain. -/
  part_sum : ∀ x ∈ closure Ω, ∑ i, part i x = 1

/-- **Every bounded domain with `C¹` boundary admits such a partition.** -/
theorem nonempty_boundaryPartition (hd : 0 < d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩopen : IsOpen Ω) (hΩ : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω) :
    Nonempty (BoundaryPartition d Ω) := by
  classical
  obtain ⟨F, c, hmem, hfits, hcover⟩ := exists_finite_chart_cover hd hΩ hC1
  set U : Option {x // x ∈ F} → Set (EuclideanSpace ℝ (Fin d)) :=
    fun i => i.elim Ω (fun x => Metric.ball (x : EuclideanSpace ℝ (Fin d)) (c x).radius)
    with hUdef
  have ho : ∀ i, IsOpen (U i) := by
    rintro (_ | x)
    · exact hΩopen
    · exact Metric.isOpen_ball
  have hU : closure Ω ⊆ ⋃ i, U i := by
    intro y hy
    by_cases hyΩ : y ∈ Ω
    · exact Set.mem_iUnion.mpr ⟨none, hyΩ⟩
    · have hyf : y ∈ frontier Ω := ⟨hy, by rwa [hΩopen.interior_eq]⟩
      obtain ⟨x, hxF, hyx⟩ := Set.mem_iUnion₂.mp (hcover hyf)
      exact Set.mem_iUnion.mpr ⟨some ⟨x, hxF⟩, hyx⟩
  obtain ⟨ζ, hζc, hζ0, hζs, hζ1⟩ :=
    exists_smooth_partition (isClosed_closure (s := Ω)) U ho hU
  exact ⟨{ centres := F, chart := c, part := ζ
           centres_mem := hmem, chart_fits := hfits
           part_contDiff := hζc, part_nonneg := hζ0
           part_interior := hζs none
           part_boundary := fun x => hζs (some x)
           part_sum := hζ1 }⟩

end EllipticPdes.Extension
