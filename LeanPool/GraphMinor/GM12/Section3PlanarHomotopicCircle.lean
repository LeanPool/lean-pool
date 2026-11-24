/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Cited
public import LeanPool.GraphMinor.Surface.DiscGrow
public import LeanPool.GraphMinor.GM12.Section3CapTopology
public import LeanPool.GraphMinor.GM12.Section3CapComparison
public import LeanPool.GraphMinor.GM12.Section3CircleInclusion
import LeanPool.GraphMinor.GM12.Section3ThetaHomotopy
import LeanPool.GraphMinor.GM12.Section3PlanarityMaps
import LeanPool.GraphMinor.GM12.Section3FiniteGraphSolid
import LeanPool.GraphMinor.GM12.Section2ArcHomotopy

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Reading a preserved circle homotopy inside a cap

The finite graph in the circle-intersection step used by XII (3.1),
page 245, retains two fixed-end path homotopies from the second circle.
If the new paths lie in a planar set, they are homotopic through its
containing disc. The original circle is therefore null-homotopic.
VII (5.1) makes a proper null-homotopic circle planar. In a cap,
properness follows from the added disc interior, and cap comparison
supplies the universal planarity condition.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

universe u

/-- A proper null-homotopic circle is planar, by VII (5.1).
Its only subcircle is itself, and circles are solid. -/
theorem planar_oArc_of_null
    {S : Type u} [TopologicalSpace S] (hS : IsSurface S) (hconn : ConnectedSpace S)
    {A : Set S} (hA : IsOArc A) (hproper : A ≠ univ) (hnull : IsNullHomotopicOArc A) :
    IsPlanar A := by
  let := hS.2.1
  apply (GraphMinor.GM07.gm07_theorem_5_1 S hS hconn A (isSolid_oArc hA) hproper).mpr
  intro Z hZ hZA
  rw [oArc_eq_of_subset hZ hA hZA]
  exact hnull

/-- If the two arcs of a circle are homotopic to paths in one planar
set, the original circle is null-homotopic. -/
theorem null_circle_of_homotopic_paths_in_planar_set
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {x y : S} (p q r s : Path x y) (hPQ : IsTwoArcs p q) {A G : Set S}
    (hAeq : range p ∪ range q = A) (hpr : p.Homotopic r) (hqs : q.Homotopic s)
    (hpaths : range r ∪ range s ⊆ G) (hplan : IsPlanar G) : IsNullHomotopicOArc A := by
  have hrs := paths_homotopic_of_planar_union r s (isPlanar_mono hpaths hplan)
  have hpq : p.Homotopic q := hpr.trans (hrs.trans hqs.symm)
  have hnull := nullHomotopic_union_of_homotopic_arcs p q hPQ.arc_left.2 hPQ.arc_right.2 hPQ.meet
    hpq
  rw [hAeq] at hnull
  exact hnull

/-- Preserving the two arc homotopies of a circle inside a set makes
planarity of that set in a cap imply planarity of the original circle
in the same cap. -/
theorem planarInCappedCuff_of_homotopic_paths
    {S : Type u} [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S)
    {x y : S} (p q r s : Path x y) (hPQ : IsTwoArcs p q) {A G C : Set S}
    (hA : IsOArc A) (hAeq : range p ∪ range q = A)
    (hpr : p.Homotopic r) (hqs : q.Homotopic s) (hpaths : range r ∪ range s ⊆ G)
    (hplan : GM07.IsPlanarInCappedCuff C G) : GM07.IsPlanarInCappedCuff C A := by
  obtain ⟨T, tT, j, D, hcap⟩ := exists_cappedCuff hS hplan.1
  let := tT
  let : T2Space T := hcap.isSurface.2.1
  have hconn : ConnectedSpace T := cappedCuff_connectedSpace hcap
  let J : C(S, T) := ⟨j, hcap.isEmbedding.continuous⟩
  have hrange : ∀ v : Path x y, range (v.map J.continuous) = j '' range v :=
    fun v => Set.range_comp j v
  have hPQ' : IsTwoArcs (p.map J.continuous) (q.map J.continuous) := by
    refine ⟨⟨(p.map J.continuous).continuous, hcap.isEmbedding.injective.comp hPQ.arc_left.2⟩,
      ⟨(q.map J.continuous).continuous, hcap.isEmbedding.injective.comp hPQ.arc_right.2⟩,
      congrArg j hPQ.zero, congrArg j hPQ.one, ?_⟩
    intro a b he
    exact hPQ.meet a b (hcap.isEmbedding.injective he)
  have hAeq' : range (p.map J.continuous) ∪ range (q.map J.continuous) = j '' A := by
    rw [hrange, hrange, ← image_union, hAeq]
  have hpaths' : range (r.map J.continuous) ∪ range (s.map J.continuous) ⊆ j '' G := by
    rw [hrange, hrange, ← image_union]
    exact image_mono hpaths
  have hnull := null_circle_of_homotopic_paths_in_planar_set
    (p.map J.continuous) (q.map J.continuous) (r.map J.continuous) (s.map J.continuous)
    hPQ' hAeq' (hpr.map J) (hqs.map J) hpaths' (hplan.2.2 T j D hcap)
  have hAo : IsOArc (j '' A) := by
    obtain ⟨e⟩ := hA
    exact ⟨e.trans (hcap.isEmbedding.homeomorphImage A)⟩
  have hproper : j '' A ≠ univ := by
    intro heq
    apply cappedCuff_range_ne_univ hcap
    apply Set.eq_univ_of_univ_subset
    rw [← heq]
    exact image_subset_range _ _
  exact isPlanarInCappedCuff_of_one_cap hS hcap
    (planar_oArc_of_null hcap.isSurface hconn hAo hproper hnull)

end GraphMinor.GM12
