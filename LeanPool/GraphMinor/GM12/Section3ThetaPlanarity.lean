/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Cited
public import LeanPool.GraphMinor.GM12.Section3ThetaCircles
import LeanPool.GraphMinor.GM12.Section3ThetaHomotopy
import LeanPool.GraphMinor.GM12.Section3SolidUnion
import LeanPool.GraphMinor.Surface.DiscsInSurface

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Planarity from two pair circles

In the third schismatic shape of VII Section 8, used by XII (3.1),
page 245, the first two pair circles generate the homotopies of the
third. If both are planar, the third is null-homotopic. Every circle
in the shape is one of these pairs, so VII (5.1) makes the whole proper
solid shape planar. This supplies the comparison needed when two
pair circles are planar after filling the same cuff.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

universe u

/-- Two planar pair circles make the whole proper three-branch shape
planar, by the relative-endpoint path argument and VII (5.1), page 230. -/
theorem planar_three_branches_of_two_planar_pairs
    {S : Type u} [TopologicalSpace S] (hS : IsSurface S) (hconn : ConnectedSpace S)
    {P Q R : Set S} {u v : S} (huv : u ≠ v)
    (hP : IsLineWithEnds P u v) (hQ : IsLineWithEnds Q u v) (hR : IsLineWithEnds R u v)
    (hPQ : P ∩ Q = {u, v}) (hPR : P ∩ R = {u, v}) (hQR : Q ∩ R = {u, v})
    (hproper : P ∪ Q ∪ R ≠ univ)
    (hplanPQ : IsPlanar (P ∪ Q)) (hplanPR : IsPlanar (P ∪ R)) :
    IsPlanar (P ∪ Q ∪ R) := by
  let := hS.1
  let := hS.2.1
  have hsolid := isSolid_union (isSolid_union (isSolid_line ⟨hP.choose⟩)
    (isSolid_line ⟨hQ.choose⟩)) (isSolid_line ⟨hR.choose⟩)
  apply (GraphMinor.GM07.gm07_theorem_5_1 S hS hconn (P ∪ Q ∪ R) hsolid hproper).mpr
  intro F hF hFX
  rcases oArc_eq_pair_of_three_branches huv hP hQ hR hPQ hPR hQR hF hFX with h | h | h
  · rw [h]
    obtain ⟨D, hD, hFD⟩ := hplanPQ
    exact isNullHomotopicOArcIn_of_subset_disc
      (isOArc_union_of_lines_inter_eq_ends hP hQ hPQ) (subset_univ D) hD hFD
  · rw [h]
    obtain ⟨D, hD, hFD⟩ := hplanPR
    exact isNullHomotopicOArcIn_of_subset_disc
      (isOArc_union_of_lines_inter_eq_ends hP hR hPR) (subset_univ D) hD hFD
  · rw [h]
    exact third_pair_null_of_two_planar_pairs hP hQ hR hQR hplanPQ hplanPR

end GraphMinor.GM12
