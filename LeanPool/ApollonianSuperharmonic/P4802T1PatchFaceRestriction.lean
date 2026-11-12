/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4802T1SimplexFaces
public import LeanPool.ApollonianSuperharmonic.P4802T1TriangleIndependent
public import LeanPool.ApollonianSuperharmonic.P4715T1HexagonSubdivision
public import LeanPool.ApollonianSuperharmonic.P4715T1PositionInjective

-- [TABLET NODE: P4802T1PatchFaceRestriction]

/-!
# P4802T1PatchFaceRestriction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4802T1PatchFaceRestriction (i j : Fin 12)
    (S T : Set PeriodicSubtileIndex)
    (hS : S ⊆ Set.range (SixSubtileFaceVertices (P4715T1PatchFaces i)))
    (hT : T ⊆ Set.range (SixSubtileFaceVertices (P4715T1PatchFaces j))) :
    convexHull Real (P4715T1Position '' S) ∩
      convexHull Real (P4715T1Position '' T) =
    convexHull Real (P4715T1Position '' (S ∩ T)) := by
-- BODY
  let V := fun i => Set.range (SixSubtileFaceVertices (P4715T1PatchFaces i))
  have restrict (i : Fin 12) (A B : Set PeriodicSubtileIndex)
      (hA : A ⊆ V i) (hB : B ⊆ V i) :
      convexHull Real (P4715T1Position '' A) ∩
        convexHull Real (P4715T1Position '' B) =
      convexHull Real (P4715T1Position '' (A ∩ B)) := by
    have hi := P4802T1TriangleIndependent _
      (P4715T1HexagonSubdivision.2.1 i)
    have hir : AffineIndependent Real
        (fun x : P4715T1Position '' V i => (x : Real × Real)) := by
      change AffineIndependent Real
        (fun x : P4715T1Position '' Set.range
          (SixSubtileFaceVertices (P4715T1PatchFaces i)) => (x : Real × Real))
      rw [← Set.range_comp]
      exact hi.range
    have hh := P4802T1SimplexFaces (P4715T1Position '' V i)
      ((Set.finite_range _).image _) hir
      (P4715T1Position '' A) (P4715T1Position '' B)
      (Set.image_mono hA) (Set.image_mono hB)
    rw [← Set.image_inter P4715T1PositionInjective] at hh
    exact hh
  by_cases hij : i = j
  · subst j
    exact restrict i S T hS hT
  apply Set.Subset.antisymm
  · intro p hp
    have hpij : p ∈ convexHull Real (P4715T1Position '' (V i ∩ V j)) := by
      rw [← P4715T1HexagonSubdivision.2.2.1 i j hij]
      exact ⟨convexHull_mono (Set.image_mono hS) hp.1,
        convexHull_mono (Set.image_mono hT) hp.2⟩
    have hpS : p ∈ convexHull Real (P4715T1Position '' (S ∩ (V i ∩ V j))) := by
      rw [← restrict i S (V i ∩ V j) hS Set.inter_subset_left]
      exact ⟨hp.1,hpij⟩
    have hpT : p ∈ convexHull Real
        (P4715T1Position '' ((S ∩ (V i ∩ V j)) ∩ T)) := by
      rw [← restrict j (S ∩ (V i ∩ V j)) T
        (fun _ h => h.2.2) hT]
      exact ⟨hpS,hp.2⟩
    have hs : (S ∩ (V i ∩ V j)) ∩ T ⊆ S ∩ T :=
      fun _ h => ⟨h.1.1,h.2⟩
    exact convexHull_mono (Set.image_mono hs) hpT
  · exact Set.subset_inter
      (convexHull_mono (Set.image_mono Set.inter_subset_left))
      (convexHull_mono (Set.image_mono Set.inter_subset_right))

end ApollonianSuperharmonic

end
