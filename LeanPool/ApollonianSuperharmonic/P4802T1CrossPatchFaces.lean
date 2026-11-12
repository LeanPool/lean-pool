/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4802T1HexagonOverlapSide
public import LeanPool.ApollonianSuperharmonic.P4802T1SideRestriction
public import LeanPool.ApollonianSuperharmonic.P4802T1SimplexFaces
public import LeanPool.ApollonianSuperharmonic.P4715T1PositionInjective

-- [TABLET NODE: P4802T1CrossPatchFaces]

/-!
# P4802T1CrossPatchFaces

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4802T1CrossPatchFaces (k l : Int × Int) (hkl : k ≠ l)
    (S T : Set PeriodicSubtileIndex)
    (hS : ∀ z ∈ S, P4715T1Position z ∈
      (fun x : Real × Real => x + ((k.1 : Real), (k.2 : Real))) ''
        P4715T1Hexagon)
    (hT : ∀ z ∈ T, P4715T1Position z ∈
      (fun x : Real × Real => x + ((l.1 : Real), (l.2 : Real))) ''
        P4715T1Hexagon) :
    convexHull Real (P4715T1Position '' S) ∩
      convexHull Real (P4715T1Position '' T) =
    convexHull Real (P4715T1Position '' (S ∩ T)) := by
-- BODY
  classical
  have side_index (k : Int × Int) (r : Fin 6) (a : PeriodicSubtileIndex)
      (ha : P4715T1Position a ∈ P4715T1Arc
        (P4715T1VertexShift k (P4715T1BoundaryCycle r))
        (P4715T1VertexShift k (P4715T1BoundaryCycle (r+1)))) :
      a ∈ ({P4715T1VertexShift k (P4715T1BoundaryCycle r),
        P4715T1VertexShift k (P4715T1BoundaryCycle (r+1))} : Set _) := by
    have hhex : P4715T1Position a ∈
        (fun x : Real × Real => x + ((k.1 : Real), (k.2 : Real))) ''
          P4715T1Hexagon := by
      rw [(P4715T1CoefficientTranslation k).2.1] at ha
      obtain ⟨x,hx,hxa⟩ := ha
      rw [P4780T1ActiveFacets] at hx
      exact ⟨x,hx.1,hxa⟩
    have hh := P4802T1SideRestriction k r ({a} : Set _)
      (by rintro z hz; rw [Set.mem_singleton_iff] at hz; exact hz.symm ▸ hhex)
    have hp := (Set.ext_iff.mp hh (P4715T1Position a)).mp
      ⟨subset_convexHull Real _ (Set.mem_image_of_mem _ (Set.mem_singleton a)), ha⟩
    by_contra hn
    have he : ({a} : Set PeriodicSubtileIndex) ∩
        {P4715T1VertexShift k (P4715T1BoundaryCycle r),
          P4715T1VertexShift k (P4715T1BoundaryCycle (r+1))} = ∅ := by
      ext b
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false]
      rintro ⟨rfl,h⟩
      exact hn h
    simp only [he, Set.image_empty, convexHull_empty, Set.mem_empty_iff_false] at hp
  have hconv (k : Int × Int) : Convex Real
      ((fun x : Real × Real => x + ((k.1 : Real), (k.2 : Real))) ''
        P4715T1Hexagon) := by
    have hh : Convex Real P4715T1Hexagon := convex_convexHull Real _
    simpa only [add_comm] using hh.translate ((k.1 : Real), (k.2 : Real))
  apply Set.Subset.antisymm
  · intro p hp
    have hpS := convexHull_min (by rintro _ ⟨z,hz,rfl⟩; exact hS z hz) (hconv k) hp.1
    have hpT := convexHull_min (by rintro _ ⟨z,hz,rfl⟩; exact hT z hz) (hconv l) hp.2
    obtain ⟨r,hr⟩ := P4802T1HexagonOverlapSide k l hkl p ⟨hpS,hpT⟩
    obtain ⟨s,hs⟩ := P4802T1HexagonOverlapSide l k hkl.symm p ⟨hpT,hpS⟩
    let u := P4715T1VertexShift k (P4715T1BoundaryCycle r)
    let v := P4715T1VertexShift k (P4715T1BoundaryCycle (r+1))
    let w := P4715T1VertexShift l (P4715T1BoundaryCycle s)
    let z := P4715T1VertexShift l (P4715T1BoundaryCycle (s+1))
    have he : P4715T1Arc u v = P4715T1Arc w z := by
      rw [← hr, Set.inter_comm, hs]
    have hpair : ({u,v} : Set PeriodicSubtileIndex) = {w,z} := by
      apply Set.Subset.antisymm
      · intro a ha
        have hpa : P4715T1Position a ∈ P4715T1Arc w z := by
          rw [← he]
          rcases ha with ha | ha
          · rw [ha]; exact left_mem_segment Real _ _
          · rw [Set.mem_singleton_iff] at ha
            rw [ha]; exact right_mem_segment Real _ _
        exact side_index l s a hpa
      · intro a ha
        have hpa : P4715T1Position a ∈ P4715T1Arc u v := by
          rw [he]
          rcases ha with ha | ha
          · rw [ha]; exact left_mem_segment Real _ _
          · rw [Set.mem_singleton_iff] at ha
            rw [ha]; exact right_mem_segment Real _ _
        exact side_index k r a hpa
    have hpr : p ∈ P4715T1Arc u v := by rw [← hr]; exact ⟨hpS,hpT⟩
    have hps : p ∈ P4715T1Arc w z := he ▸ hpr
    have ha : p ∈ convexHull Real (P4715T1Position '' (S ∩ ({u,v} : Set _))) := by
      rw [← P4802T1SideRestriction k r S hS]
      exact ⟨hp.1,hpr⟩
    have hb : p ∈ convexHull Real (P4715T1Position '' (T ∩ ({u,v} : Set _))) := by
      rw [hpair, ← P4802T1SideRestriction l s T hT]
      exact ⟨hp.2,hps⟩
    have huv : u ≠ v := by
      fin_cases r <;> simp [u,v,P4715T1VertexShift,P4715T1BoundaryCycle]
    have hi : AffineIndependent Real
        (fun x : P4715T1Position '' ({u,v} : Set _) => (x : Real × Real)) := by
      have hh := (affineIndependent_of_ne Real (P4715T1PositionInjective.ne huv)).range
      have heq : Set.range ![P4715T1Position u,P4715T1Position v] =
          P4715T1Position '' ({u,v} : Set _) := by
        ext x
        simp [or_comm]
      rw [heq] at hh
      exact hh
    have hfaces := P4802T1SimplexFaces (P4715T1Position '' ({u,v} : Set _))
      ((Set.toFinite ({u,v} : Set PeriodicSubtileIndex)).image _) hi
      (P4715T1Position '' (S ∩ ({u,v} : Set _)))
      (P4715T1Position '' (T ∩ ({u,v} : Set _)))
      (Set.image_mono Set.inter_subset_right) (Set.image_mono Set.inter_subset_right)
    rw [← Set.image_inter P4715T1PositionInjective] at hfaces
    have hab := (Set.ext_iff.mp hfaces p).mp ⟨ha,hb⟩
    have hsub : (S ∩ ({u,v} : Set _)) ∩ (T ∩ ({u,v} : Set _)) ⊆ S ∩ T :=
      fun _ h => ⟨h.1.1,h.2.1⟩
    exact convexHull_mono (Set.image_mono hsub) hab
  · exact Set.subset_inter
      (convexHull_mono (Set.image_mono Set.inter_subset_left))
      (convexHull_mono (Set.image_mono Set.inter_subset_right))

end ApollonianSuperharmonic

end
