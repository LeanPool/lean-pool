/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4793T1PatchFacetLedger
public import LeanPool.ApollonianSuperharmonic.P4793T1SupportingFace
public import LeanPool.ApollonianSuperharmonic.P4783T1PatchCoverage
public import LeanPool.ApollonianSuperharmonic.P4715T1HexagonTessellation

-- [TABLET NODE: P4793T1PatchBoundaryTraces]

/-!
# P4793T1PatchBoundaryTraces

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4793T1PatchBoundaryTraces (j : Fin 12) :
    convexHull Real (P4715T1Position ''
      Set.range (SixSubtileFaceVertices (P4715T1PatchFaces j))) ∩
      frontier P4715T1Hexagon =
    convexHull Real (P4715T1Position ''
      (Set.range (SixSubtileFaceVertices (P4715T1PatchFaces j)) ∩
        Set.range P4715T1BoundaryCycle)) := by
-- BODY
  let V := Set.range (SixSubtileFaceVertices (P4715T1PatchFaces j))
  let S := P4715T1Position '' V
  have hK : convexHull Real S ⊆ P4715T1Hexagon := by
    intro x hx
    rw [← P4783T1PatchCoverage]
    exact Set.mem_iUnion.mpr ⟨j, hx⟩
  have hside (l : Fin 6) :
      P4715T1Arc (P4715T1BoundaryCycle l)
        (P4715T1BoundaryCycle (l+1)) =
      P4715T1Hexagon ∩ {x | P4793T1FacetForms l x = 0} := by
    rw [P4780T1ActiveFacets]
    congr 1
    ext x
    fin_cases l <;> norm_num [P4793T1FacetForms] <;> constructor <;> intro h <;> linarith
  have hface (l : Fin 6) := P4793T1SupportingFace S (P4793T1FacetForms l)
    (by
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      exact P4793T1PatchFacetLedger.1 j l k)
  apply Set.Subset.antisymm
  · intro x hx
    have hb := hx.2
    rw [P4715T1HexagonTessellation.2.1] at hb
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hb
    rw [hside] at hl
    have hm : x ∈ convexHull Real (S ∩ {x | P4793T1FacetForms l x = 0}) := by
      rw [← (hface l).2]
      exact ⟨hx.1, hl.2⟩
    apply convexHull_mono (t := P4715T1Position ''
      (V ∩ Set.range P4715T1BoundaryCycle)) ?_ hm
    rintro _ ⟨⟨_, ⟨k, rfl⟩, rfl⟩, hz⟩
    exact ⟨_, ⟨⟨k, rfl⟩, P4793T1PatchFacetLedger.2.1 j l k hz⟩, rfl⟩
  · intro x hx
    obtain ⟨l, hl⟩ := P4793T1PatchFacetLedger.2.2 j
    have hm : x ∈ convexHull Real (S ∩ {x | P4793T1FacetForms l x = 0}) := by
      apply convexHull_mono (s := P4715T1Position ''
        (V ∩ Set.range P4715T1BoundaryCycle)) ?_ hx
      rintro _ ⟨_, ⟨⟨k, rfl⟩, hb⟩, rfl⟩
      exact ⟨⟨_, ⟨k, rfl⟩, rfl⟩, hl k hb⟩
    rw [← (hface l).2] at hm
    refine ⟨hm.1, ?_⟩
    rw [P4715T1HexagonTessellation.2.1]
    apply Set.mem_iUnion.mpr
    refine ⟨l, ?_⟩
    rw [hside]
    exact ⟨hK hm.1, hm.2⟩

end ApollonianSuperharmonic

end
