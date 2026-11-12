/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4715T1Hexagon
public import LeanPool.ApollonianSuperharmonic.P4715T1VertexShift
public import LeanPool.ApollonianSuperharmonic.P4715T1Arc
public import LeanPool.ApollonianSuperharmonic.P4780T1StrictInterior
public import LeanPool.ApollonianSuperharmonic.P4780T1ActiveFacets
public import LeanPool.ApollonianSuperharmonic.P4780T1IntegerCoverage
public import LeanPool.ApollonianSuperharmonic.P4780T1InteriorSeparation
public import LeanPool.ApollonianSuperharmonic.P4780T1NeighborFacets
public import LeanPool.ApollonianSuperharmonic.P4780T1NeighborCorners
public import LeanPool.ApollonianSuperharmonic.P4715T1CoefficientTranslation
public import Mathlib.Tactic.Abel

-- [TABLET NODE: P4715T1HexagonTessellation]

/-!
# P4715T1HexagonTessellation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4715T1HexagonTessellation :
    P4715T1Hexagon = {p : Real × Real |
      -2 ≤ 2 * p.1 - p.2 ∧ 2 * p.1 - p.2 ≤ 0 ∧
      -1 ≤ p.1 - 2 * p.2 ∧ p.1 - 2 * p.2 ≤ 1 ∧
      -2 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 0} ∧
    frontier P4715T1Hexagon = ⋃ j : Fin 6,
      P4715T1Arc (P4715T1BoundaryCycle j)
        (P4715T1BoundaryCycle (j + 1)) ∧
    (⋃ k : Int × Int,
      (fun p : Real × Real => p + ((k.1 : Real), (k.2 : Real))) ''
        P4715T1Hexagon) = Set.univ ∧
    (Pairwise fun k l : Int × Int => Disjoint
      (interior ((fun p : Real × Real => p + ((k.1 : Real), (k.2 : Real))) ''
        P4715T1Hexagon))
      (interior ((fun p : Real × Real => p + ((l.1 : Real), (l.2 : Real))) ''
        P4715T1Hexagon))) ∧
    ∀ k l : Int × Int, k ≠ l →
      ((fun p : Real × Real => p + ((k.1 : Real), (k.2 : Real))) ''
        P4715T1Hexagon) ∩
      ((fun p : Real × Real => p + ((l.1 : Real), (l.2 : Real))) ''
        P4715T1Hexagon) =
      convexHull Real (P4715T1Position ''
        (Set.range (P4715T1VertexShift k ∘ P4715T1BoundaryCycle) ∩
         Set.range (P4715T1VertexShift l ∘ P4715T1BoundaryCycle))) := by
-- BODY
  refine ⟨P4780T1HullHalfspaces, ?_, ?_, ?_, ?_⟩
  · have hclosed : IsClosed P4715T1Hexagon := by
      rw [P4780T1HullHalfspaces]
      simp only [Set.ofPred_and]
      repeat' apply IsClosed.inter
      all_goals exact isClosed_le (by fun_prop) (by fun_prop)
    rw [hclosed.frontier_eq]
    ext p
    simp only [Set.mem_sdiff, Set.mem_iUnion]
    constructor
    · rintro ⟨hp, hn⟩
      have hq := hp
      rw [P4780T1HullHalfspaces] at hq
      rw [P4780T1StrictInterior] at hn
      rcases hq with ⟨hx0, hx1, hy0, hy1, hz0, hz1⟩
      have he : 2*p.1-p.2=0 ∨ p.1-2*p.2=1 ∨ p.1+p.2 = -2 ∨
          2*p.1-p.2 = -2 ∨ p.1-2*p.2 = -1 ∨ p.1+p.2=0 := by
        by_contra h
        push Not at h
        apply hn
        rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
        exact ⟨lt_of_le_of_ne hx0 (Ne.symm h4), lt_of_le_of_ne hx1 h1,
          lt_of_le_of_ne hy0 (Ne.symm h5), lt_of_le_of_ne hy1 h2,
          lt_of_le_of_ne hz0 (Ne.symm h3), lt_of_le_of_ne hz1 h6⟩
      rcases he with he | he | he | he | he | he
      · exact ⟨0, by rw [P4780T1ActiveFacets]; exact ⟨hp, he⟩⟩
      · exact ⟨1, by rw [P4780T1ActiveFacets]; exact ⟨hp, he⟩⟩
      · exact ⟨2, by rw [P4780T1ActiveFacets]; exact ⟨hp, he⟩⟩
      · exact ⟨3, by rw [P4780T1ActiveFacets]; exact ⟨hp, he⟩⟩
      · exact ⟨4, by rw [P4780T1ActiveFacets]; exact ⟨hp, he⟩⟩
      · exact ⟨5, by rw [P4780T1ActiveFacets]; exact ⟨hp, he⟩⟩
    · rintro ⟨j, hp⟩
      rw [P4780T1ActiveFacets] at hp
      refine ⟨hp.1, ?_⟩
      rw [P4780T1StrictInterior]
      intro hs
      rcases hs with ⟨hx0, hx1, hy0, hy1, hz0, hz1⟩
      have he := hp.2
      fin_cases j <;> simp at he <;> linarith
  · exact P4780T1IntegerCoverage
  · exact P4780T1InteriorSeparation
  · intro k l hkl
    have hside (j : Fin 6)
        (hd : l-k = (![(1,0), (0,-1), (-1,-1), (-1,0), (0,1), (1,1)] j : Int × Int))
        (a : Real × Real)
        (ha : a ∈ P4715T1Arc (P4715T1BoundaryCycle j)
          (P4715T1BoundaryCycle (j+1))) :
        a + ((k.1 : Real), (k.2 : Real)) ∈
          convexHull Real (P4715T1Position ''
            (Set.range (P4715T1VertexShift k ∘ P4715T1BoundaryCycle) ∩
             Set.range (P4715T1VertexShift l ∘ P4715T1BoundaryCycle))) := by
      have hm (z : PeriodicSubtileIndex)
          (hz : z ∈ ({P4715T1BoundaryCycle j, P4715T1BoundaryCycle (j+1)} :
            Set PeriodicSubtileIndex)) :
          P4715T1VertexShift k z ∈
            Set.range (P4715T1VertexShift k ∘ P4715T1BoundaryCycle) ∩
            Set.range (P4715T1VertexShift l ∘ P4715T1BoundaryCycle) := by
        rw [← P4780T1NeighborCorners j] at hz
        rcases hz with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
        refine ⟨⟨r, congrArg (P4715T1VertexShift k) hr⟩, ⟨s, ?_⟩⟩
        have hkd : k + (![(1,0), (0,-1), (-1,-1), (-1,0), (0,1), (1,1)] j : Int × Int) = l := by
          rw [← hd]
          abel
        change P4715T1VertexShift l (P4715T1BoundaryCycle s) = _
        rw [← hs, Function.comp_apply, ← P4715T1IndexAction.2.1, hkd]
      have hpa : a + ((k.1 : Real), (k.2 : Real)) ∈
          P4715T1Arc (P4715T1VertexShift k (P4715T1BoundaryCycle j))
            (P4715T1VertexShift k (P4715T1BoundaryCycle (j+1))) := by
        rw [P4715T1CoefficientTranslation k |>.2.1]
        exact ⟨a, ha, rfl⟩
      exact segment_subset_convexHull
        (Set.mem_image_of_mem _ (hm _ (by simp)))
        (Set.mem_image_of_mem _ (hm _ (by simp))) hpa
    apply Set.Subset.antisymm
    · rintro p ⟨⟨a, ha, hap⟩, ⟨b, hb, hbp⟩⟩
      generalize hde : l-k = d
      have hab : a = b + ((d.1 : Real), (d.2 : Real)) := by
        rw [← hde]
        have h1 := congrArg Prod.fst (hap.trans hbp.symm)
        have h2 := congrArg Prod.snd (hap.trans hbp.symm)
        ext <;> simp [Int.cast_sub] at h1 h2 ⊢ <;> linarith
      have hcase (j : Fin 6)
          (hj : d = (![(1,0), (0,-1), (-1,-1), (-1,0), (0,1), (1,1)] j : Int × Int)) :
          p ∈ convexHull Real (P4715T1Position ''
            (Set.range (P4715T1VertexShift k ∘ P4715T1BoundaryCycle) ∩
             Set.range (P4715T1VertexShift l ∘ P4715T1BoundaryCycle))) := by
        rw [← hap]
        apply hside j (hde.trans hj) a
        rw [← P4780T1NeighborFacets j]
        refine ⟨ha, b, hb, ?_⟩
        simpa only [← hj] using hab.symm
      have hdiag : d = (1,-1) ∨ d = (-1,1) → False := by
        intro h
        rw [P4780T1HullHalfspaces] at ha hb
        rcases ha with ⟨ha1, ha2, ha3, ha4, ha5, ha6⟩
        rcases hb with ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩
        rcases h with h | h <;> rw [h] at hab
        all_goals
          have he1 := congrArg Prod.fst hab
          have he2 := congrArg Prod.snd hab
          norm_num at he1 he2
          linarith
      have hd := P4780T1OverlapBound d a b ha hb hab
      have hne : d ≠ 0 := by rw [← hde]; exact sub_ne_zero.mpr (Ne.symm hkl)
      rcases d with ⟨x,y⟩
      rcases hd with ⟨hx0, hx1, hy0, hy1⟩
      interval_cases x <;> interval_cases y
      · exact hcase 2 rfl
      · exact hcase 3 rfl
      · exact (hdiag (Or.inr rfl)).elim
      · exact hcase 1 rfl
      · exact (hne rfl).elim
      · exact hcase 4 rfl
      · exact (hdiag (Or.inl rfl)).elim
      · exact hcase 0 rfl
      · exact hcase 5 rfl
    · apply convexHull_min
      · rintro _ ⟨z, hz, rfl⟩
        constructor
        · rcases hz.1 with ⟨j, hj⟩
          rw [← hj, Function.comp_apply, (P4715T1CoefficientTranslation k).1]
          exact ⟨_, subset_convexHull Real _ ⟨j, rfl⟩, rfl⟩
        · rcases hz.2 with ⟨j, hj⟩
          rw [← hj, Function.comp_apply, (P4715T1CoefficientTranslation l).1]
          exact ⟨_, subset_convexHull Real _ ⟨j, rfl⟩, rfl⟩
      · have hc (z : Int × Int) : Convex Real
            ((fun p : Real × Real => p + ((z.1 : Real), (z.2 : Real))) '' P4715T1Hexagon) := by
          have hh : Convex Real P4715T1Hexagon := convex_convexHull Real _
          simpa only [add_comm] using hh.translate ((z.1 : Real), (z.2 : Real))
        exact (hc k).inter (hc l)

end ApollonianSuperharmonic

end
