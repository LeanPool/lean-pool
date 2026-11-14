/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandGenealogy
public import LeanPool.ApollonianSuperharmonic.CurvatureOneBandCircleClassification
public import LeanPool.ApollonianSuperharmonic.BandOrientedGapRefinement
public import LeanPool.ApollonianSuperharmonic.P4984T1IncidentArcs
public import LeanPool.ApollonianSuperharmonic.P4984T1UnitIncidence
public import LeanPool.ApollonianSuperharmonic.P4984T1BranchDecay

-- [TABLET NODE: BandOrientedGapRefinementExists]

/-!
# BandOrientedGapRefinementExists

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandOrientedGapRefinementExists : Nonempty BandOrientedGapRefinement := by
-- BODY
  classical
  let presentation (ι : GaussianInt × Bool × List (Fin 3)) :=
    P4828T1Evaluate ι.1 ι.2.1 ι.2.2
  let gap (ι : GaussianInt × Bool × List (Fin 3)) :=
    P4984T1ClosedGap (2 * (ι.1.re : Real)) (presentation ι)
  have history (ι : GaussianInt × Bool × List (Fin 3)) :=
    P4828T1HistoryRealization ι.1 ι.2.1 ι.2.2
  have proper (ι : GaussianInt × Bool × List (Fin 3)) :
      ProperBandQuadruple (presentation ι) := (history ι).1.1
  let circle (ι : GaussianInt × Bool × List (Fin 3)) : BandCircle :=
    ⟨⟨presentation ι 0,
      Or.inl (ProperBandCurvatureStructure _ (proper ι)).1,
      presentation ι, (proper ι).1, 0, rfl⟩,
      (ProperBandCurvatureStructure _ (proper ι)).1⟩
  have next (ι : GaussianInt × Bool × List (Fin 3)) (b : Fin 3) :
      presentation (ι.1, ι.2.1, ι.2.2 ++ [b]) =
        P4828T1Step (P4828T1Rotate (presentation ι) b) := by
    simp only [presentation, P4828T1Evaluate, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
  have subdivision (ι : GaussianInt × Bool × List (Fin 3)) :=
    P4984T1ClosedSubdivision (2 * (ι.1.re : Real)) (presentation ι)
      (proper ι) (history ι).1.2.1 (history ι).1.2.2
  have boundary_cover (ι : GaussianInt × Bool × List (Fin 3)) :
      Metric.sphere (BandCircleEuclideanData (circle ι)).center
          (BandCircleEuclideanData (circle ι)).radius ⊆
        ⋃ b : Fin 3, gap (ι.1, ι.2.1, ι.2.2 ++ [b]) := by
    simpa only [gap, next, circle, BandCircleEuclideanData] using
      (subdivision ι).2.2.2.1
  refine ⟨{
    gap := gap
    gap_closed := fun ι => (subdivision ι).1
    circle := circle
    presentation := presentation
    root_cover := ?_
    root_left := ?_
    root_right := ?_
    proper := proper
    presented_circle := fun _ => rfl
    root_oriented_lines := ?_
    successor_slots := ?_
    child_contained := ?_
    exact_three_residual := ?_
    inserted_boundary_covered := boundary_cover
    residual_interiors_disjoint := ?_
    diameter_bound := ?_
    branch_shrinks := ?_
    initial_incident_arcs := ?_
    incident_arc_step := ?_ }⟩
  · simpa only [gap, presentation, P4828T1Evaluate, List.foldl_nil] using
      P4984T1RootGaps.2.2
  · simpa only [gap, presentation, P4828T1Evaluate, List.foldl_nil] using
      P4984T1RootGaps.1
  · simpa only [gap, presentation, P4828T1Evaluate, List.foldl_nil] using
      P4984T1RootGaps.2.1
  · intro a side
    cases side <;> simp [presentation, P4828T1Evaluate, P4828T1Root]
  · intro ι b
    refine ⟨P4828T1Rotate (presentation ι) b, ?_, ?_⟩
    · fin_cases b
      · exact Or.inl ⟨rfl, by funext k; fin_cases k <;> rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, by funext k; fin_cases k <;> rfl⟩)
      · exact Or.inr (Or.inr ⟨rfl, by funext k; fin_cases k <;> rfl⟩)
    · exact next ι b
  · intro ι b
    simpa only [gap, next] using (subdivision ι).2.1 b
  · intro ι
    simpa only [gap, next, circle, BandCircleEuclideanData] using
      (subdivision ι).2.2.1
  · intro ι b c hbc
    simpa only [gap, next] using (subdivision ι).2.2.2.2 b c hbc
  · intro ι
    exact P4984T1ContactDiameter _ _ (proper ι)
      (history ι).1.2.1 (history ι).1.2.2
  · intro a side branch
    exact (P4984T1BranchDecay a side branch).2.2
  · intro C
    by_cases hc : C.1.1.1 = 1
    · obtain ⟨a, ha⟩ := CurvatureOneBandCircleClassification C hc
      refine ⟨{(a, false, []), (a, true, []),
        (a - ⟨0, 1⟩, false, []), (a - ⟨0, 1⟩, true, [])}, ?_⟩
      simpa [gap, presentation, BandCircleEuclideanData, ha] using
        P4984T1UnitIncidence a
    · rcases BandGenealogy C with hc' | ⟨r, hr, hchild, hless, _⟩
      · exact (hc hc').elim
      have hrp : ProperBandQuadruple r := ⟨hr, by simpa [hchild] using hless⟩
      obtain ⟨a, side, word, rot, hform⟩ := P4828T1HistoryNormalForm r hrp
      let ι : GaussianInt × Bool × List (Fin 3) := (a, side, word)
      have hzero : presentation ι 0 = C.1.1 := by
        have heq := congrFun hform 0
        exact heq.symm.trans hchild
      have hcircle : circle ι = C := Subtype.ext (Subtype.ext hzero)
      let child (b : Fin 3) : GaussianInt × Bool × List (Fin 3) :=
        (a, side, word ++ [b])
      refine ⟨Finset.univ.image child, ?_, ?_⟩
      · apply Set.Subset.antisymm
        · intro p hp
          have hp' := boundary_cover ι (by simpa only [hcircle] using hp)
          obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hp'
          apply Set.mem_iUnion.mpr
          refine ⟨child b, Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr
            ⟨b, Finset.mem_univ b, rfl⟩, hb, hp⟩⟩
        · intro p hp
          obtain ⟨η, hη⟩ := Set.mem_iUnion.mp hp
          obtain ⟨_, hmem⟩ := Set.mem_iUnion.mp hη
          exact hmem.2
      · intro η hη
        obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hη
        have hparent : presentation (child b) (Fin.succ 0) = C.1.1 := by
          change presentation (ι.1, ι.2.1, ι.2.2 ++ [b]) (Fin.succ 0) = C.1.1
          rw [next]
          exact hzero
        have hpos : 0 < (presentation (child b) (Fin.succ 0)).1 := by
          rw [hparent]; exact C.2
        have harc := P4984T1IncidentArcs _ _ (proper (child b))
          (history (child b)).1.2.1 (history (child b)).1.2.2 0 hpos
        refine ⟨?_, ?_, ?_, 0, hparent⟩
        · simpa only [gap, BandCircleEuclideanData, hparent] using harc.1
        · simpa only [gap, BandCircleEuclideanData, hparent] using harc.2.1
        · simpa only [gap, BandCircleEuclideanData, hparent] using harc.2.2.1
  · intro C ι p hparent hp
    obtain ⟨j, hj⟩ := hparent
    have hpos : 0 < (presentation ι j.succ).1 := by rw [hj]; exact C.2
    have harc := P4984T1IncidentArcs _ _ (proper ι)
      (history ι).1.2.1 (history ι).1.2.2 j hpos
    obtain ⟨_, _, _, hkeep, t, hsplit, harcs, htC, htK, hcent⟩ := harc
    let keep := Finset.univ.erase j
    have hsplit' :
        gap ι ∩ Metric.sphere (BandCircleEuclideanData C).center
            (BandCircleEuclideanData C).radius =
          ⋃ b ∈ keep, gap (ι.1, ι.2.1, ι.2.2 ++ [b]) ∩
            Metric.sphere (BandCircleEuclideanData C).center
              (BandCircleEuclideanData C).radius := by
      simpa only [gap, next, keep, BandCircleEuclideanData, hj] using hsplit
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (hsplit' ▸ hp)
    obtain ⟨hbkeep, hbp⟩ := Set.mem_iUnion.mp hb
    have hsmall : (BandCircleEuclideanData (circle ι)).radius <
        (BandCircleEuclideanData C).radius := by
      change 1 / ((presentation ι 0).1 : Real) < 1 / (C.1.1.1 : Real)
      apply one_div_lt_one_div_of_lt
      · exact_mod_cast C.2
      · have hh := (proper ι).2 j
        rw [hj] at hh
        exact_mod_cast hh
    refine ⟨t, keep, b, ?_, hbkeep, ?_, hsplit', ?_, hbp, ?_, hsmall,
      ?_, ?_, ?_⟩
    · simp [keep]
    · intro c
      simpa only [keep, Finset.mem_erase, Finset.mem_univ, and_true,
        next, hj] using hkeep c
    · simpa only [gap, next, keep, BandCircleEuclideanData, hj] using harcs
    · intro heq
      rw [heq] at hsmall
      exact (lt_irrefl _ hsmall)
    · simpa only [BandCircleEuclideanData, hj] using htC
    · exact htK
    · simpa only [BandCircleEuclideanData, circle, hj] using hcent

end ApollonianSuperharmonic

end
