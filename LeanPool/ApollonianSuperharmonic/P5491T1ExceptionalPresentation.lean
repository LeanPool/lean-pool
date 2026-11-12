/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryInversePhaseCancellation
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryProperCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCovariance
public import LeanPool.ApollonianSuperharmonic.BandPredecessorNoCollision
public import LeanPool.ApollonianSuperharmonic.FordCoordinateConfiguration
public import LeanPool.ApollonianSuperharmonic.DiamondCoordinateConfiguration
public import LeanPool.ApollonianSuperharmonic.FordFareyParentsExist

-- [TABLET NODE: P5491T1ExceptionalPresentation]

/-!
# P5491T1ExceptionalPresentation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5491T1ExceptionalPresentation (q : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q)
    (he : (∃ (g : BandPackingSymmetry) (P : FordFareyParameter),
        BandPackingSymmetryCircleAction g (FordCircleCoordinate P.p P.q) = q 0) ∨
      (∃ (g : BandPackingSymmetry) (K : DiamondParameter),
        BandPackingSymmetryCircleAction g (DiamondRecursiveQuadruple K 0) = q 0)) :
    ∃ g : BandPackingSymmetry,
      (∃ P : FordFareyParameter, 1 < P.q ∧
        (BandPackingSymmetryQuadrupleAction g q) 0 = FordRecursiveQuadruple P 0 ∧
        ∀ i : Fin 3, ∃ j : Fin 3,
          (BandPackingSymmetryQuadrupleAction g q) i.succ =
            FordRecursiveQuadruple P j.succ) ∨
      (∃ K : DiamondParameter, 1 < K.1 ∧
        (BandPackingSymmetryQuadrupleAction g q) 0 = DiamondRecursiveQuadruple K 0 ∧
        ∀ i : Fin 3, ∃ j : Fin 3,
          (BandPackingSymmetryQuadrupleAction g q) i.succ =
            DiamondRecursiveQuadruple K j.succ) := by
-- BODY
  have parents (F R : Fin 4 → CircleCoordinates)
      (hF : ProperBandQuadruple F) (hR : ProperBandQuadruple R)
      (h0 : R 0 = F 0) : ∀ i : Fin 3, ∃ j : Fin 3, R i.succ = F j.succ := by
    obtain ⟨r,hr,_⟩ := BandPredecessorNoCollision F R hF hR h0.symm
    exact fun i => ⟨i+r,hr i⟩
  have childLarge : 1 < (q 0).1 := by
    have H := ProperBandCurvatureStructure q hq
    have H0 := hq.2 0
    have H1 := hq.2 1
    have N0 := H.2.1 0
    have N1 := H.2.1 1
    by_contra hn
    have Z0 : (q (0 : Fin 3).succ).1 = 0 := by omega
    have Z1 : (q (1 : Fin 3).succ).1 = 0 := by omega
    have := H.2.2 0 1 Z0 Z1
    contradiction
  rcases he with ⟨w,P,hw⟩ | ⟨w,K,hw⟩
  · obtain ⟨v,hleft,_,_⟩ := BandPackingSymmetryInversePhaseCancellation.2 w
    have hR := BandPackingSymmetryProperCovariance v q hq
    have h0 : (BandPackingSymmetryQuadrupleAction v q) 0 = FordRecursiveQuadruple P 0 := by
      change BandPackingSymmetryCircleAction v (q 0) = FordCircleCoordinate P.p P.q
      rw [← hw,hleft]
    have hP : 1 < P.q := by
      have hc := (BandPackingSymmetryCovariance w).1 (FordCircleCoordinate P.p P.q)
      rw [hw] at hc
      by_contra hn
      have hq1 : P.q = 1 := by have := P.q_pos; omega
      simp [FordCircleCoordinate,hq1] at hc
      omega
    exact ⟨v,Or.inl ⟨P,hP,h0,parents _ _ ((FordCoordinateConfiguration P).2 hP).1 hR h0⟩⟩
  · obtain ⟨v,hleft,_,_⟩ := BandPackingSymmetryInversePhaseCancellation.2 w
    have hR := BandPackingSymmetryProperCovariance v q hq
    have h0 : (BandPackingSymmetryQuadrupleAction v q) 0 = DiamondRecursiveQuadruple K 0 := by
      change BandPackingSymmetryCircleAction v (q 0) = DiamondRecursiveQuadruple K 0
      rw [← hw,hleft]
    by_cases hK : 1 < K.1
    · exact ⟨v,Or.inr ⟨K,hK,h0,parents _ _ (DiamondCoordinateConfiguration K).2.1 hR h0⟩⟩
    · have hk1 : K.1 = 1 := by have := K.2; omega
      obtain ⟨P,⟨hp,hpden⟩,_⟩ := FordFareyParentsExist 1 2 (by decide) (by decide)
      have hP : 1 < P.q := by omega
      have hford : (BandPackingSymmetryQuadrupleAction v q) 0 = FordRecursiveQuadruple P 0 := by
        rw [h0]
        simp [DiamondRecursiveQuadruple,FordRecursiveQuadruple,FordCircleCoordinate,
          hk1,hp,hpden]
      exact ⟨v,Or.inl ⟨P,hP,hford,
        parents _ _ ((FordCoordinateConfiguration P).2 hP).1 hR hford⟩⟩

end ApollonianSuperharmonic

end
