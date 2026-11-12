/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4261T1PlacedOdometer
public import LeanPool.ApollonianSuperharmonic.P4261T1ExteriorIndices
public import LeanPool.ApollonianSuperharmonic.P3055T1ExteriorCentralIncidence
public import LeanPool.ApollonianSuperharmonic.P3055T1ParentVectorNormalForms
public import LeanPool.ApollonianSuperharmonic.P3055T1SignedCentroidNormalForms
public import LeanPool.ApollonianSuperharmonic.LeftLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.SubtileLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.P4387T1PlacedCoordinates
public import LeanPool.ApollonianSuperharmonic.P4387T1ParentSlopeNormalForms


-- [TABLET NODE: P4261T1ContactAdjacency]

/-!
# P4261T1ContactAdjacency

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4261T1ContactAdjacency
    {q : Fin 4 → CircleCoordinates} {cfg : BandOrderedGeneralConfiguration q}
    {C₀ : BandCircle} {T₀ : ProtoTile}
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T₀)
    (h₀ : PartialOdometer)
    (C D : BandCircle) (T U : ProtoTile) (h f : PartialOdometer)
    (a b : PeriodicSubtileIndex)
    (ha : a ∈ P4261T1ExteriorIndices)
    (hb₁ : b.first = 0) (hb₂ : b.second = 0)
    (pa : P4261T1PlacedOdometer cert h₀ C T h a)
    (pb : P4261T1PlacedOdometer cert h₀ D U f b)
    (hinc : AllowedSubtileIncidence a b) :
    (D = C ∧ 1 < C.1.1.1 ∧ LeftLatticeAdjacent C T U h f) ∨
      SubtileLatticeAdjacent C D T U h f ∨
      SubtileLatticeAdjacent D C U T f h := by
-- BODY
  classical
  have ha' : a = ⟨.A, -1, -1⟩ ∨
      a = ⟨.A, 0, -1⟩ ∨ a = ⟨.C, 1, 0⟩ ∨ a = ⟨.C, 1, 1⟩ ∨
      a = ⟨.E, 0, 1⟩ ∨ a = ⟨.E, -1, 0⟩ ∨ a = ⟨.B, 1, 1⟩ ∨
      a = ⟨.B, 0, 1⟩ ∨ a = ⟨.D, -1, 0⟩ ∨ a = ⟨.D, -1, -1⟩ ∨
      a = ⟨.F, 0, -1⟩ ∨ a = ⟨.F, 1, 0⟩ := by
    simpa [P4261T1ExteriorIndices] using ha
  have hb' : b = ⟨.A, 0, 0⟩ ∨ b = ⟨.B, 0, 0⟩ ∨
      b = ⟨.C, 0, 0⟩ ∨ b = ⟨.D, 0, 0⟩ ∨
      b = ⟨.E, 0, 0⟩ ∨ b = ⟨.F, 0, 0⟩ := by
    cases b with
    | mk label first second =>
      simp only at hb₁ hb₂
      subst first
      subst second
      cases label <;> simp
  have rows := P3055T1ExteriorCentralIncidence a b ha' hb' hinc
  have left (r : Fin 4 → CircleCoordinates) (i : Fin 3) (e : Bool)
      (hr : ProperBandQuadruple r) (hrC : r 0 = C.1.1)
      (hDC : D.1.1 = C.1.1) (large : 1 < C.1.1.1)
      (hc : TileCentroid U - TileCentroid T =
        (if e = true then (1 : ℝ) else -1) •
          GaussianRealPoint (BandVectors.1 (r i.succ) (r 0)))
      (hs : pb.slope - pa.slope =
        (if e = true then (1 : ℝ) else -1) •
          GaussianRealPoint (BandVectors.2 (r i.succ) (r 0))) :
      D = C ∧ 1 < C.1.1.1 ∧ LeftLatticeAdjacent C T U h f := by
    have hDC' : D = C := Subtype.ext (Subtype.ext hDC)
    refine ⟨hDC', large, pa.odometer, ?_, pa.slope, pb.slope,
      pa.function_slope, pb.function_slope, Or.inr ?_⟩
    · simpa only [hDC'] using pb.odometer
    · refine ⟨r, i, e, hr, hrC, hc, ?_, ?_⟩
      · cases e <;> simpa [GaussianRealPoint] using congrArg Prod.fst hs
      · cases e <;> simpa [GaussianRealPoint] using congrArg Prod.snd hs
  have sub {C D : BandCircle} {T U : ProtoTile} {h f : PartialOdometer}
      {a b : PeriodicSubtileIndex}
      (pa : P4261T1PlacedOdometer cert h₀ C T h a)
      (pb : P4261T1PlacedOdometer cert h₀ D U f b)
      (r : Fin 4 → CircleCoordinates) (i : Fin 3) (s : Fin 4)
      (hr : ProperBandQuadruple r) (hrC : r 0 = C.1.1)
      (hrD : r i.succ = D.1.1)
      (hc : TileCentroid U - TileCentroid T =
        (1 / 2 : ℝ) • GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (BandVectors.1 (r i.succ) (r 0) + BandVectors.1 (r 0) (r i.succ))))
      (hs : pb.slope - pa.slope =
        (1 / 2 : ℝ) • GaussianRealPoint
          ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
            (BandVectors.2 (r i.succ) (r 0) + BandVectors.2 (r 0) (r i.succ)))) :
      SubtileLatticeAdjacent C D T U h f := by
    exact ⟨pa.odometer, pb.odometer, pa.slope, pb.slope,
      pa.function_slope, pb.function_slope, r, i, s, hr, hrC, hrD, hc,
      congrArg Prod.fst hs, congrArg Prod.snd hs⟩
  obtain ⟨caV, caA⟩ := P4387T1PlacedCoordinates cert h₀ C T h a pa
  obtain ⟨cbV, cbA⟩ := P4387T1PlacedCoordinates cert h₀ D U f b pb
  have hroot : pa.rootSlope = pb.rootSlope :=
    Option.some.inj (pa.root_slope.symm.trans pb.root_slope)
  have vf := P3055T1ParentVectorNormalForms q cfg
  have af := P4387T1ParentSlopeNormalForms q cfg
  dsimp only at caV caA cbV cbA vf af
  clear ha ha' hb' hb₁ hb₂ hinc
  rcases rows with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    have hC := pa.circle
    have hD := pb.circle
    dsimp only at hC hD
  case' inl =>
    refine Or.inl (left cfg.firstPredecessor 1 true cfg.firstProper ?_ ?_ ?_ ?_ ?_)
  case' inr.inl =>
    refine Or.inr (Or.inl
      (sub pa pb cfg.firstPredecessor 1 0 cfg.firstProper ?_ ?_ ?_ ?_))
  case' inr.inr.inl =>
    refine Or.inl (left cfg.firstPredecessor 2 true cfg.firstProper ?_ ?_ ?_ ?_ ?_)
  case' inr.inr.inr.inl =>
    refine Or.inr (Or.inl
      (sub pa pb cfg.firstPredecessor 2 3 cfg.firstProper ?_ ?_ ?_ ?_))
  case' inr.inr.inr.inr.inl =>
    refine Or.inl (left cfg.secondPredecessor 0 true cfg.secondProper ?_ ?_ ?_ ?_ ?_)
  case' inr.inr.inr.inr.inr.inl =>
    refine Or.inr (Or.inl
      (sub pa pb cfg.secondPredecessor 0 0 cfg.secondProper ?_ ?_ ?_ ?_))
  case' inr.inr.inr.inr.inr.inr.inl =>
    refine Or.inr (Or.inr
      (sub pb pa cfg.firstPredecessor 1 0 cfg.firstProper ?_ ?_ ?_ ?_))
  case' inr.inr.inr.inr.inr.inr.inr.inl =>
    refine Or.inr (Or.inr
      (sub pb pa cfg.firstPredecessor 2 3 cfg.firstProper ?_ ?_ ?_ ?_))
  case' inr.inr.inr.inr.inr.inr.inr.inr.inl =>
    refine Or.inr (Or.inr
      (sub pb pa cfg.secondPredecessor 0 0 cfg.secondProper ?_ ?_ ?_ ?_))
  case' inr.inr.inr.inr.inr.inr.inr.inr.inr.inl =>
    refine Or.inl (left cfg.firstPredecessor 1 false cfg.firstProper ?_ ?_ ?_ ?_ ?_)
  case' inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inl =>
    refine Or.inr (Or.inl
      (sub pa pb cfg.firstPredecessor 1 2 cfg.firstProper ?_ ?_ ?_ ?_))
  case' inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inl =>
    refine Or.inl (left cfg.firstPredecessor 2 false cfg.firstProper ?_ ?_ ?_ ?_ ?_)
  case' inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inl =>
    refine Or.inr (Or.inl
      (sub pa pb cfg.firstPredecessor 2 1 cfg.firstProper ?_ ?_ ?_ ?_))
  case' inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inl =>
    refine Or.inl (left cfg.secondPredecessor 0 false cfg.secondProper ?_ ?_ ?_ ?_ ?_)
  case' inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inl =>
    refine Or.inr (Or.inl
      (sub pa pb cfg.secondPredecessor 0 2 cfg.secondProper ?_ ?_ ?_ ?_))
  case' inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inl =>
    refine Or.inr (Or.inr
      (sub pb pa cfg.firstPredecessor 1 2 cfg.firstProper ?_ ?_ ?_ ?_))
  case' inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inl =>
    refine Or.inr (Or.inr
      (sub pb pa cfg.firstPredecessor 2 1 cfg.firstProper ?_ ?_ ?_ ?_))
  case' inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr =>
    refine Or.inr (Or.inr
      (sub pb pa cfg.secondPredecessor 0 2 cfg.secondProper ?_ ?_ ?_ ?_))
  all_goals
    try first
      | exact cfg.firstChild.trans hC.symm
      | exact cfg.firstChild.trans hD.symm
      | exact cfg.secondChild.trans hC.symm
      | exact cfg.secondChild.trans hD.symm
      | exact cfg.firstParentTwo.trans hC.symm
      | exact cfg.firstParentTwo.trans hD.symm
      | exact cfg.firstParentThree.trans hC.symm
      | exact cfg.firstParentThree.trans hD.symm
      | exact cfg.secondParentOne.trans hC.symm
      | exact cfg.secondParentOne.trans hD.symm
      | exact hD.trans hC.symm
      | (have hh : C.1.1.1 = (q 1).1 := congrArg Prod.fst hC
         have h₂ := cfg.secondLarge
         have h₁ := cfg.order12
         omega)
      | (have hh : C.1.1.1 = (q 2).1 := congrArg Prod.fst hC
         have h₂ := cfg.secondLarge
         omega)
  all_goals
    try simp only [show (0 : Fin 3).succ = (1 : Fin 4) from rfl,
      show (1 : Fin 3).succ = (2 : Fin 4) from rfl,
      show (2 : Fin 3).succ = (3 : Fin 4) from rfl]
    try simp only [vf.2.2.2.2.2.2.2.1, vf.2.2.2.2.2.2.2.2.1,
      vf.2.2.2.2.2.2.2.2.2, af.2.2.2.2.2.2.2.1,
      af.2.2.2.2.2.2.2.2.1, af.2.2.2.2.2.2.2.2.2]
    try simp only [cfg.firstChild, cfg.firstParentTwo, cfg.firstParentThree,
      cfg.secondChild, cfg.secondParentOne, vf.2.2.1, af.2.2.1]
    first | rw [caV, cbV] | rw [caA, cbA, hroot]
    apply Prod.ext
    all_goals
      simp [GaussianRealPoint, pow_succ,
        -GaussianInt.intCast_re, -GaussianInt.intCast_im]
      ring

end ApollonianSuperharmonic

end
