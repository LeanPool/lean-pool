/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5472T1CyclicAffineCommutation
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryAffineVectorCovariance

-- [TABLET NODE: P5472T1CyclicPhaseCovariance]

/-!
# P5472T1CyclicPhaseCovariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5472T1CyclicPhaseCovariance
    (s : BandPackingSymmetry) (q : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q)
    (hrev : BandPackingSymmetryReversesOrientation s = false)
    (hword : ∃ z : GaussianInt, s = .shift z ∨ s = (BandPackingSymmetry.shift z).comp .negate) :
    ∃ delta : Bool,
      BandPackingSymmetryScopedPhase s q delta ∧
      let I : GaussianInt := ⟨0, 1⟩
      let W := BandVectors.1 (q 3) (q 2)
      let A := BandVectors.2 (q 3) (q 2)
      let W' := BandVectors.1 (BandPackingSymmetryQuadrupleAction s q 3)
        (BandPackingSymmetryQuadrupleAction s q 2)
      let A' := BandVectors.2 (BandPackingSymmetryQuadrupleAction s q 3)
        (BandPackingSymmetryQuadrupleAction s q 2)
      BandPackingSymmetryAffineVectorAction s (W - I * W, A + I * A) =
        if delta then -(W' - I * W', A' + I * A')
        else (W' - I * W', A' + I * A') := by
-- BODY
  obtain ⟨delta, hphase, hcov⟩ := BandPackingSymmetryAffineVectorCovariance s q hq
  refine ⟨delta, hphase, ?_⟩
  let I : GaussianInt := ⟨0, 1⟩
  let W := BandVectors.1 (q 3) (q 2)
  let A := BandVectors.2 (q 3) (q 2)
  let W' := BandVectors.1 (BandPackingSymmetryQuadrupleAction s q 3)
    (BandPackingSymmetryQuadrupleAction s q 2)
  let A' := BandVectors.2 (BandPackingSymmetryQuadrupleAction s q 3)
    (BandPackingSymmetryQuadrupleAction s q 2)
  have hfirst : (BandPackingSymmetryAffineVectorAction s (W, A)).1 =
      BandPackingSymmetryVectorAction s W := by
    rcases hword with ⟨z, hs | hs⟩ <;> rw [hs] <;> rfl
  have hv := (hphase (0 : Fin 3)).2.2
  have ha := (hcov (0 : Fin 3)).2
  simp only [hrev, Bool.false_eq_true, ite_false] at hv ha
  change W' = (if delta then (-1 : GaussianInt) else 1) *
    BandPackingSymmetryVectorAction s W at hv
  change A' = (if delta then (-1 : GaussianInt) else 1) *
    (BandPackingSymmetryAffineVectorAction s (W, A)).2 at ha
  rw [← hfirst] at hv
  change BandPackingSymmetryAffineVectorAction s (W - I * W, A + I * A) = _
  rw [P5472T1CyclicAffineCommutation s hword W A]
  change ((BandPackingSymmetryAffineVectorAction s (W, A)).1 -
      I * (BandPackingSymmetryAffineVectorAction s (W, A)).1,
      (BandPackingSymmetryAffineVectorAction s (W, A)).2 +
      I * (BandPackingSymmetryAffineVectorAction s (W, A)).2) =
    if delta then -(W' - I * W', A' + I * A')
    else (W' - I * W', A' + I * A')
  cases delta
  all_goals
    simp only [Bool.false_eq_true, ite_false, ite_true, one_mul, neg_one_mul] at hv ha ⊢
  · rw [hv, ha]
  · rw [hv, ha]
    ext <;> simp <;> ring

end ApollonianSuperharmonic

end
