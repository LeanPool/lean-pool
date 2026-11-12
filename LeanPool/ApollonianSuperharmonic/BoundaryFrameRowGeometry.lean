/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.P4458T1RestrictionFamily
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Shared boundary-frame row geometry

Adapted from Wesley Pegden's Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace BoundaryFrameRowGeometry

/-- The parent presentation selected by a boundary frame is proper. -/
theorem presentationProper :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        ProperBandQuadruple r ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r
  have rot : ∀ i : Fin 3,
      ProperBandQuadruple
        ![F.q 0, F.q i.succ, F.q ((i + 1).succ), F.q ((i + 2).succ)] := by
    intro i
    fin_cases i
    · convert F.proper using 1; funext j; fin_cases j <;> rfl
    · refine ⟨SemiProperQuadruple.rotate F.proper.1, ?_⟩
      intro j
      fin_cases j
      · simpa using F.proper.2 1
      · simpa using F.proper.2 2
      · simpa using F.proper.2 0
    · refine ⟨SemiProperQuadruple.rotate (SemiProperQuadruple.rotate F.proper.1), ?_⟩
      intro j
      fin_cases j
      · simpa using F.proper.2 2
      · simpa using F.proper.2 0
      · simpa using F.proper.2 1
  simpa [r] using rot F.slot

/-- The shared frame-centroid identities determine the tile displacement. -/
theorem centroidDifference :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let w : GaussianInt := BandVectors.1 (r 3) (r 2)
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        (TileCentroid (D.tiles F.slot false) - TileCentroid F.tile = -(1 / 2 : ℝ) •
            (GaussianRealPoint w - (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))) →
            ((TileCentroid Rminus - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.1 (r 1) (r 0) - BandVectors.1 (r 0) (r 1))) → (((↑(-w + I * w -
            BandVectors.1 (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ))) + BandVectors.1 (r (0 : Fin
            (4 : ℕ))) (r (1 : Fin (4 : ℕ)))).re : ℝ) = (↑((2 : GaussianInt) * y).re : ℝ)) →
            (((↑(-w + I * w - BandVectors.1 (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ))) +
            BandVectors.1 (r (0 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ)))).im : ℝ) = (↑((2 :
            GaussianInt) * y).im : ℝ)) → (TileCentroid (D.tiles F.slot false) - TileCentroid
            Rminus = GaussianRealPoint y)))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D r I w y hUcenter hMcenter hcenterRe
      hcenterIm
  rw [show TileCentroid (D.tiles F.slot false) - TileCentroid Rminus =
    (TileCentroid (D.tiles F.slot false) - TileCentroid F.tile) -
      (TileCentroid Rminus - TileCentroid F.tile) by
        ext <;> dsimp <;> ring]
  rw [hUcenter, hMcenter]
  apply Prod.ext
  · simp [GaussianRealPoint, w, y, Prod.smul_mk]
    norm_num at hcenterRe ⊢
    linarith
  · simp [GaussianRealPoint, w, y, Prod.smul_mk]
    norm_num at hcenterIm ⊢
    linarith

end BoundaryFrameRowGeometry

end ApollonianSuperharmonic

end
