/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandVectors
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import LeanPool.ApollonianSuperharmonic.TileCentroid
public import Mathlib.Init


/-!
# BandParentCentroidComparison

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace BandParentCentroidComparison

/-- Shared centroidEquality fact. -/
theorem centroidEquality :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T₀ : ProtoTile), ∀ (q' : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (i' : Fin (3 : ℕ)), ∀ (hs : Bool), ∀ (S' : Fin (3 : ℕ) → Bool →
            ProtoTile), (∀ (j : Fin (3 : ℕ)), ∀ (t : Bool), TileCentroid (S' j t) - TileCentroid
            T₀ = (if t = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint
            (BandVectors.1 (q' (j + (2 : Fin (3 : ℕ))).succ) (q' (j + (1 : Fin (3 : ℕ))).succ)) -
            (-(GaussianRealPoint (BandVectors.1 (q' (j + (2 : Fin (3 : ℕ))).succ) (q' (j + (1 :
            Fin (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (q' (j + (2 : Fin (3 :
            ℕ))).succ) (q' (j + (1 : Fin (3 : ℕ))).succ))).1))) → (∀ (R : Fin (3 : ℕ) → Bool →
            ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid (R i s) - TileCentroid
            T₀ = (if s = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint
            (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)) -
            (-(GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin
            (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 :
            ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).1))) → (∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i' + r
        (BandVectors.1 (q' ((i' + 2).succ)) (q' ((i' + 1).succ)) = BandVectors.1 (q ((j +
            2).succ)) (q ((j + 1).succ))) → (TileCentroid (S' i' hs) = TileCentroid (R j hs)))) )
            := by
  classical
  intro q T₀ q' i' hs S' hcent' R hrootCent r j hvector
  calc
    TileCentroid (S' i' hs) =
        (TileCentroid (S' i' hs) - TileCentroid T₀) + TileCentroid T₀ := by abel
    _ = (TileCentroid (R j hs) - TileCentroid T₀) + TileCentroid T₀ := by
      rw [hcent' i' hs, hrootCent j hs, hvector]
    _ = TileCentroid (R j hs) := by abel


end BandParentCentroidComparison
end ApollonianSuperharmonic

end
