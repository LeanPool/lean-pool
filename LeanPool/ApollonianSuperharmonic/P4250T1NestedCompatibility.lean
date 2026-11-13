/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.BandPrototileNonempty

public import LeanPool.ApollonianSuperharmonic.P4250T1SlopeOffset
public import LeanPool.ApollonianSuperharmonic.RightSubtileOdometerCompatibility

-- [TABLET NODE: P4250T1NestedCompatibility]

/-!
# P4250T1NestedCompatibility

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace NestedCompatibilityGeometry

private theorem hroot :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), 1 <
            (cfg.firstPredecessor 0).1 ) := by
  classical
  intro q cfg
  rw [cfg.firstChild]
  have : (q 2).1 < (q 1).1 := cfg.order12
  have hq2 : 4 ≤ (q 2).1 := cfg.secondLarge
  omega

private theorem alignA :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let A := cert.P 0 true
        ∀ (U : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (k : Fin (3 : ℕ) → Bool → PartialOdometer), (∀
            (i : Fin (3 : ℕ)), ∀ (s : Bool), TileOdometer (cfg.firstPredecessor i.succ) (U i s)
            (k i s)) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid (U i s) - TileCentroid A
            = (if s = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint
            (BandVectors.1 (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ)
            (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint
            (BandVectors.1 (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ)
            (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint
            (BandVectors.1 (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ)
            (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ))).1))) → (∀ (i : Fin 3), ∀ (s :
            Bool), (U i s).cells = (cert.Q i s).cells ∧ ((U i s).cells = ∅ → (U i s).anchor =
            (cert.Q i s).anchor) ∧ FootprintVertices (U i s) = FootprintVertices (cert.Q i s))) )
            := by
  classical
  intro q cfg C T cert A U k hchildA hcentA i s
  have hocc := cert.plus_occurrence i s
  rcases hocc with ⟨hproto, _, hcent⟩
  have hcent' : TileCentroid (U i s) = TileCentroid (cert.Q i s) := by
    -- Both pieces have the same certified centroid displacement from A.
    have huc : TileCentroid (U i s) - TileCentroid A =
        (if s then (1 : Real) else -1) •
          ((1 / 2 : Real) • (GaussianRealPoint
            (BandVectors.1 (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ))) -
            (-(GaussianRealPoint (BandVectors.1
              (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ)))).2,
              (GaussianRealPoint (BandVectors.1
              (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ)))).1))) := by
      simpa [A] using hcentA i s
    have hvc : TileCentroid (cert.Q i s) - TileCentroid A =
        (if s then (1 : Real) else -1) •
          ((1 / 2 : Real) • (GaussianRealPoint
            (BandVectors.1 (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ))) -
            (-(GaussianRealPoint (BandVectors.1
              (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ)))).2,
              (GaussianRealPoint (BandVectors.1
              (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ)))).1))) := by
      simpa [A] using hcent
    calc
      TileCentroid (U i s) =
          (TileCentroid (U i s) - TileCentroid A) + TileCentroid A := by
            ext <;> simp [sub_eq_add_neg, add_comm, add_left_comm]
      _ = (TileCentroid (cert.Q i s) - TileCentroid A) + TileCentroid A := by
            rw [huc, hvc]
      _ = TileCentroid (cert.Q i s) := by
            ext <;> simp [sub_eq_add_neg, add_comm]
  have huniq := BandPrototileCentroidUnique (cfg.firstPredecessor i.succ)
    (U i s) (cert.Q i s) (TileOdometerBandPrototile _ _ _ (hchildA i s))
    hproto hcent'
  exact ⟨huniq.1, huniq.2,
    (ProtoTileObservableExtensionality (U i s) (cert.Q i s) huniq.1
      huniq.2).1⟩

private theorem alignB :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let B := cert.P 0 false
        ∀ (V : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (l : Fin (3 : ℕ) → Bool → PartialOdometer), (∀
            (i : Fin (3 : ℕ)), ∀ (s : Bool), TileOdometer (cfg.firstPredecessor i.succ) (V i s)
            (l i s)) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid (V i s) - TileCentroid B
            = (if s = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint
            (BandVectors.1 (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ)
            (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint
            (BandVectors.1 (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ)
            (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint
            (BandVectors.1 (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ)
            (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ))).1))) → (∀ (i : Fin 3), ∀ (s :
            Bool), (V i s).cells = (cert.S i s).cells ∧ ((V i s).cells = ∅ → (V i s).anchor =
            (cert.S i s).anchor) ∧ FootprintVertices (V i s) = FootprintVertices (cert.S i s))) )
            := by
  classical
  intro q cfg C T cert B V l hchildB hcentB i s
  obtain ⟨hproto, _, hcent⟩ := cert.minus_occurrence i s
  have hcent' : TileCentroid (V i s) = TileCentroid (cert.S i s) := by
    have hvc : TileCentroid (V i s) - TileCentroid B =
        (if s = true then (1 : Real) else -1) •
          ((1 / 2 : Real) • (GaussianRealPoint
            (BandVectors.1 (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ))) -
            (-(GaussianRealPoint (BandVectors.1
              (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ)))).2,
              (GaussianRealPoint (BandVectors.1
              (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ)))).1))) := by
      simpa [B] using hcentB i s
    have hsc : TileCentroid (cert.S i s) - TileCentroid B =
        (if s = true then (1 : Real) else -1) •
          ((1 / 2 : Real) • (GaussianRealPoint
            (BandVectors.1 (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ))) -
            (-(GaussianRealPoint (BandVectors.1
              (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ)))).2,
              (GaussianRealPoint (BandVectors.1
              (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ)))).1))) := by
      simpa [B] using hcent
    calc
      TileCentroid (V i s) =
          (TileCentroid (V i s) - TileCentroid B) + TileCentroid B := by
            ext <;> simp [sub_eq_add_neg, add_comm, add_left_comm]
      _ = (TileCentroid (cert.S i s) - TileCentroid B) + TileCentroid B := by
            rw [hvc, hsc]
      _ = TileCentroid (cert.S i s) := by
            ext <;> simp [sub_eq_add_neg, add_comm]
  have huniq := BandPrototileCentroidUnique (cfg.firstPredecessor i.succ)
    (V i s) (cert.S i s) (TileOdometerBandPrototile _ _ _ (hchildB i s))
    hproto hcent'
  exact ⟨huniq.1, huniq.2,
    (ProtoTileObservableExtensionality (V i s) (cert.S i s) huniq.1
      huniq.2).1⟩

private theorem pos2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), 0 <
            (cfg.firstPredecessor 2).1 ) := by
  classical
  intro q cfg
  rw [cfg.firstParentTwo]
  have := cfg.secondLarge
  omega

private theorem pos3 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), 0 <
            (cfg.firstPredecessor 3).1 ) := by
  classical
  intro q cfg
  rw [cfg.firstParentThree]
  have hn := (ProperBandCurvatureStructure q cfg.proper).2.1 2
  have hne := cfg.noLine 3
  have hnon : 0 ≤ (q 3).1 := by simpa using hn
  omega

private theorem hX :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let xv : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        let v21 : GaussianInt := BandVectors.1 (q 2) (q 1)
        (BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) + BandVectors.1 (q (1 : Fin (4
            : ℕ))) (q (3 : Fin (4 : ℕ))) + BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 :
            ℕ))) = (0 : GaussianInt)) → ((BandVectors.1 (cfg.firstPredecessor (3 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (2 : Fin (4 : ℕ))) + BandVectors.1 (cfg.firstPredecessor (1 :
            Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin (4 : ℕ))) + BandVectors.1
            (cfg.firstPredecessor (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4 : ℕ))) =
            (0 : GaussianInt)) → ((v21 = BandVectors.1 (q 2) (cfg.firstPredecessor 1) - I * w) →
            (xv = -v21 - (1 + I) * w))) ) := by
  classical
  intro q cfg I w xv v21 hcycV hpredV hv21
  apply eq_of_sub_eq_zero
  have hpred : w + xv + BandVectors.1 (q 2) (cfg.firstPredecessor 1) = 0 := by
    simpa [w, xv, cfg.firstParentTwo, cfg.firstParentThree] using hpredV
  calc
    _ = (w + xv + BandVectors.1 (q 2) (cfg.firstPredecessor 1)) +
        (v21 - (BandVectors.1 (q 2) (cfg.firstPredecessor 1) - I * w)) := by ring
    _ = 0 := by rw [hpred, hv21]; ring

private theorem hV13 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let xv : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        let v21 : GaussianInt := BandVectors.1 (q 2) (q 1)
        let v13 : GaussianInt := BandVectors.1 (q 1) (q 3)
        (BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) + BandVectors.1 (q (1 : Fin (4
            : ℕ))) (q (3 : Fin (4 : ℕ))) + BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 :
            ℕ))) = (0 : GaussianInt)) → ((xv = -v21 - (1 + I) * w) → (v13 = xv + I * w)) ) := by
  classical
  intro q cfg I w xv v21 v13 hcycV hX
  have hcyc : w + v13 + v21 = 0 := by simpa [w, v13, v21] using hcycV
  rw [hX]
  dsimp [v13, xv, w, v21]
  linear_combination hcyc

private theorem hXalpha :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let alpha : GaussianInt := BandVectors.2 (q 3) (q 2)
        let xa : GaussianInt := BandVectors.2 (cfg.firstPredecessor 1) (q 3)
        let a21 : GaussianInt := BandVectors.2 (q 2) (q 1)
        (BandVectors.2 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) + BandVectors.2 (q (1 : Fin (4
            : ℕ))) (q (3 : Fin (4 : ℕ))) + BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 :
            ℕ))) = (0 : GaussianInt)) → ((BandVectors.2 (cfg.firstPredecessor (3 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (2 : Fin (4 : ℕ))) + BandVectors.2 (cfg.firstPredecessor (1 :
            Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin (4 : ℕ))) + BandVectors.2
            (cfg.firstPredecessor (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4 : ℕ))) =
            (0 : GaussianInt)) → ((a21 = BandVectors.2 (q 2) (cfg.firstPredecessor 1) + I *
            alpha) → (xa = -a21 - (1 - I) * alpha))) ) := by
  classical
  intro q cfg I alpha xa a21 hcycA hpredA ha21
  apply eq_of_sub_eq_zero
  have hpred : alpha + xa + BandVectors.2 (q 2) (cfg.firstPredecessor 1) = 0 := by
    simpa [alpha, xa, cfg.firstParentTwo, cfg.firstParentThree] using hpredA
  calc
    _ = (alpha + xa + BandVectors.2 (q 2) (cfg.firstPredecessor 1)) +
        (a21 - (BandVectors.2 (q 2) (cfg.firstPredecessor 1) + I * alpha)) := by ring
    _ = 0 := by rw [hpred, ha21]; ring

private theorem hA13 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let alpha : GaussianInt := BandVectors.2 (q 3) (q 2)
        let xa : GaussianInt := BandVectors.2 (cfg.firstPredecessor 1) (q 3)
        let a21 : GaussianInt := BandVectors.2 (q 2) (q 1)
        let a13 : GaussianInt := BandVectors.2 (q 1) (q 3)
        (BandVectors.2 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) + BandVectors.2 (q (1 : Fin (4
            : ℕ))) (q (3 : Fin (4 : ℕ))) + BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 :
            ℕ))) = (0 : GaussianInt)) → ((xa = -a21 - (1 - I) * alpha) → (a13 = xa - I * alpha))
            ) := by
  classical
  intro q cfg I alpha xa a21 a13 hcycA hXalpha
  have hcyc : alpha + a13 + a21 = 0 := by simpa [alpha, a13, a21] using hcycA
  rw [hXalpha]
  dsimp [a13, xa, alpha, a21]
  linear_combination hcyc

private theorem spatialIdentity :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let xv : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        let v13 : GaussianInt := BandVectors.1 (q 1) (q 3)
        let spatial (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (v13 = xv + I * w) → (spatial v13 - spatial w - spatial xv = GaussianRealPoint (I * w)) )
            := by
  classical
  intro q cfg I w xv v13 spatial hV13
  rw [hV13]
  dsimp [spatial, GaussianRealPoint, I]
  ext <;> simp [] <;> ring

private theorem slopeIdentity :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let alpha : GaussianInt := BandVectors.2 (q 3) (q 2)
        let xa : GaussianInt := BandVectors.2 (cfg.firstPredecessor 1) (q 3)
        let a13 : GaussianInt := BandVectors.2 (q 1) (q 3)
        (a13 = xa - I * alpha) → (P4250T1SlopeOffset a13 - P4250T1SlopeOffset alpha -
            P4250T1SlopeOffset xa = -GaussianRealPoint (I * alpha)) ) := by
  classical
  intro q cfg I alpha xa a13 hA13
  rw [hA13]
  dsimp [P4250T1SlopeOffset, GaussianRealPoint, I]
  ext <;> simp [] <;> ring

private theorem hI2pow :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩
        (I * I = -1) → (I ^ 2 = -1) ) := by
  classical
  intro I hI2
  rw [pow_two]
  exact hI2

private theorem hIneg :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩
        (I * I = -1) → (I * (-I) = 1) ) := by
  classical
  intro I hI2
  rw [mul_neg, hI2]
  simp

private theorem hI3neg :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩
        (I * I = -1) → ((-I : GaussianInt) ^ 3 = I) ) := by
  classical
  intro I hI2
  have hneg2 : (-I : GaussianInt) * (-I) = -1 := by
    rw [neg_mul_neg, hI2]
  calc
    (-I : GaussianInt) ^ 3 = ((-I) * (-I)) * (-I) := by
      simp [pow_succ]
    _ = (-1) * (-I) := by rw [hneg2]
    _ = I := by simp

private theorem hI3 :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩
        (I ^ 2 = -1) → ((I : GaussianInt) ^ 3 = -I) ) := by
  classical
  intro I hI2pow
  calc
    I ^ 3 = I ^ 2 * I := by simp [pow_succ]
    _ = (-1) * I := by rw [hI2pow]
    _ = -I := by simp

private theorem hnegII :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩
        (I * I = -1) → ((-I : GaussianInt) * I = 1) ) := by
  classical
  intro I hI2
  rw [neg_mul, hI2]
  simp

private theorem hcenterQ :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let A := cert.P 0 true
        let xv : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        let spatial (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        TileCentroid (cert.Q 1 true) - TileCentroid A = spatial xv ) := by
  classical
  intro q cfg C T cert A xv spatial
  simpa [spatial, xv, Fin.add_def, cfg.firstParentThree] using
    (cert.plus_occurrence 1 true).2.2

private theorem hcenterQT :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let A := cert.P 0 true
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let xv : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        let spatial (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (TileCentroid A - TileCentroid T = spatial w) → ((TileCentroid (cert.Q 1 true) -
            TileCentroid A = spatial xv) → (TileCentroid (cert.Q 1 true) - TileCentroid T =
            spatial xv + spatial w)) ) := by
  classical
  intro q cfg C T cert A w xv spatial hcenterA hcenterQ
  calc
    _ = (TileCentroid (cert.Q 1 true) - TileCentroid A) +
        (TileCentroid A - TileCentroid T) := by
          ext <;> dsimp <;> ring
    _ = _ := by rw [hcenterQ, hcenterA]

private theorem hcenterDelta :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let I : GaussianInt := ⟨0, 1⟩
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let xv : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        let v13 : GaussianInt := BandVectors.1 (q 1) (q 3)
        let spatial (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (spatial v13 - spatial w - spatial xv = GaussianRealPoint (I * w)) → ((TileCentroid
            (cert.P 1 true) - TileCentroid T = spatial v13) → ((TileCentroid (cert.Q 1 true) -
            TileCentroid T = spatial xv + spatial w) → (TileCentroid (cert.P 1 true) -
            TileCentroid (cert.Q 1 true) = GaussianRealPoint (I * w)))) ) := by
  classical
  intro q cfg C T cert I w xv v13 spatial spatialIdentity hcenterP hcenterQT
  calc
    _ = (TileCentroid (cert.P 1 true) - TileCentroid T) -
        (TileCentroid (cert.Q 1 true) - TileCentroid T) := by
          ext <;> dsimp <;> ring
    _ = spatial v13 - spatial w - spatial xv := by
          rw [hcenterP, hcenterQT]
          ext <;> dsimp <;> ring
    _ = GaussianRealPoint (I * w) := spatialIdentity

private theorem rootSlope :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (h : Fin 3 → Bool → PartialOdometer), ∀ (s0 : Real ×
            Real), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), PartialOdometerSlope (h i s) = some (s0 +
            (if s = true then (1 : ℝ) else (-1 : ℝ)) • P4250T1SlopeOffset (BandVectors.2 (q (i
            + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)))) → (
        let a13 : GaussianInt := BandVectors.2 (q 1) (q 3)
        PartialOdometerSlope (h 1 true) = some (s0 + P4250T1SlopeOffset a13)) ) := by
  classical
  intro q h s0 hp a13
  simpa [a13, Fin.add_def] using hp 1 true

private theorem childSlope :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (h :
            Fin 3 → Bool → PartialOdometer), ∀ (s0 : Real × Real), (∀ (i : Fin (3 : ℕ)), ∀ (s :
            Bool), PartialOdometerSlope (h i s) = some (s0 + (if s = true then (1 : ℝ) else (-1 :
            ℝ)) • P4250T1SlopeOffset (BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1
            : Fin (3 : ℕ))).succ)))) → (∀ (k : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i : Fin
            (3 : ℕ)), ∀ (s : Bool), (cfg.firstPredecessor i.succ).1 = (0 : ℤ) ∨ ∃ (p : ℝ × ℝ)
            (p_i : ℝ × ℝ), PartialOdometerSlope (h (0 : Fin (3 : ℕ)) true) = some p ∧
            PartialOdometerSlope (k i s) = some p_i ∧ p_i.1 - p.1 = (if s = true then (1 : ℝ)
            else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (cfg.firstPredecessor (i + (2 : Fin
            (3 : ℕ))).succ) (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ) -
            (↑(BandVectors.2 (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ)
            (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)).im : ℝ)) ∧ p_i.2 - p.2 = (if s =
            true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2
            (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ) (cfg.firstPredecessor (i + (1 :
            Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (cfg.firstPredecessor (i + (2 : Fin
            (3 : ℕ))).succ) (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → ((0
            < (cfg.firstPredecessor 2).1) → (
        let alpha : GaussianInt := BandVectors.2 (q 3) (q 2)
        let xa : GaussianInt := BandVectors.2 (cfg.firstPredecessor 1) (q 3)
        PartialOdometerSlope (k 1 true) = some (s0 + P4250T1SlopeOffset alpha +
            P4250T1SlopeOffset xa)))) ) := by
  classical
  intro q cfg h s0 hp k hslopeA pos2 alpha xa
  rcases hslopeA 1 true with hz | hs
  · have hbad : (cfg.firstPredecessor 2).1 = 0 := hz
    have : (q 2).1 = 0 := by simpa [cfg.firstParentTwo] using hbad
    exact False.elim (by have := cfg.noLine 2; omega)
  · rcases hs with ⟨p, pi, hp0, hpi, hreal, himag⟩
    have hp0' : p = s0 + P4250T1SlopeOffset alpha := by
      have heq : some p = some (s0 + P4250T1SlopeOffset alpha) := by
        simpa [alpha, Fin.add_def] using hp0.symm.trans (hp 0 true)
      exact Option.some.inj heq
    have hpi' : pi = p + P4250T1SlopeOffset xa := by
      apply Prod.ext
      · have hreal' : pi.1 - p.1 =
            ((xa.re : Real) - (xa.im : Real)) / 2 := by
          convert hreal using 1; simp [xa, cfg.firstParentThree]; ring
        change pi.1 = p.1 + ((xa.re : Real) - (xa.im : Real)) / 2
        linarith
      · have himag' : pi.2 - p.2 =
            ((xa.im : Real) + (xa.re : Real)) / 2 := by
          convert himag using 1; simp [xa, cfg.firstParentThree]; ring
        change pi.2 = p.2 + ((xa.im : Real) + (xa.re : Real)) / 2
        linarith
    rw [hpi', hp0'] at hpi
    exact hpi

private theorem slopeDelta :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (s0 :
            Real × Real),
        let I : GaussianInt := ⟨0, 1⟩
        let alpha : GaussianInt := BandVectors.2 (q 3) (q 2)
        let xa : GaussianInt := BandVectors.2 (cfg.firstPredecessor 1) (q 3)
        let a13 : GaussianInt := BandVectors.2 (q 1) (q 3)
        (P4250T1SlopeOffset a13 - P4250T1SlopeOffset alpha - P4250T1SlopeOffset xa =
            -GaussianRealPoint (I * alpha)) → ((BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (3 : Fin
            (4 : ℕ))) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (q (3 : Fin (4 : ℕ)))
            (q (2 : Fin (4 : ℕ))) ∧ BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) =
            -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2 (q (3 : Fin (4 : ℕ))) (q (2 : Fin
            (4 : ℕ)))) → ((s0 + P4250T1SlopeOffset a13) - (s0 + P4250T1SlopeOffset alpha +
            P4250T1SlopeOffset xa) = GaussianRealPoint (BandVectors.2 (q 2) (q 3)))) ) := by
  classical
  intro q cfg s0 I alpha xa a13 slopeIdentity secondFlip
  calc
    _ = P4250T1SlopeOffset a13 - P4250T1SlopeOffset alpha -
        P4250T1SlopeOffset xa := by ext <;> dsimp <;> ring
    _ = -GaussianRealPoint (I * alpha) := slopeIdentity
    _ = GaussianRealPoint (BandVectors.2 (q 2) (q 3)) := by
      rw [secondFlip.2]
      dsimp [GaussianRealPoint, I, alpha]
      ext <;> simp

private theorem adjQ2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (h : Fin 3 → Bool → PartialOdometer), ∀ (s0 : Real × Real), (∀ (i : Fin (3 :
            ℕ)), ∀ (s : Bool), TileOdometer (q i.succ) (cert.P i s) (h i s)) → (∀ (k : Fin (3 :
            ℕ) → Bool → PartialOdometer), (TileOdometer (cfg.firstPredecessor 2) (cert.Q 1 true)
            (k 1 true)) → (
        let alpha : GaussianInt := BandVectors.2 (q 3) (q 2)
        let xa : GaussianInt := BandVectors.2 (cfg.firstPredecessor 1) (q 3)
        let a13 : GaussianInt := BandVectors.2 (q 1) (q 3)
        (TileCentroid (cert.P (1 : Fin (3 : ℕ)) true) - TileCentroid (cert.Q (1 : Fin (3 : ℕ))
            true) = GaussianRealPoint (BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (3 : Fin (4 :
            ℕ))))) → ((PartialOdometerSlope (h (1 : Fin (3 : ℕ)) true) = some (s0 +
            P4250T1SlopeOffset a13)) → ((PartialOdometerSlope (k (1 : Fin (3 : ℕ)) true) = some
            (s0 + P4250T1SlopeOffset alpha + P4250T1SlopeOffset xa)) → (((s0 +
            P4250T1SlopeOffset a13) - (s0 + P4250T1SlopeOffset alpha + P4250T1SlopeOffset
            xa) = GaussianRealPoint (BandVectors.2 (q 2) (q 3))) → (∀ (posRoot2 : 0 < (q 2).1),
        let C2 : BandCircle :=
          ⟨⟨q 2, Or.inl posRoot2, q, cfg.proper.1, 2, rfl⟩, posRoot2⟩
        RightLatticeAdjacent C2 (cert.Q 1 true) (cert.P 1 true) (k 1 true) (h 1 true))))))) ) := by
  classical
  intro q cfg C T cert h s0 ho k odoQ2 alpha xa a13 hcenterDelta rootSlope childSlope slopeDelta
      posRoot2 C2
  refine ⟨?_, ?_, s0 + P4250T1SlopeOffset alpha +
    P4250T1SlopeOffset xa, s0 + P4250T1SlopeOffset a13,
    childSlope, rootSlope, cfg.secondPredecessor, 0, true,
    cfg.secondProper, cfg.secondChild, ?_, ?_, ?_⟩
  · simpa [C2, cfg.firstParentTwo] using odoQ2
  · simpa [C2, cfg.firstParentTwo] using ho 1 true
  · simpa [Fin.succ_zero_eq_one, cfg.secondChild, cfg.secondParentOne] using
      hcenterDelta
  · simpa [cfg.secondChild, cfg.secondParentOne, GaussianRealPoint,
      Fin.succ_zero_eq_one] using
      congrArg Prod.fst slopeDelta
  · simpa [cfg.secondChild, cfg.secondParentOne, GaussianRealPoint,
      Fin.succ_zero_eq_one] using
      congrArg Prod.snd slopeDelta

private theorem rawCompatLift :
    (by
      classical
      exact
        ∀ (a : PartialOdometer), ∀ (b : PartialOdometer), ∀ (r : PartialOdometer), ∀ (X :
            ProtoTile), ∀ (Y : ProtoTile), ∀ (Z : ProtoTile), ((a.domain : Set GaussianInt) =
            FootprintVertices X) → (((b.domain : Set GaussianInt) = FootprintVertices Y) →
            (((r.domain : Set GaussianInt) = FootprintVertices Z) → ((∀ x, x ∈ r.domain → a.value
            x = r.value x) → ((FootprintVertices X ∩ FootprintVertices Y ⊆
            FootprintVertices Z ∩ FootprintVertices Y) → ((OdometerCompatibility r b) →
                (OdometerCompatibility a b)))))) ) := by
  classical
  intro a b r X Y Z hX hY hZ hrestrict hcover hcompat
  rcases hcompat with hd | ⟨c, hc⟩
  · left
    apply Set.disjoint_left.mpr
    intro x hxa hxb
    have hxX : x ∈ FootprintVertices X := (Set.ext_iff.mp hX x).mp hxa
    have hxY : x ∈ FootprintVertices Y := (Set.ext_iff.mp hY x).mp hxb
    have hxZ : x ∈ FootprintVertices Z := (hcover ⟨hxX, hxY⟩).1
    exact (Set.disjoint_left.mp hd)
      ((Set.ext_iff.mp hZ x).mpr hxZ) hxb
  · right
    refine ⟨c, ?_⟩
    intro x hxa hxb
    have hxX : x ∈ FootprintVertices X := (Set.ext_iff.mp hX x).mp hxa
    have hxY : x ∈ FootprintVertices Y := (Set.ext_iff.mp hY x).mp hxb
    have hxZ : x ∈ FootprintVertices Z := (hcover ⟨hxX, hxY⟩).1
    have hxr : x ∈ r.domain := (Set.ext_iff.mp hZ x).mpr hxZ
    have hconst := hc x hxr hxb
    rw [(hrestrict x hxr).symm] at hconst
    exact hconst

private theorem hq1pos :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), (1 <
            (cfg.firstPredecessor 0).1) → (0 < (q 1).1) ) := by
  classical
  intro q cfg hroot
  exact lt_trans (by norm_num : (0 : Int) < 1)
    (by simpa [cfg.firstChild] using hroot)

private theorem hcenterS :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let B := cert.P 0 false
        let xv : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        let spatial (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        TileCentroid (cert.S 1 false) - TileCentroid B = -spatial xv ) := by
  classical
  intro q cfg C T cert B xv spatial
  simpa [spatial, xv, Fin.add_def, cfg.firstParentThree] using
    (cert.minus_occurrence 1 false).2.2

private theorem hcenterPminus :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let v13 : GaussianInt := BandVectors.1 (q 1) (q 3)
        let spatial (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        TileCentroid (cert.P 1 false) - TileCentroid T = -spatial v13 ) := by
  classical
  intro q cfg C T cert v13 spatial
  simpa [spatial, v13, Fin.add_def] using (cert.outer_occurrence 1 false).2.2

private theorem hcenterDeltaMinus :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let B := cert.P 0 false
        let I : GaussianInt := ⟨0, 1⟩
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let xv : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        let v13 : GaussianInt := BandVectors.1 (q 1) (q 3)
        let spatial (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (spatial v13 - spatial w - spatial xv = GaussianRealPoint (I * w)) → ((BandVectors.1 (q
            (2 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) ∧ BandVectors.2 (q (2 : Fin
            (4 : ℕ))) (q (3 : Fin (4 : ℕ))) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2
            (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))) → ((TileCentroid B - TileCentroid T =
            -spatial w) → ((TileCentroid (cert.S 1 false) - TileCentroid B = -spatial xv) →
            ((TileCentroid (cert.P 1 false) - TileCentroid T = -spatial v13) → (TileCentroid
            (cert.P 1 false) - TileCentroid (cert.S 1 false) = -GaussianRealPoint (BandVectors.1
            (q 2) (q 3))))))) ) := by
  classical
  intro q cfg C T cert B I w xv v13 spatial spatialIdentity secondFlip hcenterB hcenterS
      hcenterPminus
  have hcenterST : TileCentroid (cert.S 1 false) - TileCentroid T =
      -spatial xv - spatial w := by
    calc
      _ = (TileCentroid (cert.S 1 false) - TileCentroid B) +
          (TileCentroid B - TileCentroid T) := by ext <;> dsimp <;> ring
      _ = _ := by
        rw [hcenterS, hcenterB]
        ext <;> dsimp <;> ring
  calc
    _ = (TileCentroid (cert.P 1 false) - TileCentroid T) -
        (TileCentroid (cert.S 1 false) - TileCentroid T) := by
          ext <;> dsimp <;> ring
    _ = -spatial v13 + spatial xv + spatial w := by
          rw [hcenterPminus, hcenterST]
          ext <;> dsimp <;> ring
    _ = -GaussianRealPoint (I * w) := by
          rw [← spatialIdentity]
          ext <;> dsimp <;> ring
    _ = -GaussianRealPoint (BandVectors.1 (q 2) (q 3)) := by
          rw [← secondFlip.1]

private theorem childSlopeMinus :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (h :
            Fin 3 → Bool → PartialOdometer), ∀ (s0 : Real × Real), (∀ (i : Fin (3 : ℕ)), ∀ (s :
            Bool), PartialOdometerSlope (h i s) = some (s0 + (if s = true then (1 : ℝ) else (-1 :
            ℝ)) • P4250T1SlopeOffset (BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1
            : Fin (3 : ℕ))).succ)))) → (∀ (l : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i : Fin
            (3 : ℕ)), ∀ (s : Bool), (cfg.firstPredecessor i.succ).1 = (0 : ℤ) ∨ ∃ (p : ℝ × ℝ)
            (p_i : ℝ × ℝ), PartialOdometerSlope (h (0 : Fin (3 : ℕ)) false) = some p ∧
            PartialOdometerSlope (l i s) = some p_i ∧ p_i.1 - p.1 = (if s = true then (1 : ℝ)
            else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (cfg.firstPredecessor (i + (2 : Fin
            (3 : ℕ))).succ) (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ) -
            (↑(BandVectors.2 (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ)
            (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)).im : ℝ)) ∧ p_i.2 - p.2 = (if s =
            true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2
            (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ) (cfg.firstPredecessor (i + (1 :
            Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (cfg.firstPredecessor (i + (2 : Fin
            (3 : ℕ))).succ) (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → ((0
            < (cfg.firstPredecessor 2).1) → (
        let alpha : GaussianInt := BandVectors.2 (q 3) (q 2)
        let xa : GaussianInt := BandVectors.2 (cfg.firstPredecessor 1) (q 3)
        PartialOdometerSlope (l 1 false) = some (s0 - P4250T1SlopeOffset alpha -
            P4250T1SlopeOffset xa)))) ) := by
  classical
  intro q cfg h s0 hp l hslopeB pos2 alpha xa
  rcases hslopeB 1 false with hz | hs
  · have hbad : (cfg.firstPredecessor 2).1 = 0 := hz
    have : (q 2).1 = 0 := by simpa [cfg.firstParentTwo] using hbad
    exact False.elim (by have := cfg.noLine 2; omega)
  · rcases hs with ⟨p, pi, hp0, hpi, hreal, himag⟩
    have hp0' : p = s0 - P4250T1SlopeOffset alpha := by
      have heq : some p = some (s0 - P4250T1SlopeOffset alpha) := by
        simpa [alpha, Fin.add_def, sub_eq_add_neg, smul_eq_mul] using
          hp0.symm.trans (hp 0 false)
      exact Option.some.inj heq
    have hpi' : pi = p - P4250T1SlopeOffset xa := by
      apply Prod.ext
      · have hreal' : pi.1 - p.1 =
            -((xa.re : Real) - (xa.im : Real)) / 2 := by
          convert hreal using 1; simp [xa, cfg.firstParentThree]; ring
        change pi.1 = p.1 - ((xa.re : Real) - (xa.im : Real)) / 2
        linarith
      · have himag' : pi.2 - p.2 =
            -((xa.im : Real) + (xa.re : Real)) / 2 := by
          convert himag using 1; simp [xa, cfg.firstParentThree]; ring
        change pi.2 = p.2 - ((xa.im : Real) + (xa.re : Real)) / 2
        linarith
    rw [hpi', hp0'] at hpi
    exact hpi

private theorem rootSlopeMinus :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (h : Fin 3 → Bool → PartialOdometer), ∀ (s0 : Real ×
            Real), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), PartialOdometerSlope (h i s) = some (s0 +
            (if s = true then (1 : ℝ) else (-1 : ℝ)) • P4250T1SlopeOffset (BandVectors.2 (q (i
            + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)))) → (
        let a13 : GaussianInt := BandVectors.2 (q 1) (q 3)
        PartialOdometerSlope (h 1 false) = some (s0 - P4250T1SlopeOffset a13)) ) := by
  classical
  intro q h s0 hp a13
  simpa [a13, Fin.add_def, sub_eq_add_neg, smul_eq_mul] using hp 1 false

private theorem slopeIdentityMinus :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let alpha : GaussianInt := BandVectors.2 (q 3) (q 2)
        let xa : GaussianInt := BandVectors.2 (cfg.firstPredecessor 1) (q 3)
        let a13 : GaussianInt := BandVectors.2 (q 1) (q 3)
        (P4250T1SlopeOffset a13 - P4250T1SlopeOffset alpha - P4250T1SlopeOffset xa =
            -GaussianRealPoint (I * alpha)) → (P4250T1SlopeOffset alpha + P4250T1SlopeOffset
            xa - P4250T1SlopeOffset a13 = GaussianRealPoint (I * alpha)) ) := by
  classical
  intro q cfg I alpha xa a13 slopeIdentity
  calc
    _ = -(P4250T1SlopeOffset a13 - P4250T1SlopeOffset alpha -
        P4250T1SlopeOffset xa) := by ext <;> dsimp <;> ring
    _ = GaussianRealPoint (I * alpha) := by rw [slopeIdentity]; simp

private theorem slopeDeltaMinus :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (s0 :
            Real × Real),
        let I : GaussianInt := ⟨0, 1⟩
        let alpha : GaussianInt := BandVectors.2 (q 3) (q 2)
        let xa : GaussianInt := BandVectors.2 (cfg.firstPredecessor 1) (q 3)
        let a13 : GaussianInt := BandVectors.2 (q 1) (q 3)
        (BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) = (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) ∧
            BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) = -(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.2 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))) →
            ((P4250T1SlopeOffset alpha + P4250T1SlopeOffset xa - P4250T1SlopeOffset a13 =
            GaussianRealPoint (I * alpha)) → ((s0 - P4250T1SlopeOffset a13) - (s0 -
            P4250T1SlopeOffset alpha - P4250T1SlopeOffset xa) = -GaussianRealPoint
            (BandVectors.2 (q 2) (q 3)))) ) := by
  classical
  intro q cfg s0 I alpha xa a13 secondFlip slopeIdentityMinus
  have hflip := secondFlip.2
  calc
    _ = P4250T1SlopeOffset alpha + P4250T1SlopeOffset xa -
        P4250T1SlopeOffset a13 := by ext <;> dsimp <;> ring
    _ = GaussianRealPoint (I * alpha) := slopeIdentityMinus
    _ = -GaussianRealPoint (BandVectors.2 (q 2) (q 3)) := by
      rw [hflip]
      dsimp [GaussianRealPoint, I, alpha]
      ext <;> simp

private theorem adjS2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (h : Fin 3 → Bool → PartialOdometer), ∀ (s0 : Real × Real), (∀ (i : Fin (3 :
            ℕ)), ∀ (s : Bool), TileOdometer (q i.succ) (cert.P i s) (h i s)) → (∀ (l : Fin (3 :
            ℕ) → Bool → PartialOdometer), (TileOdometer (cfg.firstPredecessor 2) (cert.S 1 false)
            (l 1 false)) → (
        let alpha : GaussianInt := BandVectors.2 (q 3) (q 2)
        let xa : GaussianInt := BandVectors.2 (cfg.firstPredecessor 1) (q 3)
        let a13 : GaussianInt := BandVectors.2 (q 1) (q 3)
        ∀ (posRoot2 : 0 < (q 2).1),
        let C2 : BandCircle :=
          ⟨⟨q 2, Or.inl posRoot2, q, cfg.proper.1, 2, rfl⟩, posRoot2⟩
        (TileCentroid (cert.P 1 false) - TileCentroid (cert.S 1 false) = -GaussianRealPoint
            (BandVectors.1 (q 2) (q 3))) → ((PartialOdometerSlope (l 1 false) = some (s0 -
            P4250T1SlopeOffset alpha - P4250T1SlopeOffset xa)) → ((PartialOdometerSlope (h 1
            false) = some (s0 - P4250T1SlopeOffset a13)) → (((s0 - P4250T1SlopeOffset a13) -
            (s0 - P4250T1SlopeOffset alpha - P4250T1SlopeOffset xa) = -GaussianRealPoint
            (BandVectors.2 (q 2) (q 3))) → (RightLatticeAdjacent C2 (cert.S 1 false) (cert.P 1
            false) (l 1 false) (h 1 false))))))) ) := by
  classical
  intro q cfg C T cert h s0 ho l odoS2 alpha xa a13 posRoot2 C2 hcenterDeltaMinus childSlopeMinus
      rootSlopeMinus slopeDeltaMinus
  refine ⟨?_, ?_, s0 - P4250T1SlopeOffset alpha -
    P4250T1SlopeOffset xa, s0 - P4250T1SlopeOffset a13,
    childSlopeMinus, rootSlopeMinus, cfg.secondPredecessor, 0, false,
    cfg.secondProper, cfg.secondChild, ?_, ?_, ?_⟩
  · simpa [C2, cfg.firstParentTwo] using odoS2
  · simpa [C2, cfg.firstParentTwo] using ho 1 false
  · simpa [Fin.succ_zero_eq_one, cfg.secondChild, cfg.secondParentOne] using
      hcenterDeltaMinus
  · simpa [cfg.secondChild, cfg.secondParentOne, GaussianRealPoint,
      Fin.succ_zero_eq_one] using
      congrArg Prod.fst slopeDeltaMinus
  · simpa [cfg.secondChild, cfg.secondParentOne, GaussianRealPoint,
      Fin.succ_zero_eq_one] using
      congrArg Prod.snd slopeDeltaMinus

private theorem childSlopeS3 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (h :
            Fin 3 → Bool → PartialOdometer), ∀ (s0 : Real × Real), (∀ (i : Fin (3 : ℕ)), ∀ (s :
            Bool), PartialOdometerSlope (h i s) = some (s0 + (if s = true then (1 : ℝ) else (-1 :
            ℝ)) • P4250T1SlopeOffset (BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1
            : Fin (3 : ℕ))).succ)))) → (∀ (l : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i : Fin
            (3 : ℕ)), ∀ (s : Bool), (cfg.firstPredecessor i.succ).1 = (0 : ℤ) ∨ ∃ (p : ℝ × ℝ)
            (p_i : ℝ × ℝ), PartialOdometerSlope (h (0 : Fin (3 : ℕ)) false) = some p ∧
            PartialOdometerSlope (l i s) = some p_i ∧ p_i.1 - p.1 = (if s = true then (1 : ℝ)
            else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (cfg.firstPredecessor (i + (2 : Fin
            (3 : ℕ))).succ) (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ) -
            (↑(BandVectors.2 (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ)
            (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)).im : ℝ)) ∧ p_i.2 - p.2 = (if s =
            true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2
            (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ) (cfg.firstPredecessor (i + (1 :
            Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (cfg.firstPredecessor (i + (2 : Fin
            (3 : ℕ))).succ) (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → ((0
            < (cfg.firstPredecessor 3).1) → (
        let alpha : GaussianInt := BandVectors.2 (q 3) (q 2)
        let x2a : GaussianInt :=
          BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1)
        PartialOdometerSlope (l 2 false) = some (s0 - P4250T1SlopeOffset alpha -
            P4250T1SlopeOffset x2a)))) ) := by
  classical
  intro q cfg h s0 hp l hslopeB pos3 alpha x2a
  rcases hslopeB 2 false with hz | hs
  · have hbad : (cfg.firstPredecessor 3).1 = 0 := hz
    have : (q 3).1 = 0 := by simpa [cfg.firstParentThree] using hbad
    exact False.elim (by have := cfg.noLine 3; omega)
  · rcases hs with ⟨p, pi, hp0, hpi, hreal, himag⟩
    have hp0' : p = s0 - P4250T1SlopeOffset alpha := by
      have heq : some p = some (s0 - P4250T1SlopeOffset alpha) := by
        simpa [alpha, Fin.add_def, sub_eq_add_neg, smul_eq_mul] using
          hp0.symm.trans (hp 0 false)
      exact Option.some.inj heq
    have hpi' : pi = p - P4250T1SlopeOffset x2a := by
      apply Prod.ext
      · have hreal' : pi.1 - p.1 =
            -((x2a.re : Real) - (x2a.im : Real)) / 2 := by
          convert hreal using 1;
            simp [x2a, Fin.add_def]; ring
        change pi.1 = p.1 - ((x2a.re : Real) - (x2a.im : Real)) / 2
        linarith
      · have himag' : pi.2 - p.2 =
            -((x2a.im : Real) + (x2a.re : Real)) / 2 := by
          convert himag using 1;
            simp [x2a, Fin.add_def]; ring
        change pi.2 = p.2 - ((x2a.im : Real) + (x2a.re : Real)) / 2
        linarith
    rw [hpi', hp0'] at hpi
    exact hpi

private theorem hcenterS3 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let B := cert.P 0 false
        ∀ (V : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid
            (V i s) - TileCentroid B = (if s = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) •
            (GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ)
            (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint
            (BandVectors.1 (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ)
            (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint
            (BandVectors.1 (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ)
            (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ))).1))) → ((∀ (i : Fin 3), ∀ (s :
            Bool), (V i s).cells = (cert.S i s).cells ∧ ((V i s).cells = ∅ → (V i s).anchor =
            (cert.S i s).anchor) ∧ FootprintVertices (V i s) = FootprintVertices (cert.S i s)) → (
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let spatial (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (TileCentroid B - TileCentroid T = -spatial w) → (
        let x2v : GaussianInt :=
          BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1)
        TileCentroid (cert.S 2 false) - TileCentroid T = -spatial w - spatial x2v))) ) := by
  classical
  intro q cfg C T cert B V hcentB alignB w spatial hcenterB x2v
  have hsb : TileCentroid (cert.S 2 false) - TileCentroid B =
      -spatial x2v := by
    have hc := hcentB 2 false
    have hc' : TileCentroid (V 2 false) =
        TileCentroid (cert.S 2 false) := by
      by_cases he : (V 2 false).cells = ∅
      · simp [TileCentroid, (alignB 2 false).1,
          (alignB 2 false).2.1 he]
      · have hne : (cert.S 2 false).cells.Nonempty := by
          rw [← (alignB 2 false).1]
          exact Finset.nonempty_iff_ne_empty.mpr he
        simp [TileCentroid, (alignB 2 false).1, hne]
    have hc'' : TileCentroid (cert.S 2 false) - TileCentroid B =
        (if false = true then (1 : Real) else -1) •
          ((1 / 2 : Real) • (GaussianRealPoint x2v -
            (-(GaussianRealPoint x2v).2, (GaussianRealPoint x2v).1))) := by
      simpa [hc', x2v, Fin.add_def] using hc
    convert hc'' using 1; ext <;> dsimp [spatial] <;> ring
  calc
    _ = (TileCentroid (cert.S 2 false) - TileCentroid B) +
        (TileCentroid B - TileCentroid T) := by ext <;> dsimp <;> ring
    _ = _ := by rw [hsb, hcenterB]; ext <;> dsimp <;> ring

private theorem crossSpatial :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let I : GaussianInt := ⟨0, 1⟩
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let xv : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        let spatial (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (BandVectors.1 (cfg.firstPredecessor (3 : Fin (4 : ℕ))) (cfg.firstPredecessor (2 : Fin (4
            : ℕ))) + BandVectors.1 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor
            (3 : Fin (4 : ℕ))) + BandVectors.1 (cfg.firstPredecessor (2 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) = (0 : GaussianInt)) → ((TileCentroid
            (cert.Q 1 true) - TileCentroid T = spatial xv + spatial w) → (
        let x2v : GaussianInt :=
          BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1)
        (TileCentroid (cert.S 2 false) - TileCentroid T = -spatial w - spatial x2v) →
            (TileCentroid (cert.S 2 false) - TileCentroid (cert.Q 1 true) = (1 / 2 : Real) •
            GaussianRealPoint ((I : GaussianInt) * (w + I * w))))) ) := by
  classical
  intro q cfg C T cert I w xv spatial hpredV hcenterQT x2v hcenterS3
  have hsum : w + xv + x2v = 0 := by
    simpa [w, xv, x2v, cfg.firstParentTwo, cfg.firstParentThree] using hpredV
  have hdelta : (-spatial w - spatial x2v) -
      (spatial xv + spatial w) = -spatial w := by
    rw [show x2v = -w - xv by linear_combination hsum]
    ext <;> simp [spatial, GaussianRealPoint]  <;> ring
  calc
    _ = (TileCentroid (cert.S 2 false) - TileCentroid T) -
        (TileCentroid (cert.Q 1 true) - TileCentroid T) := by
      ext <;> dsimp <;> ring
    _ = (-spatial w - spatial x2v) - (spatial xv + spatial w) := by
      rw [hcenterS3, hcenterQT]
    _ = -spatial w := hdelta
    _ = (1 / 2 : Real) • GaussianRealPoint
        ((I : GaussianInt) * (w + I * w)) := by
      dsimp [spatial, GaussianRealPoint, I]
      ext <;> simp [] <;> all_goals ring

private theorem crossSlope :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (s0 :
            Real × Real),
        let I : GaussianInt := ⟨0, 1⟩
        let alpha : GaussianInt := BandVectors.2 (q 3) (q 2)
        let xa : GaussianInt := BandVectors.2 (cfg.firstPredecessor 1) (q 3)
        (BandVectors.2 (cfg.firstPredecessor (3 : Fin (4 : ℕ))) (cfg.firstPredecessor (2 : Fin (4
            : ℕ))) + BandVectors.2 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor
            (3 : Fin (4 : ℕ))) + BandVectors.2 (cfg.firstPredecessor (2 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) = (0 : GaussianInt)) → ((BandVectors.1 (q (2
            : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) ∧ BandVectors.2 (q (2 : Fin
            (4 : ℕ))) (q (3 : Fin (4 : ℕ))) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2
            (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))) → (
        let x2a : GaussianInt :=
          BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1)
        (s0 - P4250T1SlopeOffset alpha - P4250T1SlopeOffset x2a) - (s0 + P4250T1SlopeOffset
            alpha + P4250T1SlopeOffset xa) = (1 / 2 : Real) • GaussianRealPoint ((-I :
            GaussianInt) * (alpha + BandVectors.2 (q 2) (q 3))))) ) := by
  classical
  intro q cfg s0 I alpha xa hpredA secondFlip x2a
  have hsum : alpha + xa + x2a = 0 := by
    simpa [alpha, xa, x2a, cfg.firstParentTwo, cfg.firstParentThree] using hpredA
  have hdelta : (-2 : Real) • P4250T1SlopeOffset alpha -
      P4250T1SlopeOffset x2a - P4250T1SlopeOffset xa =
        -P4250T1SlopeOffset alpha := by
    rw [show x2a = -alpha - xa by linear_combination hsum]
    ext <;> dsimp [P4250T1SlopeOffset] <;> push_cast <;> ring
  calc
    _ = (-2 : Real) • P4250T1SlopeOffset alpha -
        P4250T1SlopeOffset x2a - P4250T1SlopeOffset xa := by
          ext <;> dsimp <;> ring
    _ = -P4250T1SlopeOffset alpha := hdelta
    _ = (1 / 2 : Real) • GaussianRealPoint
        ((-I : GaussianInt) *
          (alpha + BandVectors.2 (q 2) (q 3))) := by
      rw [secondFlip.2]
      dsimp [P4250T1SlopeOffset, GaussianRealPoint, I, alpha]
      ext <;> simp <;> ring

private theorem posRoot3 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandOrderedGeneralConfiguration q) → (0 < (q 3).1) )
            := by
  classical
  intro q cfg
  have hn := (ProperBandCurvatureStructure q cfg.proper).2.1 2
  have hnon : 0 ≤ (q 3).1 := by simpa using hn
  have hne := cfg.noLine 3
  omega

private theorem adjCross1 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (s0 : Real × Real), ∀ (k : Fin (3 : ℕ) → Bool → PartialOdometer), ∀ (l : Fin (3
            : ℕ) → Bool → PartialOdometer), (TileOdometer (cfg.firstPredecessor 2) (cert.Q 1
            true) (k 1 true)) → ((TileOdometer (cfg.firstPredecessor 3) (cert.S 2 false) (l 2
            false)) → (
        let I : GaussianInt := ⟨0, 1⟩
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let alpha : GaussianInt := BandVectors.2 (q 3) (q 2)
        let xa : GaussianInt := BandVectors.2 (cfg.firstPredecessor 1) (q 3)
        (BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) = (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) ∧
            BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) = -(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.2 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))) →
            ((PartialOdometerSlope (k (1 : Fin (3 : ℕ)) true) = some (s0 + P4250T1SlopeOffset
            alpha + P4250T1SlopeOffset xa)) → (∀ (posRoot2 : 0 < (q 2).1),
        let C2 : BandCircle :=
          ⟨⟨q 2, Or.inl posRoot2, q, cfg.proper.1, 2, rfl⟩, posRoot2⟩
        let x2a : GaussianInt :=
          BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1)
        (PartialOdometerSlope (l 2 false) = some (s0 - P4250T1SlopeOffset alpha -
            P4250T1SlopeOffset x2a)) → ((TileCentroid (cert.S 2 false) - TileCentroid (cert.Q 1
            true) = (1 / 2 : Real) • GaussianRealPoint ((I : GaussianInt) * (w + I * w))) → (((s0
            - P4250T1SlopeOffset alpha - P4250T1SlopeOffset x2a) - (s0 + P4250T1SlopeOffset
            alpha + P4250T1SlopeOffset xa) = (1 / 2 : Real) • GaussianRealPoint ((-I :
            GaussianInt) * (alpha + BandVectors.2 (q 2) (q 3)))) → (∀ (posRoot3 : 0 < (q 3).1),
        let C3 : BandCircle :=
          ⟨⟨q 3, Or.inl posRoot3, q, cfg.proper.1, 3, rfl⟩, posRoot3⟩
        SubtileLatticeAdjacent C2 C3 (cert.Q 1 true) (cert.S 2 false) (k 1 true) (l 2
            false)))))))) ) := by
  classical
  intro q cfg C T cert s0 k l odoQ2 odoS3 I w alpha xa secondFlip childSlope posRoot2 C2 x2a
      childSlopeS3 crossSpatial crossSlope posRoot3 C3
  refine ⟨?_, ?_, ⟨s0 + P4250T1SlopeOffset alpha +
    P4250T1SlopeOffset xa,
    s0 - P4250T1SlopeOffset alpha -
      P4250T1SlopeOffset x2a,
    childSlope, childSlopeS3, cfg.secondPredecessor, 0, 1,
    cfg.secondProper, cfg.secondChild, cfg.secondParentOne, ?_, ?_, ?_⟩⟩
  · simpa [C2, cfg.firstParentTwo] using odoQ2
  · simpa [C3, cfg.firstParentThree] using odoS3
  · simp only [show (0 : Fin 3).succ = (1 : Fin 4) from rfl,
      cfg.secondChild, cfg.secondParentOne]
    rw [secondFlip.1]
    exact crossSpatial
  · simp only [show (0 : Fin 3).succ = (1 : Fin 4) from rfl,
      cfg.secondChild, cfg.secondParentOne]
    simpa [pow_one] using congrArg Prod.fst crossSlope
  · simp only [show (0 : Fin 3).succ = (1 : Fin 4) from rfl,
      cfg.secondChild, cfg.secondParentOne]
    simpa [pow_one] using congrArg Prod.snd crossSlope

private theorem childSlopeQ3 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (h :
            Fin 3 → Bool → PartialOdometer), ∀ (s0 : Real × Real), (∀ (i : Fin (3 : ℕ)), ∀ (s :
            Bool), PartialOdometerSlope (h i s) = some (s0 + (if s = true then (1 : ℝ) else (-1 :
            ℝ)) • P4250T1SlopeOffset (BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1
            : Fin (3 : ℕ))).succ)))) → (∀ (k : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i : Fin
            (3 : ℕ)), ∀ (s : Bool), (cfg.firstPredecessor i.succ).1 = (0 : ℤ) ∨ ∃ (p : ℝ × ℝ)
            (p_i : ℝ × ℝ), PartialOdometerSlope (h (0 : Fin (3 : ℕ)) true) = some p ∧
            PartialOdometerSlope (k i s) = some p_i ∧ p_i.1 - p.1 = (if s = true then (1 : ℝ)
            else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (cfg.firstPredecessor (i + (2 : Fin
            (3 : ℕ))).succ) (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ) -
            (↑(BandVectors.2 (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ)
            (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)).im : ℝ)) ∧ p_i.2 - p.2 = (if s =
            true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2
            (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ) (cfg.firstPredecessor (i + (1 :
            Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (cfg.firstPredecessor (i + (2 : Fin
            (3 : ℕ))).succ) (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → ((0
            < (cfg.firstPredecessor 3).1) → (
        let alpha : GaussianInt := BandVectors.2 (q 3) (q 2)
        let x2a : GaussianInt :=
          BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1)
        PartialOdometerSlope (k 2 true) = some (s0 + P4250T1SlopeOffset alpha +
            P4250T1SlopeOffset x2a)))) ) := by
  classical
  intro q cfg h s0 hp k hslopeA pos3 alpha x2a
  rcases hslopeA 2 true with hz | hs
  · have hbad : (cfg.firstPredecessor 3).1 = 0 := hz
    have : (q 3).1 = 0 := by simpa [cfg.firstParentThree] using hbad
    exact False.elim (by have := cfg.noLine 3; omega)
  · rcases hs with ⟨p, pi, hp0, hpi, hreal, himag⟩
    have hp0' : p = s0 + P4250T1SlopeOffset alpha := by
      have heq : some p = some (s0 + P4250T1SlopeOffset alpha) := by
        simpa [alpha, Fin.add_def] using hp0.symm.trans (hp 0 true)
      exact Option.some.inj heq
    have hpi' : pi = p + P4250T1SlopeOffset x2a := by
      apply Prod.ext
      · have hreal' : pi.1 - p.1 =
            ((x2a.re : Real) - (x2a.im : Real)) / 2 := by
          convert hreal using 1;
            simp [x2a, Fin.add_def]; ring
        change pi.1 = p.1 + ((x2a.re : Real) - (x2a.im : Real)) / 2
        linarith
      · have himag' : pi.2 - p.2 =
            ((x2a.im : Real) + (x2a.re : Real)) / 2 := by
          convert himag using 1;
            simp [x2a, Fin.add_def]; ring
        change pi.2 = p.2 + ((x2a.im : Real) + (x2a.re : Real)) / 2
        linarith
    rw [hpi', hp0'] at hpi
    exact hpi

private theorem hcenterQ3 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let A := cert.P 0 true
        ∀ (U : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid
            (U i s) - TileCentroid A = (if s = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) •
            (GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ)
            (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint
            (BandVectors.1 (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ)
            (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint
            (BandVectors.1 (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ)
            (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ))).1))) → ((∀ (i : Fin 3), ∀ (s :
            Bool), (U i s).cells = (cert.Q i s).cells ∧ ((U i s).cells = ∅ → (U i s).anchor =
            (cert.Q i s).anchor) ∧ FootprintVertices (U i s) = FootprintVertices (cert.Q i s)) → (
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let spatial (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (TileCentroid A - TileCentroid T = spatial w) → (
        let x2v : GaussianInt :=
          BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1)
        TileCentroid (cert.Q 2 true) - TileCentroid T = spatial w + spatial x2v))) ) := by
  classical
  intro q cfg C T cert A U hcentA alignA w spatial hcenterA x2v
  have hqa : TileCentroid (cert.Q 2 true) - TileCentroid A =
      spatial x2v := by
    have hc := hcentA 2 true
    have hc' : TileCentroid (U 2 true) =
        TileCentroid (cert.Q 2 true) := by
      by_cases he : (U 2 true).cells = ∅
      · simp [TileCentroid, (alignA 2 true).1,
          (alignA 2 true).2.1 he]
      · have hne : (cert.Q 2 true).cells.Nonempty := by
          rw [← (alignA 2 true).1]
          exact Finset.nonempty_iff_ne_empty.mpr he
        simp [TileCentroid, (alignA 2 true).1, hne]
    have hc'' : TileCentroid (cert.Q 2 true) - TileCentroid A =
        (1 / 2 : Real) • (GaussianRealPoint x2v -
          (-(GaussianRealPoint x2v).2, (GaussianRealPoint x2v).1)) := by
      simpa [hc', x2v, Fin.add_def] using hc
    convert hc'' using 1
  calc
    _ = (TileCentroid (cert.Q 2 true) - TileCentroid A) +
        (TileCentroid A - TileCentroid T) := by ext <;> dsimp <;> ring
    _ = _ := by rw [hqa, hcenterA]; ext <;> dsimp <;> ring

private theorem crossSpatial2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let B := cert.P 0 false
        let I : GaussianInt := ⟨0, 1⟩
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let xv : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        let spatial (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (BandVectors.1 (cfg.firstPredecessor (3 : Fin (4 : ℕ))) (cfg.firstPredecessor (2 : Fin (4
            : ℕ))) + BandVectors.1 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor
            (3 : Fin (4 : ℕ))) + BandVectors.1 (cfg.firstPredecessor (2 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) = (0 : GaussianInt)) → (((I : GaussianInt) ^
            3 = -I) → (((-I : GaussianInt) * I = 1) → ((∀ (z : GaussianInt), I * z = ⟨-z.im,
            z.re⟩) → ((TileCentroid B - TileCentroid T = -spatial w) → ((TileCentroid (cert.S 1
            false) - TileCentroid B = -spatial xv) → (
        let x2v : GaussianInt :=
          BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1)
        (TileCentroid (cert.Q 2 true) - TileCentroid T = spatial w + spatial x2v) → (TileCentroid
            (cert.Q 2 true) - TileCentroid (cert.S 1 false) = (1 / 2 : Real) • GaussianRealPoint
            ((I : GaussianInt) ^ (3 : Nat) * (w + I * w))))))))) ) := by
  classical
  intro q cfg C T cert B I w xv spatial hpredV hI3 hnegII hIprod hcenterB hcenterS x2v hcenterQ3
  have hcenterS1T : TileCentroid (cert.S 1 false) - TileCentroid T =
      -spatial xv - spatial w := by
    calc
      _ = (TileCentroid (cert.S 1 false) - TileCentroid B) +
          (TileCentroid B - TileCentroid T) := by ext <;> dsimp <;> ring
      _ = _ := by rw [hcenterS, hcenterB]; ext <;> dsimp <;> ring
  have hsum : w + xv + x2v = 0 := by
    simpa [w, xv, x2v, cfg.firstParentTwo, cfg.firstParentThree] using hpredV
  have hdelta : (spatial w + spatial x2v) -
      (-spatial w - spatial xv) = spatial w := by
    rw [show x2v = -w - xv by linear_combination hsum]
    ext <;> simp [spatial, GaussianRealPoint]  <;> ring
  calc
    _ = (TileCentroid (cert.Q 2 true) - TileCentroid T) -
        (TileCentroid (cert.S 1 false) - TileCentroid T) := by
      ext <;> dsimp <;> ring
    _ = (spatial w + spatial x2v) -
        (-spatial w - spatial xv) := by
          rw [hcenterQ3, hcenterS1T]
          ext <;> dsimp <;> ring
    _ = spatial w := hdelta
    _ = (1 / 2 : Real) • GaussianRealPoint
        ((I : GaussianInt) ^ (3 : Nat) * (w + I * w)) := by
      have hp : (I : GaussianInt) ^ 3 * (w + I * w) = w - I * w := by
        rw [hI3]
        calc
          (-I) * (w + I * w) = -I * w + ((-I) * I) * w := by
            rw [mul_add, ← mul_assoc]
          _ = w - I * w := by rw [hnegII]; ring
      rw [hp, hIprod w]
      dsimp [spatial, GaussianRealPoint]
      ext <;> simp

private theorem crossSlope2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (s0 :
            Real × Real),
        let I : GaussianInt := ⟨0, 1⟩
        let alpha : GaussianInt := BandVectors.2 (q 3) (q 2)
        let xa : GaussianInt := BandVectors.2 (cfg.firstPredecessor 1) (q 3)
        (BandVectors.2 (cfg.firstPredecessor (3 : Fin (4 : ℕ))) (cfg.firstPredecessor (2 : Fin (4
            : ℕ))) + BandVectors.2 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor
            (3 : Fin (4 : ℕ))) + BandVectors.2 (cfg.firstPredecessor (2 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) = (0 : GaussianInt)) → ((BandVectors.1 (q (2
            : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) ∧ BandVectors.2 (q (2 : Fin
            (4 : ℕ))) (q (3 : Fin (4 : ℕ))) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2
            (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))) → ((I * (-I) = 1) → (((-I : GaussianInt)
            ^ 3 = I) → ((∀ (z : GaussianInt), I * z = ⟨-z.im, z.re⟩) → (
        let x2a : GaussianInt :=
          BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1)
        (s0 + P4250T1SlopeOffset alpha + P4250T1SlopeOffset x2a) - (s0 - P4250T1SlopeOffset
            alpha - P4250T1SlopeOffset xa) = (1 / 2 : Real) • GaussianRealPoint (((-I :
            GaussianInt) ^ (3 : Nat)) * (alpha + BandVectors.2 (q 2) (q 3)))))))) ) := by
  classical
  intro q cfg s0 I alpha xa hpredA secondFlip hIneg hI3neg hIprod x2a
  have hsum : alpha + xa + x2a = 0 := by
    simpa [alpha, xa, x2a, cfg.firstParentTwo, cfg.firstParentThree] using hpredA
  have hdelta : (2 : Real) • P4250T1SlopeOffset alpha +
      P4250T1SlopeOffset x2a + P4250T1SlopeOffset xa =
        P4250T1SlopeOffset alpha := by
    rw [show x2a = -alpha - xa by linear_combination hsum]
    ext <;> dsimp [P4250T1SlopeOffset] <;> push_cast <;> ring
  calc
    _ = (2 : Real) • P4250T1SlopeOffset alpha +
        P4250T1SlopeOffset x2a + P4250T1SlopeOffset xa := by
          ext <;> dsimp <;> ring
    _ = P4250T1SlopeOffset alpha := hdelta
    _ = (1 / 2 : Real) • GaussianRealPoint
        (((-I : GaussianInt) ^ (3 : Nat)) *
          (alpha + BandVectors.2 (q 2) (q 3))) := by
      rw [secondFlip.2]
      have hp : (-I : GaussianInt) ^ 3 * (alpha + (-I) * alpha) =
          alpha + I * alpha := by
        calc
          _ = I * (alpha + (-I) * alpha) := by rw [hI3neg]
          _ = I * alpha + (I * (-I)) * alpha := by
            rw [mul_add, ← mul_assoc]
          _ = alpha + I * alpha := by rw [hIneg]; ring
      rw [hp]
      have hIa := hIprod alpha
      rw [hIa]
      ext <;> simp [P4250T1SlopeOffset, GaussianRealPoint] <;> ring

private theorem adjCross2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (s0 : Real × Real), ∀ (k : Fin (3 : ℕ) → Bool → PartialOdometer), ∀ (l : Fin (3
            : ℕ) → Bool → PartialOdometer), (TileOdometer (cfg.firstPredecessor 2) (cert.S 1
            false) (l 1 false)) → ((TileOdometer (cfg.firstPredecessor 3) (cert.Q 2 true) (k 2
            true)) → (
        let I : GaussianInt := ⟨0, 1⟩
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let alpha : GaussianInt := BandVectors.2 (q 3) (q 2)
        let xa : GaussianInt := BandVectors.2 (cfg.firstPredecessor 1) (q 3)
        (BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) = (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) ∧
            BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) = -(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.2 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))) → (∀
            (posRoot2 : 0 < (q 2).1),
        let C2 : BandCircle :=
          ⟨⟨q 2, Or.inl posRoot2, q, cfg.proper.1, 2, rfl⟩, posRoot2⟩
        (PartialOdometerSlope (l 1 false) = some (s0 - P4250T1SlopeOffset alpha -
            P4250T1SlopeOffset xa)) → (
        let x2a : GaussianInt :=
          BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1)
        ∀ (posRoot3 : 0 < (q 3).1),
        let C3 : BandCircle :=
          ⟨⟨q 3, Or.inl posRoot3, q, cfg.proper.1, 3, rfl⟩, posRoot3⟩
        (PartialOdometerSlope (k 2 true) = some (s0 + P4250T1SlopeOffset alpha +
            P4250T1SlopeOffset x2a)) → ((TileCentroid (cert.Q 2 true) - TileCentroid (cert.S 1
            false) = (1 / 2 : Real) • GaussianRealPoint ((I : GaussianInt) ^ (3 : Nat) * (w + I *
            w))) → (((s0 + P4250T1SlopeOffset alpha + P4250T1SlopeOffset x2a) - (s0 -
            P4250T1SlopeOffset alpha - P4250T1SlopeOffset xa) = (1 / 2 : Real) •
            GaussianRealPoint (((-I : GaussianInt) ^ (3 : Nat)) * (alpha + BandVectors.2 (q 2) (q
            3)))) → (SubtileLatticeAdjacent C2 C3 (cert.S 1 false) (cert.Q 2 true) (l 1 false) (k
            2 true)))))))) ) := by
  classical
  intro q cfg C T cert s0 k l odoS2 odoQ3 I w alpha xa secondFlip posRoot2 C2 childSlopeMinus x2a
      posRoot3 C3 childSlopeQ3 crossSpatial2 crossSlope2
  refine ⟨?_, ?_, ⟨s0 - P4250T1SlopeOffset alpha -
    P4250T1SlopeOffset xa,
    s0 + P4250T1SlopeOffset alpha +
      P4250T1SlopeOffset x2a,
    childSlopeMinus, childSlopeQ3, cfg.secondPredecessor, 0, 3,
    cfg.secondProper, cfg.secondChild, cfg.secondParentOne, ?_, ?_, ?_⟩⟩
  · simpa [C2, cfg.firstParentTwo] using odoS2
  · simpa [C3, cfg.firstParentThree] using odoQ3
  · simp only [show (0 : Fin 3).succ = (1 : Fin 4) from rfl,
      cfg.secondChild, cfg.secondParentOne]
    rw [secondFlip.1]
    exact crossSpatial2
  · simp only [show (0 : Fin 3).succ = (1 : Fin 4) from rfl,
      cfg.secondChild, cfg.secondParentOne]
    simpa [pow_one] using congrArg Prod.fst crossSlope2
  · simp only [show (0 : Fin 3).succ = (1 : Fin 4) from rfl,
      cfg.secondChild, cfg.secondParentOne]
    simpa [pow_one] using congrArg Prod.snd crossSlope2

private theorem propagateConstant :
    (by
      classical
      exact
        ∀ {V : Type},
          ∀ (f : V → Int),
            ∀ (g : V → Int),
              ∀ (L : Set V),
                ∀ (O : Set V),
                  ∀ (R : Set V),
                    ∀ (Iset : Set V),
                      ∀ (c : Int),
                        ∀ (d : Int),
                          ∀ (e : Int),
                            ∀ (xL : V),
                              ∀ (xR : V),
                                Iset ⊆ L ∪ O ∪ R →
                                (∀ x ∈ L, g x - f x = d) →
                                (∀ x ∈ O, g x - f x = c) →
                                (∀ x ∈ R, f x - g x = e) →
                                xL ∈ L ∩ O → xR ∈ R ∩ O → ∀ x ∈ Iset, g x - f x = c
    ) := by
  classical
  intro V f g L O R Iset c d e xL xR hcover hL hO hR hxL hxR
  have hd : d = c := (hL xL hxL.1).symm.trans (hO xL hxL.2)
  have he : -e = c := by
    have h1 := hR xR hxR.1
    have h2 := hO xR hxR.2
    omega
  intro x hx
  rcases hcover hx with (hLx | hOx) | hRx
  · rw [hL x hLx, hd]
  · exact hO x hOx
  · have hr := hR x hRx
    omega

private theorem properLarge :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ProperBandQuadruple r → 1 < (r 0).1
    ) := by
  classical
  intro r hr
  have facts := ProperBandCurvatureStructure r hr
  have hsome : ∃ i : Fin 3, 0 < (r i.succ).1 := by
    by_cases h0 : 0 < (r (0 : Fin 3).succ).1
    · exact ⟨0, h0⟩
    by_cases h1 : 0 < (r (1 : Fin 3).succ).1
    · exact ⟨1, h1⟩
    by_cases h2 : 0 < (r (2 : Fin 3).succ).1
    · exact ⟨2, h2⟩
    have z0 : (r (0 : Fin 3).succ).1 = 0 := by
      have hn := facts.2.1 0
      omega
    have z1 : (r (1 : Fin 3).succ).1 = 0 := by
      have hn := facts.2.1 1
      omega
    exact ((by decide : (0 : Fin 3) ≠ 1) (facts.2.2 0 1 z0 z1)).elim
  obtain ⟨i, hi⟩ := hsome
  have hlt := hr.2 i
  omega

private theorem qSCells :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (cert.Q 0 false).cells = (cert.S 0 true).cells ) := by
  classical
  intro q cfg C T cert
  calc
    _ = cert.O.cells := by rw [cert.precursor_eq]
    _ = _ := cert.precursor_cells

private theorem qSAnchor :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ((cert.Q 0 false).cells = ∅) → ((cert.Q 0 false).anchor = (cert.S 0 true).anchor)
            ) := by
  classical
  intro q cfg C T cert he
  have hOempty : cert.O.cells = ∅ := by rw [cert.precursor_eq]; exact he
  calc
    _ = cert.O.anchor := by
      have h := congrArg ProtoTile.anchor cert.precursor_eq
      exact h.symm
    _ = (cert.S 0 true).anchor := cert.precursor_anchor hOempty

private theorem uvCells :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (U : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (V : Fin (3 : ℕ) → Bool → ProtoTile),
            (∀ (i : Fin 3), ∀ (s : Bool), (U i s).cells = (cert.Q i s).cells ∧ ((U i s).cells = ∅
            → (U i s).anchor = (cert.Q i s).anchor) ∧ FootprintVertices (U i s) =
            FootprintVertices (cert.Q i s)) → ((∀ (i : Fin 3), ∀ (s : Bool), (V i s).cells =
            (cert.S i s).cells ∧ ((V i s).cells = ∅ → (V i s).anchor = (cert.S i s).anchor) ∧
            FootprintVertices (V i s) = FootprintVertices (cert.S i s)) → (((cert.Q 0
            false).cells = (cert.S 0 true).cells) → ((U 0 false).cells = (V 0 true).cells))) ) := by
  classical
  intro q cfg C T cert U V alignA alignB qSCells
  calc
    _ = (cert.Q 0 false).cells := (alignA 0 false).1
    _ = (cert.S 0 true).cells := qSCells
    _ = (V 0 true).cells := (alignB 0 true).1.symm

private theorem uvAnchor :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (U : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (V : Fin (3 : ℕ) → Bool → ProtoTile),
            (∀ (i : Fin 3), ∀ (s : Bool), (U i s).cells = (cert.Q i s).cells ∧ ((U i s).cells = ∅
            → (U i s).anchor = (cert.Q i s).anchor) ∧ FootprintVertices (U i s) =
            FootprintVertices (cert.Q i s)) → ((∀ (i : Fin 3), ∀ (s : Bool), (V i s).cells =
            (cert.S i s).cells ∧ ((V i s).cells = ∅ → (V i s).anchor = (cert.S i s).anchor) ∧
            FootprintVertices (V i s) = FootprintVertices (cert.S i s)) → (((cert.Q 0
            false).cells = (cert.S 0 true).cells) → ((((cert.Q 0 false).cells = ∅) → ((cert.Q 0
            false).anchor = (cert.S 0 true).anchor)) → (((U 0 false).cells = ∅) → ((U 0
            false).anchor = (V 0 true).anchor))))) ) := by
  classical
  intro q cfg C T cert U V alignA alignB qSCells qSAnchor he
  have hq : (cert.Q 0 false).cells = ∅ := by
    rw [← (alignA 0 false).1]
    exact he
  have hs : (cert.S 0 true).cells = ∅ := by rw [← qSCells]; exact hq
  have hv : (V 0 true).cells = ∅ := by
    rw [(alignB 0 true).1]
    exact hs
  calc
    _ = (cert.Q 0 false).anchor := (alignA 0 false).2.1 he
    _ = (cert.S 0 true).anchor := qSAnchor hq
    _ = (V 0 true).anchor := ((alignB 0 true).2.1 hv).symm

private theorem zeroOdometerLine :
    (by
      classical
      exact
        (∀ (r : Fin 4 → CircleCoordinates), ProperBandQuadruple r → 1 < (r 0).1) →
          ∀ {D : CircleCoordinates},
            ∀ {X : ProtoTile},
              ∀ {g : PartialOdometer},
                D.1 = 0 → TileOdometer D X g → ∃ x, X = ⟨∅, x⟩ ∧ g.domain = { x }
    ) := by
  classical
  intro properLarge D X g hD hg
  cases hg with
  | line w x hw g hdom => exact ⟨x, rfl, hdom⟩
  | unit z x Z g hZ hdom htrans => norm_num at hD
  | @decompose r hr S Z hs hZ hfoot hcent hdom hvalue hcompat hslope =>
      have hlarge := properLarge r hr
      omega

private theorem kline :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (U :
            Fin (3 : ℕ) → Bool → ProtoTile), ∀ (k : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i
            : Fin (3 : ℕ)), ∀ (s : Bool), TileOdometer (cfg.firstPredecessor i.succ) (U i s) (k i
            s)) → ((∀ {D : CircleCoordinates}, ∀ {X : ProtoTile}, ∀ {g : PartialOdometer}, (D.1 =
            0) → ((TileOdometer D X g) → (∃ x, X = ⟨∅, x⟩ ∧ g.domain = {x}))) →
            (((cfg.firstPredecessor (1 : Fin (4 : ℕ))).1 = (0 : ℤ)) → (∃ x, U 0 false = ⟨∅, x⟩ ∧
            (k 0 false).domain = {x}))) ) := by
  classical
  intro q cfg U k hchildA zeroOdometerLine hzero
  exact zeroOdometerLine hzero (hchildA 0 false)

private theorem lline :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (V :
            Fin (3 : ℕ) → Bool → ProtoTile), ∀ (l : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i
            : Fin (3 : ℕ)), ∀ (s : Bool), TileOdometer (cfg.firstPredecessor i.succ) (V i s) (l i
            s)) → ((∀ {D : CircleCoordinates}, ∀ {X : ProtoTile}, ∀ {g : PartialOdometer}, (D.1 =
            0) → ((TileOdometer D X g) → (∃ x, X = ⟨∅, x⟩ ∧ g.domain = {x}))) →
            (((cfg.firstPredecessor (1 : Fin (4 : ℕ))).1 = (0 : ℤ)) → (∃ x, V 0 true = ⟨∅, x⟩ ∧
            (l 0 true).domain = {x}))) ) := by
  classical
  intro q cfg V l hchildB zeroOdometerLine hzero
  exact zeroOdometerLine hzero (hchildB 0 true)

private theorem hxy :
    (by
      classical
      exact
        ∀ (U : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (V : Fin (3 : ℕ) → Bool → ProtoTile), (((U 0
            false).cells = ∅) → ((U 0 false).anchor = (V 0 true).anchor)) → (∀ (xk :
            GaussianInt), (U (0 : Fin (3 : ℕ)) false = (⟨∅, xk⟩ : ProtoTile)) → (∀ (xl :
            GaussianInt), (V (0 : Fin (3 : ℕ)) true = (⟨∅, xl⟩ : ProtoTile)) → (xk = xl))) ) := by
  classical
  intro U V uvAnchor xk htileK xl htileL
  have he : (U 0 false).cells = ∅ := by simp [htileK]
  have ha := uvAnchor he
  simpa [htileK, htileL] using ha

private theorem hcurvpos :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
            (¬(cfg.firstPredecessor (1 : Fin (4 : ℕ))).1 = (0 : ℤ)) → (0 < (cfg.firstPredecessor
            1).1) ) := by
  classical
  intro q cfg hzero
  have hn := (ProperBandCurvatureStructure cfg.firstPredecessor
    cfg.firstProper).2.1 0
  have hn' : 0 ≤ (cfg.firstPredecessor 1).1 := by simpa using hn
  omega

private theorem kSlope :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (h :
            Fin 3 → Bool → PartialOdometer), ∀ (s0 : Real × Real), (∀ (i : Fin (3 : ℕ)), ∀ (s :
            Bool), PartialOdometerSlope (h i s) = some (s0 + (if s = true then (1 : ℝ) else (-1 :
            ℝ)) • P4250T1SlopeOffset (BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1
            : Fin (3 : ℕ))).succ)))) → (∀ (k : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i : Fin
            (3 : ℕ)), ∀ (s : Bool), (cfg.firstPredecessor i.succ).1 = (0 : ℤ) ∨ ∃ (p : ℝ × ℝ)
            (p_i : ℝ × ℝ), PartialOdometerSlope (h (0 : Fin (3 : ℕ)) true) = some p ∧
            PartialOdometerSlope (k i s) = some p_i ∧ p_i.1 - p.1 = (if s = true then (1 : ℝ)
            else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (cfg.firstPredecessor (i + (2 : Fin
            (3 : ℕ))).succ) (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ) -
            (↑(BandVectors.2 (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ)
            (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)).im : ℝ)) ∧ p_i.2 - p.2 = (if s =
            true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2
            (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ) (cfg.firstPredecessor (i + (1 :
            Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (cfg.firstPredecessor (i + (2 : Fin
            (3 : ℕ))).succ) (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → (
        (¬(cfg.firstPredecessor (1 : Fin (4 : ℕ))).1 = (0 : ℤ)) → (PartialOdometerSlope (k 0
            false) = some s0))) ) := by
  classical
  intro q cfg h s0 hp k hslopeA hzero
  let alpha : GaussianInt := BandVectors.2 (q 3) (q 2)
  rcases hslopeA 0 false with hz | hs
  · exact (hzero hz).elim
  · rcases hs with ⟨p, pi, hp0, hpi, hreal, himag⟩
    have hp0' : p = s0 + P4250T1SlopeOffset alpha := by
      have heq : some p = some (s0 + P4250T1SlopeOffset alpha) := by
        simpa [alpha, Fin.add_def, cfg.firstParentThree,
          cfg.firstParentTwo] using hp0.symm.trans (hp 0 true)
      exact Option.some.inj heq
    have hpi' : pi = p - P4250T1SlopeOffset alpha := by
      apply Prod.ext
      · have hreal' : pi.1 - p.1 =
            -((alpha.re : Real) - (alpha.im : Real)) / 2 := by
          convert hreal using 1;
            simp [alpha, cfg.firstParentThree,
              cfg.firstParentTwo]; ring
        change pi.1 = p.1 - ((alpha.re : Real) - (alpha.im : Real)) / 2
        linarith
      · have himag' : pi.2 - p.2 =
            -((alpha.im : Real) + (alpha.re : Real)) / 2 := by
          convert himag using 1;
            simp [alpha, cfg.firstParentThree,
              cfg.firstParentTwo]; ring
        change pi.2 = p.2 - ((alpha.im : Real) + (alpha.re : Real)) / 2
        linarith
    rw [hpi', hp0'] at hpi
    simpa using hpi

private theorem lSlope :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (h :
            Fin 3 → Bool → PartialOdometer), ∀ (s0 : Real × Real), (∀ (i : Fin (3 : ℕ)), ∀ (s :
            Bool), PartialOdometerSlope (h i s) = some (s0 + (if s = true then (1 : ℝ) else (-1 :
            ℝ)) • P4250T1SlopeOffset (BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1
            : Fin (3 : ℕ))).succ)))) → (∀ (l : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i : Fin
            (3 : ℕ)), ∀ (s : Bool), (cfg.firstPredecessor i.succ).1 = (0 : ℤ) ∨ ∃ (p : ℝ × ℝ)
            (p_i : ℝ × ℝ), PartialOdometerSlope (h (0 : Fin (3 : ℕ)) false) = some p ∧
            PartialOdometerSlope (l i s) = some p_i ∧ p_i.1 - p.1 = (if s = true then (1 : ℝ)
            else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (cfg.firstPredecessor (i + (2 : Fin
            (3 : ℕ))).succ) (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ) -
            (↑(BandVectors.2 (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ)
            (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)).im : ℝ)) ∧ p_i.2 - p.2 = (if s =
            true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2
            (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ) (cfg.firstPredecessor (i + (1 :
            Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (cfg.firstPredecessor (i + (2 : Fin
            (3 : ℕ))).succ) (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → (
        (¬(cfg.firstPredecessor (1 : Fin (4 : ℕ))).1 = (0 : ℤ)) → (PartialOdometerSlope (l 0
            true) = some s0))) ) := by
  classical
  intro q cfg h s0 hp l hslopeB hzero
  let alpha : GaussianInt := BandVectors.2 (q 3) (q 2)
  rcases hslopeB 0 true with hz | hs
  · exact (hzero hz).elim
  · rcases hs with ⟨p, pi, hp0, hpi, hreal, himag⟩
    have hp0' : p = s0 - P4250T1SlopeOffset alpha := by
      have heq : some p = some (s0 - P4250T1SlopeOffset alpha) := by
        simpa [alpha, Fin.add_def, cfg.firstParentThree,
          cfg.firstParentTwo, sub_eq_add_neg, smul_eq_mul] using
            hp0.symm.trans (hp 0 false)
      exact Option.some.inj heq
    have hpi' : pi = p + P4250T1SlopeOffset alpha := by
      apply Prod.ext
      · have hreal' : pi.1 - p.1 =
            ((alpha.re : Real) - (alpha.im : Real)) / 2 := by
          convert hreal using 1;
            simp [alpha, cfg.firstParentThree,
              cfg.firstParentTwo]; ring
        change pi.1 = p.1 + ((alpha.re : Real) - (alpha.im : Real)) / 2
        linarith
      · have himag' : pi.2 - p.2 =
            ((alpha.im : Real) + (alpha.re : Real)) / 2 := by
          convert himag using 1;
            simp [alpha, cfg.firstParentThree,
              cfg.firstParentTwo]; ring
        change pi.2 = p.2 + ((alpha.im : Real) + (alpha.re : Real)) / 2
        linarith
    rw [hpi', hp0'] at hpi
    simpa using hpi

private theorem hneV :
    (by
      classical
      exact
        ∀ (U : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (V : Fin (3 : ℕ) → Bool → ProtoTile), ((U 0
            false).cells = (V 0 true).cells) → (((U 0 false).cells.Nonempty) → ((V 0
            true).cells.Nonempty)) ) := by
  classical
  intro U V uvCells hneU
  rw [← uvCells]
  exact hneU

private theorem hcentShift :
    (by
      classical
      exact
        ∀ (V : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (shift : GaussianInt), ((V 0
            true).cells.Nonempty) → (((V 0 true).cells = (TileTranslation (V 0 true)
            shift).cells) → (TileCentroid (V 0 true) = TileCentroid (TileTranslation (V 0 true)
            shift))) ) := by
  classical
  intro V shift hneV hcellShift
  have hneTrans :
      (TileTranslation (V 0 true) shift).cells.Nonempty := by
    rw [(TileTranslationFormulas (V 0 true) shift).1]
    exact Finset.image_nonempty.mpr hneV
  simp [TileCentroid, hneTrans, hcellShift]

private theorem hshiftRe :
    (by
      classical
      exact
        ∀ (V : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (shift : GaussianInt), (TileCentroid (V (0 :
            Fin (3 : ℕ)) true) = ((TileCentroid (V (0 : Fin (3 : ℕ)) true)).1 + (↑shift.re : ℝ),
            (TileCentroid (V (0 : Fin (3 : ℕ)) true)).2 + (↑shift.im : ℝ))) → ((shift.re : Real)
            = 0) ) := by
  classical
  intro V shift hcentShift
  have hh := congrArg Prod.fst hcentShift
  dsimp at hh
  linarith

private theorem hshiftIm :
    (by
      classical
      exact
        ∀ (V : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (shift : GaussianInt), (TileCentroid (V (0 :
            Fin (3 : ℕ)) true) = ((TileCentroid (V (0 : Fin (3 : ℕ)) true)).1 + (↑shift.re : ℝ),
            (TileCentroid (V (0 : Fin (3 : ℕ)) true)).2 + (↑shift.im : ℝ))) → ((shift.im : Real)
            = 0) ) := by
  classical
  intro V shift hcentShift
  have hh := congrArg Prod.snd hcentShift
  dsimp at hh
  linarith

private theorem hshift :
    (by
      classical
      exact
        ∀ (shift : GaussianInt), ((shift.re : Real) = 0) → (((shift.im : Real) = 0) → (shift =
            0)) ) := by
  classical
  intro shift hshiftRe hshiftIm
  apply Zsqrtd.ext
  · exact_mod_cast hshiftRe
  · exact_mod_cast hshiftIm

private theorem hdomainEq :
    (by
      classical
      exact
        ∀ (k : Fin (3 : ℕ) → Bool → PartialOdometer), ∀ (l : Fin (3 : ℕ) → Bool →
            PartialOdometer), ∀ (shift : GaussianInt), ∀ (aa : GaussianInt), ∀ (bb : ℤ), (∀ (x :
            GaussianInt), x ∈ (k (0 : Fin (3 : ℕ)) false).domain ↔ x - shift ∈ (l (0 : Fin (3 :
            ℕ)) true).domain) → ((shift = 0) → ((k 0 false).domain =
            (PartialOdometerAffineTranslate (l 0 true) 0 aa bb).domain)) ) := by
  classical
  intro k l shift aa bb hdomains hshift
  ext x
  rw [(PartialOdometerAffineTranslateFormulas
    (l 0 true) 0 aa bb).2.1]
  simpa [hshift] using hdomains x

private theorem hvalueEq :
    (by
      classical
      exact
        ∀ (k : Fin (3 : ℕ) → Bool → PartialOdometer), ∀ (l : Fin (3 : ℕ) → Bool →
            PartialOdometer), ∀ (shift : GaussianInt), ∀ (aa : GaussianInt), ∀ (bb : ℤ), (∀ x ∈
            (k (0 : Fin (3 : ℕ)) false).domain, (k (0 : Fin (3 : ℕ)) false).value x = (l (0 : Fin
            (3 : ℕ)) true).value (x - shift) + aa.re * x.re + aa.im * x.im + bb) → ((shift = 0) →
            (((k 0 false).domain = (PartialOdometerAffineTranslate (l 0 true) 0 aa bb).domain) →
            ((k 0 false).value = (PartialOdometerAffineTranslate (l 0 true) 0 aa bb).value))) )
            := by
  classical
  intro k l shift aa bb hvalues hshift hdomainEq
  funext x
  by_cases hx : x ∈ (k 0 false).domain
  · have hx' : x ∈
        (PartialOdometerAffineTranslate (l 0 true) 0 aa bb).domain := by
      rw [← hdomainEq]
      exact hx
    rw [hvalues x hx,
      (PartialOdometerAffineTranslateFormulas
        (l 0 true) 0 aa bb).2.2.1 x hx']
    simp [hshift]
  · rw [(k 0 false).value_outside x hx,
      (PartialOdometerAffineTranslate (l 0 true) 0 aa bb).value_outside x]
    intro hx'
    apply hx
    rw [hdomainEq]
    exact hx'

private theorem heqAt1131 :
    (by
      classical
      exact
        ∀ (k : Fin (3 : ℕ) → Bool → PartialOdometer), ∀ (l : Fin (3 : ℕ) → Bool →
            PartialOdometer), ∀ (aa : GaussianInt), ∀ (bb : ℤ), ((k 0 false).domain =
            (PartialOdometerAffineTranslate (l 0 true) 0 aa bb).domain) → (((k 0 false).value =
            (PartialOdometerAffineTranslate (l 0 true) 0 aa bb).value) → (k 0 false =
            PartialOdometerAffineTranslate (l 0 true) 0 aa bb)) ) := by
  classical
  intro k l aa bb hdomainEq hvalueEq
  generalize k 0 false = K at hdomainEq hvalueEq ⊢
  cases K
  simp only [PartialOdometerAffineTranslate, PartialOdometer.mk.injEq]
  exact ⟨hdomainEq, hvalueEq⟩

private theorem hslopeEq :
    (by
      classical
      exact
        ∀ (k : Fin (3 : ℕ) → Bool → PartialOdometer), ∀ (l : Fin (3 : ℕ) → Bool →
            PartialOdometer), ∀ (aa : GaussianInt), ∀ (bb : ℤ), (k 0 false =
            PartialOdometerAffineTranslate (l 0 true) 0 aa bb) → (PartialOdometerSlope (k 0
            false) = ((PartialOdometerSlope (l 0 true)).map (fun p => (p.1 + (aa.re : Real), p.2
            + (aa.im : Real))))) ) := by
  classical
  intro k l aa bb heq
  rw [heq, (PartialOdometerAffineTranslateFormulas
    (l 0 true) 0 aa bb).2.2.2.2.2]

private theorem haaRe :
    (by
      classical
      exact
        ∀ (s0 : Real × Real), ∀ (aa : GaussianInt), (s0 = (s0.1 + (aa.re : Real), s0.2 + (aa.im :
            Real))) → ((aa.re : Real) = 0) ) := by
  classical
  intro s0 aa hslopePair
  have h := congrArg Prod.fst hslopePair
  dsimp at h
  linarith

private theorem haaIm :
    (by
      classical
      exact
        ∀ (s0 : Real × Real), ∀ (aa : GaussianInt), (s0 = (s0.1 + (aa.re : Real), s0.2 + (aa.im :
            Real))) → ((aa.im : Real) = 0) ) := by
  classical
  intro s0 aa hslopePair
  have h := congrArg Prod.snd hslopePair
  dsimp at h
  linarith

private abbrev haa := ApollonianSuperharmonic.NestedCompatibilityGeometry.hshift

private theorem boundaryRaw :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (x : GaussianInt), (x ∈ BoundaryFootprintVertices X) → (x ∈
            FootprintVertices X) ) := by
  classical
  intro X x hx
  by_cases hne : X.cells.Nonempty
  · simp only [BoundaryFootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq] at hx
    obtain ⟨e, he, hxe⟩ := hx
    have hedge : e ∈ FootprintEdges X := by
      rcases he with ⟨z, ⟨rfl, hc⟩ | ⟨rfl, hc⟩⟩
      · rcases hc with ⟨hz, _⟩ | ⟨_, hz⟩
        · exact ⟨z, hz, Or.inl rfl⟩
        · refine ⟨z - (⟨0, 1⟩ : GaussianInt), hz, Or.inr (Or.inr (Or.inr ?_))⟩
          congr 1 <;> simp [Zsqrtd.ext_iff]
      · rcases hc with ⟨hz, _⟩ | ⟨_, hz⟩
        · exact ⟨z, hz, Or.inr (Or.inl rfl)⟩
        · refine ⟨z - 1, hz, Or.inr (Or.inr (Or.inl ?_))⟩
          congr 1 <;> simp []
    simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq]
    rcases hedge with ⟨c, hc, heq⟩
    rcases heq with h | h | h | h <;> subst e
    all_goals simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
    · rcases hxe with rfl | rfl
      · exact ⟨_, hc, Or.inl rfl⟩
      · exact ⟨c, hc, Or.inr (Or.inl rfl)⟩
    · rcases hxe with rfl | rfl
      · exact ⟨_, hc, Or.inl rfl⟩
      · exact ⟨c, hc, Or.inr (Or.inr (Or.inl rfl))⟩
    · rcases hxe with rfl | rfl
      · exact ⟨c, hc, Or.inr (Or.inl rfl)⟩
      · exact ⟨c, hc, Or.inr (Or.inr (Or.inr rfl))⟩
    · rcases hxe with rfl | rfl
      · exact ⟨c, hc, Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨c, hc, Or.inr (Or.inr (Or.inr rfl))⟩
  · simpa only [BoundaryFootprintVertices, FootprintVertices, ite_eq_right hne] using hx

private theorem rootBand :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), (BandOrderedGeneralLayoutCertificate q cfg C T) →
            (BandPrototile (q 0) T) ) := by
  classical
  intro q cfg C T cert
  apply BandPrototile.decompose cfg.proper
    (fun i s => (cert.outer_occurrence i s).1)
  · exact cert.outer_union
  · intro i s
    exact (cert.outer_occurrence i s).2.1
  · intro i s
    exact (cert.outer_occurrence i s).2.2

private theorem rootNonempty :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let A := cert.P 0 true
        (1 < (cfg.firstPredecessor 0).1) → ((BandPrototile (cfg.firstPredecessor (0 : Fin (4 :
            ℕ))) A) → ((∀ (D : CircleCoordinates), ∀ (X : ProtoTile), BandPrototile D X → 0 < D.1
            → X.cells.Nonempty) → (T.cells.Nonempty))) ) := by
  classical
  intro q cfg C T cert A hroot hbandA bandPositiveNonempty
  obtain ⟨x, hx⟩ := bandPositiveNonempty (cfg.firstPredecessor 0) A
    hbandA (by linarith)
  exact ⟨x, (cert.outer_union x).2 ⟨0, true, hx⟩⟩

private theorem centerIntegral :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), (BandPrototile (q 0) T) →
            ((T.cells.Nonempty) → (∃ u : GaussianInt, (2 : Real) • TileCentroid T =
            GaussianRealPoint u)) ) := by
  classical
  intro q T rootBand rootNonempty
  let c := TileCentroid T
  let reCells : Finset Int := T.cells.image (fun x => x.re)
  let imCells : Finset Int := T.cells.image (fun x => x.im)
  have reNe : reCells.Nonempty := Finset.image_nonempty.mpr rootNonempty
  have imNe : imCells.Nonempty := Finset.image_nonempty.mpr rootNonempty
  have hcentral : CentrallyReflectedAt c T T :=
    by simpa [c] using BandPrototileCentralSymmetry (q 0) T rootBand
  have reflect_mem : ∀ p ∈ TileRealization T,
      (2 * c.1 - p.1, 2 * c.2 - p.2) ∈ TileRealization T := by
    intro p hp
    rw [hcentral]
    exact ⟨p, hp, rfl⟩
  have hboundRe : ∀ p ∈ TileRealization T,
      (↑(reCells.min' reNe) : Real) ≤ p.1 ∧
        p.1 ≤ (↑(reCells.max' reNe) : Real) + 1 := by
    intro p hp
    simp only [TileRealization, Set.mem_iUnion] at hp
    rcases hp with ⟨x, hx, hpx⟩
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hpx
    constructor
    · have hm := Finset.min'_le reCells x.re
        (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      exact le_trans (by exact_mod_cast hm) hpx.1.1
    · have hm := Finset.le_max' reCells x.re
        (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      have hm' : (x.re : Real) ≤ (reCells.max' reNe : Real) := by
        exact_mod_cast hm
      linarith [hpx.2.1, hm']
  have hboundIm : ∀ p ∈ TileRealization T,
      (imCells.min' imNe : Real) ≤ p.2 ∧
        p.2 ≤ (imCells.max' imNe : Real) + 1 := by
    intro p hp
    simp only [TileRealization, Set.mem_iUnion] at hp
    rcases hp with ⟨x, hx, hpx⟩
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hpx
    constructor
    · exact le_trans (Int.cast_le.mpr (Finset.min'_le imCells x.im
        (Finset.mem_image.mpr ⟨x, hx, rfl⟩))) hpx.1.2
    · have hm := Finset.le_max' imCells x.im
        (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      have hm' : (x.im : Real) ≤ (imCells.max' imNe : Real) := by
        exact_mod_cast hm
      linarith [hpx.2.2, hm']
  let mIm := imCells.min' imNe
  let MIm := imCells.max' imNe
  have centerRe : 2 * c.1 = (reCells.min' reNe : Real) +
      reCells.max' reNe + 1 := by
    have hmin : ∃ x, x ∈ T.cells ∧ x.re = reCells.min' reNe := by
      rcases Finset.mem_image.mp (Finset.min'_mem reCells reNe) with ⟨x, hx, he⟩
      exact ⟨x, hx, he⟩
    have hmax : ∃ x, x ∈ T.cells ∧ x.re = reCells.max' reNe := by
      rcases Finset.mem_image.mp (Finset.max'_mem reCells reNe) with ⟨x, hx, he⟩
      exact ⟨x, hx, he⟩
    obtain ⟨xmin, hxmin, hxminre⟩ := hmin
    obtain ⟨xmax, hmax, hmaxre⟩ := hmax
    have pmin : ((reCells.min' reNe : Real), (xmin.im : Real)) ∈
        TileRealization T := by
      simp only [TileRealization, Set.mem_iUnion]
      refine ⟨xmin, hxmin, ?_⟩
      simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
      exact ⟨⟨by simp [hxminre], by simp []⟩,
        ⟨by simp [hxminre], by simp⟩⟩
    have pmax : (((reCells.max' reNe : Int) : Real) + 1,
        (xmax.im : Real)) ∈ TileRealization T := by
      simp only [TileRealization, Set.mem_iUnion]
      refine ⟨xmax, hmax, ?_⟩
      simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
      exact ⟨⟨by simp [hmaxre], by simp⟩,
        ⟨by simp [hmaxre], by simp⟩⟩
    have bmin := hboundRe _ (reflect_mem _ pmin)
    have bmax := hboundRe _ (reflect_mem _ pmax)
    dsimp at bmin bmax
    norm_num at bmin bmax ⊢
    linarith
  have centerIm : 2 * c.2 = (mIm : Real) + MIm + 1 := by
    have hmin : ∃ x, x ∈ T.cells ∧ x.im = mIm := by
      rcases Finset.mem_image.mp (Finset.min'_mem imCells imNe) with ⟨x, hx, he⟩
      exact ⟨x, hx, he⟩
    have hmax : ∃ x, x ∈ T.cells ∧ x.im = MIm := by
      rcases Finset.mem_image.mp (Finset.max'_mem imCells imNe) with ⟨x, hx, he⟩
      exact ⟨x, hx, he⟩
    obtain ⟨xmin, hxmin, hxminim⟩ := hmin
    obtain ⟨xmax, hmax, hmaxim⟩ := hmax
    have pmin : ((xmin.re : Real), (mIm : Real)) ∈ TileRealization T := by
      simp only [TileRealization, Set.mem_iUnion]
      refine ⟨xmin, hxmin, ?_⟩
      simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
      refine ⟨⟨by simp, ?_⟩, ⟨by simp, ?_⟩⟩
      · simp [hxminim]
      · simp [hxminim]
    have pmax : ((xmax.re : Real), (MIm : Real) + 1) ∈
        TileRealization T := by
      simp only [TileRealization, Set.mem_iUnion]
      refine ⟨xmax, hmax, ?_⟩
      simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
      refine ⟨⟨by simp, ?_⟩, ⟨by simp, ?_⟩⟩
      · simp [hmaxim]
      · simp [hmaxim]
    have bmin := hboundIm _ (reflect_mem _ pmin)
    have bmax := hboundIm _ (reflect_mem _ pmax)
    dsimp at bmin bmax
    norm_num at bmin bmax ⊢
    linarith
  refine ⟨⟨reCells.min' reNe + reCells.max' reNe + 1,
    mIm + MIm + 1⟩, ?_⟩
  apply Prod.ext <;> simp [GaussianRealPoint] <;>
    linarith [centerRe, centerIm]

private theorem reflectedFoot :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (∀ (D : CircleCoordinates), ∀ (X : ProtoTile), BandPrototile D X → 0 <
            D.1 → X.cells.Nonempty) → (∀ (u : GaussianInt), ((2 : ℝ) • TileCentroid T =
            GaussianRealPoint u) → (∀ (D : CircleCoordinates), ∀ (X : ProtoTile), ∀ (Y :
            ProtoTile), ∀ (g : PartialOdometer), (TileOdometer D X g) → ((BandPrototile D Y) →
            ((0 < D.1) → ((TileCentroid X + TileCentroid Y =
            (2 : Real) • TileCentroid T) → (FootprintVertices (TileTranslation (TileHalfTurn X)
                u) = FootprintVertices Y)))))) ) := by
  classical
  intro T bandPositiveNonempty u hu D X Y g hX hY hD hsum
  let Z := TileTranslation (TileHalfTurn X) u
  have hhalf := (TileOdometerCentralSymmetry D X g hX).1
  have hZodo : TileOdometer D Z
      (PartialOdometerAffineTranslate (PartialOdometerHalfTurn g) u 0 0) :=
    TileOdometerAffineTranslation D (TileHalfTurn X)
      (PartialOdometerHalfTurn g) u 0 0 hhalf
  have hZband : BandPrototile D Z :=
    TileOdometerBandPrototile D Z _ hZodo
  have hcent : TileCentroid Z = TileCentroid Y := by
    rw [(TileTranslationFormulas (TileHalfTurn X) u).2.2.2.2.1,
      (TileHalfTurnFormulas X).2.2.2.2.2.2.2.1]
    have huRe := congrArg Prod.fst hu
    have huIm := congrArg Prod.snd hu
    have hsRe := congrArg Prod.fst hsum
    have hsIm := congrArg Prod.snd hsum
    dsimp [GaussianRealPoint] at huRe huIm
    dsimp at hsRe hsIm
    apply Prod.ext <;> dsimp <;> linarith
  have hcells := (BandPrototileCentroidUnique D Z Y hZband hY hcent).1
  have hYne := bandPositiveNonempty D Y hY hD
  simp only [Z, FootprintVertices, ite_eq_left hYne, hcells]

private theorem hsumAB :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let A := cert.P 0 true
        let B := cert.P 0 false
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let spatial (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (TileCentroid A - TileCentroid T = spatial w) → ((TileCentroid B - TileCentroid T =
            -spatial w) → (TileCentroid A + TileCentroid B = (2 : Real) • TileCentroid T)) ) := by
  classical
  intro q cfg C T cert A B w spatial hcenterA hcenterB
  have hr := congrArg Prod.fst hcenterA
  have hi := congrArg Prod.snd hcenterA
  have hr' := congrArg Prod.fst hcenterB
  have hi' := congrArg Prod.snd hcenterB
  apply Prod.ext <;> dsimp at hr hi hr' hi' ⊢ <;> linarith

private theorem hsumCD :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let v13 : GaussianInt := BandVectors.1 (q 1) (q 3)
        let spatial (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (TileCentroid (cert.P 1 true) - TileCentroid T = spatial v13) → ((TileCentroid (cert.P 1
            false) - TileCentroid T = -spatial v13) → (TileCentroid (cert.P 1 true) +
            TileCentroid (cert.P 1 false) = (2 : Real) • TileCentroid T)) ) := by
  classical
  intro q cfg C T cert v13 spatial hcenterP hcenterPminus
  have hr := congrArg Prod.fst hcenterP
  have hi := congrArg Prod.snd hcenterP
  have hr' := congrArg Prod.fst hcenterPminus
  have hi' := congrArg Prod.snd hcenterPminus
  apply Prod.ext <;> dsimp at hr hi hr' hi' ⊢ <;> linarith

private theorem hcenterSTAt1375 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let B := cert.P 0 false
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let xv : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        let spatial (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (TileCentroid B - TileCentroid T = -spatial w) → ((TileCentroid (cert.S 1 false) -
            TileCentroid B = -spatial xv) → (TileCentroid (cert.S 1 false) - TileCentroid T =
            -spatial xv - spatial w)) ) := by
  classical
  intro q cfg C T cert B w xv spatial hcenterB hcenterS
  calc
    _ = (TileCentroid (cert.S 1 false) - TileCentroid B) +
        (TileCentroid B - TileCentroid T) := by ext <;> dsimp <;> ring
    _ = _ := by rw [hcenterS, hcenterB]; rfl

private theorem hsumQS :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let xv : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        let spatial (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (TileCentroid (cert.Q 1 true) - TileCentroid T = spatial xv + spatial w) → ((TileCentroid
            (cert.S 1 false) - TileCentroid T = -spatial xv - spatial w) → (TileCentroid (cert.Q
            1 true) + TileCentroid (cert.S 1 false) = (2 : Real) • TileCentroid T)) ) := by
  classical
  intro q cfg C T cert w xv spatial hcenterQT hcenterST
  have hr := congrArg Prod.fst hcenterQT
  have hi := congrArg Prod.snd hcenterQT
  have hr' := congrArg Prod.fst hcenterST
  have hi' := congrArg Prod.snd hcenterST
  apply Prod.ext <;> dsimp at hr hi hr' hi' ⊢ <;> linarith

private theorem reflectedSet :
    (by
      classical
      exact
        ∀ (u : GaussianInt),
        let refl : GaussianInt → GaussianInt := fun x => GaussianTranslation u (-x)
        ∀ (X : ProtoTile), ∀ (Y : ProtoTile), (FootprintVertices (TileTranslation (TileHalfTurn
            X) u) =
            FootprintVertices Y) → (FootprintVertices Y = refl '' FootprintVertices X) ) := by
  classical
  intro u refl X Y hX
  calc
    FootprintVertices Y =
        FootprintVertices (TileTranslation (TileHalfTurn X) u) := hX.symm
    _ = GaussianTranslation u '' FootprintVertices (TileHalfTurn X) :=
      (TileTranslationFormulas (TileHalfTurn X) u).2.2.2.2.2.1
    _ = GaussianTranslation u '' ((fun x : GaussianInt => -x) ''
        FootprintVertices X) := by rw [(TileHalfTurnFormulas X).2.2.2.2.2.2.1]
    _ = refl '' FootprintVertices X := by
      rw [Set.image_image]

private theorem reflInjective :
    (by
      classical
      exact
        ∀ (u : GaussianInt),
        let refl : GaussianInt → GaussianInt := fun x => GaussianTranslation u (-x)
        Function.Injective refl ) := by
  classical
  intro u refl x y hxy
  have hneg : -x = -y := by
    have := congrArg (fun z : GaussianInt => z - u) hxy
    simpa [refl, GaussianTranslation, sub_eq_add_neg, add_assoc] using this
  exact neg_injective hneg

private theorem hrawBD :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let A := cert.P 0 true
        let B := cert.P 0 false
        (FootprintVertices (cert.P (0 : Fin (3 : ℕ)) true) ∩ FootprintVertices (cert.P (1 : Fin
            (3 : ℕ)) true) ⊆ FootprintVertices (cert.Q (1 : Fin (3 : ℕ)) true) ∩
            FootprintVertices (cert.P (1 : Fin (3 : ℕ)) true)) → (∀ (u : GaussianInt),
        let refl : GaussianInt → GaussianInt := fun x => GaussianTranslation u (-x)
        (FootprintVertices B = refl '' FootprintVertices A) → ((FootprintVertices (cert.P (1 :
            Fin (3 : ℕ)) false) = refl '' FootprintVertices (cert.P (1 : Fin (3 : ℕ)) true)) →
            ((FootprintVertices (cert.S (1 : Fin (3 : ℕ)) false) = refl '' FootprintVertices
            (cert.Q (1 : Fin (3 : ℕ)) true)) → ((Function.Injective refl) → (FootprintVertices B
            ∩ FootprintVertices (cert.P 1 false) ⊆ FootprintVertices (cert.S 1 false) ∩
            FootprintVertices (cert.P 1 false)))))) ) := by
  classical
  intro q cfg C T cert A B hrawAC u refl reflectedA reflectedC reflectedQ reflInjective x hx
  have hxA : x ∈ refl '' FootprintVertices A := by
    rw [← reflectedA]
    exact hx.1
  have hxC : x ∈ refl '' FootprintVertices (cert.P 1 true) := by
    rw [← reflectedC]
    exact hx.2
  obtain ⟨a, haA, hax⟩ := hxA
  obtain ⟨c, hcC, hcx⟩ := hxC
  have hac : a = c := reflInjective (hax.trans hcx.symm)
  subst c
  have hAC := hrawAC ⟨haA, hcC⟩
  have hxS : x ∈ FootprintVertices (cert.S 1 false) := by
    rw [reflectedQ]
    exact ⟨a, hAC.1, hax⟩
  exact ⟨hxS, hx.2⟩

private theorem oFootU :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (U : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin 3), ∀ (s : Bool), (U i
            s).cells = (cert.Q i s).cells ∧ ((U i s).cells = ∅ → (U i s).anchor = (cert.Q i
            s).anchor) ∧ FootprintVertices (U i s) = FootprintVertices (cert.Q i s)) →
            (FootprintVertices cert.O = FootprintVertices (U 0 false)) ) := by
  classical
  intro q cfg C T cert U alignA
  rw [cert.precursor_eq]
  exact (alignA 0 false).2.2.symm

private theorem oFootV :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (V : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin 3), ∀ (s : Bool), (V i
            s).cells = (cert.S i s).cells ∧ ((V i s).cells = ∅ → (V i s).anchor = (cert.S i
            s).anchor) ∧ FootprintVertices (V i s) = FootprintVertices (cert.S i s)) → (((cert.Q
            0 false).cells = (cert.S 0 true).cells) → ((((cert.Q 0 false).cells = ∅) → ((cert.Q 0
            false).anchor = (cert.S 0 true).anchor)) → (FootprintVertices cert.O =
            FootprintVertices (V 0 true)))) ) := by
  classical
  intro q cfg C T cert V alignB qSCells qSAnchor
  have hobs := ProtoTileObservableExtensionality
    (cert.Q 0 false) (cert.S 0 true) qSCells qSAnchor
  rw [cert.precursor_eq]
  exact hobs.1.trans ((alignB 0 true).2.2.symm)

private theorem hxLK :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (k : Fin (3 : ℕ) → Bool → PartialOdometer), ((k 1 true).domain =
            FootprintVertices (cert.Q 1 true)) → ((∀ (X : ProtoTile), ∀ (x : GaussianInt), (x ∈
            BoundaryFootprintVertices X) → (x ∈ FootprintVertices X)) → (∀ (xL : GaussianInt),
            (xL ∈ BoundaryFootprintVertices (cert.Q (1 : Fin (3 : ℕ)) true)) → (xL ∈ ((k 1
            true).domain : Set GaussianInt)))) ) := by
  classical
  intro q cfg C T cert k hdomQ boundaryRaw xL hxLQ
  rw [hdomQ]
  exact boundaryRaw _ _ hxLQ

private theorem hxLS3 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (l : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (X : ProtoTile), ∀ (x :
            GaussianInt), (x ∈ BoundaryFootprintVertices X) → (x ∈ FootprintVertices X)) → (((l 2
            false).domain = FootprintVertices (cert.S 2 false)) → (∀ (xL : GaussianInt), (xL ∈
            BoundaryFootprintVertices (cert.S (2 : Fin (3 : ℕ)) false)) → (xL ∈ ((l 2
            false).domain : Set GaussianInt)))) ) := by
  classical
  intro q cfg C T cert l boundaryRaw hdomS3 xL hxLS
  rw [hdomS3]
  exact boundaryRaw _ _ hxLS

private theorem hxRK3 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (k : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (X : ProtoTile), ∀ (x :
            GaussianInt), (x ∈ BoundaryFootprintVertices X) → (x ∈ FootprintVertices X)) → (((k 2
            true).domain = FootprintVertices (cert.Q 2 true)) → (∀ (xR : GaussianInt), (xR ∈
            BoundaryFootprintVertices (cert.Q (2 : Fin (3 : ℕ)) true)) → (xR ∈ ((k 2 true).domain
            : Set GaussianInt)))) ) := by
  classical
  intro q cfg C T cert k boundaryRaw hdomQ3 xR hxRQ
  rw [hdomQ3]
  exact boundaryRaw _ _ hxRQ

private theorem hxRS2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (l : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (X : ProtoTile), ∀ (x :
            GaussianInt), (x ∈ BoundaryFootprintVertices X) → (x ∈ FootprintVertices X)) → (((l 1
            false).domain = FootprintVertices (cert.S 1 false)) → (∀ (xR : GaussianInt), (xR ∈
            BoundaryFootprintVertices (cert.S (1 : Fin (3 : ℕ)) false)) → (xR ∈ ((l 1
            false).domain : Set GaussianInt)))) ) := by
  classical
  intro q cfg C T cert l boundaryRaw hdomS2 xR hxRS
  rw [hdomS2]
  exact boundaryRaw _ _ hxRS

private theorem crossOneConstant :
    (by
      classical
      exact
        ∀ (k : Fin (3 : ℕ) → Bool → PartialOdometer), ∀ (l : Fin (3 : ℕ) → Bool →
            PartialOdometer), (OdometerCompatibility (k 1 true) (l 2 false)) → (∀ (xL :
            GaussianInt), (xL ∈ ((k 1 true).domain : Set GaussianInt)) → ((xL ∈ ((l 2
            false).domain : Set GaussianInt)) → (∃ c : Int, ∀ x, x ∈ (k 1 true).domain → x ∈ (l 2
            false).domain → (l 2 false).value x - (k 1 true).value x = c))) ) := by
  classical
  intro k l compatCross1 xL hxLK hxLS3
  rcases compatCross1 with hdis | hconst
  · exact False.elim ((Set.disjoint_left.mp hdis) hxLK hxLS3)
  · exact hconst

private theorem crossTwoConstant :
    (by
      classical
      exact
        ∀ (k : Fin (3 : ℕ) → Bool → PartialOdometer), ∀ (l : Fin (3 : ℕ) → Bool →
            PartialOdometer), (OdometerCompatibility (l 1 false) (k 2 true)) → (∀ (xR :
            GaussianInt), (xR ∈ ((k 2 true).domain : Set GaussianInt)) → ((xR ∈ ((l 1
            false).domain : Set GaussianInt)) → (∃ c : Int, ∀ x, x ∈ (l 1 false).domain → x ∈ (k
            2 true).domain → (k 2 true).value x - (l 1 false).value x = c))) ) := by
  classical
  intro k l compatCross2 xR hxRK3 hxRS2
  rcases compatCross2 with hdis | hconst
  · exact False.elim ((Set.disjoint_left.mp hdis) hxRS2 hxRK3)
  · exact hconst

private theorem hleftCal :
    (by
      classical
      exact
        ∀ (h : Fin 3 → Bool → PartialOdometer), ∀ (k : Fin (3 : ℕ) → Bool → PartialOdometer), (∀
            (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ x ∈ (k i s).domain, (h (0 : Fin (3 : ℕ))
            true).value x = (k i s).value x) → (∀ (l : Fin (3 : ℕ) → Bool → PartialOdometer), (∀
            (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ x ∈ (l i s).domain, (h (0 : Fin (3 : ℕ))
            false).value x = (l i s).value x) → (∀ (cO : ℤ), (∀ x ∈ (k (0 : Fin (3 : ℕ))
            false).domain, x ∈ (l (0 : Fin (3 : ℕ)) true).domain → (l (0 : Fin (3 : ℕ))
            true).value x - (k (0 : Fin (3 : ℕ)) false).value x = cO) → (∀ (xL : GaussianInt),
            (xL ∈ ((k 1 true).domain : Set GaussianInt)) → ((xL ∈ ((l 2 false).domain : Set
            GaussianInt)) → ((xL ∈ ((k 0 false).domain : Set GaussianInt)) → ((xL ∈ ((l 0
            true).domain : Set GaussianInt)) → (∀ (cL : ℤ), (∀ x ∈ (k (1 : Fin (3 : ℕ))
            true).domain, x ∈ (l (2 : Fin (3 : ℕ)) false).domain → (l (2 : Fin (3 : ℕ))
            false).value x - (k (1 : Fin (3 : ℕ)) true).value x = cL) → (cL = cO)))))))) ) := by
  classical
  intro h k hvalueA l hvalueB cO hcO xL hxLK hxLS3 hxLK0 hxLL0 cL hcL
  have hcross := hcL xL hxLK hxLS3
  have hprec := hcO xL hxLK0 hxLL0
  have hvA := hvalueA 1 true xL hxLK
  have hvB := hvalueB 2 false xL hxLS3
  have hvA0 := hvalueA 0 false xL hxLK0
  have hvB0 := hvalueB 0 true xL hxLL0
  rw [← hvB, ← hvA] at hcross
  rw [← hvB0, ← hvA0] at hprec
  linarith

private theorem hrightCal :
    (by
      classical
      exact
        ∀ (h : Fin 3 → Bool → PartialOdometer), ∀ (k : Fin (3 : ℕ) → Bool → PartialOdometer), (∀
            (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ x ∈ (k i s).domain, (h (0 : Fin (3 : ℕ))
            true).value x = (k i s).value x) → (∀ (l : Fin (3 : ℕ) → Bool → PartialOdometer), (∀
            (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ x ∈ (l i s).domain, (h (0 : Fin (3 : ℕ))
            false).value x = (l i s).value x) → (∀ (cO : ℤ), (∀ x ∈ (k (0 : Fin (3 : ℕ))
            false).domain, x ∈ (l (0 : Fin (3 : ℕ)) true).domain → (l (0 : Fin (3 : ℕ))
            true).value x - (k (0 : Fin (3 : ℕ)) false).value x = cO) → (∀ (xR : GaussianInt),
            (xR ∈ ((k 2 true).domain : Set GaussianInt)) → ((xR ∈ ((l 1 false).domain : Set
            GaussianInt)) → ((xR ∈ ((k 0 false).domain : Set GaussianInt)) → ((xR ∈ ((l 0
            true).domain : Set GaussianInt)) → (∀ (cR : ℤ), (∀ x ∈ (l (1 : Fin (3 : ℕ))
            false).domain, x ∈ (k (2 : Fin (3 : ℕ)) true).domain → (k (2 : Fin (3 : ℕ))
            true).value x - (l (1 : Fin (3 : ℕ)) false).value x = cR) → (cR = -cO)))))))) ) := by
  classical
  intro h k hvalueA l hvalueB cO hcO xR hxRK3 hxRS2 hxRK0 hxRL0 cR hcR
  have hcross := hcR xR hxRS2 hxRK3
  have hprec := hcO xR hxRK0 hxRL0
  have hvB := hvalueB 1 false xR hxRS2
  have hvA := hvalueA 2 true xR hxRK3
  have hvA0 := hvalueA 0 false xR hxRK0
  have hvB0 := hvalueB 0 true xR hxRL0
  rw [← hvA, ← hvB] at hcross
  rw [← hvB0, ← hvA0] at hprec
  linarith

private theorem compatAB :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (h : Fin 3 → Bool → PartialOdometer),
        let A := cert.P 0 true
        let B := cert.P 0 false
        ∀ (U : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (k : Fin (3 : ℕ) → Bool → PartialOdometer), ((h
            0 true).domain = FootprintVertices A) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ x ∈ (k
            i s).domain, (h (0 : Fin (3 : ℕ)) true).value x = (k i s).value x) → (∀ (V : Fin (3 :
            ℕ) → Bool → ProtoTile), ∀ (l : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i : Fin (3
            : ℕ)), ∀ (s : Bool), ∀ x ∈ (l i s).domain, (h (0 : Fin (3 : ℕ)) false).value x = (l i
            s).value x) → ((∀ (i : Fin 3), ∀ (s : Bool), (U i s).cells = (cert.Q i s).cells ∧ ((U
            i s).cells = ∅ → (U i s).anchor = (cert.Q i s).anchor) ∧ FootprintVertices (U i s) =
            FootprintVertices (cert.Q i s)) → (((h 0 false).domain = FootprintVertices B) → (((k
            1 true).domain = FootprintVertices (cert.Q 1 true)) → ((FootprintVertices (cert.P (0
            : Fin (3 : ℕ)) true) ∩ FootprintVertices (cert.P (0 : Fin (3 : ℕ)) false) ⊆
            FootprintVertices (cert.Q (1 : Fin (3 : ℕ)) true) ∩ FootprintVertices (cert.S (2 :
            Fin (3 : ℕ)) false) ∪ FootprintVertices (cert.Q (0 : Fin (3 : ℕ)) false) ∪
            FootprintVertices (cert.Q (2 : Fin (3 : ℕ)) true) ∩ FootprintVertices (cert.S (1 :
            Fin (3 : ℕ)) false)) → ((∀ {V : Type}, ∀ (f : V → Int), ∀ (g : V → Int), ∀ (L : Set
            V), ∀ (O : Set V), ∀ (R : Set V), ∀ (Iset : Set V), ∀ (c : Int), ∀ (d : Int), ∀ (e :
            Int), ∀ (xL : V), ∀ (xR : V), (Iset ⊆ L ∪ O ∪ R) → ((∀ x ∈ L, g x - f x = d) → ((∀ x
            ∈ O, g x - f x = c) → ((∀ x ∈ R, f x - g x = e) → ((xL ∈ L ∩ O) → ((xR ∈ R ∩ O) → (∀
            x ∈ Iset, g x - f x = c))))))) → ((((k 0 false).domain : Set GaussianInt) =
            FootprintVertices (U 0 false) ∧ ((l 0 true).domain : Set GaussianInt) =
            FootprintVertices (V 0 true) ∧ ((k 0 false).domain : Set GaussianInt) = ((l 0
            true).domain : Set GaussianInt) ∧ ∃ c : Int, ∀ x, x ∈ (k 0 false).domain → x ∈ (l 0
            true).domain → (l 0 true).value x - (k 0 false).value x = c) → (((l 2 false).domain =
            FootprintVertices (cert.S 2 false)) → (((l 1 false).domain = FootprintVertices
            (cert.S 1 false)) → (((k 2 true).domain = FootprintVertices (cert.Q 2 true)) → (∀ (cO
            : ℤ), (∀ x ∈ (k (0 : Fin (3 : ℕ)) false).domain, x ∈ (l (0 : Fin (3 : ℕ))
            true).domain → (l (0 : Fin (3 : ℕ)) true).value x - (k (0 : Fin (3 : ℕ)) false).value
            x = cO) → (∀ (xL : GaussianInt), ∀ (xR : GaussianInt), (xL ∈ ((k 1 true).domain : Set
            GaussianInt)) → ((xL ∈ ((l 2 false).domain : Set GaussianInt)) → ((xL ∈ ((k 0
            false).domain : Set GaussianInt)) → ((xR ∈ ((k 2 true).domain : Set GaussianInt)) →
            ((xR ∈ ((l 1 false).domain : Set GaussianInt)) → ((xR ∈ ((k 0 false).domain : Set
            GaussianInt)) → (∀ (cL : ℤ), (∀ x ∈ (k (1 : Fin (3 : ℕ)) true).domain, x ∈ (l (2 :
            Fin (3 : ℕ)) false).domain → (l (2 : Fin (3 : ℕ)) false).value x - (k (1 : Fin (3 :
            ℕ)) true).value x = cL) → (∀ (cR : ℤ), (∀ x ∈ (l (1 : Fin (3 : ℕ)) false).domain, x ∈
            (k (2 : Fin (3 : ℕ)) true).domain → (k (2 : Fin (3 : ℕ)) true).value x - (l (1 : Fin
            (3 : ℕ)) false).value x = cR) → ((cL = cO) → ((cR = -cO) → (OdometerCompatibility (h
            0 true) (h 0 false)))))))))))))))))))))))) ) := by
  classical
  intro q cfg C T cert h A B U k hdomA hvalueA V l hvalueB alignA hdomBParent hdomQ hrawAB
      propagateConstant precursorConstant hdomS3 hdomS2 hdomQ3 cO hcO xL xR hxLK hxLS3 hxLK0
      hxRK3 hxRS2 hxRK0 cL hcL cR hcR hleftCal hrightCal
  right
  refine ⟨cO, ?_⟩
  intro x hxA hxB
  have hcover :
      (↑(h 0 true).domain ∩ ↑(h 0 false).domain : Set GaussianInt) ⊆
        (↑(k 1 true).domain ∩ ↑(l 2 false).domain) ∪
        ↑(k 0 false).domain ∪
        (↑(k 2 true).domain ∩ ↑(l 1 false).domain) := by
    intro y hy
    have hrawY : y ∈ FootprintVertices A ∩ FootprintVertices B := by
      exact ⟨by simpa only [hdomA] using hy.1,
        by simpa only [hdomBParent] using hy.2⟩
    have hraw := hrawAB hrawY
    change y ∈ (FootprintVertices (cert.Q 1 true) ∩
      FootprintVertices (cert.S 2 false)) ∪ FootprintVertices (cert.Q 0 false) ∪
      (FootprintVertices (cert.Q 2 true) ∩
        FootprintVertices (cert.S 1 false)) at hraw
    simp only [Set.mem_union, Set.mem_inter_iff] at hraw
    rcases hraw with (⟨hLQ, hLS⟩ | hO) | ⟨hRQ, hRS⟩
    · exact Or.inl (Or.inl ⟨by rw [hdomQ]; exact hLQ,
        by rw [hdomS3]; exact hLS⟩)
    · exact Or.inl (Or.inr (by
        have hO' : y ∈ FootprintVertices (U 0 false) := by
          rw [(alignA 0 false).2.2]
          exact hO
        rw [precursorConstant.1]
        exact hO'))
    · exact Or.inr ⟨by rw [hdomQ3]; exact hRQ,
        by rw [hdomS2]; exact hRS⟩
  have hleft : ∀ y, y ∈ ((k 1 true).domain : Set GaussianInt) ∩
      ((l 2 false).domain : Set GaussianInt) →
      (h 0 false).value y - (h 0 true).value y = cO := by
    intro y hy
    have hval := hcL y hy.1 hy.2
    have hvA := hvalueA 1 true y hy.1
    have hvB := hvalueB 2 false y hy.2
    rw [← hvB, ← hvA] at hval
    simpa [hleftCal] using hval
  have hmiddle : ∀ y, y ∈ ((k 0 false).domain : Set GaussianInt) →
      (h 0 false).value y - (h 0 true).value y = cO := by
    intro y hy
    have hyL : y ∈ ((l 0 true).domain : Set GaussianInt) := by
      rw [← precursorConstant.2.2.1]
      exact hy
    have hval := hcO y hy hyL
    have hvA := hvalueA 0 false y hy
    have hvB := hvalueB 0 true y hyL
    rw [← hvB, ← hvA] at hval
    exact hval
  have hright : ∀ y, y ∈ ((k 2 true).domain : Set GaussianInt) ∩
      ((l 1 false).domain : Set GaussianInt) →
      (h 0 true).value y - (h 0 false).value y = -cO := by
    intro y hy
    have hval := hcR y hy.2 hy.1
    have hvA := hvalueA 2 true y hy.1
    have hvB := hvalueB 1 false y hy.2
    rw [← hvA, ← hvB] at hval
    simpa [hrightCal] using hval
  have hxLinter : xL ∈ (((k 1 true).domain : Set GaussianInt) ∩
      ((l 2 false).domain : Set GaussianInt)) ∩
      ((k 0 false).domain : Set GaussianInt) := ⟨⟨hxLK, hxLS3⟩, hxLK0⟩
  have hxRinter : xR ∈ (((k 2 true).domain : Set GaussianInt) ∩
      ((l 1 false).domain : Set GaussianInt)) ∩
      ((k 0 false).domain : Set GaussianInt) := ⟨⟨hxRK3, hxRS2⟩, hxRK0⟩
  have hprop := propagateConstant
    (h 0 true).value (h 0 false).value
    (↑(k 1 true).domain ∩ ↑(l 2 false).domain)
    (↑(k 0 false).domain)
    (↑(k 2 true).domain ∩ ↑(l 1 false).domain)
    (↑(h 0 true).domain ∩ ↑(h 0 false).domain)
    cO cO (-cO) xL xR hcover hleft hmiddle hright hxLinter hxRinter
  exact hprop x ⟨hxA, hxB⟩

end NestedCompatibilityGeometry

namespace NestedPrecursorConstant

private theorem precursorConstant :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (h :
            Fin 3 → Bool → PartialOdometer), ∀ (s0 : Real × Real), (∀ (i : Fin (3 : ℕ)), ∀ (s :
            Bool), PartialOdometerSlope (h i s) = some (s0 + (if s = true then (1 : ℝ) else (-1 :
            ℝ)) • P4250T1SlopeOffset (BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1
            : Fin (3 : ℕ))).succ)))) → (∀ (U : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (k : Fin (3 :
            ℕ) → Bool → PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileOdometer
            (cfg.firstPredecessor i.succ) (U i s) (k i s)) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            (cfg.firstPredecessor i.succ).1 = (0 : ℤ) ∨ ∃ (p : ℝ × ℝ) (p_i : ℝ × ℝ),
            PartialOdometerSlope (h (0 : Fin (3 : ℕ)) true) = some p ∧ PartialOdometerSlope (k i
            s) = some p_i ∧ p_i.1 - p.1 = (if s = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ)
            * ((↑(BandVectors.2 (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ)
            (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ) - (↑(BandVectors.2
            (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ) (cfg.firstPredecessor (i + (1 :
            Fin (3 : ℕ))).succ)).im : ℝ)) ∧ p_i.2 - p.2 = (if s = true then (1 : ℝ) else (-1 :
            ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (cfg.firstPredecessor (i + (2 : Fin (3 :
            ℕ))).succ) (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)).im : ℝ) +
            (↑(BandVectors.2 (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ)
            (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → (∀ (V : Fin (3 : ℕ)
            → Bool → ProtoTile), ∀ (l : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i : Fin (3 :
            ℕ)), ∀ (s : Bool), TileOdometer (cfg.firstPredecessor i.succ) (V i s) (l i s)) → ((∀
            (i : Fin (3 : ℕ)), ∀ (s : Bool), (cfg.firstPredecessor i.succ).1 = (0 : ℤ) ∨ ∃ (p : ℝ
            × ℝ) (p_i : ℝ × ℝ), PartialOdometerSlope (h (0 : Fin (3 : ℕ)) false) = some p ∧
            PartialOdometerSlope (l i s) = some p_i ∧ p_i.1 - p.1 = (if s = true then (1 : ℝ)
            else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (cfg.firstPredecessor (i + (2 : Fin
            (3 : ℕ))).succ) (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ) -
            (↑(BandVectors.2 (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ)
            (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)).im : ℝ)) ∧ p_i.2 - p.2 = (if s =
            true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2
            (cfg.firstPredecessor (i + (2 : Fin (3 : ℕ))).succ) (cfg.firstPredecessor (i + (1 :
            Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (cfg.firstPredecessor (i + (2 : Fin
            (3 : ℕ))).succ) (cfg.firstPredecessor (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → ((∀
            (D : CircleCoordinates), ∀ (X : ProtoTile), BandPrototile D X → 0 < D.1 →
            X.cells.Nonempty) → (((U 0 false).cells = (V 0 true).cells) → ((((U 0 false).cells =
            ∅) → ((U 0 false).anchor = (V 0 true).anchor)) → ((FootprintVertices (U (0 : Fin (3 :
            ℕ)) false) = FootprintVertices (V (0 : Fin (3 : ℕ)) true) ∧ BoundaryFootprintVertices
            (U (0 : Fin (3 : ℕ)) false) = BoundaryFootprintVertices (V (0 : Fin (3 : ℕ)) true) ∧
            BoundaryFootprintEdges (U (0 : Fin (3 : ℕ)) false) = BoundaryFootprintEdges (V (0 :
            Fin (3 : ℕ)) true) ∧ TileRealization (U (0 : Fin (3 : ℕ)) false) = TileRealization (V
            (0 : Fin (3 : ℕ)) true) ∧ TileCentroid (U (0 : Fin (3 : ℕ)) false) = TileCentroid (V
            (0 : Fin (3 : ℕ)) true)) → ((∀ {D : CircleCoordinates}, ∀ {X : ProtoTile}, ∀
            {g : PartialOdometer}, (D.1 = 0) → ((TileOdometer D X g) → (∃ x, X = ⟨∅, x⟩ ∧
            g.domain = {x}))) → (((k 0 false).domain : Set GaussianInt) = FootprintVertices (U 0
            false) ∧ ((l 0 true).domain : Set GaussianInt) = FootprintVertices (V 0 true) ∧ ((k 0
            false).domain : Set GaussianInt) = ((l 0 true).domain : Set GaussianInt) ∧ ∃ c : Int,
            ∀ x, x ∈ (k 0 false).domain → x ∈ (l 0 true).domain → (l 0 true).value x - (k 0
            false).value x = c)))))))))) ) := by
  classical
  intro q cfg h s0 hp U k hchildA hslopeA V l hchildB hslopeB bandPositiveNonempty uvCells
      uvAnchor uvObservable zeroOdometerLine
  by_cases hzero : (cfg.firstPredecessor 1).1 = 0
  · have kline := NestedCompatibilityGeometry.kline q cfg U k hchildA zeroOdometerLine hzero
    have lline := NestedCompatibilityGeometry.lline q cfg V l hchildB zeroOdometerLine hzero
    obtain ⟨xk, htileK, hdomK⟩ := kline
    obtain ⟨xl, htileL, hdomL⟩ := lline
    have hxy := NestedCompatibilityGeometry.hxy U V uvAnchor xk htileK xl htileL
    subst xl
    refine ⟨?_, ?_, ?_, ⟨(l 0 true).value xk - (k 0 false).value xk, ?_⟩⟩
    · ext x
      simp [hdomK, htileK, FootprintVertices]
    · ext x
      simp [hdomL, htileL, FootprintVertices]
    · ext x
      simp [hdomK, hdomL]
    · intro x hxK hxL
      have hx : x = xk := by simpa [hdomK] using hxK
      subst x
      rfl
  · have hcurvpos := NestedCompatibilityGeometry.hcurvpos q cfg hzero
    have kSlope : PartialOdometerSlope (k 0 false) = some s0 :=
        NestedCompatibilityGeometry.kSlope q cfg h s0 hp k hslopeA hzero
    have lSlope : PartialOdometerSlope (l 0 true) = some s0 :=
        NestedCompatibilityGeometry.lSlope q cfg h s0 hp l hslopeB hzero
    have hdomK := PositiveCurvatureTileOdometerDomain
      (cfg.firstPredecessor 1) (U 0 false) (k 0 false) hcurvpos
      (hchildA 0 false)
    have hdomL := PositiveCurvatureTileOdometerDomain
      (cfg.firstPredecessor 1) (V 0 true) (l 0 true) hcurvpos
      (hchildB 0 true)
    obtain ⟨shift, ⟨hcellsEq, hanchorEq, aa, bb, hdomains, hvalues⟩, _⟩ :=
      TileOdometerTranslationUniqueness (cfg.firstPredecessor 1)
        (U 0 false) (V 0 true) (k 0 false) (l 0 true) hcurvpos
        (hchildA 0 false) (hchildB 0 true)
    have hneU : (U 0 false).cells.Nonempty :=
      bandPositiveNonempty (cfg.firstPredecessor 1) (U 0 false)
        (TileOdometerBandPrototile _ _ _ (hchildA 0 false)) hcurvpos
    have hcellShift : (V 0 true).cells =
        (TileTranslation (V 0 true) shift).cells :=
      uvCells.symm.trans hcellsEq
    have hcentShift : TileCentroid (V 0 true) =
        TileCentroid (TileTranslation (V 0 true) shift) :=
            NestedCompatibilityGeometry.hcentShift V shift (NestedCompatibilityGeometry.hneV U
            V uvCells hneU) hcellShift
    rw [(TileTranslationFormulas (V 0 true) shift).2.2.2.2.1]
      at hcentShift
    have hshift : shift = 0 := NestedCompatibilityGeometry.hshift shift
        (NestedCompatibilityGeometry.hshiftRe V shift hcentShift)
        (NestedCompatibilityGeometry.hshiftIm V shift hcentShift)
    have hdomainEq := NestedCompatibilityGeometry.hdomainEq k l shift aa bb hdomains hshift
    have hslopeEq : PartialOdometerSlope (k 0 false) =
        ((PartialOdometerSlope (l 0 true)).map
          (fun p => (p.1 + (aa.re : Real), p.2 + (aa.im : Real)))) :=
              NestedCompatibilityGeometry.hslopeEq k l aa bb
              (NestedCompatibilityGeometry.heqAt1131 k l aa bb hdomainEq
              (NestedCompatibilityGeometry.hvalueEq k l shift aa bb hvalues hshift hdomainEq))
    rw [kSlope, lSlope, Option.map_some] at hslopeEq
    have hslopePair :
        s0 = (s0.1 + (aa.re : Real), s0.2 + (aa.im : Real)) :=
      Option.some.inj hslopeEq
    have haa : aa = 0 := NestedCompatibilityGeometry.haa aa (NestedCompatibilityGeometry.haaRe
        s0 aa hslopePair) (NestedCompatibilityGeometry.haaIm s0 aa hslopePair)
    refine ⟨?_, ?_, ?_, ⟨-bb, ?_⟩⟩
    · exact hdomK
    · exact hdomL
    · exact hdomK.trans (uvObservable.1.trans hdomL.symm)
    · intro x hxK hxL
      have hv := hvalues x hxK
      rw [hshift, haa] at hv
      have hv' : (k 0 false).value x = (l 0 true).value x + bb := by
        simpa using hv
      omega

end NestedPrecursorConstant

namespace NestedCompatibilityConclusion

private theorem nestedCompatibilityConclusion :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (h : Fin 3 → Bool → PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            TileOdometer (q i.succ) (cert.P i s) (h i s)) → (
        let A := cert.P 0 true
        let B := cert.P 0 false
        (1 < (cfg.firstPredecessor 0).1) → (∀ (U : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (k : Fin (3
            : ℕ) → Bool → PartialOdometer), (BandPrototile (cfg.firstPredecessor (0 : Fin (4 :
            ℕ))) A) → (((h 0 true).domain = FootprintVertices A) → ((∀ (i : Fin (3 : ℕ)), ∀ (s :
            Bool), ∀ x ∈ (k i s).domain, (h (0 : Fin (3 : ℕ)) true).value x = (k i s).value x) →
            (∀ (V : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (l : Fin (3 : ℕ) → Bool →
            PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ x ∈ (l i s).domain, (h (0 :
            Fin (3 : ℕ)) false).value x = (l i s).value x) → ((∀ (i : Fin 3), ∀ (s : Bool), (U i
            s).cells = (cert.Q i s).cells ∧ ((U i s).cells = ∅ → (U i s).anchor = (cert.Q i
            s).anchor) ∧ FootprintVertices (U i s) = FootprintVertices (cert.Q i s)) → ((∀ (i :
            Fin 3), ∀ (s : Bool), (V i s).cells = (cert.S i s).cells ∧ ((V i s).cells = ∅ → (V i
            s).anchor = (cert.S i s).anchor) ∧ FootprintVertices (V i s) = FootprintVertices
            (cert.S i s)) → ((0 < (cfg.firstPredecessor 2).1) → ((0 < (cfg.firstPredecessor 3).1)
            → ((TileOdometer (cfg.firstPredecessor 2) (cert.Q 1 true) (k 1 true)) →
            ((TileOdometer (cfg.firstPredecessor 2) (cert.S 1 false) (l 1 false)) →
            ((TileOdometer (cfg.firstPredecessor 3) (cert.S 2 false) (l 2 false)) →
            ((TileOdometer (cfg.firstPredecessor 3) (cert.Q 2 true) (k 2 true)) → (
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        let xv : GaussianInt := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        let v13 : GaussianInt := BandVectors.1 (q 1) (q 3)
        let spatial (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (TileCentroid A - TileCentroid T = spatial w) → ((TileCentroid (cert.P 1 true) -
            TileCentroid T = spatial v13) → ((TileCentroid (cert.Q 1 true) - TileCentroid T =
            spatial xv + spatial w) → ((∀ (a : PartialOdometer), ∀ (b : PartialOdometer), ∀ (r :
            PartialOdometer), ∀ (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (Z : ProtoTile), ((a.domain
            : Set GaussianInt) = FootprintVertices X) → (((b.domain : Set GaussianInt) =
            FootprintVertices Y) → (((r.domain : Set GaussianInt) = FootprintVertices Z) → ((∀ x,
            x ∈ r.domain → a.value x = r.value x) → ((FootprintVertices X ∩ FootprintVertices Y ⊆
            FootprintVertices Z ∩ FootprintVertices Y) → ((OdometerCompatibility r b) →
            (OdometerCompatibility a b))))))) → ((0 < (q 1).1) → (((h 0 false).domain =
            FootprintVertices B) → (((k 1 true).domain = FootprintVertices (cert.Q 1 true)) →
            ((FootprintVertices (cert.P (0 : Fin (3 : ℕ)) true) ∩ FootprintVertices (cert.P (1 :
            Fin (3 : ℕ)) true) ⊆ FootprintVertices (cert.Q (1 : Fin (3 : ℕ)) true) ∩
            FootprintVertices (cert.P (1 : Fin (3 : ℕ)) true)) → ((FootprintVertices (cert.P (0 :
            Fin (3 : ℕ)) true) ∩ FootprintVertices (cert.P (0 : Fin (3 : ℕ)) false) ⊆
            FootprintVertices (cert.Q (1 : Fin (3 : ℕ)) true) ∩ FootprintVertices (cert.S (2 :
            Fin (3 : ℕ)) false) ∪ FootprintVertices (cert.Q (0 : Fin (3 : ℕ)) false) ∪
            FootprintVertices (cert.Q (2 : Fin (3 : ℕ)) true) ∩ FootprintVertices (cert.S (1 :
            Fin (3 : ℕ)) false)) → ((OdometerCompatibility (h 0 true) (h 1 true)) →
            ((TileCentroid B - TileCentroid T = -spatial w) → ((TileCentroid (cert.S 1 false) -
            TileCentroid B = -spatial xv) → ((TileCentroid (cert.P 1 false) - TileCentroid T =
            -spatial v13) → ((OdometerCompatibility (l 1 false) (h 1 false)) →
            ((OdometerCompatibility (k 1 true) (l 2 false)) → ((OdometerCompatibility (l 1 false)
            (k 2 true)) → ((∀ {V : Type}, ∀ (f : V → Int), ∀ (g : V → Int), ∀ (L : Set V), ∀ (O :
            Set V), ∀ (R : Set V), ∀ (Iset : Set V), ∀ (c : Int), ∀ (d : Int), ∀ (e : Int), ∀ (xL
            : V), ∀ (xR : V), (Iset ⊆ L ∪ O ∪ R) → ((∀ x ∈ L, g x - f x = d) → ((∀ x ∈ O, g x - f
            x = c) → ((∀ x ∈ R, f x - g x = e) → ((xL ∈ L ∩ O) → ((xR ∈ R ∩ O) → (∀ x ∈ Iset, g x
            - f x = c))))))) → ((∀ (D : CircleCoordinates), ∀ (X : ProtoTile), BandPrototile D X
            → 0 < D.1 → X.cells.Nonempty) → (((cert.Q 0 false).cells = (cert.S 0 true).cells) →
            ((((cert.Q 0 false).cells = ∅) → ((cert.Q 0 false).anchor = (cert.S 0 true).anchor))
            → ((((k 0 false).domain : Set GaussianInt) = FootprintVertices (U 0 false) ∧ ((l 0
            true).domain : Set GaussianInt) = FootprintVertices (V 0 true) ∧ ((k 0 false).domain
            : Set GaussianInt) = ((l 0 true).domain : Set GaussianInt) ∧ ∃ c : Int, ∀ x, x ∈ (k 0
            false).domain → x ∈ (l 0 true).domain → (l 0 true).value x - (k 0 false).value x = c)
            → (OdometerCompatibility (h 0 true) (h 1 true) ∧ OdometerCompatibility (h 0 false) (h
            1 false) ∧ OdometerCompatibility (h 0 true) (h 0
            false)))))))))))))))))))))))))))))))))))) ) := by
  classical
  intro q cfg C T cert h ho A B hroot U k hbandA hdomA hvalueA V l hvalueB alignA alignB pos2
      pos3 odoQ2 odoS2 odoS3 odoQ3 w xv v13 spatial hcenterA hcenterP hcenterQT rawCompatLift
      hq1pos hdomBParent hdomQ hrawAC hrawAB compatAC hcenterB hcenterS hcenterPminus
      compatBDNested compatCross1 compatCross2 propagateConstant bandPositiveNonempty qSCells
      qSAnchor precursorConstant
  have boundaryRaw := NestedCompatibilityGeometry.boundaryRaw
  have centerIntegral := NestedCompatibilityGeometry.centerIntegral q T
      (NestedCompatibilityGeometry.rootBand q cfg C T cert)
      (NestedCompatibilityGeometry.rootNonempty q cfg C T cert hroot hbandA bandPositiveNonempty)
  obtain ⟨u, hu⟩ := centerIntegral
  have reflectedFoot := NestedCompatibilityGeometry.reflectedFoot T bandPositiveNonempty u hu
  have hsumCD : TileCentroid (cert.P 1 true) + TileCentroid (cert.P 1 false) =
      (2 : Real) • TileCentroid T := NestedCompatibilityGeometry.hsumCD q cfg C T cert hcenterP
          hcenterPminus
  have hreflectAB : FootprintVertices (TileTranslation (TileHalfTurn A) u) =
      FootprintVertices B := reflectedFoot (q 1) A B (h 0 true)
      (by simpa [A] using ho 0 true)
      (TileOdometerBandPrototile _ _ _ (by simpa [B] using ho 0 false))
      hq1pos (NestedCompatibilityGeometry.hsumAB q cfg C T cert hcenterA hcenterB)
  have hreflectCD : FootprintVertices
      (TileTranslation (TileHalfTurn (cert.P 1 true)) u) =
        FootprintVertices (cert.P 1 false) := reflectedFoot (q 2)
          (cert.P 1 true) (cert.P 1 false) (h 1 true)
          (by simpa using ho 1 true)
          (TileOdometerBandPrototile _ _ _ (ho 1 false))
          (by simpa [cfg.firstParentTwo] using pos2) hsumCD
  have hreflectQS : FootprintVertices
      (TileTranslation (TileHalfTurn (cert.Q 1 true)) u) =
        FootprintVertices (cert.S 1 false) := reflectedFoot
          (cfg.firstPredecessor 2) (cert.Q 1 true) (cert.S 1 false)
          (k 1 true) odoQ2 (TileOdometerBandPrototile _ _ _ odoS2)
          pos2 (NestedCompatibilityGeometry.hsumQS q cfg C T cert hcenterQT
              (NestedCompatibilityGeometry.hcenterSTAt1375 q cfg C T cert hcenterB hcenterS))
  have reflectedSet := NestedCompatibilityGeometry.reflectedSet u
  have reflectedA := reflectedSet A B hreflectAB
  have reflectedC := reflectedSet (cert.P 1 true) (cert.P 1 false) hreflectCD
  have reflectedQ := reflectedSet (cert.Q 1 true) (cert.S 1 false) hreflectQS
  have hdomD : (h 1 false).domain = FootprintVertices (cert.P 1 false) :=
    PositiveCurvatureTileOdometerDomain (q 2) (cert.P 1 false) (h 1 false)
      (by simpa [cfg.firstParentTwo] using pos2)
      (by simpa using ho 1 false)
  have finishBD (hcompat : OdometerCompatibility (l 1 false) (h 1 false)) :
      OdometerCompatibility (h 0 false) (h 1 false) :=
    rawCompatLift (h 0 false) (h 1 false) (l 1 false) B
      (cert.P 1 false) (cert.S 1 false) hdomBParent hdomD
      (PositiveCurvatureTileOdometerDomain (cfg.firstPredecessor 2)
        (cert.S 1 false) (l 1 false) pos2 odoS2)
      (fun x hx => hvalueB 1 false x hx) (NestedCompatibilityGeometry.hrawBD q cfg C T cert
          hrawAC u reflectedA reflectedC reflectedQ (NestedCompatibilityGeometry.reflInjective
          u)) hcompat
  have oFootU := NestedCompatibilityGeometry.oFootU q cfg C T cert U alignA
  have oFootV := NestedCompatibilityGeometry.oFootV q cfg C T cert V alignB qSCells qSAnchor
  have hdomS3 : (l 2 false).domain = FootprintVertices (cert.S 2 false) :=
    PositiveCurvatureTileOdometerDomain (cfg.firstPredecessor 3)
      (cert.S 2 false) (l 2 false) pos3 odoS3
  have hdomS2 : (l 1 false).domain = FootprintVertices (cert.S 1 false) :=
    PositiveCurvatureTileOdometerDomain (cfg.firstPredecessor 2)
      (cert.S 1 false) (l 1 false) pos2 odoS2
  have hdomQ3 : (k 2 true).domain = FootprintVertices (cert.Q 2 true) :=
    PositiveCurvatureTileOdometerDomain (cfg.firstPredecessor 3)
      (cert.Q 2 true) (k 2 true) pos3 odoQ3
  have precursorValueConstant : ∃ c : Int, ∀ x,
      x ∈ (k 0 false).domain → x ∈ (l 0 true).domain →
      (l 0 true).value x - (k 0 false).value x = c := precursorConstant.2.2.2
  obtain ⟨cO, hcO⟩ := precursorValueConstant
  obtain ⟨xL, hxL, _⟩ := cert.precursor_first.2.2.2
  rcases hxL with ⟨hxLQ, hxLS, hxLO⟩
  obtain ⟨xR, hxR, _⟩ := cert.precursor_second.2.2.2
  rcases hxR with ⟨hxRQ, hxRS, hxRO⟩
  have hxLK := NestedCompatibilityGeometry.hxLK q cfg C T cert k hdomQ boundaryRaw xL hxLQ
  have hxLS3 := NestedCompatibilityGeometry.hxLS3 q cfg C T cert l boundaryRaw hdomS3 xL hxLS
  have precursorKMembership (x : GaussianInt) (hx : x ∈ BoundaryFootprintVertices cert.O) :
      x ∈ ((k 0 false).domain : Set GaussianInt) := by
    rw [precursorConstant.1, ← oFootU]
    exact boundaryRaw _ _ hx
  have precursorLMembership (x : GaussianInt) (hx : x ∈ BoundaryFootprintVertices cert.O) :
      x ∈ ((l 0 true).domain : Set GaussianInt) := by
    rw [precursorConstant.2.1, ← oFootV]
    exact boundaryRaw _ _ hx
  have hxLK0 := precursorKMembership xL hxLO
  have hxLL0 := precursorLMembership xL hxLO
  have hxRK3 := NestedCompatibilityGeometry.hxRK3 q cfg C T cert k boundaryRaw hdomQ3 xR hxRQ
  have hxRS2 := NestedCompatibilityGeometry.hxRS2 q cfg C T cert l boundaryRaw hdomS2 xR hxRS
  have hxRK0 := precursorKMembership xR hxRO
  have hxRL0 := precursorLMembership xR hxRO
  have crossOneConstant := NestedCompatibilityGeometry.crossOneConstant k l compatCross1 xL hxLK
      hxLS3
  have crossTwoConstant := NestedCompatibilityGeometry.crossTwoConstant k l compatCross2 xR hxRK3
      hxRS2
  obtain ⟨cL, hcL⟩ := crossOneConstant
  obtain ⟨cR, hcR⟩ := crossTwoConstant
  refine ⟨compatAC, ?_, ?_⟩
  · exact finishBD compatBDNested
  · exact (NestedCompatibilityGeometry.compatAB q cfg C T cert h U k hdomA hvalueA V l hvalueB
      alignA hdomBParent hdomQ hrawAB propagateConstant precursorConstant hdomS3 hdomS2 hdomQ3 cO
      hcO xL xR hxLK hxLS3 hxLK0 hxRK3 hxRS2 hxRK0 cL hcL cR hcR
      (NestedCompatibilityGeometry.hleftCal h k hvalueA l hvalueB cO hcO xL hxLK hxLS3 hxLK0
      hxLL0 cL hcL) (NestedCompatibilityGeometry.hrightCal h k hvalueA l hvalueB cO hcO xR hxRK3
      hxRS2 hxRK0 hxRL0 cR hcR))

end NestedCompatibilityConclusion

theorem P4250T1NestedCompatibility
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (h : Fin 3 → Bool → PartialOdometer) (s0 : Real × Real)
    (ho : ∀ i s, TileOdometer (q i.succ) (cert.P i s) (h i s))
    (hp : ∀ i s, PartialOdometerSlope (h i s) = some
      (s0 + (if s = true then (1 : Real) else -1) •
        P4250T1SlopeOffset
          (BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))))) :
    OdometerCompatibility (h 0 true) (h 1 true) ∧
    OdometerCompatibility (h 0 false) (h 1 false) ∧
    OdometerCompatibility (h 0 true) (h 0 false) := by
-- BODY
  classical
  let A := cert.P 0 true
  let B := cert.P 0 false
  have hroot : 1 < (cfg.firstPredecessor 0).1 := NestedCompatibilityGeometry.hroot q cfg
  obtain ⟨U, k, hbandA, hchildA, hcellsA, hfootA, hcentA, hdomA,
    hvalueA, hcompatA, hslopeA⟩ :=
    TileOdometerReindexedDecomposition cfg.firstPredecessor cfg.firstProper
      A (h 0 true) hroot (by simpa [A, cfg.firstChild] using ho 0 true)
  obtain ⟨V, l, hbandB, hchildB, hcellsB, hfootB, hcentB, hdomB,
    hvalueB, hcompatB, hslopeB⟩ :=
    TileOdometerReindexedDecomposition cfg.firstPredecessor cfg.firstProper
      B (h 0 false) hroot (by simpa [B, cfg.firstChild] using ho 0 false)
  have alignA := NestedCompatibilityGeometry.alignA q cfg C T cert U k hchildA hcentA
  have alignB := NestedCompatibilityGeometry.alignB q cfg C T cert V l hchildB hcentB
  have pos2 : 0 < (cfg.firstPredecessor 2).1 := NestedCompatibilityGeometry.pos2 q cfg
  have pos3 := NestedCompatibilityGeometry.pos3 q cfg
  have odoQ2 : TileOdometer (cfg.firstPredecessor 2) (cert.Q 1 true) (k 1 true) :=
    PositiveCurvatureTileOdometerSupportTransport _ _ _ _ pos2 (hchildA 1 true)
      (cert.plus_occurrence 1 true).1 (alignA 1 true).1
  have odoS2 : TileOdometer (cfg.firstPredecessor 2) (cert.S 1 false) (l 1 false) :=
    PositiveCurvatureTileOdometerSupportTransport _ _ _ _ pos2 (hchildB 1 false)
      (cert.minus_occurrence 1 false).1 (alignB 1 false).1
  have odoS3 : TileOdometer (cfg.firstPredecessor 3) (cert.S 2 false) (l 2 false) :=
    PositiveCurvatureTileOdometerSupportTransport _ _ _ _ pos3 (hchildB 2 false)
      (cert.minus_occurrence 2 false).1 (alignB 2 false).1
  have odoQ3 : TileOdometer (cfg.firstPredecessor 3) (cert.Q 2 true) (k 2 true) :=
    PositiveCurvatureTileOdometerSupportTransport _ _ _ _ pos3 (hchildA 2 true)
      (cert.plus_occurrence 2 true).1 (alignA 2 true).1
  let I : GaussianInt := ⟨0, 1⟩
  let w : GaussianInt := BandVectors.1 (q 3) (q 2)
  let v21 : GaussianInt := BandVectors.1 (q 2) (q 1)
  let v13 : GaussianInt := BandVectors.1 (q 1) (q 3)
  let alpha : GaussianInt := BandVectors.2 (q 3) (q 2)
  let a21 : GaussianInt := BandVectors.2 (q 2) (q 1)
  let spatial (z : GaussianInt) : Real × Real :=
    (1 / 2 : Real) • (GaussianRealPoint z -
      (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
  have hcycV := (VectorRecursionLaws q cfg.proper.1).1
  have hcycA := (VectorRecursionLaws q cfg.proper.1).2.1
  have hpredV := (VectorRecursionLaws cfg.firstPredecessor cfg.firstProper.1).1
  have hpredA := (VectorRecursionLaws cfg.firstPredecessor cfg.firstProper.1).2.1
  have hrot := VectorRecursionLaws _
    (SemiProperQuadruple.rotate cfg.firstProper.1)
  have spatialIdentity := NestedCompatibilityGeometry.spatialIdentity q cfg
      (NestedCompatibilityGeometry.hV13 q cfg hcycV (NestedCompatibilityGeometry.hX q cfg hcycV
      hpredV (by
        simpa [v21, w, I, cfg.firstChild, cfg.firstParentTwo,
          cfg.firstParentThree] using hrot.2.2.1)))
  have slopeIdentity := NestedCompatibilityGeometry.slopeIdentity q cfg
      (NestedCompatibilityGeometry.hA13 q cfg hcycA (NestedCompatibilityGeometry.hXalpha q cfg
      hcycA hpredA (by
        simpa [a21, alpha, I, cfg.firstChild, cfg.firstParentTwo,
          cfg.firstParentThree] using hrot.2.2.2.1)))
  have secondFlip := (VectorRecursionLaws cfg.secondPredecessor
    cfg.secondProper.1).2.2.2.2 cfg.secondProper 0
  simp only [show (0 : Fin 3).succ = (1 : Fin 4) from rfl,
    cfg.secondChild, cfg.secondParentOne] at secondFlip
  have hI2 : I * I = -1 := by
    ext <;> norm_num [I]
  have hIprod (z : GaussianInt) : I * z = ⟨-z.im, z.re⟩ := by
    ext <;> simp [I]
  have hcenterA : TileCentroid A - TileCentroid T = spatial w := by
    simpa [A, spatial, w, Fin.add_def] using (cert.outer_occurrence 0 true).2.2
  have hcenterP : TileCentroid (cert.P 1 true) - TileCentroid T = spatial v13 := by
    simpa [spatial, v13, Fin.add_def] using (cert.outer_occurrence 1 true).2.2
  have hcenterQT := NestedCompatibilityGeometry.hcenterQT q cfg C T cert hcenterA
      (NestedCompatibilityGeometry.hcenterQ q cfg C T cert)
  have hcenterDelta : TileCentroid (cert.P 1 true) -
      TileCentroid (cert.Q 1 true) = GaussianRealPoint (I * w) :=
          NestedCompatibilityGeometry.hcenterDelta q cfg C T cert spatialIdentity hcenterP hcenterQT
  have childSlope := NestedCompatibilityGeometry.childSlope q cfg h s0 hp k hslopeA pos2
  rw [← secondFlip.1] at hcenterDelta
  have posRoot2 : 0 < (q 2).1 := by have := cfg.secondLarge; omega
  let C2 : BandCircle :=
    ⟨⟨q 2, Or.inl posRoot2, q, cfg.proper.1, 2, rfl⟩, posRoot2⟩
  have rawCompatLift := NestedCompatibilityGeometry.rawCompatLift
  have hq1pos := NestedCompatibilityGeometry.hq1pos q cfg hroot
  have hdomA : (h 0 true).domain = FootprintVertices A :=
    PositiveCurvatureTileOdometerDomain (q 1) A (h 0 true) hq1pos
      (by simpa [A] using ho 0 true)
  have hdomC : (h 1 true).domain = FootprintVertices (cert.P 1 true) :=
    PositiveCurvatureTileOdometerDomain (q 2) (cert.P 1 true) (h 1 true)
      (by simpa [cfg.firstParentTwo] using pos2)
      (by simpa using ho 1 true)
  have hdomBParent : (h 0 false).domain = FootprintVertices B :=
    PositiveCurvatureTileOdometerDomain (q 1) B (h 0 false) hq1pos
      (by simpa [B] using ho 0 false)
  have hdomQ : (k 1 true).domain = FootprintVertices (cert.Q 1 true) :=
    PositiveCurvatureTileOdometerDomain (cfg.firstPredecessor 2)
      (cert.Q 1 true) (k 1 true) pos2 odoQ2
  have hrawAC := (BandOrderedGeneralRawSupport q cfg C T cert).1
  have hrawAB := (BandOrderedGeneralRawSupport q cfg C T cert).2
  have finishAC (hcompat : OdometerCompatibility (k 1 true) (h 1 true)) :
      OdometerCompatibility (h 0 true) (h 1 true) :=
    rawCompatLift (h 0 true) (h 1 true) (k 1 true) A (cert.P 1 true)
      (cert.Q 1 true) hdomA hdomC hdomQ
      (fun x hx => hvalueA 1 true x hx) hrawAC hcompat
  have compatAC : OdometerCompatibility (h 0 true) (h 1 true) :=
    finishAC ((RightSubtileOdometerCompatibility.1 C2 (cert.Q 1 true)
      (cert.P 1 true) (k 1 true) (h 1 true)) (NestedCompatibilityGeometry.adjQ2 q cfg C T cert h
          s0 ho k odoQ2 hcenterDelta (NestedCompatibilityGeometry.rootSlope q h s0 hp) childSlope
          (NestedCompatibilityGeometry.slopeDelta q cfg s0 slopeIdentity secondFlip) posRoot2))
  have hcenterB : TileCentroid B - TileCentroid T = -spatial w := by
    simpa [B, spatial, w, Fin.add_def] using (cert.outer_occurrence 0 false).2.2
  have hcenterS := NestedCompatibilityGeometry.hcenterS q cfg C T cert
  have hcenterPminus := NestedCompatibilityGeometry.hcenterPminus q cfg C T cert
  have childSlopeMinus := NestedCompatibilityGeometry.childSlopeMinus q cfg h s0 hp l hslopeB pos2
  have compatBDNested : OdometerCompatibility (l 1 false) (h 1 false) :=
    (RightSubtileOdometerCompatibility.1 C2 (cert.S 1 false)
      (cert.P 1 false) (l 1 false) (h 1 false)) (NestedCompatibilityGeometry.adjS2 q cfg C T cert
          h s0 ho l odoS2 posRoot2 (NestedCompatibilityGeometry.hcenterDeltaMinus q cfg C T cert
          spatialIdentity secondFlip hcenterB hcenterS hcenterPminus) childSlopeMinus
          (NestedCompatibilityGeometry.rootSlopeMinus q h s0 hp)
          (NestedCompatibilityGeometry.slopeDeltaMinus q cfg s0 secondFlip
          (NestedCompatibilityGeometry.slopeIdentityMinus q cfg slopeIdentity)))
  have posRoot3 := NestedCompatibilityGeometry.posRoot3 q cfg
  let C3 : BandCircle :=
    ⟨⟨q 3, Or.inl posRoot3, q, cfg.proper.1, 3, rfl⟩, posRoot3⟩
  have compatCross1 : OdometerCompatibility (k 1 true) (l 2 false) :=
    (RightSubtileOdometerCompatibility.2 C2 C3
      (cert.Q 1 true) (cert.S 2 false) (k 1 true) (l 2 false))
          (NestedCompatibilityGeometry.adjCross1 q cfg C T cert s0 k l odoQ2 odoS3 secondFlip
          childSlope posRoot2 (NestedCompatibilityGeometry.childSlopeS3 q cfg h s0 hp l hslopeB
          pos3) (NestedCompatibilityGeometry.crossSpatial q cfg C T cert hpredV hcenterQT
          (NestedCompatibilityGeometry.hcenterS3 q cfg C T cert V hcentB alignB hcenterB))
          (NestedCompatibilityGeometry.crossSlope q cfg s0 hpredA secondFlip) posRoot3)
  have compatCross2 : OdometerCompatibility (l 1 false) (k 2 true) :=
    (RightSubtileOdometerCompatibility.2 C2 C3
      (cert.S 1 false) (cert.Q 2 true) (l 1 false) (k 2 true))
          (NestedCompatibilityGeometry.adjCross2 q cfg C T cert s0 k l odoS2 odoQ3 secondFlip
          posRoot2 childSlopeMinus posRoot3 (NestedCompatibilityGeometry.childSlopeQ3 q cfg h s0
          hp k hslopeA pos3) (NestedCompatibilityGeometry.crossSpatial2 q cfg C T cert hpredV
          (NestedCompatibilityGeometry.hI3 (NestedCompatibilityGeometry.hI2pow hI2))
          (NestedCompatibilityGeometry.hnegII hI2) hIprod hcenterB hcenterS
          (NestedCompatibilityGeometry.hcenterQ3 q cfg C T cert U hcentA alignA hcenterA))
          (NestedCompatibilityGeometry.crossSlope2 q cfg s0 hpredA secondFlip
          (NestedCompatibilityGeometry.hIneg hI2) (NestedCompatibilityGeometry.hI3neg hI2) hIprod))
  have bandPositiveNonempty := (fun D V hV hD => BandPrototileNonempty.positive D V hD hV)
  have qSCells := NestedCompatibilityGeometry.qSCells q cfg C T cert
  have qSAnchor := NestedCompatibilityGeometry.qSAnchor q cfg C T cert
  have uvCells := NestedCompatibilityGeometry.uvCells q cfg C T cert U V alignA alignB qSCells
  have uvAnchor := NestedCompatibilityGeometry.uvAnchor q cfg C T cert U V alignA alignB qSCells
      qSAnchor
  have uvObservable := ProtoTileObservableExtensionality
    (U 0 false) (V 0 true) uvCells uvAnchor
  exact (NestedCompatibilityConclusion.nestedCompatibilityConclusion q cfg C T cert h ho hroot U
      k hbandA hdomA hvalueA V l hvalueB alignA alignB pos2 pos3 odoQ2 odoS2 odoS3 odoQ3 hcenterA
      hcenterP hcenterQT rawCompatLift hq1pos hdomBParent hdomQ hrawAC hrawAB compatAC hcenterB
      hcenterS hcenterPminus compatBDNested compatCross1 compatCross2
      (NestedCompatibilityGeometry.propagateConstant) bandPositiveNonempty qSCells qSAnchor
      (NestedPrecursorConstant.precursorConstant q cfg h s0 hp U k hchildA hslopeA V l hchildB
      hslopeB bandPositiveNonempty uvCells uvAnchor uvObservable
      (NestedCompatibilityGeometry.zeroOdometerLine
      (NestedCompatibilityGeometry.properLarge))))


end ApollonianSuperharmonic

end
