/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5658T1FivePointDomainCoverSymmetryCovariance
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSubtileNormalizationCertificate
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayout
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSubtileCanonicalRows
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryInversePhaseCancellation
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryPartialOdometerActionFormulas
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryProperCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryReversesOrientation
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileOdometerCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryVectorAction
public import LeanPool.ApollonianSuperharmonic.BandPrototile
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.BandRegimeClassification
public import LeanPool.ApollonianSuperharmonic.BandSubtileOccurrence
public import LeanPool.ApollonianSuperharmonic.BandTileSimultaneousInduction
public import LeanPool.ApollonianSuperharmonic.ClosedSquareRealization
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.ProperBandQuadruple
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import LeanPool.ApollonianSuperharmonic.SemiProperQuadruple
public import LeanPool.ApollonianSuperharmonic.SubtileLatticeAdjacentPackingSymmetryTransport
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile
public import LeanPool.ApollonianSuperharmonic.TileOdometerReindexedDecomposition
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: BandOrderedGeneralSubtileNormalizationCertificateExists]

/-!
# BandOrderedGeneralSubtileNormalizationCertificateExists

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace SubtileNormalizationGeometry

private theorem hqrotSemi :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (∀ (q' : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry), (
        let q' := BandPackingSymmetryQuadrupleAction g ![q (0 : Fin (4 : ℕ)), q r.succ, q (r + (1
            : Fin (3 : ℕ))).succ, q (r + (2 : Fin (3 : ℕ))).succ]; Xor (∃ (P :
            FordFareyParameter), (1 : ℕ) < P.q ∧ q' = FordRecursiveQuadruple P) (Xor (∃ (K :
            DiamondParameter), (1 : ℕ) < K.1 ∧ q' = DiamondRecursiveQuadruple K) (Nonempty
            (BandOrderedGeneralConfiguration q')))) → (
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        SemiProperQuadruple qrot)) ) := by
  classical
  intro q hq q' r g hregime qrot
  fin_cases r
  · convert hq.1 using 1; funext j; fin_cases j <;> simp [qrot]
  · convert SemiProperQuadruple.rotate hq.1 using 1;
      funext j; fin_cases j <;> simp [qrot]
  · convert SemiProperQuadruple.rotate
        (SemiProperQuadruple.rotate hq.1) using 1;
      funext j; fin_cases j <;> simp [qrot]

private theorem hqrot :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (∀ (q' : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry), (
        let q' := BandPackingSymmetryQuadrupleAction g ![q (0 : Fin (4 : ℕ)), q r.succ, q (r + (1
            : Fin (3 : ℕ))).succ, q (r + (2 : Fin (3 : ℕ))).succ]; Xor (∃ (P :
            FordFareyParameter), (1 : ℕ) < P.q ∧ q' = FordRecursiveQuadruple P) (Xor (∃ (K :
            DiamondParameter), (1 : ℕ) < K.1 ∧ q' = DiamondRecursiveQuadruple K) (Nonempty
            (BandOrderedGeneralConfiguration q')))) → (
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        (SemiProperQuadruple qrot) → (ProperBandQuadruple qrot))) ) := by
  classical
  intro q hq q' r g hregime qrot hqrotSemi
  refine ⟨hqrotSemi, ?_⟩
  intro j
  fin_cases r <;> fin_cases j <;> simp [qrot]
  · simpa using hq.2 (0 : Fin 3)
  · simpa using hq.2 (1 : Fin 3)
  · simpa using hq.2 (2 : Fin 3)
  · simpa using hq.2 (1 : Fin 3)
  · simpa using hq.2 (2 : Fin 3)
  · simpa using hq.2 (0 : Fin 3)
  · simpa using hq.2 (2 : Fin 3)
  · simpa using hq.2 (0 : Fin 3)
  · simpa using hq.2 (1 : Fin 3)

private theorem hgeneral :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), (¬((∃ (g : BandPackingSymmetry)
            (P : FordFareyParameter), BandPackingSymmetryCircleAction g (FordCircleCoordinate P.p
            P.q) = C₀.1.1) ∨ ∃ (g : BandPackingSymmetry) (K : DiamondParameter),
            BandPackingSymmetryCircleAction g (DiamondRecursiveQuadruple K (0 : Fin (4 : ℕ))) =
            C₀.1.1)) → ((q (0 : Fin (4 : ℕ)) = C₀.1.1) → (∀ (q' : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry), (
        let q' := BandPackingSymmetryQuadrupleAction g ![q (0 : Fin (4 : ℕ)), q r.succ, q (r + (1
            : Fin (3 : ℕ))).succ, q (r + (2 : Fin (3 : ℕ))).succ]; Xor (∃ (P :
            FordFareyParameter), (1 : ℕ) < P.q ∧ q' = FordRecursiveQuadruple P) (Xor (∃ (K :
            DiamondParameter), (1 : ℕ) < K.1 ∧ q' = DiamondRecursiveQuadruple K) (Nonempty
            (BandOrderedGeneralConfiguration q')))) → (
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let qbar := BandPackingSymmetryQuadrupleAction g qrot
        Nonempty (BandOrderedGeneralConfiguration qbar)))) ) := by
  classical
  intro C₀ q horbit hq₀ q' r g hregime qrot qbar
  dsimp [qbar, qrot] at hregime
  rcases hregime with hford | hrest
  · exfalso
    rcases hford.1 with ⟨P, _, heq⟩
    obtain ⟨ginv, hinv, _, _, _, _, _, _, _, _, _⟩ :=
      BandPackingSymmetryInversePhaseCancellation.2 g
    apply horbit
    left
    refine ⟨ginv, P, ?_⟩
    calc
      BandPackingSymmetryCircleAction ginv (FordCircleCoordinate P.p P.q) =
          BandPackingSymmetryCircleAction ginv
            (BandPackingSymmetryCircleAction g C₀.1.1) := by
              have h0 := congrFun heq 0
              simpa [BandPackingSymmetryQuadrupleAction,
                FordRecursiveQuadruple, hq₀] using congrArg
                  (BandPackingSymmetryCircleAction ginv) h0.symm
      _ = C₀.1.1 := hinv _
  · rcases hrest.1 with hdiamond | hgeneral
    · exfalso
      rcases hdiamond.1 with ⟨K, _, heq⟩
      obtain ⟨ginv, hinv, _, _, _, _, _, _, _, _, _⟩ :=
        BandPackingSymmetryInversePhaseCancellation.2 g
      apply horbit
      right
      refine ⟨ginv, K, ?_⟩
      calc
        BandPackingSymmetryCircleAction ginv
            (DiamondRecursiveQuadruple K 0) =
            BandPackingSymmetryCircleAction ginv
              (BandPackingSymmetryCircleAction g C₀.1.1) := by
                have h0 := congrFun heq 0
                simpa [BandPackingSymmetryQuadrupleAction, hq₀] using congrArg
                  (BandPackingSymmetryCircleAction ginv) h0.symm
        _ = C₀.1.1 := hinv _
    · exact hgeneral.1

private theorem hO₀rot :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (T₀ : ProtoTile), ∀ (h₀ :
            PartialOdometer), (TileOdometer C₀.1.1 T₀ h₀) → (∀ (r : Fin (3 : ℕ)),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        (qrot 0 = C₀.1.1) → (TileOdometer (qrot 0) T₀ h₀)) ) := by
  classical
  intro C₀ q T₀ h₀ hO₀ r qrot hqrot₀
  rw [hqrot₀]
  exact hO₀

private theorem hOᵢrot :
    (by
      classical
      exact
        ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (Tᵢ :
            ProtoTile), ∀ (hᵢ : PartialOdometer), (q i.succ = Cᵢ.1.1) → ((TileOdometer Cᵢ.1.1 Tᵢ
            hᵢ) → (∀ (r : Fin (3 : ℕ)),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let irot : Fin 3 := i - r
        (qrot irot.succ = q i.succ) → (TileOdometer (qrot irot.succ) Tᵢ hᵢ))) ) := by
  classical
  intro Cᵢ q i Tᵢ hᵢ hqᵢ hOᵢ r qrot irot hrotParent
  rw [hrotParent, hqᵢ]
  exact hOᵢ

private theorem hcentroidRot :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (T₀ : ProtoTile), ∀
            (Tᵢ : ProtoTile), (TileCentroid Tᵢ - TileCentroid T₀ = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * (BandVectors.1 (q
            i.succ) (q (0 : Fin (4 : ℕ))) + BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ)))) →
            (∀ (r : Fin (3 : ℕ)),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let irot : Fin 3 := i - r
        (qrot irot.succ = q i.succ) → (TileCentroid Tᵢ - TileCentroid T₀ = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ s.val * (BandVectors.1 (qrot irot.succ)
            (qrot 0) + BandVectors.1 (qrot 0) (qrot irot.succ))))) ) := by
  classical
  intro q i s T₀ Tᵢ hcentroid r qrot irot hrotParent
  simpa [qrot, hrotParent] using hcentroid

private theorem hslopexRot :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (p₀ : ℝ × ℝ), ∀ (pᵢ :
            ℝ × ℝ), (pᵢ.1 - p₀.1 = ((1 / 2 : ℝ) • GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) ^ (↑s : ℕ) * (BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))) +
            BandVectors.2 (q (0 : Fin (4 : ℕ))) (q i.succ)))).1) → (∀ (r : Fin (3 : ℕ)),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let irot : Fin 3 := i - r
        (qrot irot.succ = q i.succ) → (pᵢ.1 - p₀.1 = ((1 / 2 : ℝ) • GaussianRealPoint ((-⟨0, 1⟩ :
            GaussianInt) ^ s.val * (BandVectors.2 (qrot irot.succ) (qrot 0) + BandVectors.2 (qrot
            0) (qrot irot.succ)))).1)) ) := by
  classical
  intro q i s p₀ pᵢ hslopex r qrot irot hrotParent
  simpa [qrot, hrotParent] using hslopex

private theorem hslopeyRot :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (p₀ : ℝ × ℝ), ∀ (pᵢ :
            ℝ × ℝ), (pᵢ.2 - p₀.2 = ((1 / 2 : ℝ) • GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) ^ (↑s : ℕ) * (BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))) +
            BandVectors.2 (q (0 : Fin (4 : ℕ))) (q i.succ)))).2) → (∀ (r : Fin (3 : ℕ)),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let irot : Fin 3 := i - r
        (qrot irot.succ = q i.succ) → (pᵢ.2 - p₀.2 = ((1 / 2 : ℝ) • GaussianRealPoint ((-⟨0, 1⟩ :
            GaussianInt) ^ s.val * (BandVectors.2 (qrot irot.succ) (qrot 0) + BandVectors.2 (qrot
            0) (qrot irot.succ)))).2)) ) := by
  classical
  intro q i s p₀ pᵢ hslopey r qrot irot hrotParent
  simpa [qrot, hrotParent] using hslopey

private theorem hqbarᵢ :
    (by
      classical
      exact
        ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), (q i.succ =
            Cᵢ.1.1) → (∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let irot : Fin 3 := i - r
        (qrot irot.succ = q i.succ) → (
        let qbar := BandPackingSymmetryQuadrupleAction g qrot
        let reverse := BandPackingSymmetryReversesOrientation g
        let ibar : Fin 3 := if reverse then -irot else irot
        qbar ibar.succ = BandPackingSymmetryCircleAction g Cᵢ.1.1)) ) := by
  classical
  intro Cᵢ q i hqᵢ r g qrot irot hrotParent qbar reverse ibar
  have hact := congrArg (BandPackingSymmetryCircleAction g)
    (hrotParent.trans hqᵢ)
  generalize hi : irot = k at hact ⊢
  fin_cases k <;>
    cases hrev : BandPackingSymmetryReversesOrientation g <;>
    simpa [qbar, ibar, reverse, BandPackingSymmetryQuadrupleAction,
      hi, hrev, Fin.neg_def, Fin.add_def] using hact

private theorem hqbarᵢPos :
    (by
      classical
      exact
        (BandCircle) → (∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), (Fin 4) → (∀ (r : Fin
            (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let irot : Fin 3 := i - r
        let qbar := BandPackingSymmetryQuadrupleAction g qrot
        (ProperBandQuadruple qbar) → ((BandOrderedGeneralConfiguration qbar) → ((Bool) → ((Fin (4
            : ℕ)) → (
        let reverse := BandPackingSymmetryReversesOrientation g
        let ibar : Fin 3 := if reverse then -irot else irot
        0 < (qbar ibar.succ).1)))))) ) := by
  classical
  intro Cᵢ q i s r g qrot irot qbar hqbar cfg negative sbar reverse ibar
  have hn := (ProperBandCurvatureStructure qbar hqbar).2.1 ibar
  have hnl := cfg.noLine ibar.succ
  omega

private theorem hx₀bar :
    (by
      classical
      exact
        ∀ (h₀ : PartialOdometer), (PartialOdometer) → (∀ (x : GaussianInt), (x ∈ h₀.domain) → (∀
            (g : BandPackingSymmetry),
        let h₀bar := BandPackingSymmetryPartialOdometerAction g h₀
        let xbar := BandPackingSymmetryVectorAction g x
        xbar ∈ h₀bar.domain)) ) := by
  classical
  intro h₀ hᵢ x hx₀ g h₀bar xbar
  have hdom := (BandPackingSymmetryPartialOdometerActionFormulas g h₀ hᵢ).1
  have hxset : BandPackingSymmetryVectorAction g x ∈
      ((BandPackingSymmetryPartialOdometerAction g h₀).domain :
        Set GaussianInt) := by
    rw [hdom]
    exact ⟨x, hx₀, rfl⟩
  exact hxset

private theorem hxᵢbar :
    (by
      classical
      exact
        (PartialOdometer) → (∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), (x ∈ hᵢ.domain) → (∀
            (g : BandPackingSymmetry),
        let hᵢbar := BandPackingSymmetryPartialOdometerAction g hᵢ
        let xbar := BandPackingSymmetryVectorAction g x
        xbar ∈ hᵢbar.domain)) ) := by
  classical
  intro h₀ hᵢ x hxᵢ g hᵢbar xbar
  have hdom := (BandPackingSymmetryPartialOdometerActionFormulas g hᵢ h₀).1
  have hxset : BandPackingSymmetryVectorAction g x ∈
      ((BandPackingSymmetryPartialOdometerAction g hᵢ).domain :
        Set GaussianInt) := by
    rw [hdom]
    exact ⟨x, hxᵢ, rfl⟩
  exact hxset

private theorem hadjbar :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile),
            ∀ (h₀ : PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (r : Fin (3 : ℕ)), ∀ (g :
            BandPackingSymmetry),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let irot : Fin 3 := i - r
        let qbar := BandPackingSymmetryQuadrupleAction g qrot
        ∀ (hqbar : ProperBandQuadruple qbar), ∀ (p₀bar : ℝ × ℝ), ∀ (pᵢbar : ℝ × ℝ), ∀ (sbar : Fin
            (4 : ℕ)), (TileOdometer (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryTileAction g T₀) (BandPackingSymmetryPartialOdometerAction g h₀))
            → ((TileOdometer (BandPackingSymmetryQuadrupleAction g qrot ((fun (j : Fin (3 : ℕ))
            => if BandPackingSymmetryReversesOrientation g = true then -j else j) irot).succ)
            (BandPackingSymmetryTileAction g Tᵢ) (BandPackingSymmetryPartialOdometerAction g hᵢ))
            → ((PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction g h₀) = some
            p₀bar) → ((PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction g hᵢ) =
            some pᵢbar) → ((TileCentroid (BandPackingSymmetryTileAction g Tᵢ) - TileCentroid
            (BandPackingSymmetryTileAction g T₀) = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt) ^ (↑sbar : ℕ) * (BandVectors.1
            (BandPackingSymmetryQuadrupleAction g qrot ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) irot).succ)
            (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin (4 : ℕ))) + BandVectors.1
            (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction g qrot ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) irot).succ)))) →
            ((pᵢbar.1 - p₀bar.1 = ((1 / 2 : ℝ) • GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) ^ (↑sbar : ℕ) * (BandVectors.2 (BandPackingSymmetryQuadrupleAction g
            qrot ((fun (j : Fin (3 : ℕ)) => if BandPackingSymmetryReversesOrientation g = true
            then -j else j) irot).succ) (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin (4 :
            ℕ))) + BandVectors.2 (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction g qrot ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) irot).succ)))).1) →
            ((pᵢbar.2 - p₀bar.2 = ((1 / 2 : ℝ) • GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) ^ (↑sbar : ℕ) * (BandVectors.2 (BandPackingSymmetryQuadrupleAction g
            qrot ((fun (j : Fin (3 : ℕ)) => if BandPackingSymmetryReversesOrientation g = true
            then -j else j) irot).succ) (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin (4 :
            ℕ))) + BandVectors.2 (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction g qrot ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) irot).succ)))).2) → (
        let reverse := BandPackingSymmetryReversesOrientation g
        let ibar : Fin 3 := if reverse then -irot else irot
        let T₀bar := BandPackingSymmetryTileAction g T₀
        let Tᵢbar := BandPackingSymmetryTileAction g Tᵢ
        let h₀bar := BandPackingSymmetryPartialOdometerAction g h₀
        let hᵢbar := BandPackingSymmetryPartialOdometerAction g hᵢ
        ∀ (hqbar₀Pos : 0 < (qbar 0).1), ∀ (hqbarᵢPos : 0 < (qbar ibar.succ).1),
        let C₀bar : BandCircle :=
          ⟨⟨qbar 0, ⟨Or.inl hqbar₀Pos, ⟨qbar, hqbar.1, ⟨0, rfl⟩⟩⟩⟩, hqbar₀Pos⟩
        let Cᵢbar : BandCircle :=
          ⟨⟨qbar ibar.succ,
            ⟨Or.inl hqbarᵢPos, ⟨qbar, hqbar.1, ⟨ibar.succ, rfl⟩⟩⟩⟩,
            hqbarᵢPos⟩
        SubtileLatticeAdjacent C₀bar Cᵢbar T₀bar Tᵢbar h₀bar hᵢbar))))))) ) := by
  classical
  intro q i T₀ Tᵢ h₀ hᵢ r g qrot irot qbar hqbar p₀bar pᵢbar sbar hO₀bar hOᵢbar hp₀bar hpᵢbar
      hcentroidBar hslopexBar hslopeyBar reverse ibar T₀bar Tᵢbar h₀bar hᵢbar hqbar₀Pos hqbarᵢPos
      C₀bar Cᵢbar
  refine ⟨hO₀bar, hOᵢbar, p₀bar, pᵢbar, hp₀bar, hpᵢbar,
    qbar, ibar, sbar, hqbar, rfl, rfl, ?_, ?_, ?_⟩
  · simpa [qbar, reverse, ibar] using hcentroidBar
  · simpa [qbar, reverse, ibar] using hslopexBar
  · simpa [qbar, reverse, ibar] using hslopeyBar

private theorem hsmallT1 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let qbar := BandPackingSymmetryQuadrupleAction g qrot
        ∀ (q' : Fin 4 → CircleCoordinates), ∀ (T' : ProtoTile), ∀ (S' : Fin 3 → Bool →
            ProtoTile), ProperBandQuadruple q' → BandPrototile (q' 0) T' → (∀ i, ∀ s,
            BandSubtileOccurrence q' T' i s (S' i s)) → (∀ z, z ∈ T'.cells ↔ ∃ i s, z ∈ (S' i
            s).cells) → Int.toNat (q' 0).1 < Int.toNat (qbar 0).1 → LatticeTile T' ∧ TileArea T'
            = Int.toNat (q' 0).1 ∧ ∀ i, ∀ s, LatticeTile (TileCellComplement T' (S' i s)) ∧
            TileTouching (TileCellComplement T' (S' i s)) (S' i s) ) := by
  classical
  intro q r g qrot qbar q' T' S' hq' hT' hocc hcells _
  have hI := BandTileSimultaneousInduction q' hq' T' hT'
  exact ⟨hI.1, hI.2.1, hI.2.2.1 S' hocc hcells⟩

private theorem hsmallT2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let qbar := BandPackingSymmetryQuadrupleAction g qrot
        ∀ (D : CircleCoordinates), ∀ (U : ProtoTile), BandPrototile D U → Int.toNat D.1 <
            Int.toNat (qbar 0).1 → QuarterTurnSymmetric U ) := by
  classical
  intro q r g qrot qbar D U hU _
  cases hU with
  | line w z hw =>
      intro p
      simp [TileRealization, TileCentroid]
  | unit z a anchor =>
      intro p
      have hc : TileCentroid (⟨{a}, anchor⟩ : ProtoTile) =
          (((a.re : Int) : Real) + (1 / 2 : Real),
            ((a.im : Int) : Real) + (1 / 2 : Real)) := by
        simp [TileCentroid]
      rw [hc]
      rcases p with ⟨px, py⟩
      simp only [TileRealization, Finset.mem_singleton, Set.mem_iUnion]
      simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
      constructor
      · rintro ⟨b, rfl, hlo, hhi⟩
        refine ⟨b, rfl, ?_, ?_⟩ <;> constructor <;>
          linarith [hlo.1, hlo.2, hhi.1, hhi.2]
      · rintro ⟨b, rfl, hlo, hhi⟩
        refine ⟨b, rfl, ?_, ?_⟩ <;> constructor <;>
          linarith [hlo.1, hlo.2, hhi.1, hhi.2]
  | @decompose q' hq' S' U' hS hcells hfoot hcent =>
      exact (BandTileSimultaneousInduction q' hq' U
        (.decompose hq' hS hcells hfoot hcent)).2.2.2.1

private theorem hsmallT4 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let qbar := BandPackingSymmetryQuadrupleAction g qrot
        ∀ (q' : Fin 4 → CircleCoordinates), ∀ (T' : ProtoTile), ∀ (U : ProtoTile),
            ProperBandQuadruple q' → BandPrototile (q' 0) T' → Int.toNat (q' 0).1 < Int.toNat
            (qbar 0).1 → 1 < (q' 0).1 → ∀ i : Fin 3, BandPrototile (q' i.succ) U → TileCentroid U
            - TileCentroid T' = (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (q' i.succ)
            (q' 0)) + GaussianRealPoint (BandVectors.1 (q' 0) (q' i.succ))) → TouchingTriple T'
            (TileTranslation T' (BandVectors.1 (q' i.succ) (q' 0))) U ) := by
  classical
  intro q r g qrot qbar q' T' U hq' hT' _ hlarge i hU hcentU
  exact (BandTileSimultaneousInduction q' hq' T' hT').2.2.2.2.2.1
    hlarge i U hU hcentU

private theorem hsmallT5 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let qbar := BandPackingSymmetryQuadrupleAction g qrot
        ∀ (q' : Fin 4 → CircleCoordinates), ∀ (T' : ProtoTile), ∀ (U : ProtoTile), ∀ (V :
            ProtoTile), ProperBandQuadruple q' → BandPrototile (q' 0) T' → Int.toNat (q' 0).1 <
            Int.toNat (qbar 0).1 → ∀ i : Fin 3, BandPrototile (q' i.succ) U → BandPrototile (q'
            ((i + 1).succ)) V → TileCentroid U - TileCentroid T' = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q' i.succ) (q' 0)) + GaussianRealPoint
            (BandVectors.1 (q' 0) (q' i.succ))) → TileCentroid V - TileCentroid T' = (1 / 2 :
            Real) • (GaussianRealPoint (BandVectors.1 (q' ((i + 1).succ)) (q' 0)) -
            GaussianRealPoint (BandVectors.1 (q' 0) (q' ((i + 1).succ)))) → TouchingTriple T' U V
            ) := by
  classical
  intro q r g qrot qbar q' T' U V hq' hT' _ i hU hV hcentU hcentV
  exact (BandTileSimultaneousInduction q' hq' T' hT').2.2.2.2.2.2.1
    i U V hU hV hcentU hcentV

private theorem hstarFootprint :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile),
            ∀ (h₀ : PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (r : Fin
            (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let irot : Fin 3 := i - r
        let qbar := BandPackingSymmetryQuadrupleAction g qrot
        (TileOdometer (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryTileAction g T₀) (BandPackingSymmetryPartialOdometerAction g h₀))
            → ((TileOdometer (BandPackingSymmetryQuadrupleAction g qrot ((fun (j : Fin (3 : ℕ))
            => if BandPackingSymmetryReversesOrientation g = true then -j else j) irot).succ)
            (BandPackingSymmetryTileAction g Tᵢ) (BandPackingSymmetryPartialOdometerAction g hᵢ))
            → (
        let reverse := BandPackingSymmetryReversesOrientation g
        let ibar : Fin 3 := if reverse then -irot else irot
        let T₀bar := BandPackingSymmetryTileAction g T₀
        let Tᵢbar := BandPackingSymmetryTileAction g Tᵢ
        let h₀bar := BandPackingSymmetryPartialOdometerAction g h₀
        let hᵢbar := BandPackingSymmetryPartialOdometerAction g hᵢ
        let xbar := BandPackingSymmetryVectorAction g x
        (0 < (qbar 0).1) → ((0 < (qbar ibar.succ).1) → ((∀ y, y = xbar ∨ y = xbar + 1 ∨ y = xbar
            - 1 ∨ y = xbar + ⟨0, 1⟩ ∨ y = xbar - ⟨0, 1⟩ → y ∈ h₀bar.domain ∨ y ∈ hᵢbar.domain) →
            (∀ y, y = xbar ∨ y = xbar + 1 ∨ y = xbar - 1 ∨ y = xbar + ⟨0, 1⟩ ∨ y = xbar - ⟨0, 1⟩
            → y ∈ FootprintVertices T₀bar ∨ y ∈ FootprintVertices Tᵢbar))))) ) := by
  classical
  intro q i T₀ Tᵢ h₀ hᵢ x r g qrot irot qbar hO₀bar hOᵢbar reverse ibar T₀bar Tᵢbar h₀bar hᵢbar
      xbar hqbar₀Pos hqbarᵢPos hstarBarDomain y hy
  have hs := hstarBarDomain y hy
  have hd₀ := PositiveCurvatureTileOdometerDomain (qbar 0) T₀bar h₀bar
    hqbar₀Pos hO₀bar
  have hdᵢ := PositiveCurvatureTileOdometerDomain (qbar ibar.succ)
    Tᵢbar hᵢbar hqbarᵢPos hOᵢbar
  rcases hs with hs | hs
  · left
    exact (Set.ext_iff.mp hd₀ y).mp hs
  · right
    exact (Set.ext_iff.mp hdᵢ y).mp hs

private theorem hpieceIndexCentral :
    (by
      classical
      exact
        let labelOf : Fin 3 → Bool → SixSubtileLabel := fun j e =>
          match j, e with
          | 0, true => .A | 0, false => .B
          | 1, true => .C | 1, false => .D
          | 2, true => .E | 2, false => .F
        let pieceIndex : Fin 3 → Bool → PeriodicSubtileIndex := fun j e =>
          ⟨labelOf j e, 0, 0⟩
        ∀ (j : Fin 3), ∀ (e : Bool), pieceIndex j e = ⟨.A, 0, 0⟩ ∨ pieceIndex j e = ⟨.B, 0, 0⟩ ∨
            pieceIndex j e = ⟨.C, 0, 0⟩ ∨ pieceIndex j e = ⟨.D, 0, 0⟩ ∨ pieceIndex j e = ⟨.E, 0,
            0⟩ ∨ pieceIndex j e = ⟨.F, 0, 0⟩ ) := by
  classical
  intro labelOf pieceIndex j e
  fin_cases j <;> cases e <;> simp [pieceIndex, labelOf]

private theorem translation_zero :
    (by
      classical
      exact
        ∀ (U : ProtoTile), TileTranslation U 0 = U ) := by
  classical
  intro U
  cases U with
  | mk cells anchor =>
      have hc : cells.image (GaussianTranslation 0) = cells := by
        ext z
        simp [GaussianTranslation]
      simp [TileTranslation, hc, GaussianTranslation]

private theorem centralOccurrence :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T₀ : ProtoTile), ∀ (r : Fin (3 : ℕ)), ∀ (g :
            BandPackingSymmetry),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let qbar := BandPackingSymmetryQuadrupleAction g qrot
        ∀ (hqbar : ProperBandQuadruple qbar), ∀ (cfg : BandOrderedGeneralConfiguration qbar),
        let T₀bar := BandPackingSymmetryTileAction g T₀
        ∀ (hqbar₀Pos : 0 < (qbar 0).1),
        let C₀bar : BandCircle :=
          ⟨⟨qbar 0, ⟨Or.inl hqbar₀Pos, ⟨qbar, hqbar.1, ⟨0, rfl⟩⟩⟩⟩, hqbar₀Pos⟩
        ∀ (layout : BandOrderedGeneralLayoutCertificate qbar cfg C₀bar T₀bar),
        let labelOf : Fin 3 → Bool → SixSubtileLabel := fun j e =>
          match j, e with
          | 0, true => .A | 0, false => .B
          | 1, true => .C | 1, false => .D
          | 2, true => .E | 2, false => .F
        let pieceIndex : Fin 3 → Bool → PeriodicSubtileIndex := fun j e =>
          ⟨labelOf j e, 0, 0⟩
        (∀ (U : ProtoTile), TileTranslation U 0 = U) → (∀ (j : Fin 3), ∀ (e : Bool),
            SubtileOccurrenceInterpretation layout.P layout.u layout.v (pieceIndex j e) =
            layout.P j e) ) := by
  classical
  intro q T₀ r g qrot qbar hqbar cfg T₀bar hqbar₀Pos C₀bar layout labelOf pieceIndex
      translation_zero j e
  fin_cases j <;> cases e <;>
    simp [pieceIndex, labelOf, SubtileOccurrenceInterpretation,
      translation_zero]

private theorem centralData :
    (by
      classical
      exact
        (BandCircle) → (∀ (q : Fin 4 → CircleCoordinates), (Fin 3) → ((Fin 4) → (∀ (T₀ :
            ProtoTile), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let qbar := BandPackingSymmetryQuadrupleAction g qrot
        ∀ (hqbar : ProperBandQuadruple qbar), ∀ (cfg : BandOrderedGeneralConfiguration qbar),
            (Bool) → ((Fin (4 : ℕ)) → (
        let T₀bar := BandPackingSymmetryTileAction g T₀
        ∀ (hqbar₀Pos : 0 < (qbar 0).1),
        let C₀bar : BandCircle :=
          ⟨⟨qbar 0, ⟨Or.inl hqbar₀Pos, ⟨qbar, hqbar.1, ⟨0, rfl⟩⟩⟩⟩, hqbar₀Pos⟩
        ∀ (layout : BandOrderedGeneralLayoutCertificate qbar cfg C₀bar T₀bar), ∀ (pieces : Fin (3
            : ℕ) → Bool → ProtoTile), ∀ (functions : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i
                : Fin (3 : ℕ)), ∀ (s : Bool), TileOdometer (qbar i.succ) (pieces i s) (functions i
            s)) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid (pieces i s) - TileCentroid
            T₀bar = (if s = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint
            (BandVectors.1 (qbar (i + (2 : Fin (3 : ℕ))).succ) (qbar (i + (1 : Fin (3 :
            ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1 (qbar (i + (2 : Fin (3 : ℕ))).succ)
            (qbar (i + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (qbar (i +
            (2 : Fin (3 : ℕ))).succ) (qbar (i + (1 : Fin (3 : ℕ))).succ))).1))) → (
        let labelOf : Fin 3 → Bool → SixSubtileLabel := fun j e =>
          match j, e with
          | 0, true => .A | 0, false => .B
          | 1, true => .C | 1, false => .D
          | 2, true => .E | 2, false => .F
        let pieceIndex : Fin 3 → Bool → PeriodicSubtileIndex := fun j e =>
          ⟨labelOf j e, 0, 0⟩
        (∀ (j : Fin 3), ∀ (e : Bool), SubtileOccurrenceInterpretation layout.P layout.u layout.v
            (pieceIndex j e) = layout.P j e) → (∀ (j : Fin 3), ∀ (e : Bool), (pieces j e).cells =
            (SubtileOccurrenceInterpretation layout.P layout.u layout.v (pieceIndex j e)).cells ∧
            ((pieces j e).cells = ∅ → (pieces j e).anchor = (SubtileOccurrenceInterpretation
            layout.P layout.u layout.v (pieceIndex j e)).anchor) ∧ FootprintVertices (pieces j e)
            = FootprintVertices (SubtileOccurrenceInterpretation layout.P layout.u layout.v
            (pieceIndex j e)) ∧ ((functions j e).domain : Set GaussianInt) = FootprintVertices
            (SubtileOccurrenceInterpretation layout.P layout.u layout.v (pieceIndex j e)))))))))) )
            := by
  classical
  intro Cᵢ q i s T₀ r g qrot qbar hqbar cfg negative sbar T₀bar hqbar₀Pos C₀bar layout pieces
      functions hpieceOdometer hpieceCentroid labelOf pieceIndex centralOccurrence j e
  have hpieceBand : BandPrototile (qbar j.succ) (pieces j e) :=
    TileOdometerBandPrototile _ _ _ (hpieceOdometer j e)
  have hlayoutBand : BandPrototile (qbar j.succ)
      (SubtileOccurrenceInterpretation layout.P layout.u layout.v
        (pieceIndex j e)) := by
    rw [centralOccurrence]
    exact (layout.outer_occurrence j e).1
  have hcentroidAlign : TileCentroid (pieces j e) =
      TileCentroid (SubtileOccurrenceInterpretation layout.P layout.u
        layout.v (pieceIndex j e)) := by
    rw [centralOccurrence]
    have hp := hpieceCentroid j e
    have hl := (layout.outer_occurrence j e).2.2
    have hd : TileCentroid (pieces j e) - TileCentroid T₀bar =
        TileCentroid (layout.P j e) - TileCentroid T₀bar := hp.trans hl.symm
    apply Prod.ext
    · have h := congrArg Prod.fst hd
      simp only [Prod.fst_sub] at h
      linarith
    · have h := congrArg Prod.snd hd
      simp only [Prod.snd_sub] at h
      linarith
  have hu := BandPrototileCentroidUnique (qbar j.succ) (pieces j e)
    (SubtileOccurrenceInterpretation layout.P layout.u layout.v
      (pieceIndex j e)) hpieceBand hlayoutBand hcentroidAlign
  have ho := ProtoTileObservableExtensionality (pieces j e)
    (SubtileOccurrenceInterpretation layout.P layout.u layout.v
      (pieceIndex j e)) hu.1 hu.2
  have hparentPos : 0 < (qbar j.succ).1 := by
    have hn := (ProperBandCurvatureStructure qbar hqbar).2.1 j
    have hnl := cfg.noLine j.succ
    omega
  have hd := PositiveCurvatureTileOdometerDomain (qbar j.succ)
    (pieces j e) (functions j e) hparentPos (hpieceOdometer j e)
  exact ⟨hu.1, hu.2, ho.1, hd.trans ho.1⟩

private theorem hin1 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let qbar := BandPackingSymmetryQuadrupleAction g qrot
        let edge : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (qbar ((j + 2).succ)) (qbar ((j + 1).succ))
        let incoming : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (qbar j.succ) (qbar 0)
        let R : Fin 4 → CircleCoordinates := ![qbar 0, qbar 2, qbar 3, qbar 1]
        (SemiProperQuadruple R) → (incoming 1 = edge 2 - (⟨0, 1⟩ : GaussianInt) * edge 0) ) := by
  classical
  intro q r g qrot qbar edge incoming R hR
  simpa [incoming, edge, R] using (VectorRecursionLaws R hR).2.2.1

private theorem hin2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let qbar := BandPackingSymmetryQuadrupleAction g qrot
        let edge : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (qbar ((j + 2).succ)) (qbar ((j + 1).succ))
        let incoming : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (qbar j.succ) (qbar 0)
        let R : Fin 4 → CircleCoordinates := ![qbar 0, qbar 2, qbar 3, qbar 1]
        let S : Fin 4 → CircleCoordinates := ![R 0, R 2, R 3, R 1]
        (SemiProperQuadruple S) → (incoming 2 = edge 0 - (⟨0, 1⟩ : GaussianInt) * edge 1) ) := by
  classical
  intro q r g qrot qbar edge incoming R S hS
  simpa [incoming, edge, R, S] using (VectorRecursionLaws S hS).2.2.1

private theorem hexteriorIndex :
    (by
      classical
      exact
        ∀ (i : Fin 3), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let irot : Fin 3 := i - r
        ∀ (sbar : Fin (4 : ℕ)),
        let reverse := BandPackingSymmetryReversesOrientation g
        let ibar : Fin 3 := if reverse then -irot else irot
        let exteriorIndex : PeriodicSubtileIndex :=
          if ibar = 0 then
            if sbar = 0 then ⟨.A, 0, -1⟩
            else if sbar = 1 then ⟨.B, 1, 1⟩
            else if sbar = 2 then ⟨.B, 0, 1⟩
            else ⟨.A, -1, -1⟩
          else if ibar = 1 then
            if sbar = 0 then ⟨.C, 1, 1⟩
            else if sbar = 1 then ⟨.D, -1, 0⟩
            else if sbar = 2 then ⟨.D, -1, -1⟩
            else ⟨.C, 1, 0⟩
          else
            if sbar = 0 then ⟨.E, -1, 0⟩
            else if sbar = 1 then ⟨.F, 0, -1⟩
            else if sbar = 2 then ⟨.F, 1, 0⟩
            else ⟨.E, 0, 1⟩
        exteriorIndex = ⟨.A, -1, -1⟩ ∨ exteriorIndex = ⟨.A, 0, -1⟩ ∨ exteriorIndex = ⟨.C, 1, 0⟩ ∨
            exteriorIndex = ⟨.C, 1, 1⟩ ∨ exteriorIndex = ⟨.E, 0, 1⟩ ∨ exteriorIndex = ⟨.E, -1, 0⟩
            ∨ exteriorIndex = ⟨.B, 1, 1⟩ ∨ exteriorIndex = ⟨.B, 0, 1⟩ ∨ exteriorIndex = ⟨.D, -1,
            0⟩ ∨ exteriorIndex = ⟨.D, -1, -1⟩ ∨ exteriorIndex = ⟨.F, 0, -1⟩ ∨ exteriorIndex =
            ⟨.F, 1, 0⟩ ) := by
  classical
  intro i r g irot sbar reverse ibar exteriorIndex
  generalize hi : ibar = j at ⊢
  generalize hs : sbar = t at ⊢
  fin_cases j <;> fin_cases t <;> simp [exteriorIndex, hi, hs]

private theorem hexteriorCentroid :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (T₀ : ProtoTile), ∀ (r : Fin (3 :
            ℕ)), ∀ (g : BandPackingSymmetry),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let irot : Fin 3 := i - r
        let qbar := BandPackingSymmetryQuadrupleAction g qrot
        ∀ (hqbar : ProperBandQuadruple qbar), ∀ (cfg : BandOrderedGeneralConfiguration qbar), ∀
            (sbar : Fin (4 : ℕ)),
        let reverse := BandPackingSymmetryReversesOrientation g
        let ibar : Fin 3 := if reverse then -irot else irot
        let T₀bar := BandPackingSymmetryTileAction g T₀
        ∀ (hqbar₀Pos : 0 < (qbar 0).1),
        let C₀bar : BandCircle :=
          ⟨⟨qbar 0, ⟨Or.inl hqbar₀Pos, ⟨qbar, hqbar.1, ⟨0, rfl⟩⟩⟩⟩, hqbar₀Pos⟩
        ∀ (layout : BandOrderedGeneralLayoutCertificate qbar cfg C₀bar T₀bar),
        let incoming : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (qbar j.succ) (qbar 0)
        let outgoing : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (qbar 0) (qbar j.succ)
        let exteriorIndex : PeriodicSubtileIndex :=
          if ibar = 0 then
            if sbar = 0 then ⟨.A, 0, -1⟩
            else if sbar = 1 then ⟨.B, 1, 1⟩
            else if sbar = 2 then ⟨.B, 0, 1⟩
            else ⟨.A, -1, -1⟩
          else if ibar = 1 then
            if sbar = 0 then ⟨.C, 1, 1⟩
            else if sbar = 1 then ⟨.D, -1, 0⟩
            else if sbar = 2 then ⟨.D, -1, -1⟩
            else ⟨.C, 1, 0⟩
          else
            if sbar = 0 then ⟨.E, -1, 0⟩
            else if sbar = 1 then ⟨.F, 0, -1⟩
            else if sbar = 2 then ⟨.F, 1, 0⟩
            else ⟨.E, 0, 1⟩
        (
        let uIndex := if ibar = (0 : Fin (3 : ℕ)) then if sbar = (0 : Fin (4 : ℕ)) then
            (⟨SixSubtileLabel.A, (0 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else if sbar = (1 :
            Fin (4 : ℕ)) then (⟨SixSubtileLabel.B, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else
            if sbar = (2 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.B, (0 : ℤ), (1 : ℤ)⟩ :
            PeriodicSubtileIndex) else (⟨SixSubtileLabel.A, (-1 : ℤ), (-1 : ℤ)⟩ :
            PeriodicSubtileIndex) else if ibar = (1 : Fin (3 : ℕ)) then if sbar = (0 : Fin (4 :
            ℕ)) then (⟨SixSubtileLabel.C, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else if sbar
            = (1 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.D, (-1 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex) else if sbar = (2 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.D, (-1
            : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else (⟨SixSubtileLabel.C, (1 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex) else if sbar = (0 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.E, (-1
            : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) else if sbar = (1 : Fin (4 : ℕ)) then
            (⟨SixSubtileLabel.F, (0 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else if sbar = (2 :
            Fin (4 : ℕ)) then (⟨SixSubtileLabel.F, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) else
            (⟨SixSubtileLabel.E, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex);
        let vIndex := if ibar = (0 : Fin (3 : ℕ)) then if sbar = (0 : Fin (4 : ℕ)) then
            (⟨SixSubtileLabel.C, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) else if sbar = (1 :
            Fin (4 : ℕ)) then (⟨SixSubtileLabel.F, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) else
            if sbar = (2 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.D, (-1 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex) else (⟨SixSubtileLabel.E, (-1 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex) else if ibar = (1 : Fin (3 : ℕ)) then if sbar = (0 : Fin (4 :
            ℕ)) then (⟨SixSubtileLabel.E, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else if sbar
            = (1 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.B, (0 : ℤ), (1 : ℤ)⟩ :
            PeriodicSubtileIndex) else if sbar = (2 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.F, (0 :
            ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else (⟨SixSubtileLabel.A, (0 : ℤ), (-1 : ℤ)⟩ :
            PeriodicSubtileIndex) else if sbar = (0 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.A, (-1
            : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else if sbar = (1 : Fin (4 : ℕ)) then
            (⟨SixSubtileLabel.D, (-1 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else if sbar = (2 :
            Fin (4 : ℕ)) then (⟨SixSubtileLabel.B, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else
            (⟨SixSubtileLabel.C, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex);
        let U := SubtileOccurrenceInterpretation layout.P layout.u layout.v uIndex;
        let V := SubtileOccurrenceInterpretation layout.P layout.u layout.v vIndex; TileCentroid
            U - TileCentroid T₀bar = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ^ (↑sbar : ℕ) * (incoming ibar + outgoing ibar)) ∧ TileCentroid V -
            TileCentroid T₀bar = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ^ (↑sbar : ℕ) * if Even (↑sbar : ℕ) then incoming (ibar + (1 : Fin (3 :
            ℕ))) - outgoing (ibar + (1 : Fin (3 : ℕ))) else outgoing (ibar - (1 : Fin (3 : ℕ))) -
            incoming (ibar - (1 : Fin (3 : ℕ))))) → (TileCentroid
            (SubtileOccurrenceInterpretation layout.P layout.u layout.v exteriorIndex) -
            TileCentroid T₀bar = (1 / 2 : ℝ) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^
            sbar.val * (incoming ibar + outgoing ibar))) ) := by
  classical
  intro q i T₀ r g qrot irot qbar hqbar cfg sbar reverse ibar T₀bar hqbar₀Pos C₀bar layout
      incoming outgoing exteriorIndex hrows
  simpa [exteriorIndex] using hrows.1

private theorem hexteriorBand :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (T₀ : ProtoTile), ∀ (r : Fin (3 :
            ℕ)), ∀ (g : BandPackingSymmetry),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let irot : Fin 3 := i - r
        let qbar := BandPackingSymmetryQuadrupleAction g qrot
        ∀ (hqbar : ProperBandQuadruple qbar), ∀ (cfg : BandOrderedGeneralConfiguration qbar), ∀
            (sbar : Fin (4 : ℕ)),
        let reverse := BandPackingSymmetryReversesOrientation g
        let ibar : Fin 3 := if reverse then -irot else irot
        let T₀bar := BandPackingSymmetryTileAction g T₀
        ∀ (hqbar₀Pos : 0 < (qbar 0).1),
        let C₀bar : BandCircle :=
          ⟨⟨qbar 0, ⟨Or.inl hqbar₀Pos, ⟨qbar, hqbar.1, ⟨0, rfl⟩⟩⟩⟩, hqbar₀Pos⟩
        ∀ (layout : BandOrderedGeneralLayoutCertificate qbar cfg C₀bar T₀bar),
        let exteriorIndex : PeriodicSubtileIndex :=
          if ibar = 0 then
            if sbar = 0 then ⟨.A, 0, -1⟩
            else if sbar = 1 then ⟨.B, 1, 1⟩
            else if sbar = 2 then ⟨.B, 0, 1⟩
            else ⟨.A, -1, -1⟩
          else if ibar = 1 then
            if sbar = 0 then ⟨.C, 1, 1⟩
            else if sbar = 1 then ⟨.D, -1, 0⟩
            else if sbar = 2 then ⟨.D, -1, -1⟩
            else ⟨.C, 1, 0⟩
          else
            if sbar = 0 then ⟨.E, -1, 0⟩
            else if sbar = 1 then ⟨.F, 0, -1⟩
            else if sbar = 2 then ⟨.F, 1, 0⟩
            else ⟨.E, 0, 1⟩
        BandPrototile (qbar ibar.succ) (SubtileOccurrenceInterpretation layout.P layout.u
            layout.v exteriorIndex) ) := by
  classical
  intro q i T₀ r g qrot irot qbar hqbar cfg sbar reverse ibar T₀bar hqbar₀Pos C₀bar layout
      exteriorIndex
  generalize hi : ibar = j at ⊢
  generalize hs : sbar = t at ⊢
  fin_cases j <;> fin_cases t <;>
    simp? [exteriorIndex, hi, hs, SubtileOccurrenceInterpretation]
  all_goals first
    | exact BandPrototileTranslation _ _ _ (layout.outer_occurrence 0 false).1
    | exact BandPrototileTranslation _ _ _ (layout.outer_occurrence 0 true).1
    | exact BandPrototileTranslation _ _ _ (layout.outer_occurrence 1 false).1
    | exact BandPrototileTranslation _ _ _ (layout.outer_occurrence 1 true).1
    | exact BandPrototileTranslation _ _ _ (layout.outer_occurrence 2 false).1
    | exact BandPrototileTranslation _ _ _ (layout.outer_occurrence 2 true).1

private theorem hfixedCentroid :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile),
            ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let irot : Fin 3 := i - r
        let qbar := BandPackingSymmetryQuadrupleAction g qrot
        ∀ (hqbar : ProperBandQuadruple qbar), ∀ (cfg : BandOrderedGeneralConfiguration qbar), ∀
            (sbar : Fin (4 : ℕ)), (TileCentroid (BandPackingSymmetryTileAction g Tᵢ) -
            TileCentroid (BandPackingSymmetryTileAction g T₀) = (1 / 2 : ℝ) • GaussianRealPoint
            ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑sbar : ℕ) * (BandVectors.1
            (BandPackingSymmetryQuadrupleAction g qrot ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) irot).succ)
            (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin (4 : ℕ))) + BandVectors.1
            (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction g qrot ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) irot).succ)))) → (
        let reverse := BandPackingSymmetryReversesOrientation g
        let ibar : Fin 3 := if reverse then -irot else irot
        let T₀bar := BandPackingSymmetryTileAction g T₀
        let Tᵢbar := BandPackingSymmetryTileAction g Tᵢ
        ∀ (hqbar₀Pos : 0 < (qbar 0).1),
        let C₀bar : BandCircle :=
          ⟨⟨qbar 0, ⟨Or.inl hqbar₀Pos, ⟨qbar, hqbar.1, ⟨0, rfl⟩⟩⟩⟩, hqbar₀Pos⟩
        ∀ (layout : BandOrderedGeneralLayoutCertificate qbar cfg C₀bar T₀bar),
        let incoming : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (qbar j.succ) (qbar 0)
        let outgoing : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (qbar 0) (qbar j.succ)
        let exteriorIndex : PeriodicSubtileIndex :=
          if ibar = 0 then
            if sbar = 0 then ⟨.A, 0, -1⟩
            else if sbar = 1 then ⟨.B, 1, 1⟩
            else if sbar = 2 then ⟨.B, 0, 1⟩
            else ⟨.A, -1, -1⟩
          else if ibar = 1 then
            if sbar = 0 then ⟨.C, 1, 1⟩
            else if sbar = 1 then ⟨.D, -1, 0⟩
            else if sbar = 2 then ⟨.D, -1, -1⟩
            else ⟨.C, 1, 0⟩
          else
            if sbar = 0 then ⟨.E, -1, 0⟩
            else if sbar = 1 then ⟨.F, 0, -1⟩
            else if sbar = 2 then ⟨.F, 1, 0⟩
            else ⟨.E, 0, 1⟩
        (TileCentroid (SubtileOccurrenceInterpretation layout.P layout.u layout.v exteriorIndex)
            - TileCentroid T₀bar = (1 / 2 : ℝ) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^
            sbar.val * (incoming ibar + outgoing ibar))) → (TileCentroid
            (SubtileOccurrenceInterpretation layout.P layout.u layout.v exteriorIndex) =
            TileCentroid Tᵢbar)) ) := by
  classical
  intro q i T₀ Tᵢ r g qrot irot qbar hqbar cfg sbar hcentroidBar reverse ibar T₀bar Tᵢbar
      hqbar₀Pos C₀bar layout incoming outgoing exteriorIndex hexteriorCentroid
  have hd : TileCentroid (SubtileOccurrenceInterpretation layout.P layout.u
        layout.v exteriorIndex) - TileCentroid T₀bar =
      TileCentroid Tᵢbar - TileCentroid T₀bar := by
    calc
      _ = (1 / 2 : ℝ) • GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ sbar.val *
            (incoming ibar + outgoing ibar)) := hexteriorCentroid
      _ = _ := by
        simpa [qbar, reverse, ibar, incoming, outgoing] using
          hcentroidBar.symm
  apply Prod.ext
  · have h := congrArg Prod.fst hd
    simp only [Prod.fst_sub] at h
    linarith
  · have h := congrArg Prod.snd hd
    simp only [Prod.snd_sub] at h
    linarith

end SubtileNormalizationGeometry

namespace SubtileNormalizationConclusion

private theorem subtileNormalizationCertificate :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin
            3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ :
            PartialOdometer), ∀ (x : GaussianInt), (ProperBandQuadruple q) → ((q (0 : Fin (4 :
            ℕ)) = C₀.1.1) → ((q i.succ = Cᵢ.1.1) → (∀ (r : Fin (3 : ℕ)), ∀ (g :
            BandPackingSymmetry),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let irot : Fin 3 := i - r
        let qbar := BandPackingSymmetryQuadrupleAction g qrot
        ∀ (hqbar : ProperBandQuadruple qbar), ∀ (cfg : BandOrderedGeneralConfiguration qbar), ∀
            (p₀bar : ℝ × ℝ), ∀ (pᵢbar : ℝ × ℝ), ∀ (sbar : Fin (4 : ℕ)), (TileOdometer
            (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryTileAction g T₀) (BandPackingSymmetryPartialOdometerAction g h₀))
            → ((TileOdometer (BandPackingSymmetryQuadrupleAction g qrot ((fun (j : Fin (3 : ℕ))
            => if BandPackingSymmetryReversesOrientation g = true then -j else j) irot).succ)
            (BandPackingSymmetryTileAction g Tᵢ) (BandPackingSymmetryPartialOdometerAction g hᵢ))
            → ((PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction g h₀) = some
            p₀bar) → ((PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction g hᵢ) =
            some pᵢbar) → ((TileCentroid (BandPackingSymmetryTileAction g Tᵢ) - TileCentroid
            (BandPackingSymmetryTileAction g T₀) = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt) ^ (↑sbar : ℕ) * (BandVectors.1
            (BandPackingSymmetryQuadrupleAction g qrot ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) irot).succ)
            (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin (4 : ℕ))) + BandVectors.1
            (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction g qrot ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) irot).succ)))) →
            ((pᵢbar.1 - p₀bar.1 = ((1 / 2 : ℝ) • GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) ^ (↑sbar : ℕ) * (BandVectors.2 (BandPackingSymmetryQuadrupleAction g
            qrot ((fun (j : Fin (3 : ℕ)) => if BandPackingSymmetryReversesOrientation g = true
            then -j else j) irot).succ) (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin (4 :
            ℕ))) + BandVectors.2 (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction g qrot ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) irot).succ)))).1) →
            ((pᵢbar.2 - p₀bar.2 = ((1 / 2 : ℝ) • GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) ^ (↑sbar : ℕ) * (BandVectors.2 (BandPackingSymmetryQuadrupleAction g
            qrot ((fun (j : Fin (3 : ℕ)) => if BandPackingSymmetryReversesOrientation g = true
            then -j else j) irot).succ) (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin (4 :
            ℕ))) + BandVectors.2 (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction g qrot ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) irot).succ)))).2) → (
        let reverse := BandPackingSymmetryReversesOrientation g
        let ibar : Fin 3 := if reverse then -irot else irot
        let T₀bar := BandPackingSymmetryTileAction g T₀
        let Tᵢbar := BandPackingSymmetryTileAction g Tᵢ
        let h₀bar := BandPackingSymmetryPartialOdometerAction g h₀
        let hᵢbar := BandPackingSymmetryPartialOdometerAction g hᵢ
        let xbar := BandPackingSymmetryVectorAction g x
        (qbar ibar.succ = BandPackingSymmetryCircleAction g Cᵢ.1.1) → (∀ (hqbar₀Pos : 0 < (qbar
            0).1), ∀ (hqbarᵢPos : 0 < (qbar ibar.succ).1),
        let C₀bar : BandCircle :=
          ⟨⟨qbar 0, ⟨Or.inl hqbar₀Pos, ⟨qbar, hqbar.1, ⟨0, rfl⟩⟩⟩⟩, hqbar₀Pos⟩
        let Cᵢbar : BandCircle :=
          ⟨⟨qbar ibar.succ,
            ⟨Or.inl hqbarᵢPos, ⟨qbar, hqbar.1, ⟨ibar.succ, rfl⟩⟩⟩⟩,
            hqbarᵢPos⟩
        (xbar ∈ h₀bar.domain) → ((xbar ∈ hᵢbar.domain) → ((SubtileLatticeAdjacent C₀bar Cᵢbar
            T₀bar Tᵢbar h₀bar hᵢbar) → ((BandPrototile (qbar ibar.succ) Tᵢbar) → (∀ (layout :
            BandOrderedGeneralLayoutCertificate qbar cfg C₀bar T₀bar), ∀ (pieces : Fin (3 : ℕ) →
            Bool → ProtoTile), ∀ (functions : Fin (3 : ℕ) → Bool → PartialOdometer),
            (BandPrototile (qbar (0 : Fin (4 : ℕ))) T₀bar) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            TileOdometer (qbar i.succ) (pieces i s) (functions i s)) → ((∀ (x : LatticeCell), x ∈
            T₀bar.cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (pieces i s).cells) → ((∀ (i : Fin
            (3 : ℕ)), ∀ (s : Bool), FootprintVertices (pieces i s) ⊆ FootprintVertices T₀bar) →
            ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid (pieces i s) - TileCentroid T₀bar =
            (if s = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint
            (BandVectors.1 (qbar (i + (2 : Fin (3 : ℕ))).succ) (qbar (i + (1 : Fin (3 :
            ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1 (qbar (i + (2 : Fin (3 : ℕ))).succ)
            (qbar (i + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (qbar (i +
            (2 : Fin (3 : ℕ))).succ) (qbar (i + (1 : Fin (3 : ℕ))).succ))).1))) → ((∀ (x :
            GaussianInt), x ∈ h₀bar.domain ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (functions i
            s).domain) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ x ∈ (functions i s).domain,
            h₀bar.value x = (functions i s).value x) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ (j
            : Fin (3 : ℕ)), ∀ (t : Bool), OdometerCompatibility (functions i s) (functions j t))
            → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), (qbar i.succ).1 = (0 : ℤ) ∨ ∃ (p : ℝ × ℝ) (p_i
            : ℝ × ℝ), PartialOdometerSlope h₀bar = some p ∧ PartialOdometerSlope (functions i s)
            = some p_i ∧ p_i.1 - p.1 = (if s = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
            ((↑(BandVectors.2 (qbar (i + (2 : Fin (3 : ℕ))).succ) (qbar (i + (1 : Fin (3 :
            ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (qbar (i + (2 : Fin (3 : ℕ))).succ) (qbar (i +
            (1 : Fin (3 : ℕ))).succ)).im : ℝ)) ∧ p_i.2 - p.2 = (if s = true then (1 : ℝ) else (-1
            : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (qbar (i + (2 : Fin (3 : ℕ))).succ) (qbar (i
            + (1 : Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (qbar (i + (2 : Fin (3 :
            ℕ))).succ) (qbar (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → ((∀ y, y = xbar ∨ y =
            xbar + 1 ∨ y = xbar - 1 ∨ y = xbar + ⟨0, 1⟩ ∨ y = xbar - ⟨0, 1⟩ → y ∈
            FootprintVertices T₀bar ∨ y ∈ FootprintVertices Tᵢbar) → (
        let labelOf : Fin 3 → Bool → SixSubtileLabel := fun j e =>
          match j, e with
          | 0, true => .A | 0, false => .B
          | 1, true => .C | 1, false => .D
          | 2, true => .E | 2, false => .F
        let pieceIndex : Fin 3 → Bool → PeriodicSubtileIndex := fun j e =>
          ⟨labelOf j e, 0, 0⟩
        (∀ (j : Fin 3), ∀ (e : Bool), pieceIndex j e = ⟨.A, 0, 0⟩ ∨ pieceIndex j e = ⟨.B, 0, 0⟩ ∨
            pieceIndex j e = ⟨.C, 0, 0⟩ ∨ pieceIndex j e = ⟨.D, 0, 0⟩ ∨ pieceIndex j e = ⟨.E, 0,
            0⟩ ∨ pieceIndex j e = ⟨.F, 0, 0⟩) → ((∀ (j : Fin 3), ∀ (e : Bool), (pieces j e).cells
            = (SubtileOccurrenceInterpretation layout.P layout.u layout.v (pieceIndex j e)).cells
            ∧ ((pieces j e).cells = ∅ → (pieces j e).anchor = (SubtileOccurrenceInterpretation
            layout.P layout.u layout.v (pieceIndex j e)).anchor) ∧ FootprintVertices (pieces j e)
            = FootprintVertices (SubtileOccurrenceInterpretation layout.P layout.u layout.v
            (pieceIndex j e)) ∧ ((functions j e).domain : Set GaussianInt) = FootprintVertices
            (SubtileOccurrenceInterpretation layout.P layout.u layout.v (pieceIndex j e))) →
            ((QuarterTurnSymmetric T₀bar) → (Nonempty
            (BandOrderedGeneralSubtileNormalizationCertificate C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ
            x))))))))))))))))))))))))))))) ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x hq hq₀ hqᵢ r g qrot irot qbar hqbar cfg p₀bar pᵢbar sbar hO₀bar
      hOᵢbar hp₀bar hpᵢbar hcentroidBar hslopexBar hslopeyBar reverse ibar T₀bar Tᵢbar h₀bar
      hᵢbar xbar hqbarᵢ hqbar₀Pos hqbarᵢPos C₀bar Cᵢbar hx₀bar hxᵢbar hadjbar hTᵢbarBand layout
      pieces functions hrootBand hpieceOdometer hpieceCells hpieceFootprint hpieceCentroid
      hfunctionDomains hfunctionRestriction hfunctionCompatibility hpieceSlope hstarFootprint
      labelOf pieceIndex hpieceIndexCentral centralData hrootSym
  let edge : Fin 3 → GaussianInt := fun j =>
    BandVectors.1 (qbar ((j + 2).succ)) (qbar ((j + 1).succ))
  let incoming : Fin 3 → GaussianInt := fun j =>
    BandVectors.1 (qbar j.succ) (qbar 0)
  let outgoing : Fin 3 → GaussianInt := fun j =>
    BandVectors.1 (qbar 0) (qbar j.succ)
  obtain ⟨hsuper, _, hin0, _, hflip⟩ := VectorRecursionLaws qbar hqbar.1
  have hflips := hflip hqbar
  let R : Fin 4 → CircleCoordinates := ![qbar 0, qbar 2, qbar 3, qbar 1]
  have hR : SemiProperQuadruple R := by
    simpa [R] using SemiProperQuadruple.rotate hqbar.1
  let S : Fin 4 → CircleCoordinates := ![R 0, R 2, R 3, R 1]
  have hS : SemiProperQuadruple S := by
    simpa [S] using SemiProperQuadruple.rotate hR
  have hin1 : incoming 1 =
      edge 2 - (⟨0, 1⟩ : GaussianInt) * edge 0 := SubtileNormalizationGeometry.hin1 q r g hR
  have hin2 : incoming 2 =
      edge 0 - (⟨0, 1⟩ : GaussianInt) * edge 1 := SubtileNormalizationGeometry.hin2 q r g hS
  let exteriorIndex : PeriodicSubtileIndex :=
    if ibar = 0 then
      if sbar = 0 then ⟨.A, 0, -1⟩
      else if sbar = 1 then ⟨.B, 1, 1⟩
      else if sbar = 2 then ⟨.B, 0, 1⟩
      else ⟨.A, -1, -1⟩
    else if ibar = 1 then
      if sbar = 0 then ⟨.C, 1, 1⟩
      else if sbar = 1 then ⟨.D, -1, 0⟩
      else if sbar = 2 then ⟨.D, -1, -1⟩
      else ⟨.C, 1, 0⟩
    else
      if sbar = 0 then ⟨.E, -1, 0⟩
      else if sbar = 1 then ⟨.F, 0, -1⟩
      else if sbar = 2 then ⟨.F, 1, 0⟩
      else ⟨.E, 0, 1⟩
  have hexteriorIndex :
      exteriorIndex = ⟨.A, -1, -1⟩ ∨ exteriorIndex = ⟨.A, 0, -1⟩ ∨
      exteriorIndex = ⟨.C, 1, 0⟩ ∨ exteriorIndex = ⟨.C, 1, 1⟩ ∨
      exteriorIndex = ⟨.E, 0, 1⟩ ∨ exteriorIndex = ⟨.E, -1, 0⟩ ∨
      exteriorIndex = ⟨.B, 1, 1⟩ ∨ exteriorIndex = ⟨.B, 0, 1⟩ ∨
      exteriorIndex = ⟨.D, -1, 0⟩ ∨ exteriorIndex = ⟨.D, -1, -1⟩ ∨
      exteriorIndex = ⟨.F, 0, -1⟩ ∨ exteriorIndex = ⟨.F, 1, 0⟩ :=
          SubtileNormalizationGeometry.hexteriorIndex i r g sbar
  have hrows := BandOrderedGeneralSubtileCanonicalRows
    layout.P T₀bar layout.u layout.v ibar sbar edge incoming outgoing
    (by simpa [edge] using hsuper)
    (by simpa [incoming, edge] using hin0)
    hin1 hin2
    (by
      intro j
      simpa [incoming, outgoing] using (hflips j).1)
    (by simpa [outgoing, qbar] using layout.period_u)
    (by simpa [outgoing, qbar] using layout.period_v)
    (by
      intro j e
      simpa [edge] using (layout.outer_occurrence j e).2.2)
  have hexteriorCentroid :
      TileCentroid (SubtileOccurrenceInterpretation layout.P layout.u
          layout.v exteriorIndex) - TileCentroid T₀bar =
        (1 / 2 : ℝ) • GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ sbar.val *
            (incoming ibar + outgoing ibar)) := SubtileNormalizationGeometry.hexteriorCentroid q
                i T₀ r g hqbar cfg sbar hqbar₀Pos layout hrows
  have hexteriorBand : BandPrototile (qbar ibar.succ)
      (SubtileOccurrenceInterpretation layout.P layout.u layout.v
        exteriorIndex) := SubtileNormalizationGeometry.hexteriorBand q i T₀ r g hqbar cfg sbar
            hqbar₀Pos layout
  have hfixedCentroid :
      TileCentroid (SubtileOccurrenceInterpretation layout.P layout.u
        layout.v exteriorIndex) = TileCentroid Tᵢbar :=
            SubtileNormalizationGeometry.hfixedCentroid q i T₀ Tᵢ r g hqbar cfg sbar hcentroidBar
            hqbar₀Pos layout hexteriorCentroid
  have hfixedUnique := BandPrototileCentroidUnique (qbar ibar.succ)
    (SubtileOccurrenceInterpretation layout.P layout.u layout.v
      exteriorIndex) Tᵢbar hexteriorBand hTᵢbarBand hfixedCentroid
  refine ⟨{
    presentation_proper := hq
    presentation_child := hq₀
    presentation_parent := hqᵢ
    parentRotation := r
    symmetry := g
    rotatedPresentation := qrot
    rotated_presentation_eq := rfl
    normalizedPresentation := qbar
    normalized_presentation_eq := rfl
    configuration := cfg
    normalizedCircle := C₀bar
    normalized_circle_eq := rfl
    normalizedFixedCircle := Cᵢbar
    normalized_fixed_circle_eq := hqbarᵢ
    normalizedRoot := T₀bar
    normalizedFixed := Tᵢbar
    normalizedRootFunction := h₀bar
    normalizedFixedFunction := hᵢbar
    normalizedPoint := xbar
    normalized_root_eq := rfl
    normalized_fixed_eq := rfl
    normalized_root_function_eq := rfl
    normalized_fixed_function_eq := rfl
    normalized_point_eq := rfl
    normalized_point_root_domain := hx₀bar
    normalized_point_fixed_domain := hxᵢbar
    normalized_root_odometer := hO₀bar
    normalized_fixed_odometer := hOᵢbar
    normalizedRootSlope := p₀bar
    normalizedFixedSlope := pᵢbar
    normalized_root_slope := hp₀bar
    normalized_fixed_slope := hpᵢbar
    normalizedParentSlot := ibar
    normalizedQuarterTurn := sbar
    normalized_parent_coordinate := rfl
    normalized_adjacency_centroid := by
      simpa [qbar, reverse, ibar] using hcentroidBar
    normalized_adjacency_slope_real := by
      simpa [qbar, reverse, ibar] using hslopexBar
    normalized_adjacency_slope_imag := by
      simpa [qbar, reverse, ibar] using hslopeyBar
    pieces := pieces
    functions := functions
    root_band := hrootBand
    piece_odometer := hpieceOdometer
    piece_cell_cover := hpieceCells
    piece_footprint := hpieceFootprint
    piece_centroid := hpieceCentroid
    function_domain_cover := hfunctionDomains
    function_restriction := hfunctionRestriction
    function_compatibility := hfunctionCompatibility
    piece_slope := hpieceSlope
    adjacency := hadjbar
    root_quarter_turn := hrootSym
    layout := layout
    pieceIndex := pieceIndex
    piece_index_central := hpieceIndexCentral
    piece_layout_cells := fun j e => (centralData j e).1
    piece_layout_empty_anchor := fun j e => (centralData j e).2.1
    piece_layout_footprint := fun j e => (centralData j e).2.2.1
    piece_layout_domain := fun j e => (centralData j e).2.2.2
    exteriorIndex := exteriorIndex
    exterior_index := hexteriorIndex
    fixed_exterior_cells := hfixedUnique.1
    fixed_exterior_empty_anchor := hfixedUnique.2
    normalized_star := hstarFootprint }⟩

end SubtileNormalizationConclusion

theorem BandOrderedGeneralSubtileNormalizationCertificateExists
    (C₀ Cᵢ : BandCircle) (q : Fin 4 → CircleCoordinates)
    (i : Fin 3) (s : Fin 4) (T₀ Tᵢ : ProtoTile)
    (h₀ hᵢ : PartialOdometer) (x : GaussianInt) (p₀ pᵢ : ℝ × ℝ)
    (horbit :
      ¬ ((∃ (g : BandPackingSymmetry) (P : FordFareyParameter),
              BandPackingSymmetryCircleAction g
                (FordCircleCoordinate P.p P.q) = C₀.1.1) ∨
            (∃ (g : BandPackingSymmetry) (K : DiamondParameter),
              BandPackingSymmetryCircleAction g
                (DiamondRecursiveQuadruple K 0) = C₀.1.1)))
    (hq : ProperBandQuadruple q) (hq₀ : q 0 = C₀.1.1)
    (hqᵢ : q i.succ = Cᵢ.1.1)
    (hslope₀ : PartialOdometerSlope h₀ = some p₀)
    (hslopeᵢ : PartialOdometerSlope hᵢ = some pᵢ)
    (hcentroid : TileCentroid Tᵢ - TileCentroid T₀ =
      (1 / 2 : ℝ) • GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.1 (q i.succ) (q 0) +
           BandVectors.1 (q 0) (q i.succ))))
    (hslopex : pᵢ.1 - p₀.1 = ((1 / 2 : ℝ) • GaussianRealPoint
      ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
        (BandVectors.2 (q i.succ) (q 0) +
         BandVectors.2 (q 0) (q i.succ)))).1)
    (hslopey : pᵢ.2 - p₀.2 = ((1 / 2 : ℝ) • GaussianRealPoint
      ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
        (BandVectors.2 (q i.succ) (q 0) +
         BandVectors.2 (q 0) (q i.succ)))).2)
    (hadj : SubtileLatticeAdjacent C₀ Cᵢ T₀ Tᵢ h₀ hᵢ)
    (hx₀ : x ∈ h₀.domain) (hxᵢ : x ∈ hᵢ.domain)
    (hstar : ∀ y,
      y = x ∨ y = x + 1 ∨ y = x - 1 ∨
        y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
      y ∈ h₀.domain ∨ y ∈ hᵢ.domain) :
    Nonempty (BandOrderedGeneralSubtileNormalizationCertificate
      C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x) := by
-- BODY
  classical
  rcases hadj with
    ⟨hO₀, hOᵢ, p₀', pᵢ', hp₀', hpᵢ', q', i', s', hq', hq₀', hqᵢ',
      hcentroid', hslopex', hslopey'⟩
  have hparentPos : 0 < Cᵢ.1.1.1 := by
    exact Cᵢ.2
  obtain ⟨r, g, hregime⟩ := BandRegimeClassification q hq
  let qrot : Fin 4 → CircleCoordinates :=
    ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
  have hqrotSemi : SemiProperQuadruple qrot := SubtileNormalizationGeometry.hqrotSemi q hq q' r g
      hregime
  have hqrot : ProperBandQuadruple qrot := SubtileNormalizationGeometry.hqrot q hq q' r g hregime
      hqrotSemi
  let irot : Fin 3 := i - r
  have hrotParent : qrot irot.succ = q i.succ := by
    fin_cases r <;> fin_cases i <;> simp [qrot, irot]
  have hqrot₀ : qrot 0 = C₀.1.1 := by simpa [qrot] using hq₀
  let qbar := BandPackingSymmetryQuadrupleAction g qrot
  have hqbar : ProperBandQuadruple qbar :=
    BandPackingSymmetryProperCovariance g qrot hqrot
  have hqbar₀ : qbar 0 = BandPackingSymmetryCircleAction g C₀.1.1 := by
    simp [qbar, qrot, BandPackingSymmetryQuadrupleAction, hq₀]
  have hgeneral : Nonempty (BandOrderedGeneralConfiguration qbar) :=
      SubtileNormalizationGeometry.hgeneral C₀ q horbit hq₀ q' r g hregime
  obtain ⟨cfg⟩ := hgeneral
  have hO₀rot : TileOdometer (qrot 0) T₀ h₀ := SubtileNormalizationGeometry.hO₀rot C₀ q T₀ h₀ hO₀
      r hqrot₀
  have hOᵢrot : TileOdometer (qrot irot.succ) Tᵢ hᵢ := SubtileNormalizationGeometry.hOᵢrot Cᵢ q i
      Tᵢ hᵢ hqᵢ hOᵢ r hrotParent
  have hcentroidRot : TileCentroid Tᵢ - TileCentroid T₀ =
      (1 / 2 : ℝ) • GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.1 (qrot irot.succ) (qrot 0) +
           BandVectors.1 (qrot 0) (qrot irot.succ))) := SubtileNormalizationGeometry.hcentroidRot
               q i s T₀ Tᵢ hcentroid r hrotParent
  have hslopexRot : pᵢ.1 - p₀.1 = ((1 / 2 : ℝ) • GaussianRealPoint
      ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
        (BandVectors.2 (qrot irot.succ) (qrot 0) +
         BandVectors.2 (qrot 0) (qrot irot.succ)))).1 := SubtileNormalizationGeometry.hslopexRot
             q i s p₀ pᵢ hslopex r hrotParent
  have hslopeyRot : pᵢ.2 - p₀.2 = ((1 / 2 : ℝ) • GaussianRealPoint
      ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
        (BandVectors.2 (qrot irot.succ) (qrot 0) +
         BandVectors.2 (qrot 0) (qrot irot.succ)))).2 := SubtileNormalizationGeometry.hslopeyRot
             q i s p₀ pᵢ hslopey r hrotParent
  obtain ⟨negative, p₀bar, pᵢbar, sbar, hphase, hsbar,
      hO₀bar, hOᵢbar, hp₀bar, hpᵢbar, hcentroidBar,
      hslopexBar, hslopeyBar, hcompatBar⟩ :=
    SubtileLatticeAdjacentPackingSymmetryTransport g qrot hqrot irot s
      (by simpa [hrotParent, hqᵢ] using hparentPos)
      T₀ Tᵢ h₀ hᵢ p₀ pᵢ hO₀rot hOᵢrot hslope₀ hslopeᵢ
      hcentroidRot hslopexRot hslopeyRot
  let reverse := BandPackingSymmetryReversesOrientation g
  let ibar : Fin 3 := if reverse then -irot else irot
  let T₀bar := BandPackingSymmetryTileAction g T₀
  let Tᵢbar := BandPackingSymmetryTileAction g Tᵢ
  let h₀bar := BandPackingSymmetryPartialOdometerAction g h₀
  let hᵢbar := BandPackingSymmetryPartialOdometerAction g hᵢ
  let xbar := BandPackingSymmetryVectorAction g x
  have hqbarᵢ : qbar ibar.succ =
      BandPackingSymmetryCircleAction g Cᵢ.1.1 := SubtileNormalizationGeometry.hqbarᵢ Cᵢ q i hqᵢ
          r g hrotParent
  have hqbar₀Pos : 0 < (qbar 0).1 :=
    (ProperBandCurvatureStructure qbar hqbar).1
  have hqbarᵢPos : 0 < (qbar ibar.succ).1 := SubtileNormalizationGeometry.hqbarᵢPos Cᵢ q i s r g
      hqbar cfg negative sbar
  let C₀bar : BandCircle :=
    ⟨⟨qbar 0, ⟨Or.inl hqbar₀Pos, ⟨qbar, hqbar.1, ⟨0, rfl⟩⟩⟩⟩, hqbar₀Pos⟩
  let Cᵢbar : BandCircle :=
    ⟨⟨qbar ibar.succ,
      ⟨Or.inl hqbarᵢPos, ⟨qbar, hqbar.1, ⟨ibar.succ, rfl⟩⟩⟩⟩,
      hqbarᵢPos⟩
  have hx₀bar : xbar ∈ h₀bar.domain := SubtileNormalizationGeometry.hx₀bar h₀ hᵢ x hx₀ g
  have hxᵢbar : xbar ∈ hᵢbar.domain := SubtileNormalizationGeometry.hxᵢbar h₀ hᵢ x hxᵢ g
  have hadjbar : SubtileLatticeAdjacent C₀bar Cᵢbar
      T₀bar Tᵢbar h₀bar hᵢbar := SubtileNormalizationGeometry.hadjbar q i T₀ Tᵢ h₀ hᵢ r g hqbar
          p₀bar pᵢbar sbar hO₀bar hOᵢbar hp₀bar hpᵢbar hcentroidBar hslopexBar hslopeyBar
          hqbar₀Pos hqbarᵢPos
  have hT₀barBand : BandPrototile (qbar 0) T₀bar :=
    TileOdometerBandPrototile _ _ _ hO₀bar
  have hTᵢbarBand : BandPrototile (qbar ibar.succ) Tᵢbar :=
    TileOdometerBandPrototile _ _ _ hOᵢbar
  have hT₀ind := BandTileSimultaneousInduction qbar hqbar T₀bar hT₀barBand
  have hsmallT1 : ∀ (q' : Fin 4 → CircleCoordinates) (T' : ProtoTile)
      (S' : Fin 3 → Bool → ProtoTile), ProperBandQuadruple q' →
      BandPrototile (q' 0) T' →
      (∀ i s, BandSubtileOccurrence q' T' i s (S' i s)) →
      (∀ z, z ∈ T'.cells ↔ ∃ i s, z ∈ (S' i s).cells) →
      Int.toNat (q' 0).1 < Int.toNat (qbar 0).1 →
      LatticeTile T' ∧ TileArea T' = Int.toNat (q' 0).1 ∧
        ∀ i s, LatticeTile (TileCellComplement T' (S' i s)) ∧
          TileTouching (TileCellComplement T' (S' i s)) (S' i s) :=
              SubtileNormalizationGeometry.hsmallT1 q r g
  have hsmallT2 : ∀ (D : CircleCoordinates) (U : ProtoTile),
      BandPrototile D U → Int.toNat D.1 < Int.toNat (qbar 0).1 →
      QuarterTurnSymmetric U := SubtileNormalizationGeometry.hsmallT2 q r g
  have hsmallT4 : ∀ (q' : Fin 4 → CircleCoordinates)
      (T' U : ProtoTile), ProperBandQuadruple q' →
      BandPrototile (q' 0) T' →
      Int.toNat (q' 0).1 < Int.toNat (qbar 0).1 → 1 < (q' 0).1 →
      ∀ i : Fin 3, BandPrototile (q' i.succ) U →
      TileCentroid U - TileCentroid T' = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q' i.succ) (q' 0)) +
          GaussianRealPoint (BandVectors.1 (q' 0) (q' i.succ))) →
      TouchingTriple T'
        (TileTranslation T' (BandVectors.1 (q' i.succ) (q' 0))) U :=
            SubtileNormalizationGeometry.hsmallT4 q r g
  have hsmallT5 : ∀ (q' : Fin 4 → CircleCoordinates)
      (T' U V : ProtoTile), ProperBandQuadruple q' →
      BandPrototile (q' 0) T' →
      Int.toNat (q' 0).1 < Int.toNat (qbar 0).1 →
      ∀ i : Fin 3, BandPrototile (q' i.succ) U →
      BandPrototile (q' ((i + 1).succ)) V →
      TileCentroid U - TileCentroid T' = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q' i.succ) (q' 0)) +
          GaussianRealPoint (BandVectors.1 (q' 0) (q' i.succ))) →
      TileCentroid V - TileCentroid T' = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q' ((i + 1).succ)) (q' 0)) -
          GaussianRealPoint (BandVectors.1 (q' 0) (q' ((i + 1).succ)))) →
      TouchingTriple T' U V := SubtileNormalizationGeometry.hsmallT5 q r g
  obtain ⟨layout⟩ := BandOrderedGeneralLayout qbar cfg C₀bar
    rfl T₀bar hT₀barBand hsmallT1 hsmallT2 hsmallT4 hsmallT5
  obtain ⟨pieces, functions, hrootBand, hpieceOdometer, hpieceCells,
      hpieceFootprint, hpieceCentroid, hfunctionDomains,
      hfunctionRestriction, hfunctionCompatibility, hpieceSlope⟩ :=
    TileOdometerReindexedDecomposition qbar hqbar T₀bar h₀bar
      (by linarith [cfg.childLarge]) hO₀bar
  have hstarBarDomain : ∀ y,
      y = xbar ∨ y = xbar + 1 ∨ y = xbar - 1 ∨
        y = xbar + ⟨0, 1⟩ ∨ y = xbar - ⟨0, 1⟩ →
      y ∈ h₀bar.domain ∨ y ∈ hᵢbar.domain :=
    P5658T1FivePointDomainCoverSymmetryCovariance g h₀ hᵢ x hstar
  have hstarFootprint : ∀ y,
      y = xbar ∨ y = xbar + 1 ∨ y = xbar - 1 ∨
        y = xbar + ⟨0, 1⟩ ∨ y = xbar - ⟨0, 1⟩ →
      y ∈ FootprintVertices T₀bar ∨
        y ∈ FootprintVertices Tᵢbar := SubtileNormalizationGeometry.hstarFootprint q i T₀ Tᵢ h₀
            hᵢ x r g hO₀bar hOᵢbar hqbar₀Pos hqbarᵢPos hstarBarDomain
  let labelOf : Fin 3 → Bool → SixSubtileLabel := fun j e =>
    match j, e with
    | 0, true => .A | 0, false => .B
    | 1, true => .C | 1, false => .D
    | 2, true => .E | 2, false => .F
  let pieceIndex : Fin 3 → Bool → PeriodicSubtileIndex := fun j e =>
    ⟨labelOf j e, 0, 0⟩
  have hpieceIndexCentral (j : Fin 3) (e : Bool) :
      pieceIndex j e = ⟨.A, 0, 0⟩ ∨ pieceIndex j e = ⟨.B, 0, 0⟩ ∨
      pieceIndex j e = ⟨.C, 0, 0⟩ ∨ pieceIndex j e = ⟨.D, 0, 0⟩ ∨
      pieceIndex j e = ⟨.E, 0, 0⟩ ∨ pieceIndex j e = ⟨.F, 0, 0⟩ :=
          SubtileNormalizationGeometry.hpieceIndexCentral j e
  have translation_zero (U : ProtoTile) : TileTranslation U 0 = U :=
      SubtileNormalizationGeometry.translation_zero U
  have centralOccurrence (j : Fin 3) (e : Bool) :
      SubtileOccurrenceInterpretation layout.P layout.u layout.v
        (pieceIndex j e) = layout.P j e := SubtileNormalizationGeometry.centralOccurrence q T₀ r
            g hqbar cfg hqbar₀Pos layout translation_zero j e
  have centralData (j : Fin 3) (e : Bool) :
      (pieces j e).cells =
          (SubtileOccurrenceInterpretation layout.P layout.u layout.v
            (pieceIndex j e)).cells ∧
      ((pieces j e).cells = ∅ →
          (pieces j e).anchor =
            (SubtileOccurrenceInterpretation layout.P layout.u layout.v
              (pieceIndex j e)).anchor) ∧
      FootprintVertices (pieces j e) = FootprintVertices
          (SubtileOccurrenceInterpretation layout.P layout.u layout.v
            (pieceIndex j e)) ∧
      ((functions j e).domain : Set GaussianInt) = FootprintVertices
          (SubtileOccurrenceInterpretation layout.P layout.u layout.v
            (pieceIndex j e)) := SubtileNormalizationGeometry.centralData Cᵢ q i s T₀ r g hqbar
                cfg negative sbar hqbar₀Pos layout pieces functions hpieceOdometer hpieceCentroid
                centralOccurrence j e
  have hrootSym : QuarterTurnSymmetric T₀bar := hT₀ind.2.2.2.1
  have subtileNormalizationCertificate :
    Nonempty (BandOrderedGeneralSubtileNormalizationCertificate
      C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x) := SubtileNormalizationConclusion.subtileNormalizationCertificate
          C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x hq hq₀ hqᵢ r g hqbar cfg p₀bar pᵢbar sbar hO₀bar hOᵢbar hp₀bar
          hpᵢbar hcentroidBar hslopexBar hslopeyBar hqbarᵢ hqbar₀Pos hqbarᵢPos hx₀bar hxᵢbar
          hadjbar hTᵢbarBand layout pieces functions hrootBand hpieceOdometer hpieceCells
          hpieceFootprint hpieceCentroid hfunctionDomains hfunctionRestriction
          hfunctionCompatibility hpieceSlope hstarFootprint hpieceIndexCentral centralData hrootSym
  exact subtileNormalizationCertificate


end ApollonianSuperharmonic

end
