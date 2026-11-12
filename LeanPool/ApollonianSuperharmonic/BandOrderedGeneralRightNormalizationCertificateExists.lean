/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5658T1FivePointDomainCoverSymmetryCovariance
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralRightNormalizationCertificate
public import LeanPool.ApollonianSuperharmonic.BandTileSimultaneousInduction
public import LeanPool.ApollonianSuperharmonic.RightLatticeAdjacentPackingSymmetryTransport
public import LeanPool.ApollonianSuperharmonic.TileOdometerReindexedDecomposition

-- [TABLET NODE: BandOrderedGeneralRightNormalizationCertificateExists]

/-!
# BandOrderedGeneralRightNormalizationCertificateExists

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RightNormalizationGeometry

private theorem hqrotSemi :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple q) → (∀ (r : Fin (3 : ℕ)),
            ∀ (g : BandPackingSymmetry), (
        let q' := BandPackingSymmetryQuadrupleAction g ![q (0 : Fin (4 : ℕ)), q r.succ, q (r + (1
            : Fin (3 : ℕ))).succ, q (r + (2 : Fin (3 : ℕ))).succ]; Xor (∃ (P :
            FordFareyParameter), (1 : ℕ) < P.q ∧ q' = FordRecursiveQuadruple P) (Xor (∃ (K :
            DiamondParameter), (1 : ℕ) < K.1 ∧ q' = DiamondRecursiveQuadruple K) (Nonempty
            (BandOrderedGeneralConfiguration q')))) → (
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        SemiProperQuadruple qrot)) ) := by
  classical
  intro q hq r g hregime qrot
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
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple q) → (∀ (r : Fin (3 : ℕ)),
            ∀ (g : BandPackingSymmetry), (
        let q' := BandPackingSymmetryQuadrupleAction g ![q (0 : Fin (4 : ℕ)), q r.succ, q (r + (1
            : Fin (3 : ℕ))).succ, q (r + (2 : Fin (3 : ℕ))).succ]; Xor (∃ (P :
            FordFareyParameter), (1 : ℕ) < P.q ∧ q' = FordRecursiveQuadruple P) (Xor (∃ (K :
            DiamondParameter), (1 : ℕ) < K.1 ∧ q' = DiamondRecursiveQuadruple K) (Nonempty
            (BandOrderedGeneralConfiguration q')))) → (
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        (SemiProperQuadruple qrot) → (ProperBandQuadruple qrot))) ) := by
  classical
  intro q hq r g hregime qrot hqrotSemi
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
        ∀ (C : BandCircle), (¬((∃ (g : BandPackingSymmetry) (P : FordFareyParameter),
            BandPackingSymmetryCircleAction g (FordCircleCoordinate P.p P.q) = C.1.1) ∨ ∃ (g :
            BandPackingSymmetry) (K : DiamondParameter), BandPackingSymmetryCircleAction g
            (DiamondRecursiveQuadruple K (0 : Fin (4 : ℕ))) = C.1.1)) → (∀ (q : Fin (4 : ℕ) →
            CircleCoordinates), (q (0 : Fin (4 : ℕ)) = C.1.1) → (∀ (r : Fin (3 : ℕ)), ∀ (g :
            BandPackingSymmetry), (
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
  intro C horbit q hqC r g hregime qrot qbar
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
            (BandPackingSymmetryCircleAction g C.1.1) := by
              have h0 := congrFun heq 0
              simpa [BandPackingSymmetryQuadrupleAction,
                FordRecursiveQuadruple, hqC] using congrArg
                  (BandPackingSymmetryCircleAction ginv) h0.symm
      _ = C.1.1 := hinv _
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
              (BandPackingSymmetryCircleAction g C.1.1) := by
                have h0 := congrFun heq 0
                simpa [BandPackingSymmetryQuadrupleAction, hqC] using congrArg
                  (BandPackingSymmetryCircleAction ginv) h0.symm
        _ = C.1.1 := hinv _
    · exact hgeneral.1

private theorem hcentRot :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i₀ :
            Fin (3 : ℕ)), ∀ (e₀ : Bool), (TileCentroid N - TileCentroid T = (if e₀ = true then (1
            : ℝ) else (-1 : ℝ)) • GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q
            i₀.succ))) → (∀ (r : Fin (3 : ℕ)),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let irot : Fin 3 := i₀ - r
        (qrot irot.succ = q i₀.succ) → (TileCentroid N - TileCentroid T = (if e₀ = true then (1 :
            Real) else -1) • GaussianRealPoint (BandVectors.1 (qrot 0) (qrot irot.succ)))) ) := by
  classical
  intro T N q i₀ e₀ hcent r qrot irot hrotParent
  simpa [qrot, hrotParent] using hcent

private theorem hslopeReRot :
    (by
      classical
      exact
        ∀ (pT : ℝ × ℝ), ∀ (pN : ℝ × ℝ), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i₀ : Fin (3 :
            ℕ)), ∀ (e₀ : Bool), (pN.1 - pT.1 = (if e₀ = true then (1 : ℝ) else (-1 : ℝ)) *
            (↑(BandVectors.2 (q (0 : Fin (4 : ℕ))) (q i₀.succ)).re : ℝ)) → (∀ (r : Fin (3 : ℕ)),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let irot : Fin 3 := i₀ - r
        (qrot irot.succ = q i₀.succ) → (pN.1 - pT.1 = (if e₀ = true then (1 : Real) else -1) *
            (BandVectors.2 (qrot 0) (qrot irot.succ)).re)) ) := by
  classical
  intro pT pN q i₀ e₀ hslopeRe r qrot irot hrotParent
  simpa [qrot, hrotParent] using hslopeRe

private theorem hslopeImRot :
    (by
      classical
      exact
        ∀ (pT : ℝ × ℝ), ∀ (pN : ℝ × ℝ), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i₀ : Fin (3 :
            ℕ)), ∀ (e₀ : Bool), (pN.2 - pT.2 = (if e₀ = true then (1 : ℝ) else (-1 : ℝ)) *
            (↑(BandVectors.2 (q (0 : Fin (4 : ℕ))) (q i₀.succ)).im : ℝ)) → (∀ (r : Fin (3 : ℕ)),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let irot : Fin 3 := i₀ - r
        (qrot irot.succ = q i₀.succ) → (pN.2 - pT.2 = (if e₀ = true then (1 : Real) else -1) *
            (BandVectors.2 (qrot 0) (qrot irot.succ)).im)) ) := by
  classical
  intro pT pN q i₀ e₀ hslopeIm r qrot irot hrotParent
  simpa [qrot, hrotParent] using hslopeIm

private theorem hcentBar' :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i₀ :
            Fin (3 : ℕ)), ∀ (e₀ : Bool), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let irot : Fin 3 := i₀ - r
        let qbar := BandPackingSymmetryQuadrupleAction g qrot
        ∀ (negative : Bool), (TileCentroid (BandPackingSymmetryTileAction g N) - TileCentroid
            (BandPackingSymmetryTileAction g T) = (if (e₀ ^^ negative ^^
            BandPackingSymmetryReversesOrientation g) = true then (1 : ℝ) else (-1 : ℝ)) •
            GaussianRealPoint (BandVectors.1 (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin
            (4 : ℕ))) (BandPackingSymmetryQuadrupleAction g qrot ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) irot).succ))) → (
        let reverse := BandPackingSymmetryReversesOrientation g
        let idir : Fin 3 := if reverse then -irot else irot
        let ebar : Bool := xor (xor e₀ negative) reverse
        let positive : Bool := !ebar
        TileCentroid (BandPackingSymmetryTileAction g N) - TileCentroid
            (BandPackingSymmetryTileAction g T) = (if positive = true then (-1 : Real) else 1) •
            GaussianRealPoint (BandVectors.1 (qbar 0) (qbar idir.succ))) ) := by
  classical
  intro T N q i₀ e₀ r g qrot irot qbar negative hcentBar reverse idir ebar positive
  simpa [qbar, reverse, idir, ebar, positive] using hcentBar

private theorem hslopeReBar' :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i₀ : Fin (3 : ℕ)), ∀ (e₀ : Bool), ∀ (r : Fin
            (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let irot : Fin 3 := i₀ - r
        let qbar := BandPackingSymmetryQuadrupleAction g qrot
        ∀ (negative : Bool), ∀ (pTbar : ℝ × ℝ), ∀ (pNbar : ℝ × ℝ), (pNbar.1 - pTbar.1 = (if (e₀
            ^^ negative ^^ BandPackingSymmetryReversesOrientation g) = true then (1 : ℝ) else (-1
            : ℝ)) * (↑(BandVectors.2 (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin (4 :
            ℕ))) (BandPackingSymmetryQuadrupleAction g qrot ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) irot).succ)).re : ℝ))
            → (
        let reverse := BandPackingSymmetryReversesOrientation g
        let idir : Fin 3 := if reverse then -irot else irot
        let ebar : Bool := xor (xor e₀ negative) reverse
        let positive : Bool := !ebar
        pNbar.1 - pTbar.1 = (if positive = true then (-1 : Real) else 1) * (BandVectors.2 (qbar
            0) (qbar idir.succ)).re) ) := by
  classical
  intro q i₀ e₀ r g qrot irot qbar negative pTbar pNbar hslopeReBar reverse idir ebar positive
  simpa [qbar, reverse, idir, ebar, positive] using hslopeReBar

private theorem hslopeImBar' :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i₀ : Fin (3 : ℕ)), ∀ (e₀ : Bool), ∀ (r : Fin
            (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let irot : Fin 3 := i₀ - r
        let qbar := BandPackingSymmetryQuadrupleAction g qrot
        ∀ (negative : Bool), ∀ (pTbar : ℝ × ℝ), ∀ (pNbar : ℝ × ℝ), (pNbar.2 - pTbar.2 = (if (e₀
            ^^ negative ^^ BandPackingSymmetryReversesOrientation g) = true then (1 : ℝ) else (-1
            : ℝ)) * (↑(BandVectors.2 (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin (4 :
            ℕ))) (BandPackingSymmetryQuadrupleAction g qrot ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) irot).succ)).im : ℝ))
            → (
        let reverse := BandPackingSymmetryReversesOrientation g
        let idir : Fin 3 := if reverse then -irot else irot
        let ebar : Bool := xor (xor e₀ negative) reverse
        let positive : Bool := !ebar
        pNbar.2 - pTbar.2 = (if positive = true then (-1 : Real) else 1) * (BandVectors.2 (qbar
            0) (qbar idir.succ)).im) ) := by
  classical
  intro q i₀ e₀ r g qrot irot qbar negative pTbar pNbar hslopeImBar reverse idir ebar positive
  simpa [qbar, reverse, idir, ebar, positive] using hslopeImBar

private theorem hxTbar :
    (by
      classical
      exact
        ∀ (h : PartialOdometer), (PartialOdometer) → (∀ (x : GaussianInt), (x ∈ h.domain) → (∀ (g
            : BandPackingSymmetry),
        let hbar := BandPackingSymmetryPartialOdometerAction g h
        let xbar := BandPackingSymmetryVectorAction g x
        xbar ∈ hbar.domain)) ) := by
  classical
  intro h k x hxT g hbar xbar
  have hdom := (BandPackingSymmetryPartialOdometerActionFormulas g h k).1
  have hxset : BandPackingSymmetryVectorAction g x ∈
      ((BandPackingSymmetryPartialOdometerAction g h).domain :
        Set GaussianInt) := by
    rw [hdom]
    exact ⟨x, hxT, rfl⟩
  exact hxset

private theorem hxNbar :
    (by
      classical
      exact
        (PartialOdometer) → (∀ (k : PartialOdometer), ∀ (x : GaussianInt), (x ∈ k.domain) → (∀ (g
            : BandPackingSymmetry),
        let kbar := BandPackingSymmetryPartialOdometerAction g k
        let xbar := BandPackingSymmetryVectorAction g x
        xbar ∈ kbar.domain)) ) := by
  classical
  intro h k x hxN g kbar xbar
  have hdom := (BandPackingSymmetryPartialOdometerActionFormulas g k h).1
  have hxset : BandPackingSymmetryVectorAction g x ∈
      ((BandPackingSymmetryPartialOdometerAction g k).domain :
        Set GaussianInt) := by
    rw [hdom]
    exact ⟨x, hxN, rfl⟩
  exact hxset

private theorem hsmallT1 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
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
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
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
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
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
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
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

private theorem hadjbar :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k : PartialOdometer), ∀
            (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i₀ : Fin (3 : ℕ)), ∀ (e₀ : Bool), ∀ (r :
            Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let irot : Fin 3 := i₀ - r
        let qbar := BandPackingSymmetryQuadrupleAction g qrot
        ∀ (hqbar : ProperBandQuadruple qbar), ∀ (negative : Bool), ∀ (pTbar : ℝ × ℝ), ∀ (pNbar :
            ℝ × ℝ), (TileOdometer (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryTileAction g T) (BandPackingSymmetryPartialOdometerAction g h)) →
            ((TileOdometer (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryTileAction g N) (BandPackingSymmetryPartialOdometerAction g k)) →
            ((PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction g h) = some pTbar) →
            ((PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction g k) = some pNbar) →
            ((TileCentroid (BandPackingSymmetryTileAction g N) - TileCentroid
            (BandPackingSymmetryTileAction g T) = (if (e₀ ^^ negative ^^
            BandPackingSymmetryReversesOrientation g) = true then (1 : ℝ) else (-1 : ℝ)) •
            GaussianRealPoint (BandVectors.1 (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin
            (4 : ℕ))) (BandPackingSymmetryQuadrupleAction g qrot ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) irot).succ))) →
            ((pNbar.1 - pTbar.1 = (if (e₀ ^^ negative ^^ BandPackingSymmetryReversesOrientation
            g) = true then (1 : ℝ) else (-1 : ℝ)) * (↑(BandVectors.2
            (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction g qrot ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) irot).succ)).re : ℝ))
            → ((pNbar.2 - pTbar.2 = (if (e₀ ^^ negative ^^ BandPackingSymmetryReversesOrientation
            g) = true then (1 : ℝ) else (-1 : ℝ)) * (↑(BandVectors.2
            (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction g qrot ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) irot).succ)).im : ℝ))
            → (
        let Tbar := BandPackingSymmetryTileAction g T
        let Nbar := BandPackingSymmetryTileAction g N
        let hbar := BandPackingSymmetryPartialOdometerAction g h
        let kbar := BandPackingSymmetryPartialOdometerAction g k
        ∀ (hqbarPos : 0 < (qbar 0).1),
        let Cbar : BandCircle :=
          ⟨⟨qbar 0, ⟨Or.inl hqbarPos, ⟨qbar, hqbar.1, ⟨0, rfl⟩⟩⟩⟩, hqbarPos⟩
        RightLatticeAdjacent Cbar Tbar Nbar hbar kbar))))))) ) := by
  classical
  intro T N h k q i₀ e₀ r g qrot irot qbar hqbar negative pTbar pNbar hOTbar hONbar hpTbar hpNbar
      hcentBar hslopeReBar hslopeImBar Tbar Nbar hbar kbar hqbarPos Cbar
  let reverse := BandPackingSymmetryReversesOrientation g
  let idir : Fin 3 := if reverse then -irot else irot
  let ebar : Bool := xor (xor e₀ negative) reverse
  refine ⟨hOTbar, hONbar, pTbar, pNbar, hpTbar, hpNbar,
    qbar, idir, ebar, hqbar, rfl, ?_, ?_, ?_⟩
  · simpa [qbar, reverse, idir, ebar] using hcentBar
  · simpa [qbar, reverse, idir, ebar] using hslopeReBar
  · simpa [qbar, reverse, idir, ebar] using hslopeImBar

private theorem houterCentroid :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i₀ :
            Fin (3 : ℕ)), ∀ (e₀ : Bool), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let irot : Fin 3 := i₀ - r
        let qbar := BandPackingSymmetryQuadrupleAction g qrot
        ∀ (negative : Bool), ∀ (pTbar : ℝ × ℝ), ∀ (pNbar : ℝ × ℝ),
        let reverse := BandPackingSymmetryReversesOrientation g
        let idir : Fin 3 := if reverse then -irot else irot
        let ebar : Bool := xor (xor e₀ negative) reverse
        let positive : Bool := !ebar
        (TileCentroid (BandPackingSymmetryTileAction g N) - TileCentroid
            (BandPackingSymmetryTileAction g T) = (if positive = true then (-1 : Real) else 1) •
            GaussianRealPoint (BandVectors.1 (qbar 0) (qbar idir.succ))) → ((pNbar.1 - pTbar.1 =
            (if positive = true then (-1 : Real) else 1) * (BandVectors.2 (qbar 0) (qbar
            idir.succ)).re) → ((pNbar.2 - pTbar.2 = (if positive = true then (-1 : Real) else 1)
            * (BandVectors.2 (qbar 0) (qbar idir.succ)).im) → (
        let Tbar := BandPackingSymmetryTileAction g T
        let Nbar := BandPackingSymmetryTileAction g N
        let displacement : GaussianInt :=
          (if positive = true then (1 : GaussianInt) else -1) *
            BandVectors.1 (qbar 0) (qbar idir.succ)
        TileCentroid Tbar = TileCentroid (TileTranslation Nbar displacement)))) ) := by
  classical
  intro T N q i₀ e₀ r g qrot irot qbar negative pTbar pNbar reverse idir ebar positive hcentBar'
      hslopeReBar' hslopeImBar' Tbar Nbar displacement
  rw [(TileTranslationFormulas Nbar displacement).2.2.2.2.1]
  have h₁ := congrArg Prod.fst hcentBar'
  have h₂ := congrArg Prod.snd hcentBar'
  apply Prod.ext <;> rcases positive with (_ | _) <;>
    simp [displacement, GaussianRealPoint] at h₁ h₂ ⊢ <;> linarith

private theorem boundaryData :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i₀ :
            Fin (3 : ℕ)), ∀ (e₀ : Bool), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let irot : Fin 3 := i₀ - r
        let qbar := BandPackingSymmetryQuadrupleAction g qrot
        ∀ (hqbar : ProperBandQuadruple qbar), ∀ (cfg : BandOrderedGeneralConfiguration qbar), ∀
            (negative : Bool),
        let reverse := BandPackingSymmetryReversesOrientation g
        let idir : Fin 3 := if reverse then -irot else irot
        let ebar : Bool := xor (xor e₀ negative) reverse
        let positive : Bool := !ebar
        let Tbar := BandPackingSymmetryTileAction g T
        let Nbar := BandPackingSymmetryTileAction g N
        ∀ (hqbarPos : 0 < (qbar 0).1),
        let Cbar : BandCircle :=
          ⟨⟨qbar 0, ⟨Or.inl hqbarPos, ⟨qbar, hqbar.1, ⟨0, rfl⟩⟩⟩⟩, hqbarPos⟩
        ∀ (layout : BandOrderedGeneralLayoutCertificate qbar cfg Cbar Nbar), ∀ (pieces : Fin (3 :
            ℕ) → Bool → ProtoTile), ∀ (functions : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i :
            Fin (3 : ℕ)), ∀ (s : Bool), TileOdometer (qbar i.succ) (pieces i s) (functions i s))
            → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid (pieces i s) - TileCentroid Tbar
            = (if s = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint
            (BandVectors.1 (qbar (i + (2 : Fin (3 : ℕ))).succ) (qbar (i + (1 : Fin (3 :
            ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1 (qbar (i + (2 : Fin (3 : ℕ))).succ)
            (qbar (i + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (qbar (i +
            (2 : Fin (3 : ℕ))).succ) (qbar (i + (1 : Fin (3 : ℕ))).succ))).1))) → (
        let displacement : GaussianInt :=
          (if positive = true then (1 : GaussianInt) else -1) *
            BandVectors.1 (qbar 0) (qbar idir.succ)
        (TileCentroid Tbar = TileCentroid (TileTranslation Nbar displacement)) → (∀ (a : Fin 3),
            ∀ (s : Bool), (pieces a s).cells = (TileTranslation (layout.P a s)
            displacement).cells ∧ ((pieces a s).cells = ∅ → (pieces a s).anchor =
            (TileTranslation (layout.P a s) displacement).anchor) ∧ FootprintVertices (pieces a
            s) = FootprintVertices (TileTranslation (layout.P a s) displacement) ∧ ((functions a
            s).domain : Set GaussianInt) = FootprintVertices (TileTranslation (layout.P a s)
            displacement)))) ) := by
  classical
  intro T N q i₀ e₀ r g qrot irot qbar hqbar cfg negative reverse idir ebar positive Tbar Nbar
      hqbarPos Cbar layout pieces functions hpieceOdometer hpieceCentroid displacement
      houterCentroid a s
  have hpieceBand : BandPrototile (qbar a.succ) (pieces a s) :=
    TileOdometerBandPrototile _ _ _ (hpieceOdometer a s)
  have hlayoutBand : BandPrototile (qbar a.succ) (layout.P a s) :=
    (layout.outer_occurrence a s).1
  have htranslatedLayout :
      BandPrototile (qbar a.succ)
        (TileTranslation (layout.P a s) displacement) :=
    BandPrototileTranslation _ _ _ hlayoutBand
  have hcentroidAlign : TileCentroid (pieces a s) =
      TileCentroid (TileTranslation (layout.P a s) displacement) := by
    rw [(TileTranslationFormulas (layout.P a s) displacement).2.2.2.2.1]
    have hp₁ := congrArg Prod.fst (hpieceCentroid a s)
    have hp₂ := congrArg Prod.snd (hpieceCentroid a s)
    have hl₁ := congrArg Prod.fst (layout.outer_occurrence a s).2.2
    have hl₂ := congrArg Prod.snd (layout.outer_occurrence a s).2.2
    have hr₁ := congrArg Prod.fst houterCentroid
    have hr₂ := congrArg Prod.snd houterCentroid
    rw [(TileTranslationFormulas Nbar displacement).2.2.2.2.1] at hr₁ hr₂
    apply Prod.ext <;> simp only []
    · change (TileCentroid (pieces a s)).1 - (TileCentroid Tbar).1 = _ at hp₁
      change (TileCentroid (layout.P a s)).1 - (TileCentroid Nbar).1 = _ at hl₁
      change (TileCentroid Tbar).1 = (TileCentroid Nbar).1 + _ at hr₁
      linarith
    · change (TileCentroid (pieces a s)).2 - (TileCentroid Tbar).2 = _ at hp₂
      change (TileCentroid (layout.P a s)).2 - (TileCentroid Nbar).2 = _ at hl₂
      change (TileCentroid Tbar).2 = (TileCentroid Nbar).2 + _ at hr₂
      linarith
  have hu := BandPrototileCentroidUnique (qbar a.succ) (pieces a s)
    (TileTranslation (layout.P a s) displacement) hpieceBand
    htranslatedLayout hcentroidAlign
  have ho := ProtoTileObservableExtensionality (pieces a s)
    (TileTranslation (layout.P a s) displacement) hu.1 hu.2
  have hparentNonneg := (ProperBandCurvatureStructure qbar hqbar).2.1 a
  have hparentPos : 0 < (qbar a.succ).1 := by
    have hn := cfg.noLine a.succ
    omega
  have hd := PositiveCurvatureTileOdometerDomain (qbar a.succ)
    (pieces a s) (functions a s) hparentPos (hpieceOdometer a s)
  exact ⟨hu.1, hu.2, ho.1, hd.trans ho.1⟩

private theorem cyclicSlots :
    ∀ (i₀ r : Fin 3) (g : BandPackingSymmetry),
    let irot : Fin 3 := i₀ - r
    let reverse := BandPackingSymmetryReversesOrientation g
    let idir : Fin 3 := if reverse then -irot else irot
    let firstSlot : Fin 3 := idir + 1
    let secondSlot : Fin 3 := idir + 2
    (firstSlot = 0 ∧ secondSlot = 1 ∧ idir = 2) ∨
      (firstSlot = 1 ∧ secondSlot = 2 ∧ idir = 0) ∨
      (firstSlot = 2 ∧ secondSlot = 0 ∧ idir = 1) := by
  classical
  intro i₀ r g irot reverse idir firstSlot secondSlot
  have hi : idir = 0 ∨ idir = 1 ∨ idir = 2 := by omega
  rcases hi with hi | hi | hi <;> simp [firstSlot, secondSlot, hi]

private theorem hsigns :
    (by
      classical
      exact
        ∀ (e₀ : Bool), ∀ (g : BandPackingSymmetry), ∀ (negative : Bool),
        let reverse := BandPackingSymmetryReversesOrientation g
        let ebar : Bool := xor (xor e₀ negative) reverse
        let positive : Bool := !ebar
        let firstSign : Bool := positive
        let secondSign : Bool := !positive
        (positive = true ∧ firstSign = true ∧ secondSign = false) ∨ (positive = false ∧ firstSign
            = false ∧ secondSign = true) ) := by
  classical
  intro e₀ g negative reverse ebar positive firstSign secondSign
  rcases Bool.eq_false_or_eq_true positive with hp | hp <;>
    simp [firstSign, secondSign, hp]

private theorem hstarFootprint :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k : PartialOdometer), ∀
            (x : GaussianInt), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g
            : BandPackingSymmetry),
        let qrot : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let qbar := BandPackingSymmetryQuadrupleAction g qrot
        (TileOdometer (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryTileAction g T) (BandPackingSymmetryPartialOdometerAction g h)) →
            ((TileOdometer (BandPackingSymmetryQuadrupleAction g qrot (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryTileAction g N) (BandPackingSymmetryPartialOdometerAction g k)) → (
        let Tbar := BandPackingSymmetryTileAction g T
        let Nbar := BandPackingSymmetryTileAction g N
        let hbar := BandPackingSymmetryPartialOdometerAction g h
        let kbar := BandPackingSymmetryPartialOdometerAction g k
        let xbar := BandPackingSymmetryVectorAction g x
        (0 < (qbar 0).1) → ((∀ y, y = xbar ∨ y = xbar + 1 ∨ y = xbar - 1 ∨ y = xbar + ⟨0, 1⟩ ∨ y
            = xbar - ⟨0, 1⟩ → y ∈ hbar.domain ∨ y ∈ kbar.domain) → (∀ y, y = xbar ∨ y = xbar + 1
            ∨ y = xbar - 1 ∨ y = xbar + ⟨0, 1⟩ ∨ y = xbar - ⟨0, 1⟩ → y ∈ FootprintVertices Tbar ∨
            y ∈ FootprintVertices Nbar)))) ) := by
  classical
  intro T N h k x q r g qrot qbar hOTbar hONbar Tbar Nbar hbar kbar xbar hqbarPos hstarBarDomain
      y hy
  have hs := hstarBarDomain y hy
  have hdT := PositiveCurvatureTileOdometerDomain (qbar 0) Tbar hbar
    hqbarPos hOTbar
  have hdN := PositiveCurvatureTileOdometerDomain (qbar 0) Nbar kbar
    hqbarPos hONbar
  rcases hs with hs | hs
  · left
    exact (Set.ext_iff.mp hdT y).mp hs
  · right
    exact (Set.ext_iff.mp hdN y).mp hs

end RightNormalizationGeometry

theorem BandOrderedGeneralRightNormalizationCertificateExists
    (C : BandCircle) (T N : ProtoTile) (h k : PartialOdometer)
    (x : GaussianInt)
    (horbit :
      ¬ ((exists (g : BandPackingSymmetry) (P : FordFareyParameter),
              BandPackingSymmetryCircleAction g
                (FordCircleCoordinate P.p P.q) = C.1.1) \/
            (exists (g : BandPackingSymmetry) (K : DiamondParameter),
              BandPackingSymmetryCircleAction g
                (DiamondRecursiveQuadruple K 0) = C.1.1)))
    (hadj : RightLatticeAdjacent C T N h k)
    (hxT : x ∈ h.domain) (hxN : x ∈ k.domain)
    (hstar : forall y,
      y = x \/ y = x + 1 \/ y = x - 1 \/
        y = x + ⟨0, 1⟩ \/ y = x - ⟨0, 1⟩ ->
      y ∈ h.domain \/ y ∈ k.domain) :
    Nonempty (BandOrderedGeneralRightNormalizationCertificate C T N h k x) := by
-- BODY
  classical
  rcases hadj with
    ⟨hOT, hON, pT, pN, hpT, hpN, q, i₀, e₀, hq, hqC,
      hcent, hslopeRe, hslopeIm⟩
  obtain ⟨r, g, hregime⟩ := BandRegimeClassification q hq
  let qrot : Fin 4 → CircleCoordinates :=
    ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
  have hqrot := RightNormalizationGeometry.hqrot q hq r g hregime
      (RightNormalizationGeometry.hqrotSemi q hq r g hregime)
  let irot : Fin 3 := i₀ - r
  have hrotParent : qrot irot.succ = q i₀.succ := by
    fin_cases r <;> fin_cases i₀ <;> simp [qrot, irot]
  have hqrotC : qrot 0 = C.1.1 := by simpa [qrot] using hqC
  let qbar := BandPackingSymmetryQuadrupleAction g qrot
  have hqbar : ProperBandQuadruple qbar := by
    exact BandPackingSymmetryProperCovariance g qrot hqrot
  have hqbarC : qbar 0 = BandPackingSymmetryCircleAction g C.1.1 := by
    simp [qbar, qrot, BandPackingSymmetryQuadrupleAction, hqC]
  have hgeneral := RightNormalizationGeometry.hgeneral C horbit q hqC r g hregime
  obtain ⟨cfg⟩ := hgeneral
  have hOTrot : TileOdometer (qrot 0) T h := by rw [hqrotC]; exact hOT
  have hONrot : TileOdometer (qrot 0) N k := by rw [hqrotC]; exact hON
  have hcentRot := RightNormalizationGeometry.hcentRot T N q i₀ e₀ hcent r hrotParent
  have hslopeReRot := RightNormalizationGeometry.hslopeReRot pT
            pN q i₀ e₀ hslopeRe r hrotParent
  have hslopeImRot := RightNormalizationGeometry.hslopeImRot pT
            pN q i₀ e₀ hslopeIm r hrotParent
  obtain ⟨negative, pTbar, pNbar, hphase, hOTbar, hONbar,
      hpTbar, hpNbar, hcentBar, hslopeReBar, hslopeImBar, hcompatBar⟩ :=
    RightLatticeAdjacentPackingSymmetryTransport g qrot hqrot irot e₀
      T N h k pT pN hOTrot hONrot hpT hpN hcentRot hslopeReRot hslopeImRot
  let reverse := BandPackingSymmetryReversesOrientation g
  let idir : Fin 3 := if reverse then -irot else irot
  let ebar : Bool := xor (xor e₀ negative) reverse
  let positive : Bool := !ebar
  have hcentBar' := RightNormalizationGeometry.hcentBar' T N q i₀ e₀ r g negative hcentBar
  have hslopeReBar' := RightNormalizationGeometry.hslopeReBar' q
            i₀ e₀ r g negative pTbar pNbar hslopeReBar
  have hslopeImBar' := RightNormalizationGeometry.hslopeImBar' q
            i₀ e₀ r g negative pTbar pNbar hslopeImBar
  let Tbar := BandPackingSymmetryTileAction g T
  let Nbar := BandPackingSymmetryTileAction g N
  let hbar := BandPackingSymmetryPartialOdometerAction g h
  let kbar := BandPackingSymmetryPartialOdometerAction g k
  let xbar := BandPackingSymmetryVectorAction g x
  have hxTbar := RightNormalizationGeometry.hxTbar h k x hxT g
  have hxNbar := RightNormalizationGeometry.hxNbar h k x hxN g
  have hTbarBand : BandPrototile (qbar 0) Tbar :=
    TileOdometerBandPrototile _ _ _ hOTbar
  have hNbarBand : BandPrototile (qbar 0) Nbar :=
    TileOdometerBandPrototile _ _ _ hONbar
  have hTind := BandTileSimultaneousInduction qbar hqbar Tbar hTbarBand
  have hNind := BandTileSimultaneousInduction qbar hqbar Nbar hNbarBand
  have hsmallT1 := RightNormalizationGeometry.hsmallT1 q r g
  have hsmallT2 := RightNormalizationGeometry.hsmallT2 q r g
  have hsmallT4 := RightNormalizationGeometry.hsmallT4 q r g
  have hsmallT5 := RightNormalizationGeometry.hsmallT5 q r g
  have hqbarPos : 0 < (qbar 0).1 := (ProperBandCurvatureStructure qbar hqbar).1
  let Cbar : BandCircle :=
    ⟨⟨qbar 0, ⟨Or.inl hqbarPos, ⟨qbar, hqbar.1, ⟨0, rfl⟩⟩⟩⟩, hqbarPos⟩
  obtain ⟨layout⟩ := BandOrderedGeneralLayout qbar cfg Cbar
    rfl Nbar hNbarBand hsmallT1 hsmallT2 hsmallT4 hsmallT5
  obtain ⟨pieces, functions, hrootBand, hpieceOdometer, hpieceCells,
      hpieceFootprint, hpieceCentroid, hfunctionDomains,
      hfunctionRestriction, hfunctionCompatibility, hpieceSlope⟩ :=
    TileOdometerReindexedDecomposition qbar hqbar Tbar hbar
      (by linarith [cfg.childLarge]) hOTbar
  let displacement : GaussianInt :=
    (if positive = true then (1 : GaussianInt) else -1) *
      BandVectors.1 (qbar 0) (qbar idir.succ)
  have houterCentroid := RightNormalizationGeometry.houterCentroid T N q i₀ e₀ r g negative pTbar
      pNbar
          hcentBar' hslopeReBar' hslopeImBar'
  have htranslatedN :
      BandPrototile (qbar 0) (TileTranslation Nbar displacement) :=
    BandPrototileTranslation _ _ _ hNbarBand
  have houterUnique := BandPrototileCentroidUnique (qbar 0) Tbar
    (TileTranslation Nbar displacement) hTbarBand htranslatedN houterCentroid
  have hstarBarDomain : ∀ y,
      y = xbar ∨ y = xbar + 1 ∨ y = xbar - 1 ∨
        y = xbar + ⟨0, 1⟩ ∨ y = xbar - ⟨0, 1⟩ →
      y ∈ hbar.domain ∨ y ∈ kbar.domain :=
    P5658T1FivePointDomainCoverSymmetryCovariance g h k x hstar
  have boundaryData := RightNormalizationGeometry.boundaryData T N q i₀ e₀ r g hqbar cfg negative
      hqbarPos layout pieces functions hpieceOdometer hpieceCentroid houterCentroid
  let firstSlot : Fin 3 := idir + 1
  let secondSlot : Fin 3 := idir + 2
  let firstSign : Bool := positive
  let secondSign : Bool := !positive
  have hfirstData := boundaryData firstSlot firstSign
  have hsecondData := boundaryData secondSlot secondSign
  refine ⟨{
    presentation := q
    presentation_proper := hq
    presentation_child := hqC
    parentRotation := r
    symmetry := g
    rotatedPresentation := qrot
    rotated_presentation_eq := rfl
    normalizedPresentation := qbar
    normalized_presentation_eq := rfl
    configuration := cfg
    normalizedCircle := Cbar
    normalized_circle_eq := rfl
    normalizedFixedCircle := Cbar
    normalized_fixed_circle_eq := hqbarC
    normalizedRoot := Tbar
    normalizedFixed := Nbar
    normalizedRootFunction := hbar
    normalizedFixedFunction := kbar
    normalizedPoint := xbar
    normalized_root_eq := rfl
    normalized_fixed_eq := rfl
    normalized_root_function_eq := rfl
    normalized_fixed_function_eq := rfl
    normalized_point_eq := rfl
    normalized_point_root_domain := hxTbar
    normalized_point_fixed_domain := hxNbar
    normalized_root_odometer := hOTbar
    normalized_fixed_odometer := hONbar
    normalized_root_lattice := hTind.1
    normalized_fixed_lattice := hNind.1
    normalizedRootSlope := pTbar
    normalizedFixedSlope := pNbar
    normalized_root_slope := hpTbar
    normalized_fixed_slope := hpNbar
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
    adjacency := (RightNormalizationGeometry.hadjbar T N h k q i₀ e₀ r g hqbar negative pTbar
        pNbar hOTbar hONbar hpTbar hpNbar hcentBar hslopeReBar hslopeImBar hqbarPos)
    layout := layout
    fixed_quarter_turn := hNind.2.2.2.1
    rightFirstSlot := firstSlot
    rightSecondSlot := secondSlot
    rightDirectionSlot := idir
    right_slots_cyclic := (RightNormalizationGeometry.cyclicSlots i₀ r g)
    rightNeighborPositive := positive
    right_adjacency_centroid := hcentBar'
    right_adjacency_slope_real := hslopeReBar'
    right_adjacency_slope_imag := hslopeImBar'
    rightNeighborDisplacement := displacement
    right_neighbor_displacement := rfl
    right_neighbor_cells := houterUnique.1
    right_neighbor_empty_anchor := houterUnique.2
    firstBoundarySign := firstSign
    secondBoundarySign := secondSign
    boundary_signs := (RightNormalizationGeometry.hsigns e₀ g negative)
    first_boundary_cells := hfirstData.1
    first_boundary_empty_anchor := hfirstData.2.1
    first_boundary_footprint := hfirstData.2.2.1
    first_boundary_domain := hfirstData.2.2.2
    second_boundary_cells := hsecondData.1
    second_boundary_empty_anchor := hsecondData.2.1
    second_boundary_footprint := hsecondData.2.2.1
    second_boundary_domain := hsecondData.2.2.2
    normalized_star := (RightNormalizationGeometry.hstarFootprint T N h k x q r g hOTbar hONbar
        hqbarPos hstarBarDomain) }⟩

end ApollonianSuperharmonic

end
