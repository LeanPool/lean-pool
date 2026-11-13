/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurnTranslation

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSubtileInterfaceCertificate
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSubtileCanonicalRows
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSubtileCanonicalSeparation
public import LeanPool.ApollonianSuperharmonic.BandTileSimultaneousInduction
public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTripleRetargetMiddle
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile


-- [TABLET NODE: BandOrderedGeneralSubtileInterfaceCertificateExists]

/-!
# BandOrderedGeneralSubtileInterfaceCertificateExists

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

private def subtileOccurrenceLabel (j : Fin 3) (e : Bool) : SixSubtileLabel :=
  match j, e with
  | 0, true => .A
  | 0, false => .B
  | 1, true => .C
  | 1, false => .D
  | 2, true => .E
  | 2, false => .F

namespace SubtileInterfaceGeometry

private theorem quarterSymmetricTranslation (A : ProtoTile) (d : GaussianInt)
    (h : QuarterTurnSymmetric A) : QuarterTurnSymmetric (TileTranslation A d) := by
  classical
  intro p
  rw [(TileTranslationFormulas A d).2.2.2.1,
    (TileTranslationFormulas A d).2.2.2.2.1]
  simp only [Set.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' := (h y).mp hy
    refine ⟨((TileCentroid A).1 - (y.2 - (TileCentroid A).2),
      (TileCentroid A).2 + (y.1 - (TileCentroid A).1)), hy', ?_⟩
    apply Prod.ext <;> dsimp <;> ring
  · rintro ⟨y, hy, heq⟩
    let z : Real × Real := (p.1 - d.re, p.2 - d.im)
    refine ⟨z, ?_, ?_⟩
    · apply (h z).mpr
      convert hy using 1
      apply Prod.ext <;>
        have hcoord := congrArg (fun w => w.1) heq <;>
        have hcoord2 := congrArg (fun w => w.2) heq <;>
        dsimp [z] at hcoord hcoord2 ⊢ <;> linarith
    · apply Prod.ext <;> dsimp [z] <;> ring

private theorem centeredCompare (g : GaussianInt) (C : CircleCoordinates) (Y Z : ProtoTile)
    (hY : BandPrototile C Y) (hZ : BandPrototile C Z)
    (hsym : QuarterTurnSymmetric Y)
    (hcent : TileCentroid (TileTranslation (TileQuarterTurn Y) g) =
      TileCentroid Z) :
    (TileTranslation (TileQuarterTurn Y) g).cells = Z.cells ∧
      ((TileTranslation (TileQuarterTurn Y) g).cells = ∅ →
        (TileTranslation (TileQuarterTurn Y) g).anchor = Z.anchor) := by
  classical
  obtain ⟨k, hkreal, hkcells, hkanchor, hkfoot, hkcent⟩ :=
    QuarterTurnSymmetricCenteredTransport Y hsym
  let Ytr := TileTranslation Y (g - k)
  have htrband : BandPrototile C Ytr :=
    BandPrototileTranslation C Y (g - k) hY
  have hcells : (TileTranslation (TileQuarterTurn Y) g).cells = Ytr.cells := by
    dsimp [Ytr]
    rw [(TileTranslationFormulas (TileQuarterTurn Y) g).1,
      (TileTranslationFormulas Y (g - k)).1]
    ext z
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have hy : GaussianTranslation k a ∈ Y.cells := by
        rw [← hkcells, (TileTranslationFormulas (TileQuarterTurn Y) k).1]
        exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
      refine ⟨GaussianTranslation k a, hy, ?_⟩
      apply Zsqrtd.ext <;> simp [GaussianTranslation]
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ∈ (TileTranslation (TileQuarterTurn Y) k).cells := by
        rw [hkcells]
        exact hy
      rw [(TileTranslationFormulas (TileQuarterTurn Y) k).1] at hy'
      obtain ⟨a, ha, hay⟩ := Finset.mem_image.mp hy'
      refine ⟨a, ha, ?_⟩
      have hre := congrArg (fun z : GaussianInt => z.re) hay
      have him := congrArg (fun z : GaussianInt => z.im) hay
      apply Zsqrtd.ext <;>
        simp [GaussianTranslation] at hre him ⊢ <;> omega
  have hanchor : (TileTranslation (TileQuarterTurn Y) g).cells = ∅ →
      (TileTranslation (TileQuarterTurn Y) g).anchor = Ytr.anchor := by
    intro he
    have hkempty : (TileTranslation (TileQuarterTurn Y) k).cells = ∅ := by
      rw [hkcells]
      rw [hcells] at he
      exact (TileTranslationFormulas Y (g - k)).2.2.1.mp he
    have hyempty := (TileQuarterTurnFormulas Y).2.2.1.mp
      ((TileTranslationFormulas (TileQuarterTurn Y) k).2.2.1.mp hkempty)
    have ha := hkanchor hyempty
    dsimp [Ytr]
    calc
      (TileTranslation (TileQuarterTurn Y) g).anchor =
          GaussianTranslation (g - k)
            (TileTranslation (TileQuarterTurn Y) k).anchor := by
        apply Zsqrtd.ext <;>
          simp [TileTranslation, TileQuarterTurn, GaussianTranslation,
            GaussianQuarterTurn]
      _ = GaussianTranslation (g - k) Y.anchor := by rw [ha]
      _ = (TileTranslation Y (g - k)).anchor := rfl
  have hobs := ProtoTileObservableExtensionality
    (TileTranslation (TileQuarterTurn Y) g) Ytr hcells hanchor
  have hunique := BandPrototileCentroidUnique C Ytr Z htrband hZ
    (hobs.2.2.2.2.symm.trans hcent)
  exact ⟨hcells.trans hunique.1, fun he =>
    (hanchor he).trans (hunique.2 (hcells.symm.trans he))⟩

end SubtileInterfaceGeometry

namespace SubtileInterfacePreparation

private theorem hin1 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin
            3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralSubtileNormalizationCertificate C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x),
        let Q := normalization.normalizedPresentation
        let edge : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (Q ((j + 2).succ)) (Q ((j + 1).succ))
        let incoming : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (Q j.succ) (Q 0)
        let R : Fin 4 → CircleCoordinates := ![Q 0, Q 2, Q 3, Q 1]
        (SemiProperQuadruple R) → (incoming 1 = edge 2 - (⟨0, 1⟩ : GaussianInt) * edge 0) ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization Q edge incoming R hR
  simpa [incoming, edge, R] using (VectorRecursionLaws R hR).2.2.1

private theorem hin2 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin
            3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralSubtileNormalizationCertificate C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x),
        let Q := normalization.normalizedPresentation
        let edge : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (Q ((j + 2).succ)) (Q ((j + 1).succ))
        let incoming : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (Q j.succ) (Q 0)
        let R : Fin 4 → CircleCoordinates := ![Q 0, Q 2, Q 3, Q 1]
        let S : Fin 4 → CircleCoordinates := ![R 0, R 2, R 3, R 1]
        (SemiProperQuadruple S) → (incoming 2 = edge 0 - (⟨0, 1⟩ : GaussianInt) * edge 1) ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization Q edge incoming R S hS
  simpa [incoming, edge, R, S] using (VectorRecursionLaws S hS).2.2.1

private theorem hOA :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin
            3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralSubtileNormalizationCertificate C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x),
            normalization.layout.O.cells ⊆ (normalization.layout.P 0 true).cells ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization z hz
  apply (normalization.layout.plus_union z).2
  exact ⟨0, false, by simpa [normalization.layout.precursor_eq] using hz⟩

private theorem hOB :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin
            3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralSubtileNormalizationCertificate C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x),
            normalization.layout.O.cells ⊆ (normalization.layout.P 0 false).cells ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization z hz
  apply (normalization.layout.minus_union z).2
  exact ⟨0, true, by simpa [normalization.layout.precursor_cells] using hz⟩

private theorem occurrenceBand :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin
            3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralSubtileNormalizationCertificate C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x),
        let Q := normalization.normalizedPresentation
        ∀ (j : Fin 3), ∀ (e : Bool), ∀ (m : Int), ∀ (n : Int), BandPrototile (Q j.succ)
            (SubtileOccurrenceInterpretation normalization.layout.P normalization.layout.u
            normalization.layout.v ⟨subtileOccurrenceLabel j e, m, n⟩) ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization Q j e m n
  fin_cases j <;> cases e <;>
    simp only [Fin.mk_one, Fin.isValue, Fin.succ_one_eq_two, SubtileOccurrenceInterpretation,
        subtileOccurrenceLabel, Q, Fin.reduceFinMk, Fin.reduceSucc, Fin.zero_eta,
        Fin.succ_zero_eq_one]
  all_goals first
    | exact BandPrototileTranslation _ _ _
        (normalization.layout.outer_occurrence 0 false).1
    | exact BandPrototileTranslation _ _ _
        (normalization.layout.outer_occurrence 0 true).1
    | exact BandPrototileTranslation _ _ _
        (normalization.layout.outer_occurrence 1 false).1
    | exact BandPrototileTranslation _ _ _
        (normalization.layout.outer_occurrence 1 true).1
    | exact BandPrototileTranslation _ _ _
        (normalization.layout.outer_occurrence 2 false).1
    | exact BandPrototileTranslation _ _ _
        (normalization.layout.outer_occurrence 2 true).1

private theorem rotatedCentroid :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin
            3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralSubtileNormalizationCertificate C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x), ∀ (g :
            GaussianInt), (GaussianRealPoint g = ((TileCentroid normalization.normalizedRoot).1 +
            (TileCentroid normalization.normalizedRoot).2, (TileCentroid
            normalization.normalizedRoot).2 - (TileCentroid normalization.normalizedRoot).1)) →
            (∀ (Y : ProtoTile), ∀ (Z : ProtoTile), ∀ (z : GaussianInt), (TileCentroid Y -
            TileCentroid normalization.normalizedRoot =
            (1 / 2 : Real) • GaussianRealPoint z) → ((TileCentroid Z - TileCentroid
                normalization.normalizedRoot =
            (1 / 2 : Real) •
              GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) * z)) → (TileCentroid (TileTranslation
                  (TileQuarterTurn Y) g) = TileCentroid Z))) ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization g hg Y Z z hY hZ
  rw [(TileTranslationFormulas (TileQuarterTurn Y) g).2.2.2.2.1,
    (TileQuarterTurnFormulas Y).2.2.2.2.1]
  have hgre := congrArg Prod.fst hg
  have hgim := congrArg Prod.snd hg
  dsimp [GaussianRealPoint] at hgre hgim
  rw [Prod.ext_iff] at hY hZ ⊢
  rcases hY with ⟨hYre, hYim⟩
  rcases hZ with ⟨hZre, hZim⟩
  norm_num only [GaussianRealPoint, Prod.fst_sub, Prod.snd_sub,
    Prod.smul_fst, Prod.smul_snd] at hYre hYim hZre hZim ⊢
  norm_num at hZre hZim
  rw [← GaussianInt.intCast_im z] at hZre
  rw [← GaussianInt.intCast_re z] at hZim
  dsimp at hgre hgim hYre hYim hZre hZim ⊢
  constructor <;> linarith

private theorem hout0 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin
            3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralSubtileNormalizationCertificate C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x),
        let Q := normalization.normalizedPresentation
        let incoming : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (Q j.succ) (Q 0)
        (∀ (j : Fin (3 : ℕ)), BandVectors.1 (Q (0 : Fin (4 : ℕ))) (Q j.succ) = (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) * BandVectors.1 (Q j.succ) (Q (0 : Fin (4 : ℕ))) ∧ BandVectors.2
            (Q (0 : Fin (4 : ℕ))) (Q j.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.2 (Q j.succ) (Q (0 : Fin (4 : ℕ)))) → ((⟨0, 1⟩ : GaussianInt) * incoming
            0 = normalization.layout.u) ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization Q incoming hflips
  rw [← (hflips 0).1]
  simpa [Q] using normalization.layout.period_u.symm

private theorem hout1 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin
            3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralSubtileNormalizationCertificate C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x),
        let Q := normalization.normalizedPresentation
        let incoming : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (Q j.succ) (Q 0)
        (∀ (j : Fin (3 : ℕ)), BandVectors.1 (Q (0 : Fin (4 : ℕ))) (Q j.succ) = (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) * BandVectors.1 (Q j.succ) (Q (0 : Fin (4 : ℕ))) ∧ BandVectors.2
            (Q (0 : Fin (4 : ℕ))) (Q j.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.2 (Q j.succ) (Q (0 : Fin (4 : ℕ)))) → ((⟨0, 1⟩ : GaussianInt) * incoming
            1 = normalization.layout.v) ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization Q incoming hflips
  rw [← (hflips 1).1]
  simpa [Q] using normalization.layout.period_v.symm

private theorem hout2 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin
            3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralSubtileNormalizationCertificate C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x),
        let Q := normalization.normalizedPresentation
        let edge : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (Q ((j + 2).succ)) (Q ((j + 1).succ))
        let incoming : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (Q j.succ) (Q 0)
        (BandVectors.1 (Q (3 : Fin (4 : ℕ))) (Q (2 : Fin (4 : ℕ))) + BandVectors.1 (Q (1 : Fin (4
            : ℕ))) (Q (3 : Fin (4 : ℕ))) + BandVectors.1 (Q (2 : Fin (4 : ℕ))) (Q (1 : Fin (4 :
            ℕ))) = (0 : GaussianInt)) → ((BandVectors.1 (Q (1 : Fin (4 : ℕ))) (Q (0 : Fin (4 :
            ℕ))) = BandVectors.1 (Q (1 : Fin (4 : ℕ))) (Q (3 : Fin (4 : ℕ))) - (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) * BandVectors.1 (Q (2 : Fin (4 : ℕ))) (Q (1 : Fin (4 : ℕ)))) →
            ((incoming 1 = edge 2 - (⟨0, 1⟩ : GaussianInt) * edge 0) → ((incoming 2 = edge 0 -
            (⟨0, 1⟩ : GaussianInt) * edge 1) → (((⟨0, 1⟩ : GaussianInt) * incoming 0 =
            normalization.layout.u) → (((⟨0, 1⟩ : GaussianInt) * incoming 1 =
            normalization.layout.v) → ((⟨0, 1⟩ : GaussianInt) * incoming 2 =
            -normalization.layout.u - normalization.layout.v)))))) ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization Q edge incoming hsuper hin0 hin1 hin2 hout0 hout1
  have hsum : (⟨0, 1⟩ : GaussianInt) * incoming 0 +
      (⟨0, 1⟩ : GaussianInt) * incoming 1 +
      (⟨0, 1⟩ : GaussianInt) * incoming 2 = 0 := by
    have hs : edge 0 + edge 1 + edge 2 = 0 := by
      simpa [edge] using hsuper
    rw [show incoming 0 = edge 1 - (⟨0, 1⟩ : GaussianInt) * edge 2 from hin0,
      show incoming 1 = edge 2 - (⟨0, 1⟩ : GaussianInt) * edge 0 from hin1,
      show incoming 2 = edge 0 - (⟨0, 1⟩ : GaussianInt) * edge 1 from hin2]
    calc
      (⟨0, 1⟩ : GaussianInt) *
            (edge 1 - (⟨0, 1⟩ : GaussianInt) * edge 2) +
          (⟨0, 1⟩ : GaussianInt) *
            (edge 2 - (⟨0, 1⟩ : GaussianInt) * edge 0) +
          (⟨0, 1⟩ : GaussianInt) *
            (edge 0 - (⟨0, 1⟩ : GaussianInt) * edge 1) =
          (1 + (⟨0, 1⟩ : GaussianInt)) *
            (edge 0 + edge 1 + edge 2) := by
        apply Zsqrtd.ext <;> simp <;> ring
      _ = 0 := by rw [hs]; ring
  rw [← hout0, ← hout1]
  linear_combination hsum

private theorem quarterPower :
    (by
      classical
      exact
        ∀ (t : Fin 4), ∀ (z : GaussianInt), (⟨0, 1⟩ : GaussianInt) ^ (t + 1).val * z = (⟨0, 1⟩ :
            GaussianInt) * ((⟨0, 1⟩ : GaussianInt) ^ t.val * z) ) := by
  classical
  intro t z
  fin_cases t <;> apply Zsqrtd.ext <;>
    simp [Fin.add_def, pow_succ]

private theorem quarterTurnMul :
    (by
      classical
      exact
        ∀ (z : GaussianInt), GaussianQuarterTurn z = (⟨0, 1⟩ : GaussianInt) * z ) := by
  classical
  intro z
  apply Zsqrtd.ext <;> simp [GaussianQuarterTurn]

end SubtileInterfacePreparation

namespace SubtileInterfaceAssembly

private theorem transportedEndpoints {A B B' C : ProtoTile} (h : B = B')
    (data : ExactTileInterfaceTriple A B' C) :
    (h.symm ▸ data).point = data.point ∧ (h.symm ▸ data).otherCA = data.otherCA := by
  cases h
  exact ⟨rfl, rfl⟩


private theorem hUBand :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin
            3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralSubtileNormalizationCertificate C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x),
        let Q := normalization.normalizedPresentation
        let uIndex : PeriodicSubtileIndex :=
          if normalization.normalizedParentSlot = 0 then
            if normalization.normalizedQuarterTurn = 0 then ⟨.A, 0, -1⟩
            else if normalization.normalizedQuarterTurn = 1 then ⟨.B, 1, 1⟩
            else if normalization.normalizedQuarterTurn = 2 then ⟨.B, 0, 1⟩
            else ⟨.A, -1, -1⟩
          else if normalization.normalizedParentSlot = 1 then
            if normalization.normalizedQuarterTurn = 0 then ⟨.C, 1, 1⟩
            else if normalization.normalizedQuarterTurn = 1 then ⟨.D, -1, 0⟩
            else if normalization.normalizedQuarterTurn = 2 then ⟨.D, -1, -1⟩
            else ⟨.C, 1, 0⟩
          else if normalization.normalizedQuarterTurn = 0 then ⟨.E, -1, 0⟩
          else if normalization.normalizedQuarterTurn = 1 then ⟨.F, 0, -1⟩
          else if normalization.normalizedQuarterTurn = 2 then ⟨.F, 1, 0⟩
          else ⟨.E, 0, 1⟩
        let U := SubtileOccurrenceInterpretation normalization.layout.P
          normalization.layout.u normalization.layout.v uIndex
        BandPrototile (Q normalization.normalizedParentSlot.succ) U ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization Q uIndex U
  generalize hp : normalization.normalizedParentSlot = p
  generalize ht : normalization.normalizedQuarterTurn = t
  fin_cases p <;> fin_cases t <;>
    simp only [Fin.mk_one, Fin.isValue, Fin.succ_one_eq_two, SubtileOccurrenceInterpretation,
        hp, one_ne_zero, ↓reduceIte, ht, Fin.reduceFinMk, Fin.reduceEq, Int.cast_one, one_mul,
        Int.cast_zero, zero_mul, add_zero, Q, U, uIndex, Int.reduceNeg, Int.cast_neg, neg_mul,
        Fin.zero_eta, Fin.reduceSucc, zero_add, Fin.succ_zero_eq_one]
  all_goals first
    | exact BandPrototileTranslation _ _ _
        (normalization.layout.outer_occurrence 0 true).1
    | exact BandPrototileTranslation _ _ _
        (normalization.layout.outer_occurrence 0 false).1
    | exact BandPrototileTranslation _ _ _
        (normalization.layout.outer_occurrence 1 true).1
    | exact BandPrototileTranslation _ _ _
        (normalization.layout.outer_occurrence 1 false).1
    | exact BandPrototileTranslation _ _ _
        (normalization.layout.outer_occurrence 2 true).1
    | exact BandPrototileTranslation _ _ _
        (normalization.layout.outer_occurrence 2 false).1

private theorem hVBand :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin
            3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralSubtileNormalizationCertificate C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x),
        let Q := normalization.normalizedPresentation
        let vIndex : PeriodicSubtileIndex :=
          if normalization.normalizedParentSlot = 0 then
            if normalization.normalizedQuarterTurn = 0 then ⟨.C, 1, 0⟩
            else if normalization.normalizedQuarterTurn = 1 then ⟨.F, 1, 0⟩
            else if normalization.normalizedQuarterTurn = 2 then ⟨.D, -1, 0⟩
            else ⟨.E, -1, 0⟩
          else if normalization.normalizedParentSlot = 1 then
            if normalization.normalizedQuarterTurn = 0 then ⟨.E, 0, 1⟩
            else if normalization.normalizedQuarterTurn = 1 then ⟨.B, 0, 1⟩
            else if normalization.normalizedQuarterTurn = 2 then ⟨.F, 0, -1⟩
            else ⟨.A, 0, -1⟩
          else if normalization.normalizedQuarterTurn = 0 then ⟨.A, -1, -1⟩
          else if normalization.normalizedQuarterTurn = 1 then ⟨.D, -1, -1⟩
          else if normalization.normalizedQuarterTurn = 2 then ⟨.B, 1, 1⟩
          else ⟨.C, 1, 1⟩
        let V := SubtileOccurrenceInterpretation normalization.layout.P
          normalization.layout.u normalization.layout.v vIndex
        BandPrototile (Q ((if Even normalization.normalizedQuarterTurn.val then
            normalization.normalizedParentSlot + 1 else normalization.normalizedParentSlot -
            1).succ)) V ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization Q vIndex V
  generalize hp : normalization.normalizedParentSlot = p
  generalize ht : normalization.normalizedQuarterTurn = t
  fin_cases p <;> fin_cases t <;>
    simp only [Even.zero, ↓reduceIte, Fin.mk_one, Fin.isValue, Fin.reduceAdd, Fin.reduceSucc,
        SubtileOccurrenceInterpretation, hp, one_ne_zero, ht, Fin.zero_eta, Int.cast_zero,
        zero_mul, Int.cast_one, one_mul, zero_add, V, vIndex, Fin.reduceFinMk,
        Fin.succ_zero_eq_one, Fin.reduceEq, Int.reduceNeg, Int.cast_neg, neg_mul,
        Fin.succ_one_eq_two, add_zero, sub_self, Fin.reduceSub, zero_sub, Nat.not_even_one,
        even_two] <;>
    first
    | exact BandPrototileTranslation _ _ _
        (normalization.layout.outer_occurrence 0 true).1
    | exact BandPrototileTranslation _ _ _
        (normalization.layout.outer_occurrence 0 false).1
    | exact BandPrototileTranslation _ _ _
        (normalization.layout.outer_occurrence 1 true).1
    | exact BandPrototileTranslation _ _ _
        (normalization.layout.outer_occurrence 1 false).1
    | exact BandPrototileTranslation _ _ _
        (normalization.layout.outer_occurrence 2 true).1
    | exact BandPrototileTranslation _ _ _
        (normalization.layout.outer_occurrence 2 false).1

private theorem hUSym :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin
            3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralSubtileNormalizationCertificate C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x), (∀ (A :
            ProtoTile), ∀ (d : GaussianInt), (QuarterTurnSymmetric A) → (QuarterTurnSymmetric
            (TileTranslation A d))) → (
        let uIndex : PeriodicSubtileIndex :=
          if normalization.normalizedParentSlot = 0 then
            if normalization.normalizedQuarterTurn = 0 then ⟨.A, 0, -1⟩
            else if normalization.normalizedQuarterTurn = 1 then ⟨.B, 1, 1⟩
            else if normalization.normalizedQuarterTurn = 2 then ⟨.B, 0, 1⟩
            else ⟨.A, -1, -1⟩
          else if normalization.normalizedParentSlot = 1 then
            if normalization.normalizedQuarterTurn = 0 then ⟨.C, 1, 1⟩
            else if normalization.normalizedQuarterTurn = 1 then ⟨.D, -1, 0⟩
            else if normalization.normalizedQuarterTurn = 2 then ⟨.D, -1, -1⟩
            else ⟨.C, 1, 0⟩
          else if normalization.normalizedQuarterTurn = 0 then ⟨.E, -1, 0⟩
          else if normalization.normalizedQuarterTurn = 1 then ⟨.F, 0, -1⟩
          else if normalization.normalizedQuarterTurn = 2 then ⟨.F, 1, 0⟩
          else ⟨.E, 0, 1⟩
        let U := SubtileOccurrenceInterpretation normalization.layout.P
          normalization.layout.u normalization.layout.v uIndex
        QuarterTurnSymmetric U) ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization quarterSymmetricTranslation uIndex U
  generalize hp : normalization.normalizedParentSlot = p
  generalize ht : normalization.normalizedQuarterTurn = t
  fin_cases p <;> fin_cases t <;>
    simp only [SubtileOccurrenceInterpretation, hp, Fin.mk_one, Fin.isValue, one_ne_zero,
        ↓reduceIte, ht, Fin.reduceFinMk, Fin.reduceEq, Int.cast_one, one_mul, Int.cast_zero,
        zero_mul, add_zero, U, uIndex, Int.reduceNeg, Int.cast_neg, neg_mul, Fin.zero_eta,
        zero_add] <;>
    apply quarterSymmetricTranslation <;>
    first
    | exact normalization.layout.parent_quarter_turn 0 true
    | exact normalization.layout.parent_quarter_turn 0 false
    | exact normalization.layout.parent_quarter_turn 1 true
    | exact normalization.layout.parent_quarter_turn 1 false
    | exact normalization.layout.parent_quarter_turn 2 true
    | exact normalization.layout.parent_quarter_turn 2 false

private theorem hFixedBand :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin
            3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralSubtileNormalizationCertificate C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x),
        let Q := normalization.normalizedPresentation
        BandPrototile (Q normalization.normalizedParentSlot.succ) normalization.normalizedFixed )
            := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization Q
  rw [show Q normalization.normalizedParentSlot.succ =
      normalization.normalizedFixedCircle.1.1 by
    simpa [Q] using normalization.normalized_parent_coordinate]
  exact TileOdometerBandPrototile _ _ _ normalization.normalized_fixed_odometer

private theorem hfixedCent :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin
            3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralSubtileNormalizationCertificate C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x),
        let Q := normalization.normalizedPresentation
        let incoming : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (Q j.succ) (Q 0)
        let outgoing : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (Q 0) (Q j.succ)
        TileCentroid normalization.normalizedFixed - TileCentroid normalization.normalizedRoot =
            (1 / 2 : Real) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^
            normalization.normalizedQuarterTurn.val * (incoming
            normalization.normalizedParentSlot + outgoing normalization.normalizedParentSlot)) )
            := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization Q incoming outgoing
  simpa [Q, incoming, outgoing] using normalization.normalized_adjacency_centroid

private theorem hrow' :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin
            3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralSubtileNormalizationCertificate C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x),
        let uIndex : PeriodicSubtileIndex :=
          if normalization.normalizedParentSlot = 0 then
            if normalization.normalizedQuarterTurn = 0 then ⟨.A, 0, -1⟩
            else if normalization.normalizedQuarterTurn = 1 then ⟨.B, 1, 1⟩
            else if normalization.normalizedQuarterTurn = 2 then ⟨.B, 0, 1⟩
            else ⟨.A, -1, -1⟩
          else if normalization.normalizedParentSlot = 1 then
            if normalization.normalizedQuarterTurn = 0 then ⟨.C, 1, 1⟩
            else if normalization.normalizedQuarterTurn = 1 then ⟨.D, -1, 0⟩
            else if normalization.normalizedQuarterTurn = 2 then ⟨.D, -1, -1⟩
            else ⟨.C, 1, 0⟩
          else if normalization.normalizedQuarterTurn = 0 then ⟨.E, -1, 0⟩
          else if normalization.normalizedQuarterTurn = 1 then ⟨.F, 0, -1⟩
          else if normalization.normalizedQuarterTurn = 2 then ⟨.F, 1, 0⟩
          else ⟨.E, 0, 1⟩
        let vIndex : PeriodicSubtileIndex :=
          if normalization.normalizedParentSlot = 0 then
            if normalization.normalizedQuarterTurn = 0 then ⟨.C, 1, 0⟩
            else if normalization.normalizedQuarterTurn = 1 then ⟨.F, 1, 0⟩
            else if normalization.normalizedQuarterTurn = 2 then ⟨.D, -1, 0⟩
            else ⟨.E, -1, 0⟩
          else if normalization.normalizedParentSlot = 1 then
            if normalization.normalizedQuarterTurn = 0 then ⟨.E, 0, 1⟩
            else if normalization.normalizedQuarterTurn = 1 then ⟨.B, 0, 1⟩
            else if normalization.normalizedQuarterTurn = 2 then ⟨.F, 0, -1⟩
            else ⟨.A, 0, -1⟩
          else if normalization.normalizedQuarterTurn = 0 then ⟨.A, -1, -1⟩
          else if normalization.normalizedQuarterTurn = 1 then ⟨.D, -1, -1⟩
          else if normalization.normalizedQuarterTurn = 2 then ⟨.B, 1, 1⟩
          else ⟨.C, 1, 1⟩
        let uBar : PeriodicSubtileIndex :=
          if normalization.normalizedParentSlot = 0 then
            if normalization.normalizedQuarterTurn = 0 then ⟨.B, 1, 1⟩
            else if normalization.normalizedQuarterTurn = 1 then ⟨.B, 0, 1⟩
            else if normalization.normalizedQuarterTurn = 2 then ⟨.A, -1, -1⟩
            else ⟨.A, 0, -1⟩
          else if normalization.normalizedParentSlot = 1 then
            if normalization.normalizedQuarterTurn = 0 then ⟨.D, -1, 0⟩
            else if normalization.normalizedQuarterTurn = 1 then ⟨.D, -1, -1⟩
            else if normalization.normalizedQuarterTurn = 2 then ⟨.C, 1, 0⟩
            else ⟨.C, 1, 1⟩
          else if normalization.normalizedQuarterTurn = 0 then ⟨.F, 0, -1⟩
          else if normalization.normalizedQuarterTurn = 1 then ⟨.F, 1, 0⟩
          else if normalization.normalizedQuarterTurn = 2 then ⟨.E, 0, 1⟩
          else ⟨.E, -1, 0⟩
        let vBar : PeriodicSubtileIndex :=
          if normalization.normalizedParentSlot = 0 then
            if normalization.normalizedQuarterTurn = 0 then ⟨.C, 1, 1⟩
            else if normalization.normalizedQuarterTurn = 1 then ⟨.E, 0, 1⟩
            else if normalization.normalizedQuarterTurn = 2 then ⟨.D, -1, -1⟩
            else ⟨.F, 0, -1⟩
          else if normalization.normalizedParentSlot = 1 then
            if normalization.normalizedQuarterTurn = 0 then ⟨.E, -1, 0⟩
            else if normalization.normalizedQuarterTurn = 1 then ⟨.A, -1, -1⟩
            else if normalization.normalizedQuarterTurn = 2 then ⟨.F, 1, 0⟩
            else ⟨.B, 1, 1⟩
          else if normalization.normalizedQuarterTurn = 0 then ⟨.A, 0, -1⟩
          else if normalization.normalizedQuarterTurn = 1 then ⟨.C, 1, 0⟩
          else if normalization.normalizedQuarterTurn = 2 then ⟨.B, 0, 1⟩
          else ⟨.D, -1, 0⟩
        let wBlock : Int × Int :=
          if normalization.normalizedParentSlot = 0 then
            if normalization.normalizedQuarterTurn = 0 ∨
                normalization.normalizedQuarterTurn = 3 then (1, 0) else (-1, 0)
          else if normalization.normalizedParentSlot = 1 then
            if normalization.normalizedQuarterTurn = 0 ∨
                normalization.normalizedQuarterTurn = 3 then (0, 1) else (0, -1)
          else if normalization.normalizedQuarterTurn = 0 ∨
              normalization.normalizedQuarterTurn = 3 then (-1, -1) else (1, 1)
        ((normalization.normalizedParentSlot = 0 ∧ normalization.normalizedQuarterTurn = 0 ∧
            uIndex = ⟨.A, 0, -1⟩ ∧ uBar = ⟨.B, 1, 1⟩ ∧ wBlock = (1, 0) ∧ vIndex = ⟨.C, 1, 0⟩ ∧
            vBar = ⟨.C, 1, 1⟩) ∨ (normalization.normalizedParentSlot = 0 ∧
            normalization.normalizedQuarterTurn = 1 ∧ uIndex = ⟨.B, 1, 1⟩ ∧ uBar = ⟨.B, 0, 1⟩ ∧
            wBlock = (-1, 0) ∧ vIndex = ⟨.F, 1, 0⟩ ∧ vBar = ⟨.E, 0, 1⟩) ∨
            (normalization.normalizedParentSlot = 0 ∧ normalization.normalizedQuarterTurn = 2 ∧
            uIndex = ⟨.B, 0, 1⟩ ∧ uBar = ⟨.A, -1, -1⟩ ∧ wBlock = (-1, 0) ∧ vIndex = ⟨.D, -1, 0⟩ ∧
            vBar = ⟨.D, -1, -1⟩) ∨ (normalization.normalizedParentSlot = 0 ∧
            normalization.normalizedQuarterTurn = 3 ∧ uIndex = ⟨.A, -1, -1⟩ ∧ uBar = ⟨.A, 0, -1⟩
            ∧ wBlock = (1, 0) ∧ vIndex = ⟨.E, -1, 0⟩ ∧ vBar = ⟨.F, 0, -1⟩) ∨
            (normalization.normalizedParentSlot = 1 ∧ normalization.normalizedQuarterTurn = 0 ∧
            uIndex = ⟨.C, 1, 1⟩ ∧ uBar = ⟨.D, -1, 0⟩ ∧ wBlock = (0, 1) ∧ vIndex = ⟨.E, 0, 1⟩ ∧
            vBar = ⟨.E, -1, 0⟩) ∨ (normalization.normalizedParentSlot = 1 ∧
            normalization.normalizedQuarterTurn = 1 ∧ uIndex = ⟨.D, -1, 0⟩ ∧ uBar = ⟨.D, -1, -1⟩
            ∧ wBlock = (0, -1) ∧ vIndex = ⟨.B, 0, 1⟩ ∧ vBar = ⟨.A, -1, -1⟩) ∨
            (normalization.normalizedParentSlot = 1 ∧ normalization.normalizedQuarterTurn = 2 ∧
            uIndex = ⟨.D, -1, -1⟩ ∧ uBar = ⟨.C, 1, 0⟩ ∧ wBlock = (0, -1) ∧ vIndex = ⟨.F, 0, -1⟩ ∧
            vBar = ⟨.F, 1, 0⟩) ∨ (normalization.normalizedParentSlot = 1 ∧
            normalization.normalizedQuarterTurn = 3 ∧ uIndex = ⟨.C, 1, 0⟩ ∧ uBar = ⟨.C, 1, 1⟩ ∧
            wBlock = (0, 1) ∧ vIndex = ⟨.A, 0, -1⟩ ∧ vBar = ⟨.B, 1, 1⟩) ∨
            (normalization.normalizedParentSlot = 2 ∧ normalization.normalizedQuarterTurn = 0 ∧
            uIndex = ⟨.E, -1, 0⟩ ∧ uBar = ⟨.F, 0, -1⟩ ∧ wBlock = (-1, -1) ∧ vIndex = ⟨.A, -1, -1⟩
            ∧ vBar = ⟨.A, 0, -1⟩) ∨ (normalization.normalizedParentSlot = 2 ∧
            normalization.normalizedQuarterTurn = 1 ∧ uIndex = ⟨.F, 0, -1⟩ ∧ uBar = ⟨.F, 1, 0⟩ ∧
            wBlock = (1, 1) ∧ vIndex = ⟨.D, -1, -1⟩ ∧ vBar = ⟨.C, 1, 0⟩) ∨
            (normalization.normalizedParentSlot = 2 ∧ normalization.normalizedQuarterTurn = 2 ∧
            uIndex = ⟨.F, 1, 0⟩ ∧ uBar = ⟨.E, 0, 1⟩ ∧ wBlock = (1, 1) ∧ vIndex = ⟨.B, 1, 1⟩ ∧
            vBar = ⟨.B, 0, 1⟩) ∨ (normalization.normalizedParentSlot = 2 ∧
            normalization.normalizedQuarterTurn = 3 ∧ uIndex = ⟨.E, 0, 1⟩ ∧ uBar = ⟨.E, -1, 0⟩ ∧
            wBlock = (-1, -1) ∧ vIndex = ⟨.C, 1, 1⟩ ∧ vBar = ⟨.D, -1, 0⟩)) ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization uIndex vIndex uBar vBar wBlock
  generalize hp : normalization.normalizedParentSlot = p
  generalize ht : normalization.normalizedQuarterTurn = t
  fin_cases p <;> fin_cases t <;>
    simp [uIndex, uBar, vIndex, vBar, wBlock, hp, ht]

private theorem hUbarBand :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin
            3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralSubtileNormalizationCertificate C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x),
        let Q := normalization.normalizedPresentation
        let uBar : PeriodicSubtileIndex :=
          if normalization.normalizedParentSlot = 0 then
            if normalization.normalizedQuarterTurn = 0 then ⟨.B, 1, 1⟩
            else if normalization.normalizedQuarterTurn = 1 then ⟨.B, 0, 1⟩
            else if normalization.normalizedQuarterTurn = 2 then ⟨.A, -1, -1⟩
            else ⟨.A, 0, -1⟩
          else if normalization.normalizedParentSlot = 1 then
            if normalization.normalizedQuarterTurn = 0 then ⟨.D, -1, 0⟩
            else if normalization.normalizedQuarterTurn = 1 then ⟨.D, -1, -1⟩
            else if normalization.normalizedQuarterTurn = 2 then ⟨.C, 1, 0⟩
            else ⟨.C, 1, 1⟩
          else if normalization.normalizedQuarterTurn = 0 then ⟨.F, 0, -1⟩
          else if normalization.normalizedQuarterTurn = 1 then ⟨.F, 1, 0⟩
          else if normalization.normalizedQuarterTurn = 2 then ⟨.E, 0, 1⟩
          else ⟨.E, -1, 0⟩
        let Ubar := SubtileOccurrenceInterpretation normalization.layout.P
          normalization.layout.u normalization.layout.v uBar
        BandPrototile (Q normalization.normalizedParentSlot.succ) Ubar ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization Q uBar Ubar
  generalize hp : normalization.normalizedParentSlot = p
  generalize ht : normalization.normalizedQuarterTurn = t
  fin_cases p <;> fin_cases t <;>
    simp only [Fin.mk_one, Fin.isValue, Fin.succ_one_eq_two, SubtileOccurrenceInterpretation,
        hp, one_ne_zero, ↓reduceIte, ht, Fin.reduceFinMk, Fin.reduceEq, Int.cast_one, one_mul,
        Int.cast_zero, zero_mul, add_zero, Q, Ubar, uBar, Fin.zero_eta, Int.reduceNeg,
        Int.cast_neg, neg_mul, Fin.reduceSucc, zero_add, Fin.succ_zero_eq_one]
  all_goals first
    | exact BandPrototileTranslation _ _ _
        (normalization.layout.outer_occurrence 0 true).1
    | exact BandPrototileTranslation _ _ _
        (normalization.layout.outer_occurrence 0 false).1
    | exact BandPrototileTranslation _ _ _
        (normalization.layout.outer_occurrence 1 true).1
    | exact BandPrototileTranslation _ _ _
        (normalization.layout.outer_occurrence 1 false).1
    | exact BandPrototileTranslation _ _ _
        (normalization.layout.outer_occurrence 2 true).1
    | exact BandPrototileTranslation _ _ _
        (normalization.layout.outer_occurrence 2 false).1

private theorem hUbarCent :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin
            3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralSubtileNormalizationCertificate C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x),
        let Q := normalization.normalizedPresentation
        let incoming : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (Q j.succ) (Q 0)
        let outgoing : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (Q 0) (Q j.succ)
        let uBar : PeriodicSubtileIndex :=
          if normalization.normalizedParentSlot = 0 then
            if normalization.normalizedQuarterTurn = 0 then ⟨.B, 1, 1⟩
            else if normalization.normalizedQuarterTurn = 1 then ⟨.B, 0, 1⟩
            else if normalization.normalizedQuarterTurn = 2 then ⟨.A, -1, -1⟩
            else ⟨.A, 0, -1⟩
          else if normalization.normalizedParentSlot = 1 then
            if normalization.normalizedQuarterTurn = 0 then ⟨.D, -1, 0⟩
            else if normalization.normalizedQuarterTurn = 1 then ⟨.D, -1, -1⟩
            else if normalization.normalizedQuarterTurn = 2 then ⟨.C, 1, 0⟩
            else ⟨.C, 1, 1⟩
          else if normalization.normalizedQuarterTurn = 0 then ⟨.F, 0, -1⟩
          else if normalization.normalizedQuarterTurn = 1 then ⟨.F, 1, 0⟩
          else if normalization.normalizedQuarterTurn = 2 then ⟨.E, 0, 1⟩
          else ⟨.E, -1, 0⟩
        (∀ (p : Fin (3 : ℕ)), ∀ (t : Fin (4 : ℕ)),
        let uIndex := if p = (0 : Fin (3 : ℕ)) then if t = (0 : Fin (4 : ℕ)) then
            (⟨SixSubtileLabel.A, (0 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else if t = (1 : Fin
            (4 : ℕ)) then (⟨SixSubtileLabel.B, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else if
            t = (2 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.B, (0 : ℤ), (1 : ℤ)⟩ :
            PeriodicSubtileIndex) else (⟨SixSubtileLabel.A, (-1 : ℤ), (-1 : ℤ)⟩ :
            PeriodicSubtileIndex) else if p = (1 : Fin (3 : ℕ)) then if t = (0 : Fin (4 : ℕ))
            then (⟨SixSubtileLabel.C, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else if t = (1 :
            Fin (4 : ℕ)) then (⟨SixSubtileLabel.D, (-1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex)
            else if t = (2 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.D, (-1 : ℤ), (-1 : ℤ)⟩ :
            PeriodicSubtileIndex) else (⟨SixSubtileLabel.C, (1 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex) else if t = (0 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.E, (-1 :
            ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) else if t = (1 : Fin (4 : ℕ)) then
            (⟨SixSubtileLabel.F, (0 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else if t = (2 : Fin
            (4 : ℕ)) then (⟨SixSubtileLabel.F, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) else
            (⟨SixSubtileLabel.E, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex);
        let vIndex := if p = (0 : Fin (3 : ℕ)) then if t = (0 : Fin (4 : ℕ)) then
            (⟨SixSubtileLabel.C, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) else if t = (1 : Fin
            (4 : ℕ)) then (⟨SixSubtileLabel.F, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) else if
            t = (2 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.D, (-1 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex) else (⟨SixSubtileLabel.E, (-1 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex) else if p = (1 : Fin (3 : ℕ)) then if t = (0 : Fin (4 : ℕ))
            then (⟨SixSubtileLabel.E, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else if t = (1 :
            Fin (4 : ℕ)) then (⟨SixSubtileLabel.B, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else
            if t = (2 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.F, (0 : ℤ), (-1 : ℤ)⟩ :
            PeriodicSubtileIndex) else (⟨SixSubtileLabel.A, (0 : ℤ), (-1 : ℤ)⟩ :
            PeriodicSubtileIndex) else if t = (0 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.A, (-1 :
            ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else if t = (1 : Fin (4 : ℕ)) then
            (⟨SixSubtileLabel.D, (-1 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else if t = (2 : Fin
            (4 : ℕ)) then (⟨SixSubtileLabel.B, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else
            (⟨SixSubtileLabel.C, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex);
        let U := SubtileOccurrenceInterpretation normalization.layout.P normalization.layout.u
            normalization.layout.v uIndex;
        let V := SubtileOccurrenceInterpretation normalization.layout.P normalization.layout.u
            normalization.layout.v vIndex; TileCentroid U - TileCentroid
            normalization.normalizedRoot = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ^ (↑t : ℕ) * (incoming p + outgoing p)) ∧ TileCentroid V - TileCentroid
            normalization.normalizedRoot = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ^ (↑t : ℕ) * if Even (↑t : ℕ) then incoming (p + (1 : Fin (3 : ℕ))) -
            outgoing (p + (1 : Fin (3 : ℕ))) else outgoing (p - (1 : Fin (3 : ℕ))) - incoming (p
            - (1 : Fin (3 : ℕ))))) → ((∀ (t : Fin 4), ∀ (z : GaussianInt), (⟨0, 1⟩ : GaussianInt)
            ^ (t + 1).val * z = (⟨0, 1⟩ : GaussianInt) * ((⟨0, 1⟩ : GaussianInt) ^ t.val * z)) → (
        let Ubar := SubtileOccurrenceInterpretation normalization.layout.P
          normalization.layout.u normalization.layout.v uBar
        TileCentroid Ubar - TileCentroid normalization.normalizedRoot = (1 / 2 : Real) •
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) * ((⟨0, 1⟩ : GaussianInt) ^
            normalization.normalizedQuarterTurn.val * (incoming
            normalization.normalizedParentSlot + outgoing normalization.normalizedParentSlot)))))
            ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization Q incoming outgoing uBar rowsAt quarterPower Ubar
  rw [← quarterPower normalization.normalizedQuarterTurn
    (incoming normalization.normalizedParentSlot +
      outgoing normalization.normalizedParentSlot)]
  generalize hp : normalization.normalizedParentSlot = p
  generalize ht : normalization.normalizedQuarterTurn = t
  fin_cases p <;> fin_cases t
  · simpa [Ubar, uBar, hp, ht, Fin.add_def] using (rowsAt 0 1).1
  · simpa [Ubar, uBar, hp, ht, Fin.add_def] using (rowsAt 0 2).1
  · simpa [Ubar, uBar, hp, ht, Fin.add_def] using (rowsAt 0 3).1
  · simpa [Ubar, uBar, hp, ht, Fin.add_def] using (rowsAt 0 0).1
  · simpa [Ubar, uBar, hp, ht, Fin.add_def] using (rowsAt 1 1).1
  · simpa [Ubar, uBar, hp, ht, Fin.add_def] using (rowsAt 1 2).1
  · simpa [Ubar, uBar, hp, ht, Fin.add_def] using (rowsAt 1 3).1
  · simpa [Ubar, uBar, hp, ht, Fin.add_def] using (rowsAt 1 0).1
  · simpa [Ubar, uBar, hp, ht, Fin.add_def] using (rowsAt 2 1).1
  · simpa [Ubar, uBar, hp, ht, Fin.add_def] using (rowsAt 2 2).1
  · simpa [Ubar, uBar, hp, ht, Fin.add_def] using (rowsAt 2 3).1
  · simpa [Ubar, uBar, hp, ht, Fin.add_def] using (rowsAt 2 0).1

private theorem hshift :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin
            3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralSubtileNormalizationCertificate C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x),
        let Q := normalization.normalizedPresentation
        let incoming : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (Q j.succ) (Q 0)
        let outgoing : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (Q 0) (Q j.succ)
        (∀ (j : Fin (3 : ℕ)), BandVectors.1 (Q (0 : Fin (4 : ℕ))) (Q j.succ) = (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) * BandVectors.1 (Q j.succ) (Q (0 : Fin (4 : ℕ))) ∧ BandVectors.2
            (Q (0 : Fin (4 : ℕ))) (Q j.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.2 (Q j.succ) (Q (0 : Fin (4 : ℕ)))) → (
        let wBlock : Int × Int :=
          if normalization.normalizedParentSlot = 0 then
            if normalization.normalizedQuarterTurn = 0 ∨
                normalization.normalizedQuarterTurn = 3 then (1, 0) else (-1, 0)
          else if normalization.normalizedParentSlot = 1 then
            if normalization.normalizedQuarterTurn = 0 ∨
                normalization.normalizedQuarterTurn = 3 then (0, 1) else (0, -1)
          else if normalization.normalizedQuarterTurn = 0 ∨
              normalization.normalizedQuarterTurn = 3 then (-1, -1) else (1, 1)
        let wShift : GaussianInt :=
          (⟨0, 1⟩ : GaussianInt) ^ normalization.normalizedQuarterTurn.val *
            (if Even normalization.normalizedQuarterTurn.val then
              incoming normalization.normalizedParentSlot
            else outgoing normalization.normalizedParentSlot)
        ((⟨0, 1⟩ : GaussianInt) * incoming 0 = normalization.layout.u) → (((⟨0, 1⟩ : GaussianInt)
            * incoming 1 = normalization.layout.v) → (((⟨0, 1⟩ : GaussianInt) * incoming 2 =
            -normalization.layout.u - normalization.layout.v) → ((∀ (z : GaussianInt),
            GaussianQuarterTurn z = (⟨0, 1⟩ : GaussianInt) * z) → (GaussianQuarterTurn wShift =
            (wBlock.1 : GaussianInt) * normalization.layout.u + (wBlock.2 : GaussianInt) *
            normalization.layout.v))))) ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization Q incoming outgoing hflips wBlock wShift hout0
      hout1 hout2 quarterTurnMul
  rw [quarterTurnMul]
  have hf0 : outgoing 0 = (⟨0, 1⟩ : GaussianInt) * incoming 0 := by
    simpa [outgoing, incoming] using (hflips 0).1
  have hf1 : outgoing 1 = (⟨0, 1⟩ : GaussianInt) * incoming 1 := by
    simpa [outgoing, incoming] using (hflips 1).1
  have hf2 : outgoing 2 = (⟨0, 1⟩ : GaussianInt) * incoming 2 := by
    simpa [outgoing, incoming] using (hflips 2).1
  have even0 : Even 0 := ⟨0, rfl⟩
  have notEven1 : ¬ Even 1 := by
    rintro ⟨r, hr⟩
    omega
  have even2 : Even 2 := ⟨1, rfl⟩
  have notEven3 : ¬ Even 3 := by
    rintro ⟨r, hr⟩
    omega
  have h0re := congrArg (fun z : GaussianInt => z.re) hout0
  have h0im := congrArg (fun z : GaussianInt => z.im) hout0
  have h1re := congrArg (fun z : GaussianInt => z.re) hout1
  have h1im := congrArg (fun z : GaussianInt => z.im) hout1
  have h2re := congrArg (fun z : GaussianInt => z.re) hout2
  have h2im := congrArg (fun z : GaussianInt => z.im) hout2
  have hf0re := congrArg (fun z : GaussianInt => z.re) hf0
  have hf0im := congrArg (fun z : GaussianInt => z.im) hf0
  have hf1re := congrArg (fun z : GaussianInt => z.re) hf1
  have hf1im := congrArg (fun z : GaussianInt => z.im) hf1
  have hf2re := congrArg (fun z : GaussianInt => z.re) hf2
  have hf2im := congrArg (fun z : GaussianInt => z.im) hf2
  generalize hp : normalization.normalizedParentSlot = p
  generalize ht : normalization.normalizedQuarterTurn = t
  fin_cases p <;> fin_cases t <;> apply Zsqrtd.ext
  all_goals
    simp [
      ] at h0re h0im h1re h1im h2re h2im hf0re hf0im hf1re hf1im hf2re hf2im
  all_goals
    simp [wShift, wBlock, hp, ht, even0, notEven1, even2, notEven3,
      pow_succ]; omega

private theorem hVbarBand :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin
            3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralSubtileNormalizationCertificate C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x),
        let Q := normalization.normalizedPresentation
        (∀ (j : Fin 3), ∀ (e : Bool), ∀ (m : Int), ∀ (n : Int), BandPrototile (Q j.succ)
            (SubtileOccurrenceInterpretation normalization.layout.P normalization.layout.u
            normalization.layout.v ⟨subtileOccurrenceLabel j e, m, n⟩)) → (
        let vBar : PeriodicSubtileIndex :=
          if normalization.normalizedParentSlot = 0 then
            if normalization.normalizedQuarterTurn = 0 then ⟨.C, 1, 1⟩
            else if normalization.normalizedQuarterTurn = 1 then ⟨.E, 0, 1⟩
            else if normalization.normalizedQuarterTurn = 2 then ⟨.D, -1, -1⟩
            else ⟨.F, 0, -1⟩
          else if normalization.normalizedParentSlot = 1 then
            if normalization.normalizedQuarterTurn = 0 then ⟨.E, -1, 0⟩
            else if normalization.normalizedQuarterTurn = 1 then ⟨.A, -1, -1⟩
            else if normalization.normalizedQuarterTurn = 2 then ⟨.F, 1, 0⟩
            else ⟨.B, 1, 1⟩
          else if normalization.normalizedQuarterTurn = 0 then ⟨.A, 0, -1⟩
          else if normalization.normalizedQuarterTurn = 1 then ⟨.C, 1, 0⟩
          else if normalization.normalizedQuarterTurn = 2 then ⟨.B, 0, 1⟩
          else ⟨.D, -1, 0⟩
        let Vbar := SubtileOccurrenceInterpretation normalization.layout.P
          normalization.layout.u normalization.layout.v vBar
        BandPrototile (Q ((if Even normalization.normalizedQuarterTurn.val then
            normalization.normalizedParentSlot + 1 else normalization.normalizedParentSlot -
            1).succ)) Vbar) ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization Q occurrenceBand vBar Vbar
  generalize hp : normalization.normalizedParentSlot = p
  generalize ht : normalization.normalizedQuarterTurn = t
  fin_cases p <;> fin_cases t <;>
    simp only [Even.zero, ↓reduceIte, Fin.mk_one, Fin.isValue, Fin.reduceAdd, Fin.reduceSucc,
        hp, one_ne_zero, ht, Fin.zero_eta, Int.reduceNeg, Vbar, vBar, Fin.reduceFinMk,
        Fin.succ_zero_eq_one, Fin.reduceEq, zero_add, Fin.succ_one_eq_two, sub_self,
        Fin.reduceSub, zero_sub, Nat.not_even_one, even_two] <;>
    first
    | exact occurrenceBand 0 true _ _
    | exact occurrenceBand 0 false _ _
    | exact occurrenceBand 1 true _ _
    | exact occurrenceBand 1 false _ _
    | exact occurrenceBand 2 true _ _
    | exact occurrenceBand 2 false _ _

private theorem hVSym :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin
            3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralSubtileNormalizationCertificate C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x), (∀ (A :
            ProtoTile), ∀ (d : GaussianInt), (QuarterTurnSymmetric A) → (QuarterTurnSymmetric
            (TileTranslation A d))) → (
        let vIndex : PeriodicSubtileIndex :=
          if normalization.normalizedParentSlot = 0 then
            if normalization.normalizedQuarterTurn = 0 then ⟨.C, 1, 0⟩
            else if normalization.normalizedQuarterTurn = 1 then ⟨.F, 1, 0⟩
            else if normalization.normalizedQuarterTurn = 2 then ⟨.D, -1, 0⟩
            else ⟨.E, -1, 0⟩
          else if normalization.normalizedParentSlot = 1 then
            if normalization.normalizedQuarterTurn = 0 then ⟨.E, 0, 1⟩
            else if normalization.normalizedQuarterTurn = 1 then ⟨.B, 0, 1⟩
            else if normalization.normalizedQuarterTurn = 2 then ⟨.F, 0, -1⟩
            else ⟨.A, 0, -1⟩
          else if normalization.normalizedQuarterTurn = 0 then ⟨.A, -1, -1⟩
          else if normalization.normalizedQuarterTurn = 1 then ⟨.D, -1, -1⟩
          else if normalization.normalizedQuarterTurn = 2 then ⟨.B, 1, 1⟩
          else ⟨.C, 1, 1⟩
        let V := SubtileOccurrenceInterpretation normalization.layout.P
          normalization.layout.u normalization.layout.v vIndex
        QuarterTurnSymmetric V) ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization quarterSymmetricTranslation vIndex V
  generalize hp : normalization.normalizedParentSlot = p
  generalize ht : normalization.normalizedQuarterTurn = t
  fin_cases p <;> fin_cases t <;>
    simp only [SubtileOccurrenceInterpretation, hp, Fin.mk_one, Fin.isValue, one_ne_zero,
        ↓reduceIte, ht, Fin.reduceFinMk, Fin.reduceEq, Int.reduceNeg, Int.cast_zero, zero_mul,
        Int.cast_neg, Int.cast_one, neg_mul, one_mul, zero_add, V, vIndex, Fin.zero_eta,
        add_zero] <;>
    apply quarterSymmetricTranslation <;>
    first
    | exact normalization.layout.parent_quarter_turn 0 true
    | exact normalization.layout.parent_quarter_turn 0 false
    | exact normalization.layout.parent_quarter_turn 1 true
    | exact normalization.layout.parent_quarter_turn 1 false
    | exact normalization.layout.parent_quarter_turn 2 true
    | exact normalization.layout.parent_quarter_turn 2 false

private theorem hVbarCent :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin
            3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralSubtileNormalizationCertificate C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x),
        let Q := normalization.normalizedPresentation
        let incoming : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (Q j.succ) (Q 0)
        let outgoing : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (Q 0) (Q j.succ)
        (∀ (j : Fin (3 : ℕ)), BandVectors.1 (Q (0 : Fin (4 : ℕ))) (Q j.succ) = (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) * BandVectors.1 (Q j.succ) (Q (0 : Fin (4 : ℕ))) ∧ BandVectors.2
            (Q (0 : Fin (4 : ℕ))) (Q j.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.2 (Q j.succ) (Q (0 : Fin (4 : ℕ)))) → (
        let vBar : PeriodicSubtileIndex :=
          if normalization.normalizedParentSlot = 0 then
            if normalization.normalizedQuarterTurn = 0 then ⟨.C, 1, 1⟩
            else if normalization.normalizedQuarterTurn = 1 then ⟨.E, 0, 1⟩
            else if normalization.normalizedQuarterTurn = 2 then ⟨.D, -1, -1⟩
            else ⟨.F, 0, -1⟩
          else if normalization.normalizedParentSlot = 1 then
            if normalization.normalizedQuarterTurn = 0 then ⟨.E, -1, 0⟩
            else if normalization.normalizedQuarterTurn = 1 then ⟨.A, -1, -1⟩
            else if normalization.normalizedQuarterTurn = 2 then ⟨.F, 1, 0⟩
            else ⟨.B, 1, 1⟩
          else if normalization.normalizedQuarterTurn = 0 then ⟨.A, 0, -1⟩
          else if normalization.normalizedQuarterTurn = 1 then ⟨.C, 1, 0⟩
          else if normalization.normalizedQuarterTurn = 2 then ⟨.B, 0, 1⟩
          else ⟨.D, -1, 0⟩
        (∀ (p : Fin (3 : ℕ)), ∀ (t : Fin (4 : ℕ)),
        let uIndex := if p = (0 : Fin (3 : ℕ)) then if t = (0 : Fin (4 : ℕ)) then
            (⟨SixSubtileLabel.A, (0 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else if t = (1 : Fin
            (4 : ℕ)) then (⟨SixSubtileLabel.B, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else if
            t = (2 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.B, (0 : ℤ), (1 : ℤ)⟩ :
            PeriodicSubtileIndex) else (⟨SixSubtileLabel.A, (-1 : ℤ), (-1 : ℤ)⟩ :
            PeriodicSubtileIndex) else if p = (1 : Fin (3 : ℕ)) then if t = (0 : Fin (4 : ℕ))
            then (⟨SixSubtileLabel.C, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else if t = (1 :
            Fin (4 : ℕ)) then (⟨SixSubtileLabel.D, (-1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex)
            else if t = (2 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.D, (-1 : ℤ), (-1 : ℤ)⟩ :
            PeriodicSubtileIndex) else (⟨SixSubtileLabel.C, (1 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex) else if t = (0 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.E, (-1 :
            ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) else if t = (1 : Fin (4 : ℕ)) then
            (⟨SixSubtileLabel.F, (0 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else if t = (2 : Fin
            (4 : ℕ)) then (⟨SixSubtileLabel.F, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) else
            (⟨SixSubtileLabel.E, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex);
        let vIndex := if p = (0 : Fin (3 : ℕ)) then if t = (0 : Fin (4 : ℕ)) then
            (⟨SixSubtileLabel.C, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) else if t = (1 : Fin
            (4 : ℕ)) then (⟨SixSubtileLabel.F, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) else if
            t = (2 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.D, (-1 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex) else (⟨SixSubtileLabel.E, (-1 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex) else if p = (1 : Fin (3 : ℕ)) then if t = (0 : Fin (4 : ℕ))
            then (⟨SixSubtileLabel.E, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else if t = (1 :
            Fin (4 : ℕ)) then (⟨SixSubtileLabel.B, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else
            if t = (2 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.F, (0 : ℤ), (-1 : ℤ)⟩ :
            PeriodicSubtileIndex) else (⟨SixSubtileLabel.A, (0 : ℤ), (-1 : ℤ)⟩ :
            PeriodicSubtileIndex) else if t = (0 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.A, (-1 :
            ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else if t = (1 : Fin (4 : ℕ)) then
            (⟨SixSubtileLabel.D, (-1 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else if t = (2 : Fin
            (4 : ℕ)) then (⟨SixSubtileLabel.B, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else
            (⟨SixSubtileLabel.C, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex);
        let U := SubtileOccurrenceInterpretation normalization.layout.P normalization.layout.u
            normalization.layout.v uIndex;
        let V := SubtileOccurrenceInterpretation normalization.layout.P normalization.layout.u
            normalization.layout.v vIndex; TileCentroid U - TileCentroid
            normalization.normalizedRoot = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ^ (↑t : ℕ) * (incoming p + outgoing p)) ∧ TileCentroid V - TileCentroid
            normalization.normalizedRoot = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ^ (↑t : ℕ) * if Even (↑t : ℕ) then incoming (p + (1 : Fin (3 : ℕ))) -
            outgoing (p + (1 : Fin (3 : ℕ))) else outgoing (p - (1 : Fin (3 : ℕ))) - incoming (p
            - (1 : Fin (3 : ℕ))))) → (
        let Vbar := SubtileOccurrenceInterpretation normalization.layout.P
          normalization.layout.u normalization.layout.v vBar
        TileCentroid Vbar - TileCentroid normalization.normalizedRoot = (1 / 2 : Real) •
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) * ((⟨0, 1⟩ : GaussianInt) ^
            normalization.normalizedQuarterTurn.val * (if Even
            normalization.normalizedQuarterTurn.val then incoming
            (normalization.normalizedParentSlot + 1) - outgoing
            (normalization.normalizedParentSlot + 1) else outgoing
            (normalization.normalizedParentSlot - 1) - incoming
            (normalization.normalizedParentSlot - 1)))))) ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization Q incoming outgoing hflips vBar rowsAt Vbar
  have hf0 : outgoing 0 = (⟨0, 1⟩ : GaussianInt) * incoming 0 := by
    simpa [outgoing, incoming] using (hflips 0).1
  have hf1 : outgoing 1 = (⟨0, 1⟩ : GaussianInt) * incoming 1 := by
    simpa [outgoing, incoming] using (hflips 1).1
  have hf2 : outgoing 2 = (⟨0, 1⟩ : GaussianInt) * incoming 2 := by
    simpa [outgoing, incoming] using (hflips 2).1
  have even0 : Even 0 := ⟨0, rfl⟩
  have notEven1 : ¬ Even 1 := by rintro ⟨r, hr⟩; omega
  have even2 : Even 2 := ⟨1, rfl⟩
  have notEven3 : ¬ Even 3 := by rintro ⟨r, hr⟩; omega
  have zeroSubOne : (0 : Fin 3) - 1 = 2 := by decide
  generalize hp : normalization.normalizedParentSlot = p
  generalize ht : normalization.normalizedQuarterTurn = t
  fin_cases p <;> fin_cases t
  · convert (rowsAt 1 0).1 using 1
    · simp [Vbar, vBar, hp, ht]
    · congr 2
      apply Zsqrtd.ext <;> simp [hf1, even0] <;> ring
  · convert (rowsAt 2 3).1 using 1
    · simp [Vbar, vBar, hp, ht]
    · congr 2
      apply Zsqrtd.ext <;>
        simp [hf2, notEven1, zeroSubOne, pow_succ] <;> ring
  · convert (rowsAt 1 2).1 using 1
    · simp [Vbar, vBar, hp, ht]
    · congr 2
      apply Zsqrtd.ext <;> simp [hf1, even2, pow_succ] <;> ring
  · convert (rowsAt 2 1).1 using 1
    · simp [Vbar, vBar, hp, ht]
    · congr 2
      apply Zsqrtd.ext <;>
        simp [hf2, notEven3, zeroSubOne, pow_succ] <;> ring
  · convert (rowsAt 2 0).1 using 1
    · simp [Vbar, vBar, hp, ht]
    · congr 2
      apply Zsqrtd.ext <;> simp [hf2, even0] <;> ring
  · convert (rowsAt 0 3).1 using 1
    · simp [Vbar, vBar, hp, ht]
    · congr 2
      apply Zsqrtd.ext <;>
        simp [hf0, notEven1, pow_succ] <;> ring
  · convert (rowsAt 2 2).1 using 1
    · simp [Vbar, vBar, hp, ht]
    · congr 2
      apply Zsqrtd.ext <;> simp [hf2, even2, pow_succ] <;> ring
  · convert (rowsAt 0 1).1 using 1
    · simp [Vbar, vBar, hp, ht]
    · congr 2
      apply Zsqrtd.ext <;>
        simp [hf0, notEven3, pow_succ] <;> ring
  · convert (rowsAt 0 0).1 using 1
    · simp [Vbar, vBar, hp, ht]
    · congr 2
      apply Zsqrtd.ext <;> simp [hf0, even0] <;> ring
  · convert (rowsAt 1 3).1 using 1
    · simp [Vbar, vBar, hp, ht]
    · congr 2
      apply Zsqrtd.ext <;>
        simp [hf1, notEven1, Fin.sub_def, pow_succ] <;> ring
  · convert (rowsAt 0 2).1 using 1
    · simp [Vbar, vBar, hp, ht]
    · congr 2
      apply Zsqrtd.ext <;> simp [hf0, even2, pow_succ] <;> ring
  · convert (rowsAt 1 1).1 using 1
    · simp [Vbar, vBar, hp, ht]
    · congr 2
      apply Zsqrtd.ext <;>
        simp [hf1, notEven3, Fin.sub_def, pow_succ] <;> ring

end SubtileInterfaceAssembly

namespace SubtileInterfaceRowPackage

private theorem rowPackage :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin
            3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralSubtileNormalizationCertificate C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x),
        let Q := normalization.normalizedPresentation
        let edge : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (Q ((j + 2).succ)) (Q ((j + 1).succ))
        let incoming : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (Q j.succ) (Q 0)
        let outgoing : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (Q 0) (Q j.succ)
        (BandVectors.1 (Q (3 : Fin (4 : ℕ))) (Q (2 : Fin (4 : ℕ))) + BandVectors.1 (Q (1 : Fin (4
            : ℕ))) (Q (3 : Fin (4 : ℕ))) + BandVectors.1 (Q (2 : Fin (4 : ℕ))) (Q (1 : Fin (4 :
            ℕ))) = (0 : GaussianInt)) → ((BandVectors.1 (Q (1 : Fin (4 : ℕ))) (Q (0 : Fin (4 :
            ℕ))) = BandVectors.1 (Q (1 : Fin (4 : ℕ))) (Q (3 : Fin (4 : ℕ))) - (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) * BandVectors.1 (Q (2 : Fin (4 : ℕ))) (Q (1 : Fin (4 : ℕ)))) → ((∀
            (j : Fin (3 : ℕ)), BandVectors.1 (Q (0 : Fin (4 : ℕ))) (Q j.succ) = (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) * BandVectors.1 (Q j.succ) (Q (0 : Fin (4 : ℕ))) ∧ BandVectors.2
            (Q (0 : Fin (4 : ℕ))) (Q j.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.2 (Q j.succ) (Q (0 : Fin (4 : ℕ)))) → ((incoming 1 = edge 2 - (⟨0, 1⟩ :
            GaussianInt) * edge 0) → ((incoming 2 = edge 0 - (⟨0, 1⟩ : GaussianInt) * edge 1) →
            ((TileCentroid (SubtileOccurrenceInterpretation normalization.layout.P
            normalization.layout.u normalization.layout.v (if normalization.normalizedParentSlot
            = (0 : Fin (3 : ℕ)) then if normalization.normalizedQuarterTurn = (0 : Fin (4 : ℕ))
            then (⟨SixSubtileLabel.A, (0 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else if
            normalization.normalizedQuarterTurn = (1 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.B, (1
            : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else if normalization.normalizedQuarterTurn =
            (2 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.B, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex)
            else (⟨SixSubtileLabel.A, (-1 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else if
            normalization.normalizedParentSlot = (1 : Fin (3 : ℕ)) then if
            normalization.normalizedQuarterTurn = (0 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.C, (1
            : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else if normalization.normalizedQuarterTurn =
            (1 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.D, (-1 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex) else if normalization.normalizedQuarterTurn = (2 : Fin (4 : ℕ))
            then (⟨SixSubtileLabel.D, (-1 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else
            (⟨SixSubtileLabel.C, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) else if
            normalization.normalizedQuarterTurn = (0 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.E, (-1
            : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) else if normalization.normalizedQuarterTurn =
            (1 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.F, (0 : ℤ), (-1 : ℤ)⟩ :
            PeriodicSubtileIndex) else if normalization.normalizedQuarterTurn = (2 : Fin (4 : ℕ))
            then (⟨SixSubtileLabel.F, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) else
            (⟨SixSubtileLabel.E, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex))) - TileCentroid
            normalization.normalizedRoot = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ^ (↑normalization.normalizedQuarterTurn : ℕ) * (incoming
            normalization.normalizedParentSlot + outgoing normalization.normalizedParentSlot))) →
            ((TileCentroid (SubtileOccurrenceInterpretation normalization.layout.P
            normalization.layout.u normalization.layout.v (if normalization.normalizedParentSlot
            = (0 : Fin (3 : ℕ)) then if normalization.normalizedQuarterTurn = (0 : Fin (4 : ℕ))
            then (⟨SixSubtileLabel.C, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) else if
            normalization.normalizedQuarterTurn = (1 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.F, (1
            : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) else if normalization.normalizedQuarterTurn =
            (2 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.D, (-1 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex) else (⟨SixSubtileLabel.E, (-1 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex) else if normalization.normalizedParentSlot = (1 : Fin (3 : ℕ))
            then if normalization.normalizedQuarterTurn = (0 : Fin (4 : ℕ)) then
            (⟨SixSubtileLabel.E, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else if
            normalization.normalizedQuarterTurn = (1 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.B, (0
            : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else if normalization.normalizedQuarterTurn =
            (2 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.F, (0 : ℤ), (-1 : ℤ)⟩ :
            PeriodicSubtileIndex) else (⟨SixSubtileLabel.A, (0 : ℤ), (-1 : ℤ)⟩ :
            PeriodicSubtileIndex) else if normalization.normalizedQuarterTurn = (0 : Fin (4 : ℕ))
            then (⟨SixSubtileLabel.A, (-1 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else if
            normalization.normalizedQuarterTurn = (1 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.D, (-1
            : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else if normalization.normalizedQuarterTurn =
            (2 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.B, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex)
            else (⟨SixSubtileLabel.C, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex))) - TileCentroid
            normalization.normalizedRoot = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ^ (↑normalization.normalizedQuarterTurn : ℕ) * if Even
            (↑normalization.normalizedQuarterTurn : ℕ) then incoming
            (normalization.normalizedParentSlot + (1 : Fin (3 : ℕ))) - outgoing
            (normalization.normalizedParentSlot + (1 : Fin (3 : ℕ))) else outgoing
            (normalization.normalizedParentSlot - (1 : Fin (3 : ℕ))) - incoming
            (normalization.normalizedParentSlot - (1 : Fin (3 : ℕ))))) → ((
        let Q := normalization.normalizedPresentation; ∀ (j : Fin (3 : ℕ)), ∀ (e : Bool), ∀ (m :
            ℤ), ∀ (n : ℤ), BandPrototile (Q j.succ) (SubtileOccurrenceInterpretation
            normalization.layout.P normalization.layout.u normalization.layout.v
            ⟨subtileOccurrenceLabel j e, m, n⟩)) → ((∀ (A : ProtoTile), ∀ (d : GaussianInt),
            QuarterTurnSymmetric A → QuarterTurnSymmetric (TileTranslation A d)) → (∀ (g :
            GaussianInt), ((TileTranslation (TileQuarterTurn normalization.normalizedRoot)
            g).cells = normalization.normalizedRoot.cells) → ((∀ (Y : ProtoTile), ∀ (Z :
            ProtoTile), ∀ (z : GaussianInt), TileCentroid Y - TileCentroid
            normalization.normalizedRoot = (1 / 2 : ℝ) • GaussianRealPoint z → TileCentroid Z -
            TileCentroid normalization.normalizedRoot = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 :
            ℤ), (1 : ℤ)⟩ : GaussianInt) * z) → TileCentroid (TileTranslation (TileQuarterTurn Y)
            g) = TileCentroid Z) → ((∀ (C : CircleCoordinates), ∀ (Y : ProtoTile), ∀ (Z :
            ProtoTile), BandPrototile C Y → BandPrototile C Z → QuarterTurnSymmetric Y →
            TileCentroid (TileTranslation (TileQuarterTurn Y) g) = TileCentroid Z →
            (TileTranslation (TileQuarterTurn Y) g).cells = Z.cells ∧ ((TileTranslation
            (TileQuarterTurn Y) g).cells = ∅ → (TileTranslation (TileQuarterTurn Y) g).anchor =
            Z.anchor)) → ((∀ (A : ProtoTile), ∀ (a : GaussianInt), ∀ (d : GaussianInt),
            TileTranslation (TileQuarterTurn (TileTranslation A a)) d = TileTranslation
            (TileTranslation (TileQuarterTurn A) d) (GaussianQuarterTurn a)) → (
        ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * (fun (j : Fin (3 : ℕ)) => BandVectors.1
            (normalization.normalizedPresentation j.succ) (normalization.normalizedPresentation
            (0 : Fin (4 : ℕ)))) (0 : Fin (3 : ℕ)) = normalization.layout.u) → (((⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) * (fun (j : Fin (3 : ℕ)) => BandVectors.1
            (normalization.normalizedPresentation j.succ) (normalization.normalizedPresentation
            (0 : Fin (4 : ℕ)))) (1 : Fin (3 : ℕ)) = normalization.layout.v) → ((∀ (p : Fin (3 :
            ℕ)), ∀ (t : Fin (4 : ℕ)),
        let uIndex := if p = (0 : Fin (3 : ℕ)) then if t = (0 : Fin (4 : ℕ)) then
            (⟨SixSubtileLabel.A, (0 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else if t = (1 : Fin
            (4 : ℕ)) then (⟨SixSubtileLabel.B, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else if
            t = (2 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.B, (0 : ℤ), (1 : ℤ)⟩ :
            PeriodicSubtileIndex) else (⟨SixSubtileLabel.A, (-1 : ℤ), (-1 : ℤ)⟩ :
            PeriodicSubtileIndex) else if p = (1 : Fin (3 : ℕ)) then if t = (0 : Fin (4 : ℕ))
            then (⟨SixSubtileLabel.C, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else if t = (1 :
            Fin (4 : ℕ)) then (⟨SixSubtileLabel.D, (-1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex)
            else if t = (2 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.D, (-1 : ℤ), (-1 : ℤ)⟩ :
            PeriodicSubtileIndex) else (⟨SixSubtileLabel.C, (1 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex) else if t = (0 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.E, (-1 :
            ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) else if t = (1 : Fin (4 : ℕ)) then
            (⟨SixSubtileLabel.F, (0 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else if t = (2 : Fin
            (4 : ℕ)) then (⟨SixSubtileLabel.F, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) else
            (⟨SixSubtileLabel.E, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex);
        let vIndex := if p = (0 : Fin (3 : ℕ)) then if t = (0 : Fin (4 : ℕ)) then
            (⟨SixSubtileLabel.C, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) else if t = (1 : Fin
            (4 : ℕ)) then (⟨SixSubtileLabel.F, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) else if
            t = (2 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.D, (-1 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex) else (⟨SixSubtileLabel.E, (-1 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex) else if p = (1 : Fin (3 : ℕ)) then if t = (0 : Fin (4 : ℕ))
            then (⟨SixSubtileLabel.E, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else if t = (1 :
            Fin (4 : ℕ)) then (⟨SixSubtileLabel.B, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else
            if t = (2 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.F, (0 : ℤ), (-1 : ℤ)⟩ :
            PeriodicSubtileIndex) else (⟨SixSubtileLabel.A, (0 : ℤ), (-1 : ℤ)⟩ :
            PeriodicSubtileIndex) else if t = (0 : Fin (4 : ℕ)) then (⟨SixSubtileLabel.A, (-1 :
            ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else if t = (1 : Fin (4 : ℕ)) then
            (⟨SixSubtileLabel.D, (-1 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) else if t = (2 : Fin
            (4 : ℕ)) then (⟨SixSubtileLabel.B, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) else
            (⟨SixSubtileLabel.C, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex);
        let U := SubtileOccurrenceInterpretation normalization.layout.P normalization.layout.u
            normalization.layout.v uIndex;
        let V := SubtileOccurrenceInterpretation normalization.layout.P normalization.layout.u
            normalization.layout.v vIndex; TileCentroid U - TileCentroid
            normalization.normalizedRoot = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ^ (↑t : ℕ) * (incoming p + outgoing p)) ∧ TileCentroid V - TileCentroid
            normalization.normalizedRoot = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ^ (↑t : ℕ) * if Even (↑t : ℕ) then incoming (p + (1 : Fin (3 : ℕ))) -
            outgoing (p + (1 : Fin (3 : ℕ))) else outgoing (p - (1 : Fin (3 : ℕ))) - incoming (p
            - (1 : Fin (3 : ℕ))))) → (∃ (W V : ProtoTile) (g wShift : GaussianInt) (uIndex uBar
            vIndex vBar : PeriodicSubtileIndex) (wBlock : Int × Int),
            ((normalization.normalizedParentSlot = 0 ∧ normalization.normalizedQuarterTurn = 0 ∧
            uIndex = ⟨.A, 0, -1⟩ ∧ uBar = ⟨.B, 1, 1⟩ ∧ wBlock = (1, 0) ∧ vIndex = ⟨.C, 1, 0⟩ ∧
            vBar = ⟨.C, 1, 1⟩) ∨ (normalization.normalizedParentSlot = 0 ∧
            normalization.normalizedQuarterTurn = 1 ∧ uIndex = ⟨.B, 1, 1⟩ ∧ uBar = ⟨.B, 0, 1⟩ ∧
            wBlock = (-1, 0) ∧ vIndex = ⟨.F, 1, 0⟩ ∧ vBar = ⟨.E, 0, 1⟩) ∨
            (normalization.normalizedParentSlot = 0 ∧ normalization.normalizedQuarterTurn = 2 ∧
            uIndex = ⟨.B, 0, 1⟩ ∧ uBar = ⟨.A, -1, -1⟩ ∧ wBlock = (-1, 0) ∧ vIndex = ⟨.D, -1, 0⟩ ∧
            vBar = ⟨.D, -1, -1⟩) ∨ (normalization.normalizedParentSlot = 0 ∧
            normalization.normalizedQuarterTurn = 3 ∧ uIndex = ⟨.A, -1, -1⟩ ∧ uBar = ⟨.A, 0, -1⟩
            ∧ wBlock = (1, 0) ∧ vIndex = ⟨.E, -1, 0⟩ ∧ vBar = ⟨.F, 0, -1⟩) ∨
            (normalization.normalizedParentSlot = 1 ∧ normalization.normalizedQuarterTurn = 0 ∧
            uIndex = ⟨.C, 1, 1⟩ ∧ uBar = ⟨.D, -1, 0⟩ ∧ wBlock = (0, 1) ∧ vIndex = ⟨.E, 0, 1⟩ ∧
            vBar = ⟨.E, -1, 0⟩) ∨ (normalization.normalizedParentSlot = 1 ∧
            normalization.normalizedQuarterTurn = 1 ∧ uIndex = ⟨.D, -1, 0⟩ ∧ uBar = ⟨.D, -1, -1⟩
            ∧ wBlock = (0, -1) ∧ vIndex = ⟨.B, 0, 1⟩ ∧ vBar = ⟨.A, -1, -1⟩) ∨
            (normalization.normalizedParentSlot = 1 ∧ normalization.normalizedQuarterTurn = 2 ∧
            uIndex = ⟨.D, -1, -1⟩ ∧ uBar = ⟨.C, 1, 0⟩ ∧ wBlock = (0, -1) ∧ vIndex = ⟨.F, 0, -1⟩ ∧
            vBar = ⟨.F, 1, 0⟩) ∨ (normalization.normalizedParentSlot = 1 ∧
            normalization.normalizedQuarterTurn = 3 ∧ uIndex = ⟨.C, 1, 0⟩ ∧ uBar = ⟨.C, 1, 1⟩ ∧
            wBlock = (0, 1) ∧ vIndex = ⟨.A, 0, -1⟩ ∧ vBar = ⟨.B, 1, 1⟩) ∨
            (normalization.normalizedParentSlot = 2 ∧ normalization.normalizedQuarterTurn = 0 ∧
            uIndex = ⟨.E, -1, 0⟩ ∧ uBar = ⟨.F, 0, -1⟩ ∧ wBlock = (-1, -1) ∧ vIndex = ⟨.A, -1, -1⟩
            ∧ vBar = ⟨.A, 0, -1⟩) ∨ (normalization.normalizedParentSlot = 2 ∧
            normalization.normalizedQuarterTurn = 1 ∧ uIndex = ⟨.F, 0, -1⟩ ∧ uBar = ⟨.F, 1, 0⟩ ∧
            wBlock = (1, 1) ∧ vIndex = ⟨.D, -1, -1⟩ ∧ vBar = ⟨.C, 1, 0⟩) ∨
            (normalization.normalizedParentSlot = 2 ∧ normalization.normalizedQuarterTurn = 2 ∧
            uIndex = ⟨.F, 1, 0⟩ ∧ uBar = ⟨.E, 0, 1⟩ ∧ wBlock = (1, 1) ∧ vIndex = ⟨.B, 1, 1⟩ ∧
            vBar = ⟨.B, 0, 1⟩) ∨ (normalization.normalizedParentSlot = 2 ∧
            normalization.normalizedQuarterTurn = 3 ∧ uIndex = ⟨.E, 0, 1⟩ ∧ uBar = ⟨.E, -1, 0⟩ ∧
            wBlock = (-1, -1) ∧ vIndex = ⟨.C, 1, 1⟩ ∧ vBar = ⟨.D, -1, 0⟩)) ∧
            normalization.normalizedFixed.cells = (SubtileOccurrenceInterpretation
            normalization.layout.P normalization.layout.u normalization.layout.v uIndex).cells ∧
            V.cells = (SubtileOccurrenceInterpretation normalization.layout.P
            normalization.layout.u normalization.layout.v vIndex).cells ∧ W = TileTranslation
            normalization.normalizedRoot wShift ∧ wShift = (⟨0, 1⟩ : GaussianInt) ^
            normalization.normalizedQuarterTurn.val * (if Even
            normalization.normalizedQuarterTurn.val then incoming
            normalization.normalizedParentSlot else outgoing normalization.normalizedParentSlot)
            ∧ (TileTranslation (TileQuarterTurn normalization.normalizedRoot) g).cells =
            normalization.normalizedRoot.cells ∧ (TileTranslation (TileQuarterTurn
            normalization.normalizedFixed) g).cells = (SubtileOccurrenceInterpretation
            normalization.layout.P normalization.layout.u normalization.layout.v uBar).cells ∧
            (TileTranslation (TileQuarterTurn W) g).cells = (TileTranslation
            normalization.normalizedRoot ((wBlock.1 : GaussianInt) * normalization.layout.u +
            (wBlock.2 : GaussianInt) * normalization.layout.v)).cells ∧ (TileTranslation
            (TileQuarterTurn V) g).cells = (SubtileOccurrenceInterpretation
            normalization.layout.P normalization.layout.u normalization.layout.v vBar).cells ∧
            BandPrototile (Q normalization.normalizedParentSlot.succ)
            (SubtileOccurrenceInterpretation normalization.layout.P normalization.layout.u
            normalization.layout.v uIndex) ∧ BandPrototile (Q ((if Even
            normalization.normalizedQuarterTurn.val then normalization.normalizedParentSlot + 1
            else normalization.normalizedParentSlot - 1).succ)) V ∧
            ((SubtileOccurrenceInterpretation normalization.layout.P normalization.layout.u
            normalization.layout.v uIndex).cells = ∅ → (SubtileOccurrenceInterpretation
            normalization.layout.P normalization.layout.u normalization.layout.v uIndex).anchor =
            normalization.normalizedFixed.anchor) ∧ TileCentroid (SubtileOccurrenceInterpretation
            normalization.layout.P normalization.layout.u normalization.layout.v uIndex) -
            TileCentroid normalization.normalizedRoot = (1 / 2 : Real) • GaussianRealPoint ((⟨0,
            1⟩ : GaussianInt) ^ normalization.normalizedQuarterTurn.val * (incoming
            normalization.normalizedParentSlot + outgoing normalization.normalizedParentSlot)) ∧
            TileCentroid V - TileCentroid normalization.normalizedRoot = (1 / 2 : Real) •
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ normalization.normalizedQuarterTurn.val *
            (if Even normalization.normalizedQuarterTurn.val then incoming
            (normalization.normalizedParentSlot + 1) - outgoing
            (normalization.normalizedParentSlot + 1) else outgoing
            (normalization.normalizedParentSlot - 1) - incoming
            (normalization.normalizedParentSlot - 1))))))))))))))))))) ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization Q edge incoming outgoing hsuper hin0 hflips hin1
      hin2 hUcentroid hVcentroid occurrenceBand quarterSymmetricTranslation g hrootBar
      rotatedCentroid centeredCompare quarterTranslate hout0 hout1 rowsAt
  let uIndex : PeriodicSubtileIndex :=
    if normalization.normalizedParentSlot = 0 then
      if normalization.normalizedQuarterTurn = 0 then ⟨.A, 0, -1⟩
      else if normalization.normalizedQuarterTurn = 1 then ⟨.B, 1, 1⟩
      else if normalization.normalizedQuarterTurn = 2 then ⟨.B, 0, 1⟩
      else ⟨.A, -1, -1⟩
    else if normalization.normalizedParentSlot = 1 then
      if normalization.normalizedQuarterTurn = 0 then ⟨.C, 1, 1⟩
      else if normalization.normalizedQuarterTurn = 1 then ⟨.D, -1, 0⟩
      else if normalization.normalizedQuarterTurn = 2 then ⟨.D, -1, -1⟩
      else ⟨.C, 1, 0⟩
    else if normalization.normalizedQuarterTurn = 0 then ⟨.E, -1, 0⟩
    else if normalization.normalizedQuarterTurn = 1 then ⟨.F, 0, -1⟩
    else if normalization.normalizedQuarterTurn = 2 then ⟨.F, 1, 0⟩
    else ⟨.E, 0, 1⟩
  let vIndex : PeriodicSubtileIndex :=
    if normalization.normalizedParentSlot = 0 then
      if normalization.normalizedQuarterTurn = 0 then ⟨.C, 1, 0⟩
      else if normalization.normalizedQuarterTurn = 1 then ⟨.F, 1, 0⟩
      else if normalization.normalizedQuarterTurn = 2 then ⟨.D, -1, 0⟩
      else ⟨.E, -1, 0⟩
    else if normalization.normalizedParentSlot = 1 then
      if normalization.normalizedQuarterTurn = 0 then ⟨.E, 0, 1⟩
      else if normalization.normalizedQuarterTurn = 1 then ⟨.B, 0, 1⟩
      else if normalization.normalizedQuarterTurn = 2 then ⟨.F, 0, -1⟩
      else ⟨.A, 0, -1⟩
    else if normalization.normalizedQuarterTurn = 0 then ⟨.A, -1, -1⟩
    else if normalization.normalizedQuarterTurn = 1 then ⟨.D, -1, -1⟩
    else if normalization.normalizedQuarterTurn = 2 then ⟨.B, 1, 1⟩
    else ⟨.C, 1, 1⟩
  let wShift : GaussianInt :=
    (⟨0, 1⟩ : GaussianInt) ^ normalization.normalizedQuarterTurn.val *
      (if Even normalization.normalizedQuarterTurn.val then
        incoming normalization.normalizedParentSlot
      else outgoing normalization.normalizedParentSlot)
  let uBar : PeriodicSubtileIndex :=
    if normalization.normalizedParentSlot = 0 then
      if normalization.normalizedQuarterTurn = 0 then ⟨.B, 1, 1⟩
      else if normalization.normalizedQuarterTurn = 1 then ⟨.B, 0, 1⟩
      else if normalization.normalizedQuarterTurn = 2 then ⟨.A, -1, -1⟩
      else ⟨.A, 0, -1⟩
    else if normalization.normalizedParentSlot = 1 then
      if normalization.normalizedQuarterTurn = 0 then ⟨.D, -1, 0⟩
      else if normalization.normalizedQuarterTurn = 1 then ⟨.D, -1, -1⟩
      else if normalization.normalizedQuarterTurn = 2 then ⟨.C, 1, 0⟩
      else ⟨.C, 1, 1⟩
    else if normalization.normalizedQuarterTurn = 0 then ⟨.F, 0, -1⟩
    else if normalization.normalizedQuarterTurn = 1 then ⟨.F, 1, 0⟩
    else if normalization.normalizedQuarterTurn = 2 then ⟨.E, 0, 1⟩
    else ⟨.E, -1, 0⟩
  let vBar : PeriodicSubtileIndex :=
    if normalization.normalizedParentSlot = 0 then
      if normalization.normalizedQuarterTurn = 0 then ⟨.C, 1, 1⟩
      else if normalization.normalizedQuarterTurn = 1 then ⟨.E, 0, 1⟩
      else if normalization.normalizedQuarterTurn = 2 then ⟨.D, -1, -1⟩
      else ⟨.F, 0, -1⟩
    else if normalization.normalizedParentSlot = 1 then
      if normalization.normalizedQuarterTurn = 0 then ⟨.E, -1, 0⟩
      else if normalization.normalizedQuarterTurn = 1 then ⟨.A, -1, -1⟩
      else if normalization.normalizedQuarterTurn = 2 then ⟨.F, 1, 0⟩
      else ⟨.B, 1, 1⟩
    else if normalization.normalizedQuarterTurn = 0 then ⟨.A, 0, -1⟩
    else if normalization.normalizedQuarterTurn = 1 then ⟨.C, 1, 0⟩
    else if normalization.normalizedQuarterTurn = 2 then ⟨.B, 0, 1⟩
    else ⟨.D, -1, 0⟩
  let wBlock : Int × Int :=
    if normalization.normalizedParentSlot = 0 then
      if normalization.normalizedQuarterTurn = 0 ∨
          normalization.normalizedQuarterTurn = 3 then (1, 0) else (-1, 0)
    else if normalization.normalizedParentSlot = 1 then
      if normalization.normalizedQuarterTurn = 0 ∨
          normalization.normalizedQuarterTurn = 3 then (0, 1) else (0, -1)
    else if normalization.normalizedQuarterTurn = 0 ∨
        normalization.normalizedQuarterTurn = 3 then (-1, -1) else (1, 1)
  let U := SubtileOccurrenceInterpretation normalization.layout.P
    normalization.layout.u normalization.layout.v uIndex
  let V := SubtileOccurrenceInterpretation normalization.layout.P
    normalization.layout.u normalization.layout.v vIndex
  let W := TileTranslation normalization.normalizedRoot wShift
  have hUBand := SubtileInterfaceAssembly.hUBand C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization
  have hVBand := SubtileInterfaceAssembly.hVBand
          C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization
  have hUcent := hUcentroid
  have hfixedEq := BandPrototileCentroidUnique
    (Q normalization.normalizedParentSlot.succ) U normalization.normalizedFixed
    hUBand (SubtileInterfaceAssembly.hFixedBand C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization)
        (sub_left_inj.mp (hUcent.trans
      (SubtileInterfaceAssembly.hfixedCent C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization).symm))
  refine ⟨W, V, g, wShift, uIndex, uBar, vIndex, vBar, wBlock,
    (SubtileInterfaceAssembly.hrow' C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization), hfixedEq.1.symm,
        rfl, rfl, rfl, hrootBar, ?_, ?_, ?_,
    hUBand, hVBand, hfixedEq.2, hUcent, ?_⟩
  · let Ubar := SubtileOccurrenceInterpretation normalization.layout.P
      normalization.layout.u normalization.layout.v uBar
    have hrot := rotatedCentroid U Ubar _ hUcent (SubtileInterfaceAssembly.hUbarCent C₀ Cᵢ q i
        T₀ Tᵢ h₀ hᵢ x normalization rowsAt (SubtileInterfacePreparation.quarterPower))
    have hbar := centeredCompare _ U Ubar hUBand (SubtileInterfaceAssembly.hUbarBand C₀ Cᵢ q i
        T₀ Tᵢ h₀ hᵢ x normalization) (SubtileInterfaceAssembly.hUSym C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x
        normalization quarterSymmetricTranslation) hrot
    simpa [Ubar, U, TileTranslation, TileQuarterTurn, hfixedEq.1] using hbar.1
  · have hshift : GaussianQuarterTurn wShift =
        (wBlock.1 : GaussianInt) * normalization.layout.u +
          (wBlock.2 : GaussianInt) * normalization.layout.v := SubtileInterfaceAssembly.hshift
              C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization hflips hout0 hout1
                  (SubtileInterfacePreparation.hout2 C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization
                  hsuper hin0 hin1 hin2 hout0 hout1) (SubtileInterfacePreparation.quarterTurnMul)
    rw [show W = TileTranslation normalization.normalizedRoot wShift by rfl,
      quarterTranslate normalization.normalizedRoot wShift g, hshift]
    rw [(TileTranslationFormulas
      (TileTranslation (TileQuarterTurn normalization.normalizedRoot) g) _).1,
      (TileTranslationFormulas normalization.normalizedRoot _).1, hrootBar]
  · let Vbar := SubtileOccurrenceInterpretation normalization.layout.P
      normalization.layout.u normalization.layout.v vBar
    have hrot := rotatedCentroid V Vbar _ (by simpa [V, vIndex] using hVcentroid)
      (SubtileInterfaceAssembly.hVbarCent C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization hflips rowsAt)
    exact (centeredCompare _ V Vbar hVBand (SubtileInterfaceAssembly.hVbarBand C₀ Cᵢ q i T₀ Tᵢ
        h₀ hᵢ x normalization occurrenceBand) (SubtileInterfaceAssembly.hVSym C₀ Cᵢ q i T₀ Tᵢ
        h₀ hᵢ x normalization quarterSymmetricTranslation) hrot).1
  · simpa [V, vIndex] using hVcentroid

end SubtileInterfaceRowPackage

namespace SubtileInterfaceConclusion

private theorem subtileInterfaceCertificate :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin
            3), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralSubtileNormalizationCertificate C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x),
        let Q := normalization.normalizedPresentation
        let incoming : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (Q j.succ) (Q 0)
        let outgoing : Fin 3 → GaussianInt := fun j =>
          BandVectors.1 (Q 0) (Q j.succ)
        (ProperBandQuadruple Q) → ((LatticeTile normalization.normalizedRoot) →
            ((normalization.layout.O.cells ⊆ (normalization.layout.P (0 : Fin (3 : ℕ))
            true).cells) → ((normalization.layout.O.cells ⊆ (normalization.layout.P (0 : Fin (3 :
            ℕ)) false).cells) → (((∀ (m : ℤ), ∀ (n : ℤ), ∀ (x_1 : LatticeCell), x_1 ∈
            (TileTranslation normalization.normalizedRoot ((↑m : GaussianInt) *
            normalization.layout.u + (↑n : GaussianInt) * normalization.layout.v)).cells ↔ ∃
            (label : SixSubtileLabel), x_1 ∈ (ModifiedSubtileOccurrenceInterpretation
            normalization.layout.P normalization.layout.O normalization.layout.u
            normalization.layout.v ⟨label, m, n⟩).cells) ∧ ∀ (m : ℤ), ∀ (n : ℤ), ∀ (r : ℤ), ∀ (s
            : ℤ), (m, n) ≠ (r, s) → Disjoint (TileTranslation normalization.normalizedRoot ((↑m :
            GaussianInt) * normalization.layout.u + (↑n : GaussianInt) *
            normalization.layout.v)).cells (TileTranslation normalization.normalizedRoot ((↑r :
            GaussianInt) * normalization.layout.u + (↑s : GaussianInt) *
            normalization.layout.v)).cells) → (∀ (g : GaussianInt), ((TileTranslation
            (TileQuarterTurn normalization.normalizedRoot) g).cells =
            normalization.normalizedRoot.cells) → (∀ (uIndex : PeriodicSubtileIndex), ∀ (vIndex :
            PeriodicSubtileIndex), ∀ (uBar : PeriodicSubtileIndex), ∀ (vBar :
            PeriodicSubtileIndex), ∀ (wBlock : ℤ × ℤ), ∀ (wShift : GaussianInt), ∀ (V :
            ProtoTile), ∀ (W : ProtoTile), (normalization.normalizedParentSlot = (0 : Fin (3 :
            ℕ)) ∧ normalization.normalizedQuarterTurn = (0 : Fin (4 : ℕ)) ∧ uIndex =
            (⟨SixSubtileLabel.A, (0 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) ∧ uBar =
            (⟨SixSubtileLabel.B, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) ∧ wBlock = ((1 : ℤ),
            (0 : ℤ)) ∧ vIndex = (⟨SixSubtileLabel.C, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) ∧
            vBar = (⟨SixSubtileLabel.C, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) ∨
            normalization.normalizedParentSlot = (0 : Fin (3 : ℕ)) ∧
            normalization.normalizedQuarterTurn = (1 : Fin (4 : ℕ)) ∧ uIndex =
            (⟨SixSubtileLabel.B, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) ∧ uBar =
            (⟨SixSubtileLabel.B, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) ∧ wBlock = ((-1 : ℤ),
            (0 : ℤ)) ∧ vIndex = (⟨SixSubtileLabel.F, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) ∧
            vBar = (⟨SixSubtileLabel.E, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) ∨
            normalization.normalizedParentSlot = (0 : Fin (3 : ℕ)) ∧
            normalization.normalizedQuarterTurn = (2 : Fin (4 : ℕ)) ∧ uIndex =
            (⟨SixSubtileLabel.B, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) ∧ uBar =
            (⟨SixSubtileLabel.A, (-1 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) ∧ wBlock = ((-1 :
            ℤ), (0 : ℤ)) ∧ vIndex = (⟨SixSubtileLabel.D, (-1 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex) ∧ vBar = (⟨SixSubtileLabel.D, (-1 : ℤ), (-1 : ℤ)⟩ :
            PeriodicSubtileIndex) ∨ normalization.normalizedParentSlot = (0 : Fin (3 : ℕ)) ∧
            normalization.normalizedQuarterTurn = (3 : Fin (4 : ℕ)) ∧ uIndex =
            (⟨SixSubtileLabel.A, (-1 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) ∧ uBar =
            (⟨SixSubtileLabel.A, (0 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) ∧ wBlock = ((1 : ℤ),
            (0 : ℤ)) ∧ vIndex = (⟨SixSubtileLabel.E, (-1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) ∧
            vBar = (⟨SixSubtileLabel.F, (0 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) ∨
            normalization.normalizedParentSlot = (1 : Fin (3 : ℕ)) ∧
            normalization.normalizedQuarterTurn = (0 : Fin (4 : ℕ)) ∧ uIndex =
            (⟨SixSubtileLabel.C, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) ∧ uBar =
            (⟨SixSubtileLabel.D, (-1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) ∧ wBlock = ((0 : ℤ),
            (1 : ℤ)) ∧ vIndex = (⟨SixSubtileLabel.E, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) ∧
            vBar = (⟨SixSubtileLabel.E, (-1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) ∨
            normalization.normalizedParentSlot = (1 : Fin (3 : ℕ)) ∧
            normalization.normalizedQuarterTurn = (1 : Fin (4 : ℕ)) ∧ uIndex =
            (⟨SixSubtileLabel.D, (-1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) ∧ uBar =
            (⟨SixSubtileLabel.D, (-1 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) ∧ wBlock = ((0 : ℤ),
            (-1 : ℤ)) ∧ vIndex = (⟨SixSubtileLabel.B, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) ∧
            vBar = (⟨SixSubtileLabel.A, (-1 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) ∨
            normalization.normalizedParentSlot = (1 : Fin (3 : ℕ)) ∧
            normalization.normalizedQuarterTurn = (2 : Fin (4 : ℕ)) ∧ uIndex =
            (⟨SixSubtileLabel.D, (-1 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) ∧ uBar =
            (⟨SixSubtileLabel.C, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) ∧ wBlock = ((0 : ℤ),
            (-1 : ℤ)) ∧ vIndex = (⟨SixSubtileLabel.F, (0 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex)
            ∧ vBar = (⟨SixSubtileLabel.F, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) ∨
            normalization.normalizedParentSlot = (1 : Fin (3 : ℕ)) ∧
            normalization.normalizedQuarterTurn = (3 : Fin (4 : ℕ)) ∧ uIndex =
            (⟨SixSubtileLabel.C, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) ∧ uBar =
            (⟨SixSubtileLabel.C, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) ∧ wBlock = ((0 : ℤ),
            (1 : ℤ)) ∧ vIndex = (⟨SixSubtileLabel.A, (0 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) ∧
            vBar = (⟨SixSubtileLabel.B, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) ∨
            normalization.normalizedParentSlot = (2 : Fin (3 : ℕ)) ∧
            normalization.normalizedQuarterTurn = (0 : Fin (4 : ℕ)) ∧ uIndex =
            (⟨SixSubtileLabel.E, (-1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) ∧ uBar =
            (⟨SixSubtileLabel.F, (0 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) ∧ wBlock = ((-1 : ℤ),
            (-1 : ℤ)) ∧ vIndex = (⟨SixSubtileLabel.A, (-1 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex)
            ∧ vBar = (⟨SixSubtileLabel.A, (0 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) ∨
            normalization.normalizedParentSlot = (2 : Fin (3 : ℕ)) ∧
            normalization.normalizedQuarterTurn = (1 : Fin (4 : ℕ)) ∧ uIndex =
            (⟨SixSubtileLabel.F, (0 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) ∧ uBar =
            (⟨SixSubtileLabel.F, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) ∧ wBlock = ((1 : ℤ),
            (1 : ℤ)) ∧ vIndex = (⟨SixSubtileLabel.D, (-1 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex)
            ∧ vBar = (⟨SixSubtileLabel.C, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) ∨
            normalization.normalizedParentSlot = (2 : Fin (3 : ℕ)) ∧
            normalization.normalizedQuarterTurn = (2 : Fin (4 : ℕ)) ∧ uIndex =
            (⟨SixSubtileLabel.F, (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) ∧ uBar =
            (⟨SixSubtileLabel.E, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) ∧ wBlock = ((1 : ℤ),
            (1 : ℤ)) ∧ vIndex = (⟨SixSubtileLabel.B, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) ∧
            vBar = (⟨SixSubtileLabel.B, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) ∨
            normalization.normalizedParentSlot = (2 : Fin (3 : ℕ)) ∧
            normalization.normalizedQuarterTurn = (3 : Fin (4 : ℕ)) ∧ uIndex =
            (⟨SixSubtileLabel.E, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) ∧ uBar =
            (⟨SixSubtileLabel.E, (-1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex) ∧ wBlock = ((-1 : ℤ),
            (-1 : ℤ)) ∧ vIndex = (⟨SixSubtileLabel.C, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) ∧
            vBar = (⟨SixSubtileLabel.D, (-1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex)) →
            ((normalization.normalizedFixed.cells = (SubtileOccurrenceInterpretation
            normalization.layout.P normalization.layout.u normalization.layout.v uIndex).cells) →
            ((V.cells = (SubtileOccurrenceInterpretation normalization.layout.P
            normalization.layout.u normalization.layout.v vIndex).cells) → ((W = TileTranslation
            normalization.normalizedRoot wShift) → ((wShift = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)
            ^ (↑normalization.normalizedQuarterTurn : ℕ) * if Even
            (↑normalization.normalizedQuarterTurn : ℕ) then incoming
            normalization.normalizedParentSlot else outgoing normalization.normalizedParentSlot)
            → (((TileTranslation (TileQuarterTurn normalization.normalizedFixed) g).cells =
            (SubtileOccurrenceInterpretation normalization.layout.P normalization.layout.u
            normalization.layout.v uBar).cells) → (((TileTranslation (TileQuarterTurn W) g).cells
            = (TileTranslation normalization.normalizedRoot ((↑wBlock.1 : GaussianInt) *
            normalization.layout.u + (↑wBlock.2 : GaussianInt) * normalization.layout.v)).cells)
            → (((TileTranslation (TileQuarterTurn V) g).cells = (SubtileOccurrenceInterpretation
            normalization.layout.P normalization.layout.u normalization.layout.v vBar).cells) →
            ((BandPrototile (Q normalization.normalizedParentSlot.succ)
            (SubtileOccurrenceInterpretation normalization.layout.P normalization.layout.u
            normalization.layout.v uIndex)) → ((BandPrototile (Q (if Even
            (↑normalization.normalizedQuarterTurn : ℕ) then normalization.normalizedParentSlot +
            (1 : Fin (3 : ℕ)) else normalization.normalizedParentSlot - (1 : Fin (3 : ℕ))).succ)
            V) → (((SubtileOccurrenceInterpretation normalization.layout.P normalization.layout.u
            normalization.layout.v uIndex).cells = ∅ → (SubtileOccurrenceInterpretation
            normalization.layout.P normalization.layout.u normalization.layout.v uIndex).anchor =
            normalization.normalizedFixed.anchor) → ((TileCentroid
            (SubtileOccurrenceInterpretation normalization.layout.P normalization.layout.u
            normalization.layout.v uIndex) - TileCentroid normalization.normalizedRoot = (1 / 2 :
            ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^
            (↑normalization.normalizedQuarterTurn : ℕ) * (incoming
            normalization.normalizedParentSlot + outgoing normalization.normalizedParentSlot))) →
            ((TileCentroid V - TileCentroid normalization.normalizedRoot = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^
            (↑normalization.normalizedQuarterTurn : ℕ) * if Even
            (↑normalization.normalizedQuarterTurn : ℕ) then incoming
            (normalization.normalizedParentSlot + (1 : Fin (3 : ℕ))) - outgoing
            (normalization.normalizedParentSlot + (1 : Fin (3 : ℕ))) else outgoing
            (normalization.normalizedParentSlot - (1 : Fin (3 : ℕ))) - incoming
            (normalization.normalizedParentSlot - (1 : Fin (3 : ℕ))))) → (Nonempty
            (BandOrderedGeneralSubtileInterfaceCertificate normalization)))))))))))))))))))) ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization Q incoming outgoing hproper hrootLattice hOA hOB
      hblocks g hrootBar uIndex vIndex uBar vBar wBlock wShift V W hrow hfixedSource hVSource hW
      hwShift hfixedBar hWBar hVBar hSourceBand hOtherBand hSourceAnchor hSourceCentroid
      hOtherCentroid
  have hseparation := BandOrderedGeneralSubtileCanonicalSeparation
    normalization.layout.P normalization.layout.O normalization.normalizedRoot
    normalization.normalizedFixed W V normalization.layout.u normalization.layout.v
    g wShift normalization.normalizedParentSlot normalization.normalizedQuarterTurn
    uIndex uBar vIndex vBar wBlock hrow hrootLattice
    normalization.layout.parent_lattice hOA hOB normalization.layout.partition
    hblocks.1 hblocks.2 hfixedSource hVSource hW hrootBar hfixedBar hWBar hVBar
  rcases hseparation with
    ⟨hRootLattice, hFixedLattice, hWLattice, hVLattice,
      hRootFixed, hRootW, hFixedW, hRootV, hFixedV, hWV⟩
  let source := SubtileOccurrenceInterpretation normalization.layout.P
    normalization.layout.u normalization.layout.v uIndex
  change BandPrototile (Q normalization.normalizedParentSlot.succ) source at hSourceBand
  change normalization.normalizedFixed.cells = source.cells at hfixedSource
  change source.cells = ∅ →
    source.anchor = normalization.normalizedFixed.anchor at hSourceAnchor
  change TileCentroid source - TileCentroid normalization.normalizedRoot =
    (1 / 2 : Real) • GaussianRealPoint
      ((⟨0, 1⟩ : GaussianInt) ^ normalization.normalizedQuarterTurn.val *
        (incoming normalization.normalizedParentSlot +
          outgoing normalization.normalizedParentSlot)) at hSourceCentroid
  have hpaired :=
    (BandOrderedGeneralMixedAggregatePatches Q normalization.configuration
      normalization.normalizedCircle normalization.normalizedRoot
      normalization.layout normalization.root_quarter_turn).2.2
      normalization.normalizedParentSlot normalization.normalizedQuarterTurn
      source V hSourceBand hOtherBand hSourceCentroid hOtherCentroid
  dsimp only at hpaired
  obtain ⟨rightData, incomingRaw, t5Data, hrightPoint, hpointNe,
      hincomingOther, hrightOther, ht5Other⟩ := hpaired
  have hWExact : W = TileTranslation normalization.normalizedRoot
      ((⟨0, 1⟩ : GaussianInt) ^ normalization.normalizedQuarterTurn.val *
        (if Even normalization.normalizedQuarterTurn.val then
          BandVectors.1
            (Q normalization.normalizedParentSlot.succ) (Q 0)
        else BandVectors.1
            (Q 0) (Q normalization.normalizedParentSlot.succ))) := by
    rw [hW, hwShift]
  let incomingData : ExactTileInterfaceTriple
      normalization.normalizedRoot W source := hWExact.symm ▸ incomingRaw
  have hincomingPoint := (SubtileInterfaceAssembly.transportedEndpoints hWExact incomingRaw).1
  have hincomingOtherCA := (SubtileInterfaceAssembly.transportedEndpoints hWExact incomingRaw).2
  obtain ⟨startSource, hswapPoint, hswapOtherAB, hswapOtherBC,
      hswapOtherCA⟩ := ExactTileInterfaceTripleSwapLast
        normalization.normalizedRoot W source incomingData
  obtain ⟨startData, hstartPoint, hstartOtherAB, hstartOtherBC,
      hstartOtherCA⟩ := ExactTileInterfaceTripleRetargetMiddle
        normalization.normalizedRoot source normalization.normalizedFixed W
        hfixedSource.symm hSourceAnchor startSource
  obtain ⟨endData, hendPoint, hendOtherAB, hendOtherBC, hendOtherCA⟩ :=
    ExactTileInterfaceTripleRetargetMiddle
      normalization.normalizedRoot source normalization.normalizedFixed V
      hfixedSource.symm hSourceAnchor t5Data
  have hStartTouching : TouchingTriple normalization.normalizedRoot
      normalization.normalizedFixed W :=
    ExactTileInterfaceTripleLatticeTouching
      normalization.normalizedRoot normalization.normalizedFixed W startData
      hRootLattice hFixedLattice hWLattice hRootFixed hFixedW hRootW.symm
  have hEndTouching : TouchingTriple normalization.normalizedRoot
      normalization.normalizedFixed V :=
    ExactTileInterfaceTripleLatticeTouching
      normalization.normalizedRoot normalization.normalizedFixed V endData
      hRootLattice hFixedLattice hVLattice hRootFixed hFixedV hRootV.symm
  have hRootPositive : 0 < (Q 0).1 :=
    (ProperBandCurvatureStructure Q hproper).1
  have hFixedPositive :
      0 < normalization.normalizedFixedCircle.1.1.1 :=
    normalization.normalizedFixedCircle.2
  have hPointRoot : normalization.normalizedPoint ∈
      FootprintVertices normalization.normalizedRoot :=
    (Set.ext_iff.mp (PositiveCurvatureTileOdometerDomain
      (Q 0) normalization.normalizedRoot normalization.normalizedRootFunction
      hRootPositive normalization.normalized_root_odometer)
        normalization.normalizedPoint).mp
      normalization.normalized_point_root_domain
  have hPointFixed : normalization.normalizedPoint ∈
      FootprintVertices normalization.normalizedFixed :=
    (Set.ext_iff.mp (PositiveCurvatureTileOdometerDomain
      normalization.normalizedFixedCircle.1.1 normalization.normalizedFixed
      normalization.normalizedFixedFunction hFixedPositive
      normalization.normalized_fixed_odometer)
        normalization.normalizedPoint).mp
      normalization.normalized_point_fixed_domain
  exact ⟨{
    startCompanion := W
    endCompanion := V
    startData := startData
    endData := endData
    normalized_point_on_start_path := ⟨hPointRoot, hPointFixed⟩
    interface_endpoints := (by
      constructor
      · exact hendPoint.trans (hincomingOther.symm.trans (hincomingOtherCA.symm.trans
          (hswapOtherAB.symm.trans hstartOtherAB.symm)))
      · exact hendOtherAB.trans (ht5Other.trans (hincomingPoint.symm.trans
          (hswapPoint.symm.trans hstartPoint.symm))))
    root_lattice := hRootLattice
    fixed_lattice := hFixedLattice
    start_lattice := hWLattice
    end_lattice := hVLattice
    root_fixed_disjoint := hRootFixed
    root_start_disjoint := hRootW
    fixed_start_disjoint := hFixedW
    root_end_disjoint := hRootV
    fixed_end_disjoint := hFixedV
    start_end_disjoint := hWV
    start_touching := hStartTouching
    end_touching := hEndTouching }⟩

end SubtileInterfaceConclusion

theorem BandOrderedGeneralSubtileInterfaceCertificateExists
    {C₀ Cᵢ : BandCircle} {q : Fin 4 → CircleCoordinates}
    {i : Fin 3} {T₀ Tᵢ : ProtoTile}
    {h₀ hᵢ : PartialOdometer} {x : GaussianInt}
    (normalization : BandOrderedGeneralSubtileNormalizationCertificate
      C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x) :
    Nonempty (BandOrderedGeneralSubtileInterfaceCertificate normalization) := by
-- BODY
  let Q := normalization.normalizedPresentation
  let edge : Fin 3 → GaussianInt := fun j =>
    BandVectors.1 (Q ((j + 2).succ)) (Q ((j + 1).succ))
  let incoming : Fin 3 → GaussianInt := fun j =>
    BandVectors.1 (Q j.succ) (Q 0)
  let outgoing : Fin 3 → GaussianInt := fun j =>
    BandVectors.1 (Q 0) (Q j.succ)
  have hproper : ProperBandQuadruple Q := by
    simpa [Q] using normalization.configuration.proper
  obtain ⟨hsuper, _, hin0, _, hflip⟩ := VectorRecursionLaws Q hproper.1
  have hflips := hflip hproper
  let R : Fin 4 → CircleCoordinates := ![Q 0, Q 2, Q 3, Q 1]
  have hR : SemiProperQuadruple R := by
    simpa [R] using SemiProperQuadruple.rotate hproper.1
  let S : Fin 4 → CircleCoordinates := ![R 0, R 2, R 3, R 1]
  have hS : SemiProperQuadruple S := by
    simpa [S] using SemiProperQuadruple.rotate hR
  have hin1 : incoming 1 =
      edge 2 - (⟨0, 1⟩ : GaussianInt) * edge 0 := SubtileInterfacePreparation.hin1 C₀ Cᵢ q i T₀
          Tᵢ h₀ hᵢ x normalization hR
  have hin2 : incoming 2 =
      edge 0 - (⟨0, 1⟩ : GaussianInt) * edge 1 := SubtileInterfacePreparation.hin2 C₀ Cᵢ q i T₀
          Tᵢ h₀ hᵢ x normalization hS
  have hrows := BandOrderedGeneralSubtileCanonicalRows
    normalization.layout.P normalization.normalizedRoot
    normalization.layout.u normalization.layout.v
    normalization.normalizedParentSlot normalization.normalizedQuarterTurn
    edge incoming outgoing
    (by simpa [edge] using hsuper)
    (by simpa [incoming, edge] using hin0)
    hin1 hin2
    (by
      intro j
      simpa [incoming, outgoing] using (hflips j).1)
    (by simpa [outgoing, Q] using normalization.layout.period_u)
    (by simpa [outgoing, Q] using normalization.layout.period_v)
    (by
      intro j e
      simpa [edge, Q] using
        (normalization.layout.outer_occurrence j e).2.2)
  obtain ⟨hUcentroid, hVcentroid⟩ := hrows
  have hrootLattice : LatticeTile normalization.normalizedRoot :=
    (BandTileSimultaneousInduction Q hproper normalization.normalizedRoot
      (by simpa [Q] using normalization.root_band)).1
  have hOA := SubtileInterfacePreparation.hOA C₀ Cᵢ q i T₀ Tᵢ h₀
          hᵢ x normalization
  have hOB := SubtileInterfacePreparation.hOB C₀ Cᵢ q i T₀ Tᵢ
          h₀ hᵢ x normalization
  have hblocks := BandOrderedGeneralPeriodicBlockCells Q
    normalization.configuration normalization.normalizedCircle
    normalization.normalizedRoot normalization.layout
  have occurrenceBand := SubtileInterfacePreparation.occurrenceBand C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x
      normalization
  have quarterSymmetricTranslation := SubtileInterfaceGeometry.quarterSymmetricTranslation
  obtain ⟨g, hg, hrootBar, hrootAnchor, hrootFoot, hrootCentroid⟩ :=
    QuarterTurnSymmetricCenteredTransport normalization.normalizedRoot
      normalization.root_quarter_turn
  let uIndex : PeriodicSubtileIndex :=
    if normalization.normalizedParentSlot = 0 then
      if normalization.normalizedQuarterTurn = 0 then ⟨.A, 0, -1⟩
      else if normalization.normalizedQuarterTurn = 1 then ⟨.B, 1, 1⟩
      else if normalization.normalizedQuarterTurn = 2 then ⟨.B, 0, 1⟩
      else ⟨.A, -1, -1⟩
    else if normalization.normalizedParentSlot = 1 then
      if normalization.normalizedQuarterTurn = 0 then ⟨.C, 1, 1⟩
      else if normalization.normalizedQuarterTurn = 1 then ⟨.D, -1, 0⟩
      else if normalization.normalizedQuarterTurn = 2 then ⟨.D, -1, -1⟩
      else ⟨.C, 1, 0⟩
    else if normalization.normalizedQuarterTurn = 0 then ⟨.E, -1, 0⟩
    else if normalization.normalizedQuarterTurn = 1 then ⟨.F, 0, -1⟩
    else if normalization.normalizedQuarterTurn = 2 then ⟨.F, 1, 0⟩
    else ⟨.E, 0, 1⟩
  let vIndex : PeriodicSubtileIndex :=
    if normalization.normalizedParentSlot = 0 then
      if normalization.normalizedQuarterTurn = 0 then ⟨.C, 1, 0⟩
      else if normalization.normalizedQuarterTurn = 1 then ⟨.F, 1, 0⟩
      else if normalization.normalizedQuarterTurn = 2 then ⟨.D, -1, 0⟩
      else ⟨.E, -1, 0⟩
    else if normalization.normalizedParentSlot = 1 then
      if normalization.normalizedQuarterTurn = 0 then ⟨.E, 0, 1⟩
      else if normalization.normalizedQuarterTurn = 1 then ⟨.B, 0, 1⟩
      else if normalization.normalizedQuarterTurn = 2 then ⟨.F, 0, -1⟩
      else ⟨.A, 0, -1⟩
    else if normalization.normalizedQuarterTurn = 0 then ⟨.A, -1, -1⟩
    else if normalization.normalizedQuarterTurn = 1 then ⟨.D, -1, -1⟩
    else if normalization.normalizedQuarterTurn = 2 then ⟨.B, 1, 1⟩
    else ⟨.C, 1, 1⟩
  let uBar : PeriodicSubtileIndex :=
    if normalization.normalizedParentSlot = 0 then
      if normalization.normalizedQuarterTurn = 0 then ⟨.B, 1, 1⟩
      else if normalization.normalizedQuarterTurn = 1 then ⟨.B, 0, 1⟩
      else if normalization.normalizedQuarterTurn = 2 then ⟨.A, -1, -1⟩
      else ⟨.A, 0, -1⟩
    else if normalization.normalizedParentSlot = 1 then
      if normalization.normalizedQuarterTurn = 0 then ⟨.D, -1, 0⟩
      else if normalization.normalizedQuarterTurn = 1 then ⟨.D, -1, -1⟩
      else if normalization.normalizedQuarterTurn = 2 then ⟨.C, 1, 0⟩
      else ⟨.C, 1, 1⟩
    else if normalization.normalizedQuarterTurn = 0 then ⟨.F, 0, -1⟩
    else if normalization.normalizedQuarterTurn = 1 then ⟨.F, 1, 0⟩
    else if normalization.normalizedQuarterTurn = 2 then ⟨.E, 0, 1⟩
    else ⟨.E, -1, 0⟩
  let vBar : PeriodicSubtileIndex :=
    if normalization.normalizedParentSlot = 0 then
      if normalization.normalizedQuarterTurn = 0 then ⟨.C, 1, 1⟩
      else if normalization.normalizedQuarterTurn = 1 then ⟨.E, 0, 1⟩
      else if normalization.normalizedQuarterTurn = 2 then ⟨.D, -1, -1⟩
      else ⟨.F, 0, -1⟩
    else if normalization.normalizedParentSlot = 1 then
      if normalization.normalizedQuarterTurn = 0 then ⟨.E, -1, 0⟩
      else if normalization.normalizedQuarterTurn = 1 then ⟨.A, -1, -1⟩
      else if normalization.normalizedQuarterTurn = 2 then ⟨.F, 1, 0⟩
      else ⟨.B, 1, 1⟩
    else if normalization.normalizedQuarterTurn = 0 then ⟨.A, 0, -1⟩
    else if normalization.normalizedQuarterTurn = 1 then ⟨.C, 1, 0⟩
    else if normalization.normalizedQuarterTurn = 2 then ⟨.B, 0, 1⟩
    else ⟨.D, -1, 0⟩
  let wBlock : Int × Int :=
    if normalization.normalizedParentSlot = 0 then
      if normalization.normalizedQuarterTurn = 0 ∨
          normalization.normalizedQuarterTurn = 3 then (1, 0) else (-1, 0)
    else if normalization.normalizedParentSlot = 1 then
      if normalization.normalizedQuarterTurn = 0 ∨
          normalization.normalizedQuarterTurn = 3 then (0, 1) else (0, -1)
    else if normalization.normalizedQuarterTurn = 0 ∨
        normalization.normalizedQuarterTurn = 3 then (-1, -1) else (1, 1)
  let wShift : GaussianInt :=
    (⟨0, 1⟩ : GaussianInt) ^ normalization.normalizedQuarterTurn.val *
      (if Even normalization.normalizedQuarterTurn.val then
        incoming normalization.normalizedParentSlot
      else outgoing normalization.normalizedParentSlot)
  let V := SubtileOccurrenceInterpretation normalization.layout.P
    normalization.layout.u normalization.layout.v vIndex
  let W := TileTranslation normalization.normalizedRoot wShift
  have rowsAt (p : Fin 3) (t : Fin 4) :=
    BandOrderedGeneralSubtileCanonicalRows
      normalization.layout.P normalization.normalizedRoot
      normalization.layout.u normalization.layout.v p t edge incoming outgoing
      (by simpa [edge] using hsuper)
      (by simpa [incoming, edge] using hin0) hin1 hin2
      (by intro j; simpa [incoming, outgoing] using (hflips j).1)
      (by simpa [outgoing, Q] using normalization.layout.period_u)
      (by simpa [outgoing, Q] using normalization.layout.period_v)
      (by
        intro j e
        simpa [edge, Q] using
          (normalization.layout.outer_occurrence j e).2.2)
  have rowPackage := SubtileInterfaceRowPackage.rowPackage C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x normalization
                      hsuper hin0 hflips hin1 hin2 hUcentroid hVcentroid occurrenceBand
                      quarterSymmetricTranslation g hrootBar
                          (SubtileInterfacePreparation.rotatedCentroid C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x
                          normalization g hg) (SubtileInterfaceGeometry.centeredCompare g)
                      (TileQuarterTurnTranslation.translated)
                          (SubtileInterfacePreparation.hout0 C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x
                          normalization hflips) (SubtileInterfacePreparation.hout1 C₀ Cᵢ q i T₀
                          Tᵢ h₀ hᵢ x normalization hflips) rowsAt
  obtain ⟨W, V, g, wShift, uIndex, uBar, vIndex, vBar, wBlock,
      hrow, hfixedSource, hVSource, hW, hwShift, hrootBar, hfixedBar, hWBar,
      hVBar, hSourceBand, hOtherBand, hSourceAnchor, hSourceCentroid,
      hOtherCentroid⟩ := rowPackage
  exact (SubtileInterfaceConclusion.subtileInterfaceCertificate C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x
      normalization hproper hrootLattice hOA hOB hblocks g hrootBar uIndex vIndex uBar vBar
      wBlock wShift V W hrow hfixedSource hVSource hW hwShift hfixedBar hWBar hVBar hSourceBand
      hOtherBand hSourceAnchor hSourceCentroid hOtherCentroid)


end ApollonianSuperharmonic

end
