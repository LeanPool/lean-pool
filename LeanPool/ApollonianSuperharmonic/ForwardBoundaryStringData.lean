/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandVectorOrientationDichotomy
public import LeanPool.ApollonianSuperharmonic.BoundaryString
public import LeanPool.ApollonianSuperharmonic.TileOdometerReindexedDecomposition
public import LeanPool.ApollonianSuperharmonic.TileStringExists
public import LeanPool.ApollonianSuperharmonic.ParentVectorsInTilingLattice
public import LeanPool.ApollonianSuperharmonic.TileOdometerAffineTranslation
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile

-- [TABLET NODE: ForwardBoundaryStringData]

/-!
# ForwardBoundaryStringData

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ForwardBoundaryGeometry

private theorem hroot :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), (ProperBandQuadruple q) → ((BandCircle) → (∀ (i : Fin
            3), (0 < (q i.succ).1) → (1 < (q 0).1))) ) := by
  classical
  intro q hq Cᵢ i hparent
  have hlt := hq.2 i
  omega

private theorem hcyclic :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), (ProperBandQuadruple q) → (∀ (Cᵢ : BandCircle), ∀ (i
            : Fin 3), (q i.succ = Cᵢ.1.1) → (∀ (orientation : Bool), (Cᵢ.1.1.1 = (1 : ℤ) →
            UnitOccurrenceOrientation q i orientation) → ((0 < (q i.succ).1) → (∀ (S : Fin (3 :
            ℕ) → Bool → ProtoTile), ∀ (hs : Fin (3 : ℕ) → Bool → PartialOdometer),
        let B := S i false
        let g := hs i false
        (TileOdometer Cᵢ.1.1 B g) → ((BandPrototile Cᵢ.1.1 B) → (∀ (pouter : ℝ × ℝ), ∀ (pseed : ℝ
            × ℝ), (PartialOdometerSlope (hs i false) = some pseed) → ((pseed.1 - pouter.1 = (if
            false = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (q (i + (2
            : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (q
            (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)).im : ℝ))) → ((pseed.2
            - pouter.2 = (if false = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
            ((↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 :
            ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 :
            Fin (3 : ℕ))).succ)).re : ℝ))) → (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
            + BandVectors.1 (q i.succ) (q ((i + 2).succ)) + BandVectors.1 (q ((i + 1).succ)) (q
            i.succ) = 0 ∧ BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ)) + BandVectors.2 (q
            i.succ) (q ((i + 2).succ)) + BandVectors.2 (q ((i + 1).succ)) (q i.succ) = 0 ∧
            BandVectors.1 (q i.succ) (q 0) = BandVectors.1 (q i.succ) (q ((i + 2).succ)) - (⟨0,
            1⟩ : GaussianInt) * BandVectors.1 (q ((i + 1).succ)) (q i.succ) ∧ BandVectors.2 (q
            i.succ) (q 0) = BandVectors.2 (q i.succ) (q ((i + 2).succ)) + (⟨0, 1⟩ : GaussianInt)
            * BandVectors.2 (q ((i + 1).succ)) (q i.succ)))))))))) ) := by
  classical
  intro q hq Cᵢ i hCᵢ orientation horientation hparent S hs B g hBodometer hB pouter pseed hpseed
      hpre hpim
  fin_cases i
  · have h := VectorRecursionLaws q hq.1
    simpa using And.intro h.1 (And.intro h.2.1 (And.intro h.2.2.1 h.2.2.2.1))
  · have h := VectorRecursionLaws ![q 0, q 2, q 3, q 1]
      (SemiProperQuadruple.rotate hq.1)
    simpa using And.intro h.1 (And.intro h.2.1 (And.intro h.2.2.1 h.2.2.2.1))
  · have hr : SemiProperQuadruple ![q 0, q 3, q 1, q 2] := by
      simpa using SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hq.1)
    have h := VectorRecursionLaws ![q 0, q 3, q 1, q 2] hr
    simpa using And.intro h.1 (And.intro h.2.1 (And.intro h.2.2.1 h.2.2.2.1))

private theorem hseedIdentity :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (pouter : ℝ × ℝ), ∀ (pseed : ℝ × ℝ),
            (pseed.1 - pouter.1 = (if false = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
            ((↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 :
            ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 :
            Fin (3 : ℕ))).succ)).im : ℝ))) → ((pseed.2 - pouter.2 = (if false = true then (1 : ℝ)
            else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q
            (i + (1 : Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (q (i + (2 : Fin (3 :
            ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → ((BandVectors.2 (q (i + (2 :
            Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ) + BandVectors.2 (q i.succ) (q (i
            + (2 : Fin (3 : ℕ))).succ) + BandVectors.2 (q (i + (1 : Fin (3 : ℕ))).succ) (q
            i.succ) = (0 : GaussianInt)) → ((BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))) =
            BandVectors.2 (q i.succ) (q (i + (2 : Fin (3 : ℕ))).succ) + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.2 (q (i + (1 : Fin (3 : ℕ))).succ) (q i.succ)) →
            ((BandVectors.2 (q (0 : Fin (4 : ℕ))) (q i.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ)))) → (pseed +
            GaussianRealPoint (-BandVectors.2 (q ((i + 1).succ)) (q i.succ)) = pouter + (1 / 2 :
            Real) • GaussianRealPoint (BandVectors.2 (q i.succ) (q 0) - BandVectors.2 (q 0) (q
            i.succ))))))) ) := by
  classical
  intro q i pouter pseed hpre hpim hasum hachild haflip
  have sumre := congrArg (fun z : GaussianInt => (z.re : Real)) hasum
  have sumim := congrArg (fun z : GaussianInt => (z.im : Real)) hasum
  have childre := congrArg (fun z : GaussianInt => (z.re : Real)) hachild
  have childim := congrArg (fun z : GaussianInt => (z.im : Real)) hachild
  have flipre := congrArg (fun z : GaussianInt => (z.re : Real)) haflip
  have flipim := congrArg (fun z : GaussianInt => (z.im : Real)) haflip
  norm_num [Zsqrtd.re_mul, Zsqrtd.im_mul, -GaussianInt.intCast_re,
    -GaussianInt.intCast_im, -Int.cast_inj] at sumre sumim childre childim flipre flipim hpre hpim
  apply Prod.ext <;>
    simp [GaussianRealPoint, -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;>
    linarith only [sumre, sumim, childre, childim, flipre, flipim, hpre, hpim]

private theorem htangent :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
          ProperBandQuadruple q →
            ∀ (i : Fin (3 : ℕ)),
              BandTangency (q i.succ)
                (q (i + (2 : Fin (3 : ℕ))).succ)) := by
  classical
  intro q hq i
  refine ⟨q, hq.1, i.succ, (i + 2).succ, ?_, rfl, rfl⟩
  fin_cases i <;> decide

private theorem huplus :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (Cᵢ : BandCircle), ∀ (i : Fin 3),
        let uplus := (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q i.succ) (q ((i + 2).succ))
        (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q i.succ) ∈ TilingLattice Cᵢ) →
            ((BandTangency (q i.succ) (q ((i + 2).succ))) → (uplus ∈ TilingLattice Cᵢ)) ) := by
  classical
  intro q Cᵢ i uplus hvki htangent
  rcases BandVectorOrientationDichotomy _ _ htangent with h | h
  · simpa only [uplus, h.1] using hvki
  · simpa only [uplus, h.1] using (TilingLattice Cᵢ).neg_mem hvki

private theorem hseedSlope :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (hs : Fin (3 : ℕ) → Bool →
            PartialOdometer),
        let g := hs i false
        ∀ (pseed : ℝ × ℝ), (PartialOdometerSlope (hs i false) = some pseed) → (
        let uminus := -BandVectors.1 (q ((i + 1).succ)) (q i.succ)
        let hseed := PartialOdometerAffineTranslate g uminus 0 0
        PartialOdometerSlope hseed = some pseed) ) := by
  classical
  intro q i hs g pseed hpseed uminus hseed
  have h := (PartialOdometerAffineTranslateFormulas g uminus 0 0).2.2.2.2.2
  simpa [hseed, g, hpseed] using h

private theorem hendpoints :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (T₀ : ProtoTile), ∀ (S : Fin (3 : ℕ)
            → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid (S i s) -
            TileCentroid T₀ = (if s = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) •
            (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin
            (3 : ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 :
            ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (q
            (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).1))) → (
        let B := S i false
        (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ) +
            BandVectors.1 (q i.succ) (q (i + (2 : Fin (3 : ℕ))).succ) + BandVectors.1 (q (i + (1
            : Fin (3 : ℕ))).succ) (q i.succ) = (0 : GaussianInt)) → ((BandVectors.1 (q i.succ) (q
            (0 : Fin (4 : ℕ))) = BandVectors.1 (q i.succ) (q (i + (2 : Fin (3 : ℕ))).succ) - (⟨(0
            : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (q (i + (1 : Fin (3 : ℕ))).succ) (q
            i.succ)) → ((BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) → (
        let uminus := -BandVectors.1 (q ((i + 1).succ)) (q i.succ)
        let uplus := (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q i.succ) (q ((i + 2).succ))
        let Rminus := TileTranslation B uminus
        let Rplus := TileTranslation B uplus
        TileCentroid Rminus - TileCentroid T₀ = (1 / 2 : Real) • GaussianRealPoint (BandVectors.1
            (q i.succ) (q 0) - BandVectors.1 (q 0) (q i.succ)) ∧ TileCentroid Rplus -
            TileCentroid T₀ = (1 / 2 : Real) • GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)
            + BandVectors.1 (q 0) (q i.succ)))))) ) := by
  classical
  intro q i T₀ S hcentroid B hvsum hvchild hvflip uminus uplus Rminus Rplus
  have sumre := congrArg (fun z : GaussianInt => (z.re : Real)) hvsum
  have sumim := congrArg (fun z : GaussianInt => (z.im : Real)) hvsum
  have childre := congrArg (fun z : GaussianInt => (z.re : Real)) hvchild
  have childim := congrArg (fun z : GaussianInt => (z.im : Real)) hvchild
  have flipre := congrArg (fun z : GaussianInt => (z.re : Real)) hvflip
  have flipim := congrArg (fun z : GaussianInt => (z.im : Real)) hvflip
  have hbcentroid := hcentroid i false
  change TileCentroid B - TileCentroid T₀ = _ at hbcentroid
  have centre := congrArg Prod.fst hbcentroid
  have centim := congrArg Prod.snd hbcentroid
  norm_num [GaussianRealPoint, Zsqrtd.re_mul, Zsqrtd.im_mul,
    -GaussianInt.intCast_re, -GaussianInt.intCast_im,
    -Int.cast_inj] at sumre sumim childre childim
  norm_num [GaussianRealPoint, Zsqrtd.re_mul, Zsqrtd.im_mul,
    -GaussianInt.intCast_re, -GaussianInt.intCast_im,
    -Int.cast_inj] at flipre flipim centre centim
  constructor
  · change TileCentroid (TileTranslation B uminus) - TileCentroid T₀ = _
    rw [(TileTranslationFormulas B uminus).2.2.2.2.1]
    apply Prod.ext <;>
      simp [uminus, GaussianRealPoint, -GaussianInt.intCast_re,
        -GaussianInt.intCast_im] <;>
      linarith only [sumre, sumim, childre, childim, flipre, flipim, centre, centim]
  · change TileCentroid (TileTranslation B uplus) - TileCentroid T₀ = _
    rw [(TileTranslationFormulas B uplus).2.2.2.2.1]
    apply Prod.ext <;>
      simp [uplus, GaussianRealPoint, Zsqrtd.re_mul, Zsqrtd.im_mul,
        -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;>
      linarith only [sumre, sumim, childre, childim, flipre, flipim, centre, centim]

end ForwardBoundaryGeometry

theorem ForwardBoundaryStringData
    (q : Fin 4 -> CircleCoordinates) (hq : ProperBandQuadruple q)
    (C₀ Cᵢ : BandCircle) (i : Fin 3)
    (hC₀ : q 0 = C₀.1.1) (hCᵢ : q i.succ = Cᵢ.1.1)
    (orientation : Bool)
    (T₀ : ProtoTile) (h₀ : PartialOdometer)
    (hO₀ : TileOdometer C₀.1.1 T₀ h₀)
    (hpositive : 0 < Cᵢ.1.1.1)
    (horientation : Cᵢ.1.1.1 = 1 -> UnitOccurrenceOrientation q i orientation) :
    exists base Rminus Rplus : ProtoTile,
    exists tiles : List ProtoTile, exists hseed : PartialOdometer,
    exists pseed pouter : Real × Real,
      BandPrototile Cᵢ.1.1 base /\
      Rminus ∈ RegularTileFamily base (TilingLattice Cᵢ) /\
      Rplus ∈ RegularTileFamily base (TilingLattice Cᵢ) /\
      TileOdometer Cᵢ.1.1 Rminus hseed /\
      PartialOdometerSlope hseed = some pseed /\
      PartialOdometerSlope h₀ = some pouter /\
      pseed + GaussianRealPoint
          (-BandVectors.2 (q ((i + 1).succ)) (q i.succ)) =
        pouter + (1 / 2 : Real) • GaussianRealPoint
          (BandVectors.2 (q i.succ) (q 0) -
            BandVectors.2 (q 0) (q i.succ)) /\
      BoundaryString C₀ Cᵢ i orientation T₀ base Rminus Rplus tiles := by
-- BODY
  have hparent : 0 < (q i.succ).1 := by
    simpa only [hCᵢ] using hpositive
  have hroot : 1 < (q 0).1 := ForwardBoundaryGeometry.hroot q hq Cᵢ i hparent
  have houter : TileOdometer (q 0) T₀ h₀ := by
    simpa only [hC₀] using hO₀
  obtain ⟨S, hs, hT₀, hsub, _, _, hcentroid, _, _, _, hslope⟩ :=
    TileOdometerReindexedDecomposition q hq T₀ h₀ hroot houter
  let B := S i false
  let g := hs i false
  have hBodometer : TileOdometer Cᵢ.1.1 B g := by
    simpa only [B, g, hCᵢ] using hsub i false
  have hB : BandPrototile Cᵢ.1.1 B :=
    TileOdometerBandPrototile Cᵢ.1.1 B g hBodometer
  obtain ⟨pouter, pseed, hpouter, hpseed, hpre, hpim⟩ :=
    (hslope i false).resolve_left (ne_of_gt hparent)
  -- Rotate the recursion laws to the displayed parent occurrence.
  have hcyclic :
      BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ)) +
          BandVectors.1 (q i.succ) (q ((i + 2).succ)) +
          BandVectors.1 (q ((i + 1).succ)) (q i.succ) = 0 ∧
      BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ)) +
          BandVectors.2 (q i.succ) (q ((i + 2).succ)) +
          BandVectors.2 (q ((i + 1).succ)) (q i.succ) = 0 ∧
      BandVectors.1 (q i.succ) (q 0) =
          BandVectors.1 (q i.succ) (q ((i + 2).succ)) -
            (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q ((i + 1).succ)) (q i.succ) ∧
      BandVectors.2 (q i.succ) (q 0) =
          BandVectors.2 (q i.succ) (q ((i + 2).succ)) +
            (⟨0, 1⟩ : GaussianInt) * BandVectors.2 (q ((i + 1).succ)) (q i.succ) :=
                ForwardBoundaryGeometry.hcyclic q hq Cᵢ i hCᵢ orientation horientation hparent S
                hs hBodometer hB pouter pseed hpseed hpre hpim
  obtain ⟨hvsum, hasum, hvchild, hachild⟩ := hcyclic
  obtain ⟨hvflip, haflip⟩ := (VectorRecursionLaws q hq.1).2.2.2.2 hq i
  have hseedIdentity :
      pseed + GaussianRealPoint (-BandVectors.2 (q ((i + 1).succ)) (q i.succ)) =
        pouter + (1 / 2 : Real) • GaussianRealPoint
          (BandVectors.2 (q i.succ) (q 0) - BandVectors.2 (q 0) (q i.succ)) :=
              ForwardBoundaryGeometry.hseedIdentity q i pouter pseed hpre hpim hasum hachild haflip
  let uminus := -BandVectors.1 (q ((i + 1).succ)) (q i.succ)
  let uplus := (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q i.succ) (q ((i + 2).succ))
  let Rminus := TileTranslation B uminus
  let Rplus := TileTranslation B uplus
  obtain ⟨hvji, hvki⟩ := ParentVectorsInTilingLattice q hq i Cᵢ hCᵢ
  have huminus : uminus ∈ TilingLattice Cᵢ :=
    (TilingLattice Cᵢ).neg_mem hvji
  have htangent : BandTangency (q i.succ) (q ((i + 2).succ)) := ForwardBoundaryGeometry.htangent
      q hq i
  have huplus : uplus ∈ TilingLattice Cᵢ := ForwardBoundaryGeometry.huplus q Cᵢ i hvki htangent
  have hRminus : Rminus ∈ RegularTileFamily B (TilingLattice Cᵢ) :=
    ⟨uminus, huminus, rfl⟩
  have hRplus : Rplus ∈ RegularTileFamily B (TilingLattice Cᵢ) :=
    ⟨uplus, huplus, rfl⟩
  let hseed := PartialOdometerAffineTranslate g uminus 0 0
  have hseedO : TileOdometer Cᵢ.1.1 Rminus hseed :=
    TileOdometerAffineTranslation Cᵢ.1.1 B g uminus 0 0 hBodometer
  have hseedSlope : PartialOdometerSlope hseed = some pseed := ForwardBoundaryGeometry.hseedSlope
      q i hs pseed hpseed
  -- Apply the centroid formula to the two literal translated records.
  have hendpoints :
      TileCentroid Rminus - TileCentroid T₀ =
          (1 / 2 : Real) • GaussianRealPoint
            (BandVectors.1 (q i.succ) (q 0) - BandVectors.1 (q 0) (q i.succ)) ∧
      TileCentroid Rplus - TileCentroid T₀ =
          (1 / 2 : Real) • GaussianRealPoint
            (BandVectors.1 (q i.succ) (q 0) + BandVectors.1 (q 0) (q i.succ)) :=
                ForwardBoundaryGeometry.hendpoints q i T₀ S hcentroid hvsum hvchild hvflip
  obtain ⟨tiles, hstring⟩ := TileStringExists Cᵢ orientation B Rminus Rplus hB hRminus hRplus
  refine ⟨B, Rminus, Rplus, tiles, hseed, pseed, pouter,
    hB, hRminus, hRplus, hseedO, hseedSlope, hpouter, hseedIdentity, ?_⟩
  refine ⟨q, hq, hC₀, hCᵢ, ?_, horientation, hstring, hendpoints.1, hendpoints.2⟩
  simpa only [hC₀] using hT₀

end ApollonianSuperharmonic

end
