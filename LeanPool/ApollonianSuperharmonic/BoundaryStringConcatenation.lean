/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BoundaryString
public import LeanPool.ApollonianSuperharmonic.BoundaryJoinChamberCertificate
public import LeanPool.ApollonianSuperharmonic.OrientedUnimodularStripConcatenation
public import LeanPool.ApollonianSuperharmonic.TileStringCoordinateTransport

-- [TABLET NODE: BoundaryStringConcatenation]

/-!
# BoundaryStringConcatenation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace BoundaryConcatenationGeometry

private theorem hleft' :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (∀ (Cᵢ : BandCircle), ∀ (i :
            Fin 3), (q i.succ = Cᵢ.1.1) → (∀ (orientation : Bool), ∀ (leftOrientation : Bool),
            ((q i.succ).1 = (1 : ℤ) → UnitOccurrenceOrientation q i orientation) → (((q i.succ).1
            = (1 : ℤ) → UnitOccurrenceOrientation q i leftOrientation) → (∀ (base : ProtoTile), ∀
            (Tminus : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (left : List ProtoTile), (TileString
            Cᵢ leftOrientation base Rminus Tminus left) → (TileString Cᵢ orientation base Rminus
            Tminus left))))) ) := by
  classical
  intro q hq Cᵢ i hCᵢ orientation leftOrientation horientation hleftOrientation base Tminus
      Rminus left hleft
  by_cases hc : Cᵢ.1.1.1 = 1
  · have hqunit : (q i.succ).1 = 1 := by simpa [hCᵢ] using hc
    have horientEq : leftOrientation = orientation := by
      exact (UnitOccurrenceOrientationUnique.1 q hq i hqunit).unique
        (hleftOrientation hqunit) (horientation hqunit)
    simpa [horientEq] using hleft
  · simpa [TileString, hc] using hleft

private theorem hright' :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (∀ (Cᵢ : BandCircle), ∀ (i :
            Fin 3), (q i.succ = Cᵢ.1.1) → (∀ (orientation : Bool), ∀ (rightOrientation : Bool),
            ((q i.succ).1 = (1 : ℤ) → UnitOccurrenceOrientation q i orientation) → (((q i.succ).1
            = (1 : ℤ) → UnitOccurrenceOrientation q i rightOrientation) → (∀ (base : ProtoTile),
            ∀ (Tminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (right : List ProtoTile),
            (TileString Cᵢ rightOrientation base Tminus Rplus right) → (TileString Cᵢ orientation
            base Tminus Rplus right))))) ) := by
  classical
  intro q hq Cᵢ i hCᵢ orientation rightOrientation horientation hrightOrientation base Tminus
      Rplus right hright
  by_cases hc : Cᵢ.1.1.1 = 1
  · have hqunit : (q i.succ).1 = 1 := by simpa [hCᵢ] using hc
    have horientEq : rightOrientation = orientation := by
      exact (UnitOccurrenceOrientationUnique.1 q hq i hqunit).unique
        (hrightOrientation hqunit) (horientation hqunit)
    simpa [horientEq] using hright
  · simpa [TileString, hc] using hright

private theorem hcyc :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
          ProperBandQuadruple q →
            ∀ (i : Fin (3 : ℕ)),
              BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ)
                      (q (i + (1 : Fin (3 : ℕ))).succ) +
                    BandVectors.1
                      (q (i + (1 : Fin (3 : ℕ))).succ) (q i.succ) +
                  BandVectors.1 (q i.succ)
                    (q (i + (2 : Fin (3 : ℕ))).succ) =
                (0 : GaussianInt)) := by
  classical
  intro q hq i
  fin_cases i
  all_goals
    convert (VectorRecursionLaws q hq.1).1 using 1;
      simp [Fin.add_def]; abel

private theorem hin :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
          ProperBandQuadruple q →
            ∀ (i : Fin (3 : ℕ)),
              BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))) =
                BandVectors.1 (q i.succ)
                    (q (i + (2 : Fin (3 : ℕ))).succ) -
                  { re := (0 : ℤ), im := (1 : ℤ) } *
                    BandVectors.1
                      (q (i + (1 : Fin (3 : ℕ))).succ) (q i.succ)) := by
  classical
  intro q hq i
  fin_cases i
  · exact (VectorRecursionLaws q hq.1).2.2.1
  · have h := (VectorRecursionLaws (![q 0, q 2, q 3, q 1])
      (SemiProperQuadruple.rotate hq.1)).2.2.1
    simpa using h
  · have h := (VectorRecursionLaws (![q 0, q 3, q 1, q 2])
      (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hq.1))).2.2.1
    simpa using h

private theorem hrot :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩
        ∀ (z : GaussianInt), (-(GaussianRealPoint z).2, (GaussianRealPoint z).1) =
            GaussianRealPoint (I * z) ) := by
  classical
  intro I z
  ext <;> simp [GaussianRealPoint, I, Zsqrtd.re_mul, Zsqrtd.im_mul]

private theorem hminus' :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (T₀ : ProtoTile), ∀ (Tminus :
            ProtoTile), (TileCentroid Tminus - TileCentroid T₀ = (-1 : ℝ) • (1 / 2 : ℝ) •
            (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin
            (3 : ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 :
            ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (q
            (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).1))) → (
        let I : GaussianInt := ⟨0, 1⟩
        let w := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
        (∀ (z : GaussianInt), (-(GaussianRealPoint z).2, (GaussianRealPoint z).1) =
            GaussianRealPoint (I * z)) → (TileCentroid Tminus - TileCentroid T₀ = (-1 : ℝ) • ((1
            / 2 : ℝ) • (GaussianRealPoint w - GaussianRealPoint (I * w))))) ) := by
  classical
  intro q i T₀ Tminus hminus I w hrot
  simpa only [hrot] using hminus

private theorem hW :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), (BandVectors.1 (q ((i + 2).succ)) (q
            ((i + 1).succ)) + BandVectors.1 (q ((i + 1).succ)) (q i.succ) + BandVectors.1 (q
            i.succ) (q ((i + 2).succ)) = 0) → (
        let w := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
        let x := BandVectors.1 (q i.succ) (q ((i + 2).succ))
        let y := BandVectors.1 (q ((i + 1).succ)) (q i.succ)
        w = -x - y) ) := by
  classical
  intro q i hcyc w x y
  dsimp [w, x, y]
  linear_combination hcyc

private theorem hGplus :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3),
        let I : GaussianInt := ⟨0, 1⟩
        let w := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
        let x := BandVectors.1 (q i.succ) (q ((i + 2).succ))
        let y := BandVectors.1 (q ((i + 1).succ)) (q i.succ)
        (BandVectors.1 (q i.succ) (q 0) = x - I * y) → ((BandVectors.1 (q 0) (q i.succ) = I *
            BandVectors.1 (q i.succ) (q 0)) → ((I ^ 2 = -1) → ((w = -x - y) → (BandVectors.1 (q
            i.succ) (q 0) + BandVectors.1 (q 0) (q i.succ) + w - I * w = 2 * (I * x))))) ) := by
  classical
  intro q i I w x y hA hB hI2 hW
  rw [hA, hB, hA, hW]
  simp only [mul_sub]
  ring_nf
  rw [hI2]
  ring

private theorem hGminus :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3),
        let I : GaussianInt := ⟨0, 1⟩
        let w := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
        let x := BandVectors.1 (q i.succ) (q ((i + 2).succ))
        let y := BandVectors.1 (q ((i + 1).succ)) (q i.succ)
        (BandVectors.1 (q i.succ) (q 0) = x - I * y) → ((BandVectors.1 (q 0) (q i.succ) = I *
            BandVectors.1 (q i.succ) (q 0)) → ((I ^ 2 = -1) → ((w = -x - y) → (-w + I * w -
            BandVectors.1 (q i.succ) (q 0) + BandVectors.1 (q 0) (q i.succ) = 2 * y)))) ) := by
  classical
  intro q i I w x y hA hB hI2 hW
  rw [hA, hB, hA, hW]
  simp only [mul_sub]
  ring_nf
  rw [hI2]
  ring

private theorem hplus :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (T₀ : ProtoTile), ∀ (Tminus :
            ProtoTile), ∀ (Rplus : ProtoTile), (TileCentroid Rplus - TileCentroid T₀ = (1 / 2 :
            ℝ) • GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))) +
            BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → (
        let I : GaussianInt := ⟨0, 1⟩
        let w := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
        let x := BandVectors.1 (q i.succ) (q ((i + 2).succ))
        (TileCentroid Tminus - TileCentroid T₀ = (-1 : ℝ) • ((1 / 2 : ℝ) • (GaussianRealPoint w -
            GaussianRealPoint (I * w)))) → ((((GaussianInt.toComplex : GaussianInt → ℂ)
            (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))).re + ((GaussianInt.toComplex :
            GaussianInt → ℂ) (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))).re +
            ((GaussianInt.toComplex : GaussianInt → ℂ) w).re + ((GaussianInt.toComplex :
            GaussianInt → ℂ) w).im = -((2 : ℝ) * ((GaussianInt.toComplex : GaussianInt → ℂ)
            x).im)) → ((((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.1 (q i.succ) (q
            (0 : Fin (4 : ℕ))))).im + ((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.1
            (q (0 : Fin (4 : ℕ))) (q i.succ))).im + ((GaussianInt.toComplex : GaussianInt → ℂ)
            w).im - ((GaussianInt.toComplex : GaussianInt → ℂ) w).re = (2 : ℝ) *
            ((GaussianInt.toComplex : GaussianInt → ℂ) x).re) → (TileCentroid Rplus -
            TileCentroid Tminus = GaussianRealPoint (I * x))))) ) := by
  classical
  intro q i T₀ Tminus Rplus hRplus I w x hminus' hGplusRe hGplusIm
  calc
    _ = (TileCentroid Rplus - TileCentroid T₀) -
        (TileCentroid Tminus - TileCentroid T₀) := by
      ext <;> simp
    _ = _ := by
      rw [hRplus, hminus']
      ext <;> simp [GaussianRealPoint, Prod.smul_def,
        Zsqrtd.re_add, Zsqrtd.im_add,
        Zsqrtd.re_mul, Zsqrtd.im_mul, I] <;>
        nlinarith [hGplusRe, hGplusIm]

private theorem hminusInc :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (T₀ : ProtoTile), ∀ (Tminus :
            ProtoTile), ∀ (Rminus : ProtoTile), (TileCentroid Rminus - TileCentroid T₀ = (1 / 2 :
            ℝ) • GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))) -
            BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → (
        let I : GaussianInt := ⟨0, 1⟩
        let w := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
        let y := BandVectors.1 (q ((i + 1).succ)) (q i.succ)
        (TileCentroid Tminus - TileCentroid T₀ = (-1 : ℝ) • ((1 / 2 : ℝ) • (GaussianRealPoint w -
            GaussianRealPoint (I * w)))) → ((-((GaussianInt.toComplex : GaussianInt → ℂ) w).re +
            -((GaussianInt.toComplex : GaussianInt → ℂ) w).im - ((GaussianInt.toComplex :
            GaussianInt → ℂ) (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))).re +
            ((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q
            i.succ))).re = (2 : ℝ) * ((GaussianInt.toComplex : GaussianInt → ℂ) y).re) →
            ((-((GaussianInt.toComplex : GaussianInt → ℂ) w).im + ((GaussianInt.toComplex :
            GaussianInt → ℂ) w).re - ((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.1 (q
            i.succ) (q (0 : Fin (4 : ℕ))))).im + ((GaussianInt.toComplex : GaussianInt → ℂ)
            (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))).im = (2 : ℝ) *
            ((GaussianInt.toComplex : GaussianInt → ℂ) y).im) → (TileCentroid Tminus -
            TileCentroid Rminus = GaussianRealPoint y)))) ) := by
  classical
  intro q i T₀ Tminus Rminus hRminus I w y hminus' hGminusRe hGminusIm
  calc
    _ = (TileCentroid Tminus - TileCentroid T₀) -
        (TileCentroid Rminus - TileCentroid T₀) := by
      ext <;> simp
    _ = _ := by
      rw [hminus', hRminus]
      ext <;> simp [GaussianRealPoint, Prod.smul_def,
        Zsqrtd.re_sub, Zsqrtd.im_sub,
        Zsqrtd.re_mul, Zsqrtd.im_mul, I] <;>
        nlinarith [hGminusRe, hGminusIm]

private theorem translationDiff :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (u : GaussianInt), ∀ (v : GaussianInt), TileCentroid
            (TileTranslation base u) - TileCentroid (TileTranslation base v) = GaussianRealPoint
            (u - v) ) := by
  classical
  intro base u v
  rw [(TileTranslationFormulas base u).2.2.2.2.1,
    (TileTranslationFormulas base v).2.2.2.2.1]
  ext <;> simp [GaussianRealPoint, Zsqrtd.re_sub, Zsqrtd.im_sub];


private theorem hGRinj :
    (by
      classical
      exact
        Function.Injective GaussianRealPoint ) := by
  classical
  intro u v huv
  ext
  · have h := congrArg Prod.fst huv
    dsimp [GaussianRealPoint] at h
    exact_mod_cast h
  · have h := congrArg Prod.snd huv
    dsimp [GaussianRealPoint] at h
    exact_mod_cast h

private theorem hphysMinus :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (Tminus : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (e :
            GaussianInt), ∀ (f : GaussianInt), ∀ (r : ℤ × ℤ), (Rminus = TileTranslation base
            ((↑r.1 : GaussianInt) * e + (↑r.2 : GaussianInt) * f)) → (∀ (m : ℤ × ℤ), (Tminus =
            TileTranslation base ((↑m.1 : GaussianInt) * e + (↑m.2 : GaussianInt) * f)) → (
        let coord := fun z : Int × Int =>
          (z.1 : GaussianInt) * e + (z.2 : GaussianInt) * f
        (∀ (u : GaussianInt), ∀ (v : GaussianInt), TileCentroid (TileTranslation base u) -
            TileCentroid (TileTranslation base v) = GaussianRealPoint (u - v)) → (TileCentroid
            Tminus - TileCentroid Rminus = GaussianRealPoint (coord m - coord r)))) ) := by
  classical
  intro base Tminus Rminus e f r hr m hm coord translationDiff
  rw [hm, hr]
  exact translationDiff _ _

private theorem hphysPlus :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (Tminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (e : GaussianInt),
            ∀ (f : GaussianInt), ∀ (m : ℤ × ℤ), (Tminus = TileTranslation base ((↑m.1 :
            GaussianInt) * e + (↑m.2 : GaussianInt) * f)) → (∀ (s : ℤ × ℤ), (Rplus =
            TileTranslation base ((↑s.1 : GaussianInt) * e + (↑s.2 : GaussianInt) * f)) → (
        let coord := fun z : Int × Int =>
          (z.1 : GaussianInt) * e + (z.2 : GaussianInt) * f
        (∀ (u : GaussianInt), ∀ (v : GaussianInt), TileCentroid (TileTranslation base u) -
            TileCentroid (TileTranslation base v) = GaussianRealPoint (u - v)) → (TileCentroid
            Rplus - TileCentroid Tminus = GaussianRealPoint (coord s - coord m)))) ) := by
  classical
  intro base Tminus Rplus e f m hm s hs coord translationDiff
  rw [hs, hm]
  exact translationDiff _ _

private theorem hdispMinus :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (Tminus : ProtoTile), ∀ (Rminus :
            ProtoTile), ∀ (e : GaussianInt), ∀ (f : GaussianInt), ∀ (r : ℤ × ℤ), ∀ (m : ℤ × ℤ),
        let y := BandVectors.1 (q ((i + 1).succ)) (q i.succ)
        (TileCentroid Tminus - TileCentroid Rminus = GaussianRealPoint y) → (
        let coord := fun z : Int × Int =>
          (z.1 : GaussianInt) * e + (z.2 : GaussianInt) * f
        (Function.Injective GaussianRealPoint) → ((TileCentroid Tminus - TileCentroid Rminus =
            GaussianRealPoint (coord m - coord r)) → (coord m - coord r = y))) ) := by
  classical
  intro q i Tminus Rminus e f r m y hminusInc coord hGRinj hphysMinus
  apply hGRinj
  exact hphysMinus.symm.trans hminusInc

private theorem hdispPlus :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (Tminus : ProtoTile), ∀ (Rplus :
            ProtoTile), ∀ (e : GaussianInt), ∀ (f : GaussianInt), ∀ (m : ℤ × ℤ), ∀ (s : ℤ × ℤ),
        let I : GaussianInt := ⟨0, 1⟩
        let x := BandVectors.1 (q i.succ) (q ((i + 2).succ))
        (TileCentroid Rplus - TileCentroid Tminus = GaussianRealPoint (I * x)) → (
        let coord := fun z : Int × Int =>
          (z.1 : GaussianInt) * e + (z.2 : GaussianInt) * f
        (Function.Injective GaussianRealPoint) → ((TileCentroid Rplus - TileCentroid Tminus =
            GaussianRealPoint (coord s - coord m)) → (coord s - coord m = I * x))) ) := by
  classical
  intro q i Tminus Rplus e f m s I x hplus coord hGRinj hphysPlus
  apply hGRinj
  exact hphysPlus.symm.trans hplus

private theorem hcoordMinus :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (e : GaussianInt), ∀ (f :
            GaussianInt), ∀ (r : ℤ × ℤ), ∀ (m : ℤ × ℤ),
        let y := BandVectors.1 (q ((i + 1).succ)) (q i.succ)
        let coord := fun z : Int × Int =>
          (z.1 : GaussianInt) * e + (z.2 : GaussianInt) * f
        (coord m - coord r = y) → (coord (m - r) = y) ) := by
  classical
  intro q i e f r m y coord hdispMinus
  calc
    coord (m - r) = coord m - coord r := by
      dsimp [coord]
      ext <;> simp [Int.cast_sub, sub_mul] <;> ring
    _ = y := hdispMinus

private theorem hcoordPlus :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (e : GaussianInt), ∀ (f :
            GaussianInt), ∀ (m : ℤ × ℤ), ∀ (s : ℤ × ℤ),
        let I : GaussianInt := ⟨0, 1⟩
        let x := BandVectors.1 (q i.succ) (q ((i + 2).succ))
        let coord := fun z : Int × Int =>
          (z.1 : GaussianInt) * e + (z.2 : GaussianInt) * f
        (coord s - coord m = I * x) → (coord (s - m) = I * x) ) := by
  classical
  intro q i e f m s I x coord hdispPlus
  calc
    coord (s - m) = coord s - coord m := by
      dsimp [coord]
      ext <;> simp [Int.cast_sub, sub_mul] <;> ring
    _ = I * x := hdispPlus

private theorem coord_mem :
    (by
      classical
      exact
        ∀ (Cᵢ : BandCircle), ∀ (e : GaussianInt), ∀ (f : GaussianInt), (e ∈ TilingLattice Cᵢ) →
            ((f ∈ TilingLattice Cᵢ) → (
        let coord := fun z : Int × Int =>
          (z.1 : GaussianInt) * e + (z.2 : GaussianInt) * f
        ∀ (z : Int × Int), coord z ∈ TilingLattice Cᵢ)) ) := by
  classical
  intro Cᵢ e f he hf coord z
  dsimp [coord]
  apply AddSubgroup.add_mem
  · simpa using AddSubgroup.zsmul_mem (TilingLattice Cᵢ) he z.1
  · simpa using AddSubgroup.zsmul_mem (TilingLattice Cᵢ) hf z.2

private theorem coord_inj :
    (by
      classical
      exact
        ∀ (Cᵢ : BandCircle), ∀ (e : GaussianInt), ∀ (f : GaussianInt), (∀ (w : ↥(TilingLattice
            Cᵢ)), ∃! z : ℤ × ℤ, (↑z.1 : GaussianInt) * e + (↑z.2 : GaussianInt) * f = (↑w :
            GaussianInt)) → (
        let coord := fun z : Int × Int =>
          (z.1 : GaussianInt) * e + (z.2 : GaussianInt) * f
        (∀ (z : Int × Int), coord z ∈ TilingLattice Cᵢ) → (Function.Injective coord)) ) := by
  classical
  intro Cᵢ e f hcoord coord coord_mem z z' hzz
  let w : TilingLattice Cᵢ := ⟨coord z, coord_mem z⟩
  obtain ⟨u, hu, huuniq⟩ := hcoord w
  have hz : coord z = (w : GaussianInt) := rfl
  have hz' : coord z' = (w : GaussianInt) := hzz.symm.trans hz
  exact (huuniq z hz).trans (huuniq z' hz').symm

private theorem hmr :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (e : GaussianInt), ∀ (f :
            GaussianInt), ∀ (r : ℤ × ℤ), ∀ (m : ℤ × ℤ),
        let y := BandVectors.1 (q ((i + 1).succ)) (q i.succ)
        let coord := fun z : Int × Int =>
          (z.1 : GaussianInt) * e + (z.2 : GaussianInt) * f
        (coord (m - r) = y) → ((Function.Injective coord) → (∀ (σ : ℤ × ℤ ≃+ ℤ × ℤ), ∀ (a : ℤ), ∀
            (b : ℤ), (coord (σ.symm (a, b)) = y) → (m - r = σ.symm (a, b)))) ) := by
  classical
  intro q i e f r m y coord hcoordMinus coord_inj σ a b hσminus'
  apply coord_inj
  exact hcoordMinus.trans hσminus'.symm

private theorem hsm :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (e : GaussianInt), ∀ (f :
            GaussianInt), ∀ (m : ℤ × ℤ), ∀ (s : ℤ × ℤ),
        let I : GaussianInt := ⟨0, 1⟩
        let x := BandVectors.1 (q i.succ) (q ((i + 2).succ))
        let coord := fun z : Int × Int =>
          (z.1 : GaussianInt) * e + (z.2 : GaussianInt) * f
        (coord (s - m) = I * x) → ((Function.Injective coord) → (∀ (σ : ℤ × ℤ ≃+ ℤ × ℤ), ∀ (c :
            ℤ), ∀ (d : ℤ), (coord (σ.symm (c, d)) = I * x) → (s - m = σ.symm (c, d)))) ) := by
  classical
  intro q i e f m s I x coord hcoordPlus coord_inj σ c d hσplus'
  apply coord_inj
  exact hcoordPlus.trans hσplus'.symm

private theorem hσm :
    (by
      classical
      exact
        ∀ (r : ℤ × ℤ), ∀ (m : ℤ × ℤ), ∀ (σ : ℤ × ℤ ≃+ ℤ × ℤ), ∀ (a : ℤ), ∀ (b : ℤ), (σ (m - r) =
            (a, b)) → (σ m = σ r + (a, b)) ) := by
  classical
  intro r m σ a b hσmr
  have h := hσmr
  rw [map_sub] at h
  calc
    σ m = (σ m - σ r) + σ r := by abel
    _ = (a, b) + σ r := by rw [h]
    _ = σ r + (a, b) := by abel

private abbrev hσs :=
  ApollonianSuperharmonic.BoundaryConcatenationGeometry.hσm

private theorem hDimage :
    (by
      classical
      exact
        ∀ (σ : ℤ × ℤ ≃+ ℤ × ℤ), (∀ (x : ℤ × ℤ), ∀ (y : ℤ × ℤ), TriangularLatticeAdjacent ((σ : ℤ
            × ℤ → ℤ × ℤ) x) ((σ : ℤ × ℤ → ℤ × ℤ) y) ↔ TriangularLatticeAdjacent x y) → (
        let D : Finset (Int × Int) :=
          {(1, 0), (0, 1), (-1, -1), (-1, 0), (0, -1), (1, 1)}
        (∀ (z : Int × Int), z ∈ D ↔ TriangularLatticeAdjacent 0 z) → ((σ (0 : Int × Int) = 0) →
            (D.image σ = D))) ) := by
  classical
  intro σ hσadj D hD hσ0
  ext z
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩
    apply (hD (σ u)).mpr
    have h := (hσadj 0 u).mpr ((hD u).mp hu)
    simpa only [hσ0] using h
  · intro hz
    have hpre : TriangularLatticeAdjacent 0 (σ.symm z) := by
      have hz' : TriangularLatticeAdjacent (σ 0)
          (σ (σ.symm z)) := by simpa only [hσ0, σ.apply_symm_apply] using (hD z).mp hz
      exact (hσadj 0 (σ.symm z)).mp hz'
    exact ⟨σ.symm z, (hD _).mpr hpre, by simp⟩

private theorem hmaxRep :
    (by
      classical
      exact
        let D : Finset (Int × Int) :=
          {(1, 0), (0, 1), (-1, -1), (-1, 0), (0, -1), (1, 1)}
        ∀ (hDne : D.Nonempty), ∀ (u : Int × Int), ∀ (v : Int × Int), TriangularMaxIncrement u v =
            D.sup' hDne (fun z => |TriangularSignedHeight u v (u + z)|) ) := by
  classical
  intro D hDne u v
  simp only [TriangularMaxIncrement, abs_sub_comm, Int.reduceNeg, TriangularSignedHeight,
      Prod.add_def, add_sub_cancel_left, Finset.insert_nonempty, Finset.sup'_insert, mul_zero,
      mul_one, zero_sub, neg_sub, sub_zero, mul_neg, Finset.singleton_nonempty,
      Finset.sup'_singleton, max_left_comm, le_max_iff, Std.le_refl, true_or, sup_of_le_right,
      or_true, D]
  have hcross : u.1 - v.1 - (u.2 - v.2) =
      -(v.1 - u.1 - (v.2 - u.2)) := by ring
  rw [hcross, abs_neg]
  simp

private theorem hmaxσ :
    (by
      classical
      exact
        ∀ (σ : ℤ × ℤ ≃+ ℤ × ℤ), (∀ (x : ℤ × ℤ), ∀ (y : ℤ × ℤ), ∀ (z : ℤ × ℤ),
            TriangularSignedHeight ((σ : ℤ × ℤ → ℤ × ℤ) x) ((σ : ℤ × ℤ → ℤ × ℤ) y) ((σ : ℤ × ℤ →
            ℤ × ℤ) z) = TriangularSignedHeight x y z) → (
        let D : Finset (Int × Int) :=
          {(1, 0), (0, 1), (-1, -1), (-1, 0), (0, -1), (1, 1)}
        (D.image σ = D) → (∀ (hDne : D.Nonempty), (∀ (u : Int × Int), ∀ (v : Int × Int),
            TriangularMaxIncrement u v = D.sup' hDne (fun z => |TriangularSignedHeight u v (u +
            z)|)) → (∀ (u : Int × Int), ∀ (v : Int × Int), TriangularMaxIncrement (σ u) (σ v) =
            TriangularMaxIncrement u v))) ) := by
  classical
  intro σ hσheight D hDimage hDne hmaxRep u v
  rw [hmaxRep, hmaxRep]
  let g : (Int × Int) → Int := fun z =>
    |TriangularSignedHeight (σ u) (σ v) (σ u + z)|
  have himageNe : (D.image σ).Nonempty := Finset.image_nonempty.mpr hDne
  calc
    D.sup' hDne g = (D.image σ).sup' himageNe g := by
      exact (Finset.sup'_congr (s := D) (H := hDne)
        (t := D.image σ) (f := g) (g := g) hDimage.symm
        (by intro z hz; rfl))
    _ = D.sup' hDne (g ∘ σ) := by
      exact Finset.sup'_image (α := Int) (β := Int × Int)
        (γ := Int × Int) (f := σ) himageNe g
    _ = D.sup' hDne (fun z => |TriangularSignedHeight u v (u + z)|) := by
      apply Finset.sup'_congr (s := D) (H := hDne) (t := D)
        (f := g ∘ σ) (g := fun z => |TriangularSignedHeight u v (u + z)|) rfl
      intro z hz
      dsimp [g]
      rw [← hσheight u v (u + z)]
      rw [← map_add σ u z]

private theorem mapSegment :
    (by
      classical
      exact
        ∀ (ρ : (Int × Int) ≃+ (Int × Int)), (∀ x, ∀ y, TriangularLatticeAdjacent (ρ x) (ρ y) ↔
            TriangularLatticeAdjacent x y) → ((∀ x, ∀ y, ∀ z, TriangularSignedHeight (ρ x) (ρ y)
                (ρ z) =
              TriangularSignedHeight x y z) → ((∀ x, ∀ y, TriangularMaxIncrement (ρ x) (ρ y) =
                  TriangularMaxIncrement x y) → (∀ {x : Int × Int}, ∀ {y : Int × Int}, ∀
                  {path : List (Int × Int)}, (TriangularStripSegment x y path) →
                  (TriangularStripSegment (ρ x) (ρ y) (path.map ρ))))) ) := by
  classical
  intro ρ hadjρ hheightρ hmaxρ x y path hseg
  by_cases hxy : x = y
  · subst y
    simp only [TriangularStripSegment] at hseg
    subst path
    simp [TriangularStripSegment]
  · have hρxy : ρ x ≠ ρ y := by
      intro heq
      apply hxy
      exact ρ.injective heq
    simp only [TriangularStripSegment, ite_eq_right hxy] at hseg
    simp only [TriangularStripSegment, ite_eq_right hρxy]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [hseg.1]
    · simp [hseg.2.1]
    · exact hseg.2.2.1.map ρ.injective
    · intro z hz
      rcases List.mem_map.mp hz with ⟨p, hp, rfl⟩
      have hstrip := hseg.2.2.2.1 p hp
      change 0 ≤ TriangularSignedHeight (ρ x) (ρ y) (ρ p) ∧
        TriangularSignedHeight (ρ x) (ρ y) (ρ p) <
          TriangularMaxIncrement (ρ x) (ρ y)
      rw [hheightρ x y p, hmaxρ x y]
      exact hstrip
    · apply (List.isChain_map ρ).mpr
      exact hseg.2.2.2.2.imp (fun u v huv => (hadjρ u v).mpr huv)

private theorem hσrNe :
    (by
      classical
      exact
        ∀ (r : ℤ × ℤ), ∀ (m : ℤ × ℤ), ∀ (σ : ℤ × ℤ ≃+ ℤ × ℤ), ∀ (a : ℤ), ∀ (b : ℤ), ∀ (c : ℤ), ∀
            (d : ℤ), (a * d - b * c = (-1 : ℤ)) → ((σ (m - r) = (a, b)) → (σ r ≠ σ m)) ) := by
  classical
  intro r m σ a b c d hdetσ hσmr heq
  have hzero : (a, b) = 0 := by
    calc
      (a, b) = σ (m - r) := hσmr.symm
      _ = σ m - σ r := by rw [map_sub]
      _ = 0 := by rw [heq]; simp
  have ha : a = 0 := by simpa using congrArg Prod.fst hzero
  have hb : b = 0 := by simpa using congrArg Prod.snd hzero
  rw [ha, hb] at hdetσ
  norm_num at hdetσ

private theorem hinvAdj :
    (by
      classical
      exact
        ∀ (σ : ℤ × ℤ ≃+ ℤ × ℤ), (∀ (x : ℤ × ℤ), ∀ (y : ℤ × ℤ), TriangularLatticeAdjacent ((σ : ℤ
            × ℤ → ℤ × ℤ) x) ((σ : ℤ × ℤ → ℤ × ℤ) y) ↔ TriangularLatticeAdjacent x y) → (∀ (u :
            Int × Int), ∀ (v : Int × Int), TriangularLatticeAdjacent (σ.symm u) (σ.symm v) ↔
            TriangularLatticeAdjacent u v) ) := by
  classical
  intro σ hσadj u v
  simpa using (hσadj (σ.symm u) (σ.symm v)).symm

private theorem hinvHeight :
    (by
      classical
      exact
        ∀ (σ : ℤ × ℤ ≃+ ℤ × ℤ), (∀ (x : ℤ × ℤ), ∀ (y : ℤ × ℤ), ∀ (z : ℤ × ℤ),
            TriangularSignedHeight ((σ : ℤ × ℤ → ℤ × ℤ) x) ((σ : ℤ × ℤ → ℤ × ℤ) y) ((σ : ℤ × ℤ →
            ℤ × ℤ) z) = TriangularSignedHeight x y z) → (∀ (u : Int × Int), ∀ (v : Int × Int), ∀
            (z : Int × Int), TriangularSignedHeight (σ.symm u) (σ.symm v) (σ.symm z) =
            TriangularSignedHeight u v z) ) := by
  classical
  intro σ hσheight u v z
  simpa using (hσheight (σ.symm u) (σ.symm v) (σ.symm z)).symm

private theorem hinvMax :
    (by
      classical
      exact
        ∀ (σ : ℤ × ℤ ≃+ ℤ × ℤ), (∀ (u : Int × Int), ∀ (v : Int × Int), TriangularMaxIncrement (σ
            u) (σ v) = TriangularMaxIncrement u v) → (∀ (u : Int × Int), ∀ (v : Int × Int),
            TriangularMaxIncrement (σ.symm u) (σ.symm v) = TriangularMaxIncrement u v) ) := by
  classical
  intro σ hmaxσ u v
  simpa using (hmaxσ (σ.symm u) (σ.symm v)).symm

private theorem hcoordSegment' :
    (by
      classical
      exact
        ∀ (r : ℤ × ℤ), ∀ (s : ℤ × ℤ), ∀ (P : List (ℤ × ℤ)), ∀ (Q : List (ℤ × ℤ)), ∀ (σ : ℤ × ℤ ≃+
            ℤ × ℤ), ∀ (a : ℤ), ∀ (b : ℤ), ∀ (c : ℤ), ∀ (d : ℤ), (σ s = σ r + (a, b) + (c, d)) →
            ((TriangularStripSegment ((σ.symm : ℤ × ℤ → ℤ × ℤ) ((σ : ℤ × ℤ → ℤ × ℤ) r)) ((σ.symm
            : ℤ × ℤ → ℤ × ℤ) ((σ : ℤ × ℤ → ℤ × ℤ) r + (a, b) + (c, d))) (List.map (⇑σ.symm : ℤ ×
            ℤ → ℤ × ℤ) ((List.map (⇑σ : ℤ × ℤ → ℤ × ℤ) P).dropLast ++ List.map (⇑σ : ℤ × ℤ → ℤ ×
            ℤ) Q))) → (TriangularStripSegment r s (P.dropLast ++ Q))) ) := by
  classical
  intro r s P Q σ a b c d htotal hcoordSegment
  have hfirst : σ.symm (σ r) = r := by simp
  have hlast : σ.symm (σ r + (a, b) + (c, d)) = s := by
    apply σ.injective
    simpa using htotal.symm
  simpa [List.map_append, List.map_dropLast, List.map_map,
    Function.comp_def, Equiv.symm_apply_apply, hfirst, hlast] using hcoordSegment

private theorem dropLastForall₂ :
    (by
      classical
      exact
        ∀ {α : Type}, ∀ {β : Type}, ∀ {R : α → β → Prop}, ∀ {xs : List α}, ∀ {ys : List β},
            List.Forall₂ R xs ys → List.Forall₂ R xs.dropLast ys.dropLast ) := by
  classical
  intro α β R xs ys h
  induction h with
  | nil => simp
  | @cons x y xs ys hxy htail ih =>
      cases htail with
      | nil => simp
      | cons hnext hrest =>
          simpa only [List.dropLast_cons_cons] using
            (List.Forall₂.cons hxy ih)

private theorem appendForall₂ :
    (by
      classical
      exact
        ∀ {α : Type}, ∀ {β : Type}, ∀ {R : α → β → Prop}, ∀ {xs : List α}, ∀ {ys : List β}, ∀
            {us : List α}, ∀ {vs : List β}, List.Forall₂ R xs ys → List.Forall₂ R us vs →
            List.Forall₂ R (xs ++ us) (ys ++ vs) ) := by
  classical
  intro α β R xs ys us vs h
  induction h with
  | nil => intro htail; simpa using htail
  | cons hxy hrest ih =>
      intro htail
      exact List.Forall₂.cons hxy (ih htail)

private theorem hcorrespondence :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (left : List ProtoTile), ∀ (right : List ProtoTile), ∀ (e :
            GaussianInt), ∀ (f : GaussianInt), ∀ (r : ℤ × ℤ), ∀ (m : ℤ × ℤ), ∀ (s : ℤ × ℤ), ∀ (P
            : List (ℤ × ℤ)), (List.Forall₂ (fun (T : ProtoTile) (z : ℤ × ℤ) => T =
            TileTranslation base ((↑z.1 : GaussianInt) * e + (↑z.2 : GaussianInt) * f)) left P ∧
            TriangularStripSegment r m P) → (∀ (Q : List (ℤ × ℤ)), (List.Forall₂ (fun (T :
            ProtoTile) (z : ℤ × ℤ) => T = TileTranslation base ((↑z.1 : GaussianInt) * e + (↑z.2
            : GaussianInt) * f)) right Q ∧ TriangularStripSegment m s Q) → ((∀ {α : Type}, ∀
            {β : Type}, ∀ {R : α → β → Prop}, ∀ {xs : List α}, ∀ {ys : List β}, List.Forall₂ R xs
            ys → List.Forall₂ R xs.dropLast ys.dropLast) → ((∀ {α : Type}, ∀ {β : Type}, ∀
            {R : α → β → Prop}, ∀ {xs : List α}, ∀ {ys : List β}, ∀ {us : List α}, ∀
            {vs : List β}, List.Forall₂ R xs ys → List.Forall₂ R us vs → List.Forall₂ R (xs ++
            us) (ys ++ vs)) → (List.Forall₂ (fun T z => T = TileTranslation base ((z.1 :
            GaussianInt) * e + (z.2 : GaussianInt) * f)) (left.dropLast ++ right) (P.dropLast ++
            Q))))) ) := by
  classical
  intro base left right e f r m s P hP Q hQ dropLastForall₂ appendForall₂
  exact appendForall₂ (dropLastForall₂ hP.1) hQ.1

private theorem htiles :
    (by
      classical
      exact
        ∀ (Cᵢ : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus :
            ProtoTile), ∀ (Rplus : ProtoTile), ∀ (left : List ProtoTile), ∀ (right : List
            ProtoTile), ∀ (e : GaussianInt), ∀ (f : GaussianInt), (∀ (R : ProtoTile), ∀ (S :
            ProtoTile), ∀ (tiles : List ProtoTile), ∀ (r : ℤ × ℤ), ∀ (s : ℤ × ℤ), R =
            TileTranslation base ((↑r.1 : GaussianInt) * e + (↑r.2 : GaussianInt) * f) → S =
            TileTranslation base ((↑s.1 : GaussianInt) * e + (↑s.2 : GaussianInt) * f) →
            (TileString Cᵢ orientation base R S tiles ↔ ∃! coordinates : List (ℤ × ℤ),
            List.Forall₂ (fun (T : ProtoTile) (z : ℤ × ℤ) => T = TileTranslation base ((↑z.1 :
            GaussianInt) * e + (↑z.2 : GaussianInt) * f)) tiles coordinates ∧
            TriangularStripSegment r s coordinates)) → (∀ (r : ℤ × ℤ), (Rminus = TileTranslation
            base ((↑r.1 : GaussianInt) * e + (↑r.2 : GaussianInt) * f)) → (∀ (s : ℤ × ℤ), (Rplus
            = TileTranslation base ((↑s.1 : GaussianInt) * e + (↑s.2 : GaussianInt) * f)) → (∀ (P
            : List (ℤ × ℤ)), ∀ (Q : List (ℤ × ℤ)), (TriangularStripSegment r s (P.dropLast ++ Q))
            → ((List.Forall₂ (fun T z => T = TileTranslation base ((z.1 : GaussianInt) * e + (z.2
            : GaussianInt) * f)) (left.dropLast ++ right) (P.dropLast ++ Q)) → (TileString Cᵢ
            orientation base Rminus Rplus (left.dropLast ++ right)))))) ) := by
  classical
  intro Cᵢ orientation base Rminus Rplus left right e f htransport r hr s hs P Q hcoordSegment'
      hcorrespondence
  apply (htransport Rminus Rplus (left.dropLast ++ right) r s hr hs).mpr
  refine ⟨P.dropLast ++ Q, ⟨hcorrespondence, hcoordSegment'⟩, ?_⟩
  intro other hother
  exact (AffineTriangularStrip).1 r s |>.unique hother.2 hcoordSegment'

private theorem horientation' :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (Cᵢ : BandCircle), ∀ (i : Fin 3), (q i.succ =
            Cᵢ.1.1) → (∀ (orientation : Bool), ((q i.succ).1 = (1 : ℤ) →
            UnitOccurrenceOrientation q i orientation) → (Cᵢ.1.1.1 = 1 →
            UnitOccurrenceOrientation q i orientation)) ) := by
  classical
  intro q Cᵢ i hCᵢ orientation horientation hc
  apply horientation
  simpa [hCᵢ] using hc

end BoundaryConcatenationGeometry

theorem BoundaryStringConcatenation
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (C₀ Cᵢ : BandCircle) (i : Fin 3)
    (hC₀ : q 0 = C₀.1.1) (hCᵢ : q i.succ = Cᵢ.1.1)
    (orientation leftOrientation rightOrientation : Bool)
    (horientation : (q i.succ).1 = 1 →
      UnitOccurrenceOrientation q i orientation)
    (hleftOrientation : (q i.succ).1 = 1 →
      UnitOccurrenceOrientation q i leftOrientation)
    (hrightOrientation : (q i.succ).1 = 1 →
      UnitOccurrenceOrientation q i rightOrientation)
    (T₀ base Tminus Rminus Rplus : ProtoTile)
    (left right : List ProtoTile)
    (hT₀ : BandPrototile (q 0) T₀)
    (hminus : TileCentroid Tminus - TileCentroid T₀ =
      (-1 : ℝ) • ((1 / 2 : ℝ) •
        (GaussianRealPoint
            (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))) -
          (-((GaussianRealPoint
              (BandVectors.1 (q ((i + 2).succ))
                (q ((i + 1).succ)))).2),
            (GaussianRealPoint
              (BandVectors.1 (q ((i + 2).succ))
                (q ((i + 1).succ)))).1))))
    (hRminus : TileCentroid Rminus - TileCentroid T₀ =
      (1 / 2 : ℝ) • GaussianRealPoint
        (BandVectors.1 (q i.succ) (q 0) - BandVectors.1 (q 0) (q i.succ)))
    (hRplus : TileCentroid Rplus - TileCentroid T₀ =
      (1 / 2 : ℝ) • GaussianRealPoint
        (BandVectors.1 (q i.succ) (q 0) + BandVectors.1 (q 0) (q i.succ)))
    (hleft : TileString Cᵢ leftOrientation base Rminus Tminus left)
    (hright : TileString Cᵢ rightOrientation base Tminus Rplus right) :
    TileCentroid Rplus - TileCentroid Tminus =
        GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) *
            BandVectors.1 (q i.succ) (q ((i + 2).succ))) ∧
    TileCentroid Tminus - TileCentroid Rminus =
        GaussianRealPoint
          (BandVectors.1 (q ((i + 1).succ)) (q i.succ)) ∧
    BoundaryString C₀ Cᵢ i orientation T₀ base Rminus Rplus
      (left.dropLast ++ right) := by
-- BODY
  classical
  have hbase : BandPrototile Cᵢ.1.1 base := hleft.1
  have hleft' := BoundaryConcatenationGeometry.hleft' q hq Cᵢ i hCᵢ orientation leftOrientation
      horientation hleftOrientation base Tminus Rminus left hleft
  have hright' := BoundaryConcatenationGeometry.hright' q hq Cᵢ i hCᵢ orientation
      rightOrientation horientation hrightOrientation base Tminus Rplus right hright
  obtain ⟨e, f, hdet, he, hf, hcoord, horientChart, hchart⟩ :=
    TileStringCoordinateTransport Cᵢ orientation base hbase
  dsimp only at hchart
  obtain ⟨hfamily, hadj, hheight, htransport⟩ := hchart
  have hRminusMem : Rminus ∈ RegularTileFamily base (TilingLattice Cᵢ) := by
    exact hleft'.2.2.2.2.1 Rminus (List.mem_of_mem_head? hleft'.2.1)
  have hTminusMem : Tminus ∈ RegularTileFamily base (TilingLattice Cᵢ) := by
    exact hleft'.2.2.2.2.1 Tminus (List.mem_of_getLast? hleft'.2.2.1)
  have hRplusMem : Rplus ∈ RegularTileFamily base (TilingLattice Cᵢ) := by
    exact hright'.2.2.2.2.1 Rplus (List.mem_of_getLast? hright'.2.2.1)
  obtain ⟨r, hr, hruniq⟩ := (hfamily Rminus).mp hRminusMem
  obtain ⟨m, hm, hmuniq⟩ := (hfamily Tminus).mp hTminusMem
  obtain ⟨s, hs, hsuniq⟩ := (hfamily Rplus).mp hRplusMem
  obtain ⟨P, hP, hPuniq⟩ := (htransport Rminus Tminus left r m hr hm).mp hleft'
  obtain ⟨Q, hQ, hQuniq⟩ := (htransport Tminus Rplus right m s hm hs).mp hright'
  have hcyc := BoundaryConcatenationGeometry.hcyc q hq i
  have hin : BandVectors.1 (q i.succ) (q 0) =
      BandVectors.1 (q i.succ) (q ((i + 2).succ)) -
        (⟨0, 1⟩ : GaussianInt) *
          BandVectors.1 (q ((i + 1).succ)) (q i.succ) := BoundaryConcatenationGeometry.hin q hq i
  have hflip := (VectorRecursionLaws q hq.1).2.2.2.2 hq i
  let I : GaussianInt := ⟨0, 1⟩
  let w := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
  let x := BandVectors.1 (q i.succ) (q ((i + 2).succ))
  let y := BandVectors.1 (q ((i + 1).succ)) (q i.succ)
  have hminus' := BoundaryConcatenationGeometry.hminus' q i T₀ Tminus hminus
      (BoundaryConcatenationGeometry.hrot)
  have hA : BandVectors.1 (q i.succ) (q 0) = x - I * y := by
    simpa [x, y, I] using hin
  have hB : BandVectors.1 (q 0) (q i.succ) = I *
      BandVectors.1 (q i.succ) (q 0) := hflip.1
  have hI : I * I = -1 := by
    ext <;> norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul]
  have hI2 : I ^ 2 = -1 := by rw [pow_two, hI]
  have hW := BoundaryConcatenationGeometry.hW q i hcyc
  have hGplus := BoundaryConcatenationGeometry.hGplus q i hA hB hI2 hW
  have hGminus := BoundaryConcatenationGeometry.hGminus q i hA hB hI2 hW
  have hGplusRe := congrArg (fun z : GaussianInt => (z.re : ℝ)) hGplus
  have hGplusIm := congrArg (fun z : GaussianInt => (z.im : ℝ)) hGplus
  have hGminusRe := congrArg (fun z : GaussianInt => (z.re : ℝ)) hGminus
  have hGminusIm := congrArg (fun z : GaussianInt => (z.im : ℝ)) hGminus
  simp only [Int.reduceNeg, Fin.isValue, Zsqrtd.re_sub, Zsqrtd.re_add, Zsqrtd.re_mul,
      zero_mul, mul_one, neg_mul, one_mul, zero_add, sub_neg_eq_add, Int.cast_add,
      GaussianInt.intCast_re, GaussianInt.intCast_im, Zsqrtd.re_ofNat, Nat.cast_ofNat,
      mul_neg, Zsqrtd.im_ofNat, mul_zero, Zsqrtd.im_mul, add_zero, Int.cast_neg, Int.cast_mul,
      Int.cast_ofNat, Zsqrtd.im_sub, Zsqrtd.im_add, Int.cast_sub, neg_zero, Zsqrtd.re_neg,
      Zsqrtd.im_neg] at hGplusRe hGplusIm hGminusRe hGminusIm
  have hplus := BoundaryConcatenationGeometry.hplus q i T₀ Tminus Rplus hRplus hminus' hGplusRe
      hGplusIm
  have hminusInc := BoundaryConcatenationGeometry.hminusInc q i T₀ Tminus Rminus hRminus hminus'
      hGminusRe hGminusIm
  let coord := fun z : Int × Int =>
    (z.1 : GaussianInt) * e + (z.2 : GaussianInt) * f
  have translationDiff := BoundaryConcatenationGeometry.translationDiff base
  have hGRinj := BoundaryConcatenationGeometry.hGRinj
  have hcoordMinus := BoundaryConcatenationGeometry.hcoordMinus q i e f r m
      (BoundaryConcatenationGeometry.hdispMinus q i Tminus Rminus e f r m hminusInc hGRinj
      (BoundaryConcatenationGeometry.hphysMinus base Tminus Rminus e f r hr m hm translationDiff))
  have hcoordPlus := BoundaryConcatenationGeometry.hcoordPlus q i e f m s
      (BoundaryConcatenationGeometry.hdispPlus q i Tminus Rplus e f m s hplus hGRinj
      (BoundaryConcatenationGeometry.hphysPlus base Tminus Rplus e f m hm s hs translationDiff))
  have coord_inj := BoundaryConcatenationGeometry.coord_inj Cᵢ e f hcoord
      (BoundaryConcatenationGeometry.coord_mem Cᵢ e f he hf)
  have hch := BoundaryJoinChamberCertificate q hq Cᵢ i hCᵢ orientation
    horientation base hbase e f hdet he hf hcoord hadj
  dsimp only at hch
  obtain ⟨σ, hσadj, hσheight, a, b, c, d,
    hσminus, hσplus, hb0, hba, hd0, hdc, hdetσ⟩ := hch
  have hab : 0 ≤ b ∧ b ≤ a := ⟨hb0, hba⟩
  have hcd : 0 ≤ d ∧ d ≤ c := ⟨hd0, hdc⟩
  have hσminus' : coord (σ.symm (a, b)) = y := by
    simpa [coord] using hσminus
  have hσplus' : coord (σ.symm (c, d)) = I * x := by
    simpa [coord] using hσplus
  have hmr : m - r = σ.symm (a, b) := BoundaryConcatenationGeometry.hmr q i e f r m hcoordMinus
      coord_inj σ a b hσminus'
  have hsm : s - m = σ.symm (c, d) := BoundaryConcatenationGeometry.hsm q i e f m s hcoordPlus
      coord_inj σ c d hσplus'
  have hσmr : σ (m - r) = (a, b) := by rw [hmr]; simp
  have hσsm : σ (s - m) = (c, d) := by rw [hsm]; simp
  have hσm : σ m = σ r + (a, b) := BoundaryConcatenationGeometry.hσm r m σ a b hσmr
  have hσs : σ s = σ m + (c, d) := BoundaryConcatenationGeometry.hσs m s σ c d hσsm
  let D : Finset (Int × Int) :=
    {(1, 0), (0, 1), (-1, -1), (-1, 0), (0, -1), (1, 1)}
  have hD (z : Int × Int) : z ∈ D ↔ TriangularLatticeAdjacent 0 z := by
    simp [D, TriangularLatticeAdjacent]
  have hσ0 : σ (0 : Int × Int) = 0 := σ.map_zero
  have hDne : D.Nonempty := by simp [D]
  have hmaxσ := BoundaryConcatenationGeometry.hmaxσ σ hσheight
      (BoundaryConcatenationGeometry.hDimage σ hσadj hD hσ0) hDne
      (BoundaryConcatenationGeometry.hmaxRep hDne)
  have mapSegment (ρ : (Int × Int) ≃+ (Int × Int))
      (hadjρ : ∀ x y, TriangularLatticeAdjacent (ρ x) (ρ y) ↔
        TriangularLatticeAdjacent x y)
      (hheightρ : ∀ x y z,
        TriangularSignedHeight (ρ x) (ρ y) (ρ z) =
          TriangularSignedHeight x y z)
      (hmaxρ : ∀ x y,
        TriangularMaxIncrement (ρ x) (ρ y) = TriangularMaxIncrement x y)
      {x y : Int × Int} {path : List (Int × Int)}
      (hseg : TriangularStripSegment x y path) := BoundaryConcatenationGeometry.mapSegment ρ
          hadjρ hheightρ hmaxρ (x := x) (y := y) (path := path) hseg
  have hσrNe := BoundaryConcatenationGeometry.hσrNe r m σ a b c d hdetσ hσmr
  have hPσ := mapSegment σ hσadj hσheight hmaxσ hP.2
  rw [hσm] at hPσ
  have hQσ := mapSegment σ hσadj hσheight hmaxσ hQ.2
  rw [hσs, hσm] at hQσ
  have hjoined := OrientedUnimodularStripConcatenation (σ r) a b c d
    hab hcd hdetσ (P.map σ) (Q.map σ) hPσ hQσ
  have htotal : σ s = σ r + (a, b) + (c, d) := by
    rw [hσs, hσm]
  have hcoordSegment := mapSegment σ.symm (BoundaryConcatenationGeometry.hinvAdj σ hσadj)
      (BoundaryConcatenationGeometry.hinvHeight σ hσheight)
      (BoundaryConcatenationGeometry.hinvMax σ hmaxσ) hjoined
  have hT₀' : BandPrototile C₀.1.1 T₀ := by simpa [hC₀] using hT₀
  exact ⟨hplus, hminusInc,
    ⟨q, hq, hC₀, hCᵢ, hT₀', (BoundaryConcatenationGeometry.horientation' q Cᵢ i hCᵢ orientation
        horientation), (BoundaryConcatenationGeometry.htiles Cᵢ orientation base Rminus Rplus
        left right e f htransport r hr s hs P Q (BoundaryConcatenationGeometry.hcoordSegment' r s
        P Q σ a b c d htotal hcoordSegment) (BoundaryConcatenationGeometry.hcorrespondence base
        left right e f r m s P hP Q hQ (BoundaryConcatenationGeometry.dropLastForall₂)
        (BoundaryConcatenationGeometry.appendForall₂))), hRminus, hRplus⟩⟩

end ApollonianSuperharmonic

end
