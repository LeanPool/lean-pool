/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.BandPrototileNonempty
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathBetween

public import LeanPool.ApollonianSuperharmonic.BandRegularTileTouchingClassification
public import LeanPool.ApollonianSuperharmonic.BoundaryString
public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTripleRetargetMiddle
public import LeanPool.ApollonianSuperharmonic.LatticeEdgeRegularity
public import LeanPool.ApollonianSuperharmonic.TileOdometerAffineTranslation
public import LeanPool.ApollonianSuperharmonic.TileOdometerCentralSymmetry

-- [TABLET NODE: P4366T2OuterGeometry]

/-!
# P4366T2OuterGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace OuterGeometry

private theorem hcurv0 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (C0 : BandCircle), (q (0 : Fin (4 : ℕ)) = C0.1.1) →
            (0 < (q 0).1) ) := by
  classical
  intro q C0 hC0
  rw [hC0]
  exact C0.2

private theorem hcurvi :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (Ci : BandCircle), ∀ (i : Fin 3), (q i.succ =
            Ci.1.1) → (((1 : ℤ) < Ci.1.1.1) → (0 < (q i.succ).1)) ) := by
  classical
  intro q Ci i hCi hlarge
  rw [hCi]
  omega

private theorem hcplus :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (T0 : ProtoTile), ∀ (Rplus :
            ProtoTile), ∀ (qf : Fin (4 : ℕ) → CircleCoordinates), (TileCentroid Rplus -
            TileCentroid T0 = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.1 (qf i.succ) (qf (0 :
            Fin (4 : ℕ))) + BandVectors.1 (qf (0 : Fin (4 : ℕ))) (qf i.succ))) → ((qf 0 = q 0) →
            ((qf i.succ = q i.succ) → (TileCentroid Rplus - TileCentroid T0 = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) + GaussianRealPoint
            (BandVectors.1 (q 0) (q i.succ)))))) ) := by
  classical
  intro q i T0 Rplus qf hcentplus hvec0 hveci
  simpa [hvec0, hveci, GaussianRealPoint] using hcentplus

private theorem hcentT :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (T0 : ProtoTile), TileCentroid
            (TileTranslation T0 (BandVectors.1 (q i.succ) (q 0))) = TileCentroid T0 +
            GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) ) := by
  classical
  intro q i T0
  rw [(TileTranslationFormulas T0 (BandVectors.1 (q i.succ) (q 0))).2.2.2.2.1]
  ext <;> simp [GaussianRealPoint]

private theorem hshift :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (C0 : BandCircle), ∀ (i : Fin 3), ∀ (T0 :
            ProtoTile), ∀ (T0' : ProtoTile), (TileCentroid T0' - TileCentroid T0 =
            GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) → ((BandPrototile
            C0.1.1 T0) → ((BandPrototile C0.1.1 T0') → ((TileCentroid (TileTranslation T0
            (BandVectors.1 (q i.succ) (q 0))) = TileCentroid T0 + GaussianRealPoint
            (BandVectors.1 (q i.succ) (q 0))) → (T0'.cells = (TileTranslation T0 (BandVectors.1
            (q i.succ) (q 0))).cells)))) ) := by
  classical
  intro q C0 i T0 T0' hcentroid hT0 hT0' hcentT
  have htr : BandPrototile C0.1.1
      (TileTranslation T0 (BandVectors.1 (q i.succ) (q 0))) :=
    BandPrototileTranslation C0.1.1 T0 _ hT0
  have hcentroidEq : TileCentroid T0' =
      TileCentroid (TileTranslation T0 (BandVectors.1 (q i.succ) (q 0))) := by
    have hh : TileCentroid T0' =
        TileCentroid T0 + GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) := by
      calc
        TileCentroid T0' =
            (TileCentroid T0' - TileCentroid T0) + TileCentroid T0 := by
              ext <;> simp
        _ = GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) + TileCentroid T0 := by
              rw [hcentroid]
        _ = TileCentroid T0 + GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) := by
              ext <;> simp <;> ring
    simpa [hcentT] using hh
  exact (BandPrototileCentroidUnique C0.1.1 _ _ hT0' htr hcentroidEq).1

private theorem hrealShift :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (T0 : ProtoTile), ∀ (T0' :
            ProtoTile), (T0'.cells = (TileTranslation T0 (BandVectors.1 (q i.succ) (q 0))).cells)
            → (TileRealization T0' = TileRealization (TileTranslation T0 (BandVectors.1 (q
            i.succ) (q 0)))) ) := by
  classical
  intro q i T0 T0' hshift
  simp only [TileRealization]
  rw [hshift]

private theorem hlat0' :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (T0 : ProtoTile), ∀ (T0' :
            ProtoTile), (LatticeTile (TileTranslation T0 (BandVectors.1 (q i.succ) (q (0 : Fin (4
            : ℕ)))))) → ((TileRealization T0' = TileRealization (TileTranslation T0
            (BandVectors.1 (q i.succ) (q 0)))) → (LatticeTile T0')) ) := by
  classical
  intro q i T0 T0' hlatTrans hrealShift
  rw [show LatticeTile T0' = TopologicalDisk (TileRealization T0') from rfl,
    hrealShift]
  exact hlatTrans

private theorem centroid_cells_eq :
    (by
      classical
      exact
        ∀ (A : ProtoTile),
          ∀ (B : ProtoTile),
            B.cells.Nonempty → A.cells = B.cells → TileCentroid A = TileCentroid B
    ) := by
  classical
  intro A B hB hc
  simp [TileCentroid, hB, hc]

private theorem hFminusne :
    (by
      classical
      exact
        ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (centerShift : GaussianInt),
            ((TileTranslation (TileHalfTurn Rminus) centerShift).cells = Rplus.cells) →
            ((Rplus.cells.Nonempty) → ((TileTranslation (TileHalfTurn Rminus)
            centerShift).cells.Nonempty)) ) := by
  classical
  intro Rminus Rplus centerShift hmc hRpne
  rw [hmc]
  exact hRpne

private theorem hFplusne :
    (by
      classical
      exact
        ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (centerShift : GaussianInt),
            ((TileTranslation (TileHalfTurn Rplus) centerShift).cells = Rminus.cells) →
            ((Rminus.cells.Nonempty) → ((TileTranslation (TileHalfTurn Rplus)
            centerShift).cells.Nonempty)) ) := by
  classical
  intro Rminus Rplus centerShift hpc hRmne
  rw [hpc]
  exact hRmne

private theorem huCent :
    (by
      classical
      exact
        ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (centerShift : GaussianInt),
            (TileCentroid (TileTranslation (TileHalfTurn Rminus) centerShift) = TileCentroid
            Rplus) → ((TileCentroid (TileHalfTurn Rminus) = (-(TileCentroid Rminus).1,
            -(TileCentroid Rminus).2)) → (GaussianRealPoint centerShift = TileCentroid Rminus +
            TileCentroid Rplus)) ) := by
  classical
  intro Rminus Rplus centerShift hcentFminus hcentHalfMinus
  have ht := (TileTranslationFormulas (TileHalfTurn Rminus) centerShift).2.2.2.2.1
  rw [hcentHalfMinus] at ht
  rw [hcentFminus] at ht
  apply Prod.ext
  · have hx := congrArg Prod.fst ht
    change (TileCentroid Rplus).1 = -(TileCentroid Rminus).1 +
      (centerShift.re : Real) at hx
    change (centerShift.re : Real) =
      (TileCentroid Rminus).1 + (TileCentroid Rplus).1
    linarith
  · have hy := congrArg Prod.snd ht
    change (TileCentroid Rplus).2 = -(TileCentroid Rminus).2 +
      (centerShift.im : Real) at hy
    change (centerShift.im : Real) =
      (TileCentroid Rminus).2 + (TileCentroid Rplus).2
    linarith

private theorem hsumCent :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (T0 : ProtoTile), ∀ (Rminus :
            ProtoTile), ∀ (Rplus : ProtoTile), ∀ (qf : Fin (4 : ℕ) → CircleCoordinates),
            (TileCentroid Rminus - TileCentroid T0 = (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.1 (qf i.succ) (qf (0 : Fin (4 : ℕ))) - BandVectors.1 (qf (0 : Fin (4 :
            ℕ))) (qf i.succ))) → ((qf 0 = q 0) → ((qf i.succ = q i.succ) → ((TileCentroid Rplus -
            TileCentroid T0 = (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q
            0)) + GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)))) → (TileCentroid Rminus +
            TileCentroid Rplus = (2 : Real) • TileCentroid T0 + GaussianRealPoint (BandVectors.1
            (q i.succ) (q 0)))))) ) := by
  classical
  intro q i T0 Rminus Rplus qf hcentminus hvec0 hveci hcplus
  have hmin : TileCentroid Rminus - TileCentroid T0 =
      (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) -
        GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) := by
    simpa [hvec0, hveci, GaussianRealPoint] using hcentminus
  have hpl : TileCentroid Rplus - TileCentroid T0 =
      (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
        GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) := hcplus
  have hminx := congrArg Prod.fst hmin
  have hminy := congrArg Prod.snd hmin
  have hplx := congrArg Prod.fst hpl
  have hply := congrArg Prod.snd hpl
  simp only [Prod.fst_sub, one_div, GaussianRealPoint, Int.reduceNeg, Fin.isValue,
      GaussianInt.intCast_re, GaussianInt.intCast_im, Prod.mk_sub_mk, Prod.smul_mk,
      smul_eq_mul, Prod.snd_sub, Prod.mk_add_mk] at hminx hminy hplx hply
  apply Prod.ext
  · simp only [Prod.fst_add]
    simp only [GaussianRealPoint]
    rw [GaussianInt.intCast_re (BandVectors.1 (q i.succ) (q 0))]
    calc
      (TileCentroid Rminus).1 + (TileCentroid Rplus).1 =
          ((TileCentroid Rminus).1 - (TileCentroid T0).1) +
            ((TileCentroid Rplus).1 - (TileCentroid T0).1) +
            2 * (TileCentroid T0).1 := by ring
      _ = (1 / 2 : Real) *
            ((GaussianInt.toComplex (BandVectors.1 (q i.succ) (q 0))).re -
              (GaussianInt.toComplex (BandVectors.1 (q 0) (q i.succ))).re) +
            (1 / 2 : Real) *
            ((GaussianInt.toComplex (BandVectors.1 (q i.succ) (q 0))).re +
              (GaussianInt.toComplex (BandVectors.1 (q 0) (q i.succ))).re) +
            2 * (TileCentroid T0).1 := by rw [hminx, hplx]; ring
      _ = 2 * (TileCentroid T0).1 +
            (GaussianInt.toComplex (BandVectors.1 (q i.succ) (q 0))).re := by ring
  · simp only [Prod.snd_add]
    simp only [GaussianRealPoint]
    rw [GaussianInt.intCast_im (BandVectors.1 (q i.succ) (q 0))]
    calc
      (TileCentroid Rminus).2 + (TileCentroid Rplus).2 =
          ((TileCentroid Rminus).2 - (TileCentroid T0).2) +
            ((TileCentroid Rplus).2 - (TileCentroid T0).2) +
            2 * (TileCentroid T0).2 := by ring
      _ = (1 / 2 : Real) *
            ((GaussianInt.toComplex (BandVectors.1 (q i.succ) (q 0))).im -
              (GaussianInt.toComplex (BandVectors.1 (q 0) (q i.succ))).im) +
            (1 / 2 : Real) *
            ((GaussianInt.toComplex (BandVectors.1 (q i.succ) (q 0))).im +
              (GaussianInt.toComplex (BandVectors.1 (q 0) (q i.succ))).im) +
            2 * (TileCentroid T0).2 := by rw [hminy, hply]; ring
      _ = 2 * (TileCentroid T0).2 +
            (GaussianInt.toComplex (BandVectors.1 (q i.succ) (q 0))).im := by ring

private theorem hFrootCent :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (T0 : ProtoTile), ∀ (T0' :
            ProtoTile), (TileCentroid T0' - TileCentroid T0 = GaussianRealPoint (BandVectors.1 (q
            i.succ) (q (0 : Fin (4 : ℕ))))) → (∀ (centerShift : GaussianInt), (GaussianRealPoint
            centerShift = (2 : Real) • TileCentroid T0 + GaussianRealPoint (BandVectors.1 (q
            i.succ) (q 0))) → (TileCentroid (TileTranslation (TileHalfTurn T0) centerShift) =
            TileCentroid T0')) ) := by
  classical
  intro q i T0 T0' hcentroid centerShift huCenter
  rw [(TileTranslationFormulas (TileHalfTurn T0) centerShift).2.2.2.2.1,
    (TileHalfTurnFormulas T0).2.2.2.2.2.2.2.1]
  have hcx := congrArg Prod.fst hcentroid
  have hcy := congrArg Prod.snd hcentroid
  have hux := congrArg Prod.fst huCenter
  have huy := congrArg Prod.snd huCenter
  simp only [Prod.fst_sub, GaussianRealPoint, Int.reduceNeg, Fin.isValue,
      GaussianInt.intCast_re, GaussianInt.intCast_im, Prod.snd_sub, Prod.fst_add,
      Prod.smul_fst, smul_eq_mul, Prod.snd_add, Prod.smul_snd] at hcx hcy hux huy
  apply Prod.ext
  · change -(TileCentroid T0).1 + (centerShift.re : Real) =
      (TileCentroid T0').1
    rw [GaussianInt.intCast_re centerShift] at ⊢
    calc
      -(TileCentroid T0).1 + (GaussianInt.toComplex centerShift).re =
          -(TileCentroid T0).1 +
            (2 * (TileCentroid T0).1 +
              (GaussianInt.toComplex (BandVectors.1 (q i.succ) (q 0))).re) := by rw [hux]
      _ = (TileCentroid T0').1 := by rw [← hcx]; ring
  · change -(TileCentroid T0).2 + (centerShift.im : Real) =
      (TileCentroid T0').2
    rw [GaussianInt.intCast_im centerShift] at ⊢
    calc
      -(TileCentroid T0).2 + (GaussianInt.toComplex centerShift).im =
          -(TileCentroid T0).2 +
            (2 * (TileCentroid T0).2 +
              (GaussianInt.toComplex (BandVectors.1 (q i.succ) (q 0))).im) := by rw [huy]
      _ = (TileCentroid T0').2 := by rw [← hcy]; ring

private theorem hFroot'Cent :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (T0 : ProtoTile), ∀ (T0' :
            ProtoTile), (TileCentroid T0' - TileCentroid T0 = GaussianRealPoint (BandVectors.1 (q
            i.succ) (q (0 : Fin (4 : ℕ))))) → (∀ (centerShift : GaussianInt), (GaussianRealPoint
            centerShift = (2 : Real) • TileCentroid T0 + GaussianRealPoint (BandVectors.1 (q
            i.succ) (q 0))) → (TileCentroid (TileTranslation (TileHalfTurn T0') centerShift) =
            TileCentroid T0)) ) := by
  classical
  intro q i T0 T0' hcentroid centerShift huCenter
  rw [(TileTranslationFormulas (TileHalfTurn T0') centerShift).2.2.2.2.1,
    (TileHalfTurnFormulas T0').2.2.2.2.2.2.2.1]
  have hcx := congrArg Prod.fst hcentroid
  have hcy := congrArg Prod.snd hcentroid
  have hux := congrArg Prod.fst huCenter
  have huy := congrArg Prod.snd huCenter
  simp only [Prod.fst_sub, GaussianRealPoint, Int.reduceNeg, Fin.isValue,
      GaussianInt.intCast_re, GaussianInt.intCast_im, Prod.snd_sub, Prod.fst_add,
      Prod.smul_fst, smul_eq_mul, Prod.snd_add, Prod.smul_snd] at hcx hcy hux huy
  apply Prod.ext
  · change -(TileCentroid T0').1 + (centerShift.re : Real) = (TileCentroid T0).1
    rw [GaussianInt.intCast_re centerShift] at ⊢
    calc
      -(TileCentroid T0').1 + (GaussianInt.toComplex centerShift).re =
          -(TileCentroid T0').1 +
            (2 * (TileCentroid T0).1 +
              (GaussianInt.toComplex (BandVectors.1 (q i.succ) (q 0))).re) := by rw [hux]
      _ = (TileCentroid T0).1 := by linear_combination -hcx
  · change -(TileCentroid T0').2 + (centerShift.im : Real) = (TileCentroid T0).2
    rw [GaussianInt.intCast_im centerShift] at ⊢
    calc
      -(TileCentroid T0').2 + (GaussianInt.toComplex centerShift).im =
          -(TileCentroid T0').2 +
            (2 * (TileCentroid T0).2 +
              (GaussianInt.toComplex (BandVectors.1 (q i.succ) (q 0))).im) := by rw [huy]
      _ = (TileCentroid T0).2 := by linear_combination -hcy

private theorem finj :
    (by
      classical
      exact
        ∀ (centerShift : GaussianInt),
        let f : GaussianInt → GaussianInt := fun x => -x + centerShift
        Function.Injective f ) := by
  classical
  intro centerShift f x y hxy
  apply neg_injective
  exact add_right_cancel hxy

private theorem fstep :
    (by
      classical
      exact
        ∀ (centerShift : GaussianInt),
        let f : GaussianInt → GaussianInt := fun x => -x + centerShift
        ∀ (x : GaussianInt), ∀ (y : GaussianInt), (y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x
            - ⟨0, 1⟩) → (f y = f x + 1 ∨ f y = f x - 1 ∨ f y = f x + ⟨0, 1⟩ ∨ f y = f x - ⟨0, 1⟩)
            ) := by
  classical
  intro centerShift f x y hxy
  rcases hxy with hxy | hxy | hxy | hxy
  · right; left; rw [hxy]; simp [f]; abel
  · left; rw [hxy]; simp [f]; abel
  · right; right; right; rw [hxy]; simp [f]; abel
  · right; right; left; rw [hxy]; simp [f]; abel

private theorem hVertexCov :
    (by
      classical
      exact
        ∀ (centerShift : GaussianInt),
        let f : GaussianInt → GaussianInt := fun x => -x + centerShift
        ∀ (X : ProtoTile), FootprintVertices (TileTranslation (TileHalfTurn X) centerShift) = f
            '' FootprintVertices X ) := by
  classical
  intro centerShift f X
  rw [(TileTranslationFormulas (TileHalfTurn X) centerShift).2.2.2.2.2.1,
    (TileHalfTurnFormulas X).2.2.2.2.2.2.1]
  rw [Set.image_image]
  have hcomp : (fun z : GaussianInt => GaussianTranslation centerShift (-z)) = f := by
    funext z
    apply Zsqrtd.ext <;> simp [f, GaussianTranslation]
  rw [hcomp]

private theorem hHalfEdges :
    (by
      classical
      exact
        ∀ (X : ProtoTile), FootprintEdges (TileHalfTurn X) = (fun e : Finset GaussianInt =>
            e.image (fun z => -z)) '' FootprintEdges X ) := by
  classical
  intro X
  calc
    FootprintEdges (TileHalfTurn X) = FootprintEdges (TileQuarterTurn (TileQuarterTurn X)) := by
      simp only [FootprintEdges]
      rw [(TileHalfTurnFormulas X).2.2.2.2.1]
    _ = (fun e : Finset GaussianInt => e.image (fun z => -z)) '' FootprintEdges X := by
      rw [(TileQuarterTurnFormulas (TileQuarterTurn X)).2.2.2.2.2.2.1,
        (TileQuarterTurnFormulas X).2.2.2.2.2.2.1]
      have hneg : (fun z : GaussianInt => GaussianQuarterTurn (GaussianQuarterTurn z)) =
          (fun z => -z) := by
        funext z
        apply Zsqrtd.ext <;> simp [GaussianQuarterTurn]
      rw [Set.image_image]
      have hfin : (fun e : Finset GaussianInt =>
          (e.image GaussianQuarterTurn).image GaussianQuarterTurn) =
          (fun e => e.image (fun z => -z)) := by
        funext e
        rw [Finset.image_image]
        congr 1
      rw [hfin]

private theorem hEdgeCov :
    (by
      classical
      exact
        ∀ (centerShift : GaussianInt),
        let f : GaussianInt → GaussianInt := fun x => -x + centerShift
        (∀ (X : ProtoTile), FootprintEdges (TileHalfTurn X) = (fun e : Finset GaussianInt =>
            e.image (fun z => -z)) '' FootprintEdges X) → (∀ (X : ProtoTile), FootprintEdges
            (TileTranslation (TileHalfTurn X) centerShift) = (fun e : Finset GaussianInt =>
            e.image f) '' FootprintEdges X) ) := by
  classical
  intro centerShift f hHalfEdges X
  rw [(TileTranslationFormulas (TileHalfTurn X) centerShift).2.2.2.2.2.2.1,
    hHalfEdges]
  rw [Set.image_image]
  have hfin : (fun e : Finset GaussianInt =>
      (e.image (fun z => -z)).image (GaussianTranslation centerShift)) =
      (fun e => e.image f) := by
    funext e
    rw [Finset.image_image]
    congr 1
  rw [hfin]

private theorem pathMap :
    (by
      classical
      exact
        ∀ (centerShift : GaussianInt),
        let f : GaussianInt → GaussianInt := fun x => -x + centerShift
        (Function.Injective f) → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), (y = x + 1 ∨ y = x -
            1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩) → (f y = f x + 1 ∨ f y = f x - 1 ∨ f y = f x +
            ⟨0, 1⟩ ∨ f y = f x - ⟨0, 1⟩)) → (∀ {V : Set GaussianInt}, ∀
            {E : Set (Finset GaussianInt)}, ∀ {V' : Set GaussianInt}, ∀
            {E' : Set (Finset GaussianInt)}, ∀ {x : GaussianInt}, ∀ {y : GaussianInt}, (V' = f ''
            V) → ((E' = (fun e : Finset GaussianInt => e.image f) '' E) → ((SimpleGridPathBetween
            V E x y) → (SimpleGridPathBetween V' E' (f x) (f y)))))) ) := by
  classical
  intro centerShift f finj fstep V E V' E' x y hV hE P
  rcases P with ⟨p, hnodup, hlength, hhead, hlast, hvertices, hsteps, hedges⟩
  let g : GaussianInt → GaussianInt := fun z => -(z - centerShift)
  have fg (z : GaussianInt) : f (g z) = z := by
    simp [f, g]
  have gf (z : GaussianInt) : g (f z) = z := by
    simp [f, g]
  have hlistInjective : Function.Injective (fun r : List GaussianInt => r.map f) :=
    List.map_injective_iff.mpr finj
  have unmap (a b : GaussianInt) (l1 l2 : List GaussianInt)
      (hm : p.map f = l1 ++ a :: b :: l2) :
      p = l1.map g ++ g a :: g b :: l2.map g := by
    apply hlistInjective
    simpa [List.map_append, Function.comp_def, fg] using hm
  refine ⟨p.map f, hnodup.map finj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hlength
  · simp [hhead]
  · simp [hlast]
  · rw [hV, hvertices]
    ext z
    simp []
  · intro a b l1 l2 hm
    have hpre := unmap a b l1 l2 hm
    have hstep0 := hsteps (g a) (g b) (l1.map g) (l2.map g) hpre
    simpa [fg a, fg b] using fstep (g a) (g b) hstep0
  · intro e
    rw [hE]
    simp only [Set.mem_image]
    constructor
    · rintro ⟨e0, he0, rfl⟩
      rcases (hedges e0).mp he0 with ⟨a, b, l1, l2, hp, heq⟩
      refine ⟨f a, f b, l1.map f, l2.map f, ?_, ?_⟩
      · simp [List.map_append, hp]
      · simp [heq]
    · rintro ⟨a, b, l1, l2, hm, heq⟩
      have hpre := unmap a b l1 l2 hm
      have he0 : ({g a, g b} : Finset GaussianInt) ∈ E :=
        (hedges _).2 ⟨g a, g b, l1.map g, l2.map g, hpre, rfl⟩
      refine ⟨{g a, g b}, he0, ?_⟩
      rw [heq]
      ext z
      simp [fg]

private theorem hVrootNe :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (centerShift : GaussianInt),
            (T0'.cells.Nonempty) → (((TileTranslation (TileHalfTurn T0) centerShift).cells =
            T0'.cells) → ((TileTranslation (TileHalfTurn T0) centerShift).cells.Nonempty)) ) := by
  classical
  intro T0 T0' centerShift hT0'ne hFrootCells
  rw [hFrootCells]
  exact hT0'ne

private theorem hVroot'Ne :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (centerShift : GaussianInt),
            (T0.cells.Nonempty) → (((TileTranslation (TileHalfTurn T0') centerShift).cells =
            T0.cells) → ((TileTranslation (TileHalfTurn T0') centerShift).cells.Nonempty)) ) := by
  classical
  intro T0 T0' centerShift hT0ne hFroot'Cells
  rw [hFroot'Cells]
  exact hT0ne

private theorem hVrootEq :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (centerShift : GaussianInt),
            (T0'.cells.Nonempty) → (((TileTranslation (TileHalfTurn T0) centerShift).cells =
            T0'.cells) → (FootprintVertices T0' = FootprintVertices (TileTranslation
            (TileHalfTurn T0) centerShift))) ) := by
  classical
  intro T0 T0' centerShift hT0'ne hFrootCells
  simp [FootprintVertices, hT0'ne, hFrootCells]

private theorem hVroot'Eq :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (centerShift : GaussianInt),
            (T0.cells.Nonempty) → (((TileTranslation (TileHalfTurn T0') centerShift).cells =
            T0.cells) → (FootprintVertices T0 = FootprintVertices (TileTranslation (TileHalfTurn
            T0') centerShift))) ) := by
  classical
  intro T0 T0' centerShift hT0ne hFroot'Cells
  simp [FootprintVertices, hT0ne, hFroot'Cells]

private theorem hVplusEq :
    (by
      classical
      exact
        ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (centerShift : GaussianInt),
            ((TileTranslation (TileHalfTurn Rplus) centerShift).cells = Rminus.cells) →
            ((Rminus.cells.Nonempty) → (FootprintVertices Rminus = FootprintVertices
            (TileTranslation (TileHalfTurn Rplus) centerShift))) ) := by
  classical
  intro Rminus Rplus centerShift hpc hRmne
  simp [FootprintVertices, hRmne, hpc]

private theorem hErootEq :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (centerShift : GaussianInt), ((TileTranslation
            (TileHalfTurn T0) centerShift).cells = T0'.cells) → (FootprintEdges T0' =
            FootprintEdges (TileTranslation (TileHalfTurn T0) centerShift)) ) := by
  classical
  intro T0 T0' centerShift hFrootCells
  simp [FootprintEdges, hFrootCells]

private theorem hEroot'Eq :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (centerShift : GaussianInt), ((TileTranslation
            (TileHalfTurn T0') centerShift).cells = T0.cells) → (FootprintEdges T0 =
            FootprintEdges (TileTranslation (TileHalfTurn T0') centerShift)) ) := by
  classical
  intro T0 T0' centerShift hFroot'Cells
  simp [FootprintEdges, hFroot'Cells]

private theorem hEplusEq :
    (by
      classical
      exact
        ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (centerShift : GaussianInt),
            ((TileTranslation (TileHalfTurn Rplus) centerShift).cells = Rminus.cells) →
            (FootprintEdges Rminus = FootprintEdges (TileTranslation (TileHalfTurn Rplus)
            centerShift)) ) := by
  classical
  intro Rminus Rplus centerShift hpc
  simp [FootprintEdges, hpc]

private theorem heT0 :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (centerShift : GaussianInt),
        let f : GaussianInt → GaussianInt := fun x => -x + centerShift
        (∀ (X : ProtoTile), FootprintEdges (TileTranslation (TileHalfTurn X) centerShift) = (fun
            e : Finset GaussianInt => e.image f) '' FootprintEdges X) → ((FootprintEdges T0' =
            FootprintEdges (TileTranslation (TileHalfTurn T0) centerShift)) → (FootprintEdges T0'
            = (fun e : Finset GaussianInt => e.image f) '' FootprintEdges T0)) ) := by
  classical
  intro T0 T0' centerShift f hEdgeCov hErootEq
  rw [hErootEq, hEdgeCov]

private theorem heT0' :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (centerShift : GaussianInt),
        let f : GaussianInt → GaussianInt := fun x => -x + centerShift
        (∀ (X : ProtoTile), FootprintEdges (TileTranslation (TileHalfTurn X) centerShift) = (fun
            e : Finset GaussianInt => e.image f) '' FootprintEdges X) → ((FootprintEdges T0 =
            FootprintEdges (TileTranslation (TileHalfTurn T0') centerShift)) → (FootprintEdges T0
            = (fun e : Finset GaussianInt => e.image f) '' FootprintEdges T0')) ) := by
  classical
  intro T0 T0' centerShift f hEdgeCov hEroot'Eq
  rw [hEroot'Eq, hEdgeCov]

private theorem hePlus :
    (by
      classical
      exact
        ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (centerShift : GaussianInt),
        let f : GaussianInt → GaussianInt := fun x => -x + centerShift
        (∀ (X : ProtoTile), FootprintEdges (TileTranslation (TileHalfTurn X) centerShift) = (fun
            e : Finset GaussianInt => e.image f) '' FootprintEdges X) → ((FootprintEdges Rminus =
            FootprintEdges (TileTranslation (TileHalfTurn Rplus) centerShift)) → (FootprintEdges
            Rminus = (fun e : Finset GaussianInt => e.image f) '' FootprintEdges Rplus)) ) := by
  classical
  intro Rminus Rplus centerShift f hEdgeCov hEplusEq
  rw [hEplusEq, hEdgeCov]

private theorem vAB :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (centerShift : GaussianInt),
        let f : GaussianInt → GaussianInt := fun x => -x + centerShift
        (Function.Injective f) → ((FootprintVertices T0' = f '' FootprintVertices T0) →
            ((FootprintVertices T0 = f '' FootprintVertices T0') → (FootprintVertices T0 ∩
            FootprintVertices T0' = f '' (FootprintVertices T0 ∩ FootprintVertices T0')))) ) := by
  classical
  intro T0 T0' centerShift f finj hvT0 hvT0'
  calc
    _ = FootprintVertices T0' ∩ FootprintVertices T0 := Set.inter_comm _ _
    _ = (f '' FootprintVertices T0) ∩ (f '' FootprintVertices T0') := by
      exact congrArg₂ (fun A B : Set GaussianInt => A ∩ B) hvT0 hvT0'
    _ = f '' (FootprintVertices T0 ∩ FootprintVertices T0') := (Set.image_inter finj).symm

private theorem eAB :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (centerShift : GaussianInt),
        let f : GaussianInt → GaussianInt := fun x => -x + centerShift
        (Function.Injective f) → ((FootprintEdges T0' = (fun e : Finset GaussianInt => e.image f)
            '' FootprintEdges T0) → ((FootprintEdges T0 = (fun e : Finset GaussianInt => e.image
            f) '' FootprintEdges T0') → (FootprintEdges T0 ∩ FootprintEdges T0' = (fun e : Finset
            GaussianInt => e.image f) '' (FootprintEdges T0 ∩ FootprintEdges T0')))) ) := by
  classical
  intro T0 T0' centerShift f finj heT0 heT0'
  calc
    _ = FootprintEdges T0' ∩ FootprintEdges T0 := Set.inter_comm _ _
    _ = (fun e : Finset GaussianInt => e.image f) '' FootprintEdges T0 ∩
        (fun e : Finset GaussianInt => e.image f) '' FootprintEdges T0' := by
      exact congrArg₂ (fun A B : Set (Finset GaussianInt) => A ∩ B) heT0 heT0'
    _ = (fun e : Finset GaussianInt => e.image f) ''
        (FootprintEdges T0 ∩ FootprintEdges T0') :=
          (Set.image_inter (Finset.image_injective finj)).symm

private theorem vBC :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀
            (centerShift : GaussianInt),
        let f : GaussianInt → GaussianInt := fun x => -x + centerShift
        (Function.Injective f) → ((FootprintVertices T0' = f '' FootprintVertices T0) →
            ((FootprintVertices Rminus = f '' FootprintVertices Rplus) → (FootprintVertices T0' ∩
            FootprintVertices Rminus = f '' (FootprintVertices Rplus ∩ FootprintVertices T0)))) )
            := by
  classical
  intro T0 T0' Rminus Rplus centerShift f finj hvT0 hvPlus
  calc
    _ = FootprintVertices Rminus ∩ FootprintVertices T0' := Set.inter_comm _ _
    _ = (f '' FootprintVertices Rplus) ∩ (f '' FootprintVertices T0) := by
      exact congrArg₂ (fun A B : Set GaussianInt => A ∩ B) hvPlus hvT0
    _ = f '' (FootprintVertices Rplus ∩ FootprintVertices T0) := (Set.image_inter finj).symm

private theorem eBC :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀
            (centerShift : GaussianInt),
        let f : GaussianInt → GaussianInt := fun x => -x + centerShift
        (Function.Injective f) → ((FootprintEdges T0' = (fun e : Finset GaussianInt => e.image f)
            '' FootprintEdges T0) → ((FootprintEdges Rminus = (fun e : Finset GaussianInt =>
            e.image f) '' FootprintEdges Rplus) → (FootprintEdges T0' ∩ FootprintEdges Rminus =
            (fun e : Finset GaussianInt => e.image f) '' (FootprintEdges Rplus ∩ FootprintEdges
            T0)))) ) := by
  classical
  intro T0 T0' Rminus Rplus centerShift f finj heT0 hePlus
  calc
    _ = FootprintEdges Rminus ∩ FootprintEdges T0' := Set.inter_comm _ _
    _ = (fun e : Finset GaussianInt => e.image f) '' FootprintEdges Rplus ∩
        (fun e : Finset GaussianInt => e.image f) '' FootprintEdges T0 := by
      exact congrArg₂ (fun A B : Set (Finset GaussianInt) => A ∩ B) hePlus heT0
    _ = (fun e : Finset GaussianInt => e.image f) ''
        (FootprintEdges Rplus ∩ FootprintEdges T0) :=
          (Set.image_inter (Finset.image_injective finj)).symm

private theorem vCA :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀
            (centerShift : GaussianInt),
        let f : GaussianInt → GaussianInt := fun x => -x + centerShift
        (Function.Injective f) → ((FootprintVertices T0 = f '' FootprintVertices T0') →
            ((FootprintVertices Rminus = f '' FootprintVertices Rplus) → (FootprintVertices
            Rminus ∩ FootprintVertices T0 = f '' (FootprintVertices T0' ∩ FootprintVertices
            Rplus)))) ) := by
  classical
  intro T0 T0' Rminus Rplus centerShift f finj hvT0' hvPlus
  calc
    _ = FootprintVertices T0 ∩ FootprintVertices Rminus := Set.inter_comm _ _
    _ = (f '' FootprintVertices T0') ∩ (f '' FootprintVertices Rplus) := by
      exact congrArg₂ (fun A B : Set GaussianInt => A ∩ B) hvT0' hvPlus
    _ = f '' (FootprintVertices T0' ∩ FootprintVertices Rplus) := (Set.image_inter finj).symm

private theorem eCA :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀
            (centerShift : GaussianInt),
        let f : GaussianInt → GaussianInt := fun x => -x + centerShift
        (Function.Injective f) → ((FootprintEdges T0 = (fun e : Finset GaussianInt => e.image f)
            '' FootprintEdges T0') → ((FootprintEdges Rminus = (fun e : Finset GaussianInt =>
            e.image f) '' FootprintEdges Rplus) → (FootprintEdges Rminus ∩ FootprintEdges T0 =
            (fun e : Finset GaussianInt => e.image f) '' (FootprintEdges T0' ∩ FootprintEdges
            Rplus)))) ) := by
  classical
  intro T0 T0' Rminus Rplus centerShift f finj heT0' hePlus
  calc
    _ = FootprintEdges T0 ∩ FootprintEdges Rminus := Set.inter_comm _ _
    _ = (fun e : Finset GaussianInt => e.image f) '' FootprintEdges T0' ∩
        (fun e : Finset GaussianInt => e.image f) '' FootprintEdges Rplus := by
      exact congrArg₂ (fun A B : Set (Finset GaussianInt) => A ∩ B) heT0' hePlus
    _ = (fun e : Finset GaussianInt => e.image f) ''
        (FootprintEdges T0' ∩ FootprintEdges Rplus) :=
          (Set.image_inter (Finset.image_injective finj)).symm

private theorem hTriple :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀
            (centerShift : GaussianInt),
        let f : GaussianInt → GaussianInt := fun x => -x + centerShift
        (Function.Injective f) → ((FootprintVertices Rminus = f '' FootprintVertices Rplus) →
            ((FootprintVertices T0 ∩ FootprintVertices T0' = f '' (FootprintVertices T0 ∩
            FootprintVertices T0')) → (FootprintVertices T0 ∩ FootprintVertices T0' ∩
            FootprintVertices Rminus = f '' (FootprintVertices T0 ∩ FootprintVertices T0' ∩
            FootprintVertices Rplus)))) ) := by
  classical
  intro T0 T0' Rminus Rplus centerShift f finj hvPlus vAB
  calc
    _ = (f '' (FootprintVertices T0 ∩ FootprintVertices T0')) ∩
        (f '' FootprintVertices Rplus) :=
      congrArg₂ (fun A B : Set GaussianInt => A ∩ B) vAB hvPlus
    _ = f '' (FootprintVertices T0 ∩ FootprintVertices T0' ∩ FootprintVertices Rplus) :=
      (Set.image_inter finj).symm

private theorem hunique :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀
            (centerShift : GaussianInt), ∀ (Eplus : ExactTileInterfaceTriple T0 T0' Rplus),
        let f : GaussianInt → GaussianInt := fun x => -x + centerShift
        (FootprintVertices T0 ∩ FootprintVertices T0' ∩ FootprintVertices Rminus = f ''
            (FootprintVertices T0 ∩ FootprintVertices T0' ∩ FootprintVertices Rplus)) → (∀ x, x ∈
            FootprintVertices T0 ∩ FootprintVertices T0' ∩ FootprintVertices Rminus ↔ x = f
            Eplus.point) ) := by
  classical
  intro T0 T0' Rminus Rplus centerShift Eplus f hTriple x
  rw [hTriple]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hone := (Eplus.unique_common y).mp hy
    simp [hone]
  · intro hx
    subst x
    exact ⟨Eplus.point, (Eplus.unique_common Eplus.point).mpr rfl, rfl⟩

private theorem path_endpoints_ne :
    (by
      classical
      exact
        ∀ {V : Set GaussianInt}, ∀ {E : Set (Finset GaussianInt)}, ∀ {x : GaussianInt}, ∀
            {y : GaussianInt}, (SimpleGridPathBetween V E x y) → (x ≠ y) ) := by
  classical
  intro V E x y P
  rcases P with ⟨p, hnodup, hlen, hhead, hlast, _, _, _⟩
  have hpne : p ≠ [] := by
    intro hp
    subst p
    simp at hlen
  have hhead' : p.head hpne = x := by
    have h := List.head?_eq_some_head hpne
    rw [hhead] at h
    exact Option.some.inj h.symm
  have hlast' : p.getLast hpne = y := by
    have h := List.getLast?_eq_some_getLast hpne
    rw [hlast] at h
    exact Option.some.inj h.symm
  intro hxy
  have heq : p.head hpne = p.getLast hpne := by
    rw [hhead', hlast', hxy]
  obtain ⟨z, rfl⟩ := (List.Nodup.head_eq_getLast_iff hpne hnodup).mp heq
  simp at hlen

private theorem hpairCases :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀
            (centerShift : GaussianInt), ∀ (Eplus : ExactTileInterfaceTriple T0 T0' Rplus),
        let f : GaussianInt → GaussianInt := fun x => -x + centerShift
        ∀ (pAB : SimpleGridPathBetween (FootprintVertices T0 ∩ FootprintVertices T0')
            (FootprintEdges T0 ∩ FootprintEdges T0') (f Eplus.point) (f Eplus.otherAB)), ∀ (pBC :
            SimpleGridPathBetween (FootprintVertices T0' ∩ FootprintVertices Rminus)
            (FootprintEdges T0' ∩ FootprintEdges Rminus) (f Eplus.point) (f Eplus.otherCA)), ∀
            (pCA : SimpleGridPathBetween (FootprintVertices Rminus ∩ FootprintVertices T0)
            (FootprintEdges Rminus ∩ FootprintEdges T0) (f Eplus.point) (f Eplus.otherBC)), ∀
            (hunique : ∀ x, x ∈ FootprintVertices T0 ∩ FootprintVertices T0' ∩ FootprintVertices
            Rminus ↔ x = f Eplus.point),
        let EM : ExactTileInterfaceTriple T0 T0' Rminus :=
          { point := f Eplus.point
            otherAB := f Eplus.otherAB
            otherBC := f Eplus.otherCA
            otherCA := f Eplus.otherBC
            pathAB := pAB
            pathBC := pBC
            pathCA := pCA
            unique_common := hunique }
        (Eplus.point ≠ Eplus.otherAB) → ((({Eplus.point, Eplus.otherAB} : Finset GaussianInt) =
            {EM.point, EM.otherAB}) → (Eplus.point = EM.point ∧ Eplus.otherAB = EM.otherAB ∨
            Eplus.point = EM.otherAB ∧ Eplus.otherAB = EM.point)) ) := by
  classical
  intro T0 T0' Rminus Rplus centerShift Eplus f pAB pBC pCA hunique EM hpt hpair
  have hpMem : Eplus.point ∈ ({EM.point, EM.otherAB} : Finset GaussianInt) := by
    rw [← hpair]
    simp
  have htMem : Eplus.otherAB ∈ ({EM.point, EM.otherAB} : Finset GaussianInt) := by
    rw [← hpair]
    simp
  have hpCases : Eplus.point = EM.point ∨ Eplus.point = EM.otherAB := by
    simpa using hpMem
  have htCases : Eplus.otherAB = EM.point ∨ Eplus.otherAB = EM.otherAB := by
    simpa using htMem
  rcases hpCases with hp | hp <;> rcases htCases with ht | ht
  · exact False.elim (hpt (hp.trans ht.symm))
  · exact Or.inl ⟨hp, ht⟩
  · exact Or.inr ⟨hp, ht⟩
  · exact False.elim (hpt (hp.trans ht.symm))

private theorem houterEnds :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile),
          ∀ (T0' : ProtoTile),
            ∀ (Rminus : ProtoTile),
              ∀ (Rplus : ProtoTile),
                ∀ (centerShift : GaussianInt),
                  ∀ (Eplus : ExactTileInterfaceTriple T0 T0' Rplus),
                    let f : GaussianInt → GaussianInt := fun x => -x + centerShift
                    ∀
                      (pAB :
                        SimpleGridPathBetween
                          (FootprintVertices T0 ∩ FootprintVertices T0')
                          (FootprintEdges T0 ∩ FootprintEdges T0') (f Eplus.point)
                          (f Eplus.otherAB)),
                      ∀
                        (pBC :
                          SimpleGridPathBetween
                            (FootprintVertices T0' ∩ FootprintVertices Rminus)
                            (FootprintEdges T0' ∩ FootprintEdges Rminus) (f Eplus.point)
                            (f Eplus.otherCA)),
                        ∀
                          (pCA :
                            SimpleGridPathBetween
                              (FootprintVertices Rminus ∩ FootprintVertices T0)
                              (FootprintEdges Rminus ∩ FootprintEdges T0) (f Eplus.point)
                              (f Eplus.otherBC)),
                          ∀
                            (hunique :
                              ∀ x,
                                x ∈
                                FootprintVertices T0 ∩ FootprintVertices T0' ∩
                                FootprintVertices Rminus ↔
                                x = f Eplus.point),
                            let EM : ExactTileInterfaceTriple T0 T0' Rminus :=
                              { point := f Eplus.point
                                otherAB := f Eplus.otherAB
                                otherBC := f Eplus.otherCA
                                otherCA := f Eplus.otherBC
                                pathAB := pAB
                                pathBC := pBC
                                pathCA := pCA
                                unique_common := hunique }
                            Eplus.point ≠ Eplus.otherAB →
                              Eplus.point = EM.point ∧ Eplus.otherAB = EM.otherAB ∨
                                Eplus.point = EM.otherAB ∧ Eplus.otherAB = EM.point →
                                f Eplus.point = Eplus.otherAB ∧
                                f Eplus.otherAB = Eplus.point
    ) := by
  classical
  intro T0 T0' Rminus Rplus centerShift Eplus f pAB pBC pCA hunique EM hpt hpairCases
  rcases hpairCases with hfix | hswap
  · rcases hfix with ⟨hfp, hft⟩
    have hu1 : centerShift = Eplus.point + Eplus.point := by
      have hfixed : f Eplus.point = Eplus.point := by simpa [EM] using hfp.symm
      dsimp [f] at hfixed
      linear_combination hfixed
    have hu2 : centerShift = Eplus.otherAB + Eplus.otherAB := by
      have hfixed : f Eplus.otherAB = Eplus.otherAB := by simpa [EM] using hft.symm
      dsimp [f] at hfixed
      linear_combination hfixed
    have hdouble : Eplus.point + Eplus.point =
        Eplus.otherAB + Eplus.otherAB := hu1.symm.trans hu2
    have heq : Eplus.point = Eplus.otherAB := by
      apply Zsqrtd.ext
      · have h := congrArg (fun z : GaussianInt => z.re) hdouble
        simp at h
        omega
      · have h := congrArg (fun z : GaussianInt => z.im) hdouble
        simp at h
        omega
    exact (hpt heq).elim
  · exact ⟨hswap.2.symm, hswap.1.symm⟩

private abbrev reversePath := @SimpleGridPathBetween.reverse

private theorem hOuterPath :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀
            (centerShift : GaussianInt), ∀ (Eplus : ExactTileInterfaceTriple T0 T0' Rplus),
        let f : GaussianInt → GaussianInt := fun x => -x + centerShift
        ∀ (pAB : SimpleGridPathBetween (FootprintVertices T0 ∩ FootprintVertices T0')
            (FootprintEdges T0 ∩ FootprintEdges T0') (f Eplus.point) (f Eplus.otherAB)), ∀ (pBC :
            SimpleGridPathBetween (FootprintVertices T0' ∩ FootprintVertices Rminus)
            (FootprintEdges T0' ∩ FootprintEdges Rminus) (f Eplus.point) (f Eplus.otherCA)), ∀
            (pCA : SimpleGridPathBetween (FootprintVertices Rminus ∩ FootprintVertices T0)
            (FootprintEdges Rminus ∩ FootprintEdges T0) (f Eplus.point) (f Eplus.otherBC)), ∀
            (hunique : ∀ x, x ∈ FootprintVertices T0 ∩ FootprintVertices T0' ∩ FootprintVertices
            Rminus ↔ x = f Eplus.point),
        let EM : ExactTileInterfaceTriple T0 T0' Rminus :=
          { point := f Eplus.point
            otherAB := f Eplus.otherAB
            otherBC := f Eplus.otherCA
            otherCA := f Eplus.otherBC
            pathAB := pAB
            pathBC := pBC
            pathCA := pCA
            unique_common := hunique }
        (f Eplus.point = Eplus.otherAB ∧ f Eplus.otherAB = Eplus.point) → ((∀
            {V : Set GaussianInt}, ∀ {E : Set (Finset GaussianInt)}, ∀ {x : GaussianInt}, ∀
            {y : GaussianInt}, (SimpleGridPathBetween V E x y) → (SimpleGridPathBetween V E y x))
            → (SimpleGridPathBetween (FootprintVertices T0 ∩ FootprintVertices T0')
            (FootprintEdges T0 ∩ FootprintEdges T0') EM.point Eplus.point)) ) := by
  classical
  intro T0 T0' Rminus Rplus centerShift Eplus f pAB pBC pCA hunique EM houterEnds reversePath
  have hrev := reversePath Eplus.pathAB
  change SimpleGridPathBetween _ _ (f Eplus.point) Eplus.point
  simpa [EM, houterEnds.1] using hrev

private theorem hlatMinus :
    (by
      classical
      exact
        ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (centerShift : GaussianInt),
            ((TileTranslation (TileHalfTurn Rplus) centerShift).cells = Rminus.cells) →
            ((LatticeTile Rplus) → (LatticeTile Rminus)) ) := by
  classical
  intro Rminus Rplus centerShift hpc hlatPlus
  have hq1 : LatticeTile (TileQuarterTurn Rplus) :=
    (TileDiskAreaCovariance Rplus 0).2.1.mp hlatPlus
  have hq2 : LatticeTile (TileQuarterTurn (TileQuarterTurn Rplus)) :=
    (TileDiskAreaCovariance (TileQuarterTurn Rplus) 0).2.1.mp hq1
  have hhalf : LatticeTile (TileHalfTurn Rplus) := by
    change TopologicalDisk (TileRealization (TileHalfTurn Rplus))
    rw [show TileRealization (TileHalfTurn Rplus) =
      TileRealization (TileQuarterTurn (TileQuarterTurn Rplus)) by
        simp [TileRealization, (TileHalfTurnFormulas Rplus).2.2.2.2.1]]
    exact hq2
  have htrans : LatticeTile (TileTranslation (TileHalfTurn Rplus) centerShift) :=
    (TileDiskAreaCovariance (TileHalfTurn Rplus) centerShift).1.mp hhalf
  have hreal : TileRealization Rminus =
      TileRealization (TileTranslation (TileHalfTurn Rplus) centerShift) := by
    simp only [TileRealization]
    rw [hpc]
  rw [show LatticeTile Rminus = TopologicalDisk (TileRealization Rminus) from rfl,
    hreal]
  exact htrans

private theorem hcellMap :
    (by
      classical
      exact
        ∀ (centerShift : GaussianInt),
        let g : GaussianInt → GaussianInt :=
          fun x => GaussianTranslation centerShift (-x - 1 - ⟨0, 1⟩)
        ∀ (A : ProtoTile), (TileTranslation (TileHalfTurn A) centerShift).cells = A.cells.image g
            ) := by
  classical
  intro centerShift g A
  rw [(TileTranslationFormulas (TileHalfTurn A) centerShift).1,
    (TileHalfTurnFormulas A).1, Finset.image_image]
  rfl

private theorem hdisjoint_image :
    (by
      classical
      exact
        ∀ (centerShift : GaussianInt),
        let g : GaussianInt → GaussianInt :=
          fun x => GaussianTranslation centerShift (-x - 1 - ⟨0, 1⟩)
        ∀ {A : Finset GaussianInt}, ∀ {B : Finset GaussianInt}, (Disjoint A B) → (Disjoint
            (A.image g) (B.image g)) ) := by
  classical
  intro centerShift g A B hd
  have ginj : Function.Injective g := by
    intro a b hab
    have hn : -a - 1 - ⟨0, 1⟩ = -b - 1 - ⟨0, 1⟩ := by
      dsimp [g, GaussianTranslation] at hab
      exact add_right_cancel hab
    have hn' : -a = -b := by linear_combination hn
    exact neg_injective hn'
  apply Finset.disjoint_left.mpr
  intro z hza hzb
  rcases Finset.mem_image.mp hza with ⟨a, ha, rfl⟩
  rcases Finset.mem_image.mp hzb with ⟨b, hb, hab⟩
  exact (Finset.disjoint_left.mp hd) ha (ginj hab ▸ hb)

private theorem hdisjoint0Minus :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀
            (centerShift : GaussianInt), ((TileTranslation (TileHalfTurn Rplus)
            centerShift).cells = Rminus.cells) → ((Disjoint T0'.cells Rplus.cells) →
            (((TileTranslation (TileHalfTurn T0') centerShift).cells = T0.cells) → (
        let g : GaussianInt → GaussianInt :=
          fun x => GaussianTranslation centerShift (-x - 1 - ⟨0, 1⟩)
        (∀ (A : ProtoTile), (TileTranslation (TileHalfTurn A) centerShift).cells = A.cells.image
            g) → ((∀ {A : Finset GaussianInt}, ∀ {B : Finset GaussianInt}, (Disjoint A B) →
            (Disjoint (A.image g) (B.image g))) → (Disjoint T0.cells Rminus.cells))))) ) := by
  classical
  intro T0 T0' Rminus Rplus centerShift hpc hdisjoint0'Plus hFroot'Cells g hcellMap hdisjoint_image
  rw [← hFroot'Cells, ← hpc, hcellMap, hcellMap]
  exact hdisjoint_image hdisjoint0'Plus

private theorem hdisjoint0'Minus :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀
            (centerShift : GaussianInt), ((TileTranslation (TileHalfTurn Rplus)
            centerShift).cells = Rminus.cells) → ((Disjoint T0.cells Rplus.cells) →
            (((TileTranslation (TileHalfTurn T0) centerShift).cells = T0'.cells) → (
        let g : GaussianInt → GaussianInt :=
          fun x => GaussianTranslation centerShift (-x - 1 - ⟨0, 1⟩)
        (∀ (A : ProtoTile), (TileTranslation (TileHalfTurn A) centerShift).cells = A.cells.image
            g) → ((∀ {A : Finset GaussianInt}, ∀ {B : Finset GaussianInt}, (Disjoint A B) →
            (Disjoint (A.image g) (B.image g))) → (Disjoint T0'.cells Rminus.cells))))) ) := by
  classical
  intro T0 T0' Rminus Rplus centerShift hpc hdisjoint0Plus hFrootCells g hcellMap hdisjoint_image
  rw [← hFrootCells, ← hpc, hcellMap, hcellMap]
  exact hdisjoint_image hdisjoint0Plus

private theorem hRminusFamily :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus :
            ProtoTile), ∀ (Rplus : ProtoTile), ∀ (tiles : List ProtoTile), (TileString Ci
            orientation base Rminus Rplus tiles) → (Rminus ∈ RegularTileFamily base
            (TilingLattice Ci)) ) := by
  classical
  intro Ci orientation base Rminus Rplus tiles hstring
  rcases hstring with ⟨_, hhead, _, _, hfam, _, _⟩
  have hmem : Rminus ∈ tiles := by
    have heq := List.eq_cons_of_mem_head? (show Rminus ∈ tiles.head? by
      simp [hhead])
    rw [heq]
    simp
  exact hfam Rminus hmem

private theorem hRplusFamily :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus :
            ProtoTile), ∀ (Rplus : ProtoTile), ∀ (tiles : List ProtoTile), (TileString Ci
            orientation base Rminus Rplus tiles) → (Rplus ∈ RegularTileFamily base (TilingLattice
            Ci)) ) := by
  classical
  intro Ci orientation base Rminus Rplus tiles hstring
  rcases hstring with ⟨_, _, hlast, _, hfam, _, _⟩
  have hmem : Rplus ∈ tiles := by
    have hne : tiles ≠ [] := by
      intro he
      simp [he] at hlast
    have hlast' := List.getLast?_eq_some_getLast hne
    rw [hlast] at hlast'
    have hmemLast := List.getLast_mem hne
    exact (Option.some.inj hlast') ▸ hmemLast
  exact hfam Rplus hmem

private theorem hcentDiff :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (T0 : ProtoTile), ∀ (Rminus :
            ProtoTile), ∀ (Rplus : ProtoTile), ∀ (qf : Fin (4 : ℕ) → CircleCoordinates),
            (TileCentroid Rminus - TileCentroid T0 = (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.1 (qf i.succ) (qf (0 : Fin (4 : ℕ))) - BandVectors.1 (qf (0 : Fin (4 :
            ℕ))) (qf i.succ))) → ((qf 0 = q 0) → ((qf i.succ = q i.succ) → ((TileCentroid Rplus -
            TileCentroid T0 = (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q
            0)) + GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)))) → (TileCentroid Rplus -
            TileCentroid Rminus = GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)))))) ) := by
  classical
  intro q i T0 Rminus Rplus qf hcentminus hvec0 hveci hcplus
  have hmin : TileCentroid Rminus - TileCentroid T0 =
      (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) -
        GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) := by
    simpa [hvec0, hveci, GaussianRealPoint] using hcentminus
  have hpl : TileCentroid Rplus - TileCentroid T0 =
      (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
        GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) := hcplus
  calc
    TileCentroid Rplus - TileCentroid Rminus =
        (TileCentroid Rplus - TileCentroid T0) -
          (TileCentroid Rminus - TileCentroid T0) := by ext <;> simp
    _ = (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
          GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) -
        (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) -
          GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) := by rw [hpl, hmin]
    _ = GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)) := by
      apply Prod.ext
      · have hm := congrArg Prod.fst hmin
        have hp := congrArg Prod.fst hpl
        simp [GaussianRealPoint] at hm hp ⊢
        ring
      · have hm := congrArg Prod.snd hmin
        have hp := congrArg Prod.snd hpl
        simp [GaussianRealPoint] at hm hp ⊢
        ring

private theorem hNoTouch :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (Ci : BandCircle), ∀ (i : Fin 3), (q i.succ =
            Ci.1.1) → (((1 : ℤ) < Ci.1.1.1) → (∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
            (Rplus : ProtoTile), (ProperBandQuadruple q) → ((0 < (q 0).1) → ((0 < (q i.succ).1) →
            ((BandPrototile Ci.1.1 base) → ((Rminus ∈ RegularTileFamily base (TilingLattice Ci))
            → ((Rplus ∈ RegularTileFamily base (TilingLattice Ci)) → ((TileCentroid Rplus -
            TileCentroid Rminus = GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) → (¬
            TileTouching Rminus Rplus))))))))) ) := by
  classical
  intro q Ci i hCi hlarge base Rminus Rplus hproper hcurv0 hcurvi hBandBase hRminusFamily
      hRplusFamily hcentDiff htouch
  rcases BandGenealogy Ci with hunit | ⟨qb, hsemi, hqb0, hless, _⟩
  · have : Ci.1.1.1 = 1 := hunit
    omega
  have hproperB : ProperBandQuadruple qb := ⟨hsemi, by
    intro j
    rw [hqb0]
    exact hless j⟩
  have hBandBase' : BandPrototile (qb 0) base := by simpa [hqb0] using hBandBase
  have hclassified := (BandRegularTileTouchingClassification Ci qb hproperB
    hqb0 base hBandBase' Rminus Rplus hRminusFamily hRplusFamily).mp htouch
  have hLengthContradiction (j : Fin 3)
      (hcontact : TileCentroid Rplus - TileCentroid Rminus =
          GaussianRealPoint (BandVectors.1 (qb j.succ) (qb 0)) ∨
        TileCentroid Rplus - TileCentroid Rminus =
          -GaussianRealPoint (BandVectors.1 (qb j.succ) (qb 0))) : False := by
    have hinj : Function.Injective GaussianRealPoint := by
      intro x y hxy
      apply Zsqrtd.ext
      · have hx := congrArg Prod.fst hxy
        dsimp [GaussianRealPoint] at hx
        exact_mod_cast hx
      · have hy := congrArg Prod.snd hxy
        dsimp [GaussianRealPoint] at hy
        exact_mod_cast hy
    have hvecEq : Zsqrtd.norm (BandVectors.1 (q 0) (q i.succ)) =
        Zsqrtd.norm (BandVectors.1 (qb j.succ) (qb 0)) := by
      rcases hcontact with hcontact | hcontact
      · have hreal : GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)) =
            GaussianRealPoint (BandVectors.1 (qb j.succ) (qb 0)) := by
          rw [← hcentDiff, hcontact]
        have hv := hinj hreal
        exact congrArg Zsqrtd.norm hv
      · have hreal : GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)) =
            GaussianRealPoint (-BandVectors.1 (qb j.succ) (qb 0)) := by
          rw [← hcentDiff, hcontact]
          ext <;> simp [GaussianRealPoint]
        have hv := hinj hreal
        rw [hv, Zsqrtd.norm_neg]
    have hrootNorm := TangencyCoordinateIdentity q hproper.1 0 i.succ
      (Fin.succ_ne_zero _).symm
    have hchildNorm := TangencyCoordinateIdentity qb hsemi j.succ 0
      (Fin.succ_ne_zero _)
    have hrootSq := (VectorSquareProduct q hproper.1 0 i.succ
      (Fin.succ_ne_zero _).symm).1
    have hchildSq := (VectorSquareProduct qb hsemi j.succ 0
      (Fin.succ_ne_zero _)).1
    have hrootLen : Zsqrtd.norm (BandVectors.1 (q 0) (q i.succ)) ^ 2 =
        ((q i.succ).1 + (q 0).1) ^ 2 := by
      calc
        _ = Zsqrtd.norm (BandVectors.1 (q 0) (q i.succ)) *
            Zsqrtd.norm (BandVectors.1 (q 0) (q i.succ)) := by rw [pow_two]
        _ = Zsqrtd.norm (BandVectors.1 (q 0) (q i.succ) *
            BandVectors.1 (q 0) (q i.succ)) := (Zsqrtd.norm_mul _ _).symm
        _ = Zsqrtd.norm (BandVectors.1 (q 0) (q i.succ) ^ 2) := by rw [pow_two]
        _ = Zsqrtd.norm ((q i.succ).1 • (q 0).2 -
            (q 0).1 • (q i.succ).2) := by rw [hrootSq]
        _ = _ := by simpa [add_comm] using hrootNorm
    have hchildLen : Zsqrtd.norm (BandVectors.1 (qb j.succ) (qb 0)) ^ 2 =
        ((qb j.succ).1 + (qb 0).1) ^ 2 := by
      calc
        _ = Zsqrtd.norm (BandVectors.1 (qb j.succ) (qb 0)) *
            Zsqrtd.norm (BandVectors.1 (qb j.succ) (qb 0)) := by rw [pow_two]
        _ = Zsqrtd.norm (BandVectors.1 (qb j.succ) (qb 0) *
            BandVectors.1 (qb j.succ) (qb 0)) := (Zsqrtd.norm_mul _ _).symm
        _ = Zsqrtd.norm (BandVectors.1 (qb j.succ) (qb 0) ^ 2) := by rw [pow_two]
        _ = Zsqrtd.norm ((qb 0).1 • (qb j.succ).2 -
            (qb j.succ).1 • (qb 0).2) := by rw [hchildSq]
        _ = _ := hchildNorm
    have hcurvEq : ((q i.succ).1 + (q 0).1) ^ 2 =
        ((qb j.succ).1 + (qb 0).1) ^ 2 := by
      calc
        _ = Zsqrtd.norm (BandVectors.1 (q 0) (q i.succ)) ^ 2 := hrootLen.symm
        _ = Zsqrtd.norm (BandVectors.1 (qb j.succ) (qb 0)) ^ 2 := by rw [hvecEq]
        _ = _ := hchildLen
    have hchildLess : (qb j.succ).1 < (q i.succ).1 := by
      simpa [hCi] using hless j
    have hrootLarger : (qb j.succ).1 + (qb 0).1 <
        (q i.succ).1 + (q 0).1 := by
      have hqless := hproper.2 i
      have hparentEq : (qb 0).1 = (q i.succ).1 := by rw [hqb0, hCi]
      omega
    have hrootPositive : 0 < (q i.succ).1 + (q 0).1 := by omega
    have hchildPositive : 0 < (qb j.succ).1 + (qb 0).1 := by
      have hnonneg := (ProperBandCurvatureStructure qb hproperB).2.1 j
      have hparentPos : 0 < (qb 0).1 := by simpa [hqb0, hCi] using hcurvi
      omega
    nlinarith
  rcases hclassified with ⟨j, hcontact⟩
  exact hLengthContradiction j hcontact

private theorem hvecZero :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (Rminus : ProtoTile), ∀ (Rplus :
            ProtoTile), (TileCentroid Rplus - TileCentroid Rminus = GaussianRealPoint
            (BandVectors.1 (q 0) (q i.succ))) → ((TileCentroid Rminus = TileCentroid Rplus) →
            (GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)) = 0)) ) := by
  classical
  intro q i Rminus Rplus hcentDiff hcentEq
  rw [← hcentDiff]
  rw [hcentEq]
  ext <;> simp

private theorem hinjAt979 :
    (by
      classical
      exact
        Function.Injective GaussianRealPoint ) := by
  classical
  intro x y hxy
  apply Zsqrtd.ext
  · have hx := congrArg Prod.fst hxy
    dsimp [GaussianRealPoint] at hx
    exact_mod_cast hx
  · have hy := congrArg Prod.snd hxy
    dsimp [GaussianRealPoint] at hy
    exact_mod_cast hy

private theorem hvZero :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), (GaussianRealPoint (BandVectors.1 (q
            0) (q i.succ)) = 0) → ((Function.Injective GaussianRealPoint) → (BandVectors.1 (q 0)
            (q i.succ) = 0)) ) := by
  classical
  intro q i hvecZero hinj
  exact hinj (by
    have hz : GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)) =
        GaussianRealPoint 0 := by simpa [GaussianRealPoint] using hvecZero
    exact hz)

end OuterGeometry

theorem P4366T2OuterGeometry
    (q : Fin 4 -> CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C0 Ci : BandCircle) (i : Fin 3)
    (hC0 : q 0 = C0.1.1) (hCi : q i.succ = Ci.1.1)
    (T0 T0' : ProtoTile) (h0 h0' : PartialOdometer)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C0 T0)
    (hsym : QuarterTurnSymmetric T0)
    (hO0 : TileOdometer C0.1.1 T0 h0)
    (hO0' : TileOdometer C0.1.1 T0' h0')
    (hlarge : 1 < Ci.1.1.1)
    (hcentroid : TileCentroid T0' - TileCentroid T0 =
      GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)))
    (orientation : Bool) (base Rminus Rplus : ProtoTile)
    (tiles : List ProtoTile) (centerShift : GaussianInt)
    (hf : BoundaryString C0 Ci i orientation T0 base Rminus Rplus tiles)
    (hminus hplus : PartialOdometer)
    (hOm : TileOdometer Ci.1.1 Rminus hminus)
    (hOp : TileOdometer Ci.1.1 Rplus hplus)
    (hmc : (TileTranslation (TileHalfTurn Rminus) centerShift).cells = Rplus.cells)
    (hpc : (TileTranslation (TileHalfTurn Rplus) centerShift).cells = Rminus.cells) :
    ∃ EM : ExactTileInterfaceTriple T0 T0' Rminus,
    ∃ EP : ExactTileInterfaceTriple T0 T0' Rplus,
      SimpleGridPathBetween (FootprintVertices T0 ∩ FootprintVertices T0')
        (FootprintEdges T0 ∩ FootprintEdges T0') EM.point EP.point ∧
      LatticeTile T0 ∧ LatticeTile T0' ∧
      LatticeTile Rminus ∧ LatticeTile Rplus ∧
      Disjoint T0.cells T0'.cells ∧
      Disjoint T0.cells Rminus.cells ∧ Disjoint T0'.cells Rminus.cells ∧
      Disjoint T0.cells Rplus.cells ∧ Disjoint T0'.cells Rplus.cells ∧
      (∀ x, x ∈ FootprintVertices T0 → ∀ y, y ∈ FootprintVertices T0 →
        FourNeighborAdjacent x y → {x, y} ∈ FootprintEdges T0) ∧
      (∀ x, x ∈ FootprintVertices T0' → ∀ y, y ∈ FootprintVertices T0' →
        FourNeighborAdjacent x y → {x, y} ∈ FootprintEdges T0') ∧
      Rminus ≠ Rplus ∧ ¬ TileTouching Rminus Rplus := by
-- BODY
  classical
  obtain ⟨qf, hqf, hqf0, hqfi, hT0f, hunitf, hstring,
    hcentminus, hcentplus⟩ := hf
  have hproper : ProperBandQuadruple q := cfg.proper
  have hcurv0 : 0 < (q 0).1 := OuterGeometry.hcurv0 q C0 hC0
  have hcurvi : 0 < (q i.succ).1 := OuterGeometry.hcurvi q Ci i hCi hlarge
  have positive_nonempty : ∀ (D : CircleCoordinates) (U : ProtoTile),
      BandPrototile D U → 0 < D.1 → U.cells.Nonempty :=
        fun D V hV hD => BandPrototileNonempty.positive D V hD hV
  have hT0 : BandPrototile C0.1.1 T0 := TileOdometerBandPrototile _ _ _ hO0
  have hT0' : BandPrototile C0.1.1 T0' := TileOdometerBandPrototile _ _ _ hO0'
  have hRm : BandPrototile Ci.1.1 Rminus := TileOdometerBandPrototile _ _ _ hOm
  have hRp : BandPrototile Ci.1.1 Rplus := TileOdometerBandPrototile _ _ _ hOp
  have hT0ne : T0.cells.Nonempty := positive_nonempty _ _ hT0 (by rw [← hC0]; exact hcurv0)
  have hT0'ne : T0'.cells.Nonempty := positive_nonempty _ _ hT0' (by rw [← hC0]; exact hcurv0)
  have hRmne : Rminus.cells.Nonempty := positive_nonempty _ _ hRm (by rw [← hCi]; exact hcurvi)
  have hRpne : Rplus.cells.Nonempty := positive_nonempty _ _ hRp (by rw [← hCi]; exact hcurvi)
  have hvec0 : qf 0 = q 0 := by rw [hqf0, hC0]
  have hveci : qf i.succ = q i.succ := by rw [hqfi, hCi]
  have hcplus := OuterGeometry.hcplus q i T0 Rplus qf hcentplus hvec0 hveci
  have hcentT := OuterGeometry.hcentT q i T0
  have hpluscent : TileCentroid Rplus - TileCentroid T0 =
      (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
        GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) := hcplus
  have hChild := BandOrderedGeneralChildInterfaces q cfg C0 T0 cert hsym
  have hRpq : BandPrototile (q i.succ) Rplus := hCi ▸ hRp
  have plusExists := hChild.2.1 i Rplus hRpq hpluscent
  rcases plusExists with ⟨Eplus0⟩
  have hshift : T0'.cells =
      (TileTranslation T0 (BandVectors.1 (q i.succ) (q 0))).cells := OuterGeometry.hshift q C0 i
          T0 T0' hcentroid hT0 hT0' hcentT
  have hretarget := ExactTileInterfaceTripleRetargetMiddle T0
    (TileTranslation T0 (BandVectors.1 (q i.succ) (q 0))) T0' Rplus hshift.symm
    (by
      intro he
      have hempty : T0.cells = ∅ :=
        (TileTranslationFormulas T0 (BandVectors.1 (q i.succ) (q 0))).2.2.1.mp he
      exact False.elim (hT0ne.ne_empty hempty)) Eplus0
  rcases hretarget with ⟨Eplus, hpoint, _, _, _⟩
  obtain ⟨AB, BC, CA, ABC, hlat0, hlatTrans, hlatPlus,
    hlatAB, hlatBC, hlatCA, hlatABC, hd0Trans, hdTransPlus,
    hdPlus0, hUnionAB, hUnionBC, hUnionCA, hUnionABC,
    hEdgeAB, hEdgeBC, hEdgeCA⟩ :=
    (BandOrderedGeneralMixedAggregatePatches q cfg C0 T0 cert hsym).1
      i Rplus hRpq hcplus
  have hlat0' := OuterGeometry.hlat0' q i T0 T0' hlatTrans (OuterGeometry.hrealShift q i T0 T0'
      hshift)
  have hdisjoint0' : Disjoint T0.cells T0'.cells := by
    simpa [hshift] using hd0Trans
  have hdisjoint0Plus : Disjoint T0.cells Rplus.cells := hdPlus0.symm
  have hdisjoint0'Plus : Disjoint T0'.cells Rplus.cells := by
    simpa [hshift] using hdTransPlus
  have hregular0 := LatticeEdgeRegularity C0 T0 hT0 hlat0
  have hregular0' := LatticeEdgeRegularity C0 T0' hT0' hlat0'
  have hregular0_induced := hregular0.2.1
  have hregular0'_induced := hregular0'.2.1
  have centroid_cells_eq := OuterGeometry.centroid_cells_eq
  have hFplusne := OuterGeometry.hFplusne Rminus Rplus centerShift hpc hRmne
  have hcentFminus : TileCentroid (TileTranslation (TileHalfTurn Rminus) centerShift) =
      TileCentroid Rplus := centroid_cells_eq _ _ hRpne hmc
  have hcentFplus : TileCentroid (TileTranslation (TileHalfTurn Rplus) centerShift) =
      TileCentroid Rminus := centroid_cells_eq _ _ hRmne hpc
  have hcentHalfMinus : TileCentroid (TileHalfTurn Rminus) =
      (-(TileCentroid Rminus).1, -(TileCentroid Rminus).2) :=
    (TileHalfTurnFormulas Rminus).2.2.2.2.2.2.2.1
  have hcentHalfPlus : TileCentroid (TileHalfTurn Rplus) =
      (-(TileCentroid Rplus).1, -(TileCentroid Rplus).2) :=
    (TileHalfTurnFormulas Rplus).2.2.2.2.2.2.2.1
  have huCenter : GaussianRealPoint centerShift =
      (2 : Real) • TileCentroid T0 + GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) :=
    (OuterGeometry.huCent Rminus Rplus centerShift hcentFminus hcentHalfMinus).trans
        (OuterGeometry.hsumCent q i T0 Rminus Rplus qf hcentminus hvec0 hveci hcplus)
  have hOhalf := (TileOdometerCentralSymmetry C0.1.1 T0 h0 hO0).1
  have hOF := TileOdometerAffineTranslation C0.1.1 (TileHalfTurn T0)
    (PartialOdometerHalfTurn h0) centerShift 0 0 hOhalf
  have hFroot : BandPrototile C0.1.1 (TileTranslation (TileHalfTurn T0) centerShift) :=
    TileOdometerBandPrototile _ _ _ hOF
  have hFrootCells :
      (TileTranslation (TileHalfTurn T0) centerShift).cells = T0'.cells :=
    (BandPrototileCentroidUnique C0.1.1 _ _ hFroot hT0' (OuterGeometry.hFrootCent q i T0 T0'
        hcentroid centerShift huCenter)).1
  have hOhalf' := (TileOdometerCentralSymmetry C0.1.1 T0' h0' hO0').1
  have hOF' := TileOdometerAffineTranslation C0.1.1 (TileHalfTurn T0')
    (PartialOdometerHalfTurn h0') centerShift 0 0 hOhalf'
  have hFroot' : BandPrototile C0.1.1
      (TileTranslation (TileHalfTurn T0') centerShift) :=
    TileOdometerBandPrototile _ _ _ hOF'
  have hFroot'Cells :
      (TileTranslation (TileHalfTurn T0') centerShift).cells = T0.cells :=
    (BandPrototileCentroidUnique C0.1.1 _ _ hFroot' hT0 (OuterGeometry.hFroot'Cent q i T0 T0'
        hcentroid centerShift huCenter)).1
  let f : GaussianInt → GaussianInt := fun x => -x + centerShift
  have finj := OuterGeometry.finj centerShift
  have hVertexCov (X : ProtoTile) :
      FootprintVertices (TileTranslation (TileHalfTurn X) centerShift) =
        f '' FootprintVertices X := OuterGeometry.hVertexCov centerShift X
  have hEdgeCov := OuterGeometry.hEdgeCov centerShift (OuterGeometry.hHalfEdges)
  have pathMap {V : Set GaussianInt} {E : Set (Finset GaussianInt)}
      {V' : Set GaussianInt} {E' : Set (Finset GaussianInt)}
      {x y : GaussianInt} (hV : V' = f '' V)
      (hE : E' = (fun e : Finset GaussianInt => e.image f) '' E)
      (P : SimpleGridPathBetween V E x y) := OuterGeometry.pathMap centerShift finj
          (OuterGeometry.fstep centerShift) (V := V) (E := E) (V' := V') (E' := E') (x := x) (y
          := y) hV hE P
  have hVrootNe := OuterGeometry.hVrootNe T0 T0' centerShift hT0'ne hFrootCells
  have hVroot'Ne := OuterGeometry.hVroot'Ne T0 T0' centerShift hT0ne hFroot'Cells
  have hVplusNe : (TileTranslation (TileHalfTurn Rplus) centerShift).cells.Nonempty := hFplusne
  have hVrootEq : FootprintVertices T0' =
      FootprintVertices (TileTranslation (TileHalfTurn T0) centerShift) := OuterGeometry.hVrootEq
          T0 T0' centerShift hT0'ne hFrootCells
  have hVroot'Eq : FootprintVertices T0 =
      FootprintVertices (TileTranslation (TileHalfTurn T0') centerShift) :=
          OuterGeometry.hVroot'Eq T0 T0' centerShift hT0ne hFroot'Cells
  have hVplusEq : FootprintVertices Rminus =
      FootprintVertices (TileTranslation (TileHalfTurn Rplus) centerShift) :=
          OuterGeometry.hVplusEq Rminus Rplus centerShift hpc hRmne
  have hvT0 : FootprintVertices T0' = f '' FootprintVertices T0 := by
    rw [hVrootEq, hVertexCov]
  have hvT0' : FootprintVertices T0 = f '' FootprintVertices T0' := by
    rw [hVroot'Eq, hVertexCov]
  have hvPlus : FootprintVertices Rminus = f '' FootprintVertices Rplus := by
    rw [hVplusEq, hVertexCov]
  have heT0 := OuterGeometry.heT0 T0 T0' centerShift hEdgeCov (OuterGeometry.hErootEq T0 T0'
      centerShift hFrootCells)
  have heT0' := OuterGeometry.heT0' T0 T0' centerShift hEdgeCov (OuterGeometry.hEroot'Eq T0 T0'
      centerShift hFroot'Cells)
  have hePlus := OuterGeometry.hePlus Rminus Rplus centerShift hEdgeCov (OuterGeometry.hEplusEq
      Rminus Rplus centerShift hpc)
  have vAB := OuterGeometry.vAB T0 T0' centerShift finj hvT0 hvT0'
  have pAB := pathMap vAB (OuterGeometry.eAB T0 T0' centerShift finj heT0 heT0') Eplus.pathAB
  have pBC := pathMap (OuterGeometry.vBC T0 T0' Rminus Rplus centerShift finj hvT0 hvPlus)
      (OuterGeometry.eBC T0 T0' Rminus Rplus centerShift finj heT0 hePlus) Eplus.pathCA
  have pCA := pathMap (OuterGeometry.vCA T0 T0' Rminus Rplus centerShift finj hvT0' hvPlus)
      (OuterGeometry.eCA T0 T0' Rminus Rplus centerShift finj heT0' hePlus) Eplus.pathBC
  have hunique := OuterGeometry.hunique T0 T0' Rminus Rplus centerShift Eplus
      (OuterGeometry.hTriple T0 T0' Rminus Rplus centerShift finj hvPlus vAB)
  let EM : ExactTileInterfaceTriple T0 T0' Rminus :=
    { point := f Eplus.point
      otherAB := f Eplus.otherAB
      otherBC := f Eplus.otherCA
      otherCA := f Eplus.otherBC
      pathAB := pAB
      pathBC := pBC
      pathCA := pCA
      unique_common := hunique }
  have hpt : Eplus.point ≠ Eplus.otherAB := (OuterGeometry.path_endpoints_ne) Eplus.pathAB
  have hpair : ({Eplus.point, Eplus.otherAB} : Finset GaussianInt) =
      {EM.point, EM.otherAB} :=
    SimpleGridPathEndpointPairUnique Eplus.pathAB EM.pathAB
  have hOuterPath := OuterGeometry.hOuterPath T0 T0' Rminus Rplus centerShift Eplus pAB pBC pCA
      hunique (OuterGeometry.houterEnds T0 T0' Rminus Rplus centerShift Eplus pAB pBC pCA
      hunique hpt (OuterGeometry.hpairCases T0 T0' Rminus Rplus centerShift Eplus pAB pBC pCA
      hunique hpt hpair)) (OuterGeometry.reversePath)
  have hlatMinus := OuterGeometry.hlatMinus Rminus Rplus centerShift hpc hlatPlus
  let g : GaussianInt → GaussianInt :=
    fun x => GaussianTranslation centerShift (-x - 1 - ⟨0, 1⟩)
  have hcellMap := OuterGeometry.hcellMap centerShift
  have hdisjoint_image {A B : Finset GaussianInt}
      (hd : Disjoint A B) := OuterGeometry.hdisjoint_image centerShift (A := A) (B := B) hd
  have hdisjoint0Minus := OuterGeometry.hdisjoint0Minus T0 T0' Rminus Rplus centerShift hpc
      hdisjoint0'Plus hFroot'Cells hcellMap hdisjoint_image
  have hdisjoint0'Minus := OuterGeometry.hdisjoint0'Minus T0 T0' Rminus Rplus centerShift hpc
      hdisjoint0Plus hFrootCells hcellMap hdisjoint_image
  have hproperBase : ProperBandQuadruple qf := hqf
  have hBandBase : BandPrototile Ci.1.1 base := (by
    rcases hstring with ⟨hbase, _, _, _, _, _, _⟩
    exact hbase)
  have hcentDiff := OuterGeometry.hcentDiff q i T0 Rminus Rplus qf hcentminus hvec0 hveci hcplus
  refine ⟨EM, Eplus, hOuterPath, hlat0, hlat0', hlatMinus, hlatPlus,
    hdisjoint0', hdisjoint0Minus, hdisjoint0'Minus, hdisjoint0Plus,
    hdisjoint0'Plus, hregular0_induced, hregular0'_induced, ?_, (OuterGeometry.hNoTouch q Ci i
        hCi hlarge base Rminus Rplus hproper hcurv0 hcurvi hBandBase (OuterGeometry.hRminusFamily
        Ci orientation base Rminus Rplus tiles hstring) (OuterGeometry.hRplusFamily Ci
        orientation base Rminus Rplus tiles hstring) hcentDiff)⟩
  intro heq
  have hcentEq : TileCentroid Rminus = TileCentroid Rplus := by rw [heq]
  have hvNonzero := VectorNonvanishing q hproper.1 0 i.succ
    (Fin.succ_ne_zero _).symm (Or.inl hcurv0)
  exact hvNonzero (OuterGeometry.hvZero q i (OuterGeometry.hvecZero q i Rminus Rplus hcentDiff
      hcentEq) (OuterGeometry.hinjAt979))

end ApollonianSuperharmonic

end
