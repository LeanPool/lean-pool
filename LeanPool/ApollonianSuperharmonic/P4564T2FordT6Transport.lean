/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FordBaseT6
public import LeanPool.ApollonianSuperharmonic.FordRegimeConverse
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryScopedPhaseUnique
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTilingTransport
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslationNormalForm
public import LeanPool.ApollonianSuperharmonic.BandSubtileOccurrenceTranslation

-- [TABLET NODE: P4564T2FordT6Transport]

/-!
# P4564T2FordT6Transport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FordT6Geometry

private theorem hlineq :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (∀ (a : Fin 3), ∀ (g :
            BandPackingSymmetry), ∀ (F : FordFareyParameter), (BandPackingSymmetryQuadrupleAction
            g ![q (0 : Fin (4 : ℕ)), q a.succ, q (a + (1 : Fin (3 : ℕ))).succ, q (a + (2 : Fin (3
            : ℕ))).succ] = FordRecursiveQuadruple F) → (((q (2 : Fin (4 : ℕ))).1 ≤ (q (1 : Fin (4
            : ℕ))).1) → (((1 : ℤ) < (q (2 : Fin (4 : ℕ))).1) → (((0 : ℤ) < (q (0 : Fin (4 :
            ℕ))).1 ∧ (∀ (i : Fin (3 : ℕ)), (0 : ℤ) ≤ (q i.succ).1) ∧ ∀ (i : Fin (3 : ℕ)), ∀ (j :
            Fin (3 : ℕ)), (q i.succ).1 = (0 : ℤ) → (q j.succ).1 = (0 : ℤ) → i = j) → (∃ i : Fin
            4, (q i).1 = 0))))) ) := by
  classical
  intro q hq a g F hnormal h12 hlarge qcur
  have hzero : ((FordRecursiveQuadruple F) 3).1 = 0 := by
    simp [FordRecursiveQuadruple]
  have hval := congrArg (fun t : Fin 4 → CircleCoordinates => (t 3).1) hnormal
  have hcurv := (BandPackingSymmetryCovariance g).1
  have hact : (BandPackingSymmetryQuadrupleAction g
      ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ] 3).1 = 0 := by
    rw [hval]
    exact hzero
  have hparent : ∃ j : Fin 3, (q j.succ).1 = 0 := by
    cases hor : BandPackingSymmetryReversesOrientation g <;>
      fin_cases a <;>
      simp only [BandPackingSymmetryQuadrupleAction, Fin.isValue, Fin.mk_one,
          Fin.succ_one_eq_two, Fin.reduceAdd, Fin.reduceSucc, Fin.succ_zero_eq_one,
          Matrix.cons_val_zero, hor, Bool.false_eq_true, ↓reduceIte, Matrix.cons_val_one,
          Matrix.cons_val, neg_zero, Matrix.cons_val_succ, Fin.reduceFinMk, Fin.zero_eta,
          zero_add] at hact
    all_goals
      first
      | exact ⟨0, (hcurv (q 1)).symm.trans hact⟩
      | exact ⟨1, (hcurv (q 2)).symm.trans hact⟩
      | exact ⟨2, (hcurv (q 3)).symm.trans hact⟩
  rcases hparent with ⟨j, hj⟩
  have hq1 : 0 < (q 1).1 := by
    have := hq.2 0
    simp at this
    omega
  fin_cases j
  · simp at hj
    omega
  · simp at hj
    omega
  · exact ⟨3, by simpa using hj⟩

private theorem hb :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
          (q (2 : Fin (4 : ℕ))).1 ≤ (q (1 : Fin (4 : ℕ))).1 →
            (1 : ℤ) < (q (2 : Fin (4 : ℕ))).1 →
              ((0 : ℤ) < (q (0 : Fin (4 : ℕ))).1 ∧
                  (∀ (i : Fin (3 : ℕ)), (0 : ℤ) ≤ (q i.succ).1) ∧
                    ∀ (i : Fin (3 : ℕ)),
                      ∀ (j : Fin (3 : ℕ)),
                        (q i.succ).1 = (0 : ℤ) → (q j.succ).1 = (0 : ℤ) → i = j) →
                (∃ i : Fin 4, (q i).1 = 0) →
                  ∀ (b : Fin (3 : ℕ)),
                    (q (b + (2 : Fin (3 : ℕ))).succ).1 = (0 : ℤ) → b = 0
    ) := by
  classical
  intro q h12 hlarge qcur hlineq b hzero
  fin_cases b
  · rfl
  · have := qcur.2.1 0
    have hz : (q 1).1 = 0 := by simpa using hzero
    omega
  · have := qcur.2.1 1
    have hz : (q 2).1 = 0 := by simpa using hzero
    omega

private theorem hnormq :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (h : BandPackingSymmetry), ∀ (F' :
            FordFareyParameter), (BandPackingSymmetryQuadrupleAction h ![q (0 : Fin (4 : ℕ)), q
            (Fin.succ (0 : Fin (3 : ℕ))), q ((0 : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ, q ((0 :
            Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ] = FordRecursiveQuadruple F') →
            (BandPackingSymmetryQuadrupleAction h q = FordRecursiveQuadruple F') ) := by
  classical
  intro q h F' hnorm
  rw [show q = ![q 0, q 1, q 2, q 3] by
    funext i
    fin_cases i <;> rfl]
  exact hnorm

private theorem hqhat :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (h : BandPackingSymmetry), ∀ (F' :
            FordFareyParameter), (BandPackingSymmetryQuadrupleAction h q = FordRecursiveQuadruple
            F') → (∀ (gN : BandPackingSymmetry), (∀ (p : Fin (4 : ℕ) → CircleCoordinates),
            BandPackingSymmetryQuadrupleAction gN p = BandPackingSymmetryQuadrupleAction h p) →
            (BandPackingSymmetryQuadrupleAction gN q = FordRecursiveQuadruple F')) ) := by
  classical
  intro q h F' hnormq gN hquadAdapt
  rw [hquadAdapt]
  exact hnormq

private theorem hr0hat :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (r : Fin (4 : ℕ) → CircleCoordinates), (r (0 : Fin
            (4 : ℕ)) = q (1 : Fin (4 : ℕ))) → (∀ (h : BandPackingSymmetry), ∀ (F' :
            FordFareyParameter), ∀ (gN : BandPackingSymmetry),
            (BandPackingSymmetryReversesOrientation gN = BandPackingSymmetryReversesOrientation
            h) → ((BandPackingSymmetryQuadrupleAction gN q = FordRecursiveQuadruple F') →
            ((BandPackingSymmetryQuadrupleAction gN r) 0 = (FordRecursiveQuadruple F') 1))) ) := by
  classical
  intro q r hr0 h F' gN horientationAdapt hqhat
  have hh := congrFun hqhat 1
  change BandPackingSymmetryCircleAction gN (r 0) = _
  rw [hr0]
  simpa [BandPackingSymmetryQuadrupleAction, horientationAdapt] using hh

private theorem hr2hat :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (r : Fin (4 : ℕ) → CircleCoordinates), (r (2 : Fin
            (4 : ℕ)) = q (2 : Fin (4 : ℕ))) → (∀ (h : BandPackingSymmetry), ∀ (F' :
            FordFareyParameter), (BandPackingSymmetryReversesOrientation h = false) → (∀ (gN :
            BandPackingSymmetry), (BandPackingSymmetryReversesOrientation gN =
            BandPackingSymmetryReversesOrientation h) → ((BandPackingSymmetryQuadrupleAction gN q
            = FordRecursiveQuadruple F') → ((BandPackingSymmetryQuadrupleAction gN r) 2 =
            (FordRecursiveQuadruple F') 2)))) ) := by
  classical
  intro q r hr2 h F' hrev gN horientationAdapt hqhat
  have hh : BandPackingSymmetryCircleAction gN (q 2) =
      (FordRecursiveQuadruple F') 2 := by
    simpa [BandPackingSymmetryQuadrupleAction, horientationAdapt, hrev] using
      congrFun hqhat 2
  simpa [BandPackingSymmetryQuadrupleAction, horientationAdapt, hrev, hr2] using
    hh

private theorem hr3hat :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (r : Fin (4 : ℕ) → CircleCoordinates), (r (3 : Fin
            (4 : ℕ)) = q (3 : Fin (4 : ℕ))) → (∀ (h : BandPackingSymmetry), ∀ (F' :
            FordFareyParameter), (BandPackingSymmetryReversesOrientation h = false) → (∀ (gN :
            BandPackingSymmetry), (BandPackingSymmetryReversesOrientation gN =
            BandPackingSymmetryReversesOrientation h) → ((BandPackingSymmetryQuadrupleAction gN q
            = FordRecursiveQuadruple F') → ((BandPackingSymmetryQuadrupleAction gN r) 3 =
            (FordRecursiveQuadruple F') 3)))) ) := by
  classical
  intro q r hr3 h F' hrev gN horientationAdapt hqhat
  have hh : BandPackingSymmetryCircleAction gN (q 3) =
      (FordRecursiveQuadruple F') 3 := by
    simpa [BandPackingSymmetryQuadrupleAction, horientationAdapt, hrev] using
      congrFun hqhat 3
  simpa [BandPackingSymmetryQuadrupleAction, horientationAdapt, hrev, hr3] using
    hh

private theorem horder :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (r : Fin (4 : ℕ) → CircleCoordinates), (r (0 : Fin
            (4 : ℕ)) = q (1 : Fin (4 : ℕ))) → ((r (2 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ))) → (((q
            (2 : Fin (4 : ℕ))).1 ≤ (q (1 : Fin (4 : ℕ))).1) → (∀ (h : BandPackingSymmetry), ∀ (F'
            : FordFareyParameter), (BandPackingSymmetryReversesOrientation h = false) → (∀ (gN :
            BandPackingSymmetry), (BandPackingSymmetryReversesOrientation gN =
            BandPackingSymmetryReversesOrientation h) → (((BandPackingSymmetryQuadrupleAction gN
            r) 0 = (FordRecursiveQuadruple F') 1) → (((BandPackingSymmetryQuadrupleAction gN r) 2
            = (FordRecursiveQuadruple F') 2) → (((FordRecursiveQuadruple F') 2).1 ≤
            ((FordRecursiveQuadruple F') 1).1))))))) ) := by
  classical
  intro q r hr0 hr2 h12 h F' hrev gN horientationAdapt hr0hat hr2hat
  have hc : ∀ C, (BandPackingSymmetryCircleAction gN C).1 = C.1 :=
    (BandPackingSymmetryCovariance gN).1
  rw [← hr2hat, ← hr0hat]
  simp only [BandPackingSymmetryQuadrupleAction, Fin.isValue, hr0, horientationAdapt, hrev,
      Bool.false_eq_true, ↓reduceIte, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, hr2,
      Fin.reduceSucc, Matrix.cons_val, hc, Matrix.cons_val_zero, ge_iff_le]
  exact h12

private theorem hlarge' :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (r : Fin (4 : ℕ) → CircleCoordinates), (r (2 : Fin
            (4 : ℕ)) = q (2 : Fin (4 : ℕ))) → (((1 : ℤ) < (q (2 : Fin (4 : ℕ))).1) → (∀ (h :
            BandPackingSymmetry), ∀ (F' : FordFareyParameter),
            (BandPackingSymmetryReversesOrientation h = false) → (∀ (gN : BandPackingSymmetry),
            (BandPackingSymmetryReversesOrientation gN = BandPackingSymmetryReversesOrientation
            h) → (((BandPackingSymmetryQuadrupleAction gN r) 2 = (FordRecursiveQuadruple F') 2) →
            (1 < ((FordRecursiveQuadruple F') 2).1))))) ) := by
  classical
  intro q r hr2 hlarge h F' hrev gN horientationAdapt hr2hat
  have hc : ∀ C, (BandPackingSymmetryCircleAction gN C).1 = C.1 :=
    (BandPackingSymmetryCovariance gN).1
  rw [← hr2hat]
  simp only [BandPackingSymmetryQuadrupleAction, Fin.isValue, horientationAdapt, hrev,
      Bool.false_eq_true, ↓reduceIte, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, hr2,
      Fin.reduceSucc, Matrix.cons_val, hc, gt_iff_lt]
  exact hlarge

private theorem hT' :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), (BandPrototile (q (0 : Fin (4 :
            ℕ))) T) → (∀ (gN : BandPackingSymmetry), BandPrototile
            ((BandPackingSymmetryQuadrupleAction gN q) 0) (BandPackingSymmetryTileAction gN T)) )
            := by
  classical
  intro q T hT gN
  exact ((BandPackingSymmetryCovariance gN).2.1 (q 0) T).mp hT

private theorem hep :
    (by
      classical
      exact
        ∀ (h : BandPackingSymmetry), (BandPackingSymmetryReversesOrientation h = false) → (∀ (gN
            : BandPackingSymmetry), (BandPackingSymmetryReversesOrientation gN =
            BandPackingSymmetryReversesOrientation h) → (∀ (dp : Bool), ∀ (ep : Fin (3 : ℕ) ×
            Bool ≃ Fin (3 : ℕ) × Bool), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), (ep : Fin (3 : ℕ) ×
            Bool → Fin (3 : ℕ) × Bool) (i, s) = ((fun (i : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation gN = true then -i else i) i, s ^^ dp)) → ((dp
            = false) → (∀ (i : Fin 3), ∀ (s : Bool), ep (i, s) = (i, s))))) ) := by
  classical
  intro h hrev gN horientationAdapt dp ep hpe hdp i s
  rw [hpe]
  simp [horientationAdapt, hrev, hdp]

private theorem hPp :
    (by
      classical
      exact
        ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (gN : BandPackingSymmetry), ∀ (ep : Fin (3 : ℕ)
            × Bool ≃ Fin (3 : ℕ) × Bool), ∀ (Pp : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3
            : ℕ)), ∀ (s : Bool), Pp ((ep : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s)).1
            ((ep : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s)).2 =
            BandPackingSymmetryTileAction gN (P i s)) → ((∀ (i : Fin 3), ∀ (s : Bool), ep (i, s)
            = (i, s)) → (∀ i, ∀ s, Pp i s = BandPackingSymmetryTileAction gN (P i s))) ) := by
  classical
  intro P gN ep Pp hpmem hep i s
  simpa [hep i s] using hpmem i s

private abbrev heq := ApollonianSuperharmonic.FordT6Geometry.hep

private abbrev hes := ApollonianSuperharmonic.FordT6Geometry.hep

private abbrev hQp := ApollonianSuperharmonic.FordT6Geometry.hPp

private abbrev hSp := ApollonianSuperharmonic.FordT6Geometry.hPp

private theorem hFord :
    (by
      classical
      exact
        ∀ (F' : FordFareyParameter), BandPrototile ((FordRecursiveQuadruple F') 0) (FordTile
            F'.q) ) := by
  classical
  intro F'
  simpa [FordRecursiveQuadruple] using
    (FordTileRecursiveIdentification F').1

private theorem cancelTranslation :
    (by
      classical
      exact
        ∀ (w : GaussianInt), ∀ (U : ProtoTile), TileTranslation (TileTranslation U w) (-w) = U )
            := by
  classical
  intro w U
  cases U with
  | mk cells anchor =>
    simp [TileTranslation, GaussianTranslation, Finset.image_image,
      Function.comp_def, add_assoc, add_comm]

private theorem hrootCells :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (F' : FordFareyParameter), ∀ (gN : BandPackingSymmetry),
        let Tn := BandPackingSymmetryTileAction gN T
        ∀ (w : GaussianInt), (Tn.cells = (TileTranslation (FordTile F'.q) w).cells) → (
        let Tbar : ProtoTile := TileTranslation Tn (-w)
        (∀ (U : ProtoTile), TileTranslation (TileTranslation U w) (-w) = U) → (Tbar.cells =
            (FordTile F'.q).cells)) ) := by
  classical
  intro T F' gN Tn w hcellsNormal Tbar cancelTranslation
  rw [(TileTranslationFormulas Tn (-w)).1, hcellsNormal,
    (TileTranslationFormulas (FordTile F'.q) w).1]
  have hc := congrArg ProtoTile.cells (cancelTranslation (FordTile F'.q))
  simpa [TileTranslation, Finset.image_image, Function.comp_def] using hc

private theorem hrootAnchor :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (F' : FordFareyParameter), ∀ (gN : BandPackingSymmetry),
        let Tn := BandPackingSymmetryTileAction gN T
        ∀ (w : GaussianInt), (Tn.cells = ∅ → Tn.anchor = (TileTranslation (FordTile F'.q)
            w).anchor) → (
        let Tbar : ProtoTile := TileTranslation Tn (-w)
        Tbar.cells = ∅ → Tbar.anchor = (FordTile F'.q).anchor) ) := by
  classical
  intro T F' gN Tn w hemptyNormal Tbar hempty
  have hempty' : Tn.cells = ∅ :=
    (TileTranslationFormulas Tn (-w)).2.2.1.mp (by simpa [Tbar] using hempty)
  have ha := hemptyNormal hempty'
  change GaussianTranslation (-w) Tn.anchor = (FordTile F'.q).anchor
  rw [ha]
  simp [TileTranslation, GaussianTranslation, add_assoc, add_comm]

private theorem hPbar :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (F' : FordFareyParameter), ∀ (gN
            : BandPackingSymmetry), (BandPackingSymmetryQuadrupleAction gN q =
            FordRecursiveQuadruple F') → (∀ (Pp : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3
            : ℕ)), ∀ (s : Bool), BandSubtileOccurrence (BandPackingSymmetryQuadrupleAction gN q)
            (BandPackingSymmetryTileAction gN T) i s (Pp i s)) → (
        let Tn := BandPackingSymmetryTileAction gN T
        let Pn : Fin 3 → Bool → ProtoTile := Pp
        ∀ (w : GaussianInt),
        let Pbar : Fin 3 → Bool → ProtoTile := fun i s => TileTranslation (Pn i s) (-w)
        let Tbar : ProtoTile := TileTranslation Tn (-w)
        ∀ i, ∀ s, BandSubtileOccurrence (FordRecursiveQuadruple F') Tbar i s (Pbar i s))) ) := by
  classical
  intro q T F' gN hqhat Pp hpp Tn Pn w Pbar Tbar i s
  have ho := (BandSubtileOccurrenceTranslation
    (FordRecursiveQuadruple F') Tn (Pn i s) i s (-w)
    ).mp (by simpa [Tn, Pn, hqhat] using hpp i s)
  rcases ho with ⟨hb, hf, hc⟩
  refine ⟨hb, ?_, ?_⟩
  · simpa [Pbar, Tbar] using hf
  · simpa [Pbar, Tbar, TileTranslationFormulas] using hc

private theorem hPford :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (F' : FordFareyParameter), ∀ (gN : BandPackingSymmetry), ∀ (Pp : Fin
            (3 : ℕ) → Bool → ProtoTile),
        let Tn := BandPackingSymmetryTileAction gN T
        let Pn : Fin 3 → Bool → ProtoTile := Pp
        ∀ (w : GaussianInt),
        let Pbar : Fin 3 → Bool → ProtoTile := fun i s => TileTranslation (Pn i s) (-w)
        let Tbar : ProtoTile := TileTranslation Tn (-w)
        (FootprintVertices Tbar = FootprintVertices (FordTile F'.q) ∧ BoundaryFootprintVertices
            Tbar = BoundaryFootprintVertices (FordTile F'.q) ∧ BoundaryFootprintEdges Tbar =
            BoundaryFootprintEdges (FordTile F'.q) ∧ TileRealization Tbar = TileRealization
            (FordTile F'.q) ∧ TileCentroid Tbar = TileCentroid (FordTile F'.q)) → ((∀ i, ∀ s,
            BandSubtileOccurrence (FordRecursiveQuadruple F') Tbar i s (Pbar i s)) → (∀ i, ∀ s,
            BandSubtileOccurrence (FordRecursiveQuadruple F') (FordTile F'.q) i s (Pbar i s))) )
            := by
  classical
  intro T F' gN Pp Tn Pn w Pbar Tbar hobs hPbar i s
  rcases hPbar i s with ⟨hb, hf, hc⟩
  refine ⟨hb, ?_, ?_⟩
  · simpa [hobs.1] using hf
  · simpa [hobs.2.2.2.2] using hc

private theorem hQbar :
    (by
      classical
      exact
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (gN :
            BandPackingSymmetry), ∀ (Pp : Fin (3 : ℕ) → Bool → ProtoTile), (∀ i, ∀ s, Pp i s =
            BandPackingSymmetryTileAction gN (P i s)) → (∀ (Qp : Fin (3 : ℕ) → Bool → ProtoTile),
            (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence
            (BandPackingSymmetryQuadrupleAction gN r) (BandPackingSymmetryTileAction gN (P (0 :
            Fin (3 : ℕ)) true)) i s (Qp i s)) → (
        let rN := BandPackingSymmetryQuadrupleAction gN r
        let Pn : Fin 3 → Bool → ProtoTile := Pp
        let Qn : Fin 3 → Bool → ProtoTile := Qp
        ∀ (w : GaussianInt),
        let Pbar : Fin 3 → Bool → ProtoTile := fun i s => TileTranslation (Pn i s) (-w)
        let Qbar : Fin 3 → Bool → ProtoTile := fun i s => TileTranslation (Qn i s) (-w)
        ∀ i, ∀ s, BandSubtileOccurrence rN (Pbar 0 true) i s (Qbar i s))) ) := by
  classical
  intro r P gN Pp hPp Qp hqocc rN Pn Qn w Pbar Qbar i s
  have ho := (BandSubtileOccurrenceTranslation rN (Pn 0 true) (Qn i s) i s (-w)).mp
    (by simpa [rN, Pn, Qn, hPp 0 true] using hqocc i s)
  simpa [Pbar, Qbar] using ho

private theorem hSbar :
    (by
      classical
      exact
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (gN :
            BandPackingSymmetry), ∀ (Pp : Fin (3 : ℕ) → Bool → ProtoTile), (∀ i, ∀ s, Pp i s =
            BandPackingSymmetryTileAction gN (P i s)) → (∀ (Sp : Fin (3 : ℕ) → Bool → ProtoTile),
            (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence
            (BandPackingSymmetryQuadrupleAction gN r) (BandPackingSymmetryTileAction gN (P (0 :
            Fin (3 : ℕ)) false)) i s (Sp i s)) → (
        let rN := BandPackingSymmetryQuadrupleAction gN r
        let Pn : Fin 3 → Bool → ProtoTile := Pp
        let Sn : Fin 3 → Bool → ProtoTile := Sp
        ∀ (w : GaussianInt),
        let Pbar : Fin 3 → Bool → ProtoTile := fun i s => TileTranslation (Pn i s) (-w)
        let Sbar : Fin 3 → Bool → ProtoTile := fun i s => TileTranslation (Sn i s) (-w)
        ∀ i, ∀ s, BandSubtileOccurrence rN (Pbar 0 false) i s (Sbar i s))) ) := by
  classical
  intro r P gN Pp hPp Sp hsocc rN Pn Sn w Pbar Sbar i s
  have ho := (BandSubtileOccurrenceTranslation rN (Pn 0 false) (Sn i s) i s (-w)).mp
    (by simpa [rN, Pn, Sn, hPp 0 false] using hsocc i s)
  simpa [Pbar, Sbar] using ho

private theorem hq0 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (h : BandPackingSymmetry), ∀ (F' :
            FordFareyParameter), (BandPackingSymmetryReversesOrientation h = false) → (∀ (gN :
            BandPackingSymmetry), (BandPackingSymmetryReversesOrientation gN =
            BandPackingSymmetryReversesOrientation h) → ((BandPackingSymmetryQuadrupleAction gN q
            = FordRecursiveQuadruple F') → (BandPackingSymmetryCircleAction gN (q 0) =
            (FordRecursiveQuadruple F') 0))) ) := by
  classical
  intro q h F' hrev gN horientationAdapt hqhat
  simpa [BandPackingSymmetryQuadrupleAction, horientationAdapt, hrev] using
    congrFun hqhat 0

private theorem hq1At383 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (h : BandPackingSymmetry), ∀ (F' :
            FordFareyParameter), (BandPackingSymmetryReversesOrientation h = false) → (∀ (gN :
            BandPackingSymmetry), (BandPackingSymmetryReversesOrientation gN =
            BandPackingSymmetryReversesOrientation h) → ((BandPackingSymmetryQuadrupleAction gN q
            = FordRecursiveQuadruple F') → (BandPackingSymmetryCircleAction gN (q 1) =
            (FordRecursiveQuadruple F') 1))) ) := by
  classical
  intro q h F' hrev gN horientationAdapt hqhat
  simpa [BandPackingSymmetryQuadrupleAction, horientationAdapt, hrev] using
    congrFun hqhat 1

private theorem hq2At387 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (h : BandPackingSymmetry), ∀ (F' :
            FordFareyParameter), (BandPackingSymmetryReversesOrientation h = false) → (∀ (gN :
            BandPackingSymmetry), (BandPackingSymmetryReversesOrientation gN =
            BandPackingSymmetryReversesOrientation h) → ((BandPackingSymmetryQuadrupleAction gN q
            = FordRecursiveQuadruple F') → (BandPackingSymmetryCircleAction gN (q 2) =
            (FordRecursiveQuadruple F') 2))) ) := by
  classical
  intro q h F' hrev gN horientationAdapt hqhat
  simpa [BandPackingSymmetryQuadrupleAction, horientationAdapt, hrev] using
    congrFun hqhat 2

private theorem huN :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
        let hclaim : GaussianInt := BandVectors.1 (q 0) (q 1)
         ∀ (h : BandPackingSymmetry),
            ∀ (F' : FordFareyParameter), (BandPackingSymmetryReversesOrientation h = false) → (∀
            (gN : BandPackingSymmetry), (BandPackingSymmetryReversesOrientation gN =
            BandPackingSymmetryReversesOrientation h) → ((BandPackingSymmetryScopedPhase gN q
            false) → (
        let uN := BandVectors.1 ((FordRecursiveQuadruple F') 0)
          ((FordRecursiveQuadruple F') 1)
        (BandPackingSymmetryCircleAction gN (q 0) = (FordRecursiveQuadruple F') 0) →
            ((BandPackingSymmetryCircleAction gN (q 1) = (FordRecursiveQuadruple F') 1) → (uN =
            BandPackingSymmetryVectorAction gN hclaim))))) ) := by
  classical
  intro q hclaim h F' hrev gN horientationAdapt hqphase uN hq0 hq1
  have hh := (hqphase 0).2.1
  simpa [uN, hclaim, BandPackingSymmetryScopedPhase, BandPackingSymmetryQuadrupleAction,
    horientationAdapt, hrev, hq0, hq1] using hh

private theorem hvN :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (h : BandPackingSymmetry), ∀ (F' :
            FordFareyParameter), (BandPackingSymmetryReversesOrientation h = false) → (∀ (gN :
            BandPackingSymmetry), (BandPackingSymmetryReversesOrientation gN =
            BandPackingSymmetryReversesOrientation h) → ((BandPackingSymmetryScopedPhase gN q
            false) → (
        let v0 := BandVectors.1 (q 0) (q 2)
        let vN := BandVectors.1 ((FordRecursiveQuadruple F') 0)
          ((FordRecursiveQuadruple F') 2)
        (BandPackingSymmetryCircleAction gN (q 0) = (FordRecursiveQuadruple F') 0) →
            ((BandPackingSymmetryCircleAction gN (q 2) = (FordRecursiveQuadruple F') 2) → (vN =
            BandPackingSymmetryVectorAction gN v0))))) ) := by
  classical
  intro q h F' hrev gN horientationAdapt hqphase v0 vN hq0 hq2
  have hh := (hqphase 1).2.1
  simpa [vN, v0, BandPackingSymmetryScopedPhase, BandPackingSymmetryQuadrupleAction,
    horientationAdapt, hrev, hq0, hq2] using hh

private theorem L_injective_all :
    (by
      classical
      exact
        ∀ z : BandPackingSymmetry, Function.Injective (BandPackingSymmetryVectorAction z) ) := by
  classical
  intro z
  induction z with
  | identity => intro x y hxy; exact hxy
  | shift w => intro x y hxy; exact hxy
  | negate =>
      intro x y hxy
      apply Zsqrtd.ext
      · have hh := congrArg (fun z : GaussianInt => z.im) hxy
        simpa [BandPackingSymmetryVectorAction, GaussianQuarterTurn] using hh
      · have hh := congrArg (fun z : GaussianInt => z.re) hxy
        have hh' : -x.im = -y.im := by
          simpa [BandPackingSymmetryVectorAction, GaussianQuarterTurn] using hh
        exact neg_injective hh'
  | conjugate =>
      intro x y hxy
      apply Zsqrtd.ext
      · have hh := congrArg (fun z : GaussianInt => z.re) hxy
        have hh' : -x.re = -y.re := by
          simpa [BandPackingSymmetryVectorAction, GaussianReflection] using hh
        exact neg_injective hh'
      · have hh := congrArg (fun z : GaussianInt => z.im) hxy
        simpa [BandPackingSymmetryVectorAction, GaussianReflection] using hh
  | comp g k ihg ihk => exact ihg.comp ihk

private theorem f_injective :
    (by
      classical
      exact
        ∀ (gN : BandPackingSymmetry), ∀ (w : GaussianInt), (Function.Injective
            (BandPackingSymmetryVectorAction gN)) → (
        let f : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation (-w) (BandPackingSymmetryVectorAction gN z)
        Function.Injective f) ) := by
  classical
  intro gN w L_injective f x y hxy
  apply L_injective
  apply add_right_cancel
  change BandPackingSymmetryVectorAction gN x + (-w) =
    BandPackingSymmetryVectorAction gN y + (-w) at hxy
  exact hxy

private theorem hfv :
    (by
      classical
      exact
        ∀ (gN : BandPackingSymmetry), ∀ (w : GaussianInt),
        let f : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation (-w) (BandPackingSymmetryVectorAction gN z)
        (∀ (T : ProtoTile), FootprintVertices (BandPackingSymmetryTileAction gN T) =
            BandPackingSymmetryVectorAction gN '' FootprintVertices T) → (∀ (X : ProtoTile),
            FootprintVertices (TileTranslation (BandPackingSymmetryTileAction gN X) (-w)) = f ''
            FootprintVertices X) ) := by
  classical
  intro gN w f hvertices X
  rw [(TileTranslationFormulas (BandPackingSymmetryTileAction gN X) (-w)).2.2.2.2.2.1,
    hvertices X]
  simp only [Set.image_image]
  rfl

private theorem hfe :
    (by
      classical
      exact
        ∀ (gN : BandPackingSymmetry), ∀ (w : GaussianInt),
        let f : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation (-w) (BandPackingSymmetryVectorAction gN z)
        (∀ (T : ProtoTile), FootprintEdges (BandPackingSymmetryTileAction gN T) = (fun (e :
            Finset GaussianInt) => Finset.image (BandPackingSymmetryVectorAction gN) e) ''
            FootprintEdges T) → (∀ (X : ProtoTile), FootprintEdges (TileTranslation
            (BandPackingSymmetryTileAction gN X) (-w)) = (fun e : Finset GaussianInt => e.image
            f) '' FootprintEdges X) ) := by
  classical
  intro gN w f hedges X
  rw [(TileTranslationFormulas (BandPackingSymmetryTileAction gN X) (-w)).2.2.2.2.2.2.1,
    hedges X]
  simp only [Set.image_image, Finset.image_image, Function.comp_def]
  rfl

private theorem hPfoot :
    (by
      classical
      exact
        ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (gN : BandPackingSymmetry), ∀ (Pp : Fin (3 : ℕ)
            → Bool → ProtoTile), (∀ i, ∀ s, Pp i s = BandPackingSymmetryTileAction gN (P i s)) → (
        let Pn : Fin 3 → Bool → ProtoTile := Pp
        ∀ (w : GaussianInt),
        let Pbar : Fin 3 → Bool → ProtoTile := fun i s => TileTranslation (Pn i s) (-w)
        let f : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation (-w) (BandPackingSymmetryVectorAction gN z)
        (∀ (X : ProtoTile), FootprintVertices (TileTranslation (BandPackingSymmetryTileAction gN
            X) (-w)) = f '' FootprintVertices X) → (∀ (i : Fin 3), ∀ (s : Bool),
            FootprintVertices (Pbar i s) = f '' FootprintVertices (P i s))) ) := by
  classical
  intro P gN Pp hPp Pn w Pbar f hfv i s
  simpa [Pbar, Pn, hPp i s] using hfv (P i s)

private abbrev hQfoot := ApollonianSuperharmonic.FordT6Geometry.hPfoot

private abbrev hSfoot := ApollonianSuperharmonic.FordT6Geometry.hPfoot

private theorem hOccNorm :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (hclaim :
            GaussianInt), ∀ (F' : FordFareyParameter), ∀ (gN : BandPackingSymmetry), ∀ (Pp : Fin
            (3 : ℕ) → Bool → ProtoTile), (∀ i, ∀ s, Pp i s = BandPackingSymmetryTileAction gN (P
            i s)) → (
        let Pn : Fin 3 → Bool → ProtoTile := Pp
        ∀ (w : GaussianInt),
        let Pbar : Fin 3 → Bool → ProtoTile := fun i s => TileTranslation (Pn i s) (-w)
        let v0 := BandVectors.1 (q 0) (q 2)
        let uN := BandVectors.1 ((FordRecursiveQuadruple F') 0)
          ((FordRecursiveQuadruple F') 1)
        let vN := BandVectors.1 ((FordRecursiveQuadruple F') 0)
          ((FordRecursiveQuadruple F') 2)
        (uN = BandPackingSymmetryVectorAction gN hclaim) → ((vN = BandPackingSymmetryVectorAction
            gN v0) → ((∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (u : GaussianInt), ∀ (v :
            GaussianInt), ∀ (o : PeriodicSubtileIndex), BandPackingSymmetryTileAction gN
            (SubtileOccurrenceInterpretation S u v o) = SubtileOccurrenceInterpretation (fun (i :
            Fin (3 : ℕ)) (s : Bool) => BandPackingSymmetryTileAction gN (S i s))
            (BandPackingSymmetryVectorAction gN u) (BandPackingSymmetryVectorAction gN v) o) → (∀
            (o : PeriodicSubtileIndex), SubtileOccurrenceInterpretation Pbar uN vN o =
            TileTranslation (BandPackingSymmetryTileAction gN (SubtileOccurrenceInterpretation P
            hclaim v0 o)) (-w))))) ) := by
  classical
  intro q P hclaim F' gN Pp hPp Pn w Pbar v0 uN vN huN hvN hocc o
  have h := hocc P hclaim v0 o
  rw [← huN, ← hvN] at h
  have ht := (SubtileOccurrenceInterpretationCovariance Pn uN vN (-w) o).1
  have hfamily : (fun i s => BandPackingSymmetryTileAction gN (P i s)) = Pn := by
    funext i s
    exact (hPp i s).symm
  have h' : BandPackingSymmetryTileAction gN
      (SubtileOccurrenceInterpretation P hclaim v0 o) =
      SubtileOccurrenceInterpretation Pn uN vN o := by
    rw [hfamily] at h
    exact h
  calc
    SubtileOccurrenceInterpretation Pbar uN vN o =
        TileTranslation (SubtileOccurrenceInterpretation Pn uN vN o) (-w) := by
      simpa [Pbar] using ht.symm
    _ = TileTranslation (BandPackingSymmetryTileAction gN
        (SubtileOccurrenceInterpretation P hclaim v0 o)) (-w) :=
      congrArg (fun X : ProtoTile => TileTranslation X (-w)) h'.symm

private theorem hOccEdges :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (hclaim :
            GaussianInt), ∀ (F' : FordFareyParameter), ∀ (gN : BandPackingSymmetry), ∀ (Pp : Fin
            (3 : ℕ) → Bool → ProtoTile),
        let Pn : Fin 3 → Bool → ProtoTile := Pp
        ∀ (w : GaussianInt),
        let Pbar : Fin 3 → Bool → ProtoTile := fun i s => TileTranslation (Pn i s) (-w)
        let v0 := BandVectors.1 (q 0) (q 2)
        let uN := BandVectors.1 ((FordRecursiveQuadruple F') 0)
          ((FordRecursiveQuadruple F') 1)
        let vN := BandVectors.1 ((FordRecursiveQuadruple F') 0)
          ((FordRecursiveQuadruple F') 2)
        let f : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation (-w) (BandPackingSymmetryVectorAction gN z)
        (∀ (X : ProtoTile), FootprintEdges (TileTranslation (BandPackingSymmetryTileAction gN X)
            (-w)) = (fun e : Finset GaussianInt => e.image f) '' FootprintEdges X) → ((∀ (o :
            PeriodicSubtileIndex), SubtileOccurrenceInterpretation Pbar uN vN o = TileTranslation
            (BandPackingSymmetryTileAction gN (SubtileOccurrenceInterpretation P hclaim v0 o))
            (-w)) → (∀ (o : PeriodicSubtileIndex), FootprintEdges
            (SubtileOccurrenceInterpretation Pbar uN vN o) = (fun e : Finset GaussianInt =>
            e.image f) '' FootprintEdges (SubtileOccurrenceInterpretation P hclaim v0 o))) ) := by
  classical
  intro q P hclaim F' gN Pp Pn w Pbar v0 uN vN f hfe hOccNorm o
  rw [hOccNorm]
  exact hfe _

private theorem hOccVertices :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (hclaim :
            GaussianInt), ∀ (F' : FordFareyParameter), ∀ (gN : BandPackingSymmetry), ∀ (Pp : Fin
            (3 : ℕ) → Bool → ProtoTile),
        let Pn : Fin 3 → Bool → ProtoTile := Pp
        ∀ (w : GaussianInt),
        let Pbar : Fin 3 → Bool → ProtoTile := fun i s => TileTranslation (Pn i s) (-w)
        let v0 := BandVectors.1 (q 0) (q 2)
        let uN := BandVectors.1 ((FordRecursiveQuadruple F') 0)
          ((FordRecursiveQuadruple F') 1)
        let vN := BandVectors.1 ((FordRecursiveQuadruple F') 0)
          ((FordRecursiveQuadruple F') 2)
        let f : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation (-w) (BandPackingSymmetryVectorAction gN z)
        (∀ (X : ProtoTile), FootprintVertices (TileTranslation (BandPackingSymmetryTileAction gN
            X) (-w)) = f '' FootprintVertices X) → ((∀ (o : PeriodicSubtileIndex),
            SubtileOccurrenceInterpretation Pbar uN vN o = TileTranslation
            (BandPackingSymmetryTileAction gN (SubtileOccurrenceInterpretation P hclaim v0 o))
            (-w)) → (∀ (o : PeriodicSubtileIndex), FootprintVertices
            (SubtileOccurrenceInterpretation Pbar uN vN o) = f '' FootprintVertices
            (SubtileOccurrenceInterpretation P hclaim v0 o))) ) := by
  classical
  intro q P hclaim F' gN Pp Pn w Pbar v0 uN vN f hfv hOccNorm o
  rw [hOccNorm]
  exact hfv _

private theorem imageMem :
    (by
      classical
      exact
        ∀ (gN : BandPackingSymmetry), ∀ (w : GaussianInt),
        let f : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation (-w) (BandPackingSymmetryVectorAction gN z)
        (Function.Injective f) → (∀ (A : Set GaussianInt), ∀ (B : Set GaussianInt), (B = f '' A)
            → (∀ (x : GaussianInt), f x ∈ B ↔ x ∈ A)) ) := by
  classical
  intro gN w f f_injective A B hB x
  rw [hB]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hEq : y = x := f_injective hxy
    simpa [hEq] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem hperiodic :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (hclaim :
            GaussianInt), ∀ (F' : FordFareyParameter), ∀ (gN : BandPackingSymmetry), ∀ (Pp : Fin
            (3 : ℕ) → Bool → ProtoTile),
        let Pn : Fin 3 → Bool → ProtoTile := Pp
        ∀ (w : GaussianInt),
        let Pbar : Fin 3 → Bool → ProtoTile := fun i s => TileTranslation (Pn i s) (-w)
        (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), a ≠ b → ((FootprintEdges
            (SubtileOccurrenceInterpretation Pbar (BandVectors.1 (FordRecursiveQuadruple F' (0 :
            Fin (4 : ℕ))) (FordRecursiveQuadruple F' (1 : Fin (4 : ℕ)))) (BandVectors.1
            (FordRecursiveQuadruple F' (0 : Fin (4 : ℕ))) (FordRecursiveQuadruple F' (2 : Fin (4
            : ℕ)))) a) ∩ FootprintEdges (SubtileOccurrenceInterpretation Pbar (BandVectors.1
            (FordRecursiveQuadruple F' (0 : Fin (4 : ℕ))) (FordRecursiveQuadruple F' (1 : Fin (4
            : ℕ)))) (BandVectors.1 (FordRecursiveQuadruple F' (0 : Fin (4 : ℕ)))
            (FordRecursiveQuadruple F' (2 : Fin (4 : ℕ)))) b)).Nonempty → AllowedSubtileIncidence
            a b) ∧ (¬AllowedSubtileIncidence a b → FootprintVertices
            (SubtileOccurrenceInterpretation Pbar (BandVectors.1 (FordRecursiveQuadruple F' (0 :
            Fin (4 : ℕ))) (FordRecursiveQuadruple F' (1 : Fin (4 : ℕ)))) (BandVectors.1
            (FordRecursiveQuadruple F' (0 : Fin (4 : ℕ))) (FordRecursiveQuadruple F' (2 : Fin (4
            : ℕ)))) a) ∩ FootprintVertices (SubtileOccurrenceInterpretation Pbar (BandVectors.1
            (FordRecursiveQuadruple F' (0 : Fin (4 : ℕ))) (FordRecursiveQuadruple F' (1 : Fin (4
            : ℕ)))) (BandVectors.1 (FordRecursiveQuadruple F' (0 : Fin (4 : ℕ)))
            (FordRecursiveQuadruple F' (2 : Fin (4 : ℕ)))) b) = ∅ ∨ (FootprintVertices
            (SubtileOccurrenceInterpretation Pbar (BandVectors.1 (FordRecursiveQuadruple F' (0 :
            Fin (4 : ℕ))) (FordRecursiveQuadruple F' (1 : Fin (4 : ℕ)))) (BandVectors.1
            (FordRecursiveQuadruple F' (0 : Fin (4 : ℕ))) (FordRecursiveQuadruple F' (2 : Fin (4
            : ℕ)))) a) ∩ FootprintVertices (SubtileOccurrenceInterpretation Pbar (BandVectors.1
            (FordRecursiveQuadruple F' (0 : Fin (4 : ℕ))) (FordRecursiveQuadruple F' (1 : Fin (4
            : ℕ)))) (BandVectors.1 (FordRecursiveQuadruple F' (0 : Fin (4 : ℕ)))
            (FordRecursiveQuadruple F' (2 : Fin (4 : ℕ)))) b)).Subsingleton)) → (
        let v0 := BandVectors.1 (q 0) (q 2)
        let uN := BandVectors.1 ((FordRecursiveQuadruple F') 0)
          ((FordRecursiveQuadruple F') 1)
        let vN := BandVectors.1 ((FordRecursiveQuadruple F') 0)
          ((FordRecursiveQuadruple F') 2)
        let f : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation (-w) (BandPackingSymmetryVectorAction gN z)
        (Function.Injective f) → ((∀ (o : PeriodicSubtileIndex), FootprintEdges
            (SubtileOccurrenceInterpretation Pbar uN vN o) = (fun e : Finset GaussianInt =>
            e.image f) '' FootprintEdges (SubtileOccurrenceInterpretation P hclaim v0 o)) → ((∀
            (o : PeriodicSubtileIndex), FootprintVertices (SubtileOccurrenceInterpretation Pbar
            uN vN o) = f '' FootprintVertices (SubtileOccurrenceInterpretation P hclaim v0 o)) →
            ((∀ a b : PeriodicSubtileIndex, a ≠ b → ((FootprintEdges
            (SubtileOccurrenceInterpretation P hclaim v0 a) ∩ FootprintEdges
            (SubtileOccurrenceInterpretation P hclaim v0 b)).Nonempty → AllowedSubtileIncidence a
            b) ∧ (¬ AllowedSubtileIncidence a b → FootprintVertices
            (SubtileOccurrenceInterpretation P hclaim v0 a) ∩ FootprintVertices
            (SubtileOccurrenceInterpretation P hclaim v0 b) = ∅ ∨ (FootprintVertices
            (SubtileOccurrenceInterpretation P hclaim v0 a) ∩ FootprintVertices
            (SubtileOccurrenceInterpretation P hclaim v0 b)).Subsingleton)))))) ) := by
  classical
  intro q P hclaim F' gN Pp Pn w Pbar hledgerN v0 uN vN f f_injective hOccEdges hOccVertices a b hab
  constructor
  · intro hedgesAB
    have hedgesN :
        (FootprintEdges (SubtileOccurrenceInterpretation Pbar uN vN a) ∩
          FootprintEdges (SubtileOccurrenceInterpretation Pbar uN vN b)).Nonempty := by
      rcases hedgesAB with ⟨e, hea, heb⟩
      refine ⟨e.image f, ?_, ?_⟩
      · rw [hOccEdges]
        exact Set.mem_image_of_mem (fun e : Finset GaussianInt => e.image f) hea
      · rw [hOccEdges]
        exact Set.mem_image_of_mem (fun e : Finset GaussianInt => e.image f) heb
    exact (hledgerN a b hab).1 hedgesN
  · intro hnot
    rcases (hledgerN a b hab).2 hnot with hempty | hsingle
    · left
      ext x
      constructor
      · intro hx
        have hxN : f x ∈
          FootprintVertices (SubtileOccurrenceInterpretation Pbar uN vN a) ∩
            FootprintVertices (SubtileOccurrenceInterpretation Pbar uN vN b) := by
          rw [hOccVertices a, hOccVertices b]
          exact ⟨Set.mem_image_of_mem f hx.1, Set.mem_image_of_mem f hx.2⟩
        rw [hempty] at hxN
        simp at hxN
      · simp
    · right
      intro x hx y hy
      have hxN : f x ∈
          FootprintVertices (SubtileOccurrenceInterpretation Pbar uN vN a) ∩
            FootprintVertices (SubtileOccurrenceInterpretation Pbar uN vN b) := by
        rw [hOccVertices a, hOccVertices b]
        exact ⟨Set.mem_image_of_mem f hx.1, Set.mem_image_of_mem f hx.2⟩
      have hyN : f y ∈
          FootprintVertices (SubtileOccurrenceInterpretation Pbar uN vN a) ∩
            FootprintVertices (SubtileOccurrenceInterpretation Pbar uN vN b) := by
        rw [hOccVertices a, hOccVertices b]
        exact ⟨Set.mem_image_of_mem f hy.1, Set.mem_image_of_mem f hy.2⟩
      exact f_injective (hsingle hxN hyN)

private theorem hraw1 :
    (by
      classical
      exact
        ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (Q : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (gN :
            BandPackingSymmetry), ∀ (Pp : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (Qp : Fin (3 : ℕ) →
            Bool → ProtoTile),
        let Pn : Fin 3 → Bool → ProtoTile := Pp
        let Qn : Fin 3 → Bool → ProtoTile := Qp
        ∀ (w : GaussianInt),
        let Pbar : Fin 3 → Bool → ProtoTile := fun i s => TileTranslation (Pn i s) (-w)
        let Qbar : Fin 3 → Bool → ProtoTile := fun i s => TileTranslation (Qn i s) (-w)
        (FootprintVertices (Pbar (0 : Fin (3 : ℕ)) true) ∩ FootprintVertices (Pbar (1 : Fin (3 :
            ℕ)) true) ⊆ FootprintVertices (Qbar (1 : Fin (3 : ℕ)) true) ∩ FootprintVertices (Pbar
            (1 : Fin (3 : ℕ)) true)) → (
        let f : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation (-w) (BandPackingSymmetryVectorAction gN z)
        (∀ (i : Fin 3), ∀ (s : Bool), FootprintVertices (Pbar i s) = f '' FootprintVertices (P i
            s)) → ((∀ (i : Fin 3), ∀ (s : Bool), FootprintVertices (Qbar i s) = f ''
            FootprintVertices (Q i s)) → ((∀ (A : Set GaussianInt), ∀ (B : Set GaussianInt), (B =
            f '' A) → (∀ (x : GaussianInt), f x ∈ B ↔ x ∈ A)) → (FootprintVertices (P 0 true) ∩
            FootprintVertices (P 1 true) ⊆ FootprintVertices (Q 1 true) ∩ FootprintVertices (P 1
            true))))) ) := by
  classical
  intro P Q gN Pp Qp Pn Qn w Pbar Qbar hraw1N f hPfoot hQfoot imageMem x hx
  have hxN : f x ∈ FootprintVertices (Pbar 0 true) ∩
      FootprintVertices (Pbar 1 true) := by
    exact ⟨(imageMem _ _ (hPfoot 0 true) x).2 hx.1,
      (imageMem _ _ (hPfoot 1 true) x).2 hx.2⟩
  have hout := hraw1N hxN
  exact ⟨(imageMem _ _ (hQfoot 1 true) x).1 hout.1,
    (imageMem _ _ (hPfoot 1 true) x).1 hout.2⟩

private theorem hraw2 :
    (by
      classical
      exact
        ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (Q : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (S :
            Fin (3 : ℕ) → Bool → ProtoTile), ∀ (gN : BandPackingSymmetry), ∀ (Pp : Fin (3 : ℕ) →
            Bool → ProtoTile), ∀ (Qp : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (Sp : Fin (3 : ℕ) →
            Bool → ProtoTile),
        let Pn : Fin 3 → Bool → ProtoTile := Pp
        let Qn : Fin 3 → Bool → ProtoTile := Qp
        let Sn : Fin 3 → Bool → ProtoTile := Sp
        ∀ (w : GaussianInt),
        let Pbar : Fin 3 → Bool → ProtoTile := fun i s => TileTranslation (Pn i s) (-w)
        let Qbar : Fin 3 → Bool → ProtoTile := fun i s => TileTranslation (Qn i s) (-w)
        let Sbar : Fin 3 → Bool → ProtoTile := fun i s => TileTranslation (Sn i s) (-w)
        (FootprintVertices (Pbar (0 : Fin (3 : ℕ)) true) ∩ FootprintVertices (Pbar (0 : Fin (3 :
            ℕ)) false) ⊆ FootprintVertices (Qbar (1 : Fin (3 : ℕ)) true) ∩ FootprintVertices
            (Sbar (2 : Fin (3 : ℕ)) false) ∪ FootprintVertices (Qbar (0 : Fin (3 : ℕ)) false) ∪
            FootprintVertices (Qbar (2 : Fin (3 : ℕ)) true) ∩ FootprintVertices (Sbar (1 : Fin (3
            : ℕ)) false)) → (
        let f : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation (-w) (BandPackingSymmetryVectorAction gN z)
        (∀ (i : Fin 3), ∀ (s : Bool), FootprintVertices (Pbar i s) = f '' FootprintVertices (P i
            s)) → ((∀ (i : Fin 3), ∀ (s : Bool), FootprintVertices (Qbar i s) = f ''
            FootprintVertices (Q i s)) → ((∀ (i : Fin 3), ∀ (s : Bool), FootprintVertices (Sbar i
            s) = f '' FootprintVertices (S i s)) → ((∀ (A : Set GaussianInt), ∀ (B : Set
            GaussianInt), (B = f '' A) → (∀ (x : GaussianInt), f x ∈ B ↔ x ∈ A)) →
            (FootprintVertices (P 0 true) ∩ FootprintVertices (P 0 false) ⊆ (FootprintVertices (Q
            1 true) ∩ FootprintVertices (S 2 false)) ∪ FootprintVertices (Q 0 false) ∪
            (FootprintVertices (Q 2 true) ∩ FootprintVertices (S 1 false))))))) ) := by
  classical
  intro P Q S gN Pp Qp Sp Pn Qn Sn w Pbar Qbar Sbar hraw2N f hPfoot hQfoot hSfoot imageMem x hx
  have hxN : f x ∈ FootprintVertices (Pbar 0 true) ∩
      FootprintVertices (Pbar 0 false) := by
    exact ⟨(imageMem _ _ (hPfoot 0 true) x).2 hx.1,
      (imageMem _ _ (hPfoot 0 false) x).2 hx.2⟩
  have hout := hraw2N hxN
  have hA : f x ∈ FootprintVertices (Qbar 1 true) ∩
      FootprintVertices (Sbar 2 false) ↔
        x ∈ FootprintVertices (Q 1 true) ∩ FootprintVertices (S 2 false) := by
    simp only [Set.mem_inter_iff]
    exact and_congr (imageMem _ _ (hQfoot 1 true) x)
      (imageMem _ _ (hSfoot 2 false) x)
  have hB : f x ∈ FootprintVertices (Qbar 0 false) ↔
      x ∈ FootprintVertices (Q 0 false) := imageMem _ _ (hQfoot 0 false) x
  have hC : f x ∈ FootprintVertices (Qbar 2 true) ∩
      FootprintVertices (Sbar 1 false) ↔
        x ∈ FootprintVertices (Q 2 true) ∩ FootprintVertices (S 1 false) := by
    simp only [Set.mem_inter_iff]
    exact and_congr (imageMem _ _ (hQfoot 2 true) x)
      (imageMem _ _ (hSfoot 1 false) x)
  simp only [Set.mem_union, Set.mem_inter_iff, hA, hB, hC] at hout ⊢
  exact hout

end FordT6Geometry

theorem P4564T2FordT6Transport :
    ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (∀ (T : ProtoTile),
        (BandPrototile (q 0) T) → (∀ (a : Fin 3), ∀ (g : BandPackingSymmetry), ∀ (F :
        FordFareyParameter), (1 < F.q) → ((BandPackingSymmetryQuadrupleAction g
      ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ] = FordRecursiveQuadruple F) → ((∀ (r : Fin
          4 → CircleCoordinates), ProperBandQuadruple r →
      r 0 = q 1 → r 2 = q 2 → r 3 = q 3 →
      (q 2).1 ≤ (q 1).1 → (q 3).1 ≤ (q 2).1 →
      1 < (q 2).1 →
      ∀ (P : Fin 3 → Bool → ProtoTile), ∀ (Q : Fin 3 → Bool → ProtoTile), ∀ (S : Fin 3 → Bool →
          ProtoTile), (∀ i, ∀ s, BandSubtileOccurrence q T i s (P i s)) →
      (∀ x, x ∈ T.cells ↔ ∃ i s, x ∈ (P i s).cells) →
      (∀ i, ∀ s, BandSubtileOccurrence r (P 0 true) i s (Q i s)) →
      (∀ x, x ∈ (P 0 true).cells ↔ ∃ i s, x ∈ (Q i s).cells) →
      (∀ i, ∀ s, BandSubtileOccurrence r (P 0 false) i s (S i s)) →
      (∀ x, x ∈ (P 0 false).cells ↔ ∃ i s, x ∈ (S i s).cells) →
      (
    let u := BandVectors.1 (q 0) (q 1)
       let v := BandVectors.1 (q 0) (q 2)
       (∀ a b : PeriodicSubtileIndex, a ≠ b →
         ((FootprintEdges (SubtileOccurrenceInterpretation P u v a) ∩
             FootprintEdges
               (SubtileOccurrenceInterpretation P u v b)).Nonempty →
           AllowedSubtileIncidence a b) ∧
         (¬ AllowedSubtileIncidence a b →
           FootprintVertices (SubtileOccurrenceInterpretation P u v a) ∩
               FootprintVertices
                 (SubtileOccurrenceInterpretation P u v b) = ∅ ∨
             (FootprintVertices
                  (SubtileOccurrenceInterpretation P u v a) ∩
                FootprintVertices
                  (SubtileOccurrenceInterpretation P u v b)).Subsingleton)) ∧
       FootprintVertices (P 0 true) ∩ FootprintVertices (P 1 true) ⊆
         FootprintVertices (Q 1 true) ∩ FootprintVertices (P 1 true) ∧
       FootprintVertices (P 0 true) ∩ FootprintVertices (P 0 false) ⊆
         (FootprintVertices (Q 1 true) ∩ FootprintVertices (S 2 false)) ∪
           FootprintVertices (Q 0 false) ∪
           (FootprintVertices (Q 2 true) ∩
             FootprintVertices (S 1 false)))))))) := by
  intro q hq T hT a g F hF hnormal r hr hr0 hr2 hr3 h12 h23 hlarge
      P Q S hP hcells hQ hQcells hS hScells hclaim
  have qcur := ProperBandCurvatureStructure q hq
  have hlineq := FordT6Geometry.hlineq q hq a g F hnormal h12 hlarge qcur
  obtain ⟨b, h, F', hF', hrev, hword, hzero, hnorm⟩ :=
    FordRegimeConverse q hq hlineq
  have hb := FordT6Geometry.hb q h12 hlarge qcur hlineq b hzero
  subst b
  have hnormq := FordT6Geometry.hnormq q h F' hnorm
  obtain ⟨negative, hphase, hphaseR, hphaseT, hcircle, horientation,
      hquad, hvector, ⟨gN, hwordAdapt, hcircleAdapt, horientationAdapt, hquadAdapt,
        hphaseAdaptQ, hphaseAdaptRest⟩⟩ :=
    BandPackingSymmetryProjectiveVectorCovariance h q hq
  have hqphase : BandPackingSymmetryScopedPhase gN q false := hphaseAdaptQ
  rcases hphaseAdaptRest with ⟨hphaseAdaptR, _⟩
  have hrphase : BandPackingSymmetryScopedPhase gN r false :=
    hphaseAdaptR r hr hr0 hr2 hr3
  have hqhat : BandPackingSymmetryQuadrupleAction gN q = FordRecursiveQuadruple F' :=
      FordT6Geometry.hqhat q h F' hnormq gN hquadAdapt
  have hrproper : ProperBandQuadruple (BandPackingSymmetryQuadrupleAction gN r) :=
    BandPackingSymmetryProperCovariance gN r hr
  have hr0hat : (BandPackingSymmetryQuadrupleAction gN r) 0 =
      (FordRecursiveQuadruple F') 1 := FordT6Geometry.hr0hat q r hr0 h F' gN horientationAdapt hqhat
  have hr2hat : (BandPackingSymmetryQuadrupleAction gN r) 2 =
      (FordRecursiveQuadruple F') 2 := FordT6Geometry.hr2hat q r hr2 h F' hrev gN
          horientationAdapt hqhat
  have hr3hat : (BandPackingSymmetryQuadrupleAction gN r) 3 =
      (FordRecursiveQuadruple F') 3 := FordT6Geometry.hr3hat q r hr3 h F' hrev gN
          horientationAdapt hqhat
  have horder : ((FordRecursiveQuadruple F') 2).1 ≤
      ((FordRecursiveQuadruple F') 1).1 := FordT6Geometry.horder q r hr0 hr2 h12 h F' hrev gN
          horientationAdapt hr0hat hr2hat
  have hlarge' : 1 < ((FordRecursiveQuadruple F') 2).1 := FordT6Geometry.hlarge' q r hr2 hlarge h
      F' hrev gN horientationAdapt hr2hat
  have hT' : BandPrototile ((BandPackingSymmetryQuadrupleAction gN q) 0)
      (BandPackingSymmetryTileAction gN T) := FordT6Geometry.hT' q T hT gN
  have covP := (BandPackingSymmetryCovariance gN).2.2 q T P hq hT hP hcells
  rcases covP with ⟨dp, ep, Pp, hpphase, hpe, hpmem, hpp, hpcells⟩
  have hdp : dp = false :=
    BandPackingSymmetryScopedPhaseUnique gN q hq dp false hpphase hqphase
  have hep (i : Fin 3) (s : Bool) := FordT6Geometry.hep h hrev gN horientationAdapt dp ep hpe hdp
      i s
  have hPp := FordT6Geometry.hPp P gN ep Pp hpmem hep
  have hP0plus : BandPrototile (r 0) (P 0 true) := by
    simpa [hr0] using (hP 0 true).1
  have hP0minus : BandPrototile (r 0) (P 0 false) := by
    simpa [hr0] using (hP 0 false).1
  have hQcov := (BandPackingSymmetryCovariance gN).2.2 r (P 0 true) Q hr
    hP0plus (fun i s => hQ i s) hQcells
  have hScov := (BandPackingSymmetryCovariance gN).2.2 r (P 0 false) S hr
    hP0minus (fun i s => hS i s) hScells
  rcases hQcov with ⟨dq, eq, Qp, hqphase', hqe, hqmem, hqocc, hqcells'⟩
  rcases hScov with ⟨ds, es, Sp, hsphase', hse, hsmem, hsocc, hscells'⟩
  have hdq : dq = false :=
    BandPackingSymmetryScopedPhaseUnique gN r hr dq false hqphase' hrphase
  have hds : ds = false :=
    BandPackingSymmetryScopedPhaseUnique gN r hr ds false hsphase' hrphase
  have heq (i : Fin 3) (s : Bool) := FordT6Geometry.heq h hrev gN horientationAdapt dq eq hqe hdq
      i s
  have hes (i : Fin 3) (s : Bool) := FordT6Geometry.hes h hrev gN horientationAdapt ds es hse hds
      i s
  have hQp := FordT6Geometry.hQp Q gN eq Qp hqmem heq
  have hSp := FordT6Geometry.hSp S gN es Sp hsmem hes
  let rN := BandPackingSymmetryQuadrupleAction gN r
  let Tn := BandPackingSymmetryTileAction gN T
  let Pn : Fin 3 → Bool → ProtoTile := Pp
  let Qn : Fin 3 → Bool → ProtoTile := Qp
  let Sn : Fin 3 → Bool → ProtoTile := Sp
  have hFord := FordT6Geometry.hFord F'
  have hTn : BandPrototile ((FordRecursiveQuadruple F') 0) Tn := by
    simpa [Tn, hqhat] using hT'
  obtain ⟨w, hcellsNormal, hemptyNormal⟩ :=
    BandPrototileTranslationNormalForm _ Tn (FordTile F'.q) hTn hFord
  let Pbar : Fin 3 → Bool → ProtoTile := fun i s => TileTranslation (Pn i s) (-w)
  let Qbar : Fin 3 → Bool → ProtoTile := fun i s => TileTranslation (Qn i s) (-w)
  let Sbar : Fin 3 → Bool → ProtoTile := fun i s => TileTranslation (Sn i s) (-w)
  let Tbar : ProtoTile := TileTranslation Tn (-w)
  have cancelTranslation (U : ProtoTile) := FordT6Geometry.cancelTranslation w U
  have hrootCells := FordT6Geometry.hrootCells T F' gN w hcellsNormal cancelTranslation
  have hrootAnchor := FordT6Geometry.hrootAnchor T F' gN w hemptyNormal
  have hobs := ProtoTileObservableExtensionality Tbar (FordTile F'.q)
    hrootCells hrootAnchor
  have hPbar := FordT6Geometry.hPbar q T F' gN hqhat Pp hpp w
  have hPford : ∀ i s,
      BandSubtileOccurrence (FordRecursiveQuadruple F') (FordTile F'.q) i s (Pbar i s) :=
          FordT6Geometry.hPford T F' gN Pp w hobs hPbar
  have hQbar : ∀ i s, BandSubtileOccurrence rN (Pbar 0 true) i s (Qbar i s) :=
      FordT6Geometry.hQbar r P gN Pp hPp Qp hqocc w
  have hSbar : ∀ i s, BandSubtileOccurrence rN (Pbar 0 false) i s (Sbar i s) :=
      FordT6Geometry.hSbar r P gN Pp hPp Sp hsocc w
  have hFordBase := FordBaseT6 F' hF' rN hrproper (by simpa [rN] using hr0hat)
    (by simpa [rN] using hr2hat) (by simpa [rN] using hr3hat)
    horder hlarge' Pbar Qbar Sbar hPford hQbar hSbar
  rcases hFordBase with ⟨hledgerN, hraw1N, hraw2N⟩
  have hq0 := FordT6Geometry.hq0 q h F' hrev gN horientationAdapt hqhat
  have hq1 := FordT6Geometry.hq1At383 q h F' hrev gN horientationAdapt hqhat
  have hq2 := FordT6Geometry.hq2At387 q h F' hrev gN horientationAdapt hqhat
  have huN := FordT6Geometry.huN q h F' hrev gN horientationAdapt hqphase hq0 hq1
  have hvN := FordT6Geometry.hvN q h F' hrev gN horientationAdapt hqphase hq0 hq2
  have L_injective_all := FordT6Geometry.L_injective_all
  have L_injective := L_injective_all gN
  let f : GaussianInt → GaussianInt := fun z =>
    GaussianTranslation (-w) (BandPackingSymmetryVectorAction gN z)
  have f_injective := FordT6Geometry.f_injective gN w L_injective
  obtain ⟨_, _, _, _, _, _, _, hvertices, hedges, _, hocc⟩ :=
    BandPackingSymmetryTilingTransport gN
  have hfv (X : ProtoTile) := FordT6Geometry.hfv gN w hvertices X
  have hfe (X : ProtoTile) := FordT6Geometry.hfe gN w hedges X
  have hPfoot (i : Fin 3) (s : Bool) := FordT6Geometry.hPfoot P gN Pp hPp w hfv i s
  have hQfoot (i : Fin 3) (s : Bool) := FordT6Geometry.hQfoot Q gN Qp hQp w hfv i s
  have hSfoot (i : Fin 3) (s : Bool) := FordT6Geometry.hSfoot S gN Sp hSp w hfv i s
  have hOccNorm (o : PeriodicSubtileIndex) := FordT6Geometry.hOccNorm q P hclaim F' gN Pp hPp w
      huN hvN hocc o
  have hOccEdges (o : PeriodicSubtileIndex) := FordT6Geometry.hOccEdges q P hclaim F' gN Pp w hfe
      hOccNorm o
  have hOccVertices (o : PeriodicSubtileIndex) := FordT6Geometry.hOccVertices q P hclaim F' gN Pp
      w hfv hOccNorm o
  have imageMem (A B : Set GaussianInt) (hB : B = f '' A) (x : GaussianInt) :=
      FordT6Geometry.imageMem gN w f_injective A B hB x
  have hperiodic := FordT6Geometry.hperiodic q P hclaim F' gN Pp w hledgerN f_injective hOccEdges
      hOccVertices
  have hraw1 := FordT6Geometry.hraw1 P Q gN Pp Qp w hraw1N hPfoot hQfoot imageMem
  have hraw2 := FordT6Geometry.hraw2 P Q S gN Pp Qp Sp w hraw2N hPfoot hQfoot hSfoot imageMem
  dsimp
  exact ⟨hperiodic, hraw1, hraw2⟩

end ApollonianSuperharmonic

end
