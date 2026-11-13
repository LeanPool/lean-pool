/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4261T2LiteralInterface
public import LeanPool.ApollonianSuperharmonic.OpposingBoundaryOdometerStrings
public import LeanPool.ApollonianSuperharmonic.OpposingStringInterfacePath
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.P4158T1AncestorCells
public import LeanPool.ApollonianSuperharmonic.P4250T1DefinedHalfIntegralSlope
public import LeanPool.ApollonianSuperharmonic.P4055T1ExactTripleImage
public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTripleRetargetMiddle

-- [TABLET NODE: P4261T2UnitInterface]

/-!
# P4261T2UnitInterface

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace UnitInterfaceGeometry

private theorem hcentMinusQ :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (T : ProtoTile), ∀ (Rminus :
            ProtoTile), ∀ (q' : Fin (4 : ℕ) → CircleCoordinates), (TileCentroid Rminus -
            TileCentroid T = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.1 (q' i.succ) (q' (0 :
            Fin (4 : ℕ))) - BandVectors.1 (q' (0 : Fin (4 : ℕ))) (q' i.succ))) → ((q' i.succ = q
            i.succ) → ((q' 0 = q 0) → (TileCentroid Rminus - TileCentroid T = (1 / 2 : Real) •
            GaussianRealPoint (BandVectors.1 (q i.succ) (q 0) - BandVectors.1 (q 0) (q
            i.succ))))) ) := by
  classical
  intro q i T Rminus q' hcentMinus hqi' hq0'
  rw [hqi', hq0'] at hcentMinus
  exact hcentMinus

private theorem hcentPlusQ :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (T : ProtoTile), ∀ (Rplus :
            ProtoTile), ∀ (q' : Fin (4 : ℕ) → CircleCoordinates), (TileCentroid Rplus -
            TileCentroid T = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.1 (q' i.succ) (q' (0 :
            Fin (4 : ℕ))) + BandVectors.1 (q' (0 : Fin (4 : ℕ))) (q' i.succ))) → ((q' i.succ = q
            i.succ) → ((q' 0 = q 0) → (TileCentroid Rplus - TileCentroid T = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) + GaussianRealPoint
            (BandVectors.1 (q 0) (q i.succ)))))) ) := by
  classical
  intro q i T Rplus q' hcentPlus hqi' hq0'
  rw [hqi', hq0'] at hcentPlus
  simpa [GaussianRealPoint] using hcentPlus

private theorem hcentDiff :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (T : ProtoTile), ∀ (Rminus :
            ProtoTile), ∀ (Rplus : ProtoTile), (TileCentroid Rminus - TileCentroid T = (1 / 2 :
            Real) • GaussianRealPoint (BandVectors.1 (q i.succ) (q 0) - BandVectors.1 (q 0) (q
            i.succ))) → ((TileCentroid Rplus - TileCentroid T = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) + GaussianRealPoint
            (BandVectors.1 (q 0) (q i.succ)))) → (TileCentroid Rplus - TileCentroid Rminus =
            GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)))) ) := by
  classical
  intro q i T Rminus Rplus hcentMinusQ hcentPlusQ
  have hpR : (TileCentroid Rplus).1 - (TileCentroid T).1 =
      (1 / 2 : Real) * ((GaussianInt.toComplex (BandVectors.1 (q i.succ) (q 0))).re +
        (GaussianInt.toComplex (BandVectors.1 (q 0) (q i.succ))).re) := by
    have hp := congrArg Prod.fst hcentPlusQ
    simpa [GaussianRealPoint, Prod.smul_mk, Zsqrtd.re_add,
      Int.cast_add, Prod.fst_sub] using hp
  have hmR : (TileCentroid Rminus).1 - (TileCentroid T).1 =
      (1 / 2 : Real) * ((GaussianInt.toComplex (BandVectors.1 (q i.succ) (q 0))).re -
        (GaussianInt.toComplex (BandVectors.1 (q 0) (q i.succ))).re) := by
    have hm := congrArg Prod.fst hcentMinusQ
    simpa [GaussianRealPoint, Prod.smul_mk, Zsqrtd.re_sub,
      Int.cast_sub, Prod.fst_sub] using hm
  have hpI : (TileCentroid Rplus).2 - (TileCentroid T).2 =
      (1 / 2 : Real) * ((GaussianInt.toComplex (BandVectors.1 (q i.succ) (q 0))).im +
        (GaussianInt.toComplex (BandVectors.1 (q 0) (q i.succ))).im) := by
    have hp := congrArg Prod.snd hcentPlusQ
    simpa [GaussianRealPoint, Prod.smul_mk, Zsqrtd.im_add,
      Int.cast_add, Prod.snd_sub] using hp
  have hmI : (TileCentroid Rminus).2 - (TileCentroid T).2 =
      (1 / 2 : Real) * ((GaussianInt.toComplex (BandVectors.1 (q i.succ) (q 0))).im -
        (GaussianInt.toComplex (BandVectors.1 (q 0) (q i.succ))).im) := by
    have hm := congrArg Prod.snd hcentMinusQ
    simpa [GaussianRealPoint, Prod.smul_mk, Zsqrtd.im_sub,
      Int.cast_sub, Prod.snd_sub] using hm
  apply Prod.ext
  · change (TileCentroid Rplus).1 - (TileCentroid Rminus).1 =
      (((BandVectors.1 (q 0) (q i.succ)).re : Int) : Real)
    simp only [GaussianInt.intCast_re]
    linarith
  · change (TileCentroid Rplus).2 - (TileCentroid Rminus).2 =
      (((BandVectors.1 (q 0) (q i.succ)).im : Int) : Real)
    simp only [GaussianInt.intCast_im]
    linarith

private theorem hnormSq :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3),
        let w : GaussianInt := BandVectors.1 (q 0) (q i.succ)
        (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ) ^ (2 : ℕ) = (q i.succ).1 • (q (0 : Fin (4
            : ℕ))).2 - (q (0 : Fin (4 : ℕ))).1 • (q i.succ).2) → ((Zsqrtd.norm ((q i.succ).1 • (q
            (0 : Fin (4 : ℕ))).2 - (q (0 : Fin (4 : ℕ))).1 • (q i.succ).2) = ((q (0 : Fin (4 :
            ℕ))).1 + (q i.succ).1) ^ (2 : ℕ)) → (Zsqrtd.norm w ^ 2 = ((q 0).1 + (q i.succ).1) ^
            2)) ) := by
  classical
  intro q i w hvector htangent
  calc
    Zsqrtd.norm w ^ 2 = Zsqrtd.norm (w ^ 2) := by
      simp [w, pow_two]
    _ = Zsqrtd.norm ((q i.succ).1 • (q 0).2 -
        (q 0).1 • (q i.succ).2) := by
      change Zsqrtd.norm (BandVectors.1 (q 0) (q i.succ) ^ 2) = _
      rw [hvector]
    _ = _ := htangent

private theorem hcurvSum :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandOrderedGeneralConfiguration q) → (∀ (D :
            BandCircle), ∀ (i : Fin 3), (q i.succ = D.1.1) → ((D.1.1.1 = (1 : ℤ)) → (5 < (q 0).1
            + (q i.succ).1))) ) := by
  classical
  intro q cfg D i hD hunit
  rw [hD, hunit]
  have hc := cfg.childLarge
  omega

private theorem hnormBig :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3),
        let w : GaussianInt := BandVectors.1 (q 0) (q i.succ)
        (Zsqrtd.norm w ^ 2 = ((q 0).1 + (q i.succ).1) ^ 2) → ((5 < (q 0).1 + (q i.succ).1) → (5 <
            Zsqrtd.norm w)) ) := by
  classical
  intro q i w hnormSq hcurvSum
  have hn := GaussianInt.norm_nonneg w
  nlinarith [hnormSq, sq_nonneg (Zsqrtd.norm w - 5)]

private theorem hrealPointInj :
    (by
      classical
      exact
        Function.Injective GaussianRealPoint ) := by
  classical
  intro x y hxy
  apply Zsqrtd.ext
  · have hr := congrArg Prod.fst hxy
    change ((x.re : Int) : Real) = ((y.re : Int) : Real) at hr
    exact_mod_cast hr
  · have hi := congrArg Prod.snd hxy
    change ((x.im : Int) : Real) = ((y.im : Int) : Real) at hi
    exact_mod_cast hi

private theorem hRminusNeRplus :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (Rminus : ProtoTile), ∀ (Rplus :
            ProtoTile), (TileCentroid Rplus - TileCentroid Rminus = GaussianRealPoint
            (BandVectors.1 (q 0) (q i.succ))) → (
        let w : GaussianInt := BandVectors.1 (q 0) (q i.succ)
        (5 < Zsqrtd.norm w) → ((Function.Injective GaussianRealPoint) → (Rminus ≠ Rplus))) ) := by
  classical
  intro q i Rminus Rplus hcentDiff w hnormBig hrealPointInj heq
  have hz : GaussianRealPoint w = 0 := by
    have h := hcentDiff
    rw [heq] at h
    simpa [w] using h.symm
  have hw : w = 0 := by
    apply hrealPointInj
    simpa [GaussianRealPoint] using hz
  rw [hw] at hnormBig
  norm_num [Zsqrtd.norm] at hnormBig

private theorem hunitStepNorm :
    (by
      classical
      exact
        ∀ (orientation : Bool), ∀ (z : GaussianInt), (UnitTriangularStep orientation z) →
            (Zsqrtd.norm z ≤ 2) ) := by
  classical
  intro orientation z hz
  by_cases ho : orientation
  · simp only [UnitTriangularStep, ite_eq_left ho] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with h | h | h | h | h | h <;> subst z <;>
      norm_num [Zsqrtd.norm]
  · simp only [UnitTriangularStep, ite_eq_right ho] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with h | h | h | h | h | h <;> subst z <;>
      norm_num [Zsqrtd.norm]

private theorem hnonadj :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (D : BandCircle), ∀ (i : Fin 3), (D.1.1.1 = (1 : ℤ))
            → (∀ (orientation : Bool), ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile),
            (TileCentroid Rplus - TileCentroid Rminus = GaussianRealPoint (BandVectors.1 (q 0) (q
            i.succ))) → (
        let w : GaussianInt := BandVectors.1 (q 0) (q i.succ)
        (5 < Zsqrtd.norm w) → ((Function.Injective GaussianRealPoint) → ((∀ (z : GaussianInt),
            (UnitTriangularStep orientation z) → (Zsqrtd.norm z ≤ 2)) → (¬ (if D.1.1.1 = 1 then ∃
            v : GaussianInt, UnitTriangularStep orientation v ∧ TileCentroid Rplus - TileCentroid
            Rminus = GaussianRealPoint v else TileTouching Rminus Rplus)))))) ) := by
  classical
  intro q D i hunit orientation Rminus Rplus hcentDiff w hnormBig hrealPointInj hunitStepNorm
  rw [hunit]
  rintro ⟨v, hv, hcent⟩
  have hvEq : v = w := hrealPointInj (hcent.symm.trans hcentDiff)
  subst v
  have hn := hunitStepNorm w hv
  omega

private theorem htriplePositive :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (D : BandCircle), ∀ (i : Fin 3), (q (0 : Fin (4 : ℕ)) = C.1.1) → ((q
            i.succ = D.1.1) → (∀ (T : ProtoTile), ∀ (U : ProtoTile),
            (BandOrderedGeneralLayoutCertificate q cfg C T) → ((QuarterTurnSymmetric T) →
            ((TileCentroid U - TileCentroid T = GaussianRealPoint (BandVectors.1 (q i.succ) (q (0
            : Fin (4 : ℕ))))) → (∀ (Rplus : ProtoTile), ∀ (q' : Fin (4 : ℕ) → CircleCoordinates),
            (q' (0 : Fin (4 : ℕ)) = C.1.1) → ((q' i.succ = D.1.1) → ((TileCentroid Rplus -
            TileCentroid T = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.1 (q' i.succ) (q' (0 :
            Fin (4 : ℕ))) + BandVectors.1 (q' (0 : Fin (4 : ℕ))) (q' i.succ))) → ((BandPrototile
            C.1.1 T) → ((BandPrototile C.1.1 U) → ((BandPrototile D.1.1 Rplus) →
            ((Finset.Nonempty U.cells) → (Nonempty (ExactTileInterfaceTriple T U
            Rplus))))))))))))) ) := by
  classical
  intro q cfg C D i hC hD T U cert hsym hc Rplus q' hq0 hqi hcentPlus hTband hUband hRplusBand hUNe
  have hcentPlus : TileCentroid Rplus - TileCentroid T =
      (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
        GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) := by
    have hqi' : q' i.succ = q i.succ := hqi.trans hD.symm
    have hq0' : q' 0 = q 0 := hq0.trans hC.symm
    rw [hqi', hq0'] at hcentPlus
    simpa [GaussianRealPoint] using hcentPlus
  have hRplusBand' : BandPrototile (q i.succ) Rplus := by
    rw [hD]
    exact hRplusBand
  have hTplus := (BandOrderedGeneralChildInterfaces q cfg C T cert hsym).2.1
    i Rplus hRplusBand' hcentPlus
  have htransBand : BandPrototile C.1.1 (TileTranslation T
      (BandVectors.1 (q i.succ) (q 0))) := by
    exact BandPrototileTranslation _ _ _ hTband
  have htransCent : TileCentroid (TileTranslation T
      (BandVectors.1 (q i.succ) (q 0))) - TileCentroid T =
      GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) := by
    rw [(TileTranslationFormulas T _).2.2.2.2.1]
    exact Prod.ext (by simp [GaussianRealPoint]) (by simp [GaussianRealPoint])
  have htransCent' : TileCentroid (TileTranslation T
      (BandVectors.1 (q i.succ) (q 0))) = TileCentroid U := by
    have hdifference := htransCent.trans hc.symm
    apply Prod.ext
    · have hd := congrArg Prod.fst hdifference
      change (TileCentroid (TileTranslation T (BandVectors.1 (q i.succ) (q 0)))).1 -
        (TileCentroid T).1 = (TileCentroid U).1 - (TileCentroid T).1 at hd
      linarith
    · have hd := congrArg Prod.snd hdifference
      change (TileCentroid (TileTranslation T (BandVectors.1 (q i.succ) (q 0)))).2 -
        (TileCentroid T).2 = (TileCentroid U).2 - (TileCentroid T).2 at hd
      linarith
  obtain ⟨htransCells, htransAnchor⟩ := BandPrototileCentroidUnique C.1.1
    (TileTranslation T (BandVectors.1 (q i.succ) (q 0))) U htransBand hUband
    htransCent'
  obtain ⟨E⟩ := hTplus
  obtain ⟨E'⟩ := ExactTileInterfaceTripleRetargetMiddle T
    (TileTranslation T (BandVectors.1 (q i.succ) (q 0))) U Rplus
    htransCells (by
      intro hempty
      rw [htransCells] at hempty
      exact (Finset.Nonempty.ne_empty hUNe hempty).elim) E
  exact ⟨E'⟩

private theorem hFCellsInvolutive :
    (by
      classical
      exact
        ∀ (centerShift : GaussianInt),
          let F : ProtoTile → ProtoTile := fun X =>
            TileTranslation (TileHalfTurn X) centerShift
          ∀ (X : ProtoTile), (F (F X)).cells = X.cells
    ) := by
  classical
  intro centerShift F X
  have hfun : (GaussianTranslation centerShift ∘
      (fun x : GaussianInt => -x - 1 - (⟨0, 1⟩ : GaussianInt)) ∘
        GaussianTranslation centerShift ∘
          (fun x : GaussianInt => -x - 1 - (⟨0, 1⟩ : GaussianInt))) = id := by
    funext z
    apply Zsqrtd.ext <;> simp [Function.comp_def, GaussianTranslation] <;> omega
  simp only [F, TileTranslationFormulas, TileHalfTurnFormulas, Finset.image_image]
  rw [hfun, Finset.image_id]

private theorem hFCellCongr :
    (by
      classical
      exact
        ∀ (centerShift : GaussianInt),
        let F : ProtoTile → ProtoTile := fun X => TileTranslation (TileHalfTurn X) centerShift
        ∀ {X : ProtoTile}, ∀ {Y : ProtoTile}, (X.cells = Y.cells) → ((F X).cells = (F Y).cells) )
            := by
  classical
  intro centerShift F X Y hXY
  have htX := (TileTranslationFormulas (TileHalfTurn X) centerShift).1
  have htY := (TileTranslationFormulas (TileHalfTurn Y) centerShift).1
  have hhX := (TileHalfTurnFormulas X).1
  have hhY := (TileHalfTurnFormulas Y).1
  rw [htX, htY, hhX, hhY, hXY]

private theorem hFTCells :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
          ∀ (C : BandCircle),
            ∀ (D : BandCircle),
              ∀ (i : Fin 3),
                q (0 : Fin (4 : ℕ)) = C.1.1 →
                  q i.succ = D.1.1 →
                    ∀ (T : ProtoTile),
                      ∀ (U : ProtoTile),
                        ∀ (h : PartialOdometer),
                          TileOdometer C.1.1 T h →
                            TileCentroid U - TileCentroid T =
                                GaussianRealPoint
                                (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) →
                              ∀ (centerShift : GaussianInt),
                                ∀ (Rminus : ProtoTile),
                                ∀ (Rplus : ProtoTile),
                                GaussianInt →
                                ℤ →
                                (TileTranslation (TileHalfTurn Rminus)
                                centerShift).cells =
                                Rplus.cells →
                                ∀ (q' : Fin (4 : ℕ) → CircleCoordinates),
                                q' (0 : Fin (4 : ℕ)) = C.1.1 →
                                q' i.succ = D.1.1 →
                                TileCentroid Rminus - TileCentroid T =
                                (1 / 2 : ℝ) •
                                GaussianRealPoint
                                (BandVectors.1 (q' i.succ) (q' (0 : Fin (4 : ℕ))) -
                                BandVectors.1 (q' (0 : Fin (4 : ℕ))) (q' i.succ)) →
                                TileCentroid Rplus - TileCentroid T =
                                (1 / 2 : ℝ) •
                                GaussianRealPoint
                                (BandVectors.1 (q' i.succ) (q' (0 : Fin (4 : ℕ))) +
                                BandVectors.1 (q' (0 : Fin (4 : ℕ))) (q' i.succ)) →
                                BandPrototile C.1.1 U →
                                Finset.Nonempty Rplus.cells →
                                let F : ProtoTile → ProtoTile := fun X =>
                                TileTranslation (TileHalfTurn X) centerShift
                              (F T).cells = U.cells
    ) := by
  classical
  intro q C D i hC hD T U h hh hc centerShift Rminus Rplus a b hminusCells q' hq0 hqi hcentMinus
      hcentPlus hUband hRplusNe F
  let hbar := PartialOdometerAffineTranslate
    (PartialOdometerHalfTurn h) centerShift a b
  have hbarO : TileOdometer C.1.1 (F T) hbar :=
    TileOdometerAffineTranslation C.1.1 (TileHalfTurn T)
      (PartialOdometerHalfTurn h) centerShift a b
      (TileOdometerCentralSymmetry C.1.1 T h hh).1
  have hFband : BandPrototile C.1.1 (F T) :=
    TileOdometerBandPrototile C.1.1 (F T) hbar hbarO
  have hcentBar : TileCentroid (F T) = TileCentroid U := by
    have hcm := hcentMinus
    have hcp := hcentPlus
    have hqi' : q' i.succ = q i.succ := hqi.trans hD.symm
    have hq0' : q' 0 = q 0 := hq0.trans hC.symm
    rw [hqi', hq0'] at hcm hcp
    have hsum : TileCentroid Rminus + TileCentroid Rplus =
        TileCentroid T + TileCentroid T + GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) := by
      apply Prod.ext
      · have hm := congrArg Prod.fst hcm
        have hp' := congrArg Prod.fst hcp
        simp only [Prod.fst_sub, GaussianRealPoint] at hm hp'
        norm_num [Zsqrtd.re_sub, Zsqrtd.re_add, Int.cast_sub, Int.cast_add] at hm hp'
        have hc' := congrArg Prod.fst hc
        simp only [Prod.fst_sub, GaussianRealPoint] at hc'
        simp only [Prod.fst_add, GaussianRealPoint,
          GaussianInt.intCast_re] at ⊢
        linarith
      · have hm := congrArg Prod.snd hcm
        have hp' := congrArg Prod.snd hcp
        simp only [Prod.snd_sub, GaussianRealPoint] at hm hp'
        norm_num [Zsqrtd.im_sub, Zsqrtd.im_add, Int.cast_sub, Int.cast_add] at hm hp'
        have hc' := congrArg Prod.snd hc
        simp only [Prod.snd_sub, GaussianRealPoint] at hc'
        simp only [Prod.snd_add, GaussianRealPoint,
          GaussianInt.intCast_im] at ⊢
        linarith
    have hcentFminus : TileCentroid (F Rminus) = TileCentroid Rplus := by
      simp [TileCentroid, F, hminusCells, hRplusNe]
    have hcentFormula := (TileTranslationFormulas (TileHalfTurn Rminus) centerShift).2.2.2.2.1
    have hhalfFormula := (TileHalfTurnFormulas Rminus).2.2.2.2.2.2.2.1
    rw [hcentFormula, hhalfFormula] at hcentFminus
    have hcenterRe : (centerShift.re : Real) =
        (TileCentroid Rminus).1 + (TileCentroid Rplus).1 := by
      have hh := congrArg Prod.fst hcentFminus
      have hs := congrArg Prod.fst hsum
      simp only [Prod.fst_add, GaussianRealPoint] at hs
      change -(TileCentroid Rminus).1 + (centerShift.re : Real) =
        (TileCentroid Rplus).1 at hh
      nlinarith
    have hcenterIm : (centerShift.im : Real) =
        (TileCentroid Rminus).2 + (TileCentroid Rplus).2 := by
      have hh := congrArg Prod.snd hcentFminus
      have hs := congrArg Prod.snd hsum
      simp only [Prod.snd_add, GaussianRealPoint] at hs
      change -(TileCentroid Rminus).2 + (centerShift.im : Real) =
        (TileCentroid Rplus).2 at hh
      nlinarith
    rw [(TileTranslationFormulas (TileHalfTurn T) centerShift).2.2.2.2.1,
      (TileHalfTurnFormulas T).2.2.2.2.2.2.2.1]
    apply Prod.ext
    · change -(TileCentroid T).1 + (centerShift.re : Real) = (TileCentroid U).1
      have hs := congrArg Prod.fst hsum
      simp only [Prod.fst_add, GaussianRealPoint] at hs
      rw [hcenterRe]
      have hc' := congrArg Prod.fst hc
      simp only [Prod.fst_sub, GaussianRealPoint] at hc'
      nlinarith
    · change -(TileCentroid T).2 + (centerShift.im : Real) = (TileCentroid U).2
      have hs := congrArg Prod.snd hsum
      simp only [Prod.snd_add, GaussianRealPoint] at hs
      rw [hcenterIm]
      have hc' := congrArg Prod.snd hc
      simp only [Prod.snd_sub, GaussianRealPoint] at hc'
      nlinarith
  obtain ⟨hcells, _⟩ := BandPrototileCentroidUnique C.1.1 (F T) U
    hFband hUband hcentBar
  exact hcells

private theorem hFUCells :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (centerShift : GaussianInt),
        let F : ProtoTile → ProtoTile := fun X => TileTranslation (TileHalfTurn X) centerShift
        (∀ (X : ProtoTile), (F (F X)).cells = X.cells) → ((∀ {X : ProtoTile}, ∀ {Y : ProtoTile},
            (X.cells = Y.cells) → ((F X).cells = (F Y).cells)) → (((F T).cells = U.cells) → ((F
            U).cells = T.cells))) ) := by
  classical
  intro T U centerShift F hFCellsInvolutive hFCellCongr hFTCells
  have h := hFCellCongr (X := F T) (Y := U) hFTCells
  have h' : T.cells = (F U).cells := by simpa only [hFCellsInvolutive] using h
  exact h'.symm

private theorem hf :
    (by
      classical
      exact
        ∀ (centerShift : GaussianInt),
        let f : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation centerShift (GaussianQuarterTurn (GaussianQuarterTurn z))
        Function.Injective f ) := by
  classical
  intro centerShift f x y hxy
  have hqinj : Function.Injective GaussianQuarterTurn := by
    intro u v huv
    apply Zsqrtd.ext
    · simpa [GaussianQuarterTurn] using congrArg (fun z : GaussianInt => z.im) huv
    · simpa [GaussianQuarterTurn] using congrArg (fun z : GaussianInt => z.re) huv
  have hqt : GaussianQuarterTurn (GaussianQuarterTurn x) =
      GaussianQuarterTurn (GaussianQuarterTurn y) := by
    dsimp [f, GaussianTranslation] at hxy
    exact add_right_cancel hxy
  exact hqinj (hqinj hqt)

private theorem hstep :
    (by
      classical
      exact
        ∀ (centerShift : GaussianInt),
          let f : GaussianInt → GaussianInt := fun z =>
            GaussianTranslation centerShift (GaussianQuarterTurn (GaussianQuarterTurn z))
          ∀ x y : GaussianInt,
            y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
              f y = f x + 1 ∨ f y = f x - 1 ∨ f y = f x + ⟨0, 1⟩ ∨ f y = f x - ⟨0, 1⟩
    ) := by
  classical
  intro centerShift f x y hy
  rcases hy with hy | hy | hy | hy
  all_goals subst y; first
    | left; apply Zsqrtd.ext <;> simp [f, GaussianTranslation, GaussianQuarterTurn] <;> omega
    | right; left; apply Zsqrtd.ext <;> simp [f, GaussianTranslation, GaussianQuarterTurn] <;> omega
    | right; right; left; apply Zsqrtd.ext <;> simp [f, GaussianTranslation,
      GaussianQuarterTurn]; omega
    | right; right; right; apply Zsqrtd.ext <;> simp [f, GaussianTranslation,
        GaussianQuarterTurn]; omega

private theorem hvertices :
    (by
      classical
      exact
        ∀ (centerShift : GaussianInt),
        let F : ProtoTile → ProtoTile := fun X => TileTranslation (TileHalfTurn X) centerShift
        let f : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation centerShift (GaussianQuarterTurn (GaussianQuarterTurn z))
        ∀ (X : ProtoTile), FootprintVertices (F X) = f '' FootprintVertices X ) := by
  classical
  intro centerShift F f X
  rw [(TileTranslationFormulas (TileHalfTurn X) centerShift).2.2.2.2.2.1,
    (TileHalfTurnFormulas X).2.2.2.2.2.2.1]
  have hq (z : GaussianInt) : GaussianQuarterTurn (GaussianQuarterTurn z) = -z := by
    apply Zsqrtd.ext <;> simp [GaussianQuarterTurn]
  simp only [Set.image_image]
  congr 1

private theorem hedges :
    (by
      classical
      exact
        ∀ (centerShift : GaussianInt),
        let F : ProtoTile → ProtoTile := fun X => TileTranslation (TileHalfTurn X) centerShift
        let f : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation centerShift (GaussianQuarterTurn (GaussianQuarterTurn z))
        ∀ (X : ProtoTile), FootprintEdges (F X) = (fun e : Finset GaussianInt => e.image f) ''
            FootprintEdges X ) := by
  classical
  intro centerShift F f X
  have hquarter : ∀ Y : ProtoTile,
      FootprintEdges (TileQuarterTurn Y) =
        (fun e : Finset GaussianInt => e.image GaussianQuarterTurn) '' FootprintEdges Y :=
    fun Y => (TileQuarterTurnFormulas Y).2.2.2.2.2.2.1
  have hhalfEdges : FootprintEdges (TileHalfTurn X) =
      (fun e : Finset GaussianInt => e.image (fun z => -z)) '' FootprintEdges X := by
    have hcells : (TileHalfTurn X).cells =
        (TileQuarterTurn (TileQuarterTurn X)).cells :=
      (TileHalfTurnFormulas X).2.2.2.2.1
    have heq : FootprintEdges (TileHalfTurn X) =
        FootprintEdges (TileQuarterTurn (TileQuarterTurn X)) := by
      simp only [FootprintEdges]
      rw [hcells]
    rw [heq, hquarter, hquarter]
    simp only [Set.image_image, Finset.image_image]
    congr 1
  rw [(TileTranslationFormulas (TileHalfTurn X) centerShift).2.2.2.2.2.2.1,
    hhalfEdges]
  simp only [Set.image_image, Finset.image_image]
  congr 1

private theorem hpositiveImage :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (centerShift : GaussianInt), ∀ (Rplus : ProtoTile),
        let F : ProtoTile → ProtoTile := fun X => TileTranslation (TileHalfTurn X) centerShift
        let f : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation centerShift (GaussianQuarterTurn (GaussianQuarterTurn z))
        (Function.Injective f) → ((∀ x y : GaussianInt, (y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨
            y = x - ⟨0, 1⟩) → (f y = f x + 1 ∨ f y = f x - 1 ∨ f y = f x + ⟨0, 1⟩ ∨ f y = f x -
            ⟨0, 1⟩)) → ((∀ (X : ProtoTile), FootprintVertices (F X) = f '' FootprintVertices X) →
            ((∀ (X : ProtoTile), FootprintEdges (F X) = (fun e : Finset GaussianInt => e.image f)
            '' FootprintEdges X) → (∀ E : ExactTileInterfaceTriple T U Rplus, ∃ E' :
            ExactTileInterfaceTriple (F T) (F U) (F Rplus), E'.point = f E.point ∧ E'.otherAB = f
            E.otherAB)))) ) := by
  classical
  intro T U centerShift Rplus F f hf hstep hvertices hedges E
  obtain ⟨E', hp, hab, hbc, hca⟩ := P4055T1ExactTripleImage f hf hstep
    T U Rplus (F T) (F U) (F Rplus)
    (hvertices T) (hvertices U) (hvertices Rplus)
    (hedges T) (hedges U) (hedges Rplus) E
  exact ⟨E', hp, hab⟩

private theorem hnegPath :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (centerShift : GaussianInt), ∀ (Rminus :
            ProtoTile), ∀ (Rplus : ProtoTile),
        let F : ProtoTile → ProtoTile := fun X => TileTranslation (TileHalfTurn X) centerShift
        ∀ (Eimage : ExactTileInterfaceTriple (F T) (F U) (F Rplus)), ∀ (hvFT : FootprintVertices
            (F T) = FootprintVertices U), ∀ (hvFU : FootprintVertices (F U) = FootprintVertices
            T), ∀ (hvFR : FootprintVertices (F Rplus) = FootprintVertices Rminus), ∀ (heFT :
            FootprintEdges (F T) = FootprintEdges U), ∀ (heFU : FootprintEdges (F U) =
            FootprintEdges T), ∀ (heFR : FootprintEdges (F Rplus) = FootprintEdges Rminus),
        let Enegative : ExactTileInterfaceTriple U T Rminus := {
          point := Eimage.point
          otherAB := Eimage.otherAB
          otherBC := Eimage.otherBC
          otherCA := Eimage.otherCA
          pathAB := by simpa [hvFT, hvFU, heFT, heFU] using Eimage.pathAB
          pathBC := by simpa [hvFU, hvFR, heFU, heFR] using Eimage.pathBC
          pathCA := by simpa [hvFR, hvFT, heFR, heFT] using Eimage.pathCA
          unique_common := by
            intro z
            simpa [hvFT, hvFU, hvFR] using Eimage.unique_common z }
        SimpleGridPathBetween (FootprintVertices T ∩ FootprintVertices U) (FootprintEdges T ∩
            FootprintEdges U) Enegative.point Enegative.otherAB ) := by
  classical
  intro T U centerShift Rminus Rplus F Eimage hvFT hvFU hvFR heFT heFU heFR Enegative
  simpa [Set.inter_comm] using Enegative.pathAB

private theorem hposNe :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (Epositive :
            ExactTileInterfaceTriple T U Rplus), (SimpleGridPathBetween (FootprintVertices T ∩
            FootprintVertices U) (FootprintEdges T ∩ FootprintEdges U) Epositive.point
            Epositive.otherAB) → (Epositive.point ≠ Epositive.otherAB) ) := by
  classical
  intro T U Rplus Epositive hposPath
  rcases hposPath with ⟨path, hnd, hlen, hhead, hlast, _, _, _⟩
  intro heq
  have hpne : path ≠ [] := by intro hn; subst path; simp at hlen
  have hheadLast : path.head hpne = path.getLast hpne := by
    have hh := List.head?_eq_some_head hpne
    have hl := List.getLast?_eq_some_getLast hpne
    rw [hh] at hhead
    rw [hl] at hlast
    simp only [Option.some.injEq] at hhead hlast
    rw [hhead, hlast, heq]
  have hsingle : ∃ z, path = [z] :=
    (List.Nodup.head_eq_getLast_iff hpne hnd).mp hheadLast
  rcases hsingle with ⟨z, rfl⟩
  simp at hlen

private theorem hfixedUnique :
    (by
      classical
      exact
        ∀ (centerShift : GaussianInt),
          let f : GaussianInt → GaussianInt := fun z =>
            GaussianTranslation centerShift (GaussianQuarterTurn (GaussianQuarterTurn z))
          ∀ (x : GaussianInt), ∀ (y : GaussianInt), f x = x → f y = y → x = y
    ) := by
  classical
  intro centerShift f x y hx hy
  have hx' := by simpa [f, GaussianTranslation, GaussianQuarterTurn] using hx
  have hy' := by simpa [f, GaussianTranslation, GaussianQuarterTurn] using hy
  apply Zsqrtd.ext
  · have hxr := congrArg (fun z : GaussianInt => z.re) hx'
    have hyr := congrArg (fun z : GaussianInt => z.re) hy'
    simp only [Zsqrtd.re_add] at hxr hyr
    omega
  · have hxi := congrArg (fun z : GaussianInt => z.im) hx'
    have hyi := congrArg (fun z : GaussianInt => z.im) hy'
    simp only [Zsqrtd.im_add] at hxi hyi
    omega

private theorem hpointNotFixed :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (centerShift : GaussianInt), ∀ (Rminus :
            ProtoTile), ∀ (Rplus : ProtoTile),
        let F : ProtoTile → ProtoTile := fun X => TileTranslation (TileHalfTurn X) centerShift
        let f : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation centerShift (GaussianQuarterTurn (GaussianQuarterTurn z))
        ∀ (Epositive : ExactTileInterfaceTriple T U Rplus), ∀ (Eimage : ExactTileInterfaceTriple
            (F T) (F U) (F Rplus)), (Eimage.otherAB = f Epositive.otherAB) → (∀ (hvFT :
                FootprintVertices (F T) = FootprintVertices U), ∀ (hvFU : FootprintVertices (F U) =
            FootprintVertices T), ∀ (hvFR : FootprintVertices (F Rplus) = FootprintVertices
            Rminus), ∀ (heFT : FootprintEdges (F T) = FootprintEdges U), ∀ (heFU : FootprintEdges
            (F U) = FootprintEdges T), ∀ (heFR : FootprintEdges (F Rplus) = FootprintEdges Rminus),
        let Enegative : ExactTileInterfaceTriple U T Rminus := {
          point := Eimage.point
          otherAB := Eimage.otherAB
          otherBC := Eimage.otherBC
          otherCA := Eimage.otherCA
          pathAB := by simpa [hvFT, hvFU, heFT, heFU] using Eimage.pathAB
          pathBC := by simpa [hvFU, hvFR, heFU, heFR] using Eimage.pathBC
          pathCA := by simpa [hvFR, hvFT, heFR, heFT] using Eimage.pathCA
          unique_common := by
            intro z
            simpa [hvFT, hvFU, hvFR] using Eimage.unique_common z }
        (({Epositive.point, Epositive.otherAB} : Finset GaussianInt) = {Enegative.point,
            Enegative.otherAB}) →
            ((Epositive.point ≠ Epositive.otherAB) → ((∀ (z : GaussianInt), f (f z) = z) → ((∀ (x
                : GaussianInt), ∀ (y : GaussianInt), (f x = x) → ((f y = y) → (x = y))) → (f
            Epositive.point ≠ Epositive.point)))))) := by
  classical
  intro T U centerShift Rminus Rplus F f Epositive Eimage himageAB hvFT hvFU hvFR heFT heFU heFR
      Enegative hendpointPair hposNe hinvolutive hfixedUnique hfix
  have hfoMem : f Epositive.otherAB ∈ ({Epositive.point, Epositive.otherAB} : Finset GaussianInt)
      := by
    rw [hendpointPair]
    simp [Enegative, himageAB]
  rcases Finset.mem_insert.mp hfoMem with hfo | hfo
  · have heq : Epositive.otherAB = Epositive.point := by
      calc
        Epositive.otherAB = f (f Epositive.otherAB) := (hinvolutive _).symm
        _ = f Epositive.point := by rw [hfo, hfix]
        _ = Epositive.point := hfix
    exact hposNe heq.symm
  · have hfo' : f Epositive.otherAB = Epositive.otherAB := by simpa using hfo
    exact hposNe (hfixedUnique Epositive.point Epositive.otherAB hfix hfo')

private theorem hnegativePoint :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (centerShift : GaussianInt), ∀ (Rminus :
            ProtoTile), ∀ (Rplus : ProtoTile),
        let F : ProtoTile → ProtoTile := fun X => TileTranslation (TileHalfTurn X) centerShift
        let f : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation centerShift (GaussianQuarterTurn (GaussianQuarterTurn z))
        ∀ (Epositive : ExactTileInterfaceTriple T U Rplus), ∀ (Eimage : ExactTileInterfaceTriple
            (F T) (F U) (F Rplus)), (Eimage.point = f Epositive.point) → (∀ (hvFT :
                FootprintVertices (F T) = FootprintVertices U), ∀ (hvFU : FootprintVertices (F U) =
            FootprintVertices T), ∀ (hvFR : FootprintVertices (F Rplus) = FootprintVertices
            Rminus), ∀ (heFT : FootprintEdges (F T) = FootprintEdges U), ∀ (heFU : FootprintEdges
            (F U) = FootprintEdges T), ∀ (heFR : FootprintEdges (F Rplus) = FootprintEdges Rminus),
        let Enegative : ExactTileInterfaceTriple U T Rminus := {
          point := Eimage.point
          otherAB := Eimage.otherAB
          otherBC := Eimage.otherBC
          otherCA := Eimage.otherCA
          pathAB := by simpa [hvFT, hvFU, heFT, heFU] using Eimage.pathAB
          pathBC := by simpa [hvFU, hvFR, heFU, heFR] using Eimage.pathBC
          pathCA := by simpa [hvFR, hvFT, heFR, heFT] using Eimage.pathCA
          unique_common := by
            intro z
            simpa [hvFT, hvFU, hvFR] using Eimage.unique_common z }
        (({Epositive.point, Epositive.otherAB} : Finset GaussianInt) = {Enegative.point,
            Enegative.otherAB}) → ((f
            Epositive.point ≠ Epositive.point) → (Enegative.point = Epositive.otherAB)))) := by
  classical
  intro T U centerShift Rminus Rplus F f Epositive Eimage himagePoint hvFT hvFU hvFR heFT heFU
      heFR Enegative hendpointPair hpointNotFixed
  have hm : Enegative.point ∈ ({Epositive.point, Epositive.otherAB} : Finset GaussianInt) := by
    have hn : Enegative.point ∈ ({Enegative.point, Enegative.otherAB} : Finset GaussianInt) :=
        by simp
    rw [hendpointPair.symm] at hn
    exact hn
  rcases Finset.mem_insert.mp hm with hm | hm
  · have hfix : f Epositive.point = Epositive.point := by
      simpa [Enegative, himagePoint] using hm
    exact (hpointNotFixed hfix).elim
  · simpa using hm

private theorem hCpositive :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
          BandOrderedGeneralConfiguration q →
            ∀ (C : BandCircle), q (0 : Fin (4 : ℕ)) = C.1.1 → 0 < C.1.1.1
    ) := by
  classical
  intro q cfg C hC
  have hc := cfg.childLarge
  rw [hC] at hc
  omega

private theorem hwalkInOuter :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (tiles : List ProtoTile), ∀
            (reverseTiles : List ProtoTile), ∀ (functions : List PartialOdometer), ∀
            (reverseFunctions : List PartialOdometer), (∀ T_1 ∈ (List.drop (1 : ℕ)
            tiles).dropLast, ∃ (h_1 : PartialOdometer), (T_1, h_1) ∈ tiles.zip functions ∧
            AncestorOdometer D.1.1 C.1.1 T_1 T h_1 h) → ((∀ T ∈ (List.drop (1 : ℕ)
            reverseTiles).dropLast, ∃ (h : PartialOdometer), (T, h) ∈ reverseTiles.zip
            reverseFunctions ∧ AncestorOdometer D.1.1 C.1.1 T U h k) → (∀ (walk : List
            GaussianInt), (∀ x ∈ walk, (∃ a ∈ (List.drop (1 : ℕ) tiles).dropLast, x ∈
            FootprintVertices a) ∧ ∃ b ∈ (List.drop (1 : ℕ) reverseTiles).dropLast, x ∈
            FootprintVertices b) → (((h.domain : Set GaussianInt) = FootprintVertices T) →
            (((k.domain : Set GaussianInt) = FootprintVertices U) → (∀ x, x ∈ walk → x ∈
            FootprintVertices T ∩ FootprintVertices U))))) ) := by
  classical
  intro C D T U h k tiles reverseTiles functions reverseFunctions hrestrictionsForward
      hrestrictionsBackward walk hwalkVertices hdomOuterT hdomOuterU x hx
  obtain ⟨⟨A, hA, hxA⟩, ⟨B, hB, hxB⟩⟩ := hwalkVertices x hx
  obtain ⟨g, hzip, hAnc⟩ := hrestrictionsForward A hA
  obtain ⟨kA, hzipA, hAncA⟩ := hrestrictionsBackward B hB
  have hxg : x ∈ (g.domain : Set GaussianInt) :=
    (Set.ext_iff.mp hAnc.2.2.1 x).mpr hxA
  have hxk : x ∈ (kA.domain : Set GaussianInt) :=
    (Set.ext_iff.mp hAncA.2.2.1 x).mpr hxB
  have hxh : x ∈ (h.domain : Set GaussianInt) := hAnc.2.2.2.1 hxg
  have hxouterT : x ∈ FootprintVertices T := by
    rw [← hdomOuterT]
    exact hxh
  have hxouterK : x ∈ (k.domain : Set GaussianInt) := hAncA.2.2.2.1 hxk
  have hxouterU : x ∈ FootprintVertices U := by
    rw [← hdomOuterU]
    exact hxouterK
  exact ⟨hxouterT, hxouterU⟩

private theorem edgeAncestor :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ {A : ProtoTile}, ∀ {O : ProtoTile}, ∀
            {g : PartialOdometer}, ∀ {k₀ : PartialOdometer}, (AncestorOdometer D.1.1 C.1.1 A O g
            k₀) → (∀ (e : Finset GaussianInt), (e ∈ FootprintEdges A) → (e ∈ FootprintEdges O)) )
            := by
  classical
  intro C D A O g k₀ hAnc e he
  have hcells := P4158T1AncestorCells D.1.1 C.1.1 A O hAnc.2.1
  rcases he with ⟨cell, hcell, hshape⟩
  exact ⟨cell, hcells hcell, hshape⟩

private theorem hwalkOuterEdges :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (tiles : List ProtoTile), ∀
            (reverseTiles : List ProtoTile), ∀ (functions : List PartialOdometer), ∀
            (reverseFunctions : List PartialOdometer), (∀ T_1 ∈ (List.drop (1 : ℕ)
            tiles).dropLast, ∃ (h_1 : PartialOdometer), (T_1, h_1) ∈ tiles.zip functions ∧
            AncestorOdometer D.1.1 C.1.1 T_1 T h_1 h) → ((∀ T ∈ (List.drop (1 : ℕ)
            reverseTiles).dropLast, ∃ (h : PartialOdometer), (T, h) ∈ reverseTiles.zip
            reverseFunctions ∧ AncestorOdometer D.1.1 C.1.1 T U h k) → (∀ (walk : List
            GaussianInt), (∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (l₁ : List GaussianInt), ∀
            (l₂ : List GaussianInt), walk = l₁ ++ x :: y :: l₂ → (∃ a ∈ (List.drop (1 : ℕ)
            tiles).dropLast, {x, y} ∈ FootprintEdges a) ∧ ∃ b ∈ (List.drop (1 : ℕ)
            reverseTiles).dropLast, {x, y} ∈ FootprintEdges b) → ((∀ {A : ProtoTile}, ∀
            {O : ProtoTile}, ∀ {g : PartialOdometer}, ∀ {k₀ : PartialOdometer}, (AncestorOdometer
            D.1.1 C.1.1 A O g k₀) → (∀ (e : Finset GaussianInt), (e ∈ FootprintEdges A) → (e ∈
            FootprintEdges O))) → (∀ x y : GaussianInt, ∀ pre post : List GaussianInt, walk = pre
            ++ x :: y :: post → {x, y} ∈ FootprintEdges T ∩ FootprintEdges U)))) ) := by
  classical
  intro C D T U h k tiles reverseTiles functions reverseFunctions hrestrictionsForward
      hrestrictionsBackward walk hwalkEdges edgeAncestor x y pre post hsplit
  obtain ⟨⟨A, hA, heA⟩, ⟨B, hB, heB⟩⟩ := hwalkEdges x y pre post hsplit
  obtain ⟨g, hzip, hAnc⟩ := hrestrictionsForward A hA
  obtain ⟨kA, hzipA, hAncA⟩ := hrestrictionsBackward B hB
  exact ⟨edgeAncestor hAnc {x, y} heA, edgeAncestor hAncA {x, y} heB⟩

private theorem hwalkStart :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (centerShift : GaussianInt), ∀ (Rminus :
            ProtoTile), ∀ (Rplus : ProtoTile), ∀ (tiles : List ProtoTile), ∀ (reverseTiles : List
            ProtoTile),
        let F : ProtoTile → ProtoTile := fun X => TileTranslation (TileHalfTurn X) centerShift
        ∀ (Eimage : ExactTileInterfaceTriple (F T) (F U) (F Rplus)), ∀ (hvFT : FootprintVertices
            (F T) = FootprintVertices U), ∀ (hvFU : FootprintVertices (F U) = FootprintVertices
            T), ∀ (hvFR : FootprintVertices (F Rplus) = FootprintVertices Rminus), ∀ (heFT :
            FootprintEdges (F T) = FootprintEdges U), ∀ (heFU : FootprintEdges (F U) =
            FootprintEdges T), ∀ (heFR : FootprintEdges (F Rplus) = FootprintEdges Rminus),
        let Enegative : ExactTileInterfaceTriple U T Rminus := {
          point := Eimage.point
          otherAB := Eimage.otherAB
          otherBC := Eimage.otherBC
          otherCA := Eimage.otherCA
          pathAB := by simpa [hvFT, hvFU, heFT, heFU] using Eimage.pathAB
          pathBC := by simpa [hvFU, hvFR, heFU, heFR] using Eimage.pathBC
          pathCA := by simpa [hvFR, hvFT, heFR, heFT] using Eimage.pathCA
          unique_common := by
            intro z
            simpa [hvFT, hvFU, hvFR] using Eimage.unique_common z }
        ∀ (walk : List GaussianInt), (∃ (x : GaussianInt), walk.head? = some x ∧ x ∈
            FootprintVertices Rminus) → ((∃ (y : GaussianInt), walk.getLast? = some y ∧ y ∈
            FootprintVertices Rplus) → ((List.IsChain (fun (x y : GaussianInt) => y = x + (1 :
            GaussianInt) ∨ y = x - (1 : GaussianInt) ∨ y = x + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)
            ∨ y = x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) walk) → ((∀ x ∈ walk, (∃ a ∈ (List.drop
            (1 : ℕ) tiles).dropLast, x ∈ FootprintVertices a) ∧ ∃ b ∈ (List.drop (1 : ℕ)
            reverseTiles).dropLast, x ∈ FootprintVertices b) → ((∀ (x : GaussianInt), ∀ (y :
            GaussianInt), ∀ (l₁ : List GaussianInt), ∀ (l₂ : List GaussianInt), walk = l₁ ++ x ::
            y :: l₂ → (∃ a ∈ (List.drop (1 : ℕ) tiles).dropLast, {x, y} ∈ FootprintEdges a) ∧ ∃ b
            ∈ (List.drop (1 : ℕ) reverseTiles).dropLast, {x, y} ∈ FootprintEdges b) → ((∀ x, x ∈
            walk → x ∈ FootprintVertices T ∩ FootprintVertices U) → ((∀ x y : GaussianInt, ∀ pre
            post : List GaussianInt, walk = pre ++ x :: y :: post → {x, y} ∈ FootprintEdges T ∩
            FootprintEdges U) → (∃ z, walk.head? = some z ∧ z = Enegative.point))))))) ) := by
  classical
  intro T U centerShift Rminus Rplus tiles reverseTiles F Eimage hvFT hvFU hvFR heFT heFU heFR
      Enegative walk hwalkHead hwalkLast hwalkChain hwalkVertices hwalkEdges hwalkInOuter
      hwalkOuterEdges
  obtain ⟨z, hzhead, hzR⟩ := hwalkHead
  have hmem : z ∈ walk := by
    cases walk with
    | nil => simp at hzhead
    | cons a rest => simp only [List.mem_cons]; left; simpa using hzhead.symm
  have houter := hwalkInOuter z hmem
  have hcommon : z ∈ FootprintVertices U ∩ FootprintVertices T ∩
      FootprintVertices Rminus := ⟨⟨houter.2, houter.1⟩, hzR⟩
  have hpoint := (Enegative.unique_common z).mp hcommon
  exact ⟨z, hzhead, hpoint⟩

private theorem hwalkFinish :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (Epositive :
            ExactTileInterfaceTriple T U Rplus), ∀ (walk : List GaussianInt), (∃ (y :
            GaussianInt), walk.getLast? = some y ∧ y ∈ FootprintVertices Rplus) → ((∀ x, x ∈ walk
            → x ∈ FootprintVertices T ∩ FootprintVertices U) → (∃ z, walk.getLast? = some z ∧ z =
            Epositive.point)) ) := by
  classical
  intro T U Rplus Epositive walk hwalkLast hwalkInOuter
  obtain ⟨z, hzlast, hzR⟩ := hwalkLast
  have hmem : z ∈ walk := List.mem_of_mem_getLast? hzlast
  have houter := hwalkInOuter z hmem
  have hcommon : z ∈ FootprintVertices T ∩ FootprintVertices U ∩
      FootprintVertices Rplus := ⟨⟨houter.1, houter.2⟩, hzR⟩
  have hpoint := (Epositive.unique_common z).mp hcommon
  exact ⟨z, hzlast, hpoint⟩

private theorem hpathIndex :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
          ∀ (U : ProtoTile),
            ∀ (path : List GaussianInt),
              path.Nodup →
                (∀ (e : Finset GaussianInt),
                    e ∈ FootprintEdges T ∩ FootprintEdges U ↔
                      ∃ (a : GaussianInt) (b : GaussianInt) (l₁ : List GaussianInt) (l₂ :
                        List GaussianInt), path = l₁ ++ a :: b :: l₂ ∧ e = { a, b }) →
                  ∀ a b : GaussianInt,
                    { a, b } ∈ FootprintEdges T ∩ FootprintEdges U →
                      path.idxOf a + 1 = path.idxOf b ∨ path.idxOf b + 1 = path.idxOf a
    ) := by
  classical
  intro T U path hpathNodup hpathEdges a b hab
  rcases (hpathEdges {a, b}).mp hab with ⟨c, d, l, r, heq, hedge⟩
  have hnd := hpathNodup
  rw [heq, List.nodup_append] at hnd
  have hc : c ∉ l := by
    intro hc
    exact hnd.2.2 c hc c (by simp) rfl
  have hd : d ∉ l := by
    intro hd
    exact hnd.2.2 d hd d (by simp) rfl
  have hcd : c ≠ d := by
    have hcnot := (List.nodup_cons.mp hnd.2.1).1
    intro h
    exact hcnot (by simp [h])
  have hic : path.idxOf c = l.length := by
    simp [heq, List.idxOf_append, hc]
  have hid : path.idxOf d = l.length + 1 := by
    simp [heq, List.idxOf_append, hd, hcd, Nat.add_comm]
  have ha : a = c ∨ a = d := by
    have : a ∈ ({c, d} : Finset GaussianInt) := by rw [← hedge]; simp
    simpa using this
  have hb : b = c ∨ b = d := by
    have : b ∈ ({c, d} : Finset GaussianInt) := by rw [← hedge]; simp
    simpa using this
  have habne : a ≠ b := by
    intro h
    have hcmem : c ∈ ({a, b} : Finset GaussianInt) := by rw [hedge]; simp
    have hdmem : d ∈ ({a, b} : Finset GaussianInt) := by rw [hedge]; simp
    simp [h] at hcmem hdmem
    exact hcd (hcmem.trans hdmem.symm)
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact False.elim (habne rfl)
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)
  · exact False.elim (habne rfl)

private theorem hstartIndex :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (Epositive :
            ExactTileInterfaceTriple T U Rplus), ∀ (path : List GaussianInt), (path.Nodup) →
            ((path.getLast? = some Epositive.otherAB) → (path.idxOf Epositive.otherAB =
            path.length - 1)) ) := by
  classical
  intro T U Rplus Epositive path hpathNodup hpathLast
  have hpform : path.dropLast ++ [Epositive.otherAB] = path :=
    List.dropLast_append_getLast? Epositive.otherAB (by simp [hpathLast])
  have hyabsent : Epositive.otherAB ∉ path.dropLast := by
    have hnd := hpathNodup
    rw [← hpform, List.nodup_append] at hnd
    intro hm
    exact hnd.2.2 Epositive.otherAB hm Epositive.otherAB (by simp) rfl
  rw [← hpform, List.idxOf_append]
  simp [hyabsent]

private theorem hfinishIndex :
    (by
      classical
      exact
        ∀ (T U Rplus : ProtoTile)
          (Epositive : ExactTileInterfaceTriple T U Rplus)
          (path : List GaussianInt),
          (2 : ℕ) ≤ path.length →
            path.head? = some Epositive.point →
              List.idxOf Epositive.point path = (0 : ℕ)) := by
  classical
  intro T U Rplus Epositive path hpathLength hpathHead
  cases path with
  | nil => simp at hpathLength
  | cons a rest =>
    simp only [List.head?_cons, Option.some.injEq] at hpathHead
    simp [hpathHead]

private theorem hpathIndexEdge :
    (by
      classical
      exact
        ∀ (path : List GaussianInt), (path.Nodup) → (∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀
            (pre : List GaussianInt), ∀ (post : List GaussianInt), (path = pre ++ x :: y :: post)
            → (path.idxOf x = pre.length ∧ path.idxOf y = pre.length + 1)) ) := by
  classical
  intro path hpathNodup x y pre post hsplit
  have hnd := hpathNodup
  rw [hsplit, List.nodup_append] at hnd
  have hxnot : x ∉ pre := by
    intro hx
    exact hnd.2.2 x hx x (by simp) rfl
  have hxy : x ≠ y := by
    have hxnotTail : x ∉ y :: post := (List.nodup_cons.mp hnd.2.1).1
    simp only [List.mem_cons, not_or] at hxnotTail
    exact hxnotTail.1
  have hynot : y ∉ pre := by
    intro hy
    exact hnd.2.2 y hy y (by simp) rfl
  constructor
  · simp [hsplit, List.idxOf_append, hxnot]
  · simp [hsplit, List.idxOf_append, hynot, hxy, Nat.add_comm]

private theorem hwalkLastPos :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (Epositive :
            ExactTileInterfaceTriple T U Rplus), ∀ (walk : List GaussianInt), (∃ z, walk.getLast?
            = some z ∧ z = Epositive.point) → (walk.getLast? = some Epositive.point) ) := by
  classical
  intro T U Rplus Epositive walk hwalkFinish
  obtain ⟨z, hz, hzpoint⟩ := hwalkFinish
  rw [hzpoint] at hz
  exact hz

private theorem hwalkVertexPath :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (walk : List GaussianInt), (∀ x, x ∈ walk → x ∈
            FootprintVertices T ∩ FootprintVertices U) → (∀ (path : List GaussianInt),
            (FootprintVertices T ∩ FootprintVertices U = (↑path.toFinset : Set GaussianInt)) → (∀
            z ∈ walk, z ∈ path)) ) := by
  classical
  intro T U walk hwalkInOuter path hpathVertices z hz
  have hmem : z ∈ FootprintVertices T ∩ FootprintVertices U := hwalkInOuter z hz
  have hmem' : z ∈ (path.toFinset : Set GaussianInt) := by
    rw [← hpathVertices]
    exact hmem
  simpa using hmem'

private theorem hcovered :
    (by
      classical
      exact
                                      (
                                                      (
                                                                      (
                                                                                 (∀ (T :
            ProtoTile), ∀ (U : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (Epositive :
            ExactTileInterfaceTriple T U Rplus), ∀ (walk : List GaussianInt), (∀ x y :
            GaussianInt, ∀ pre post : List GaussianInt, walk = pre ++ x :: y :: post → {x, y} ∈
            FootprintEdges T ∩ FootprintEdges U) → (∀ (path : List GaussianInt), ((2 : ℕ) ≤
            path.length) → ((∀ a b : GaussianInt, {a, b} ∈ FootprintEdges T ∩ FootprintEdges U →
            path.idxOf a + 1 = path.idxOf b ∨ path.idxOf b + 1 = path.idxOf a) → ((∀
            {a : GaussianInt}, ∀ {b : GaussianInt}, (a ∈ path) → ((path.idxOf a = path.idxOf b) →
            (a = b))) → ((path.idxOf Epositive.otherAB = path.length - 1) → ((path.idxOf
            Epositive.point = 0) → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (pre : List
            GaussianInt), ∀ (post : List GaussianInt), (path = pre ++ x :: y :: post) →
            (path.idxOf x = pre.length ∧ path.idxOf y = pre.length + 1)) → ((walk.head? = some
            Epositive.otherAB) → ((walk.getLast? = some Epositive.point) → ((∀ z ∈ walk, z ∈
            path) → (∀ x y : GaussianInt, ∀ pre post : List GaussianInt, path = pre ++ x :: y ::
            post → ∃ l r : List GaussianInt, ∃ a b : GaussianInt, walk = l ++ a :: b :: r ∧ ({a,
            b} : Finset GaussianInt) = {x, y})))))))))))))) ) := by
  classical
  intro T U Rplus Epositive walk hwalkOuterEdges path hpathLength hpathIndex hpathIndexInjective
      hstartIndex hfinishIndex hpathIndexEdge hwalkHeadPos hwalkLastPos hwalkVertexPath u v pre
      post hsplit
  have hindices := hpathIndexEdge u v pre post hsplit
  have humem : u ∈ path := by rw [hsplit]; simp
  have hvmem : v ∈ path := by rw [hsplit]; simp
  by_contra hnot
  have hnoPair : ∀ a b : GaussianInt, ∀ l r : List GaussianInt,
      walk = l ++ a :: b :: r →
        ({a, b} : Finset GaussianInt) ≠ {u, v} := by
    intro a b l r hw hpair
    apply hnot
    exact ⟨l, r, a, b, hw, hpair⟩
  have hstartGreater : path.idxOf Epositive.otherAB > pre.length := by
    rw [hstartIndex]
    have hylt := List.idxOf_lt_length_of_mem hvmem
    rw [hindices.2] at hylt
    omega
  have propagate : ∀ (w : List GaussianInt),
      (∀ a b : GaussianInt, ∀ l r : List GaussianInt,
        w = l ++ a :: b :: r → {a, b} ∈ FootprintEdges T ∩ FootprintEdges U) →
      (∀ a b : GaussianInt, ∀ l r : List GaussianInt,
        w = l ++ a :: b :: r →
          ({a, b} : Finset GaussianInt) ≠ {u, v}) →
      (∀ z ∈ w, z ∈ path) →
      (∀ a ∈ w.head?, path.idxOf a > pre.length) →
      ∀ b ∈ w.getLast?, path.idxOf b > pre.length := by
    intro w
    induction w with
    | nil => simp
    | cons a w ih =>
      intro hw hno hv ha
      cases w with
      | nil => simpa using ha a (by simp)
      | cons b w =>
        have hab := hpathIndex a b (hw a b [] w rfl)
        have hia : path.idxOf a > pre.length := ha a (by simp)
        have hib : path.idxOf b > pre.length := by
          by_contra hle
          have hbmem : b ∈ path := hv b (by simp)
          have hbx : b = u := by
            apply hpathIndexInjective hbmem
            rw [hindices.1]
            omega
          have hay : a = v := by
            apply hpathIndexInjective (hv a (by simp))
            rw [hindices.2]
            omega
          subst a
          subst b
          have hpair : ({v, u} : Finset GaussianInt) = {u, v} := Finset.pair_comm _ _
          exact (hno v u [] w (by simp) hpair)
        have hw' : ∀ c d : GaussianInt, ∀ l r : List GaussianInt,
            b :: w = l ++ c :: d :: r →
              {c, d} ∈ FootprintEdges T ∩ FootprintEdges U := by
          intro c d l r h
          exact hw c d (a :: l) r (by simp [h, List.cons_append])
        have hno' : ∀ c d : GaussianInt, ∀ l r : List GaussianInt,
            b :: w = l ++ c :: d :: r →
              ({c, d} : Finset GaussianInt) ≠ {u, v} := by
          intro c d l r h
          exact hno c d (a :: l) r (by simp [h, List.cons_append])
        have hv' : ∀ z ∈ b :: w, z ∈ path := by
          intro z hz
          exact hv z (List.mem_cons_of_mem a hz)
        simpa using ih hw' hno' hv' (by simpa using hib)
  have hlastGreater := propagate walk
    (by
      intro a b l r hw
      exact hwalkOuterEdges a b l r hw)
    hnoPair hwalkVertexPath
    (by simpa [hwalkHeadPos] using hstartGreater)
    Epositive.point (by simp [hwalkLastPos])
  rw [hfinishIndex] at hlastGreater
  omega

private theorem hrestrictions :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (tiles : List ProtoTile), ∀
            (reverseTiles : List ProtoTile), ∀ (functions : List PartialOdometer), ∀
            (reverseFunctions : List PartialOdometer), (∀ T_1 ∈ (List.drop (1 : ℕ)
            tiles).dropLast, ∃ (h_1 : PartialOdometer), (T_1, h_1) ∈ tiles.zip functions ∧
            AncestorOdometer D.1.1 C.1.1 T_1 T h_1 h) → ((∀ T ∈ (List.drop (1 : ℕ)
            reverseTiles).dropLast, ∃ (h : PartialOdometer), (T, h) ∈ reverseTiles.zip
            reverseFunctions ∧ AncestorOdometer D.1.1 C.1.1 T U h k) → (∀ (walk : List
            GaussianInt), (∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (l₁ : List GaussianInt), ∀
            (l₂ : List GaussianInt), walk = l₁ ++ x :: y :: l₂ → (∃ a ∈ (List.drop (1 : ℕ)
            tiles).dropLast, {x, y} ∈ FootprintEdges a) ∧ ∃ b ∈ (List.drop (1 : ℕ)
            reverseTiles).dropLast, {x, y} ∈ FootprintEdges b) → (∀ (path : List GaussianInt), (∀
            x y : GaussianInt, ∀ pre post : List GaussianInt, path = pre ++ x :: y :: post → ∃ l
            r : List GaussianInt, ∃ a b : GaussianInt, walk = l ++ a :: b :: r ∧ ({a, b} : Finset
            GaussianInt) = {x, y}) → (∀ x y : GaussianInt, ∀ pre post : List GaussianInt, path =
            pre ++ x :: y :: post → ∃ (A B : ProtoTile) (g kA : PartialOdometer), (A, g) ∈
            tiles.zip functions ∧ (B, kA) ∈ reverseTiles.zip reverseFunctions ∧ {x, y} ∈
            FootprintEdges A ∩ FootprintEdges B ∧ AncestorOdometer D.1.1 C.1.1 A T g h ∧
            AncestorOdometer D.1.1 C.1.1 B U kA k)))) ) := by
  classical
  intro C D T U h k tiles reverseTiles functions reverseFunctions hrestrictionsForward
      hrestrictionsBackward walk hwalkEdges path hcovered x y pre post hsplit
  obtain ⟨l, r, a₁, b₁, hw, hpairs⟩ := hcovered x y pre post hsplit
  obtain ⟨⟨A, hA, heA⟩, ⟨B, hB, heB⟩⟩ := hwalkEdges a₁ b₁ l r hw
  obtain ⟨g, hzip, hAnc⟩ := hrestrictionsForward A hA
  obtain ⟨kA, hzipA, hAncA⟩ := hrestrictionsBackward B hB
  have hedgeA : {x, y} ∈ FootprintEdges A := by
    rw [← hpairs]
    exact heA
  have hedgeB : {x, y} ∈ FootprintEdges B := by
    rw [← hpairs]
    exact heB
  exact ⟨A, B, g, kA, hzip, hzipA, ⟨hedgeA, hedgeB⟩, hAnc, hAncA⟩

end UnitInterfaceGeometry

theorem P4261T2UnitInterface
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C D : BandCircle) (i : Fin 3)
    (hC : q 0 = C.1.1) (hD : q i.succ = D.1.1)
    (T U : ProtoTile) (h k : PartialOdometer)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (hsym : QuarterTurnSymmetric T)
    (hh : TileOdometer C.1.1 T h) (hk : TileOdometer C.1.1 U k)
    (hunit : D.1.1.1 = 1) (p r : Real × Real)
    (hp : PartialOdometerSlope h = some p) (hr : PartialOdometerSlope k = some r)
    (hc : TileCentroid U - TileCentroid T =
      GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)))
    (hs : r - p = GaussianRealPoint (BandVectors.2 (q i.succ) (q 0))) :
    Nonempty (P4261T2LiteralInterface D C T U h k) := by
-- BODY
  classical
  have hpositive : 0 < D.1.1.1 := by rw [hunit]; norm_num
  have hstrings := OpposingBoundaryOdometerStrings q cfg.proper C D i hC hD T U
    h k hh hk hpositive p r hp hr hc hs
  obtain ⟨orientation, centerShift, base, Rminus, Rplus, tiles, reverseTiles,
    functions, reverseFunctions, hminus, hplus, pminus, pplus, a, b, bminus,
    bplus, hboundary, hminusCells, hplusCells, hcellPairs, hreverse,
    hforwardRespect, hbackwardRespect, hheadForward, hlastForward,
    hheadBackward, hlastBackward, hOminus, hOplus, hsminus, hsplus,
    hsminusDiff, hsplusDiff, houterAffine, hplusAffine, hminusAffine,
    hrestrictionsForward, hrestrictionsBackward⟩ := hstrings
  rcases hboundary with ⟨q', hq', hq0, hqi, _, _, hstring, hcentMinus,
    hcentPlus⟩
  have hTband : BandPrototile C.1.1 T := TileOdometerBandPrototile _ _ _ hh
  have hUband : BandPrototile C.1.1 U := TileOdometerBandPrototile _ _ _ hk
  have hRminusBand : BandPrototile D.1.1 Rminus :=
    TileOdometerBandPrototile _ _ _ hOminus
  have hRplusBand : BandPrototile D.1.1 Rplus :=
    TileOdometerBandPrototile _ _ _ hOplus
  obtain ⟨_, _, _, _, hRminusNe⟩ :=
    P4250T1DefinedHalfIntegralSlope D.1.1 Rminus hminus
      (by rw [hunit]; norm_num) hOminus
  obtain ⟨_, _, _, _, hRplusNe⟩ :=
    P4250T1DefinedHalfIntegralSlope D.1.1 Rplus hplus
      (by rw [hunit]; norm_num) hOplus
  obtain ⟨_, _, _, _, hTNe⟩ := P4250T1DefinedHalfIntegralSlope C.1.1 T h (by
      have hcpos := cfg.childLarge
      rw [← hC]
      omega) hh
  obtain ⟨_, _, _, _, hUNe⟩ := P4250T1DefinedHalfIntegralSlope C.1.1 U k (by
      have hcpos := cfg.childLarge
      rw [← hC]
      omega) hk
  have hqi' : q' i.succ = q i.succ := hqi.trans hD.symm
  have hq0' : q' 0 = q 0 := hq0.trans hC.symm
  have hcentDiff := UnitInterfaceGeometry.hcentDiff q i T Rminus Rplus
      (UnitInterfaceGeometry.hcentMinusQ q i T Rminus q' hcentMinus hqi' hq0')
      (UnitInterfaceGeometry.hcentPlusQ q i T Rplus q' hcentPlus hqi' hq0')
  let w : GaussianInt := BandVectors.1 (q 0) (q i.succ)
  have hneq : (0 : Fin 4) ≠ i.succ := (Fin.succ_ne_zero i).symm
  have hvector := (VectorSquareProduct q cfg.proper.1 0 i.succ hneq).1
  have htangent := TangencyCoordinateIdentity q cfg.proper.1 0 i.succ hneq
  have hnormBig := UnitInterfaceGeometry.hnormBig q i (UnitInterfaceGeometry.hnormSq q i hvector
      htangent) (UnitInterfaceGeometry.hcurvSum q cfg D i hD hunit)
  have hrealPointInj := UnitInterfaceGeometry.hrealPointInj
  have hRminusNeRplus := UnitInterfaceGeometry.hRminusNeRplus q i Rminus Rplus hcentDiff hnormBig
      hrealPointInj
  have hnonadj := UnitInterfaceGeometry.hnonadj q D i hunit orientation Rminus Rplus hcentDiff
      hnormBig hrealPointInj (UnitInterfaceGeometry.hunitStepNorm orientation)
  have htriplePositive := UnitInterfaceGeometry.htriplePositive q cfg C D i hC hD T U cert hsym
      hc Rplus q' hq0 hqi hcentPlus hTband hUband hRplusBand hUNe
  let F : ProtoTile → ProtoTile := fun X => TileTranslation (TileHalfTurn X) centerShift
  have hFTCells : (F T).cells = U.cells := UnitInterfaceGeometry.hFTCells q C D i hC hD T U h
      hh hc centerShift Rminus Rplus a b hminusCells q' hq0 hqi hcentMinus hcentPlus
      hUband hRplusNe
  have hFUCells : (F U).cells = T.cells := UnitInterfaceGeometry.hFUCells T U centerShift
      (UnitInterfaceGeometry.hFCellsInvolutive centerShift)
      (UnitInterfaceGeometry.hFCellCongr centerShift) hFTCells
  have hFRplusCells : (F Rplus).cells = Rminus.cells := hplusCells
  let f : GaussianInt → GaussianInt := fun z =>
    GaussianTranslation centerShift (GaussianQuarterTurn (GaussianQuarterTurn z))
  have hpositiveImage : ∀ E : ExactTileInterfaceTriple T U Rplus,
      ∃ E' : ExactTileInterfaceTriple (F T) (F U) (F Rplus),
        E'.point = f E.point ∧ E'.otherAB = f E.otherAB  := UnitInterfaceGeometry.hpositiveImage
            T U centerShift Rplus
      (UnitInterfaceGeometry.hf centerShift) (UnitInterfaceGeometry.hstep centerShift)
      (UnitInterfaceGeometry.hvertices centerShift) (UnitInterfaceGeometry.hedges centerShift)
  obtain ⟨Epositive⟩ := htriplePositive
  obtain ⟨Eimage, himagePoint, himageAB⟩ := hpositiveImage Epositive
  have hFNeT : (F T).cells.Nonempty := by rw [hFTCells]; exact hUNe
  have hFNeU : (F U).cells.Nonempty := by rw [hFUCells]; exact hTNe
  have hFNeRminus : (F Rplus).cells.Nonempty := by rw [hFRplusCells]; exact hRminusNe
  have hvFT : FootprintVertices (F T) = FootprintVertices U := by
    simp [FootprintVertices, hFTCells, hUNe]
  have hvFU : FootprintVertices (F U) = FootprintVertices T := by
    simp [FootprintVertices, hFUCells, hTNe]
  have hvFR : FootprintVertices (F Rplus) = FootprintVertices Rminus := by
    simp [FootprintVertices, hFRplusCells, hRminusNe]
  have heFT : FootprintEdges (F T) = FootprintEdges U := by
    simp [FootprintEdges, hFTCells]
  have heFU : FootprintEdges (F U) = FootprintEdges T := by
    simp [FootprintEdges, hFUCells]
  have heFR : FootprintEdges (F Rplus) = FootprintEdges Rminus := by
    simp [FootprintEdges, hFRplusCells]
  let Enegative : ExactTileInterfaceTriple U T Rminus := {
    point := Eimage.point
    otherAB := Eimage.otherAB
    otherBC := Eimage.otherBC
    otherCA := Eimage.otherCA
    pathAB := by simpa [hvFT, hvFU, heFT, heFU] using Eimage.pathAB
    pathBC := by simpa [hvFU, hvFR, heFU, heFR] using Eimage.pathBC
    pathCA := by simpa [hvFR, hvFT, heFR, heFT] using Eimage.pathCA
    unique_common := by
      intro z
      simpa [hvFT, hvFU, hvFR] using Eimage.unique_common z }
  have hposPath : SimpleGridPathBetween
      (FootprintVertices T ∩ FootprintVertices U)
      (FootprintEdges T ∩ FootprintEdges U)
      Epositive.point Epositive.otherAB := Epositive.pathAB
  have hendpointPair := SimpleGridPathEndpointPairUnique hposPath (UnitInterfaceGeometry.hnegPath
      T U centerShift Rminus Rplus Eimage hvFT hvFU hvFR heFT heFU heFR)
  have hinvolutive (z : GaussianInt) : f (f z) = z := by
    apply Zsqrtd.ext <;> simp [f, GaussianTranslation, GaussianQuarterTurn]
  have hnegativePoint := UnitInterfaceGeometry.hnegativePoint T U centerShift Rminus Rplus
      Epositive Eimage himagePoint hvFT hvFU hvFR heFT heFU heFR hendpointPair
      (UnitInterfaceGeometry.hpointNotFixed T U centerShift Rminus Rplus Epositive Eimage
      himageAB hvFT hvFU hvFR heFT heFU heFR hendpointPair (UnitInterfaceGeometry.hposNe T U
      Rplus Epositive hposPath) hinvolutive (UnitInterfaceGeometry.hfixedUnique centerShift))
  obtain ⟨walk, hwalkHead, hwalkLast, hwalkChain, hwalkVertices,
    hwalkEdges⟩ := OpposingStringInterfacePath D orientation base Rminus Rplus
      hRminusNeRplus hnonadj tiles reverseTiles hstring hreverse
  have hCpositive := UnitInterfaceGeometry.hCpositive q cfg C hC
  have hdomOuterT : (h.domain : Set GaussianInt) = FootprintVertices T :=
    PositiveCurvatureTileOdometerDomain C.1.1 T h hCpositive hh
  have hdomOuterU : (k.domain : Set GaussianInt) = FootprintVertices U :=
    PositiveCurvatureTileOdometerDomain C.1.1 U k hCpositive hk
  have hwalkInOuter := UnitInterfaceGeometry.hwalkInOuter C D T U h k tiles reverseTiles
      functions reverseFunctions hrestrictionsForward hrestrictionsBackward walk hwalkVertices
      hdomOuterT hdomOuterU
  have hwalkOuterEdges := UnitInterfaceGeometry.hwalkOuterEdges C D T U h k tiles reverseTiles
      functions reverseFunctions hrestrictionsForward hrestrictionsBackward walk hwalkEdges
      (UnitInterfaceGeometry.edgeAncestor C D)
  have hwalkStart := UnitInterfaceGeometry.hwalkStart T U centerShift Rminus Rplus tiles
      reverseTiles Eimage hvFT hvFU hvFR heFT heFU heFR walk hwalkHead hwalkLast hwalkChain
      hwalkVertices hwalkEdges hwalkInOuter hwalkOuterEdges
  have hwalkFinish := UnitInterfaceGeometry.hwalkFinish T U Rplus Epositive walk hwalkLast
      hwalkInOuter
  obtain ⟨path, hpathNodup, hpathLength, hpathHead, hpathLast,
    hpathVertices, hpathStep, hpathEdges⟩ := Epositive.pathAB
  have hpathIndex := UnitInterfaceGeometry.hpathIndex T U path hpathNodup hpathEdges
  have hpathIndexInjective {a b : GaussianInt} (ha : a ∈ path)
      (hidx : path.idxOf a = path.idxOf b) : a = b :=
    (List.idxOf_inj ha).mp hidx
  have hstartIndex := UnitInterfaceGeometry.hstartIndex T U Rplus Epositive path hpathNodup
      hpathLast
  exact ⟨{
    orientation := orientation
    base := base
    minus := Rminus
    plus := Rplus
    tiles := tiles
    reverseTiles := reverseTiles
    functions := functions
    reverseFunctions := reverseFunctions
    hminus := hminus
    hplus := hplus
    path := path
    forward := hforwardRespect
    backward := hbackwardRespect
    head_forward := hheadForward
    last_forward := hlastForward
    head_backward := hheadBackward
    last_backward := hlastBackward
    nodup := hpathNodup
    length := hpathLength
    vertices := hpathVertices
    edges := hpathEdges
    restrictions := (UnitInterfaceGeometry.hrestrictions C D T U h k tiles reverseTiles functions
        reverseFunctions hrestrictionsForward hrestrictionsBackward walk hwalkEdges path
        (UnitInterfaceGeometry.hcovered T U Rplus Epositive walk hwalkOuterEdges path
        hpathLength hpathIndex hpathIndexInjective hstartIndex
        (UnitInterfaceGeometry.hfinishIndex T U Rplus Epositive path hpathLength
        hpathHead) (UnitInterfaceGeometry.hpathIndexEdge path hpathNodup)
        ((show
            walk.head? = some Epositive.otherAB
          from by
            classical
            obtain ⟨z, hz, hzpoint⟩ := hwalkStart
            rw [hzpoint, hnegativePoint] at hz
            exact hz))
        (UnitInterfaceGeometry.hwalkLastPos T U Rplus Epositive walk hwalkFinish)
        (UnitInterfaceGeometry.hwalkVertexPath T U walk hwalkInOuter path hpathVertices)))
  }⟩

end ApollonianSuperharmonic

end
