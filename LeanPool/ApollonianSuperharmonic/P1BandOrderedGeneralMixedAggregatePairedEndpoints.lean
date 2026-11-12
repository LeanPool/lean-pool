/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTriple
public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTripleSwapLast
public import LeanPool.ApollonianSuperharmonic.LatticeTileThreeDiskJunction
public import LeanPool.ApollonianSuperharmonic.P1BandOrderedGeneralMixedAggregateJunctionData
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathEndpointPairUnique

-- [TABLET NODE: P1BandOrderedGeneralMixedAggregatePairedEndpoints]

/-!
# P1BandOrderedGeneralMixedAggregatePairedEndpoints

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PairedEndpointGeometry

private theorem incoming :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), (
        let junctionData := fun (A B C : ProtoTile) => ∃ (AB : ProtoTile) (BC : ProtoTile) (CA :
            ProtoTile) (ABC : ProtoTile), LatticeTile A ∧ LatticeTile B ∧ LatticeTile C ∧
            LatticeTile AB ∧ LatticeTile BC ∧ LatticeTile CA ∧ LatticeTile ABC ∧ Disjoint A.cells
            B.cells ∧ Disjoint B.cells C.cells ∧ Disjoint C.cells A.cells ∧ (∀ (z : LatticeCell),
            z ∈ AB.cells ↔ z ∈ A.cells ∨ z ∈ B.cells) ∧ (∀ (z : LatticeCell), z ∈ BC.cells ↔ z ∈
            B.cells ∨ z ∈ C.cells) ∧ (∀ (z : LatticeCell), z ∈ CA.cells ↔ z ∈ C.cells ∨ z ∈
            A.cells) ∧ (∀ (z : LatticeCell), z ∈ ABC.cells ↔ z ∈ A.cells ∨ z ∈ B.cells ∨ z ∈
            C.cells) ∧ (FootprintEdges A ∩ FootprintEdges B).Nonempty ∧ (FootprintEdges B ∩
            FootprintEdges C).Nonempty ∧ (FootprintEdges C ∩ FootprintEdges A).Nonempty; (∀ (i :
            Fin (3 : ℕ)), ∀ (U : ProtoTile), BandPrototile (q i.succ) U → TileCentroid U -
            TileCentroid T = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ)))) + GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ)))
            → junctionData T (TileTranslation T (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))))
            U) ∧ ∀ (i : Fin (3 : ℕ)), ∀ (U : ProtoTile), ∀ (V : ProtoTile), BandPrototile (q
            i.succ) U → BandPrototile (q (i + (1 : Fin (3 : ℕ))).succ) V → TileCentroid U -
            TileCentroid T = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ)))) + GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ)))
            → TileCentroid V - TileCentroid T = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1
            (q (i + (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))) - GaussianRealPoint
            (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (i + (1 : Fin (3 : ℕ))).succ))) →
            junctionData T U V) → (∀ (i : Fin 3), ∀ (U : ProtoTile), (BandPrototile (q i.succ) U)
            → ((TileCentroid U - TileCentroid T = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
              GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)))) → (Nonempty
                  (ExactTileInterfaceTriple T (TileTranslation T (BandVectors.1 (q i.succ) (q
                  0))) U)))) ) := by
  classical
  intro q T junctions i U hU hcent
  obtain ⟨AB, BC, CA, ABC, hA, hB, hC, hAB, hBC, hCA, hABC,
    hdAB, hdBC, hdCA, huAB, huBC, huCA, huABC, heAB, heBC, heCA⟩ :=
    junctions.1 i U hU hcent
  exact LatticeTileThreeDiskJunction T
    (TileTranslation T (BandVectors.1 (q i.succ) (q 0))) U AB BC CA ABC
    hA hB hC hAB hBC hCA hABC hdAB hdBC hdCA
    huAB huBC huCA huABC heAB heBC heCA

private theorem evenT5 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), (
        let junctionData := fun (A B C : ProtoTile) => ∃ (AB : ProtoTile) (BC : ProtoTile) (CA :
            ProtoTile) (ABC : ProtoTile), LatticeTile A ∧ LatticeTile B ∧ LatticeTile C ∧
            LatticeTile AB ∧ LatticeTile BC ∧ LatticeTile CA ∧ LatticeTile ABC ∧ Disjoint A.cells
            B.cells ∧ Disjoint B.cells C.cells ∧ Disjoint C.cells A.cells ∧ (∀ (z : LatticeCell),
            z ∈ AB.cells ↔ z ∈ A.cells ∨ z ∈ B.cells) ∧ (∀ (z : LatticeCell), z ∈ BC.cells ↔ z ∈
            B.cells ∨ z ∈ C.cells) ∧ (∀ (z : LatticeCell), z ∈ CA.cells ↔ z ∈ C.cells ∨ z ∈
            A.cells) ∧ (∀ (z : LatticeCell), z ∈ ABC.cells ↔ z ∈ A.cells ∨ z ∈ B.cells ∨ z ∈
            C.cells) ∧ (FootprintEdges A ∩ FootprintEdges B).Nonempty ∧ (FootprintEdges B ∩
            FootprintEdges C).Nonempty ∧ (FootprintEdges C ∩ FootprintEdges A).Nonempty; (∀ (i :
            Fin (3 : ℕ)), ∀ (U : ProtoTile), BandPrototile (q i.succ) U → TileCentroid U -
            TileCentroid T = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ)))) + GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ)))
            → junctionData T (TileTranslation T (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))))
            U) ∧ ∀ (i : Fin (3 : ℕ)), ∀ (U : ProtoTile), ∀ (V : ProtoTile), BandPrototile (q
            i.succ) U → BandPrototile (q (i + (1 : Fin (3 : ℕ))).succ) V → TileCentroid U -
            TileCentroid T = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ)))) + GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ)))
            → TileCentroid V - TileCentroid T = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1
            (q (i + (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))) - GaussianRealPoint
            (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (i + (1 : Fin (3 : ℕ))).succ))) →
            junctionData T U V) → (∀ (i : Fin 3), ∀ (U : ProtoTile), ∀ (V : ProtoTile),
            (BandPrototile (q i.succ) U) → ((BandPrototile (q ((i + 1).succ)) V) → ((TileCentroid
            U - TileCentroid T = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
              GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)))) → ((TileCentroid V -
                  TileCentroid T = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q ((i + 1).succ)) (q 0)) -
              GaussianRealPoint (BandVectors.1 (q 0) (q ((i + 1).succ))))) → (Nonempty
                  (ExactTileInterfaceTriple T U V)))))) ) := by
  classical
  intro q T junctions i U V hU hV hcentU hcentV
  obtain ⟨AB, BC, CA, ABC, hA, hB, hC, hAB, hBC, hCA, hABC,
    hdAB, hdBC, hdCA, huAB, huBC, huCA, huABC, heAB, heBC, heCA⟩ :=
    junctions.2 i U V hU hV hcentU hcentV
  exact LatticeTileThreeDiskJunction T U V AB BC CA ABC
    hA hB hC hAB hBC hCA hABC hdAB hdBC hdCA
    huAB huBC huCA huABC heAB heBC heCA

private theorem endpointRelations :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (R : ProtoTile), ∀ (L :
            ProtoTile), ∀ (rightData : ExactTileInterfaceTriple T R U), ∀ (incomingData :
            ExactTileInterfaceTriple T L U), ∀ (t5Data : ExactTileInterfaceTriple T U V),
            (rightData.point = t5Data.point) → ((incomingData.point ≠ t5Data.point) →
            (incomingData.otherCA = t5Data.point ∧ rightData.otherCA = incomingData.point ∧
            t5Data.otherAB = incomingData.point)) ) := by
  classical
  intro T U V R L rightData incomingData t5Data hpoint hne
  have endpoint_ne {W : Set GaussianInt} {E : Set (Finset GaussianInt)}
      {x y : GaussianInt} (h : SimpleGridPathBetween W E x y) : x ≠ y := by
    rcases h with ⟨p, hn, hl, hh, ht, _⟩
    intro heq
    have hp : p ≠ [] := by
      intro hp
      subst p
      simp at hl
    have hx : p.head hp = x := by
      simpa [List.head?_eq_some_head hp] using hh
    have hy : p.getLast hp = y := by
      simpa [List.getLast?_eq_some_getLast hp] using ht
    obtain ⟨z, hz⟩ := (List.Nodup.head_eq_getLast_iff hp hn).mp
      (hx.trans (heq.trans hy.symm))
    subst p
    simp at hl
  have ht5 : SimpleGridPathBetween
      (FootprintVertices U ∩ FootprintVertices T)
      (FootprintEdges U ∩ FootprintEdges T) t5Data.point t5Data.otherAB := by
    simpa [Set.inter_comm] using t5Data.pathAB
  have hLI := SimpleGridPathEndpointPairUnique incomingData.pathCA ht5
  have hRI := SimpleGridPathEndpointPairUnique rightData.pathCA incomingData.pathCA
  have hotherL : incomingData.otherCA = t5Data.point := by
    have hm : t5Data.point ∈
        ({incomingData.point, incomingData.otherCA} : Finset GaussianInt) := by
      rw [hLI]
      simp
    rcases (show t5Data.point = incomingData.point ∨
        t5Data.point = incomingData.otherCA from by simpa using hm) with h | h
    · exact (hne h.symm).elim
    · exact h.symm
  have hotherR : rightData.otherCA = incomingData.point := by
    have hm : incomingData.point ∈
        ({rightData.point, rightData.otherCA} : Finset GaussianInt) := by
      rw [hRI]
      simp
    rcases (show incomingData.point = rightData.point ∨
        incomingData.point = rightData.otherCA from by simpa using hm) with h | h
    · exact (hne (h.trans hpoint)).elim
    · exact h.symm
  have hother5 : t5Data.otherAB = incomingData.point := by
    have hm : t5Data.otherAB ∈
        ({incomingData.point, incomingData.otherCA} : Finset GaussianInt) := by
      rw [hLI]
      simp
    rcases (show t5Data.otherAB = incomingData.point ∨
        t5Data.otherAB = incomingData.otherCA from by simpa using hm) with h | h
    · exact h
    · exact (endpoint_ne ht5 (hotherL.symm.trans h.symm)).elim
  exact ⟨hotherL, hotherR, hother5⟩

private theorem literalData :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let pLit (i : Fin 3) := TileTranslation (cert.P i true)
          (if i = 0 then -cert.v else if i = 1 then cert.u + cert.v else -cert.u)
        let qLit (i : Fin 3) := TileTranslation (cert.P (i + 1) true)
          (if i = 0 then cert.u else if i = 1 then cert.v else -cert.u - cert.v)
        ∀ (i : Fin 3), BandPrototile (q i.succ) (pLit i) ∧ BandPrototile (q ((i + 1).succ)) (qLit
            i) ∧ TileCentroid (pLit i) - TileCentroid T = (1 / 2 : Real) • (GaussianRealPoint
            (BandVectors.1 (q i.succ) (q 0)) + GaussianRealPoint (BandVectors.1 (q 0) (q
            i.succ))) ∧ TileCentroid (qLit i) - TileCentroid T = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q ((i + 1).succ)) (q 0)) - GaussianRealPoint
            (BandVectors.1 (q 0) (q ((i + 1).succ)))) ) := by
  classical
  intro q cfg C₀ T cert pLit qLit i
  have laws := VectorRecursionLaws q cfg.proper.1
  have laws1 := VectorRecursionLaws _ (SemiProperQuadruple.rotate cfg.proper.1)
  have laws2 := VectorRecursionLaws _
    (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate cfg.proper.1))
  have superbasis := laws.1
  have w1 := laws.2.2.1
  have w2 := laws1.2.2.1
  have w3 := laws2.2.2.1
  dsimp at w2 w3
  have flip := laws.2.2.2.2 cfg.proper
  dsimp only [pLit, qLit]
  refine ⟨BandPrototileTranslation _ _ _ (cert.outer_occurrence i true).1,
    BandPrototileTranslation _ _ _ (cert.outer_occurrence (i + 1) true).1, ?_, ?_⟩
  all_goals
    rw [(TileTranslationFormulas _ _).2.2.2.2.1]
    have h0 := (cert.outer_occurrence 0 true).2.2
    have h1 := (cert.outer_occurrence 1 true).2.2
    have h2 := (cert.outer_occurrence 2 true).2.2
    have f0 := (flip 0).1
    have f1 := (flip 1).1
    have f2 := (flip 2).1
    fin_cases i
    all_goals
      simp only [Fin.reduceAdd, Fin.reduceSucc, ↓reduceIte, one_smul] at h0 h1 h2
      simp only [Fin.reduceSucc] at f0 f1 f2
      simp only [Fin.mk_one, Fin.isValue, Fin.reduceAdd, Int.reduceNeg, one_ne_zero,
          ↓reduceIte, cert.period_v, f1, w2, Zsqrtd.re_mul, Zsqrtd.re_sub, zero_mul, mul_one,
          neg_mul, one_mul, zero_add, sub_neg_eq_add, Zsqrtd.im_sub, Zsqrtd.im_mul, neg_sub,
          Int.cast_sub, GaussianInt.intCast_re, GaussianInt.intCast_im, Int.cast_add, one_div,
          Fin.reduceSucc, w3, f2, cert.period_u, f0, w1, Zsqrtd.re_add, Zsqrtd.im_add,
          Fin.succ_one_eq_two, smul_add, Fin.reduceFinMk, Fin.reduceEq, Zsqrtd.re_neg,
          Zsqrtd.im_neg, neg_add_rev, Int.cast_neg, Fin.succ_zero_eq_one, Fin.zero_eta]
      have re := congrArg (fun z : GaussianInt => z.re) superbasis
      have im := congrArg (fun z : GaussianInt => z.im) superbasis
      have r0 := congrArg Prod.fst h0
      have s0 := congrArg Prod.snd h0
      have r1 := congrArg Prod.fst h1
      have s1 := congrArg Prod.snd h1
      have r2 := congrArg Prod.fst h2
      have s2 := congrArg Prod.snd h2
      simp only [Fin.isValue, Prod.fst_sub, one_div, GaussianRealPoint, Int.reduceNeg,
          GaussianInt.intCast_re, GaussianInt.intCast_im, Prod.mk_sub_mk, sub_neg_eq_add,
          Prod.smul_mk, smul_eq_mul, Prod.snd_sub, Zsqrtd.re_sub, Zsqrtd.re_mul, zero_mul,
          mul_one, neg_mul, one_mul, zero_add, Int.cast_add, Zsqrtd.im_sub, Zsqrtd.im_mul,
          Int.cast_sub, neg_sub, Prod.mk_add_mk] at r0 s0 r1 s1 r2 s2 ⊢
      simp only [Int.reduceNeg, Fin.isValue, Zsqrtd.re_add, Zsqrtd.re_zero, Zsqrtd.im_add,
          Zsqrtd.im_zero] at re im
      have rr : ((BandVectors.1 (q 3) (q 2)).re : Real) +
          ((BandVectors.1 (q 1) (q 3)).re : Real) +
          ((BandVectors.1 (q 2) (q 1)).re : Real) = 0 := by exact_mod_cast re
      have ri : ((BandVectors.1 (q 3) (q 2)).im : Real) +
          ((BandVectors.1 (q 1) (q 3)).im : Real) +
          ((BandVectors.1 (q 2) (q 1)).im : Real) = 0 := by exact_mod_cast im
      simp at r0 s0 r1 s1 r2 s2 rr ri
      ext <;> simp <;> linarith only [r0, s0, r1, s1, r2, s2, rr, ri]

private theorem translated_sym :
    (by
      classical
      exact
        ∀ (Y : ProtoTile), ∀ (a : GaussianInt), (QuarterTurnSymmetric Y) → (QuarterTurnSymmetric
            (TileTranslation Y a)) ) := by
  classical
  intro Y a hY p
  rw [(TileTranslationFormulas Y a).2.2.2.1,
    (TileTranslationFormulas Y a).2.2.2.2.1]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨((TileCentroid Y).1 - (z.2 - (TileCentroid Y).2),
      (TileCentroid Y).2 + (z.1 - (TileCentroid Y).1)), (hY z).mp hz, ?_⟩
    ext <;> dsimp <;> ring
  · rintro ⟨z, hz, heq⟩
    let z' : Real × Real := (p.1 - (a.re : Int), p.2 - (a.im : Int))
    have hturn : ((TileCentroid Y).1 - (z'.2 - (TileCentroid Y).2),
        (TileCentroid Y).2 + (z'.1 - (TileCentroid Y).1)) = z := by
      have hre := congrArg Prod.fst heq
      have him := congrArg Prod.snd heq
      ext <;> dsimp [z'] at hre him ⊢ <;> linarith
    refine ⟨z', (hY z').mpr ?_, ?_⟩
    · change ((TileCentroid Y).1 - (z'.2 - (TileCentroid Y).2),
        (TileCentroid Y).2 + (z'.1 - (TileCentroid Y).1)) ∈ TileRealization Y
      rw [hturn]
      exact hz
    · ext <;> dsimp [z'] <;> ring

private theorem centeredProxy :
    (by
      classical
      exact
        (∀ (Y : ProtoTile), ∀ (a : GaussianInt), (QuarterTurnSymmetric Y) → (QuarterTurnSymmetric
            (TileTranslation Y a))) → (∀ (C : CircleCoordinates), ∀ (Y : ProtoTile), ∀ (g :
            GaussianInt), (BandPrototile C Y) → ((QuarterTurnSymmetric Y) → (∃ Ysharp :
            ProtoTile, BandPrototile C Ysharp ∧ QuarterTurnSymmetric Ysharp ∧ (TileTranslation
            (TileQuarterTurn Y) g).cells = Ysharp.cells ∧ ((TileTranslation (TileQuarterTurn Y)
            g).cells = ∅ → (TileTranslation (TileQuarterTurn Y) g).anchor = Ysharp.anchor) ∧
            TileCentroid Ysharp = (-((TileCentroid Y).2) + (g.re : Int), (TileCentroid Y).1 +
            (g.im : Int))))) ) := by
  classical
  intro translated_sym C Y g hY hYsym
  obtain ⟨d, hd, hcells, hanchor, hvertices, hcent⟩ :=
    QuarterTurnSymmetricCenteredTransport Y hYsym
  let Ysharp := TileTranslation Y (g - d)
  have hcomp : TileTranslation (TileTranslation (TileQuarterTurn Y) d) (g - d) =
      TileTranslation (TileQuarterTurn Y) g := by
    simp only [TileTranslation, ProtoTile.mk.injEq]
    constructor
    · rw [Finset.image_image]
      congr 1
      funext z
      dsimp [Function.comp_def, GaussianTranslation]
      abel
    · dsimp [GaussianTranslation]
      abel
  have hc : (TileTranslation (TileQuarterTurn Y) g).cells = Ysharp.cells := by
    rw [← hcomp]
    change _ = Y.cells.image (GaussianTranslation (g - d))
    rw [(TileTranslationFormulas _ _).1, hcells]
  have ha : (TileTranslation (TileQuarterTurn Y) g).cells = ∅ →
      (TileTranslation (TileQuarterTurn Y) g).anchor = Ysharp.anchor := by
    intro he
    have heY : Y.cells = ∅ := by
      rw [hc] at he
      exact (TileTranslationFormulas Y (g - d)).2.2.1.mp he
    rw [← hcomp]
    change GaussianTranslation (g - d)
      (TileTranslation (TileQuarterTurn Y) d).anchor =
        GaussianTranslation (g - d) Y.anchor
    rw [hanchor heY]
  have hobs := ProtoTileObservableExtensionality _ Ysharp hc ha
  refine ⟨Ysharp, BandPrototileTranslation C Y (g - d) hY,
    translated_sym Y (g - d) hYsym, hc, ha, ?_⟩
  rw [← hobs.2.2.2.2, (TileTranslationFormulas _ g).2.2.2.2.1,
    (TileQuarterTurnFormulas Y).2.2.2.2.1]

private theorem halfTurnProxy :
    (by
      classical
      exact
        (∀ (C : CircleCoordinates), ∀ (Y : ProtoTile), ∀ (g : GaussianInt), (BandPrototile C Y) →
            ((QuarterTurnSymmetric Y) → (∃ Ysharp : ProtoTile, BandPrototile C Ysharp ∧
            QuarterTurnSymmetric Ysharp ∧ (TileTranslation (TileQuarterTurn Y) g).cells =
            Ysharp.cells ∧ ((TileTranslation (TileQuarterTurn Y) g).cells = ∅ → (TileTranslation
            (TileQuarterTurn Y) g).anchor = Ysharp.anchor) ∧ TileCentroid Ysharp =
            (-((TileCentroid Y).2) + (g.re : Int), (TileCentroid Y).1 + (g.im : Int))))) → (∀ (C
            : CircleCoordinates), ∀ (Y : ProtoTile), ∀ (g : GaussianInt), (BandPrototile C Y) →
            ((QuarterTurnSymmetric Y) → (∃ Zsharp : ProtoTile, BandPrototile C Zsharp ∧
            QuarterTurnSymmetric Zsharp ∧ (TileTranslation (TileQuarterTurn (TileTranslation
            (TileQuarterTurn Y) g)) g).cells = Zsharp.cells ∧ ((TileTranslation (TileQuarterTurn
            (TileTranslation (TileQuarterTurn Y) g)) g).cells = ∅ → (TileTranslation
            (TileQuarterTurn (TileTranslation (TileQuarterTurn Y) g)) g).anchor = Zsharp.anchor)
            ∧ TileCentroid Zsharp = (-((TileCentroid Y).1) + (g.re : Int) - (g.im : Int),
            -((TileCentroid Y).2) + (g.re : Int) + (g.im : Int))))) ) := by
  classical
  intro centeredProxy C Y g hY hYsym
  let R (W : ProtoTile) := TileTranslation (TileQuarterTurn W) g
  obtain ⟨Ysharp, hband1, hsym1, hc1, ha1, hcent1⟩ :=
    centeredProxy C Y g hY hYsym
  obtain ⟨Zsharp, hband2, hsym2, hc2, ha2, hcent2⟩ :=
    centeredProxy C Ysharp g hband1 hsym1
  have hcMap : (R (R Y)).cells = (R Ysharp).cells := by
    change (TileTranslation (TileQuarterTurn (R Y)) g).cells = _
    rw [(TileTranslationFormulas _ _).1, (TileQuarterTurnFormulas _).1]
    change ((R Y).cells.image _).image _ = _
    rw [hc1]
    rfl
  have haMap : (R (R Y)).cells = ∅ → (R (R Y)).anchor = (R Ysharp).anchor := by
    intro he
    have he' : (R Y).cells = ∅ :=
      (TileQuarterTurnFormulas (R Y)).2.2.1.mp
        ((TileTranslationFormulas _ _).2.2.1.mp he)
    change GaussianTranslation g (GaussianQuarterTurn (R Y).anchor) =
      GaussianTranslation g (GaussianQuarterTurn Ysharp.anchor)
    rw [ha1 he']
  have hc : (R (R Y)).cells = Zsharp.cells := hcMap.trans hc2
  have ha : (R (R Y)).cells = ∅ → (R (R Y)).anchor = Zsharp.anchor := by
    intro he
    exact (haMap he).trans (ha2 (hcMap ▸ he))
  refine ⟨Zsharp, hband2, hsym2, hc, ha, ?_⟩
  rw [hcent2, hcent1]
  ext <;> dsimp; ring

private theorem period3 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), BandVectors.1 (q 0) (q 3) = -cert.u - cert.v ) := by
  classical
  intro q cfg C₀ T cert
  have laws := VectorRecursionLaws q cfg.proper.1
  have laws1 := VectorRecursionLaws _ (SemiProperQuadruple.rotate cfg.proper.1)
  have laws2 := VectorRecursionLaws _
    (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate cfg.proper.1))
  have w1 := laws.2.2.1
  have w2 := laws1.2.2.1
  have w3 := laws2.2.2.1
  dsimp at w2 w3
  have f0 := (laws.2.2.2.2 cfg.proper 0).1
  have f1 := (laws.2.2.2.2 cfg.proper 1).1
  have f2 := (laws.2.2.2.2 cfg.proper 2).1
  simp only [Fin.reduceSucc] at f0 f1 f2
  rw [cert.period_u, cert.period_v, f0, f1, f2, w1, w2, w3]
  have h := laws.1
  linear_combination ((⟨0, 1⟩ : GaussianInt) - (⟨0, 1⟩ : GaussianInt) ^ 2) * h

private theorem markedMembership :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let pLit (i : Fin 3) := TileTranslation (cert.P i true)
          (if i = 0 then -cert.v else if i = 1 then cert.u + cert.v else -cert.u)
        let qLit (i : Fin 3) := TileTranslation (cert.P (i + 1) true)
          (if i = 0 then cert.u else if i = 1 then cert.v else -cert.u - cert.v)
        let markedPoint (i : Fin 3) := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm
            ⟨.J5, if i = 2 then -1 else 0, if i = 1 then 0 else -1⟩)
        (BandVectors.1 (q 0) (q 3) = -cert.u - cert.v) → (∀ (i : Fin 3), markedPoint i ∈
            FootprintVertices T ∩ FootprintVertices (pLit i) ∩ FootprintVertices (qLit i) ∧
            markedPoint i ∈ FootprintVertices (TileTranslation T (BandVectors.1 (q 0) (q
            i.succ)))) ) := by
  classical
  intro q cfg C₀ T cert pLit qLit markedPoint period3 i
  have trzero (Y : ProtoTile) : TileTranslation Y 0 = Y := by
    have hfun : GaussianTranslation 0 = id := by
      funext z
      simp [GaussianTranslation]
    cases Y
    simp [TileTranslation, hfun]
  have trsubset (Y : ProtoTile) (a : GaussianInt)
      (h : FootprintVertices Y ⊆ FootprintVertices T) :
      FootprintVertices (TileTranslation Y a) ⊆ FootprintVertices (TileTranslation T a) := by
    rw [(TileTranslationFormulas Y a).2.2.2.2.2.1,
      (TileTranslationFormulas T a).2.2.2.2.2.1]
    exact Set.image_mono h
  have rho_mem (f : PeriodicSubtileFaceIndex) (k : Fin 3) :
      cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm f) ∈
        FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v
          (SixSubtileFaceVertices f k)) := by
    have h := cert.unmodified.core.rho_common (cert.unmodified.faceEquiv.symm f) k
    rw [cert.unmodified.face_vertices, cert.unmodified.faceEquiv.apply_symm_apply,
      cert.unmodified.tile_eq] at h
    exact h
  let f : PeriodicSubtileFaceIndex :=
    ⟨.J5, if i = 2 then -1 else 0, if i = 1 then 0 else -1⟩
  have h0 := rho_mem f 0
  have h1 := rho_mem f 1
  have h2 := rho_mem f 2
  fin_cases i
  all_goals
    simp only [SubtileOccurrenceInterpretation, SixSubtileFaceVertices, Fin.mk_one,
        Fin.isValue, Fin.reduceEq, ↓reduceIte, zero_add, Matrix.cons_val_zero, Int.cast_zero,
        zero_mul, add_zero, trzero, Matrix.cons_val_one, Int.cast_one, one_mul,
        Matrix.cons_val, one_ne_zero, Fin.reduceAdd, Int.reduceNeg, Set.mem_inter_iff,
        Fin.succ_one_eq_two, f, pLit, qLit, markedPoint, Fin.reduceFinMk, neg_add_cancel,
        Int.cast_neg, neg_mul, Fin.reduceSucc, Fin.zero_eta, zero_ne_one,
        Fin.succ_zero_eq_one] at h0 h1 h2 ⊢
  · exact ⟨⟨⟨(cert.outer_occurrence 2 true).2.1 h2, h0⟩, h1⟩,
      (by
        rw [← cert.period_u]
        exact trsubset _ cert.u (cert.outer_occurrence 1 true).2.1 h1)⟩
  · exact ⟨⟨⟨(cert.outer_occurrence 0 true).2.1 h0, h1⟩, h2⟩,
      (by
        rw [← cert.period_v]
        exact trsubset _ cert.v (cert.outer_occurrence 2 true).2.1 h2)⟩
  · have h0' := h0
    simp only [← sub_eq_add_neg] at h0'
    exact ⟨⟨⟨(cert.outer_occurrence 1 true).2.1 h1, h2⟩, h0'⟩,
      (by
        rw [period3]
        exact trsubset _ (-cert.u - cert.v) (cert.outer_occurrence 0 true).2.1 h0')⟩

private theorem unrotated :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (∀ (i : Fin 3), ∀ (U : ProtoTile), (BandPrototile (q i.succ) U) →
            ((TileCentroid U - TileCentroid T = (1 / 2 : Real) • (GaussianRealPoint
            (BandVectors.1 (q i.succ) (q 0)) + GaussianRealPoint (BandVectors.1 (q 0) (q
            i.succ)))) → (Nonempty (ExactTileInterfaceTriple T (TileTranslation T (BandVectors.1
            (q i.succ) (q 0))) U)))) → ((∀ (i : Fin 3), ∀ (U : ProtoTile), ∀ (V : ProtoTile),
            (BandPrototile (q i.succ) U) → ((BandPrototile (q ((i + 1).succ)) V) → ((TileCentroid
            U - TileCentroid T = (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q
            0)) + GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)))) → ((TileCentroid V -
            TileCentroid T = (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (q ((i +
            1).succ)) (q 0)) - GaussianRealPoint (BandVectors.1 (q 0) (q ((i + 1).succ))))) →
            (Nonempty (ExactTileInterfaceTriple T U V)))))) → (
        let pLit (i : Fin 3) := TileTranslation (cert.P i true)
          (if i = 0 then -cert.v else if i = 1 then cert.u + cert.v else -cert.u)
        let qLit (i : Fin 3) := TileTranslation (cert.P (i + 1) true)
          (if i = 0 then cert.u else if i = 1 then cert.v else -cert.u - cert.v)
        let markedPoint (i : Fin 3) := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm
            ⟨.J5, if i = 2 then -1 else 0, if i = 1 then 0 else -1⟩)
        (∀ (i : Fin 3), BandPrototile (q i.succ) (pLit i) ∧ BandPrototile (q ((i + 1).succ))
            (qLit i) ∧ TileCentroid (pLit i) - TileCentroid T = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) + GaussianRealPoint
            (BandVectors.1 (q 0) (q i.succ))) ∧ TileCentroid (qLit i) - TileCentroid T = (1 / 2 :
            Real) • (GaussianRealPoint (BandVectors.1 (q ((i + 1).succ)) (q 0)) -
            GaussianRealPoint (BandVectors.1 (q 0) (q ((i + 1).succ))))) → ((∀ (i : Fin 3),
            markedPoint i ∈ FootprintVertices T ∩ FootprintVertices (pLit i) ∩ FootprintVertices
            (qLit i) ∧ markedPoint i ∈ FootprintVertices (TileTranslation T (BandVectors.1 (q 0)
            (q i.succ)))) → (∀ (i : Fin 3), ∀ (U : ProtoTile), ∀ (V : ProtoTile), (BandPrototile
            (q i.succ) U) → ((BandPrototile (q ((i + 1).succ)) V) → ((TileCentroid U -
            TileCentroid T = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
              GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)))) → ((TileCentroid V -
                  TileCentroid T = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q ((i + 1).succ)) (q 0)) -
              GaussianRealPoint (BandVectors.1 (q 0) (q ((i + 1).succ))))) → (∃ _ :
                  ExactTileInterfaceTriple T (TileTranslation T (BandVectors.1 (q i.succ) (q 0)))
                  U, ∃ t5Data : ExactTileInterfaceTriple T U V, t5Data.point = markedPoint i ∧ (∀
                  rightData : ExactTileInterfaceTriple T (TileTranslation T (BandVectors.1 (q 0)
                  (q i.succ))) U, rightData.point = t5Data.point))))))))) ) := by
  classical
  intro q cfg C₀ T cert incoming evenT5 pLit qLit markedPoint literalData markedMembership i U V
      hU hV hcentU hcentV
  have hcentP : TileCentroid (pLit i) = TileCentroid U :=
    sub_left_injective ((literalData i).2.2.1.trans hcentU.symm)
  have hcentQ : TileCentroid (qLit i) = TileCentroid V :=
    sub_left_injective ((literalData i).2.2.2.trans hcentV.symm)
  have obsP := BandPrototileCentroidUnique _ _ _ (literalData i).1 hU hcentP
  have obsQ := BandPrototileCentroidUnique _ _ _ (literalData i).2.1 hV hcentQ
  have footP := (ProtoTileObservableExtensionality _ _ obsP.1 obsP.2).1
  have footQ := (ProtoTileObservableExtensionality _ _ obsQ.1 obsQ.2).1
  obtain ⟨incomingData⟩ := incoming i U hU hcentU
  obtain ⟨t5Data⟩ := evenT5 i U V hU hV hcentU hcentV
  have hm := markedMembership i
  have hmU : markedPoint i ∈ FootprintVertices U := footP ▸ hm.1.1.2
  have hmV : markedPoint i ∈ FootprintVertices V := footQ ▸ hm.1.2
  have hpoint : markedPoint i = t5Data.point :=
    (t5Data.unique_common _).mp ⟨⟨hm.1.1.1, hmU⟩, hmV⟩
  refine ⟨incomingData, t5Data, hpoint.symm, ?_⟩
  intro rightData
  have hright : markedPoint i = rightData.point :=
    (rightData.unique_common _).mp ⟨⟨hm.1.1.1, hm.2⟩, hmU⟩
  exact hright.symm.trans hpoint

private theorem signedNeg :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (i : Fin 3), ∀ (a : GaussianInt), TileCentroid (TileTranslation (cert.P i
            false) (-a)) - TileCentroid T = -(TileCentroid (TileTranslation (cert.P i true) a) -
            TileCentroid T) ) := by
  classical
  intro q cfg C₀ T cert i a
  have hp := (cert.outer_occurrence i true).2.2
  have hm := (cert.outer_occurrence i false).2.2
  simp only [↓reduceIte, Bool.false_eq_true, one_smul, neg_smul] at hp hm
  have hn : TileCentroid (cert.P i false) - TileCentroid T =
      -(TileCentroid (cert.P i true) - TileCentroid T) := by
    rw [hp, hm]
  have ha : GaussianRealPoint (-a) = -GaussianRealPoint a := by
    ext <;> simp [GaussianRealPoint]
  rw [(TileTranslationFormulas _ _).2.2.2.2.1,
    (TileTranslationFormulas _ _).2.2.2.2.1]
  change TileCentroid (cert.P i false) + GaussianRealPoint (-a) - TileCentroid T =
    -(TileCentroid (cert.P i true) + GaussianRealPoint a - TileCentroid T)
  rw [ha]
  calc
    TileCentroid (cert.P i false) + -GaussianRealPoint a - TileCentroid T =
      (TileCentroid (cert.P i false) - TileCentroid T) - GaussianRealPoint a := by abel
    _ = -(TileCentroid (cert.P i true) - TileCentroid T) - GaussianRealPoint a := by rw [hn]
    _ = -(TileCentroid (cert.P i true) + GaussianRealPoint a - TileCentroid T) := by abel

private theorem oddFormulaU :
    (by
      classical
      exact
        ∀ (w : GaussianInt), -((1 / 2 : Real) • (GaussianRealPoint w - GaussianRealPoint ((⟨0, 1⟩
            : GaussianInt) * w))) = (1 / 2 : Real) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) *
            (w + (⟨0, 1⟩ : GaussianInt) * w)) ) := by
  classical
  intro w
  ext <;> simp [GaussianRealPoint, Prod.smul_mk, smul_eq_mul] <;> ring

private theorem oddFormulaV :
    (by
      classical
      exact
        ∀ (w : GaussianInt), -((1 / 2 : Real) • (GaussianRealPoint w + GaussianRealPoint ((⟨0, 1⟩
            : GaussianInt) * w))) = (1 / 2 : Real) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) *
            ((⟨0, 1⟩ : GaussianInt) * w - w)) ) := by
  classical
  intro w
  ext <;> simp [GaussianRealPoint, Prod.smul_mk, smul_eq_mul] <;> ring

private theorem oddLiteralData :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let pLit (i : Fin 3) := TileTranslation (cert.P i true)
          (if i = 0 then -cert.v else if i = 1 then cert.u + cert.v else -cert.u)
        let qLit (i : Fin 3) := TileTranslation (cert.P (i + 1) true)
          (if i = 0 then cert.u else if i = 1 then cert.v else -cert.u - cert.v)
        (∀ (i : Fin 3), BandPrototile (q i.succ) (pLit i) ∧ BandPrototile (q ((i + 1).succ))
            (qLit i) ∧ TileCentroid (pLit i) - TileCentroid T = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) + GaussianRealPoint
            (BandVectors.1 (q 0) (q i.succ))) ∧ TileCentroid (qLit i) - TileCentroid T = (1 / 2 :
            Real) • (GaussianRealPoint (BandVectors.1 (q ((i + 1).succ)) (q 0)) -
            GaussianRealPoint (BandVectors.1 (q 0) (q ((i + 1).succ))))) → (
        let pOdd (i : Fin 3) := TileTranslation (cert.P i false)
          (if i = 0 then cert.u + cert.v else if i = 1 then -cert.u else -cert.v)
        let qOdd (i : Fin 3) := TileTranslation (cert.P (i - 1) false)
          (if i = 0 then cert.u else if i = 1 then cert.v else -cert.u - cert.v)
        (∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (i : Fin 3), ∀ (a : GaussianInt), TileCentroid (TileTranslation (cert.P i
            false) (-a)) - TileCentroid T = -(TileCentroid (TileTranslation (cert.P i true) a) -
            TileCentroid T)) → ((∀ (w : GaussianInt), -((1 / 2 : Real) • (GaussianRealPoint w -
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) * w))) = (1 / 2 : Real) • GaussianRealPoint
            ((⟨0, 1⟩ : GaussianInt) * (w + (⟨0, 1⟩ : GaussianInt) * w))) → ((∀ (w : GaussianInt),
            -((1 / 2 : Real) • (GaussianRealPoint w + GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) *
            w))) = (1 / 2 : Real) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) * ((⟨0, 1⟩ :
            GaussianInt) * w - w))) → (∀ (i : Fin 3), BandPrototile (q i.succ) (pOdd i) ∧
            BandPrototile (q ((i - 1).succ)) (qOdd i) ∧ TileCentroid (pOdd i) - TileCentroid T =
            (1 / 2 : Real) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) * (BandVectors.1 (q
            i.succ) (q 0) + BandVectors.1 (q 0) (q i.succ))) ∧ TileCentroid (qOdd i) -
            TileCentroid T = (1 / 2 : Real) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) *
            (BandVectors.1 (q 0) (q ((i - 1).succ)) - BandVectors.1 (q ((i - 1).succ)) (q
            0))))))) ) := by
  classical
  intro q cfg C₀ T cert pLit qLit literalData pOdd qOdd signedNeg oddFormulaU oddFormulaV i
  have hprev : ((i - 1) + 1 : Fin 3) = i := by fin_cases i <;> decide
  have hP : TileCentroid (pOdd i) - TileCentroid T =
      -(TileCentroid (qLit (i - 1)) - TileCentroid T) := by
    fin_cases i
    · simpa [pOdd, qLit, add_comm, show (-1 : Fin 3) = 2 by decide] using
        signedNeg q cfg C₀ T cert 0 (-cert.u - cert.v)
    · simpa [pOdd, qLit] using signedNeg q cfg C₀ T cert 1 cert.u
    · simpa [pOdd, qLit] using signedNeg q cfg C₀ T cert 2 cert.v
  have hQ : TileCentroid (qOdd i) - TileCentroid T =
      -(TileCentroid (pLit (i - 1)) - TileCentroid T) := by
    fin_cases i
    · simpa [qOdd, pLit, show (-1 : Fin 3) = 2 by decide] using
        signedNeg q cfg C₀ T cert 2 (-cert.u)
    · simpa [qOdd, pLit] using signedNeg q cfg C₀ T cert 0 (-cert.v)
    · simpa [qOdd, pLit, sub_eq_add_neg, add_comm, show (-1 : Fin 3) = 2 by decide] using
        signedNeg q cfg C₀ T cert 1 (cert.u + cert.v)
  have flip := (VectorRecursionLaws q cfg.proper.1).2.2.2.2 cfg.proper
  refine ⟨BandPrototileTranslation _ _ _ (cert.outer_occurrence i false).1,
    BandPrototileTranslation _ _ _ (cert.outer_occurrence (i - 1) false).1, ?_, ?_⟩
  · rw [hP, (literalData (i - 1)).2.2.2, hprev, (flip i).1]
    exact oddFormulaU _
  · rw [hQ, (literalData (i - 1)).2.2.1, (flip (i - 1)).1]
    exact oddFormulaV _

private theorem oddMembership :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (BandVectors.1 (q 0) (q 3) = -cert.u - cert.v) → (
        let pOdd (i : Fin 3) := TileTranslation (cert.P i false)
          (if i = 0 then cert.u + cert.v else if i = 1 then -cert.u else -cert.v)
        let qOdd (i : Fin 3) := TileTranslation (cert.P (i - 1) false)
          (if i = 0 then cert.u else if i = 1 then cert.v else -cert.u - cert.v)
        let oddPoint (i : Fin 3) := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm
            ⟨.J6, if i = 0 then 1 else 0, if i = 2 then 0 else 1⟩)
        ∀ (i : Fin 3), oddPoint i ∈ FootprintVertices T ∩ FootprintVertices (pOdd i) ∩
            FootprintVertices (qOdd i) ∧ oddPoint i ∈ FootprintVertices (TileTranslation T
            (BandVectors.1 (q 0) (q i.succ)))) ) := by
  classical
  intro q cfg C₀ T cert period3 pOdd qOdd oddPoint i
  have trzero (Y : ProtoTile) : TileTranslation Y 0 = Y := by
    have hfun : GaussianTranslation 0 = id := by
      funext z
      simp [GaussianTranslation]
    cases Y
    simp [TileTranslation, hfun]
  have trsubset (Y : ProtoTile) (a : GaussianInt)
      (h : FootprintVertices Y ⊆ FootprintVertices T) :
      FootprintVertices (TileTranslation Y a) ⊆ FootprintVertices (TileTranslation T a) := by
    rw [(TileTranslationFormulas Y a).2.2.2.2.2.1,
      (TileTranslationFormulas T a).2.2.2.2.2.1]
    exact Set.image_mono h
  have rho_mem (f : PeriodicSubtileFaceIndex) (k : Fin 3) :
      cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm f) ∈
        FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v
          (SixSubtileFaceVertices f k)) := by
    have h := cert.unmodified.core.rho_common (cert.unmodified.faceEquiv.symm f) k
    rw [cert.unmodified.face_vertices, cert.unmodified.faceEquiv.apply_symm_apply,
      cert.unmodified.tile_eq] at h
    exact h
  let f : PeriodicSubtileFaceIndex :=
    ⟨.J6, if i = 0 then 1 else 0, if i = 2 then 0 else 1⟩
  have h0 := rho_mem f 0
  have h1 := rho_mem f 1
  have h2 := rho_mem f 2
  fin_cases i
  all_goals
    simp only [SubtileOccurrenceInterpretation, SixSubtileFaceVertices, Fin.mk_one,
        Fin.isValue, one_ne_zero, ↓reduceIte, Fin.reduceEq, zero_sub, Int.reduceNeg, sub_self,
        Matrix.cons_val_zero, Int.cast_zero, zero_mul, Int.cast_one, one_mul, zero_add,
        Matrix.cons_val_one, Int.cast_neg, neg_mul, add_zero, Matrix.cons_val, trzero,
        Set.mem_inter_iff, Fin.succ_one_eq_two, f, pOdd, qOdd, oddPoint, Fin.reduceFinMk,
        Fin.reduceSub, Fin.reduceSucc, Fin.zero_eta, show (-1 : Fin 3) = 2 by decide,
        Fin.succ_zero_eq_one] at h0 h1 h2 ⊢
  · exact ⟨⟨⟨(cert.outer_occurrence 1 false).2.1 h1, h0⟩, h2⟩,
      (by
        rw [← cert.period_u]
        exact trsubset _ cert.u (cert.outer_occurrence 2 false).2.1 h2)⟩
  · exact ⟨⟨⟨(cert.outer_occurrence 2 false).2.1 h2, h1⟩, h0⟩,
      (by
        rw [← cert.period_v]
        exact trsubset _ cert.v (cert.outer_occurrence 0 false).2.1 h0)⟩
  · have h1' := h1
    simp only [← sub_eq_add_neg] at h1'
    exact ⟨⟨⟨(cert.outer_occurrence 0 false).2.1 h0, h2⟩, h1'⟩,
      (by
        rw [period3]
        exact trsubset _ (-cert.u - cert.v) (cert.outer_occurrence 1 false).2.1 h1')⟩

private theorem oddPoints :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let pOdd (i : Fin 3) := TileTranslation (cert.P i false)
          (if i = 0 then cert.u + cert.v else if i = 1 then -cert.u else -cert.v)
        let qOdd (i : Fin 3) := TileTranslation (cert.P (i - 1) false)
          (if i = 0 then cert.u else if i = 1 then cert.v else -cert.u - cert.v)
        let oddPoint (i : Fin 3) := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm
            ⟨.J6, if i = 0 then 1 else 0, if i = 2 then 0 else 1⟩)
        (∀ (i : Fin 3), BandPrototile (q i.succ) (pOdd i) ∧ BandPrototile (q ((i - 1).succ))
            (qOdd i) ∧ TileCentroid (pOdd i) - TileCentroid T = (1 / 2 : Real) •
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) * (BandVectors.1 (q i.succ) (q 0) +
            BandVectors.1 (q 0) (q i.succ))) ∧ TileCentroid (qOdd i) - TileCentroid T = (1 / 2 :
            Real) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) * (BandVectors.1 (q 0) (q ((i -
            1).succ)) - BandVectors.1 (q ((i - 1).succ)) (q 0)))) → ((∀ (i : Fin 3), oddPoint i ∈
            FootprintVertices T ∩ FootprintVertices (pOdd i) ∩ FootprintVertices (qOdd i) ∧
            oddPoint i ∈ FootprintVertices (TileTranslation T (BandVectors.1 (q 0) (q i.succ))))
            → (∀ (i : Fin 3), ∀ (U : ProtoTile), ∀ (V : ProtoTile), (BandPrototile (q i.succ) U)
            → ((BandPrototile (q ((i - 1).succ)) V) → ((TileCentroid U - TileCentroid T = (1 / 2
            : Real) •
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) *
              (BandVectors.1 (q i.succ) (q 0) + BandVectors.1 (q 0) (q i.succ)))) →
                  ((TileCentroid V - TileCentroid T = (1 / 2 : Real) •
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) *
              (BandVectors.1 (q 0) (q ((i - 1).succ)) -
                BandVectors.1 (q ((i - 1).succ)) (q 0)))) → (∀ (rightData :
                    ExactTileInterfaceTriple T
            (TileTranslation T (BandVectors.1 (q 0) (q i.succ))) U), ∀ (t5Data :
                ExactTileInterfaceTriple T U V), rightData.point = oddPoint i ∧ t5Data.point =
                oddPoint i)))))) ) := by
  classical
  intro q cfg C₀ T cert pOdd qOdd oddPoint oddLiteralData oddMembership i U V hU hV hcentU hcentV
      rightData t5Data
  have hcentP : TileCentroid (pOdd i) = TileCentroid U :=
    sub_left_injective ((oddLiteralData i).2.2.1.trans hcentU.symm)
  have hcentQ : TileCentroid (qOdd i) = TileCentroid V :=
    sub_left_injective ((oddLiteralData i).2.2.2.trans hcentV.symm)
  have obsP := BandPrototileCentroidUnique _ _ _ (oddLiteralData i).1 hU hcentP
  have obsQ := BandPrototileCentroidUnique _ _ _ (oddLiteralData i).2.1 hV hcentQ
  have footP := (ProtoTileObservableExtensionality _ _ obsP.1 obsP.2).1
  have footQ := (ProtoTileObservableExtensionality _ _ obsQ.1 obsQ.2).1
  have hm := oddMembership i
  have hmU : oddPoint i ∈ FootprintVertices U := footP ▸ hm.1.1.2
  have hmV : oddPoint i ∈ FootprintVertices V := footQ ▸ hm.1.2
  exact ⟨((rightData.unique_common _).mp ⟨⟨hm.1.1.1, hm.2⟩, hmU⟩).symm,
    ((t5Data.unique_common _).mp ⟨⟨hm.1.1.1, hmU⟩, hmV⟩).symm⟩

private theorem centeredComparison :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (∀ (C : CircleCoordinates), ∀ (Y : ProtoTile), ∀ (g : GaussianInt),
            (BandPrototile C Y) → ((QuarterTurnSymmetric Y) → (∃ Ysharp : ProtoTile,
            BandPrototile C Ysharp ∧ QuarterTurnSymmetric Ysharp ∧ (TileTranslation
            (TileQuarterTurn Y) g).cells = Ysharp.cells ∧ ((TileTranslation (TileQuarterTurn Y)
            g).cells = ∅ → (TileTranslation (TileQuarterTurn Y) g).anchor = Ysharp.anchor) ∧
            TileCentroid Ysharp = (-((TileCentroid Y).2) + (g.re : Int), (TileCentroid Y).1 +
            (g.im : Int))))) → (∀ (g : GaussianInt), (GaussianRealPoint g = ((TileCentroid T).1 +
            (TileCentroid T).2, (TileCentroid T).2 - (TileCentroid T).1)) → (∀ (C :
            CircleCoordinates), ∀ (Y : ProtoTile), ∀ (U : ProtoTile), (BandPrototile C Y) →
            ((QuarterTurnSymmetric Y) → ((BandPrototile C U) → ((TileCentroid U - TileCentroid T =
            (-((TileCentroid Y - TileCentroid T).2),
              (TileCentroid Y - TileCentroid T).1)) → ((TileTranslation (TileQuarterTurn Y)
                  g).cells = U.cells ∧ ((TileTranslation (TileQuarterTurn Y) g).cells = ∅ →
                  (TileTranslation (TileQuarterTurn Y) g).anchor = U.anchor))))))) ) := by
  classical
  intro T centeredProxy g hg C Y U hY hYsym hU hcentU
  obtain ⟨Ysharp, hband, hYsharpSym, hc, ha, hcent⟩ :=
    centeredProxy C Y g hY hYsym
  have hcentEq : TileCentroid Ysharp = TileCentroid U := by
    rw [hcent]
    have hr := congrArg Prod.fst hg
    have hi := congrArg Prod.snd hg
    have ur := congrArg Prod.fst hcentU
    have ui := congrArg Prod.snd hcentU
    change (g.re : Real) = (TileCentroid T).1 + (TileCentroid T).2 at hr
    change (g.im : Real) = (TileCentroid T).2 - (TileCentroid T).1 at hi
    ext <;> dsimp at ur ui ⊢ <;> linarith
  have obs := BandPrototileCentroidUnique C Ysharp U hband hU hcentEq
  exact ⟨hc.trans obs.1, fun he => (ha he).trans (obs.2 (hc ▸ he))⟩

private theorem halfTurnComparison :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (∀ (C : CircleCoordinates), ∀ (Y : ProtoTile), ∀ (g : GaussianInt),
            (BandPrototile C Y) → ((QuarterTurnSymmetric Y) → (∃ Zsharp : ProtoTile,
            BandPrototile C Zsharp ∧ QuarterTurnSymmetric Zsharp ∧ (TileTranslation
            (TileQuarterTurn (TileTranslation (TileQuarterTurn Y) g)) g).cells = Zsharp.cells ∧
            ((TileTranslation (TileQuarterTurn (TileTranslation (TileQuarterTurn Y) g)) g).cells
            = ∅ → (TileTranslation (TileQuarterTurn (TileTranslation (TileQuarterTurn Y) g))
            g).anchor = Zsharp.anchor) ∧ TileCentroid Zsharp = (-((TileCentroid Y).1) + (g.re :
            Int) - (g.im : Int), -((TileCentroid Y).2) + (g.re : Int) + (g.im : Int))))) → (∀ (g
            : GaussianInt), (GaussianRealPoint g = ((TileCentroid T).1 + (TileCentroid T).2,
            (TileCentroid T).2 - (TileCentroid T).1)) → (∀ (C : CircleCoordinates), ∀ (Y :
            ProtoTile), ∀ (U : ProtoTile), (BandPrototile C Y) → ((QuarterTurnSymmetric Y) →
            ((BandPrototile C U) → ((TileCentroid U - TileCentroid T =
            -(TileCentroid Y - TileCentroid T)) → ((TileTranslation (TileQuarterTurn
                (TileTranslation (TileQuarterTurn Y) g)) g).cells = U.cells ∧ ((TileTranslation
                (TileQuarterTurn (TileTranslation (TileQuarterTurn Y) g)) g).cells = ∅ →
                (TileTranslation (TileQuarterTurn (TileTranslation (TileQuarterTurn Y) g))
                g).anchor = U.anchor))))))) ) := by
  classical
  intro T halfTurnProxy g hg C Y U hY hYsym hU hcentU
  obtain ⟨Ysharp, hband, hYsharpSym, hc, ha, hcent⟩ :=
    halfTurnProxy C Y g hY hYsym
  have hcentEq : TileCentroid Ysharp = TileCentroid U := by
    rw [hcent]
    have hr := congrArg Prod.fst hg
    have hi := congrArg Prod.snd hg
    have ur := congrArg Prod.fst hcentU
    have ui := congrArg Prod.snd hcentU
    change (g.re : Real) = (TileCentroid T).1 + (TileCentroid T).2 at hr
    change (g.im : Real) = (TileCentroid T).2 - (TileCentroid T).1 at hi
    ext <;> dsimp at ur ui ⊢ <;> linarith
  have obs := BandPrototileCentroidUnique C Ysharp U hband hU hcentEq
  exact ⟨hc.trans obs.1, fun he => (ha he).trans (obs.2 (hc ▸ he))⟩

private theorem pathMap :
    (by
      classical
      exact
        ∀ (f : GaussianInt → GaussianInt), (Function.Injective f) → ((∀ a b : GaussianInt,
            (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) →
            (f b = f a + 1 ∨ f b = f a - 1 ∨
              f b = f a + ⟨0, 1⟩ ∨ f b = f a - ⟨0, 1⟩)) → (∀ (V : Set GaussianInt), ∀ (E : Set
                  (Finset GaussianInt)), ∀ (x : GaussianInt), ∀ (y : GaussianInt),
                  (SimpleGridPathBetween V E x y) → (SimpleGridPathBetween (f '' V) ((fun e :
                  Finset GaussianInt => e.image f) '' E) (f x) (f y)))) ) := by
  classical
  intro f hf hstep V E x y h
  rcases h with ⟨p, hn, hl, hh, ht, hv, hs, he⟩
  refine ⟨p.map f, hn.map hf, by simpa using hl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.head?_map, hh]; rfl
  · rw [List.getLast?_map, ht]; rfl
  · rw [hv]; ext z; simp
  · exact List.isChain_iff_forall_rel_of_append_cons_cons.mp
      (List.isChain_map_of_isChain f hstep
        (List.isChain_iff_forall_rel_of_append_cons_cons.mpr hs))
  · intro e
    constructor
    · rintro ⟨d, hd, rfl⟩
      rcases (he d).mp hd with ⟨a, b, l₁, l₂, hp, rfl⟩
      refine ⟨f a, f b, l₁.map f, l₂.map f, ?_, ?_⟩
      · simpa using congrArg (List.map f) hp
      · simp
    · rintro ⟨a, b, l₁, l₂, hp, rfl⟩
      obtain ⟨k, r, hkr, hk, hr⟩ := List.map_eq_append_iff.mp hp
      obtain ⟨a₀, r₁, hr₁, ha, hm₁⟩ := List.map_eq_cons_iff.mp hr
      obtain ⟨b₀, r₂, hr₂, hb, hm₂⟩ := List.map_eq_cons_iff.mp hm₁
      refine ⟨{a₀, b₀}, (he _).mpr ⟨a₀, b₀, k, r₂, ?_, rfl⟩, ?_⟩
      · rw [hkr, hr₁, hr₂]
      · simp [ha, hb]

private theorem tripleMap :
    (by
      classical
      exact
        (∀ (f : GaussianInt → GaussianInt), (Function.Injective f) → ((∀ a b : GaussianInt, (b =
            a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) → (f b = f a + 1 ∨ f b = f a - 1
            ∨ f b = f a + ⟨0, 1⟩ ∨ f b = f a - ⟨0, 1⟩)) → (∀ (V : Set GaussianInt), ∀ (E : Set
            (Finset GaussianInt)), ∀ (x : GaussianInt), ∀ (y : GaussianInt),
            (SimpleGridPathBetween V E x y) → (SimpleGridPathBetween (f '' V) ((fun e : Finset
            GaussianInt => e.image f) '' E) (f x) (f y))))) → (∀ (F : ProtoTile → ProtoTile), ∀
            (f : GaussianInt → GaussianInt), (Function.Injective f) → ((∀ a b : GaussianInt,
            (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) →
            (f b = f a + 1 ∨ f b = f a - 1 ∨
              f b = f a + ⟨0, 1⟩ ∨ f b = f a - ⟨0, 1⟩)) → ((∀ Y, FootprintVertices (F Y) = f ''
                  FootprintVertices Y) → ((∀ Y, FootprintEdges (F Y) =
            (fun e : Finset GaussianInt => e.image f) '' FootprintEdges Y) → (∀ (A : ProtoTile),
                ∀ (B : ProtoTile), ∀ (C : ProtoTile), ∀ (E : ExactTileInterfaceTriple A B C), ∃
                E' : ExactTileInterfaceTriple (F A) (F B) (F C), E'.point = f E.point ∧
                E'.otherAB = f E.otherAB ∧ E'.otherBC = f E.otherBC ∧ E'.otherCA = f
                E.otherCA))))) ) := by
  classical
  intro pathMap F f hf hstep hv he A B C E
  have hedge : Function.Injective (fun e : Finset GaussianInt => e.image f) :=
    Finset.image_injective hf
  refine ⟨⟨f E.point, f E.otherAB, f E.otherBC, f E.otherCA,
    ?_, ?_, ?_, ?_⟩, rfl, rfl, rfl, rfl⟩
  · simpa only [hv, he, ← Set.image_inter hf, ← Set.image_inter hedge] using
      pathMap f hf hstep _ _ _ _ E.pathAB
  · simpa only [hv, he, ← Set.image_inter hf, ← Set.image_inter hedge] using
      pathMap f hf hstep _ _ _ _ E.pathBC
  · simpa only [hv, he, ← Set.image_inter hf, ← Set.image_inter hedge] using
      pathMap f hf hstep _ _ _ _ E.pathCA
  · intro z
    rw [hv, hv, hv, ← Set.image_inter hf, ← Set.image_inter hf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [(E.unique_common x).mp hx]
    · rintro rfl
      exact ⟨E.point, (E.unique_common _).mpr rfl, rfl⟩

private theorem tripleRetarget :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (A' : ProtoTile), ∀ (B : ProtoTile), ∀ (B' : ProtoTile), ∀ (C :
            ProtoTile), ∀ (C' : ProtoTile), (A.cells = A'.cells ∧ (A.cells = ∅ → A.anchor =
            A'.anchor)) → ((B.cells = B'.cells ∧ (B.cells = ∅ → B.anchor = B'.anchor)) →
            ((C.cells = C'.cells ∧ (C.cells = ∅ → C.anchor = C'.anchor)) → (∀ (E :
            ExactTileInterfaceTriple A B C), ∃ E' : ExactTileInterfaceTriple A' B' C', E'.point =
            E.point ∧ E'.otherAB = E.otherAB ∧ E'.otherBC = E.otherBC ∧ E'.otherCA = E.otherCA)))
            ) := by
  classical
  intro A A' B B' C C' hA hB hC E
  have vA := (ProtoTileObservableExtensionality A A' hA.1 hA.2).1
  have vB := (ProtoTileObservableExtensionality B B' hB.1 hB.2).1
  have vC := (ProtoTileObservableExtensionality C C' hC.1 hC.2).1
  have eA : FootprintEdges A = FootprintEdges A' := by simp [FootprintEdges, hA.1]
  have eB : FootprintEdges B = FootprintEdges B' := by simp [FootprintEdges, hB.1]
  have eC : FootprintEdges C = FootprintEdges C' := by simp [FootprintEdges, hC.1]
  refine ⟨⟨E.point, E.otherAB, E.otherBC, E.otherCA, ?_, ?_, ?_, ?_⟩,
    rfl, rfl, rfl, rfl⟩
  · simpa only [← vA, ← vB, ← eA, ← eB] using E.pathAB
  · simpa only [← vB, ← vC, ← eB, ← eC] using E.pathBC
  · simpa only [← vC, ← vA, ← eC, ← eA] using E.pathCA
  · intro z; simpa only [← vA, ← vB, ← vC] using E.unique_common z

private theorem tripleTurn :
    (by
      classical
      exact
        (∀ (F : ProtoTile → ProtoTile), ∀ (f : GaussianInt → GaussianInt), (Function.Injective f)
            → ((∀ a b : GaussianInt, (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) →
            (f b = f a + 1 ∨ f b = f a - 1 ∨ f b = f a + ⟨0, 1⟩ ∨ f b = f a - ⟨0, 1⟩)) → ((∀ Y,
            FootprintVertices (F Y) = f '' FootprintVertices Y) → ((∀ Y, FootprintEdges (F Y) =
            (fun e : Finset GaussianInt => e.image f) '' FootprintEdges Y) → (∀ (A : ProtoTile),
            ∀ (B : ProtoTile), ∀ (C : ProtoTile), ∀ (E : ExactTileInterfaceTriple A B C), ∃ E' :
            ExactTileInterfaceTriple (F A) (F B) (F C), E'.point = f E.point ∧ E'.otherAB = f
            E.otherAB ∧ E'.otherBC = f E.otherBC ∧ E'.otherCA = f E.otherCA))))) → (∀ (a :
            GaussianInt), ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), ∀ (E :
            ExactTileInterfaceTriple A B C), ∃ E' : ExactTileInterfaceTriple (TileTranslation
            (TileQuarterTurn A) a) (TileTranslation (TileQuarterTurn B) a) (TileTranslation
            (TileQuarterTurn C) a), E'.point = GaussianQuarterTurn E.point + a ∧ E'.otherAB =
            GaussianQuarterTurn E.otherAB + a ∧ E'.otherBC = GaussianQuarterTurn E.otherBC + a ∧
            E'.otherCA = GaussianQuarterTurn E.otherCA + a) ) := by
  classical
  intro tripleMap a A B C E
  apply tripleMap (fun Y => TileTranslation (TileQuarterTurn Y) a)
    (fun z => GaussianQuarterTurn z + a) _ _ _ _ A B C E
  · intro x y h
    have hq := add_right_cancel h
    apply Zsqrtd.ext
    · simpa [GaussianQuarterTurn] using congrArg (fun z : GaussianInt => z.im) hq
    · simpa [GaussianQuarterTurn] using congrArg (fun z : GaussianInt => -z.re) hq
  · intro x y h
    rcases h with h | h | h | h <;> subst y
    · right; right; left; ext <;> simp [GaussianQuarterTurn]; omega
    · right; right; right; ext <;> simp [GaussianQuarterTurn]; omega
    · right; left; ext <;> simp [GaussianQuarterTurn]; omega
    · left; ext <;> simp [GaussianQuarterTurn]; omega
  · intro Y
    rw [(TileTranslationFormulas _ _).2.2.2.2.2.1,
      (TileQuarterTurnFormulas _).2.2.2.2.2.1, Set.image_image]
    rfl
  · intro Y
    rw [(TileTranslationFormulas _ _).2.2.2.2.2.2.1,
      (TileQuarterTurnFormulas _).2.2.2.2.2.2.1, Set.image_image]
    congr 1
    funext e
    rw [Finset.image_image]
    rfl

private theorem translateZero :
    (by
      classical
      exact
        ∀ (Y : ProtoTile), TileTranslation Y 0 = Y ) := by
  classical
  intro Y
  have h : GaussianTranslation 0 = id := by funext z; simp [GaussianTranslation]
  cases Y
  simp [TileTranslation, h]

private theorem turnTranslate :
    (by
      classical
      exact
        ∀ (Y : ProtoTile), ∀ (a : GaussianInt), ∀ (k : GaussianInt), ∀ (g : GaussianInt),
            TileTranslation (TileQuarterTurn (TileTranslation Y a)) k = TileTranslation
            (TileTranslation (TileQuarterTurn Y) g) (k - g + GaussianQuarterTurn a) ) := by
  classical
  intro Y a k g
  simp only [TileTranslation, TileQuarterTurn, ProtoTile.mk.injEq]
  constructor
  · simp only [Finset.image_image]
    congr 1
    funext z
    ext <;> simp [Function.comp_def, GaussianTranslation, GaussianQuarterTurn] <;> ring
  · ext <;> simp [GaussianTranslation, GaussianQuarterTurn] <;> ring

private theorem obsTranslate :
    (by
      classical
      exact
        ∀ (Y : ProtoTile), ∀ (Z : ProtoTile), ∀ (a : GaussianInt), (Y.cells = Z.cells ∧ (Y.cells
            = ∅ → Y.anchor = Z.anchor)) → ((TileTranslation Y a).cells = (TileTranslation Z
            a).cells ∧ ((TileTranslation Y a).cells = ∅ → (TileTranslation Y a).anchor =
            (TileTranslation Z a).anchor)) ) := by
  classical
  intro Y Z a h
  constructor
  · simp [TileTranslation, h.1]
  · intro he
    change GaussianTranslation a Y.anchor = GaussianTranslation a Z.anchor
    rw [h.2 ((TileTranslationFormulas Y a).2.2.1.mp he)]

private theorem swapFirst :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), ∀ (E : ExactTileInterfaceTriple
            A B C), ∃ E' : ExactTileInterfaceTriple B A C, E'.point = E.point ∧ E'.otherAB =
            E.otherAB ∧ E'.otherBC = E.otherCA ∧ E'.otherCA = E.otherBC ) := by
  classical
  intro A B C E
  refine ⟨⟨E.point, E.otherAB, E.otherCA, E.otherBC, ?_, ?_, ?_, ?_⟩,
    rfl, rfl, rfl, rfl⟩
  · simpa [Set.inter_comm] using E.pathAB
  · simpa [Set.inter_comm] using E.pathCA
  · simpa [Set.inter_comm] using E.pathBC
  · intro z
    simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using E.unique_common z

private theorem parentTurn :
    (by
      classical
      exact
        (∀ (A : ProtoTile), ∀ (A' : ProtoTile), ∀ (B : ProtoTile), ∀ (B' : ProtoTile), ∀ (C :
            ProtoTile), ∀ (C' : ProtoTile), (A.cells = A'.cells ∧ (A.cells = ∅ → A.anchor =
            A'.anchor)) → ((B.cells = B'.cells ∧ (B.cells = ∅ → B.anchor = B'.anchor)) →
            ((C.cells = C'.cells ∧ (C.cells = ∅ → C.anchor = C'.anchor)) → (∀ (E :
            ExactTileInterfaceTriple A B C), ∃ E' : ExactTileInterfaceTriple A' B' C', E'.point =
            E.point ∧ E'.otherAB = E.otherAB ∧ E'.otherBC = E.otherBC ∧ E'.otherCA =
            E.otherCA)))) → ((∀ (a : GaussianInt), ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C :
            ProtoTile), ∀ (E : ExactTileInterfaceTriple A B C), ∃ E' : ExactTileInterfaceTriple
            (TileTranslation (TileQuarterTurn A) a) (TileTranslation (TileQuarterTurn B) a)
            (TileTranslation (TileQuarterTurn C) a), E'.point = GaussianQuarterTurn E.point + a ∧
            E'.otherAB = GaussianQuarterTurn E.otherAB + a ∧ E'.otherBC = GaussianQuarterTurn
            E.otherBC + a ∧ E'.otherCA = GaussianQuarterTurn E.otherCA + a) → ((∀ (Y :
            ProtoTile), ∀ (a : GaussianInt), ∀ (k : GaussianInt), ∀ (g : GaussianInt),
            TileTranslation (TileQuarterTurn (TileTranslation Y a)) k = TileTranslation
            (TileTranslation (TileQuarterTurn Y) g) (k - g + GaussianQuarterTurn a)) → ((∀ (Y :
            ProtoTile), ∀ (Z : ProtoTile), ∀ (a : GaussianInt), (Y.cells = Z.cells ∧ (Y.cells = ∅
            → Y.anchor = Z.anchor)) → ((TileTranslation Y a).cells = (TileTranslation Z a).cells
            ∧ ((TileTranslation Y a).cells = ∅ → (TileTranslation Y a).anchor = (TileTranslation
            Z a).anchor))) → (∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (w : GaussianInt), ∀ (g :
            GaussianInt), ∀ (k : GaussianInt), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
            ((TileTranslation (TileQuarterTurn T) g).cells = T.cells ∧
            ((TileTranslation (TileQuarterTurn T) g).cells = ∅ →
              (TileTranslation (TileQuarterTurn T) g).anchor = T.anchor)) → (((TileTranslation
                  (TileQuarterTurn U) k).cells = U.cells ∧
            ((TileTranslation (TileQuarterTurn U) k).cells = ∅ →
              (TileTranslation (TileQuarterTurn U) k).anchor = U.anchor)) → ((k - g = w) → (∀ (E
                  : ExactTileInterfaceTriple (TileTranslation T a) (TileTranslation T b) U), ∃ E'
                  : ExactTileInterfaceTriple (TileTranslation T (w + GaussianQuarterTurn a))
                  (TileTranslation T (w + GaussianQuarterTurn b)) U, E'.point =
                  GaussianQuarterTurn E.point + k))))))) ) := by
  classical
  intro tripleRetarget tripleTurn turnTranslate obsTranslate T U w g k a b hT hU hw E
  subst w
  obtain ⟨D, hp, _⟩ := tripleTurn k _ _ _ E
  have hA := obsTranslate _ T (k - g + GaussianQuarterTurn a) hT
  have hB := obsTranslate _ T (k - g + GaussianQuarterTurn b) hT
  rw [← turnTranslate] at hA hB
  obtain ⟨D', hp', _⟩ := tripleRetarget _ _ _ _ _ _ hA hB hU D
  exact ⟨D', hp'.trans hp⟩

private theorem fixedPointNotCommon :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (k : GaussianInt), ∀ (x : GaussianInt),
            (T.cells.Nonempty) → ((U.cells.Nonempty) → ((Disjoint T.cells U.cells) →
            (((TileTranslation (TileQuarterTurn U) k).cells = U.cells) → ((GaussianQuarterTurn x
            + k = x) → ((x ∈ FootprintVertices T) → ((x ∈ FootprintVertices U) → (False))))))) )
            := by
  classical
  intro T U k x hT hU hd hc hfixed hxT hxU
  have incident (Y : ProtoTile) (hne : Y.cells.Nonempty) (hx : x ∈ FootprintVertices Y) :
      ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ Y.cells := by
    simp only [FootprintVertices, hne, ite_true, Set.mem_ofPred_eq] at hx
    rcases hx with ⟨c, hc, h | h | h | h⟩
    · refine ⟨0, ?_⟩; simpa [LatticeVertexIncidentCell] using h ▸ hc
    · subst x; refine ⟨1, ?_⟩; simpa [LatticeVertexIncidentCell] using hc
    · subst x; refine ⟨3, ?_⟩; simpa [LatticeVertexIncidentCell] using hc
    · subst x; refine ⟨2, ?_⟩
      convert hc using 1
      ext <;> simp [LatticeVertexIncidentCell]
  obtain ⟨j, hj⟩ := incident U hU hxU
  obtain ⟨l, hl⟩ := incident T hT hxT
  have rotate (j : Fin 4) (hj : LatticeVertexIncidentCell x j ∈ U.cells) :
      LatticeVertexIncidentCell x (j + 1) ∈ U.cells := by
    rw [← hc, (TileTranslationFormulas _ _).1, (TileQuarterTurnFormulas _).1]
    apply Finset.mem_image.mpr
    refine ⟨GaussianQuarterTurn (LatticeVertexIncidentCell x j) - 1,
      Finset.mem_image.mpr ⟨_, hj, rfl⟩, ?_⟩
    have hr := congrArg Zsqrtd.re hfixed
    have hi := congrArg Zsqrtd.im hfixed
    fin_cases j <;> ext <;>
      simp [GaussianTranslation, GaussianQuarterTurn,
        LatticeVertexIncidentCell] at hr hi ⊢ <;> omega
  have h1 := rotate j hj
  have h2 := rotate (j + 1) h1
  have h3 := rotate ((j + 1) + 1) h2
  have hall : LatticeVertexIncidentCell x l ∈ U.cells := by
    fin_cases j <;> fin_cases l <;>
      simp only [] at hj h1 h2 h3 <;> assumption
  exact Finset.disjoint_left.mp hd hl hall

private theorem markedFromIncoming :
    (by
      classical
      exact
        (∀ (Y : ProtoTile), TileTranslation Y 0 = Y) → ((∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀
            (C : ProtoTile), ∀ (E : ExactTileInterfaceTriple A B C), ∃ E' :
            ExactTileInterfaceTriple B A C, E'.point = E.point ∧ E'.otherAB = E.otherAB ∧
            E'.otherBC = E.otherCA ∧ E'.otherCA = E.otherBC) → ((∀ (T : ProtoTile), ∀ (U :
            ProtoTile), ∀ (w : GaussianInt), ∀ (g : GaussianInt), ∀ (k : GaussianInt), ∀ (a :
            GaussianInt), ∀ (b : GaussianInt), ((TileTranslation (TileQuarterTurn T) g).cells =
            T.cells ∧ ((TileTranslation (TileQuarterTurn T) g).cells = ∅ → (TileTranslation
            (TileQuarterTurn T) g).anchor = T.anchor)) → (((TileTranslation (TileQuarterTurn U)
            k).cells = U.cells ∧ ((TileTranslation (TileQuarterTurn U) k).cells = ∅ →
            (TileTranslation (TileQuarterTurn U) k).anchor = U.anchor)) → ((k - g = w) → (∀ (E :
            ExactTileInterfaceTriple (TileTranslation T a) (TileTranslation T b) U), ∃ E' :
            ExactTileInterfaceTriple (TileTranslation T (w + GaussianQuarterTurn a))
            (TileTranslation T (w + GaussianQuarterTurn b)) U, E'.point = GaussianQuarterTurn
            E.point + k)))) → ((∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (k : GaussianInt), ∀ (x :
            GaussianInt), (T.cells.Nonempty) → ((U.cells.Nonempty) → ((Disjoint T.cells U.cells)
            → (((TileTranslation (TileQuarterTurn U) k).cells = U.cells) → ((GaussianQuarterTurn
            x + k = x) → ((x ∈ FootprintVertices T) → ((x ∈ FootprintVertices U) → (False))))))))
            → (∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (w : GaussianInt), (QuarterTurnSymmetric
            T) → ((QuarterTurnSymmetric U) → ((T.cells.Nonempty) → ((U.cells.Nonempty) →
            ((Disjoint T.cells U.cells) → ((TileCentroid U - TileCentroid T = (1 / 2 : Real) •
            GaussianRealPoint (w + GaussianQuarterTurn w)) → (∀ (E : ExactTileInterfaceTriple T
                (TileTranslation T w) U), ∃ R : ExactTileInterfaceTriple T (TileTranslation T
                (GaussianQuarterTurn w)) U, E.point ≠ R.point)))))))))) ) := by
  classical
  intro translateZero swapFirst parentTurn fixedPointNotCommon T U w hsT hsU hT hU hd hcent E
  obtain ⟨g, hg, hTc, hTa, _⟩ := QuarterTurnSymmetricCenteredTransport T hsT
  obtain ⟨k, hk, hUc, hUa, _⟩ := QuarterTurnSymmetricCenteredTransport U hsU
  have hw : k - g = w := by
    have gr := congrArg Prod.fst hg
    have gi := congrArg Prod.snd hg
    have kr := congrArg Prod.fst hk
    have ki := congrArg Prod.snd hk
    have dr := congrArg Prod.fst hcent
    have di := congrArg Prod.snd hcent
    simp [GaussianRealPoint, GaussianQuarterTurn, Prod.smul_mk, smul_eq_mul] at gr gi kr ki dr di
    simp only [← GaussianInt.intCast_re, ← GaussianInt.intCast_im] at gr gi kr ki dr di
    ext
    · have h : (k.re : Real) - (g.re : Real) = (w.re : Real) := by linarith
      exact_mod_cast h
    · have h : (k.im : Real) - (g.im : Real) = (w.im : Real) := by linarith
      exact_mod_cast h
  have ht : (TileTranslation (TileQuarterTurn T) g).cells = T.cells ∧
      ((TileTranslation (TileQuarterTurn T) g).cells = ∅ →
        (TileTranslation (TileQuarterTurn T) g).anchor = T.anchor) :=
    ⟨hTc, fun he => hTa (hTc ▸ he)⟩
  have hu : (TileTranslation (TileQuarterTurn U) k).cells = U.cells ∧
      ((TileTranslation (TileQuarterTurn U) k).cells = ∅ →
        (TileTranslation (TileQuarterTurn U) k).anchor = U.anchor) :=
    ⟨hUc, fun he => hUa (hUc ▸ he)⟩
  have ep0 : ∃ E0 : ExactTileInterfaceTriple (TileTranslation T 0) (TileTranslation T w) U,
      E0.point = E.point := by
    rw [translateZero T]
    exact ⟨E, rfl⟩
  obtain ⟨E0, hp0⟩ := ep0
  have ep1 := parentTurn T U w g k 0 w ht hu hw E0
  have qzero : GaussianQuarterTurn 0 = 0 := by ext <;> simp [GaussianQuarterTurn]
  rw [qzero, add_zero] at ep1
  obtain ⟨E1, hp1⟩ := ep1
  obtain ⟨E2, hp2⟩ := parentTurn T U w g k w
    (w + GaussianQuarterTurn w) ht hu hw E1
  have ep3 := parentTurn T U w g k
    (w + GaussianQuarterTurn w) (w + GaussianQuarterTurn (w + GaussianQuarterTurn w))
    ht hu hw E2
  have ha : w + GaussianQuarterTurn (w + GaussianQuarterTurn w) = GaussianQuarterTurn w := by
    ext <;> simp [GaussianQuarterTurn]
  have hb : w + GaussianQuarterTurn (w + GaussianQuarterTurn (w + GaussianQuarterTurn w)) = 0 := by
    ext <;> simp [GaussianQuarterTurn]
  generalize hx2 : E2.point = x2 at ep3
  rw [hb, ha, translateZero] at ep3
  obtain ⟨E3, hp3⟩ := ep3
  obtain ⟨R, hpR, _⟩ := swapFirst _ _ _ E3
  refine ⟨R, ?_⟩
  intro heq
  have hfixed : GaussianQuarterTurn E.point + k = E.point := by
    have h := hpR.trans hp3
    rw [← hx2, hp2, hp1, hp0] at h
    rw [← heq] at h
    have hr := congrArg Zsqrtd.re h
    have hi := congrArg Zsqrtd.im h
    ext <;> simp [GaussianQuarterTurn] at hr hi ⊢ <;> omega
  have hx := (E.unique_common E.point).mpr rfl
  exact fixedPointNotCommon T U k E.point hT hU hd hUc hfixed hx.1.1 hx.2

private theorem qinj :
    (by
      classical
      exact
        Function.Injective GaussianQuarterTurn ) := by
  classical
  intro x y h
  apply Zsqrtd.ext
  · simpa [GaussianQuarterTurn] using congrArg (fun z : GaussianInt => z.im) h
  · simpa [GaussianQuarterTurn] using congrArg (fun z : GaussianInt => -z.re) h

private theorem turnAtRoot :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (g : GaussianInt), (∀ (A : ProtoTile), ∀ (A' : ProtoTile), ∀ (B :
            ProtoTile), ∀ (B' : ProtoTile), ∀ (C : ProtoTile), ∀ (C' : ProtoTile), (A.cells =
            A'.cells ∧ (A.cells = ∅ → A.anchor = A'.anchor)) → ((B.cells = B'.cells ∧ (B.cells =
            ∅ → B.anchor = B'.anchor)) → ((C.cells = C'.cells ∧ (C.cells = ∅ → C.anchor =
            C'.anchor)) → (∀ (E : ExactTileInterfaceTriple A B C), ∃ E' :
            ExactTileInterfaceTriple A' B' C', E'.point = E.point ∧ E'.otherAB = E.otherAB ∧
            E'.otherBC = E.otherBC ∧ E'.otherCA = E.otherCA)))) → ((∀ (a : GaussianInt), ∀ (A :
            ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), ∀ (E : ExactTileInterfaceTriple A B
            C), ∃ E' : ExactTileInterfaceTriple (TileTranslation (TileQuarterTurn A) a)
            (TileTranslation (TileQuarterTurn B) a) (TileTranslation (TileQuarterTurn C) a),
            E'.point = GaussianQuarterTurn E.point + a ∧ E'.otherAB = GaussianQuarterTurn
            E.otherAB + a ∧ E'.otherBC = GaussianQuarterTurn E.otherBC + a ∧ E'.otherCA =
            GaussianQuarterTurn E.otherCA + a) → (
        let R (Y : ProtoTile) := TileTranslation (TileQuarterTurn Y) g
        ((R T).cells = T.cells ∧ ((R T).cells = ∅ → (R T).anchor = T.anchor)) → (∀ (B :
            ProtoTile), ∀ (C : ProtoTile), ∀ (B' : ProtoTile), ∀ (C' : ProtoTile), ((R B).cells =
            B'.cells ∧ ((R B).cells = ∅ → (R B).anchor = B'.anchor)) → (((R C).cells = C'.cells ∧
            ((R C).cells = ∅ → (R C).anchor = C'.anchor)) → (∀ (E : ExactTileInterfaceTriple T B
            C), ∃ E' : ExactTileInterfaceTriple T B' C', E'.point = GaussianQuarterTurn E.point +
            g ∧ E'.otherAB = GaussianQuarterTurn E.otherAB + g ∧ E'.otherBC = GaussianQuarterTurn
            E.otherBC + g ∧ E'.otherCA = GaussianQuarterTurn E.otherCA + g))))) ) := by
  classical
  intro T g tripleRetarget tripleTurn R rootObs B C B' C' hB hC E
  obtain ⟨D, hp, hab, hbc, hca⟩ := tripleTurn g _ _ _ E
  obtain ⟨D', hp', hab', hbc', hca'⟩ := tripleRetarget _ _ _ _ _ _ rootObs hB hC D
  exact ⟨D', hp'.trans hp, hab'.trans hab, hbc'.trans hbc, hca'.trans hca⟩

private theorem companionObs :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (g : GaussianInt), (∀ (Y : ProtoTile), ∀ (a : GaussianInt), ∀ (k :
            GaussianInt), ∀ (g : GaussianInt), TileTranslation (TileQuarterTurn (TileTranslation
            Y a)) k = TileTranslation (TileTranslation (TileQuarterTurn Y) g) (k - g +
            GaussianQuarterTurn a)) → ((∀ (Y : ProtoTile), ∀ (Z : ProtoTile), ∀ (a :
            GaussianInt), (Y.cells = Z.cells ∧ (Y.cells = ∅ → Y.anchor = Z.anchor)) →
            ((TileTranslation Y a).cells = (TileTranslation Z a).cells ∧ ((TileTranslation Y
            a).cells = ∅ → (TileTranslation Y a).anchor = (TileTranslation Z a).anchor))) → (
        let R (Y : ProtoTile) := TileTranslation (TileQuarterTurn Y) g
        ((R T).cells = T.cells ∧ ((R T).cells = ∅ → (R T).anchor = T.anchor)) → (∀ (a :
            GaussianInt), (R (TileTranslation T a)).cells = (TileTranslation T
            (GaussianQuarterTurn a)).cells ∧ ((R (TileTranslation T a)).cells = ∅ → (R
            (TileTranslation T a)).anchor = (TileTranslation T (GaussianQuarterTurn
            a)).anchor)))) ) := by
  classical
  intro T g turnTranslate obsTranslate R rootObs a
  have h := obsTranslate _ T (GaussianQuarterTurn a) rootObs
  rw [show GaussianQuarterTurn a = g - g + GaussianQuarterTurn a by simp,
    ← turnTranslate] at h
  simpa only [R, sub_self, zero_add] using h

private theorem obsTurn :
    (by
      classical
      exact
        ∀ (g : GaussianInt),
        let R (Y : ProtoTile) := TileTranslation (TileQuarterTurn Y) g
        ∀ (Y : ProtoTile), ∀ (Z : ProtoTile), (Y.cells = Z.cells ∧ (Y.cells = ∅ → Y.anchor =
            Z.anchor)) → ((R Y).cells = (R Z).cells ∧ ((R Y).cells = ∅ → (R Y).anchor = (R
            Z).anchor)) ) := by
  classical
  intro g R Y Z h
  constructor
  · simp only [R, TileTranslation, TileQuarterTurn, h.1]
  · intro he
    have heY : Y.cells = ∅ :=
      (TileQuarterTurnFormulas Y).2.2.1.mp ((TileTranslationFormulas _ _).2.2.1.mp he)
    change GaussianTranslation g (GaussianQuarterTurn Y.anchor) =
      GaussianTranslation g (GaussianQuarterTurn Z.anchor)
    rw [h.2 heY]

private theorem halfCompanionObs :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (g : GaussianInt), (∀ (w : GaussianInt), GaussianQuarterTurn
            (GaussianQuarterTurn w) = -w) → (
        let R (Y : ProtoTile) := TileTranslation (TileQuarterTurn Y) g
        (∀ (a : GaussianInt), (R (TileTranslation T a)).cells = (TileTranslation T
            (GaussianQuarterTurn a)).cells ∧ ((R (TileTranslation T a)).cells = ∅ → (R
            (TileTranslation T a)).anchor = (TileTranslation T (GaussianQuarterTurn a)).anchor))
            → ((∀ (Y : ProtoTile), ∀ (Z : ProtoTile), (Y.cells = Z.cells ∧ (Y.cells = ∅ →
            Y.anchor = Z.anchor)) → ((R Y).cells = (R Z).cells ∧ ((R Y).cells = ∅ → (R Y).anchor
            = (R Z).anchor))) → ((∀ (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (Z : ProtoTile),
            (X.cells = Y.cells ∧ (X.cells = ∅ → X.anchor = Y.anchor)) → ((Y.cells = Z.cells ∧
            (Y.cells = ∅ → Y.anchor = Z.anchor)) → (X.cells = Z.cells ∧ (X.cells = ∅ → X.anchor =
            Z.anchor)))) → (∀ (a : GaussianInt), (R (R (TileTranslation T a))).cells =
            (TileTranslation T (-a)).cells ∧ ((R (R (TileTranslation T a))).cells = ∅ → (R (R
            (TileTranslation T a))).anchor = (TileTranslation T (-a)).anchor))))) ) := by
  classical
  intro T g qneg R companionObs obsTurn obsTrans a
  have h := obsTrans _ _ _ (obsTurn _ _ (companionObs a))
    (companionObs (GaussianQuarterTurn a))
  simpa only [qneg] using h

private theorem halfAtRoot :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (g : GaussianInt),
        let R (Y : ProtoTile) := TileTranslation (TileQuarterTurn Y) g
        (∀ (Y : ProtoTile), Y.cells = Y.cells ∧ (Y.cells = ∅ → Y.anchor = Y.anchor)) → ((∀ (B :
            ProtoTile), ∀ (C : ProtoTile), ∀ (B' : ProtoTile), ∀ (C' : ProtoTile), ((R B).cells =
            B'.cells ∧ ((R B).cells = ∅ → (R B).anchor = B'.anchor)) → (((R C).cells = C'.cells ∧
            ((R C).cells = ∅ → (R C).anchor = C'.anchor)) → (∀ (E : ExactTileInterfaceTriple T B
            C), ∃ E' : ExactTileInterfaceTriple T B' C', E'.point = GaussianQuarterTurn E.point +
            g ∧ E'.otherAB = GaussianQuarterTurn E.otherAB + g ∧ E'.otherBC = GaussianQuarterTurn
            E.otherBC + g ∧ E'.otherCA = GaussianQuarterTurn E.otherCA + g))) → (∀ (B :
            ProtoTile), ∀ (C : ProtoTile), ∀ (B' : ProtoTile), ∀ (C' : ProtoTile), ((R (R
            B)).cells = B'.cells ∧ ((R (R B)).cells = ∅ → (R (R B)).anchor = B'.anchor)) → (((R
            (R C)).cells = C'.cells ∧ ((R (R C)).cells = ∅ → (R (R C)).anchor = C'.anchor)) → (∀
            (E : ExactTileInterfaceTriple T B C), ∃ E' : ExactTileInterfaceTriple T B' C',
            E'.point = GaussianQuarterTurn (GaussianQuarterTurn E.point + g) + g)))) ) := by
  classical
  intro T g R obsId turnAtRoot B C B' C' hB hC E
  obtain ⟨D, hp, _⟩ := turnAtRoot B C (R B) (R C) (obsId _) (obsId _) E
  obtain ⟨D', hp', _⟩ := turnAtRoot (R B) (R C) B' C' hB hC D
  exact ⟨D', by rw [hp', hp]⟩

private theorem evenPackage :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (QuarterTurnSymmetric T) → ((
        let junctionData := fun (A B C : ProtoTile) => ∃ (AB : ProtoTile) (BC : ProtoTile) (CA :
            ProtoTile) (ABC : ProtoTile), LatticeTile A ∧ LatticeTile B ∧ LatticeTile C ∧
            LatticeTile AB ∧ LatticeTile BC ∧ LatticeTile CA ∧ LatticeTile ABC ∧ Disjoint A.cells
            B.cells ∧ Disjoint B.cells C.cells ∧ Disjoint C.cells A.cells ∧ (∀ (z : LatticeCell),
            z ∈ AB.cells ↔ z ∈ A.cells ∨ z ∈ B.cells) ∧ (∀ (z : LatticeCell), z ∈ BC.cells ↔ z ∈
            B.cells ∨ z ∈ C.cells) ∧ (∀ (z : LatticeCell), z ∈ CA.cells ↔ z ∈ C.cells ∨ z ∈
            A.cells) ∧ (∀ (z : LatticeCell), z ∈ ABC.cells ↔ z ∈ A.cells ∨ z ∈ B.cells ∨ z ∈
            C.cells) ∧ (FootprintEdges A ∩ FootprintEdges B).Nonempty ∧ (FootprintEdges B ∩
            FootprintEdges C).Nonempty ∧ (FootprintEdges C ∩ FootprintEdges A).Nonempty; (∀ (i :
            Fin (3 : ℕ)), ∀ (U : ProtoTile), BandPrototile (q i.succ) U → TileCentroid U -
            TileCentroid T = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ)))) + GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ)))
            → junctionData T (TileTranslation T (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))))
            U) ∧ ∀ (i : Fin (3 : ℕ)), ∀ (U : ProtoTile), ∀ (V : ProtoTile), BandPrototile (q
            i.succ) U → BandPrototile (q (i + (1 : Fin (3 : ℕ))).succ) V → TileCentroid U -
            TileCentroid T = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ)))) + GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ)))
            → TileCentroid V - TileCentroid T = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1
            (q (i + (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))) - GaussianRealPoint
            (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (i + (1 : Fin (3 : ℕ))).succ))) →
            junctionData T U V) → (
        let pLit (i : Fin 3) := TileTranslation (cert.P i true)
          (if i = 0 then -cert.v else if i = 1 then cert.u + cert.v else -cert.u)
        let qLit (i : Fin 3) := TileTranslation (cert.P (i + 1) true)
          (if i = 0 then cert.u else if i = 1 then cert.v else -cert.u - cert.v)
        let markedPoint (i : Fin 3) := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm
            ⟨.J5, if i = 2 then -1 else 0, if i = 1 then 0 else -1⟩)
        (∀ (i : Fin 3), BandPrototile (q i.succ) (pLit i) ∧ BandPrototile (q ((i + 1).succ))
            (qLit i) ∧ TileCentroid (pLit i) - TileCentroid T = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) + GaussianRealPoint
            (BandVectors.1 (q 0) (q i.succ))) ∧ TileCentroid (qLit i) - TileCentroid T = (1 / 2 :
            Real) • (GaussianRealPoint (BandVectors.1 (q ((i + 1).succ)) (q 0)) -
            GaussianRealPoint (BandVectors.1 (q 0) (q ((i + 1).succ))))) → ((∀ (i : Fin 3),
            QuarterTurnSymmetric (pLit i) ∧ QuarterTurnSymmetric (qLit i)) → ((∀ (i : Fin 3), ∀
            (U : ProtoTile), ∀ (V : ProtoTile), (BandPrototile (q i.succ) U) → ((BandPrototile (q
            ((i + 1).succ)) V) → ((TileCentroid U - TileCentroid T = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) + GaussianRealPoint
            (BandVectors.1 (q 0) (q i.succ)))) → ((TileCentroid V - TileCentroid T = (1 / 2 :
            Real) • (GaussianRealPoint (BandVectors.1 (q ((i + 1).succ)) (q 0)) -
            GaussianRealPoint (BandVectors.1 (q 0) (q ((i + 1).succ))))) → (∃ _ :
            ExactTileInterfaceTriple T (TileTranslation T (BandVectors.1 (q i.succ) (q 0))) U, ∃
            t5Data : ExactTileInterfaceTriple T U V, t5Data.point = markedPoint i ∧ (∀ rightData
            : ExactTileInterfaceTriple T (TileTranslation T (BandVectors.1 (q 0) (q i.succ))) U,
            rightData.point = t5Data.point)))))) → ((∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (w :
            GaussianInt), (QuarterTurnSymmetric T) → ((QuarterTurnSymmetric U) →
            ((T.cells.Nonempty) → ((U.cells.Nonempty) → ((Disjoint T.cells U.cells) →
            ((TileCentroid U - TileCentroid T = (1 / 2 : Real) • GaussianRealPoint (w +
            GaussianQuarterTurn w)) → (∀ (E : ExactTileInterfaceTriple T (TileTranslation T w)
            U), ∃ R : ExactTileInterfaceTriple T (TileTranslation T (GaussianQuarterTurn w)) U,
            E.point ≠ R.point))))))) → ((∀ (w : GaussianInt), GaussianQuarterTurn w = (⟨0, 1⟩ :
            GaussianInt) * w) → (∀ (i : Fin 3), ∃ rightData : ExactTileInterfaceTriple T
            (TileTranslation T (BandVectors.1 (q 0) (q i.succ))) (pLit i), ∃ incomingData :
            ExactTileInterfaceTriple T (TileTranslation T (BandVectors.1 (q i.succ) (q 0))) (pLit
            i), ∃ t5Data : ExactTileInterfaceTriple T (pLit i) (qLit i), rightData.point =
            t5Data.point ∧ incomingData.point ≠ t5Data.point))))))) ) := by
  classical
  intro q cfg C₀ T cert hsym junctions pLit qLit markedPoint literalData literalSym unrotated
      markedFromIncoming qmul i
  obtain ⟨L, E, hp, heq⟩ := unrotated i _ _ (literalData i).1 (literalData i).2.1
    (literalData i).2.2.1 (literalData i).2.2.2
  obtain ⟨AB, BC, CA, ABC, hA, hB, hC, hAB, hBC, hCA, hABC,
    hdAB, hdBC, hdCA, _⟩ := junctions.1 i _ (literalData i).1 (literalData i).2.2.1
  have flip := (VectorRecursionLaws q cfg.proper.1).2.2.2.2 cfg.proper i |>.1
  have hc : TileCentroid (pLit i) - TileCentroid T = (1 / 2 : Real) •
      GaussianRealPoint (BandVectors.1 (q i.succ) (q 0) +
        GaussianQuarterTurn (BandVectors.1 (q i.succ) (q 0))) := by
    rw [(literalData i).2.2.1, flip]
    ext <;> simp [GaussianRealPoint, GaussianQuarterTurn, Prod.smul_mk, smul_eq_mul]
  have p := markedFromIncoming T (pLit i) (BandVectors.1 (q i.succ) (q 0))
    hsym (literalSym i).1 (LatticeTileGridStructure T hA).1.1
    (LatticeTileGridStructure _ hC).1.1 hdCA.symm hc L
  rw [qmul, ← flip] at p
  obtain ⟨D, hne⟩ := p
  exact ⟨D, L, E, heq D, by simpa only [← heq D] using hne⟩

private theorem turnDisjoint :
    (by
      classical
      exact
        ∀ (g : GaussianInt), (Function.Injective GaussianQuarterTurn) → (
        let R (Y : ProtoTile) := TileTranslation (TileQuarterTurn Y) g
        ∀ (X : ProtoTile), ∀ (Y : ProtoTile), (Disjoint X.cells Y.cells) → (Disjoint (R X).cells
            (R Y).cells)) ) := by
  classical
  intro g qinj R X Y h
  apply Finset.disjoint_left.mpr
  intro z hzX hzY
  simp only [R, TileTranslation, TileQuarterTurn, Finset.mem_image] at hzX hzY
  obtain ⟨a, ⟨a₀, ha₀, rfl⟩, ha⟩ := hzX
  obtain ⟨b, ⟨b₀, hb₀, rfl⟩, hb⟩ := hzY
  have hab : a₀ = b₀ := by
    apply qinj
    dsimp [GaussianTranslation] at ha hb
    have hh := add_right_cancel (ha.trans hb.symm)
    exact sub_left_injective hh
  exact Finset.disjoint_left.mp h ha₀ (hab ▸ hb₀)

private theorem oddPackage :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (QuarterTurnSymmetric T) → ((
        let junctionData := fun (A B C : ProtoTile) => ∃ (AB : ProtoTile) (BC : ProtoTile) (CA :
            ProtoTile) (ABC : ProtoTile), LatticeTile A ∧ LatticeTile B ∧ LatticeTile C ∧
            LatticeTile AB ∧ LatticeTile BC ∧ LatticeTile CA ∧ LatticeTile ABC ∧ Disjoint A.cells
            B.cells ∧ Disjoint B.cells C.cells ∧ Disjoint C.cells A.cells ∧ (∀ (z : LatticeCell),
            z ∈ AB.cells ↔ z ∈ A.cells ∨ z ∈ B.cells) ∧ (∀ (z : LatticeCell), z ∈ BC.cells ↔ z ∈
            B.cells ∨ z ∈ C.cells) ∧ (∀ (z : LatticeCell), z ∈ CA.cells ↔ z ∈ C.cells ∨ z ∈
            A.cells) ∧ (∀ (z : LatticeCell), z ∈ ABC.cells ↔ z ∈ A.cells ∨ z ∈ B.cells ∨ z ∈
            C.cells) ∧ (FootprintEdges A ∩ FootprintEdges B).Nonempty ∧ (FootprintEdges B ∩
            FootprintEdges C).Nonempty ∧ (FootprintEdges C ∩ FootprintEdges A).Nonempty; (∀ (i :
            Fin (3 : ℕ)), ∀ (U : ProtoTile), BandPrototile (q i.succ) U → TileCentroid U -
            TileCentroid T = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ)))) + GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ)))
            → junctionData T (TileTranslation T (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))))
            U) ∧ ∀ (i : Fin (3 : ℕ)), ∀ (U : ProtoTile), ∀ (V : ProtoTile), BandPrototile (q
            i.succ) U → BandPrototile (q (i + (1 : Fin (3 : ℕ))).succ) V → TileCentroid U -
            TileCentroid T = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ)))) + GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ)))
            → TileCentroid V - TileCentroid T = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1
            (q (i + (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))) - GaussianRealPoint
            (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (i + (1 : Fin (3 : ℕ))).succ))) →
            junctionData T U V) → ((∀ (i : Fin 3), ∀ (U : ProtoTile), (BandPrototile (q i.succ)
            U) → ((TileCentroid U - TileCentroid T = (1 / 2 : Real) • (GaussianRealPoint
            (BandVectors.1 (q i.succ) (q 0)) + GaussianRealPoint (BandVectors.1 (q 0) (q
            i.succ)))) → (Nonempty (ExactTileInterfaceTriple T (TileTranslation T (BandVectors.1
            (q i.succ) (q 0))) U)))) → ((∀ (i : Fin 3), ∀ (U : ProtoTile), ∀ (V : ProtoTile),
            (BandPrototile (q i.succ) U) → ((BandPrototile (q ((i + 1).succ)) V) → ((TileCentroid
            U - TileCentroid T = (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q
            0)) + GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)))) → ((TileCentroid V -
            TileCentroid T = (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (q ((i +
            1).succ)) (q 0)) - GaussianRealPoint (BandVectors.1 (q 0) (q ((i + 1).succ))))) →
            (Nonempty (ExactTileInterfaceTriple T U V)))))) → (
        let pLit (i : Fin 3) := TileTranslation (cert.P i true)
          (if i = 0 then -cert.v else if i = 1 then cert.u + cert.v else -cert.u)
        let qLit (i : Fin 3) := TileTranslation (cert.P (i + 1) true)
          (if i = 0 then cert.u else if i = 1 then cert.v else -cert.u - cert.v)
        (∀ (i : Fin 3), BandPrototile (q i.succ) (pLit i) ∧ BandPrototile (q ((i + 1).succ))
            (qLit i) ∧ TileCentroid (pLit i) - TileCentroid T = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) + GaussianRealPoint
            (BandVectors.1 (q 0) (q i.succ))) ∧ TileCentroid (qLit i) - TileCentroid T = (1 / 2 :
            Real) • (GaussianRealPoint (BandVectors.1 (q ((i + 1).succ)) (q 0)) -
            GaussianRealPoint (BandVectors.1 (q 0) (q ((i + 1).succ))))) → ((∀ (Y : ProtoTile), ∀
            (a : GaussianInt), (QuarterTurnSymmetric Y) → (QuarterTurnSymmetric (TileTranslation
            Y a))) → ((∀ (i : Fin 3), QuarterTurnSymmetric (pLit i) ∧ QuarterTurnSymmetric (qLit
            i)) → (
        let pOdd (i : Fin 3) := TileTranslation (cert.P i false)
          (if i = 0 then cert.u + cert.v else if i = 1 then -cert.u else -cert.v)
        let qOdd (i : Fin 3) := TileTranslation (cert.P (i - 1) false)
          (if i = 0 then cert.u else if i = 1 then cert.v else -cert.u - cert.v)
        let oddPoint (i : Fin 3) := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm
            ⟨.J6, if i = 0 then 1 else 0, if i = 2 then 0 else 1⟩)
        (∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (i : Fin 3), ∀ (a : GaussianInt), TileCentroid (TileTranslation (cert.P i
            false) (-a)) - TileCentroid T = -(TileCentroid (TileTranslation (cert.P i true) a) -
            TileCentroid T)) → ((∀ (i : Fin 3), BandPrototile (q i.succ) (pOdd i) ∧ BandPrototile
            (q ((i - 1).succ)) (qOdd i) ∧ TileCentroid (pOdd i) - TileCentroid T = (1 / 2 : Real)
            • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) * (BandVectors.1 (q i.succ) (q 0) +
            BandVectors.1 (q 0) (q i.succ))) ∧ TileCentroid (qOdd i) - TileCentroid T = (1 / 2 :
            Real) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) * (BandVectors.1 (q 0) (q ((i -
            1).succ)) - BandVectors.1 (q ((i - 1).succ)) (q 0)))) → ((∀ (i : Fin 3), ∀ (U :
            ProtoTile), ∀ (V : ProtoTile), (BandPrototile (q i.succ) U) → ((BandPrototile (q ((i
            - 1).succ)) V) → ((TileCentroid U - TileCentroid T = (1 / 2 : Real) •
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) * (BandVectors.1 (q i.succ) (q 0) +
            BandVectors.1 (q 0) (q i.succ)))) → ((TileCentroid V - TileCentroid T = (1 / 2 :
            Real) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) * (BandVectors.1 (q 0) (q ((i -
            1).succ)) - BandVectors.1 (q ((i - 1).succ)) (q 0)))) → (∀ (rightData :
            ExactTileInterfaceTriple T (TileTranslation T (BandVectors.1 (q 0) (q i.succ))) U), ∀
            (t5Data : ExactTileInterfaceTriple T U V), rightData.point = oddPoint i ∧
            t5Data.point = oddPoint i))))) → (∀ (g : GaussianInt), (∀ (C : CircleCoordinates), ∀
            (Y : ProtoTile), ∀ (U : ProtoTile), (BandPrototile C Y) → ((QuarterTurnSymmetric Y) →
            ((BandPrototile C U) → ((TileCentroid U - TileCentroid T = (-((TileCentroid Y -
            TileCentroid T).2), (TileCentroid Y - TileCentroid T).1)) → ((TileTranslation
            (TileQuarterTurn Y) g).cells = U.cells ∧ ((TileTranslation (TileQuarterTurn Y)
            g).cells = ∅ → (TileTranslation (TileQuarterTurn Y) g).anchor = U.anchor)))))) → ((∀
            (C : CircleCoordinates), ∀ (Y : ProtoTile), ∀ (U : ProtoTile), (BandPrototile C Y) →
            ((QuarterTurnSymmetric Y) → ((BandPrototile C U) → ((TileCentroid U - TileCentroid T
            = -(TileCentroid Y - TileCentroid T)) → ((TileTranslation (TileQuarterTurn
            (TileTranslation (TileQuarterTurn Y) g)) g).cells = U.cells ∧ ((TileTranslation
            (TileQuarterTurn (TileTranslation (TileQuarterTurn Y) g)) g).cells = ∅ →
            (TileTranslation (TileQuarterTurn (TileTranslation (TileQuarterTurn Y) g)) g).anchor
            = U.anchor)))))) → ((∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (w : GaussianInt),
            (QuarterTurnSymmetric T) → ((QuarterTurnSymmetric U) → ((T.cells.Nonempty) →
            ((U.cells.Nonempty) → ((Disjoint T.cells U.cells) → ((TileCentroid U - TileCentroid T
            = (1 / 2 : Real) • GaussianRealPoint (w + GaussianQuarterTurn w)) → (∀ (E :
            ExactTileInterfaceTriple T (TileTranslation T w) U), ∃ R : ExactTileInterfaceTriple T
            (TileTranslation T (GaussianQuarterTurn w)) U, E.point ≠ R.point))))))) → ((∀ (w :
            GaussianInt), GaussianQuarterTurn w = (⟨0, 1⟩ : GaussianInt) * w) → ((∀ (w :
            GaussianInt), GaussianQuarterTurn (GaussianQuarterTurn w) = -w) → (
        let R (Y : ProtoTile) := TileTranslation (TileQuarterTurn Y) g
        ((R T).cells = T.cells ∧ ((R T).cells = ∅ → (R T).anchor = T.anchor)) → ((∀ (B :
            ProtoTile), ∀ (C : ProtoTile), ∀ (B' : ProtoTile), ∀ (C' : ProtoTile), ((R B).cells =
            B'.cells ∧ ((R B).cells = ∅ → (R B).anchor = B'.anchor)) → (((R C).cells = C'.cells ∧
            ((R C).cells = ∅ → (R C).anchor = C'.anchor)) → (∀ (E : ExactTileInterfaceTriple T B
            C), ∃ E' : ExactTileInterfaceTriple T B' C', E'.point = GaussianQuarterTurn E.point +
            g ∧ E'.otherAB = GaussianQuarterTurn E.otherAB + g ∧ E'.otherBC = GaussianQuarterTurn
            E.otherBC + g ∧ E'.otherCA = GaussianQuarterTurn E.otherCA + g))) → ((∀ (a :
            GaussianInt), (R (TileTranslation T a)).cells = (TileTranslation T
            (GaussianQuarterTurn a)).cells ∧ ((R (TileTranslation T a)).cells = ∅ → (R
            (TileTranslation T a)).anchor = (TileTranslation T (GaussianQuarterTurn a)).anchor))
            → ((∀ (B : ProtoTile), ∀ (C : ProtoTile), ∀ (B' : ProtoTile), ∀ (C' : ProtoTile), ((R
            (R B)).cells = B'.cells ∧ ((R (R B)).cells = ∅ → (R (R B)).anchor = B'.anchor)) →
            (((R (R C)).cells = C'.cells ∧ ((R (R C)).cells = ∅ → (R (R C)).anchor = C'.anchor))
            → (∀ (E : ExactTileInterfaceTriple T B C), ∃ E' : ExactTileInterfaceTriple T B' C',
            E'.point = GaussianQuarterTurn (GaussianQuarterTurn E.point + g) + g))) → ((∀ (X :
            ProtoTile), ∀ (Y : ProtoTile), (Disjoint X.cells Y.cells) → (Disjoint (R X).cells (R
            Y).cells)) → (∀ (i : Fin 3), ∃ rightData : ExactTileInterfaceTriple T
            (TileTranslation T (BandVectors.1 (q 0) (q i.succ))) (pOdd i), ∃ incomingData :
            ExactTileInterfaceTriple T (TileTranslation T (-BandVectors.1 (q i.succ) (q 0)))
            (pOdd i), ∃ t5Data : ExactTileInterfaceTriple T (pOdd i) (qOdd i), rightData.point =
            t5Data.point ∧ incomingData.point ≠ t5Data.point)))))))))))))))))))) ) := by
  classical
  intro q cfg C₀ T cert hsym junctions incoming evenT5 pLit qLit literalData translated_sym
      literalSym pOdd qOdd oddPoint signedNeg oddLiteralData oddPoints g centeredComparison
      halfTurnComparison markedFromIncoming qmul qneg R rootObs turnAtRoot companionObs
      halfAtRoot turnDisjoint i
  have flip := (VectorRecursionLaws q cfg.proper.1).2.2.2.2 cfg.proper i |>.1
  have hprev : ((i - 1) + 1 : Fin 3) = i := by fin_cases i <;> decide
  have hP : TileCentroid (pOdd i) - TileCentroid T =
      -(TileCentroid (qLit (i - 1)) - TileCentroid T) := by
    fin_cases i
    · simpa [pOdd, qLit, add_comm, show (-1 : Fin 3) = 2 by decide] using
        signedNeg q cfg C₀ T cert 0 (-cert.u - cert.v)
    · simpa [pOdd, qLit] using signedNeg q cfg C₀ T cert 1 cert.u
    · simpa [pOdd, qLit] using signedNeg q cfg C₀ T cert 2 cert.v
  have hQ : TileCentroid (qOdd i) - TileCentroid T =
      -(TileCentroid (pLit (i - 1)) - TileCentroid T) := by
    fin_cases i
    · simpa [qOdd, pLit, show (-1 : Fin 3) = 2 by decide] using
        signedNeg q cfg C₀ T cert 2 (-cert.u)
    · simpa [qOdd, pLit] using signedNeg q cfg C₀ T cert 0 (-cert.v)
    · simpa [qOdd, pLit, sub_eq_add_neg, add_comm, show (-1 : Fin 3) = 2 by decide] using
        signedNeg q cfg C₀ T cert 1 (cert.u + cert.v)
  have hPband : BandPrototile (q i.succ) (qLit (i - 1)) := by
    simpa only [hprev] using (literalData (i - 1)).2.1
  have obsP := halfTurnComparison _ _ _ hPband (literalSym (i - 1)).2
    (oddLiteralData i).1 hP
  have obsQ := halfTurnComparison _ _ _ (literalData (i - 1)).1 (literalSym (i - 1)).1
    (oddLiteralData i).2.1 hQ
  -- Half-turn the predecessor's even triple, then exchange its parents.
  obtain ⟨E₀⟩ := evenT5 (i - 1) _ _ (literalData (i - 1)).1 (literalData (i - 1)).2.1
    (literalData (i - 1)).2.2.1 (literalData (i - 1)).2.2.2
  obtain ⟨EH, _⟩ := halfAtRoot _ _ _ _ obsQ obsP E₀
  obtain ⟨E5, _⟩ := ExactTileInterfaceTripleSwapLast _ _ _ EH
  have obsU := centeredComparison _ _ _ (literalData i).1 (literalSym i).1
    (oddLiteralData i).1 (by
      rw [(oddLiteralData i).2.2.1, (literalData i).2.2.1]
      ext <;> simp [GaussianRealPoint, Prod.smul_mk, smul_eq_mul]; ring)
  obtain ⟨L⟩ := incoming i _ (literalData i).1 (literalData i).2.2.1
  have hComp := companionObs (BandVectors.1 (q i.succ) (q 0))
  rw [qmul, ← flip] at hComp
  obtain ⟨D, _⟩ := turnAtRoot _ _ _ _ hComp obsU L
  obtain ⟨AB, BC, CA, ABC, hA, hB, hC, hAB, hBC, hCA, hABC,
    hdAB, hdBC, hdCA, _⟩ := junctions.1 i _ (literalData i).1 (literalData i).2.2.1
  have hd : Disjoint T.cells (pOdd i).cells := by
    rw [← rootObs.1, ← obsU.1]
    exact turnDisjoint T (pLit i) hdCA.symm
  have hOddLattice : LatticeTile (pOdd i) :=
    (TileDiskAreaCovariance _ _).1.mp (cert.parent_lattice i false)
  have hc : TileCentroid (pOdd i) - TileCentroid T = (1 / 2 : Real) •
      GaussianRealPoint (BandVectors.1 (q 0) (q i.succ) +
        GaussianQuarterTurn (BandVectors.1 (q 0) (q i.succ))) := by
    rw [(oddLiteralData i).2.2.1, flip]
    ext <;> simp [GaussianRealPoint, GaussianQuarterTurn, Prod.smul_mk, smul_eq_mul]; ring
  have p := markedFromIncoming T (pOdd i) (BandVectors.1 (q 0) (q i.succ))
    hsym (translated_sym _ _ (cert.parent_quarter_turn i false))
    (LatticeTileGridStructure T hA).1.1 (LatticeTileGridStructure _ hOddLattice).1.1 hd hc D
  have hq : GaussianQuarterTurn (BandVectors.1 (q 0) (q i.succ)) =
      -BandVectors.1 (q i.succ) (q 0) := by
    rw [flip, ← qmul, qneg]
  rw [hq] at p
  obtain ⟨I, hne⟩ := p
  have hpoints := oddPoints i _ _ (oddLiteralData i).1 (oddLiteralData i).2.1
    (oddLiteralData i).2.2.1 (oddLiteralData i).2.2.2 D E5
  have heq : D.point = E5.point := hpoints.1.trans hpoints.2.symm
  exact ⟨D, I, E5, heq, fun h => hne (heq.trans h.symm)⟩

private theorem retargetPackage :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (R : ProtoTile), ∀ (L :
            ProtoTile), ∀ (rightData : ExactTileInterfaceTriple T R U), ∀ (incomingData :
            ExactTileInterfaceTriple T L U), ∀ (t5Data : ExactTileInterfaceTriple T U V),
            (rightData.point = t5Data.point) → ((incomingData.point ≠ t5Data.point) →
            (incomingData.otherCA = t5Data.point ∧ rightData.otherCA = incomingData.point ∧
            t5Data.otherAB = incomingData.point))) → ((∀ (A : ProtoTile), ∀ (A' : ProtoTile), ∀
            (B : ProtoTile), ∀ (B' : ProtoTile), ∀ (C : ProtoTile), ∀ (C' : ProtoTile), (A.cells
            = A'.cells ∧ (A.cells = ∅ → A.anchor = A'.anchor)) → ((B.cells = B'.cells ∧ (B.cells
            = ∅ → B.anchor = B'.anchor)) → ((C.cells = C'.cells ∧ (C.cells = ∅ → C.anchor =
            C'.anchor)) → (∀ (E : ExactTileInterfaceTriple A B C), ∃ E' :
            ExactTileInterfaceTriple A' B' C', E'.point = E.point ∧ E'.otherAB = E.otherAB ∧
            E'.otherBC = E.otherBC ∧ E'.otherCA = E.otherCA)))) → ((∀ (Y : ProtoTile), Y.cells =
            Y.cells ∧ (Y.cells = ∅ → Y.anchor = Y.anchor)) → (∀ (a : GaussianInt), ∀ (b :
            GaussianInt), ∀ (P : ProtoTile), ∀ (Q : ProtoTile), ∀ (U : ProtoTile), ∀ (V :
            ProtoTile), (P.cells = U.cells ∧ (P.cells = ∅ → P.anchor = U.anchor)) → ((Q.cells =
            V.cells ∧ (Q.cells = ∅ → Q.anchor = V.anchor)) → (∀ (D : ExactTileInterfaceTriple T
            (TileTranslation T a) P), ∀ (L : ExactTileInterfaceTriple T (TileTranslation T b) P),
            ∀ (E : ExactTileInterfaceTriple T P Q), (D.point = E.point) → ((L.point ≠ E.point) →
            (∃ D' : ExactTileInterfaceTriple T (TileTranslation T a) U, ∃ L' :
            ExactTileInterfaceTriple T (TileTranslation T b) U, ∃ E' : ExactTileInterfaceTriple T
            U V, D'.point = E'.point ∧ L'.point ≠ E'.point ∧ L'.otherCA = E'.point ∧ D'.otherCA =
            L'.point ∧ E'.otherAB = L'.point))))))) ) := by
  classical
  intro T endpointRelations tripleRetarget obsId a b P Q U V hP hQ D L E hp hne
  obtain ⟨D', hd, _⟩ := tripleRetarget _ _ _ _ _ _ (obsId T) (obsId _) hP D
  obtain ⟨L', hl, _⟩ := tripleRetarget _ _ _ _ _ _ (obsId T) (obsId _) hP L
  obtain ⟨E', he, _⟩ := tripleRetarget _ _ _ _ _ _ (obsId T) hP hQ E
  have hp' : D'.point = E'.point := hd.trans (hp.trans he.symm)
  have hn' : L'.point ≠ E'.point := by simpa only [hl, he] using hne
  exact ⟨D', L', E', hp', hn', endpointRelations _ _ _ _ D' L' E' hp' hn'⟩

private theorem halfPackage :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (R : ProtoTile), ∀ (L :
            ProtoTile), ∀ (rightData : ExactTileInterfaceTriple T R U), ∀ (incomingData :
            ExactTileInterfaceTriple T L U), ∀ (t5Data : ExactTileInterfaceTriple T U V),
            (rightData.point = t5Data.point) → ((incomingData.point ≠ t5Data.point) →
            (incomingData.otherCA = t5Data.point ∧ rightData.otherCA = incomingData.point ∧
            t5Data.otherAB = incomingData.point))) → (∀ (g : GaussianInt), (Function.Injective
            GaussianQuarterTurn) → (
        let R (Y : ProtoTile) := TileTranslation (TileQuarterTurn Y) g
        (∀ (a : GaussianInt), (R (R (TileTranslation T a))).cells = (TileTranslation T
            (-a)).cells ∧ ((R (R (TileTranslation T a))).cells = ∅ → (R (R (TileTranslation T
            a))).anchor = (TileTranslation T (-a)).anchor)) → ((∀ (B : ProtoTile), ∀ (C :
            ProtoTile), ∀ (B' : ProtoTile), ∀ (C' : ProtoTile), ((R (R B)).cells = B'.cells ∧ ((R
            (R B)).cells = ∅ → (R (R B)).anchor = B'.anchor)) → (((R (R C)).cells = C'.cells ∧
            ((R (R C)).cells = ∅ → (R (R C)).anchor = C'.anchor)) → (∀ (E :
            ExactTileInterfaceTriple T B C), ∃ E' : ExactTileInterfaceTriple T B' C', E'.point =
            GaussianQuarterTurn (GaussianQuarterTurn E.point + g) + g))) → (∀ (a : GaussianInt),
            ∀ (b : GaussianInt), ∀ (P : ProtoTile), ∀ (Q : ProtoTile), ∀ (U : ProtoTile), ∀ (V :
            ProtoTile), ((R (R P)).cells = U.cells ∧ ((R (R P)).cells = ∅ → (R (R P)).anchor =
            U.anchor)) → (((R (R Q)).cells = V.cells ∧ ((R (R Q)).cells = ∅ → (R (R Q)).anchor =
            V.anchor)) → (∀ (D : ExactTileInterfaceTriple T (TileTranslation T a) P), ∀ (L :
            ExactTileInterfaceTriple T (TileTranslation T b) P), ∀ (E : ExactTileInterfaceTriple
            T P Q), (D.point = E.point) → ((L.point ≠ E.point) → (∃ D' : ExactTileInterfaceTriple
            T (TileTranslation T (-a)) U, ∃ L' : ExactTileInterfaceTriple T (TileTranslation T
            (-b)) U, ∃ E' : ExactTileInterfaceTriple T U V, D'.point = E'.point ∧ L'.point ≠
            E'.point ∧ L'.otherCA = E'.point ∧ D'.otherCA = L'.point ∧ E'.otherAB =
            L'.point)))))))) ) := by
  classical
  intro T endpointRelations g qinj R halfCompanionObs halfAtRoot a b P Q U V hP hQ D L E hp hne
  obtain ⟨D', hd⟩ := halfAtRoot _ _ _ _ (halfCompanionObs a) hP D
  obtain ⟨L', hl⟩ := halfAtRoot _ _ _ _ (halfCompanionObs b) hP L
  obtain ⟨E', he⟩ := halfAtRoot _ _ _ _ hP hQ E
  have hp' : D'.point = E'.point := by rw [hd, he, hp]
  have hn' : L'.point ≠ E'.point := by
    intro h
    apply hne
    apply qinj
    apply add_right_cancel (b := g)
    apply qinj
    exact add_right_cancel (hl.symm.trans (h.trans he))
  exact ⟨D', L', E', hp', hn', endpointRelations _ _ _ _ D' L' E' hp' hn'⟩

private theorem realAdd :
    (by
      classical
      exact
        ∀ (a : GaussianInt), ∀ (b : GaussianInt), GaussianRealPoint (a + b) = GaussianRealPoint a
            + GaussianRealPoint b ) := by
  classical
  intro a b
  ext <;> simp [GaussianRealPoint]

private theorem realSub :
    (by
      classical
      exact
        ∀ (a : GaussianInt), ∀ (b : GaussianInt), GaussianRealPoint (a - b) = GaussianRealPoint a
            - GaussianRealPoint b ) := by
  classical
  intro a b
  ext <;> simp [GaussianRealPoint]

end PairedEndpointGeometry

namespace PairedEndpointCertificate

private theorem completePackages :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (R : ProtoTile), ∀ (L : ProtoTile), ∀
            (rightData : ExactTileInterfaceTriple T R U), ∀ (incomingData :
            ExactTileInterfaceTriple T L U), ∀ (t5Data : ExactTileInterfaceTriple T U V),
            (rightData.point = t5Data.point) → ((incomingData.point ≠ t5Data.point) →
            (incomingData.otherCA = t5Data.point ∧ rightData.otherCA = incomingData.point ∧
            t5Data.otherAB = incomingData.point))) → (
        let pLit (i : Fin 3) := TileTranslation (cert.P i true)
          (if i = 0 then -cert.v else if i = 1 then cert.u + cert.v else -cert.u)
        let qLit (i : Fin 3) := TileTranslation (cert.P (i + 1) true)
          (if i = 0 then cert.u else if i = 1 then cert.v else -cert.u - cert.v)
        (∀ (i : Fin 3), BandPrototile (q i.succ) (pLit i) ∧ BandPrototile (q ((i + 1).succ))
            (qLit i) ∧ TileCentroid (pLit i) - TileCentroid T = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) + GaussianRealPoint
            (BandVectors.1 (q 0) (q i.succ))) ∧ TileCentroid (qLit i) - TileCentroid T = (1 / 2 :
            Real) • (GaussianRealPoint (BandVectors.1 (q ((i + 1).succ)) (q 0)) -
            GaussianRealPoint (BandVectors.1 (q 0) (q ((i + 1).succ))))) → ((∀ (Y : ProtoTile), ∀
            (a : GaussianInt), (QuarterTurnSymmetric Y) → (QuarterTurnSymmetric (TileTranslation
            Y a))) → ((∀ (i : Fin 3), QuarterTurnSymmetric (pLit i) ∧ QuarterTurnSymmetric (qLit
            i)) → (
        let pOdd (i : Fin 3) := TileTranslation (cert.P i false)
          (if i = 0 then cert.u + cert.v else if i = 1 then -cert.u else -cert.v)
        let qOdd (i : Fin 3) := TileTranslation (cert.P (i - 1) false)
          (if i = 0 then cert.u else if i = 1 then cert.v else -cert.u - cert.v)
        (∀ (i : Fin 3), BandPrototile (q i.succ) (pOdd i) ∧ BandPrototile (q ((i - 1).succ))
            (qOdd i) ∧ TileCentroid (pOdd i) - TileCentroid T = (1 / 2 : Real) •
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) * (BandVectors.1 (q i.succ) (q 0) +
            BandVectors.1 (q 0) (q i.succ))) ∧ TileCentroid (qOdd i) - TileCentroid T = (1 / 2 :
            Real) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) * (BandVectors.1 (q 0) (q ((i -
            1).succ)) - BandVectors.1 (q ((i - 1).succ)) (q 0)))) → (∀ (g : GaussianInt), (∀ (C :
            CircleCoordinates), ∀ (Y : ProtoTile), ∀ (U : ProtoTile), (BandPrototile C Y) →
            ((QuarterTurnSymmetric Y) → ((BandPrototile C U) → ((TileCentroid U - TileCentroid T
            = -(TileCentroid Y - TileCentroid T)) → ((TileTranslation (TileQuarterTurn
            (TileTranslation (TileQuarterTurn Y) g)) g).cells = U.cells ∧ ((TileTranslation
            (TileQuarterTurn (TileTranslation (TileQuarterTurn Y) g)) g).cells = ∅ →
            (TileTranslation (TileQuarterTurn (TileTranslation (TileQuarterTurn Y) g)) g).anchor
            = U.anchor)))))) → ((∀ (A : ProtoTile), ∀ (A' : ProtoTile), ∀ (B : ProtoTile), ∀ (B'
            : ProtoTile), ∀ (C : ProtoTile), ∀ (C' : ProtoTile), (A.cells = A'.cells ∧ (A.cells =
            ∅ → A.anchor = A'.anchor)) → ((B.cells = B'.cells ∧ (B.cells = ∅ → B.anchor =
            B'.anchor)) → ((C.cells = C'.cells ∧ (C.cells = ∅ → C.anchor = C'.anchor)) → (∀ (E :
            ExactTileInterfaceTriple A B C), ∃ E' : ExactTileInterfaceTriple A' B' C', E'.point =
            E.point ∧ E'.otherAB = E.otherAB ∧ E'.otherBC = E.otherBC ∧ E'.otherCA =
            E.otherCA)))) → ((∀ (w : GaussianInt), GaussianQuarterTurn w = (⟨0, 1⟩ : GaussianInt)
            * w) → ((∀ (w : GaussianInt), GaussianQuarterTurn (GaussianQuarterTurn w) = -w) →
            ((Function.Injective GaussianQuarterTurn) → (
        let R (Y : ProtoTile) := TileTranslation (TileQuarterTurn Y) g
        (∀ (Y : ProtoTile), Y.cells = Y.cells ∧ (Y.cells = ∅ → Y.anchor = Y.anchor)) → ((∀ (a :
            GaussianInt), (R (TileTranslation T a)).cells = (TileTranslation T
            (GaussianQuarterTurn a)).cells ∧ ((R (TileTranslation T a)).cells = ∅ → (R
            (TileTranslation T a)).anchor = (TileTranslation T (GaussianQuarterTurn a)).anchor))
            → ((∀ (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (Z : ProtoTile), (X.cells = Y.cells ∧
            (X.cells = ∅ → X.anchor = Y.anchor)) → ((Y.cells = Z.cells ∧ (Y.cells = ∅ → Y.anchor
            = Z.anchor)) → (X.cells = Z.cells ∧ (X.cells = ∅ → X.anchor = Z.anchor)))) → ((∀ (B :
            ProtoTile), ∀ (C : ProtoTile), ∀ (B' : ProtoTile), ∀ (C' : ProtoTile), ((R (R
            B)).cells = B'.cells ∧ ((R (R B)).cells = ∅ → (R (R B)).anchor = B'.anchor)) → (((R
            (R C)).cells = C'.cells ∧ ((R (R C)).cells = ∅ → (R (R C)).anchor = C'.anchor)) → (∀
            (E : ExactTileInterfaceTriple T B C), ∃ E' : ExactTileInterfaceTriple T B' C',
            E'.point = GaussianQuarterTurn (GaussianQuarterTurn E.point + g) + g))) → ((∀ (i :
            Fin 3), ∃ rightData : ExactTileInterfaceTriple T (TileTranslation T (BandVectors.1 (q
            0) (q i.succ))) (pLit i), ∃ incomingData : ExactTileInterfaceTriple T
            (TileTranslation T (BandVectors.1 (q i.succ) (q 0))) (pLit i), ∃ t5Data :
            ExactTileInterfaceTriple T (pLit i) (qLit i), rightData.point = t5Data.point ∧
            incomingData.point ≠ t5Data.point) → ((∀ (i : Fin 3), ∃ rightData :
            ExactTileInterfaceTriple T (TileTranslation T (BandVectors.1 (q 0) (q i.succ))) (pOdd
            i), ∃ incomingData : ExactTileInterfaceTriple T (TileTranslation T (-BandVectors.1 (q
            i.succ) (q 0))) (pOdd i), ∃ t5Data : ExactTileInterfaceTriple T (pOdd i) (qOdd i),
            rightData.point = t5Data.point ∧ incomingData.point ≠ t5Data.point) → (
        let pairedEndpointData : Fin 3 → Fin 4 → ProtoTile → ProtoTile → Prop :=
          fun i s U V ↦
            let uR := (⟨0, 1⟩ : GaussianInt) ^ s.val *
              (if Even s.val then BandVectors.1 (q 0) (q i.succ)
                else BandVectors.1 (q i.succ) (q 0))
            let uL := (⟨0, 1⟩ : GaussianInt) ^ s.val *
              (if Even s.val then BandVectors.1 (q i.succ) (q 0)
                else BandVectors.1 (q 0) (q i.succ))
            ∃ rightData : ExactTileInterfaceTriple T
                (TileTranslation T uR) U,
              ∃ incomingData : ExactTileInterfaceTriple T
                (TileTranslation T uL) U,
                ∃ t5Data : ExactTileInterfaceTriple T U V,
                  rightData.point = t5Data.point ∧
                  incomingData.point ≠ t5Data.point ∧
                  incomingData.otherCA = t5Data.point ∧
                  rightData.otherCA = incomingData.point ∧
                  t5Data.otherAB = incomingData.point
        (∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (U : ProtoTile), ∀ (V : ProtoTile), BandPrototile (q
            i.succ) U →
          BandPrototile
            (q ((if Even s.val then i + 1 else i - 1).succ)) V →
          TileCentroid U - TileCentroid T = (1 / 2 : Real) •
            GaussianRealPoint
              ((⟨0, 1⟩ : GaussianInt) ^ s.val *
                (BandVectors.1 (q i.succ) (q 0) +
                  BandVectors.1 (q 0) (q i.succ))) →
          TileCentroid V - TileCentroid T = (1 / 2 : Real) •
            GaussianRealPoint
              ((⟨0, 1⟩ : GaussianInt) ^ s.val *
                (if Even s.val then
                  BandVectors.1 (q ((i + 1).succ)) (q 0) -
                    BandVectors.1 (q 0) (q ((i + 1).succ))
                else
                  BandVectors.1 (q 0) (q ((i - 1).succ)) -
                    BandVectors.1 (q ((i - 1).succ)) (q 0))) →
          pairedEndpointData i s U V))))))))))))))))) ) := by
  classical
  intro q cfg C₀ T cert endpointRelations pLit qLit literalData translated_sym literalSym pOdd
      qOdd oddLiteralData g halfTurnComparison tripleRetarget qmul qneg qinj R obsId companionObs
      obsTrans halfAtRoot evenPackage oddPackage
  have retargetPackage (a b : GaussianInt) (P Q U V : ProtoTile)
      (hP : P.cells = U.cells ∧ (P.cells = ∅ → P.anchor = U.anchor))
      (hQ : Q.cells = V.cells ∧ (Q.cells = ∅ → Q.anchor = V.anchor))
      (D : ExactTileInterfaceTriple T (TileTranslation T a) P)
      (L : ExactTileInterfaceTriple T (TileTranslation T b) P)
      (E : ExactTileInterfaceTriple T P Q)
      (hp : D.point = E.point) (hne : L.point ≠ E.point) :
      ∃ D' : ExactTileInterfaceTriple T (TileTranslation T a) U,
        ∃ L' : ExactTileInterfaceTriple T (TileTranslation T b) U,
          ∃ E' : ExactTileInterfaceTriple T U V,
            D'.point = E'.point ∧ L'.point ≠ E'.point ∧
            L'.otherCA = E'.point ∧ D'.otherCA = L'.point ∧ E'.otherAB = L'.point :=
                PairedEndpointGeometry.retargetPackage T endpointRelations tripleRetarget obsId a
                b P Q U V hP hQ D L E hp hne
  have halfPackage (a b : GaussianInt) (P Q U V : ProtoTile)
      (hP : (R (R P)).cells = U.cells ∧ ((R (R P)).cells = ∅ → (R (R P)).anchor = U.anchor))
      (hQ : (R (R Q)).cells = V.cells ∧ ((R (R Q)).cells = ∅ → (R (R Q)).anchor = V.anchor))
      (D : ExactTileInterfaceTriple T (TileTranslation T a) P)
      (L : ExactTileInterfaceTriple T (TileTranslation T b) P)
      (E : ExactTileInterfaceTriple T P Q)
      (hp : D.point = E.point) (hne : L.point ≠ E.point) :
      ∃ D' : ExactTileInterfaceTriple T (TileTranslation T (-a)) U,
        ∃ L' : ExactTileInterfaceTriple T (TileTranslation T (-b)) U,
          ∃ E' : ExactTileInterfaceTriple T U V,
            D'.point = E'.point ∧ L'.point ≠ E'.point ∧
            L'.otherCA = E'.point ∧ D'.otherCA = L'.point ∧ E'.otherAB = L'.point :=
                PairedEndpointGeometry.halfPackage T endpointRelations g qinj
                    (PairedEndpointGeometry.halfCompanionObs T g qneg companionObs
                    (PairedEndpointGeometry.obsTurn g) obsTrans)
                halfAtRoot a b P Q U V hP hQ D L E hp hne
  have realAdd (a b : GaussianInt) :
      GaussianRealPoint (a + b) = GaussianRealPoint a + GaussianRealPoint b :=
          PairedEndpointGeometry.realAdd a b
  have realSub (a b : GaussianInt) :
      GaussianRealPoint (a - b) = GaussianRealPoint a - GaussianRealPoint b :=
          PairedEndpointGeometry.realSub a b
  have realNeg (a : GaussianInt) : GaussianRealPoint (-a) = -GaussianRealPoint a := by
    ext <;> simp [GaussianRealPoint]
  have compare (C : CircleCoordinates) (Y U : ProtoTile)
      (hY : BandPrototile C Y) (hU : BandPrototile C U)
      (hc : TileCentroid U - TileCentroid T = TileCentroid Y - TileCentroid T) :
      Y.cells = U.cells ∧ (Y.cells = ∅ → Y.anchor = U.anchor) :=
    BandPrototileCentroidUnique C Y U hY hU (sub_left_injective hc.symm)
  have flipAll (i : Fin 3) : BandVectors.1 (q 0) (q i.succ) =
      (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q i.succ) (q 0) :=
    (VectorRecursionLaws q cfg.proper.1).2.2.2.2 cfg.proper i |>.1
  have doubleFlip (i : Fin 3) : (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 0) (q i.succ) =
      -BandVectors.1 (q i.succ) (q 0) := by rw [flipAll, ← qmul, ← qmul, qneg]
  have ii2 : (⟨0, 1⟩ : GaussianInt) ^ 2 = -1 := by decide
  have ii3 : (⟨0, 1⟩ : GaussianInt) ^ 3 = -(⟨0, 1⟩ : GaussianInt) := by decide
  dsimp only
  intro i s U V hU hV hcU hcV
  fin_cases s
  · simp only [show Even (0 : Nat) by decide, ite_true, pow_zero, one_mul] at hV hcU hcV
    dsimp only
    rw [ite_eq_left (show Even (0 : Nat) by decide), ite_eq_left (show Even (0 : Nat) by decide),
      pow_zero, one_mul, one_mul]
    obtain ⟨D, L, E, hp, hn⟩ := evenPackage i
    have hP := compare _ _ _ (literalData i).1 hU (by
      rw [(literalData i).2.2.1]; simpa only [realAdd] using hcU)
    have hQ := compare _ _ _ (literalData i).2.1 hV (by
      rw [(literalData i).2.2.2]; simpa only [realSub] using hcV)
    exact retargetPackage _ _ _ _ _ _ hP hQ D L E hp hn
  · simp only [show ¬ Even (1 : Nat) by decide, ite_false, pow_one] at hV hcU hcV
    dsimp only
    rw [ite_eq_right (show ¬ Even (1 : Nat) by decide), ite_eq_right (show ¬ Even (1 : Nat)
        by decide),
      pow_one, ← flipAll i, doubleFlip i]
    obtain ⟨D, L, E, hp, hn⟩ := oddPackage i
    have hP := compare _ _ _ (oddLiteralData i).1 hU (by
      rw [(oddLiteralData i).2.2.1]; exact hcU)
    have hQ := compare _ _ _ (oddLiteralData i).2.1 hV (by
      rw [(oddLiteralData i).2.2.2]; exact hcV)
    simpa only [← flipAll i, doubleFlip i] using
      retargetPackage _ _ _ _ _ _ hP hQ D L E hp hn
  · simp only [show Even (2 : Nat) by decide, ite_true, ii2, neg_one_mul] at hV hcU hcV
    dsimp only
    rw [ite_eq_left (show Even (2 : Nat) by decide), ite_eq_left (show Even (2 : Nat) by decide),
      ii2, neg_one_mul, neg_one_mul]
    obtain ⟨D, L, E, hp, hn⟩ := evenPackage i
    have hP := halfTurnComparison _ _ _ (literalData i).1 (literalSym i).1 hU (by
      rw [(literalData i).2.2.1]
      simpa only [realNeg, realAdd, smul_neg] using hcU)
    have hQ := halfTurnComparison _ _ _ (literalData i).2.1 (literalSym i).2 hV (by
      rw [(literalData i).2.2.2]
      simpa only [realNeg, realSub, smul_neg] using hcV)
    exact halfPackage _ _ _ _ _ _ hP hQ D L E hp hn
  · simp only [show ¬ Even (3 : Nat) by decide, ite_false, ii3] at hV hcU hcV
    dsimp only
    rw [ite_eq_right (show ¬ Even (3 : Nat) by decide), ite_eq_right (show ¬ Even (3 : Nat)
        by decide),
      ii3, neg_mul, neg_mul, ← flipAll i, doubleFlip i, neg_neg]
    obtain ⟨D, L, E, hp, hn⟩ := oddPackage i
    have hP := halfTurnComparison _ _ _ (oddLiteralData i).1
      (translated_sym _ _ (cert.parent_quarter_turn i false)) hU (by
        rw [(oddLiteralData i).2.2.1]
        simpa only [neg_mul, realNeg, smul_neg] using hcU)
    have hQ := halfTurnComparison _ _ _ (oddLiteralData i).2.1
      (translated_sym _ _ (cert.parent_quarter_turn (i - 1) false)) hV (by
        rw [(oddLiteralData i).2.2.2]
        simpa only [neg_mul, realNeg, smul_neg] using hcV)
    have H := halfPackage _ _ _ _ _ _ hP hQ D L E hp hn
    rw [neg_neg] at H
    exact H

end PairedEndpointCertificate

theorem P1BandOrderedGeneralMixedAggregatePairedEndpoints
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T)
    (hsym : QuarterTurnSymmetric T) :
    let pairedEndpointData : Fin 3 → Fin 4 → ProtoTile → ProtoTile → Prop :=
      fun i s U V ↦
        let uR := (⟨0, 1⟩ : GaussianInt) ^ s.val *
          (if Even s.val then BandVectors.1 (q 0) (q i.succ)
            else BandVectors.1 (q i.succ) (q 0))
        let uL := (⟨0, 1⟩ : GaussianInt) ^ s.val *
          (if Even s.val then BandVectors.1 (q i.succ) (q 0)
            else BandVectors.1 (q 0) (q i.succ))
        ∃ rightData : ExactTileInterfaceTriple T
            (TileTranslation T uR) U,
          ∃ incomingData : ExactTileInterfaceTriple T
            (TileTranslation T uL) U,
            ∃ t5Data : ExactTileInterfaceTriple T U V,
              rightData.point = t5Data.point ∧
              incomingData.point ≠ t5Data.point ∧
              incomingData.otherCA = t5Data.point ∧
              rightData.otherCA = incomingData.point ∧
              t5Data.otherAB = incomingData.point
    (∀ (i : Fin 3) (s : Fin 4) (U V : ProtoTile),
      BandPrototile (q i.succ) U →
      BandPrototile
        (q ((if Even s.val then i + 1 else i - 1).succ)) V →
      TileCentroid U - TileCentroid T = (1 / 2 : Real) •
        GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (BandVectors.1 (q i.succ) (q 0) +
              BandVectors.1 (q 0) (q i.succ))) →
      TileCentroid V - TileCentroid T = (1 / 2 : Real) •
        GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (if Even s.val then
              BandVectors.1 (q ((i + 1).succ)) (q 0) -
                BandVectors.1 (q 0) (q ((i + 1).succ))
            else
              BandVectors.1 (q 0) (q ((i - 1).succ)) -
                BandVectors.1 (q ((i - 1).succ)) (q 0))) →
      pairedEndpointData i s U V) := by
-- BODY
  have junctions := P1BandOrderedGeneralMixedAggregateJunctionData q cfg C₀ T cert hsym
  have incoming := PairedEndpointGeometry.incoming q T junctions
  have evenT5 := PairedEndpointGeometry.evenT5 q T junctions
  have endpointRelations := PairedEndpointGeometry.endpointRelations T
  let pLit (i : Fin 3) := TileTranslation (cert.P i true)
    (if i = 0 then -cert.v else if i = 1 then cert.u + cert.v else -cert.u)
  let qLit (i : Fin 3) := TileTranslation (cert.P (i + 1) true)
    (if i = 0 then cert.u else if i = 1 then cert.v else -cert.u - cert.v)
  let markedPoint (i : Fin 3) := cert.unmodified.core.rho
    (cert.unmodified.faceEquiv.symm
      ⟨.J5, if i = 2 then -1 else 0, if i = 1 then 0 else -1⟩)
  have literalData (i : Fin 3) :
      BandPrototile (q i.succ) (pLit i) ∧
      BandPrototile (q ((i + 1).succ)) (qLit i) ∧
      TileCentroid (pLit i) - TileCentroid T = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
          GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) ∧
      TileCentroid (qLit i) - TileCentroid T = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q ((i + 1).succ)) (q 0)) -
          GaussianRealPoint (BandVectors.1 (q 0) (q ((i + 1).succ)))) :=
              PairedEndpointGeometry.literalData q cfg C₀ T cert i
  have translated_sym (Y : ProtoTile) (a : GaussianInt)
      (hY : QuarterTurnSymmetric Y) : QuarterTurnSymmetric (TileTranslation Y a) :=
          PairedEndpointGeometry.translated_sym Y a hY
  have literalSym (i : Fin 3) : QuarterTurnSymmetric (pLit i) ∧
      QuarterTurnSymmetric (qLit i) :=
    ⟨translated_sym _ _ (cert.parent_quarter_turn i true),
      translated_sym _ _ (cert.parent_quarter_turn (i + 1) true)⟩
  -- Keep a translated band-prototile proxy for each geometric centered turn.
  have centeredProxy := PairedEndpointGeometry.centeredProxy translated_sym
  have halfTurnProxy := PairedEndpointGeometry.halfTurnProxy centeredProxy
  have period3 := PairedEndpointGeometry.period3 q
      cfg C₀ T cert
  have unrotated := PairedEndpointGeometry.unrotated q cfg C₀ T cert incoming evenT5 literalData
      (PairedEndpointGeometry.markedMembership q cfg C₀ T cert period3)
  let pOdd (i : Fin 3) := TileTranslation (cert.P i false)
    (if i = 0 then cert.u + cert.v else if i = 1 then -cert.u else -cert.v)
  let qOdd (i : Fin 3) := TileTranslation (cert.P (i - 1) false)
    (if i = 0 then cert.u else if i = 1 then cert.v else -cert.u - cert.v)
  let oddPoint (i : Fin 3) := cert.unmodified.core.rho
    (cert.unmodified.faceEquiv.symm
      ⟨.J6, if i = 0 then 1 else 0, if i = 2 then 0 else 1⟩)
  have signedNeg := PairedEndpointGeometry.signedNeg
  have oddLiteralData (i : Fin 3) :
      BandPrototile (q i.succ) (pOdd i) ∧
      BandPrototile (q ((i - 1).succ)) (qOdd i) ∧
      TileCentroid (pOdd i) - TileCentroid T = (1 / 2 : Real) •
        GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) *
          (BandVectors.1 (q i.succ) (q 0) + BandVectors.1 (q 0) (q i.succ))) ∧
      TileCentroid (qOdd i) - TileCentroid T = (1 / 2 : Real) •
        GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) *
          (BandVectors.1 (q 0) (q ((i - 1).succ)) -
            BandVectors.1 (q ((i - 1).succ)) (q 0))) := PairedEndpointGeometry.oddLiteralData q
                cfg C₀ T cert literalData signedNeg (PairedEndpointGeometry.oddFormulaU)
                    (PairedEndpointGeometry.oddFormulaV) i
  have oddPoints := PairedEndpointGeometry.oddPoints q cfg C₀ T cert oddLiteralData
      (PairedEndpointGeometry.oddMembership q cfg C₀ T cert period3)
  obtain ⟨g, hg, hTcells, hTanchor, hTfoot, hTcent⟩ :=
    QuarterTurnSymmetricCenteredTransport T hsym
  have halfTurnComparison (C : CircleCoordinates) (Y U : ProtoTile)
      (hY : BandPrototile C Y) (hYsym : QuarterTurnSymmetric Y)
      (hU : BandPrototile C U)
      (hcentU : TileCentroid U - TileCentroid T =
        -(TileCentroid Y - TileCentroid T)) :
      (TileTranslation (TileQuarterTurn
        (TileTranslation (TileQuarterTurn Y) g)) g).cells = U.cells ∧
      ((TileTranslation (TileQuarterTurn
        (TileTranslation (TileQuarterTurn Y) g)) g).cells = ∅ →
        (TileTranslation (TileQuarterTurn
          (TileTranslation (TileQuarterTurn Y) g)) g).anchor = U.anchor) :=
              PairedEndpointGeometry.halfTurnComparison T halfTurnProxy g hg C Y U hY hYsym hU
              hcentU
  have tripleRetarget := PairedEndpointGeometry.tripleRetarget
  have tripleTurn := PairedEndpointGeometry.tripleTurn (PairedEndpointGeometry.tripleMap
      (PairedEndpointGeometry.pathMap))
  have turnTranslate := PairedEndpointGeometry.turnTranslate
  have obsTranslate := PairedEndpointGeometry.obsTranslate
  -- A fixed common vertex would force all four incident cells into the parent.
  -- Three centered turns about the parent exchange the two child supports.
  have markedFromIncoming := PairedEndpointGeometry.markedFromIncoming
      (PairedEndpointGeometry.translateZero) (PairedEndpointGeometry.swapFirst)
      (PairedEndpointGeometry.parentTurn tripleRetarget tripleTurn turnTranslate obsTranslate)
      (PairedEndpointGeometry.fixedPointNotCommon)
  have qmul (w : GaussianInt) : GaussianQuarterTurn w = (⟨0, 1⟩ : GaussianInt) * w := by
    ext <;> simp [GaussianQuarterTurn]
  have qneg (w : GaussianInt) : GaussianQuarterTurn (GaussianQuarterTurn w) = -w := by
    ext <;> simp [GaussianQuarterTurn]
  have qinj := PairedEndpointGeometry.qinj
  let R (Y : ProtoTile) := TileTranslation (TileQuarterTurn Y) g
  have rootObs : (R T).cells = T.cells ∧ ((R T).cells = ∅ → (R T).anchor = T.anchor) :=
    ⟨hTcells, fun he => hTanchor (hTcells ▸ he)⟩
  have obsId (Y : ProtoTile) : Y.cells = Y.cells ∧ (Y.cells = ∅ → Y.anchor = Y.anchor) :=
    ⟨rfl, fun _ => rfl⟩
  have turnAtRoot := PairedEndpointGeometry.turnAtRoot T g tripleRetarget tripleTurn rootObs
  have companionObs := PairedEndpointGeometry.companionObs T g turnTranslate obsTranslate rootObs
  have obsTrans (X Y Z : ProtoTile)
      (h : X.cells = Y.cells ∧ (X.cells = ∅ → X.anchor = Y.anchor))
      (k : Y.cells = Z.cells ∧ (Y.cells = ∅ → Y.anchor = Z.anchor)) :
      X.cells = Z.cells ∧ (X.cells = ∅ → X.anchor = Z.anchor) :=
    ⟨h.1.trans k.1, fun he => (h.2 he).trans (k.2 (h.1 ▸ he))⟩
  have halfAtRoot := PairedEndpointGeometry.halfAtRoot T g obsId turnAtRoot
  have evenPackage (i : Fin 3) :
      ∃ rightData : ExactTileInterfaceTriple T
          (TileTranslation T (BandVectors.1 (q 0) (q i.succ))) (pLit i),
        ∃ incomingData : ExactTileInterfaceTriple T
          (TileTranslation T (BandVectors.1 (q i.succ) (q 0))) (pLit i),
          ∃ t5Data : ExactTileInterfaceTriple T (pLit i) (qLit i),
            rightData.point = t5Data.point ∧ incomingData.point ≠ t5Data.point :=
                PairedEndpointGeometry.evenPackage q cfg C₀ T cert hsym junctions literalData
                literalSym unrotated markedFromIncoming qmul i
  have oddPackage (i : Fin 3) :
      ∃ rightData : ExactTileInterfaceTriple T
          (TileTranslation T (BandVectors.1 (q 0) (q i.succ))) (pOdd i),
        ∃ incomingData : ExactTileInterfaceTriple T
          (TileTranslation T (-BandVectors.1 (q i.succ) (q 0))) (pOdd i),
          ∃ t5Data : ExactTileInterfaceTriple T (pOdd i) (qOdd i),
            rightData.point = t5Data.point ∧ incomingData.point ≠ t5Data.point :=
                PairedEndpointGeometry.oddPackage q cfg C₀ T cert hsym junctions incoming evenT5
                literalData translated_sym literalSym signedNeg oddLiteralData oddPoints g
                (PairedEndpointGeometry.centeredComparison T centeredProxy g hg)
                    halfTurnComparison markedFromIncoming qmul qneg rootObs
                turnAtRoot companionObs halfAtRoot (PairedEndpointGeometry.turnDisjoint g qinj) i
  have completePackages :
    let pairedEndpointData : Fin 3 → Fin 4 → ProtoTile → ProtoTile → Prop :=
      fun i s U V ↦
        let uR := (⟨0, 1⟩ : GaussianInt) ^ s.val *
          (if Even s.val then BandVectors.1 (q 0) (q i.succ)
            else BandVectors.1 (q i.succ) (q 0))
        let uL := (⟨0, 1⟩ : GaussianInt) ^ s.val *
          (if Even s.val then BandVectors.1 (q i.succ) (q 0)
            else BandVectors.1 (q 0) (q i.succ))
        ∃ rightData : ExactTileInterfaceTriple T
            (TileTranslation T uR) U,
          ∃ incomingData : ExactTileInterfaceTriple T
            (TileTranslation T uL) U,
            ∃ t5Data : ExactTileInterfaceTriple T U V,
              rightData.point = t5Data.point ∧
              incomingData.point ≠ t5Data.point ∧
              incomingData.otherCA = t5Data.point ∧
              rightData.otherCA = incomingData.point ∧
              t5Data.otherAB = incomingData.point
    (∀ (i : Fin 3) (s : Fin 4) (U V : ProtoTile),
      BandPrototile (q i.succ) U →
      BandPrototile
        (q ((if Even s.val then i + 1 else i - 1).succ)) V →
      TileCentroid U - TileCentroid T = (1 / 2 : Real) •
        GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (BandVectors.1 (q i.succ) (q 0) +
              BandVectors.1 (q 0) (q i.succ))) →
      TileCentroid V - TileCentroid T = (1 / 2 : Real) •
        GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (if Even s.val then
              BandVectors.1 (q ((i + 1).succ)) (q 0) -
                BandVectors.1 (q 0) (q ((i + 1).succ))
            else
              BandVectors.1 (q 0) (q ((i - 1).succ)) -
                BandVectors.1 (q ((i - 1).succ)) (q 0))) →
      pairedEndpointData i s U V) := PairedEndpointCertificate.completePackages q cfg C₀ T cert
          endpointRelations literalData translated_sym literalSym oddLiteralData g
          halfTurnComparison tripleRetarget qmul qneg qinj obsId companionObs obsTrans halfAtRoot
          evenPackage oddPackage
  exact completePackages


end ApollonianSuperharmonic

end
