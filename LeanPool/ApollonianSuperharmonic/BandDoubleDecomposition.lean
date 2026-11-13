/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPrototile
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.BandParentBoundaryGenealogy
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetricCenteredTransport
public import LeanPool.ApollonianSuperharmonic.TouchingTripleCovariance
public import LeanPool.ApollonianSuperharmonic.TouchingTriplePermutations
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: BandDoubleDecomposition]

/-!
# BandDoubleDecomposition

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace DoubleDecompositionProof

private theorem observable :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (X : ProtoTile), ∀ (Y : ProtoTile), T.cells =
            U.cells → (T.cells = ∅ → T.anchor = U.anchor) → (TouchingTriple X T Y ↔
            TouchingTriple X U Y)
    ) := by
  classical
  intro T U X Y he ha
  have obs := ProtoTileObservableExtensionality T U he ha
  have left : TileTouching X T ↔ TileTouching X U := by
    by_cases hz : T.cells = ∅
    · simp only [TileTouching, he, obs.2.1, obs.2.2.1, ha hz]
    · have hz' : U.cells ≠ ∅ := by rwa [← he]
      simp only [TileTouching, hz', false_and, or_false, he,
        obs.2.1, obs.2.2.1]
  have right : TileTouching T Y ↔ TileTouching U Y := by
    by_cases hz : T.cells = ∅
    · simp only [TileTouching, he, obs.2.1, obs.2.2.1, ha hz]
    · have hz' : U.cells ≠ ∅ := by rwa [← he]
      simp only [TileTouching, hz', false_and, he, obs.2.1, obs.2.2.1]
  simp only [TouchingTriple, left, right, obs.2.1]

private theorem preimage :
    (by
      classical
      exact
        ∀ (C : CircleCoordinates), ∀ (W : ProtoTile), BandPrototile C W → QuarterTurnSymmetric W
            → ∃ (W' : ProtoTile), BandPrototile C W' ∧ (TileQuarterTurn W').cells = W.cells ∧
            ((TileQuarterTurn W').cells = ∅ → (TileQuarterTurn W').anchor = W.anchor) ∧
            TileCentroid (TileQuarterTurn W') = TileCentroid W
    ) := by
  classical
  intro C W hW hs
  obtain ⟨u, _, hc, ha, _, hcent⟩ := QuarterTurnSymmetricCenteredTransport W hs
  let v : GaussianInt := ⟨u.im, -u.re⟩
  have he : TileQuarterTurn (TileTranslation W v) =
      TileTranslation (TileQuarterTurn W) u := by
    change ProtoTile.mk _ _ = ProtoTile.mk _ _
    congr 1
    · simp only [TileQuarterTurn, TileTranslation, Finset.image_image]
      congr 1
      funext z
      ext <;> simp [GaussianQuarterTurn, GaussianTranslation, v]; ring
    · ext <;> simp [TileQuarterTurn, TileTranslation, GaussianQuarterTurn,
        GaussianTranslation, v]; ring
  refine ⟨TileTranslation W v, BandPrototileTranslation C W v hW, ?_, ?_, ?_⟩
  · rw [he]; exact hc
  · rw [he]; intro hz; exact ha (hc ▸ hz)
  · rw [he]; exact hcent

private theorem rotatedT5 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
          (∀ (D : CircleCoordinates),
              ∀ (U : ProtoTile),
                BandPrototile D U →
                  D.1.toNat < (q (0 : Fin (4 : ℕ))).1.toNat → QuarterTurnSymmetric U) →
            (∀ (q' : Fin (4 : ℕ) → CircleCoordinates),
                ∀ (T' : ProtoTile),
                  ∀ (U : ProtoTile),
                    ∀ (V : ProtoTile),
                      ProperBandQuadruple q' →
                        BandPrototile (q' (0 : Fin (4 : ℕ))) T' →
                          (q' (0 : Fin (4 : ℕ))).1.toNat < (q (0 : Fin (4 : ℕ))).1.toNat →
                            ∀ (i : Fin (3 : ℕ)),
                              BandPrototile (q' i.succ) U →
                                BandPrototile (q' (i + (1 : Fin (3 : ℕ))).succ) V →
                                TileCentroid U - TileCentroid T' =
                                (1 / 2 : ℝ) •
                                (GaussianRealPoint
                                (BandVectors.1 (q' i.succ) (q' (0 : Fin (4 : ℕ)))) +
                                GaussianRealPoint
                                (BandVectors.1 (q' (0 : Fin (4 : ℕ))) (q' i.succ))) →
                                TileCentroid V - TileCentroid T' =
                                (1 / 2 : ℝ) •
                                (GaussianRealPoint
                                (BandVectors.1 (q' (i + (1 : Fin (3 : ℕ))).succ)
                                (q' (0 : Fin (4 : ℕ)))) -
                                GaussianRealPoint
                                (BandVectors.1 (q' (0 : Fin (4 : ℕ)))
                                (q' (i + (1 : Fin (3 : ℕ))).succ))) →
                                TouchingTriple T' U V) →
              (∀ (T : ProtoTile),
                  ∀ (U : ProtoTile),
                    ∀ (X : ProtoTile),
                      ∀ (Y : ProtoTile),
                        T.cells = U.cells →
                          (T.cells = ∅ → T.anchor = U.anchor) →
                            (TouchingTriple X T Y ↔ TouchingTriple X U Y)) →
                (∀ (C : CircleCoordinates),
                    ∀ (W : ProtoTile),
                      BandPrototile C W →
                        QuarterTurnSymmetric W →
                          ∃ W' : ProtoTile,
                            BandPrototile C W' ∧
                              (TileQuarterTurn W').cells = W.cells ∧
                                ((TileQuarterTurn W').cells = ∅ →
                                (TileQuarterTurn W').anchor = W.anchor) ∧
                                TileCentroid (TileQuarterTurn W') = TileCentroid W) →
                  ∀ (p : Fin (4 : ℕ) → CircleCoordinates),
                    ProperBandQuadruple p →
                      (p (0 : Fin (4 : ℕ))).1.toNat < (q (0 : Fin (4 : ℕ))).1.toNat →
                        ∀ (n : ℕ),
                          ∀ (T : ProtoTile),
                            ∀ (U : ProtoTile),
                              ∀ (V : ProtoTile),
                                BandPrototile (p (0 : Fin (4 : ℕ))) T →
                                BandPrototile (p (2 : Fin (4 : ℕ))) U →
                                BandPrototile (p (3 : Fin (4 : ℕ))) V →
                                TileCentroid U - TileCentroid T =
                                (1 / 2 : ℝ) •
                                (GaussianRealPoint
                                (GaussianQuarterTurn^[n]
                                (BandVectors.1 (p (2 : Fin (4 : ℕ)))
                                (p (0 : Fin (4 : ℕ))))) +
                                GaussianRealPoint
                                (GaussianQuarterTurn^[n]
                                (BandVectors.1 (p (0 : Fin (4 : ℕ)))
                                (p (2 : Fin (4 : ℕ)))))) →
                                TileCentroid V - TileCentroid T =
                                (1 / 2 : ℝ) •
                                (GaussianRealPoint
                                (GaussianQuarterTurn^[n]
                                (BandVectors.1 (p (3 : Fin (4 : ℕ)))
                                (p (0 : Fin (4 : ℕ))))) -
                                GaussianRealPoint
                                (GaussianQuarterTurn^[n]
                                (BandVectors.1 (p (0 : Fin (4 : ℕ)))
                                (p (3 : Fin (4 : ℕ)))))) →
                                TouchingTriple T U V
    ) := by
  classical
  intro q hT2 hT5 observable preimage p hp hsmall
  have hsmall2 : Int.toNat (p 2).1 < Int.toNat (q 0).1 := by
    have hn := (SemiProperForestClassification p hp.1).1 2
    have hl := hp.2 1
    change (p 2).1 < (p 0).1 at hl
    omega
  have hsmall3 : Int.toNat (p 3).1 < Int.toNat (q 0).1 := by
    have hn := (SemiProperForestClassification p hp.1).1 3
    have hl := hp.2 2
    change (p 3).1 < (p 0).1 at hl
    omega
  intro n
  induction n with
  | zero =>
      intro T U V hT hU hV hu hv
      exact hT5 p T U V hp hT hsmall 1 hU hV hu hv
  | succ n ih =>
      intro T U V hT hU hV hu hv
      obtain ⟨T', hT', htcell, htanchor, htcent⟩ :=
        preimage _ T hT (hT2 _ T hT hsmall)
      obtain ⟨U', hU', hucell, huanchor, hucent⟩ :=
        preimage _ U hU (hT2 _ U hU hsmall2)
      obtain ⟨V', hV', hvcell, hvanchor, hvcent⟩ :=
        preimage _ V hV (hT2 _ V hV hsmall3)
      have tc := (TileQuarterTurnFormulas T').2.2.2.2.1.symm.trans htcent
      have uc := (TileQuarterTurnFormulas U').2.2.2.2.1.symm.trans hucent
      have vc := (TileQuarterTurnFormulas V').2.2.2.2.1.symm.trans hvcent
      have tx := congrArg Prod.fst tc
      have ty := congrArg Prod.snd tc
      have ux := congrArg Prod.fst uc
      have uy := congrArg Prod.snd uc
      have vx := congrArg Prod.fst vc
      have vy := congrArg Prod.snd vc
      have hux := congrArg Prod.fst hu
      have huy := congrArg Prod.snd hu
      have hvx := congrArg Prod.fst hv
      have hvy := congrArg Prod.snd hv
      simp only [Prod.fst_sub, one_div, GaussianRealPoint, Int.reduceNeg, Fin.isValue,
          Function.iterate_succ_apply', GaussianQuarterTurn, Int.cast_neg,
          GaussianInt.intCast_im, GaussianInt.intCast_re, Prod.mk_add_mk, Prod.smul_mk,
          smul_eq_mul, Prod.snd_sub, Prod.mk_sub_mk, sub_neg_eq_add] at hux huy hvx hvy
      have h : TouchingTriple T' U' V' := by
        apply ih T' U' V' hT' hU' hV'
        · apply Prod.ext <;> simp [GaussianRealPoint] <;>
            linarith only [hux, huy, tx, ty, ux, uy]
        · apply Prod.ext <;> simp [GaussianRealPoint] <;>
            linarith only [hvx, hvy, tx, ty, vx, vy]
      have h := (TouchingTripleCovariance T' U' V' 0).2.1.mp h
      have h := ((TouchingTriplePermutations _ _ _).mp h).2.1
      have h := (observable _ _ _ _ htcell htanchor).mp h
      have h := ((TouchingTriplePermutations _ _ _).mp h).2.1
      have h := (observable _ _ _ _ hucell huanchor).mp h
      have h := ((TouchingTriplePermutations _ _ _).mp h).1
      have h := (observable _ _ _ _ hvcell hvanchor).mp h
      exact ((TouchingTriplePermutations _ _ _).mp h).1

private theorem hd :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (4 : ℕ) → CircleCoordinates),
            (ProperBandQuadruple r) → ((r (0 : Fin (4 : ℕ)) = q (1 : Fin (4 : ℕ))) → ((r (3 : Fin
            (4 : ℕ)) = q (3 : Fin (4 : ℕ))) → (
        let I : GaussianInt := ⟨0, 1⟩
        let a := BandVectors.1 (q 3) (q 2)
        let b := BandVectors.1 (q 1) (q 3)
        let d := BandVectors.1 (r 1) (r 3)
        (BandVectors.1 (r 3) (r 2) = a) → (d = b - I * a))))
    ) := by
  classical
  intro q r hr hr0 hr3 I a b d hr32
  have step := (VectorRecursionLaws _
    (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hr.1))).2.2.1
  change BandVectors.1 (r 3) (r 0) = BandVectors.1 (r 3) (r 2) - I * d at step
  rw [hr32] at step
  have flip := ((VectorRecursionLaws r hr.1).2.2.2.2 hr 2).1
  change BandVectors.1 (r 0) (r 3) = I * BandVectors.1 (r 3) (r 0) at flip
  have hr03 : BandVectors.1 (r 0) (r 3) = b := by rw [hr0, hr3]
  rw [hr03] at flip
  change b = I * BandVectors.1 (r 3) (r 0) at flip
  calc
    d = I * (a - I * d) - I * a := by ext <;> simp [I]
    _ = b - I * a := by rw [← step, ← flip]

private theorem literal :
    (by
      classical
      exact
        ∀ (t : Fin (4 : ℕ) → CircleCoordinates), (∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (X :
            ProtoTile), ∀ (Y : ProtoTile), (T.cells = U.cells) → ((T.cells = ∅ → T.anchor =
            U.anchor) → (TouchingTriple X T Y ↔ TouchingTriple X U Y))) → (∀ (X : ProtoTile), ∀
            (X' : ProtoTile), ∀ (Y : ProtoTile), ∀ (z : GaussianInt), BandPrototile (t (0 : Fin
            (4 : ℕ))) X → BandPrototile (t (0 : Fin (4 : ℕ))) X' → TileCentroid X' - TileCentroid
            X = GaussianRealPoint z → TouchingTriple X (TileTranslation X z) Y → TouchingTriple X
            X' Y)
    ) := by
  classical
  intro t observable X X' Y z hX hX' hoff h
  have hcent : TileCentroid (TileTranslation X z) = TileCentroid X' := by
    rw [(TileTranslationFormulas X z).2.2.2.2.1]
    change TileCentroid X + GaussianRealPoint z = TileCentroid X'
    rw [← hoff]
    abel
  have eqs := BandPrototileCentroidUnique (t 0) (TileTranslation X z) X'
    (BandPrototileTranslation _ _ _ hX) hX' hcent
  exact (observable _ _ _ _ eqs.1 eqs.2).mp h

private theorem cross1 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (t : Fin (4 : ℕ) → CircleCoordinates), (∀ (T₀
            : ProtoTile), ∀ (T₁ : ProtoTile), ∀ (s : Fin (4 : ℕ)), BandPrototile (t (0 : Fin (4 :
            ℕ))) T₀ → BandPrototile (t (1 : Fin (4 : ℕ))) T₁ → TileCentroid T₁ - TileCentroid T₀
            = (1 / 2 : ℝ) • (GaussianRealPoint (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1 (t
            (1 : Fin (4 : ℕ))) (t (0 : Fin (4 : ℕ))))) + GaussianRealPoint
            (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1 (t (0 : Fin (4 : ℕ))) (t (1 : Fin (4 :
            ℕ)))))) → TouchingTriple T₀ (TileTranslation T₀ (GaussianQuarterTurn^[(↑s : ℕ)]
            (BandVectors.1 (t (1 : Fin (4 : ℕ))) (t (0 : Fin (4 : ℕ)))))) T₁) → (∀ (x : ℝ × ℝ), ∀
            (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (Q : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (S :
            Fin (3 : ℕ) → Bool → ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let a := BandVectors.1 (q 3) (q 2)
        let b := BandVectors.1 (q 1) (q 3)
        (BandVectors.1 (t 1) (t 0) = a) → ((BandVectors.1 (t 0) (t 1) = I * a) → (((TileCentroid
            (P (0 : Fin (3 : ℕ)) true)).1 - x.1 = (2 : ℝ)⁻¹ * (((GaussianInt.toComplex :
            GaussianInt → ℂ) a).re + ((GaussianInt.toComplex : GaussianInt → ℂ) a).im)) →
            (((TileCentroid (P (0 : Fin (3 : ℕ)) true)).2 - x.2 = (2 : ℝ)⁻¹ *
            (((GaussianInt.toComplex : GaussianInt → ℂ) a).im - ((GaussianInt.toComplex :
            GaussianInt → ℂ) a).re)) → (((TileCentroid (P (0 : Fin (3 : ℕ)) false)).1 - x.1 =
            -((2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) a).re +
            ((GaussianInt.toComplex : GaussianInt → ℂ) a).im))) → (((TileCentroid (P (0 : Fin (3
            : ℕ)) false)).2 - x.2 = -((2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ)
            a).im - ((GaussianInt.toComplex : GaussianInt → ℂ) a).re))) → (((TileCentroid (P (1 :
            Fin (3 : ℕ)) true)).1 - x.1 = (2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ)
            b).re + ((GaussianInt.toComplex : GaussianInt → ℂ) b).im)) → (((TileCentroid (P (1 :
            Fin (3 : ℕ)) true)).2 - x.2 = (2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ)
            b).im - ((GaussianInt.toComplex : GaussianInt → ℂ) b).re)) → (((TileCentroid (Q (1 :
            Fin (3 : ℕ)) true)).1 - (TileCentroid (P (0 : Fin (3 : ℕ)) true)).1 = (2 : ℝ)⁻¹ *
            (((GaussianInt.toComplex : GaussianInt → ℂ) b).re + ((GaussianInt.toComplex :
            GaussianInt → ℂ) a).im - (((GaussianInt.toComplex : GaussianInt → ℂ) a).re -
            ((GaussianInt.toComplex : GaussianInt → ℂ) b).im))) → (((TileCentroid (Q (1 : Fin (3
            : ℕ)) true)).2 - (TileCentroid (P (0 : Fin (3 : ℕ)) true)).2 = (2 : ℝ)⁻¹ *
            (((GaussianInt.toComplex : GaussianInt → ℂ) b).im - ((GaussianInt.toComplex :
            GaussianInt → ℂ) a).re - (((GaussianInt.toComplex : GaussianInt → ℂ) b).re +
            ((GaussianInt.toComplex : GaussianInt → ℂ) a).im))) → (((TileCentroid (S (2 : Fin (3
            : ℕ)) false)).1 - (TileCentroid (P (0 : Fin (3 : ℕ)) false)).1 = -((2 : ℝ)⁻¹ *
            (-((GaussianInt.toComplex : GaussianInt → ℂ) a).re - ((GaussianInt.toComplex :
            GaussianInt → ℂ) b).re + -((GaussianInt.toComplex : GaussianInt → ℂ) a).im -
            (-((GaussianInt.toComplex : GaussianInt → ℂ) a).re + (((GaussianInt.toComplex :
            GaussianInt → ℂ) b).im + ((GaussianInt.toComplex : GaussianInt → ℂ) a).im))))) →
            (((TileCentroid (S (2 : Fin (3 : ℕ)) false)).2 - (TileCentroid (P (0 : Fin (3 : ℕ))
            false)).2 = -((2 : ℝ)⁻¹ * (-((GaussianInt.toComplex : GaussianInt → ℂ) a).im -
            ((GaussianInt.toComplex : GaussianInt → ℂ) b).im + ((GaussianInt.toComplex :
            GaussianInt → ℂ) a).re - (-((GaussianInt.toComplex : GaussianInt → ℂ) a).re -
            ((GaussianInt.toComplex : GaussianInt → ℂ) b).re + -((GaussianInt.toComplex :
            GaussianInt → ℂ) a).im)))) → ((BandPrototile (t 0) (Q 1 true)) → ((BandPrototile (t
            0) (P 1 true)) → ((BandPrototile (t 1) (S 2 false)) → ((∀ (X : ProtoTile), ∀ (X' :
            ProtoTile), ∀ (Y : ProtoTile), ∀ (z : GaussianInt), (BandPrototile (t 0) X) →
            ((BandPrototile (t 0) X') → ((TileCentroid X' - TileCentroid X = GaussianRealPoint z)
            → ((TouchingTriple X (TileTranslation X z) Y) → (TouchingTriple X X' Y))))) →
            (TouchingTriple (Q 1 true) (S 2 false) (P 1 true))))))))))))))))))
    ) := by
  classical
  intro q t hT4t x P Q S I a b ht10 ht01 p0x p0y m0x m0y p1x p1y q1x q1y s2x s2y hQt hPpt hSmt
      literal
  have h : TouchingTriple (Q 1 true) (P 1 true) (S 2 false) := by
    refine literal _ _ _ ((GaussianQuarterTurn^[1]) (BandVectors.1 (t 1) (t 0)))
      hQt hPpt ?_ (hT4t _ _ 1 hQt hSmt ?_)
    · apply Prod.ext <;>
        simp [ht10, GaussianRealPoint, GaussianQuarterTurn]
      · linarith only [p0x, q1x, p1x]
      · linarith only [p0y, q1y, p1y]
    · apply Prod.ext <;>
        simp [ht10, ht01, GaussianRealPoint, GaussianQuarterTurn, I,
          ]
      · linarith only [p0x, m0x, q1x, s2x]
      · linarith only [p0y, m0y, q1y, s2y]
  exact ((TouchingTriplePermutations _ _ _).mp h).1

private theorem cross2 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (t : Fin (4 : ℕ) → CircleCoordinates), (∀ (T₀
            : ProtoTile), ∀ (T₁ : ProtoTile), ∀ (s : Fin (4 : ℕ)), BandPrototile (t (0 : Fin (4 :
            ℕ))) T₀ → BandPrototile (t (1 : Fin (4 : ℕ))) T₁ → TileCentroid T₁ - TileCentroid T₀
            = (1 / 2 : ℝ) • (GaussianRealPoint (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1 (t
            (1 : Fin (4 : ℕ))) (t (0 : Fin (4 : ℕ))))) + GaussianRealPoint
            (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1 (t (0 : Fin (4 : ℕ))) (t (1 : Fin (4 :
            ℕ)))))) → TouchingTriple T₀ (TileTranslation T₀ (GaussianQuarterTurn^[(↑s : ℕ)]
            (BandVectors.1 (t (1 : Fin (4 : ℕ))) (t (0 : Fin (4 : ℕ)))))) T₁) → (∀ (x : ℝ × ℝ), ∀
            (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (Q : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (S :
            Fin (3 : ℕ) → Bool → ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let a := BandVectors.1 (q 3) (q 2)
        let b := BandVectors.1 (q 1) (q 3)
        (BandVectors.1 (t 1) (t 0) = a) → ((BandVectors.1 (t 0) (t 1) = I * a) → (((TileCentroid
            (P (0 : Fin (3 : ℕ)) true)).1 - x.1 = (2 : ℝ)⁻¹ * (((GaussianInt.toComplex :
            GaussianInt → ℂ) a).re + ((GaussianInt.toComplex : GaussianInt → ℂ) a).im)) →
            (((TileCentroid (P (0 : Fin (3 : ℕ)) true)).2 - x.2 = (2 : ℝ)⁻¹ *
            (((GaussianInt.toComplex : GaussianInt → ℂ) a).im - ((GaussianInt.toComplex :
            GaussianInt → ℂ) a).re)) → (((TileCentroid (P (0 : Fin (3 : ℕ)) false)).1 - x.1 =
            -((2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) a).re +
            ((GaussianInt.toComplex : GaussianInt → ℂ) a).im))) → (((TileCentroid (P (0 : Fin (3
            : ℕ)) false)).2 - x.2 = -((2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ)
            a).im - ((GaussianInt.toComplex : GaussianInt → ℂ) a).re))) → (((TileCentroid (P (1 :
            Fin (3 : ℕ)) false)).1 - x.1 = -((2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt →
            ℂ) b).re + ((GaussianInt.toComplex : GaussianInt → ℂ) b).im))) → (((TileCentroid (P
            (1 : Fin (3 : ℕ)) false)).2 - x.2 = -((2 : ℝ)⁻¹ * (((GaussianInt.toComplex :
            GaussianInt → ℂ) b).im - ((GaussianInt.toComplex : GaussianInt → ℂ) b).re))) →
            (((TileCentroid (Q (2 : Fin (3 : ℕ)) true)).1 - (TileCentroid (P (0 : Fin (3 : ℕ))
            true)).1 = (2 : ℝ)⁻¹ * (-((GaussianInt.toComplex : GaussianInt → ℂ) a).re -
            ((GaussianInt.toComplex : GaussianInt → ℂ) b).re + -((GaussianInt.toComplex :
            GaussianInt → ℂ) a).im - (-((GaussianInt.toComplex : GaussianInt → ℂ) a).re +
            (((GaussianInt.toComplex : GaussianInt → ℂ) b).im + ((GaussianInt.toComplex :
            GaussianInt → ℂ) a).im)))) → (((TileCentroid (Q (2 : Fin (3 : ℕ)) true)).2 -
            (TileCentroid (P (0 : Fin (3 : ℕ)) true)).2 = (2 : ℝ)⁻¹ * (-((GaussianInt.toComplex :
            GaussianInt → ℂ) a).im - ((GaussianInt.toComplex : GaussianInt → ℂ) b).im +
            ((GaussianInt.toComplex : GaussianInt → ℂ) a).re - (-((GaussianInt.toComplex :
            GaussianInt → ℂ) a).re - ((GaussianInt.toComplex : GaussianInt → ℂ) b).re +
            -((GaussianInt.toComplex : GaussianInt → ℂ) a).im))) → (((TileCentroid (S (1 : Fin (3
            : ℕ)) false)).1 - (TileCentroid (P (0 : Fin (3 : ℕ)) false)).1 = -((2 : ℝ)⁻¹ *
            (((GaussianInt.toComplex : GaussianInt → ℂ) b).re + ((GaussianInt.toComplex :
            GaussianInt → ℂ) a).im - (((GaussianInt.toComplex : GaussianInt → ℂ) a).re -
            ((GaussianInt.toComplex : GaussianInt → ℂ) b).im)))) → (((TileCentroid (S (1 : Fin (3
            : ℕ)) false)).2 - (TileCentroid (P (0 : Fin (3 : ℕ)) false)).2 = -((2 : ℝ)⁻¹ *
            (((GaussianInt.toComplex : GaussianInt → ℂ) b).im - ((GaussianInt.toComplex :
            GaussianInt → ℂ) a).re - (((GaussianInt.toComplex : GaussianInt → ℂ) b).re +
            ((GaussianInt.toComplex : GaussianInt → ℂ) a).im)))) → ((BandPrototile (t 0) (S 1
            false)) → ((BandPrototile (t 0) (P 1 false)) → ((BandPrototile (t 1) (Q 2 true)) →
            ((∀ (X : ProtoTile), ∀ (X' : ProtoTile), ∀ (Y : ProtoTile), ∀ (z : GaussianInt),
            (BandPrototile (t 0) X) → ((BandPrototile (t 0) X') → ((TileCentroid X' -
            TileCentroid X = GaussianRealPoint z) → ((TouchingTriple X (TileTranslation X z) Y) →
            (TouchingTriple X X' Y))))) → (TouchingTriple (Q 2 true) (S 1 false) (P 1
            false))))))))))))))))))
    ) := by
  classical
  intro q t hT4t x P Q S I a b ht10 ht01 p0x p0y m0x m0y m1x m1y q2x q2y s1x s1y hSt hPmt hQpt
      literal
  have h : TouchingTriple (S 1 false) (P 1 false) (Q 2 true) := by
    refine literal _ _ _ ((GaussianQuarterTurn^[3]) (BandVectors.1 (t 1) (t 0)))
      hSt hPmt ?_ (hT4t _ _ 3 hSt hQpt ?_)
    · apply Prod.ext <;>
        simp [ht10, GaussianRealPoint, GaussianQuarterTurn, Function.iterate_succ_apply]
      · linarith only [m0x, s1x, m1x]
      · linarith only [m0y, s1y, m1y]
    · apply Prod.ext <;>
        simp [ht10, ht01, GaussianRealPoint, GaussianQuarterTurn, I,
          Function.iterate_succ_apply]
      · linarith only [p0x, m0x, q2x, s1x]
      · linarith only [p0y, m0y, q2y, s1y]
  exact ((TouchingTriplePermutations _ _ _).mp h).2.2.2.1

private theorem cross3 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (t : Fin (4 : ℕ) → CircleCoordinates), (∀ (T₀
            : ProtoTile), ∀ (T₁ : ProtoTile), ∀ (s : Fin (4 : ℕ)), BandPrototile (t (0 : Fin (4 :
            ℕ))) T₀ → BandPrototile (t (1 : Fin (4 : ℕ))) T₁ → TileCentroid T₁ - TileCentroid T₀
            = (1 / 2 : ℝ) • (GaussianRealPoint (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1 (t
            (1 : Fin (4 : ℕ))) (t (0 : Fin (4 : ℕ))))) + GaussianRealPoint
            (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1 (t (0 : Fin (4 : ℕ))) (t (1 : Fin (4 :
            ℕ)))))) → TouchingTriple T₀ (TileTranslation T₀ (GaussianQuarterTurn^[(↑s : ℕ)]
            (BandVectors.1 (t (1 : Fin (4 : ℕ))) (t (0 : Fin (4 : ℕ)))))) T₁) → (∀ (x : ℝ × ℝ), ∀
            (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (Q : Fin (3 : ℕ) → Bool → ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let a := BandVectors.1 (q 3) (q 2)
        let b := BandVectors.1 (q 1) (q 3)
        (BandVectors.1 (t 1) (t 0) = a) → ((BandVectors.1 (t 0) (t 1) = I * a) → (((TileCentroid
            (P (0 : Fin (3 : ℕ)) true)).1 - x.1 = (2 : ℝ)⁻¹ * (((GaussianInt.toComplex :
            GaussianInt → ℂ) a).re + ((GaussianInt.toComplex : GaussianInt → ℂ) a).im)) →
            (((TileCentroid (P (0 : Fin (3 : ℕ)) true)).2 - x.2 = (2 : ℝ)⁻¹ *
            (((GaussianInt.toComplex : GaussianInt → ℂ) a).im - ((GaussianInt.toComplex :
            GaussianInt → ℂ) a).re)) → (((TileCentroid (P (1 : Fin (3 : ℕ)) true)).1 - x.1 = (2 :
            ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) b).re + ((GaussianInt.toComplex :
            GaussianInt → ℂ) b).im)) → (((TileCentroid (P (1 : Fin (3 : ℕ)) true)).2 - x.2 = (2 :
            ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) b).im - ((GaussianInt.toComplex :
            GaussianInt → ℂ) b).re)) → (((TileCentroid (P (2 : Fin (3 : ℕ)) false)).1 - x.1 =
            -((2 : ℝ)⁻¹ * (-((GaussianInt.toComplex : GaussianInt → ℂ) a).re -
            ((GaussianInt.toComplex : GaussianInt → ℂ) b).re - (((GaussianInt.toComplex :
            GaussianInt → ℂ) b).im + ((GaussianInt.toComplex : GaussianInt → ℂ) a).im)))) →
            (((TileCentroid (P (2 : Fin (3 : ℕ)) false)).2 - x.2 = -((2 : ℝ)⁻¹ *
            (-((GaussianInt.toComplex : GaussianInt → ℂ) a).im - ((GaussianInt.toComplex :
            GaussianInt → ℂ) b).im - (-((GaussianInt.toComplex : GaussianInt → ℂ) a).re -
            ((GaussianInt.toComplex : GaussianInt → ℂ) b).re)))) → (((TileCentroid (Q (1 : Fin (3
            : ℕ)) true)).1 - (TileCentroid (P (0 : Fin (3 : ℕ)) true)).1 = (2 : ℝ)⁻¹ *
            (((GaussianInt.toComplex : GaussianInt → ℂ) b).re + ((GaussianInt.toComplex :
            GaussianInt → ℂ) a).im - (((GaussianInt.toComplex : GaussianInt → ℂ) a).re -
            ((GaussianInt.toComplex : GaussianInt → ℂ) b).im))) → (((TileCentroid (Q (1 : Fin (3
            : ℕ)) true)).2 - (TileCentroid (P (0 : Fin (3 : ℕ)) true)).2 = (2 : ℝ)⁻¹ *
            (((GaussianInt.toComplex : GaussianInt → ℂ) b).im - ((GaussianInt.toComplex :
            GaussianInt → ℂ) a).re - (((GaussianInt.toComplex : GaussianInt → ℂ) b).re +
            ((GaussianInt.toComplex : GaussianInt → ℂ) a).im))) → ((BandPrototile (t 0) (Q 1
            true)) → ((BandPrototile (t 0) (P 1 true)) → ((BandPrototile (t 1) (P 2 false)) → ((∀
            (X : ProtoTile), ∀ (X' : ProtoTile), ∀ (Y : ProtoTile), ∀ (z : GaussianInt),
            (BandPrototile (t 0) X) → ((BandPrototile (t 0) X') → ((TileCentroid X' -
            TileCentroid X = GaussianRealPoint z) → ((TouchingTriple X (TileTranslation X z) Y) →
            (TouchingTriple X X' Y))))) → (TouchingTriple (Q 1 true) (P 1 true) (P 2
            false))))))))))))))))
    ) := by
  classical
  intro q t hT4t x P Q I a b ht10 ht01 p0x p0y p1x p1y m2x m2y q1x q1y hQt hPpt hP2mt literal
  have h : TouchingTriple (P 1 true) (Q 1 true) (P 2 false) := by
    refine literal _ _ _ ((GaussianQuarterTurn^[3]) (BandVectors.1 (t 1) (t 0)))
      hPpt hQt ?_ (hT4t _ _ 3 hPpt hP2mt ?_)
    · apply Prod.ext <;>
        simp [ht10, GaussianRealPoint, GaussianQuarterTurn, Function.iterate_succ_apply]
      · linarith only [p0x, q1x, p1x]
      · linarith only [p0y, q1y, p1y]
    · apply Prod.ext <;>
        simp [ht10, ht01, GaussianRealPoint, GaussianQuarterTurn, I,
          Function.iterate_succ_apply]
      · linarith only [p1x, m2x]
      · linarith only [p1y, m2y]
  exact ((TouchingTriplePermutations _ _ _).mp h).2.1

private theorem cross4 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (t : Fin (4 : ℕ) → CircleCoordinates), (∀ (T₀
            : ProtoTile), ∀ (T₁ : ProtoTile), ∀ (s : Fin (4 : ℕ)), BandPrototile (t (0 : Fin (4 :
            ℕ))) T₀ → BandPrototile (t (1 : Fin (4 : ℕ))) T₁ → TileCentroid T₁ - TileCentroid T₀
            = (1 / 2 : ℝ) • (GaussianRealPoint (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1 (t
            (1 : Fin (4 : ℕ))) (t (0 : Fin (4 : ℕ))))) + GaussianRealPoint
            (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1 (t (0 : Fin (4 : ℕ))) (t (1 : Fin (4 :
            ℕ)))))) → TouchingTriple T₀ (TileTranslation T₀ (GaussianQuarterTurn^[(↑s : ℕ)]
            (BandVectors.1 (t (1 : Fin (4 : ℕ))) (t (0 : Fin (4 : ℕ)))))) T₁) → (∀ (x : ℝ × ℝ), ∀
            (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let a := BandVectors.1 (q 3) (q 2)
        let b := BandVectors.1 (q 1) (q 3)
        (BandVectors.1 (t 1) (t 0) = a) → ((BandVectors.1 (t 0) (t 1) = I * a) → (((TileCentroid
            (P (0 : Fin (3 : ℕ)) false)).1 - x.1 = -((2 : ℝ)⁻¹ * (((GaussianInt.toComplex :
            GaussianInt → ℂ) a).re + ((GaussianInt.toComplex : GaussianInt → ℂ) a).im))) →
            (((TileCentroid (P (0 : Fin (3 : ℕ)) false)).2 - x.2 = -((2 : ℝ)⁻¹ *
            (((GaussianInt.toComplex : GaussianInt → ℂ) a).im - ((GaussianInt.toComplex :
            GaussianInt → ℂ) a).re))) → (((TileCentroid (P (1 : Fin (3 : ℕ)) false)).1 - x.1 =
            -((2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) b).re +
            ((GaussianInt.toComplex : GaussianInt → ℂ) b).im))) → (((TileCentroid (P (1 : Fin (3
            : ℕ)) false)).2 - x.2 = -((2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ)
            b).im - ((GaussianInt.toComplex : GaussianInt → ℂ) b).re))) → (((TileCentroid (P (2 :
            Fin (3 : ℕ)) true)).1 - x.1 = (2 : ℝ)⁻¹ * (-((GaussianInt.toComplex : GaussianInt →
            ℂ) a).re - ((GaussianInt.toComplex : GaussianInt → ℂ) b).re -
            (((GaussianInt.toComplex : GaussianInt → ℂ) b).im + ((GaussianInt.toComplex :
            GaussianInt → ℂ) a).im))) → (((TileCentroid (P (2 : Fin (3 : ℕ)) true)).2 - x.2 = (2
            : ℝ)⁻¹ * (-((GaussianInt.toComplex : GaussianInt → ℂ) a).im - ((GaussianInt.toComplex
            : GaussianInt → ℂ) b).im - (-((GaussianInt.toComplex : GaussianInt → ℂ) a).re -
            ((GaussianInt.toComplex : GaussianInt → ℂ) b).re))) → (((TileCentroid (S (1 : Fin (3
            : ℕ)) false)).1 - (TileCentroid (P (0 : Fin (3 : ℕ)) false)).1 = -((2 : ℝ)⁻¹ *
            (((GaussianInt.toComplex : GaussianInt → ℂ) b).re + ((GaussianInt.toComplex :
            GaussianInt → ℂ) a).im - (((GaussianInt.toComplex : GaussianInt → ℂ) a).re -
            ((GaussianInt.toComplex : GaussianInt → ℂ) b).im)))) → (((TileCentroid (S (1 : Fin (3
            : ℕ)) false)).2 - (TileCentroid (P (0 : Fin (3 : ℕ)) false)).2 = -((2 : ℝ)⁻¹ *
            (((GaussianInt.toComplex : GaussianInt → ℂ) b).im - ((GaussianInt.toComplex :
            GaussianInt → ℂ) a).re - (((GaussianInt.toComplex : GaussianInt → ℂ) b).re +
            ((GaussianInt.toComplex : GaussianInt → ℂ) a).im)))) → ((BandPrototile (t 0) (S 1
            false)) → ((BandPrototile (t 0) (P 1 false)) → ((BandPrototile (t 1) (P 2 true)) →
            ((∀ (X : ProtoTile), ∀ (X' : ProtoTile), ∀ (Y : ProtoTile), ∀ (z : GaussianInt),
            (BandPrototile (t 0) X) → ((BandPrototile (t 0) X') → ((TileCentroid X' -
            TileCentroid X = GaussianRealPoint z) → ((TouchingTriple X (TileTranslation X z) Y) →
            (TouchingTriple X X' Y))))) → (TouchingTriple (S 1 false) (P 1 false) (P 2
            true))))))))))))))))
    ) := by
  classical
  intro q t hT4t x P S I a b ht10 ht01 m0x m0y m1x m1y p2x p2y s1x s1y hSt hPmt hP2pt literal
  have h : TouchingTriple (P 1 false) (S 1 false) (P 2 true) := by
    refine literal _ _ _ ((GaussianQuarterTurn^[1]) (BandVectors.1 (t 1) (t 0)))
      hPmt hSt ?_ (hT4t _ _ 1 hPmt hP2pt ?_)
    · apply Prod.ext <;>
        simp [ht10, GaussianRealPoint, GaussianQuarterTurn]
      · linarith only [m0x, s1x, m1x]
      · linarith only [m0y, s1y, m1y]
    · apply Prod.ext <;>
        simp [ht10, ht01, GaussianRealPoint, GaussianQuarterTurn, I,
          ]
      · linarith only [m1x, p2x]
      · linarith only [m1y, p2y]
  exact ((TouchingTriplePermutations _ _ _).mp h).2.1

private theorem precursors :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
          ∀ (r : Fin (4 : ℕ) → CircleCoordinates),
            ProperBandQuadruple q →
              ProperBandQuadruple r →
                r (0 : Fin (4 : ℕ)) = q (1 : Fin (4 : ℕ)) →
                  r (2 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) →
                    (q (2 : Fin (4 : ℕ))).1 < (q (1 : Fin (4 : ℕ))).1 →
                      (4 : ℤ) ≤ (q (2 : Fin (4 : ℕ))).1 →
                        ∀ (x : ℝ × ℝ),
                          ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile),
                            ∀ (Q : Fin (3 : ℕ) → Bool → ProtoTile),
                              ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
                                (∀ (i : Fin (3 : ℕ)),
                                ∀ (s : Bool), BandPrototile (r i.succ) (Q i s)) →
                                (∀ (i : Fin (3 : ℕ)),
                                ∀ (s : Bool), BandPrototile (r i.succ) (S i s)) →
                                (∀ (p : Fin 4 → CircleCoordinates),
                                ProperBandQuadruple p →
                                Int.toNat (p 0).1 < Int.toNat (q 0).1 →
                                ∀ (n : Nat),
                                ∀ (T : ProtoTile),
                                ∀ (U : ProtoTile),
                                ∀ (V : ProtoTile),
                                BandPrototile (p 0) T →
                                BandPrototile (p 2) U →
                                BandPrototile (p 3) V →
                                TileCentroid U - TileCentroid T =
                                (1 / 2 : Real) •
                                (GaussianRealPoint
                                (GaussianQuarterTurn^[n] (BandVectors.1 (p 2) (p 0))) +
                                GaussianRealPoint
                                (GaussianQuarterTurn^[n] (BandVectors.1 (p 0) (p 2)))) →
                                TileCentroid V - TileCentroid T =
                                (1 / 2 : Real) •
                                (GaussianRealPoint
                                (GaussianQuarterTurn^[n] (BandVectors.1 (p 3) (p 0))) -
                                GaussianRealPoint
                                (GaussianQuarterTurn^[n] (BandVectors.1 (p 0) (p 3)))) →
                                TouchingTriple T U V) →
                                let I : GaussianInt := ⟨0, 1⟩
                              let a := BandVectors.1 (q 3) (q 2)
                              let b := BandVectors.1 (q 1) (q 3)
                              let c := BandVectors.1 (q 2) (q 1)
                              let d := BandVectors.1 (r 1) (r 3)
                              let e := BandVectors.1 (r 2) (r 1)
                              c = -a - b →
                                BandVectors.1 (r 3) (r 2) = a →
                                e = c + I * a →
                                d = b - I * a →
                                (∀ (z : GaussianInt),
                                ∀ (w : GaussianInt), z = I * w → w = -I * z) →
                                (TileCentroid (P (0 : Fin (3 : ℕ)) true)).1 - x.1 =
                                (2 : ℝ)⁻¹ *
                                (((GaussianInt.toComplex : GaussianInt → ℂ) a).re +
                                ((GaussianInt.toComplex : GaussianInt → ℂ) a).im) →
                                (TileCentroid (P (0 : Fin (3 : ℕ)) true)).2 - x.2 =
                                (2 : ℝ)⁻¹ *
                                (((GaussianInt.toComplex : GaussianInt → ℂ) a).im -
                                ((GaussianInt.toComplex : GaussianInt → ℂ) a).re) →
                                (TileCentroid (P (0 : Fin (3 : ℕ)) false)).1 - x.1 =
                                -((2 : ℝ)⁻¹ *
                                (((GaussianInt.toComplex : GaussianInt → ℂ) a).re +
                                ((GaussianInt.toComplex : GaussianInt → ℂ) a).im)) →
                                (TileCentroid (P (0 : Fin (3 : ℕ)) false)).2 - x.2 =
                                -((2 : ℝ)⁻¹ *
                                (((GaussianInt.toComplex : GaussianInt → ℂ) a).im -
                                ((GaussianInt.toComplex : GaussianInt → ℂ) a).re)) →
                                (TileCentroid (Q (0 : Fin (3 : ℕ)) false)).1 -
                                (TileCentroid (P (0 : Fin (3 : ℕ)) true)).1 =
                                -((2 : ℝ)⁻¹ *
                                (((GaussianInt.toComplex : GaussianInt → ℂ) a).re +
                                ((GaussianInt.toComplex : GaussianInt → ℂ) a).im)) →
                                (TileCentroid (Q (0 : Fin (3 : ℕ)) false)).2 -
                                (TileCentroid (P (0 : Fin (3 : ℕ)) true)).2 =
                                -((2 : ℝ)⁻¹ *
                                (((GaussianInt.toComplex : GaussianInt → ℂ) a).im -
                                ((GaussianInt.toComplex : GaussianInt → ℂ) a).re)) →
                                (TileCentroid (Q (1 : Fin (3 : ℕ)) true)).1 -
                                (TileCentroid (P (0 : Fin (3 : ℕ)) true)).1 =
                                (2 : ℝ)⁻¹ *
                                (((GaussianInt.toComplex : GaussianInt → ℂ) b).re +
                                ((GaussianInt.toComplex : GaussianInt → ℂ) a).im -
                                (((GaussianInt.toComplex : GaussianInt → ℂ) a).re -
                                ((GaussianInt.toComplex : GaussianInt → ℂ) b).im)) →
                                (TileCentroid (Q (1 : Fin (3 : ℕ)) true)).2 -
                                (TileCentroid (P (0 : Fin (3 : ℕ)) true)).2 =
                                (2 : ℝ)⁻¹ *
                                (((GaussianInt.toComplex : GaussianInt → ℂ) b).im -
                                ((GaussianInt.toComplex : GaussianInt → ℂ) a).re -
                                (((GaussianInt.toComplex : GaussianInt → ℂ) b).re +
                                ((GaussianInt.toComplex : GaussianInt → ℂ) a).im)) →
                                (TileCentroid (Q (2 : Fin (3 : ℕ)) true)).1 -
                                (TileCentroid (P (0 : Fin (3 : ℕ)) true)).1 =
                                (2 : ℝ)⁻¹ *
                                (-((GaussianInt.toComplex : GaussianInt → ℂ) a).re -
                                ((GaussianInt.toComplex : GaussianInt → ℂ) b).re +
                                -((GaussianInt.toComplex : GaussianInt → ℂ) a).im -
                                (-((GaussianInt.toComplex : GaussianInt → ℂ) a).re +
                                (((GaussianInt.toComplex : GaussianInt → ℂ) b).im +
                                ((GaussianInt.toComplex : GaussianInt → ℂ) a).im))) →
                                (TileCentroid (Q (2 : Fin (3 : ℕ)) true)).2 -
                                (TileCentroid (P (0 : Fin (3 : ℕ)) true)).2 =
                                (2 : ℝ)⁻¹ *
                                (-((GaussianInt.toComplex : GaussianInt → ℂ) a).im -
                                ((GaussianInt.toComplex : GaussianInt → ℂ) b).im +
                                ((GaussianInt.toComplex : GaussianInt → ℂ) a).re -
                                (-((GaussianInt.toComplex : GaussianInt → ℂ) a).re -
                                ((GaussianInt.toComplex : GaussianInt → ℂ) b).re +
                                -((GaussianInt.toComplex : GaussianInt → ℂ) a).im)) →
                                (TileCentroid (S (1 : Fin (3 : ℕ)) false)).1 -
                                (TileCentroid (P (0 : Fin (3 : ℕ)) false)).1 =
                                -((2 : ℝ)⁻¹ *
                                (((GaussianInt.toComplex : GaussianInt → ℂ) b).re +
                                ((GaussianInt.toComplex : GaussianInt → ℂ) a).im -
                                (((GaussianInt.toComplex : GaussianInt → ℂ) a).re -
                                ((GaussianInt.toComplex : GaussianInt → ℂ) b).im))) →
                                (TileCentroid (S (1 : Fin (3 : ℕ)) false)).2 -
                                (TileCentroid (P (0 : Fin (3 : ℕ)) false)).2 =
                                -((2 : ℝ)⁻¹ *
                                (((GaussianInt.toComplex : GaussianInt → ℂ) b).im -
                                ((GaussianInt.toComplex : GaussianInt → ℂ) a).re -
                                (((GaussianInt.toComplex : GaussianInt → ℂ) b).re +
                                ((GaussianInt.toComplex : GaussianInt → ℂ) a).im))) →
                                (TileCentroid (S (2 : Fin (3 : ℕ)) false)).1 -
                                (TileCentroid (P (0 : Fin (3 : ℕ)) false)).1 =
                                -((2 : ℝ)⁻¹ *
                                (-((GaussianInt.toComplex : GaussianInt → ℂ) a).re -
                                ((GaussianInt.toComplex : GaussianInt → ℂ) b).re +
                                -((GaussianInt.toComplex : GaussianInt → ℂ) a).im -
                                (-((GaussianInt.toComplex : GaussianInt → ℂ) a).re +
                                (((GaussianInt.toComplex : GaussianInt → ℂ) b).im +
                                ((GaussianInt.toComplex : GaussianInt → ℂ) a).im)))) →
                                (TileCentroid (S (2 : Fin (3 : ℕ)) false)).2 -
                                (TileCentroid (P (0 : Fin (3 : ℕ)) false)).2 =
                                -((2 : ℝ)⁻¹ *
                                (-((GaussianInt.toComplex : GaussianInt → ℂ) a).im -
                                ((GaussianInt.toComplex : GaussianInt → ℂ) b).im +
                                ((GaussianInt.toComplex : GaussianInt → ℂ) a).re -
                                (-((GaussianInt.toComplex : GaussianInt → ℂ) a).re -
                                ((GaussianInt.toComplex : GaussianInt → ℂ) b).re +
                                -((GaussianInt.toComplex : GaussianInt → ℂ) a).im))) →
                                TouchingTriple (Q 1 true) (S 2 false) (Q 0 false) ∧
                                TouchingTriple (Q 2 true) (S 1 false) (Q 0 false)
    ) := by
  classical
  intro q r hq hr hr0 hr2 h12 h2four x P Q S hQ hS rotatedT5 I a b c d e hc hr32 he hd inverse
      p0x p0y m0x m0y q0x q0y q1x q1y q2x q2y s1x s1y s2x s2y
  have rsmall (j : Fin 3) : Int.toNat (r j.succ).1 < Int.toNat (q 0).1 := by
    have hl := hr.2 j
    have hq1 := hq.2 0
    change (q 1).1 < (q 0).1 at hq1
    rw [hr0] at hl
    omega
  rcases BandParentBoundaryGenealogy r hr with roots | first | second | third
  · rcases roots with ⟨_, hz, _⟩ | ⟨_, hz, _⟩ | ⟨_, hz, _⟩ <;>
      rw [hr2] at hz <;> omega
  · obtain ⟨p, hp, _, hp0, hp2, hp3, _, _⟩ := first
    have small : Int.toNat (p 0).1 < Int.toNat (q 0).1 := by
      simpa [hp0] using rsmall 0
    have v20 : BandVectors.1 (p 2) (p 0) = e := by rw [hp2, hp0]
    have v02 : BandVectors.1 (p 0) (p 2) = I * e := by
      have h := ((VectorRecursionLaws p hp.1).2.2.2.2 hp 1).1
      change BandVectors.1 (p 0) (p 2) = I * BandVectors.1 (p 2) (p 0) at h
      simpa only [v20] using h
    have v03 : BandVectors.1 (p 0) (p 3) = d := by rw [hp0, hp3]
    have v30 : BandVectors.1 (p 3) (p 0) = -I * d := by
      have h := ((VectorRecursionLaws p hp.1).2.2.2.2 hp 2).1
      change BandVectors.1 (p 0) (p 3) = I * BandVectors.1 (p 3) (p 0) at h
      exact inverse _ _ (v03.symm.trans h)
    have h0 : BandPrototile (p 0) (Q 0 false) := by
      simpa [hp0] using hQ 0 false
    have h2q : BandPrototile (p 2) (Q 1 true) := by
      simpa [hp2] using hQ 1 true
    have h2s : BandPrototile (p 2) (S 1 false) := by
      simpa [hp2] using hS 1 false
    have h3q : BandPrototile (p 3) (Q 2 true) := by
      simpa [hp3] using hQ 2 true
    have h3s : BandPrototile (p 3) (S 2 false) := by
      simpa [hp3] using hS 2 false
    have one : TouchingTriple (Q 0 false) (Q 1 true) (S 2 false) := by
      apply rotatedT5 p hp small 1 _ _ _ h0 h2q h3s
      · apply Prod.ext <;>
          simp [v20, v02, he, hc, I, GaussianRealPoint, GaussianQuarterTurn,
            ]
        · linarith only [p0x, q0x, q1x]
        · linarith only [p0y, q0y, q1y]
      · apply Prod.ext <;>
          simp [v30, v03, hd, I, GaussianRealPoint, GaussianQuarterTurn,
            ]
        · linarith only [p0x, m0x, q0x, s2x]
        · linarith only [p0y, m0y, q0y, s2y]
    have three : TouchingTriple (Q 0 false) (S 1 false) (Q 2 true) := by
      apply rotatedT5 p hp small 3 _ _ _ h0 h2s h3q
      · apply Prod.ext <;>
          simp [v20, v02, he, hc, I, GaussianRealPoint, GaussianQuarterTurn,
            Function.iterate_succ_apply]
        · linarith only [p0x, m0x, q0x, s1x]
        · linarith only [p0y, m0y, q0y, s1y]
      · apply Prod.ext <;>
          simp [v30, v03, hd, I, GaussianRealPoint, GaussianQuarterTurn,
            Function.iterate_succ_apply]
        · linarith only [p0x, q0x, q2x]
        · linarith only [p0y, q0y, q2y]
    exact ⟨((TouchingTriplePermutations _ _ _).mp one).2.2.1,
      ((TouchingTriplePermutations _ _ _).mp three).2.2.2.2⟩
  · obtain ⟨p, hp, _, hp0, hp2, hp3, _, _⟩ := second
    have small : Int.toNat (p 0).1 < Int.toNat (q 0).1 := by
      simpa [hp0] using rsmall 1
    have v20 : BandVectors.1 (p 2) (p 0) = a := by rw [hp2, hp0, hr32]
    have v02 : BandVectors.1 (p 0) (p 2) = I * a := by
      have h := ((VectorRecursionLaws p hp.1).2.2.2.2 hp 1).1
      change BandVectors.1 (p 0) (p 2) = I * BandVectors.1 (p 2) (p 0) at h
      simpa only [v20] using h
    have v03 : BandVectors.1 (p 0) (p 3) = e := by rw [hp0, hp3]
    have v30 : BandVectors.1 (p 3) (p 0) = -I * e := by
      have h := ((VectorRecursionLaws p hp.1).2.2.2.2 hp 2).1
      change BandVectors.1 (p 0) (p 3) = I * BandVectors.1 (p 3) (p 0) at h
      exact inverse _ _ (v03.symm.trans h)
    have h0q : BandPrototile (p 0) (Q 1 true) := by
      simpa [hp0] using hQ 1 true
    have h0s : BandPrototile (p 0) (S 1 false) := by
      simpa [hp0] using hS 1 false
    have h2s : BandPrototile (p 2) (S 2 false) := by
      simpa [hp2] using hS 2 false
    have h2q : BandPrototile (p 2) (Q 2 true) := by
      simpa [hp2] using hQ 2 true
    have h3 : BandPrototile (p 3) (Q 0 false) := by
      simpa [hp3] using hQ 0 false
    have one : TouchingTriple (Q 1 true) (S 2 false) (Q 0 false) := by
      apply rotatedT5 p hp small 1 _ _ _ h0q h2s h3
      · apply Prod.ext <;>
          simp [v20, v02, I, GaussianRealPoint, GaussianQuarterTurn,
            ]
        · linarith only [p0x, m0x, q1x, s2x]
        · linarith only [p0y, m0y, q1y, s2y]
      · apply Prod.ext <;>
          simp [v30, v03, he, hc, I, GaussianRealPoint, GaussianQuarterTurn,
            ]
        · linarith only [q0x, q1x]
        · linarith only [q0y, q1y]
    have three : TouchingTriple (S 1 false) (Q 2 true) (Q 0 false) := by
      apply rotatedT5 p hp small 3 _ _ _ h0s h2q h3
      · apply Prod.ext <;>
          simp [v20, v02, I, GaussianRealPoint, GaussianQuarterTurn,
            Function.iterate_succ_apply]
        · linarith only [p0x, m0x, s1x, q2x]
        · linarith only [p0y, m0y, s1y, q2y]
      · apply Prod.ext <;>
          simp [v30, v03, he, hc, I, GaussianRealPoint, GaussianQuarterTurn,
            Function.iterate_succ_apply]
        · linarith only [p0x, m0x, q0x, s1x]
        · linarith only [p0y, m0y, q0y, s1y]
    exact ⟨one, ((TouchingTriplePermutations _ _ _).mp three).2.1⟩
  · obtain ⟨p, hp, _, hp0, hp2, hp3, _, _⟩ := third
    have small : Int.toNat (p 0).1 < Int.toNat (q 0).1 := by
      simpa [hp0] using rsmall 2
    have v20 : BandVectors.1 (p 2) (p 0) = d := by rw [hp2, hp0]
    have v02 : BandVectors.1 (p 0) (p 2) = I * d := by
      have h := ((VectorRecursionLaws p hp.1).2.2.2.2 hp 1).1
      change BandVectors.1 (p 0) (p 2) = I * BandVectors.1 (p 2) (p 0) at h
      simpa only [v20] using h
    have v03 : BandVectors.1 (p 0) (p 3) = a := by rw [hp0, hp3, hr32]
    have v30 : BandVectors.1 (p 3) (p 0) = -I * a := by
      have h := ((VectorRecursionLaws p hp.1).2.2.2.2 hp 2).1
      change BandVectors.1 (p 0) (p 3) = I * BandVectors.1 (p 3) (p 0) at h
      exact inverse _ _ (v03.symm.trans h)
    have h0s : BandPrototile (p 0) (S 2 false) := by
      simpa [hp0] using hS 2 false
    have h0q : BandPrototile (p 0) (Q 2 true) := by
      simpa [hp0] using hQ 2 true
    have h2 : BandPrototile (p 2) (Q 0 false) := by
      simpa [hp2] using hQ 0 false
    have h3q : BandPrototile (p 3) (Q 1 true) := by
      simpa [hp3] using hQ 1 true
    have h3s : BandPrototile (p 3) (S 1 false) := by
      simpa [hp3] using hS 1 false
    have one : TouchingTriple (S 2 false) (Q 0 false) (Q 1 true) := by
      apply rotatedT5 p hp small 1 _ _ _ h0s h2 h3q
      · apply Prod.ext <;>
          simp [v20, v02, hd, I, GaussianRealPoint, GaussianQuarterTurn,
            ]
        · linarith only [p0x, m0x, q0x, s2x]
        · linarith only [p0y, m0y, q0y, s2y]
      · apply Prod.ext <;>
          simp [v30, v03, I, GaussianRealPoint, GaussianQuarterTurn,
            ]
        · linarith only [p0x, m0x, q1x, s2x]
        · linarith only [p0y, m0y, q1y, s2y]
    have three : TouchingTriple (Q 2 true) (Q 0 false) (S 1 false) := by
      apply rotatedT5 p hp small 3 _ _ _ h0q h2 h3s
      · apply Prod.ext <;>
          simp [v20, v02, hd, I, GaussianRealPoint, GaussianQuarterTurn,
            Function.iterate_succ_apply]
        · linarith only [q0x, q2x]
        · linarith only [q0y, q2y]
      · apply Prod.ext <;>
          simp [v30, v03, I, GaussianRealPoint, GaussianQuarterTurn,
            Function.iterate_succ_apply]
        · linarith only [p0x, m0x, q2x, s1x]
        · linarith only [p0y, m0y, q2y, s1y]
    exact ⟨((TouchingTriplePermutations _ _ _).mp one).2.2.2.1,
      ((TouchingTriplePermutations _ _ _).mp three).1⟩

end DoubleDecompositionProof

theorem BandDoubleDecomposition :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (r : Fin 4 → CircleCoordinates), ∀ (t : Fin 4 →
        CircleCoordinates), (ProperBandQuadruple q) → ((ProperBandQuadruple r) →
        ((ProperBandQuadruple t) → ((r 0 = q 1) → ((r 2 = q 2) → ((r 3 = q 3) → ((t 0 = q 2) →
        ((t 1 = q 3) → (((q 2).1 < (q 1).1) → ((4 ≤ (q 2).1) → (((q 3).1 ≤ (q 2).1) → (((t 0).1 <
        (q 0).1) → ((∀ (D : CircleCoordinates), ∀ (U : ProtoTile), BandPrototile D U → Int.toNat
        D.1 < Int.toNat (q 0).1 →
      QuarterTurnSymmetric U) → ((∀ (q' : Fin 4 → CircleCoordinates), ∀ (T' : ProtoTile), ∀ (U :
          ProtoTile), ∀ (V : ProtoTile), ProperBandQuadruple q' →
      BandPrototile (q' 0) T' →
      Int.toNat (q' 0).1 < Int.toNat (q 0).1 →
      ∀ i : Fin 3, BandPrototile (q' i.succ) U →
      BandPrototile (q' ((i + 1).succ)) V →
      TileCentroid U - TileCentroid T' = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q' i.succ) (q' 0)) +
          GaussianRealPoint (BandVectors.1 (q' 0) (q' i.succ))) →
      TileCentroid V - TileCentroid T' = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q' ((i + 1).succ)) (q' 0)) -
          GaussianRealPoint (BandVectors.1 (q' 0) (q' ((i + 1).succ)))) →
      TouchingTriple T' U V) → ((∀ (T₀ : ProtoTile), ∀ (T₁ : ProtoTile), ∀ (s : Fin 4),
          BandPrototile (t 0) T₀ → BandPrototile (t 1) T₁ →
      TileCentroid T₁ - TileCentroid T₀ =
        (1 / 2 : Real) •
          (GaussianRealPoint
              ((GaussianQuarterTurn^[s.val])
                (BandVectors.1 (t 1) (t 0))) +
            GaussianRealPoint
              ((GaussianQuarterTurn^[s.val])
                (BandVectors.1 (t 0) (t 1)))) →
      TouchingTriple T₀
        (TileTranslation T₀
          ((GaussianQuarterTurn^[s.val])
            (BandVectors.1 (t 1) (t 0)))) T₁) → (∀ (x : Real × Real), ∀ (P : Fin 3 → Bool →
                ProtoTile), ∀ (Q : Fin 3 → Bool → ProtoTile), ∀ (S : Fin 3 → Bool → ProtoTile),
                (∀ i, ∀ s, BandPrototile (q i.succ) (P i s)) → ((∀ i, ∀ s, BandPrototile (r
                i.succ) (Q i s)) → ((∀ i, ∀ s, BandPrototile (r i.succ) (S i s)) → ((∀ i, ∀ s,
                TileCentroid (P i s) - x =
        (if s = true then (1 : Real) else -1) •
          ((1 / 2 : Real) •
            (GaussianRealPoint
                (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))) -
              (-((GaussianRealPoint
                  (BandVectors.1 (q ((i + 2).succ))
                    (q ((i + 1).succ)))).2),
                (GaussianRealPoint
                  (BandVectors.1 (q ((i + 2).succ))
                    (q ((i + 1).succ)))).1)))) → ((∀ i, ∀ s, TileCentroid (Q i s) - TileCentroid
                        (P 0 true) =
        (if s = true then (1 : Real) else -1) •
          ((1 / 2 : Real) •
            (GaussianRealPoint
                (BandVectors.1 (r ((i + 2).succ)) (r ((i + 1).succ))) -
              (-((GaussianRealPoint
                  (BandVectors.1 (r ((i + 2).succ))
                    (r ((i + 1).succ)))).2),
                (GaussianRealPoint
                  (BandVectors.1 (r ((i + 2).succ))
                    (r ((i + 1).succ)))).1)))) → ((∀ i, ∀ s, TileCentroid (S i s) - TileCentroid
                        (P 0 false) =
        (if s = true then (1 : Real) else -1) •
          ((1 / 2 : Real) •
            (GaussianRealPoint
                (BandVectors.1 (r ((i + 2).succ)) (r ((i + 1).succ))) -
              (-((GaussianRealPoint
                  (BandVectors.1 (r ((i + 2).succ))
                    (r ((i + 1).succ)))).2),
                (GaussianRealPoint
                  (BandVectors.1 (r ((i + 2).succ))
                    (r ((i + 1).succ)))).1)))) → ((Q 0 false).cells = (S 0 true).cells ∧
      ((Q 0 false).cells = ∅ → (Q 0 false).anchor = (S 0 true).anchor) ∧
      TouchingTriple (Q 1 true) (S 2 false) (Q 0 false) ∧
      TouchingTriple (Q 2 true) (S 1 false) (Q 0 false) ∧
      TouchingTriple (Q 1 true) (S 2 false) (P 1 true) ∧
      TouchingTriple (Q 2 true) (S 1 false) (P 1 false) ∧
      TouchingTriple (Q 1 true) (P 1 true) (P 2 false) ∧
      TouchingTriple (S 1 false) (P 1 false) (P 2 true)))))))))))))))))))))) := by
  intro q r t hq hr ht hr0 hr2 hr3 ht0 ht1 h12 h2four h23 htlt hT2 hT5 hT4t x P Q S hP hQ hS
      hPcent hQcent hScent
-- BODY
  have observable (T U X Y : ProtoTile) (he : T.cells = U.cells)
      (ha : T.cells = ∅ → T.anchor = U.anchor) :
      TouchingTriple X T Y ↔ TouchingTriple X U Y := DoubleDecompositionProof.observable T U X Y
          he ha
  have preimage (C : CircleCoordinates) (W : ProtoTile)
      (hW : BandPrototile C W) (hs : QuarterTurnSymmetric W) :
      ∃ W' : ProtoTile, BandPrototile C W' ∧
        (TileQuarterTurn W').cells = W.cells ∧
        ((TileQuarterTurn W').cells = ∅ →
          (TileQuarterTurn W').anchor = W.anchor) ∧
        TileCentroid (TileQuarterTurn W') = TileCentroid W := DoubleDecompositionProof.preimage C
            W hW hs
  -- Smaller T5 is transported through translated quarter-turn preimages.
  have rotatedT5 (p : Fin 4 → CircleCoordinates) (hp : ProperBandQuadruple p)
      (hsmall : Int.toNat (p 0).1 < Int.toNat (q 0).1) :
      ∀ (n : Nat) (T U V : ProtoTile), BandPrototile (p 0) T →
        BandPrototile (p 2) U → BandPrototile (p 3) V →
        TileCentroid U - TileCentroid T = (1 / 2 : Real) •
          (GaussianRealPoint ((GaussianQuarterTurn^[n])
              (BandVectors.1 (p 2) (p 0))) +
            GaussianRealPoint ((GaussianQuarterTurn^[n])
              (BandVectors.1 (p 0) (p 2)))) →
        TileCentroid V - TileCentroid T = (1 / 2 : Real) •
          (GaussianRealPoint ((GaussianQuarterTurn^[n])
              (BandVectors.1 (p 3) (p 0))) -
            GaussianRealPoint ((GaussianQuarterTurn^[n])
              (BandVectors.1 (p 0) (p 3)))) → TouchingTriple T U V :=
                  DoubleDecompositionProof.rotatedT5 q hT2 hT5 observable preimage p hp hsmall
  let I : GaussianInt := ⟨0, 1⟩
  let a := BandVectors.1 (q 3) (q 2)
  let b := BandVectors.1 (q 1) (q 3)
  let c := BandVectors.1 (q 2) (q 1)
  let d := BandVectors.1 (r 1) (r 3)
  let e := BandVectors.1 (r 2) (r 1)
  have hsum := (VectorRecursionLaws q hq.1).1
  have hc : c = -a - b := by
    change a + b + c = 0 at hsum
    calc
      c = (a + b + c) - a - b := by ring
      _ = -a - b := by rw [hsum]; ring
  have hr32 : BandVectors.1 (r 3) (r 2) = a := by rw [hr3, hr2]
  have he : e = c + I * a := by
    have h := (VectorRecursionLaws _ (SemiProperQuadruple.rotate hr.1)).2.2.1
    change BandVectors.1 (r 2) (r 0) = e - I * BandVectors.1 (r 3) (r 2) at h
    rw [hr32, hr2, hr0] at h
    change c = e - I * a at h
    rw [h]
    ring
  have hd : d = b - I * a := DoubleDecompositionProof.hd q r hr hr0 hr3 hr32
  have ht10 : BandVectors.1 (t 1) (t 0) = a := by rw [ht1, ht0]
  have ht01 : BandVectors.1 (t 0) (t 1) = I * a := by
    have h := ((VectorRecursionLaws t ht.1).2.2.2.2 ht 0).1
    change BandVectors.1 (t 0) (t 1) = I * BandVectors.1 (t 1) (t 0) at h
    simpa only [ht10] using h
  have inverse (z w : GaussianInt) (h : z = I * w) : w = -I * z := by
    rw [h]
    ext <;> simp [I]
  have cp0 := hPcent 0 true
  have cm0 := hPcent 0 false
  have cp1 := hPcent 1 true
  have cm1 := hPcent 1 false
  have cp2 := hPcent 2 true
  have cm2 := hPcent 2 false
  have cq0 := hQcent 0 false
  have cs0 := hScent 0 true
  have cq1 := hQcent 1 true
  have cq2 := hQcent 2 true
  have cs1 := hScent 1 false
  have cs2 := hScent 2 false
  change TileCentroid (P 0 true) - x = (1 : Real) • ((1 / 2 : Real) •
    (GaussianRealPoint a - (-(GaussianRealPoint a).2, (GaussianRealPoint a).1))) at cp0
  change TileCentroid (P 0 false) - x = (-1 : Real) • ((1 / 2 : Real) •
    (GaussianRealPoint a - (-(GaussianRealPoint a).2, (GaussianRealPoint a).1))) at cm0
  change TileCentroid (P 1 true) - x = (1 : Real) • ((1 / 2 : Real) •
    (GaussianRealPoint b - (-(GaussianRealPoint b).2, (GaussianRealPoint b).1))) at cp1
  change TileCentroid (P 1 false) - x = (-1 : Real) • ((1 / 2 : Real) •
    (GaussianRealPoint b - (-(GaussianRealPoint b).2, (GaussianRealPoint b).1))) at cm1
  change TileCentroid (P 2 true) - x = (1 : Real) • ((1 / 2 : Real) •
    (GaussianRealPoint c - (-(GaussianRealPoint c).2, (GaussianRealPoint c).1))) at cp2
  change TileCentroid (P 2 false) - x = (-1 : Real) • ((1 / 2 : Real) •
    (GaussianRealPoint c - (-(GaussianRealPoint c).2, (GaussianRealPoint c).1))) at cm2
  change TileCentroid (Q 0 false) - TileCentroid (P 0 true) =
    (-1 : Real) • ((1 / 2 : Real) •
      (GaussianRealPoint (BandVectors.1 (r 3) (r 2)) -
        (-(GaussianRealPoint (BandVectors.1 (r 3) (r 2))).2,
          (GaussianRealPoint (BandVectors.1 (r 3) (r 2))).1))) at cq0
  change TileCentroid (S 0 true) - TileCentroid (P 0 false) =
    (1 : Real) • ((1 / 2 : Real) •
      (GaussianRealPoint (BandVectors.1 (r 3) (r 2)) -
        (-(GaussianRealPoint (BandVectors.1 (r 3) (r 2))).2,
          (GaussianRealPoint (BandVectors.1 (r 3) (r 2))).1))) at cs0
  rw [hr32] at cq0 cs0
  change TileCentroid (Q 0 false) - TileCentroid (P 0 true) =
    (-1 : Real) • ((1 / 2 : Real) •
      (GaussianRealPoint a - (-(GaussianRealPoint a).2, (GaussianRealPoint a).1))) at cq0
  change TileCentroid (S 0 true) - TileCentroid (P 0 false) =
    (1 : Real) • ((1 / 2 : Real) •
      (GaussianRealPoint a - (-(GaussianRealPoint a).2, (GaussianRealPoint a).1))) at cs0
  change TileCentroid (Q 1 true) - TileCentroid (P 0 true) =
    (1 : Real) • ((1 / 2 : Real) •
      (GaussianRealPoint d - (-(GaussianRealPoint d).2, (GaussianRealPoint d).1))) at cq1
  change TileCentroid (Q 2 true) - TileCentroid (P 0 true) =
    (1 : Real) • ((1 / 2 : Real) •
      (GaussianRealPoint e - (-(GaussianRealPoint e).2, (GaussianRealPoint e).1))) at cq2
  change TileCentroid (S 1 false) - TileCentroid (P 0 false) =
    (-1 : Real) • ((1 / 2 : Real) •
      (GaussianRealPoint d - (-(GaussianRealPoint d).2, (GaussianRealPoint d).1))) at cs1
  change TileCentroid (S 2 false) - TileCentroid (P 0 false) =
    (-1 : Real) • ((1 / 2 : Real) •
      (GaussianRealPoint e - (-(GaussianRealPoint e).2, (GaussianRealPoint e).1))) at cs2
  have p0x := congrArg Prod.fst cp0
  have p0y := congrArg Prod.snd cp0
  have m0x := congrArg Prod.fst cm0
  have m0y := congrArg Prod.snd cm0
  have p1x := congrArg Prod.fst cp1
  have p1y := congrArg Prod.snd cp1
  have m1x := congrArg Prod.fst cm1
  have m1y := congrArg Prod.snd cm1
  have p2x := congrArg Prod.fst cp2
  have p2y := congrArg Prod.snd cp2
  have m2x := congrArg Prod.fst cm2
  have m2y := congrArg Prod.snd cm2
  have q0x := congrArg Prod.fst cq0
  have q0y := congrArg Prod.snd cq0
  have s0x := congrArg Prod.fst cs0
  have s0y := congrArg Prod.snd cs0
  have q1x := congrArg Prod.fst cq1
  have q1y := congrArg Prod.snd cq1
  have q2x := congrArg Prod.fst cq2
  have q2y := congrArg Prod.snd cq2
  have s1x := congrArg Prod.fst cs1
  have s1y := congrArg Prod.snd cs1
  have s2x := congrArg Prod.fst cs2
  have s2y := congrArg Prod.snd cs2
  simp only [Fin.isValue, Prod.fst_sub, one_div, GaussianRealPoint, Int.reduceNeg,
      GaussianInt.intCast_re, GaussianInt.intCast_im, Prod.mk_sub_mk, sub_neg_eq_add,
      Prod.smul_mk, smul_eq_mul, one_smul, Prod.snd_sub, neg_smul, Prod.neg_mk]
      at p0x p0y m0x m0y p1x p1y m1x m1y
  simp only [Fin.isValue, Prod.fst_sub, one_div, GaussianRealPoint, Int.reduceNeg, hc,
      Zsqrtd.re_sub, Zsqrtd.re_neg, Int.cast_sub, Int.cast_neg, GaussianInt.intCast_re,
      Zsqrtd.im_sub, Zsqrtd.im_neg, GaussianInt.intCast_im, neg_sub, sub_neg_eq_add,
      Prod.mk_sub_mk, Prod.smul_mk, smul_eq_mul, one_smul, Prod.snd_sub, neg_smul,
      Prod.neg_mk] at p2x p2y m2x m2y q0x q0y s0x s0y
  simp only [Fin.isValue, Prod.fst_sub, one_div, GaussianRealPoint, Int.reduceNeg, hd,
      Zsqrtd.re_sub, Zsqrtd.re_mul, zero_mul, mul_one, neg_mul, one_mul, zero_add,
      sub_neg_eq_add, Int.cast_add, GaussianInt.intCast_re, GaussianInt.intCast_im,
      Zsqrtd.im_sub, Zsqrtd.im_mul, Int.cast_sub, neg_sub, Prod.mk_sub_mk, Prod.smul_mk,
      smul_eq_mul, one_smul, Prod.snd_sub, he, hc, Zsqrtd.re_add, Zsqrtd.re_neg, Int.cast_neg,
      Zsqrtd.im_add, Zsqrtd.im_neg, neg_add_rev, neg_smul, Prod.neg_mk, I]
      at q1x q1y q2x q2y s1x s1y s2x s2y
  have qcenter : TileCentroid (Q 0 false) = x := by
    apply Prod.ext
    · linarith only [p0x, q0x]
    · linarith only [p0y, q0y]
  have scenter : TileCentroid (S 0 true) = x := by
    apply Prod.ext
    · linarith only [m0x, s0x]
    · linarith only [m0y, s0y]
  have common := BandPrototileCentroidUnique (r 1) (Q 0 false) (S 0 true)
    (hQ 0 false) (hS 0 true) (qcenter.trans scenter.symm)
  have hQt : BandPrototile (t 0) (Q 1 true) := by rw [ht0, ← hr2]; exact hQ 1 true
  have hSt : BandPrototile (t 0) (S 1 false) := by rw [ht0, ← hr2]; exact hS 1 false
  have hPpt : BandPrototile (t 0) (P 1 true) := by rw [ht0]; exact hP 1 true
  have hPmt : BandPrototile (t 0) (P 1 false) := by rw [ht0]; exact hP 1 false
  have hQpt : BandPrototile (t 1) (Q 2 true) := by rw [ht1, ← hr3]; exact hQ 2 true
  have hSmt : BandPrototile (t 1) (S 2 false) := by rw [ht1, ← hr3]; exact hS 2 false
  have hP2pt : BandPrototile (t 1) (P 2 true) := by rw [ht1]; exact hP 2 true
  have hP2mt : BandPrototile (t 1) (P 2 false) := by rw [ht1]; exact hP 2 false
  have literal (X X' Y : ProtoTile) (z : GaussianInt)
      (hX : BandPrototile (t 0) X) (hX' : BandPrototile (t 0) X')
      (hoff : TileCentroid X' - TileCentroid X = GaussianRealPoint z)
      (h : TouchingTriple X (TileTranslation X z) Y) : TouchingTriple X X' Y :=
          DoubleDecompositionProof.literal t observable X X' Y z hX hX' hoff h
  have cross1 : TouchingTriple (Q 1 true) (S 2 false) (P 1 true) :=
      DoubleDecompositionProof.cross1 q t hT4t x P Q S ht10 ht01 p0x p0y m0x m0y p1x p1y q1x q1y
      s2x s2y hQt hPpt hSmt literal
  have cross2 : TouchingTriple (Q 2 true) (S 1 false) (P 1 false) :=
      DoubleDecompositionProof.cross2 q t hT4t x P Q S ht10 ht01 p0x p0y m0x m0y m1x m1y q2x q2y
      s1x s1y hSt hPmt hQpt literal
  have cross3 : TouchingTriple (Q 1 true) (P 1 true) (P 2 false) :=
      DoubleDecompositionProof.cross3 q t hT4t x P Q ht10 ht01 p0x p0y p1x p1y m2x m2y q1x q1y
      hQt hPpt hP2mt literal
  have cross4 : TouchingTriple (S 1 false) (P 1 false) (P 2 true) :=
      DoubleDecompositionProof.cross4 q t hT4t x P S ht10 ht01 m0x m0y m1x m1y p2x p2y s1x s1y
      hSt hPmt hP2pt literal
  have precursors : TouchingTriple (Q 1 true) (S 2 false) (Q 0 false) ∧
      TouchingTriple (Q 2 true) (S 1 false) (Q 0 false) := DoubleDecompositionProof.precursors q
          r hq hr hr0 hr2 h12 h2four x P Q S hQ hS rotatedT5 hc hr32 he hd inverse p0x p0y m0x
          m0y q0x q0y q1x q1y q2x q2y s1x s1y s2x s2y
  exact ⟨common.1, common.2, precursors.1, precursors.2, cross1, cross2, cross3, cross4⟩

end ApollonianSuperharmonic

end
