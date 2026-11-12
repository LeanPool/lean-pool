/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.GaussianQuarterTurn
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetricCenteredTransport
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurnFormulas
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.TouchingTripleCovariance
public import LeanPool.ApollonianSuperharmonic.TouchingTriplePermutations

-- [TABLET NODE: OrientedTouchingCovariance]

/-!
# OrientedTouchingCovariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace TouchingCovarianceProof

private theorem quarter_translate :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (x : GaussianInt), TileQuarterTurn (TileTranslation T x) =
            TileTranslation (TileQuarterTurn T) (GaussianQuarterTurn x)
    ) := by
  classical
  intro T x
  cases T with
  | mk cells anchor =>
    have map : (fun z : GaussianInt => GaussianQuarterTurn (z + x) - 1) =
        (fun z : GaussianInt => (GaussianQuarterTurn z - 1) +
          GaussianQuarterTurn x) := by
      funext z
      ext <;> simp [GaussianQuarterTurn, add_comm]; ring
    apply congrArg₂ (fun c : FiniteTile => fun d : GaussianInt =>
      ProtoTile.mk c d)
    · simp [TileQuarterTurn, TileTranslation, GaussianTranslation,
        Finset.image_image, Function.comp_def, map]
    · simp [TileQuarterTurn, TileTranslation, GaussianTranslation,
        GaussianQuarterTurn, add_comm]

private theorem same_touch :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), ∀ (A' : ProtoTile), ∀ (B' :
            ProtoTile), ∀ (C' : ProtoTile), A.cells = A'.cells → B.cells = B'.cells → C.cells =
            C'.cells → (A.cells = ∅ → A.anchor = A'.anchor) → (B.cells = ∅ → B.anchor =
            B'.anchor) → (C.cells = ∅ → C.anchor = C'.anchor) → (TouchingTriple A B C ↔
            TouchingTriple A' B' C')
    ) := by
  classical
  intro A B C A' B' C' ha hb hc haa hbb hcc
  have boundary : ∀ (X X' : ProtoTile), X.cells = X'.cells →
      (X.cells = ∅ → X.anchor = X'.anchor) →
      BoundaryFootprintVertices X = BoundaryFootprintVertices X' := by
    intro X X' hx hxa
    unfold BoundaryFootprintVertices
    have hn : X.cells.Nonempty ↔ X'.cells.Nonempty := by rw [hx]
    simp only [hn]
    split
    · congr 1
      unfold BoundaryFootprintEdges
      rw [hx]
    · have hn' : ¬ X.cells.Nonempty := by
        intro h
        exact ‹¬X'.cells.Nonempty› (hn.mp h)
      have he : X.cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn'
      simp [hxa he]
  have edges : ∀ (X X' : ProtoTile), X.cells = X'.cells →
      BoundaryFootprintEdges X = BoundaryFootprintEdges X' := by
    intro X X' hx
    ext e
    simp [BoundaryFootprintEdges, hx]
  have ba := boundary A A' ha haa
  have bb := boundary B B' hb hbb
  have bc := boundary C C' hc hcc
  have ea := edges A A' ha
  have eb := edges B B' hb
  have ec := edges C C' hc
  unfold TouchingTriple TileTouching
  rw [ea, eb, ec]
  by_cases ha0 : A.cells = ∅ <;> by_cases hb0 : B.cells = ∅ <;>
    by_cases hc0 : C.cells = ∅ <;>
    first
    | simp? [ha0, hb0, hc0, ba, bb, bc,
        haa ha0, hbb hb0, hcc hc0]
    | simp? [ha0, hb0, hc0, ha, hb, hc, ba, bb, bc]
  all_goals first
    | simp [ha0, hb0, hc0, ← haa ha0, ← hbb hb0, ← hcc hc0, ← ha, ← hb, ← hc, ← ba, ← bb, ← bc,
        ← ea, ← eb, ← ec]
    | simp [ha0, hb0, hc0, ← haa ha0, ← hbb hb0, ← ha, ← hb, ← hc, ← ba, ← bb, ← bc, ← ea, ←
        eb, ← ec]
    | simp [ha0, hb0, hc0, ← haa ha0, ← hcc hc0, ← ha, ← hb, ← hc, ← ba, ← bb, ← bc, ← ea, ←
        eb, ← ec]
    | simp [ha0, hb0, hc0, ← hbb hb0, ← hcc hc0, ← ha, ← hb, ← hc, ← ba, ← bb, ← bc, ← ea, ←
        eb, ← ec]
    | simp [ha0, hb0, hc0, ← haa ha0, ← ha, ← hb, ← hc, ← ba, ← bb, ← bc, ← ea, ← eb, ← ec]
    | simp [ha0, hb0, hc0, ← hbb hb0, ← ha, ← hb, ← hc, ← ba, ← bb, ← bc, ← ea, ← eb, ← ec]
    | simp [ha0, hb0, hc0, ← hcc hc0, ← ha, ← hb, ← hc, ← ba, ← bb, ← bc, ← ea, ← eb, ← ec]
    | simp [ha0, hb0, hc0, ← ha, ← hb, ← hc, ← ba, ← bb, ← bc, ← ea, ← eb, ← ec]

private theorem shift_centroid :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (uT : GaussianInt), ∀ (uU : GaussianInt), ∀ (x :
            GaussianInt), ∀ (y : GaussianInt), GaussianRealPoint uT = ((TileCentroid T).1 +
            (TileCentroid T).2, (TileCentroid T).2 - (TileCentroid T).1) → GaussianRealPoint uU =
            ((TileCentroid U).1 + (TileCentroid U).2, (TileCentroid U).2 - (TileCentroid U).1) →
            TileCentroid U - TileCentroid T = (1 / 2 : ℝ) • (GaussianRealPoint
            (GaussianQuarterTurn x) + GaussianRealPoint (GaussianQuarterTurn y)) → TileCentroid
            (TileTranslation U ⟨uU.im, -uU.re⟩) - TileCentroid (TileTranslation T ⟨uT.im,
            -uT.re⟩) = (1 / 2 : ℝ) • (GaussianRealPoint x + GaussianRealPoint y)
    ) := by
  classical
  intro T U uT uU x y huT huU hcent
  rw [(TileTranslationFormulas U _).2.2.2.2.1,
    (TileTranslationFormulas T _).2.2.2.2.1]
  have huT' := congrArg Prod.fst huT
  have huT'' := congrArg Prod.snd huT
  have huU' := congrArg Prod.fst huU
  have huU'' := congrArg Prod.snd huU
  change (uT.re : Real) = _ at huT'
  change (uT.im : Real) = _ at huT''
  change (uU.re : Real) = _ at huU'
  change (uU.im : Real) = _ at huU''
  have h₁ := congrArg Prod.fst hcent
  have h₂ := congrArg Prod.snd hcent
  simp only [GaussianRealPoint, GaussianQuarterTurn] at h₁ h₂ ⊢
  apply Prod.ext <;> dsimp at * <;> norm_num at * <;> linarith

private theorem turn4 :
    (by
      classical
      exact
        (∀ (T : ProtoTile), ∀ (x : GaussianInt), TileQuarterTurn (TileTranslation T x) =
            TileTranslation (TileQuarterTurn T) (GaussianQuarterTurn x)) → ((∀ (A : ProtoTile), ∀
            (B : ProtoTile), ∀ (C : ProtoTile), ∀ (A' : ProtoTile), ∀ (B' : ProtoTile), ∀ (C' :
            ProtoTile), (A.cells = A'.cells) → ((B.cells = B'.cells) → ((C.cells = C'.cells) →
            ((A.cells = ∅ → A.anchor = A'.anchor) → ((B.cells = ∅ → B.anchor = B'.anchor) →
            ((C.cells = ∅ → C.anchor = C'.anchor) → (TouchingTriple A B C ↔ TouchingTriple A' B'
            C'))))))) → (∀ (C : CircleCoordinates), ∀ (D : CircleCoordinates), ∀ (T : ProtoTile),
            ∀ (U : ProtoTile), ∀ (x : GaussianInt), ∀ (y : GaussianInt), BandPrototile C T →
            BandPrototile D U → QuarterTurnSymmetric T → QuarterTurnSymmetric U → (∀ (X :
            ProtoTile), ∀ (Y : ProtoTile), BandPrototile C X → BandPrototile D Y → TileCentroid Y
            - TileCentroid X = (1 / 2 : Real) • (GaussianRealPoint x + GaussianRealPoint y) →
            TouchingTriple X (TileTranslation X x) Y) → (TileCentroid U - TileCentroid T = (1 / 2
            : Real) • (GaussianRealPoint (GaussianQuarterTurn x) + GaussianRealPoint
            (GaussianQuarterTurn y))) → TouchingTriple T (TileTranslation T (GaussianQuarterTurn
            x)) U))
    ) := by
  classical
  intro quarter_translate same_touch C D T U x y hT hU hTs hUs hbase hcent
  obtain ⟨uT, huT, hcellT, hanchorT, hfootT, hcenterT⟩ :=
    QuarterTurnSymmetricCenteredTransport T hTs
  obtain ⟨uU, huU, hcellU, hanchorU, hfootU, hcenterU⟩ :=
    QuarterTurnSymmetricCenteredTransport U hUs
  let vT : GaussianInt := ⟨uT.im, -uT.re⟩
  let vU : GaussianInt := ⟨uU.im, -uU.re⟩
  have hvT : GaussianQuarterTurn vT = uT := by
    dsimp [vT]
    ext <;> simp [GaussianQuarterTurn]
  have hvU : GaussianQuarterTurn vU = uU := by
    dsimp [vU]
    ext <;> simp [GaussianQuarterTurn]
  let T' := TileTranslation T vT
  let U' := TileTranslation U vU
  have hT' : BandPrototile C T' := by
    exact BandPrototileTranslation C T vT hT
  have hU' : BandPrototile D U' := by
    exact BandPrototileTranslation D U vU hU
  have hcent' : TileCentroid U' - TileCentroid T' =
      (1 / 2 : Real) •
        (GaussianRealPoint x + GaussianRealPoint y) := by
    rw [(TileTranslationFormulas U vU).2.2.2.2.1,
      (TileTranslationFormulas T vT).2.2.2.2.1]
    have huT' := congrArg Prod.fst huT
    have huT'' := congrArg Prod.snd huT
    have huU' := congrArg Prod.fst huU
    have huU'' := congrArg Prod.snd huU
    have huT_re : (uT.re : Real) = (TileCentroid T).1 + (TileCentroid T).2 := by
      change (uT.re : Real) = (TileCentroid T).1 + (TileCentroid T).2 at huT'
      exact huT'
    have huT_im : (uT.im : Real) = (TileCentroid T).2 - (TileCentroid T).1 := by
      change (uT.im : Real) = (TileCentroid T).2 - (TileCentroid T).1 at huT''
      exact huT''
    have huU_re : (uU.re : Real) = (TileCentroid U).1 + (TileCentroid U).2 := by
      change (uU.re : Real) = (TileCentroid U).1 + (TileCentroid U).2 at huU'
      exact huU'
    have huU_im : (uU.im : Real) = (TileCentroid U).2 - (TileCentroid U).1 := by
      change (uU.im : Real) = (TileCentroid U).2 - (TileCentroid U).1 at huU''
      exact huU''
    dsimp [vT, vU]
    have h₁ := congrArg Prod.fst hcent
    have h₂ := congrArg Prod.snd hcent
    simp only [GaussianRealPoint, GaussianQuarterTurn] at h₁ h₂ ⊢
    apply Prod.ext <;> dsimp at * <;> norm_num at * <;> linarith
  have hrot : TouchingTriple (TileQuarterTurn T')
      (TileQuarterTurn (TileTranslation T' x))
      (TileQuarterTurn U') := by
    have h := hbase T' U' hT' hU' hcent'
    exact (TouchingTripleCovariance T' (TileTranslation T' x) U' 0).2.1.mp h
  have eT : (TileQuarterTurn T').cells = T.cells := by
    dsimp [T']
    rw [quarter_translate, hvT]
    exact hcellT
  have eU : (TileQuarterTurn U').cells = U.cells := by
    dsimp [U']
    rw [quarter_translate, hvU]
    exact hcellU
  have eM : (TileQuarterTurn (TileTranslation T' x)).cells =
      (TileTranslation T (GaussianQuarterTurn x)).cells := by
    dsimp [T']
    rw [quarter_translate, quarter_translate, hvT]
    change Finset.image (GaussianTranslation (GaussianQuarterTurn x))
      (Finset.image (GaussianTranslation uT) (TileQuarterTurn T).cells) =
      Finset.image (GaussianTranslation (GaussianQuarterTurn x)) T.cells
    have ht : Finset.image (GaussianTranslation uT) (TileQuarterTurn T).cells = T.cells :=
      by
        change (TileTranslation (TileQuarterTurn T) uT).cells = T.cells
        exact hcellT
    rw [ht]
  have aT : (TileQuarterTurn T').cells = ∅ →
      (TileQuarterTurn T').anchor = T.anchor := by
    intro he
    simpa [T', quarter_translate, hvT] using
      hanchorT (by rwa [eT] at he)
  have aU : (TileQuarterTurn U').cells = ∅ →
      (TileQuarterTurn U').anchor = U.anchor := by
    intro he
    simpa [U', quarter_translate, hvU] using
      hanchorU (by rwa [eU] at he)
  have aM : (TileQuarterTurn (TileTranslation T' x)).cells = ∅ →
      (TileQuarterTurn (TileTranslation T' x)).anchor =
        (TileTranslation T (GaussianQuarterTurn x)).anchor := by
    intro he
    dsimp [T'] at he ⊢
    rw [quarter_translate, quarter_translate, hvT]
    have ht : T.cells = ∅ := by
      have htarget : (TileTranslation T (GaussianQuarterTurn x)).cells = ∅ := by
        rw [← eM]
        exact he
      exact (TileTranslationFormulas T (GaussianQuarterTurn x)).2.2.1.mp htarget
    change GaussianTranslation (GaussianQuarterTurn x)
        (GaussianTranslation uT (TileQuarterTurn T).anchor) =
      GaussianTranslation (GaussianQuarterTurn x) T.anchor
    have ha : GaussianTranslation uT (TileQuarterTurn T).anchor = T.anchor := by
      simpa [TileTranslation, GaussianTranslation] using hanchorT ht
    rw [ha]
  have hs := same_touch (TileQuarterTurn T')
    (TileQuarterTurn (TileTranslation T' x))
    (TileQuarterTurn U') T
    (TileTranslation T (GaussianQuarterTurn x)) U
    eT eM eU aT aM aU
  exact hs.mp hrot

private theorem turn5 :
    (by
      classical
      exact
        (∀ (T : ProtoTile), ∀ (x : GaussianInt), TileQuarterTurn (TileTranslation T x) =
            TileTranslation (TileQuarterTurn T) (GaussianQuarterTurn x)) → ((∀ (A : ProtoTile), ∀
            (B : ProtoTile), ∀ (C : ProtoTile), ∀ (A' : ProtoTile), ∀ (B' : ProtoTile), ∀ (C' :
            ProtoTile), (A.cells = A'.cells) → ((B.cells = B'.cells) → ((C.cells = C'.cells) →
            ((A.cells = ∅ → A.anchor = A'.anchor) → ((B.cells = ∅ → B.anchor = B'.anchor) →
            ((C.cells = ∅ → C.anchor = C'.anchor) → (TouchingTriple A B C ↔ TouchingTriple A' B'
            C'))))))) → ((∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (uT : GaussianInt), ∀ (uU :
            GaussianInt), ∀ (x : GaussianInt), ∀ (y : GaussianInt), (GaussianRealPoint uT =
            ((TileCentroid T).1 + (TileCentroid T).2, (TileCentroid T).2 - (TileCentroid T).1)) →
            ((GaussianRealPoint uU = ((TileCentroid U).1 + (TileCentroid U).2, (TileCentroid U).2
            - (TileCentroid U).1)) → ((TileCentroid U - TileCentroid T = (1 / 2 : Real) •
            (GaussianRealPoint (GaussianQuarterTurn x) + GaussianRealPoint (GaussianQuarterTurn
            y))) → (TileCentroid (TileTranslation U ⟨uU.im, -uU.re⟩) - TileCentroid
            (TileTranslation T ⟨uT.im, -uT.re⟩) = (1 / 2 : Real) • (GaussianRealPoint x +
            GaussianRealPoint y))))) → (∀ (C : CircleCoordinates), ∀ (D : CircleCoordinates), ∀
            (E : CircleCoordinates), ∀ (T : ProtoTile), ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀
            (x : GaussianInt), ∀ (y : GaussianInt), ∀ (z : GaussianInt), ∀ (w : GaussianInt),
            BandPrototile C T → BandPrototile D U → BandPrototile E V → QuarterTurnSymmetric T →
            QuarterTurnSymmetric U → QuarterTurnSymmetric V → (∀ (X : ProtoTile), ∀ (Y :
            ProtoTile), ∀ (Z : ProtoTile), BandPrototile C X → BandPrototile D Y → BandPrototile
            E Z → TileCentroid Y - TileCentroid X = (1 / 2 : Real) • (GaussianRealPoint x +
            GaussianRealPoint y) → TileCentroid Z - TileCentroid X = (1 / 2 : Real) •
            (GaussianRealPoint z - GaussianRealPoint w) → TouchingTriple X Y Z) → TileCentroid U
            - TileCentroid T = (1 / 2 : Real) • (GaussianRealPoint (GaussianQuarterTurn x) +
            GaussianRealPoint (GaussianQuarterTurn y)) → TileCentroid V - TileCentroid T = (1 / 2
            : Real) • (GaussianRealPoint (GaussianQuarterTurn z) - GaussianRealPoint
            (GaussianQuarterTurn w)) → TouchingTriple T U V)))
    ) := by
  classical
  intro quarter_translate same_touch shift_centroid C D E T U V x y z w hT hU hV hTs hUs hVs
      hbase hcu hcv
  obtain ⟨uT, huT, hcellT, hanchorT, hfootT, hcenterT⟩ :=
    QuarterTurnSymmetricCenteredTransport T hTs
  obtain ⟨uU, huU, hcellU, hanchorU, hfootU, hcenterU⟩ :=
    QuarterTurnSymmetricCenteredTransport U hUs
  obtain ⟨uV, huV, hcellV, hanchorV, hfootV, hcenterV⟩ :=
    QuarterTurnSymmetricCenteredTransport V hVs
  let vT : GaussianInt := ⟨uT.im, -uT.re⟩
  let vU : GaussianInt := ⟨uU.im, -uU.re⟩
  let vV : GaussianInt := ⟨uV.im, -uV.re⟩
  have hvT : GaussianQuarterTurn vT = uT := by dsimp [vT]; ext <;> simp [GaussianQuarterTurn]
  have hvU : GaussianQuarterTurn vU = uU := by dsimp [vU]; ext <;> simp [GaussianQuarterTurn]
  have hvV : GaussianQuarterTurn vV = uV := by dsimp [vV]; ext <;> simp [GaussianQuarterTurn]
  let T' := TileTranslation T vT
  let U' := TileTranslation U vU
  let V' := TileTranslation V vV
  have hT' := BandPrototileTranslation C T vT hT
  have hU' := BandPrototileTranslation D U vU hU
  have hV' := BandPrototileTranslation E V vV hV
  have hcu' := shift_centroid T U uT uU x y huT huU hcu
  have hcvMinus : TileCentroid V - TileCentroid T = (1 / 2 : Real) •
      (GaussianRealPoint (GaussianQuarterTurn z) +
        GaussianRealPoint (GaussianQuarterTurn (-w))) := by
    simpa [GaussianRealPoint, GaussianQuarterTurn, sub_eq_add_neg] using hcv
  have hcv' : TileCentroid (TileTranslation V vV) -
      TileCentroid (TileTranslation T vT) = (1 / 2 : Real) •
      (GaussianRealPoint z - GaussianRealPoint w) := by
    have hh := shift_centroid T V uT uV z (-w) huT huV hcvMinus
    simpa [GaussianRealPoint, GaussianQuarterTurn, sub_eq_add_neg] using hh
  have hrot : TouchingTriple (TileQuarterTurn T')
      (TileQuarterTurn U') (TileQuarterTurn V') := by
    exact (TouchingTripleCovariance T' U' V' 0).2.1.mp
      (hbase T' U' V' hT' hU' hV' hcu' hcv')
  have eT : (TileQuarterTurn T').cells = T.cells := by
    dsimp [T']; rw [quarter_translate, hvT]; exact hcellT
  have eU : (TileQuarterTurn U').cells = U.cells := by
    dsimp [U']; rw [quarter_translate, hvU]; exact hcellU
  have eV : (TileQuarterTurn V').cells = V.cells := by
    dsimp [V']; rw [quarter_translate, hvV]; exact hcellV
  have aT : (TileQuarterTurn T').cells = ∅ →
      (TileQuarterTurn T').anchor = T.anchor := by
    intro he; simpa [T', quarter_translate, hvT] using hanchorT (by rwa [eT] at he)
  have aU : (TileQuarterTurn U').cells = ∅ →
      (TileQuarterTurn U').anchor = U.anchor := by
    intro he; simpa [U', quarter_translate, hvU] using hanchorU (by rwa [eU] at he)
  have aV : (TileQuarterTurn V').cells = ∅ →
      (TileQuarterTurn V').anchor = V.anchor := by
    intro he; simpa [V', quarter_translate, hvV] using hanchorV (by rwa [eV] at he)
  exact (same_touch (TileQuarterTurn T') (TileQuarterTurn U') (TileQuarterTurn V')
    T U V eT eU eV aT aU aV).mp hrot

private theorem firstAt463 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (∀ (a : Fin (4 : ℕ)), ∀ (T : ProtoTile),
            BandPrototile (q a) T → QuarterTurnSymmetric T) → ((∀ (T₀ : ProtoTile), ∀ (Tᵢ :
            ProtoTile), ∀ (i : Fin (3 : ℕ)), BandPrototile (q (0 : Fin (4 : ℕ))) T₀ →
            BandPrototile (q i.succ) Tᵢ → TileCentroid Tᵢ - TileCentroid T₀ = (1 / 2 : ℝ) •
            (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) +
            GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → TouchingTriple
            T₀ (TileTranslation T₀ (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) Tᵢ) → ((∀ (C
            : CircleCoordinates), ∀ (D : CircleCoordinates), ∀ (T : ProtoTile), ∀ (U :
            ProtoTile), ∀ (x : GaussianInt), ∀ (y : GaussianInt), BandPrototile C T →
            BandPrototile D U → QuarterTurnSymmetric T → QuarterTurnSymmetric U → (∀ (X :
            ProtoTile), ∀ (Y : ProtoTile), BandPrototile C X → BandPrototile D Y → TileCentroid Y
            - TileCentroid X = (1 / 2 : Real) • (GaussianRealPoint x + GaussianRealPoint y) →
            TouchingTriple X (TileTranslation X x) Y) → (TileCentroid U - TileCentroid T = (1 / 2
            : Real) • (GaussianRealPoint (GaussianQuarterTurn x) + GaussianRealPoint
            (GaussianQuarterTurn y))) → TouchingTriple T (TileTranslation T (GaussianQuarterTurn
            x)) U) → (∀ (i : Fin (3 : ℕ)), ∀ (X : ProtoTile), ∀ (Y : ProtoTile), BandPrototile (q
            0) X → BandPrototile (q i.succ) Y → TileCentroid Y - TileCentroid X = (1 / 2 : Real)
            • (GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q i.succ) (q 0))) +
            GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q 0) (q i.succ)))) →
            TouchingTriple X (TileTranslation X (GaussianQuarterTurn (BandVectors.1 (q i.succ) (q
            0)))) Y)))
    ) := by
  classical
  intro q hT2 hT4 turn4 i X Y hX hY hcent
  exact turn4 (q 0) (q i.succ) X Y
    (BandVectors.1 (q i.succ) (q 0))
    (BandVectors.1 (q 0) (q i.succ)) hX hY
    (hT2 0 X hX) (hT2 i.succ Y hY)
    (fun A B hA hB hz => hT4 A B i hA hB hz) hcent

private theorem firstAt482 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (∀ (a : Fin (4 : ℕ)), ∀ (T : ProtoTile),
            BandPrototile (q a) T → QuarterTurnSymmetric T) → ((∀ (T₀ : ProtoTile), ∀ (Tᵢ :
            ProtoTile), ∀ (i : Fin (3 : ℕ)), BandPrototile (q (0 : Fin (4 : ℕ))) T₀ →
            BandPrototile (q i.succ) Tᵢ → TileCentroid Tᵢ - TileCentroid T₀ = (1 / 2 : ℝ) •
            (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) +
            GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → TouchingTriple
            T₀ (TileTranslation T₀ (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) Tᵢ) → ((∀ (C
            : CircleCoordinates), ∀ (D : CircleCoordinates), ∀ (T : ProtoTile), ∀ (U :
            ProtoTile), ∀ (x : GaussianInt), ∀ (y : GaussianInt), BandPrototile C T →
            BandPrototile D U → QuarterTurnSymmetric T → QuarterTurnSymmetric U → (∀ (X :
            ProtoTile), ∀ (Y : ProtoTile), BandPrototile C X → BandPrototile D Y → TileCentroid Y
            - TileCentroid X = (1 / 2 : Real) • (GaussianRealPoint x + GaussianRealPoint y) →
            TouchingTriple X (TileTranslation X x) Y) → (TileCentroid U - TileCentroid T = (1 / 2
            : Real) • (GaussianRealPoint (GaussianQuarterTurn x) + GaussianRealPoint
            (GaussianQuarterTurn y))) → TouchingTriple T (TileTranslation T (GaussianQuarterTurn
            x)) U) → (∀ (i : Fin (3 : ℕ)), ∀ (X : ProtoTile), ∀ (Y : ProtoTile), BandPrototile (q
            0) X → BandPrototile (q i.succ) Y → TileCentroid Y - TileCentroid X = (1 / 2 : Real)
            • (GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q i.succ) (q 0))) +
            GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q 0) (q i.succ)))) →
            TouchingTriple X (TileTranslation X (GaussianQuarterTurn (BandVectors.1 (q i.succ) (q
            0)))) Y)))
    ) := by
  classical
  intro q hT2 hT4 turn4 i X Y hX hY hcent
  exact turn4 (q 0) (q i.succ) X Y
    (BandVectors.1 (q i.succ) (q 0))
    (BandVectors.1 (q 0) (q i.succ)) hX hY
    (hT2 0 X hX) (hT2 i.succ Y hY)
    (fun A B hA hB hz => hT4 A B i hA hB hz) hcent

private theorem base :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (∀ (a : Fin (4 : ℕ)), ∀ (T : ProtoTile),
            BandPrototile (q a) T → QuarterTurnSymmetric T) → ((∀ (T₀ : ProtoTile), ∀ (Tᵢ :
            ProtoTile), ∀ (Tⱼ : ProtoTile), ∀ (i : Fin (3 : ℕ)), BandPrototile (q (0 : Fin (4 :
            ℕ))) T₀ → BandPrototile (q i.succ) Tᵢ → BandPrototile (q (i + (1 : Fin (3 :
            ℕ))).succ) Tⱼ → TileCentroid Tᵢ - TileCentroid T₀ = (1 / 2 : ℝ) • (GaussianRealPoint
            (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) + GaussianRealPoint (BandVectors.1
            (q (0 : Fin (4 : ℕ))) (q i.succ))) → TileCentroid Tⱼ - TileCentroid T₀ = (1 / 2 : ℝ)
            • (GaussianRealPoint (BandVectors.1 (q (i + (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 :
            ℕ)))) - GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (i + (1 : Fin (3 :
            ℕ))).succ))) → TouchingTriple T₀ Tᵢ Tⱼ) → ((∀ (C : CircleCoordinates), ∀ (D :
            CircleCoordinates), ∀ (E : CircleCoordinates), ∀ (T : ProtoTile), ∀ (U : ProtoTile),
            ∀ (V : ProtoTile), ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (z : GaussianInt), ∀
            (w : GaussianInt), BandPrototile C T → BandPrototile D U → BandPrototile E V →
            QuarterTurnSymmetric T → QuarterTurnSymmetric U → QuarterTurnSymmetric V → (∀ (X :
            ProtoTile), ∀ (Y : ProtoTile), ∀ (Z : ProtoTile), BandPrototile C X → BandPrototile D
            Y → BandPrototile E Z → TileCentroid Y - TileCentroid X = (1 / 2 : Real) •
            (GaussianRealPoint x + GaussianRealPoint y) → TileCentroid Z - TileCentroid X = (1 /
            2 : Real) • (GaussianRealPoint z - GaussianRealPoint w) → TouchingTriple X Y Z) →
            TileCentroid U - TileCentroid T = (1 / 2 : Real) • (GaussianRealPoint
            (GaussianQuarterTurn x) + GaussianRealPoint (GaussianQuarterTurn y)) → TileCentroid V
            - TileCentroid T = (1 / 2 : Real) • (GaussianRealPoint (GaussianQuarterTurn z) -
            GaussianRealPoint (GaussianQuarterTurn w)) → TouchingTriple T U V) → (∀ (i : Fin (3 :
            ℕ)), ∀ (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (Z : ProtoTile), BandPrototile (q 0) X →
            BandPrototile (q i.succ) Y → BandPrototile (q ((i + 1).succ)) Z → TileCentroid Y -
            TileCentroid X = (1 / 2 : Real) • (GaussianRealPoint (GaussianQuarterTurn
            (BandVectors.1 (q i.succ) (q 0))) + GaussianRealPoint (GaussianQuarterTurn
            (BandVectors.1 (q 0) (q i.succ)))) → TileCentroid Z - TileCentroid X = (1 / 2 : Real)
            • (GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q ((i + 1).succ)) (q 0))) -
            GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q 0) (q ((i + 1).succ))))) →
            TouchingTriple X Y Z)))
    ) := by
  classical
  intro q hT2 hT5 turn5 i X Y Z hX hY hZ ha hb
  exact turn5 (q 0) (q i.succ) (q ((i + 1).succ)) X Y Z
    (BandVectors.1 (q i.succ) (q 0)) (BandVectors.1 (q 0) (q i.succ))
    (BandVectors.1 (q ((i + 1).succ)) (q 0)) (BandVectors.1 (q 0) (q ((i + 1).succ)))
    hX hY hZ (hT2 0 X hX) (hT2 i.succ Y hY) (hT2 (i + 1).succ Z hZ)
    (fun A B C hA hB hC ha' hb' => hT5 A B C i hA hB hC ha' hb') ha hb

private theorem firstAt532 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (∀ (a : Fin (4 : ℕ)), ∀ (T : ProtoTile),
            BandPrototile (q a) T → QuarterTurnSymmetric T) → ((∀ (T₀ : ProtoTile), ∀ (Tᵢ :
            ProtoTile), ∀ (Tⱼ : ProtoTile), ∀ (i : Fin (3 : ℕ)), BandPrototile (q (0 : Fin (4 :
            ℕ))) T₀ → BandPrototile (q i.succ) Tᵢ → BandPrototile (q (i + (1 : Fin (3 :
            ℕ))).succ) Tⱼ → TileCentroid Tᵢ - TileCentroid T₀ = (1 / 2 : ℝ) • (GaussianRealPoint
            (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) + GaussianRealPoint (BandVectors.1
            (q (0 : Fin (4 : ℕ))) (q i.succ))) → TileCentroid Tⱼ - TileCentroid T₀ = (1 / 2 : ℝ)
            • (GaussianRealPoint (BandVectors.1 (q (i + (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 :
            ℕ)))) - GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (i + (1 : Fin (3 :
            ℕ))).succ))) → TouchingTriple T₀ Tᵢ Tⱼ) → ((∀ (C : CircleCoordinates), ∀ (D :
            CircleCoordinates), ∀ (E : CircleCoordinates), ∀ (T : ProtoTile), ∀ (U : ProtoTile),
            ∀ (V : ProtoTile), ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (z : GaussianInt), ∀
            (w : GaussianInt), BandPrototile C T → BandPrototile D U → BandPrototile E V →
            QuarterTurnSymmetric T → QuarterTurnSymmetric U → QuarterTurnSymmetric V → (∀ (X :
            ProtoTile), ∀ (Y : ProtoTile), ∀ (Z : ProtoTile), BandPrototile C X → BandPrototile D
            Y → BandPrototile E Z → TileCentroid Y - TileCentroid X = (1 / 2 : Real) •
            (GaussianRealPoint x + GaussianRealPoint y) → TileCentroid Z - TileCentroid X = (1 /
            2 : Real) • (GaussianRealPoint z - GaussianRealPoint w) → TouchingTriple X Y Z) →
            TileCentroid U - TileCentroid T = (1 / 2 : Real) • (GaussianRealPoint
            (GaussianQuarterTurn x) + GaussianRealPoint (GaussianQuarterTurn y)) → TileCentroid V
            - TileCentroid T = (1 / 2 : Real) • (GaussianRealPoint (GaussianQuarterTurn z) -
            GaussianRealPoint (GaussianQuarterTurn w)) → TouchingTriple T U V) → (∀ (i : Fin (3 :
            ℕ)), ∀ (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (Z : ProtoTile), BandPrototile (q 0) X →
            BandPrototile (q i.succ) Y → BandPrototile (q ((i + 1).succ)) Z → TileCentroid Y -
            TileCentroid X = (1 / 2 : Real) • (GaussianRealPoint (GaussianQuarterTurn
            (BandVectors.1 (q i.succ) (q 0))) + GaussianRealPoint (GaussianQuarterTurn
            (BandVectors.1 (q 0) (q i.succ)))) → TileCentroid Z - TileCentroid X = (1 / 2 : Real)
            • (GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q ((i + 1).succ)) (q 0))) -
            GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q 0) (q ((i + 1).succ))))) →
            TouchingTriple X Y Z)))
    ) := by
  classical
  intro q hT2 hT5 turn5 i X Y Z hX hY hZ ha hb
  exact turn5 (q 0) (q i.succ) (q ((i + 1).succ)) X Y Z
    (BandVectors.1 (q i.succ) (q 0)) (BandVectors.1 (q 0) (q i.succ))
    (BandVectors.1 (q ((i + 1).succ)) (q 0))
    (BandVectors.1 (q 0) (q ((i + 1).succ))) hX hY hZ
    (hT2 0 X hX) (hT2 i.succ Y hY) (hT2 (i + 1).succ Z hZ)
    (fun A B C hA hB hC ha' hb' => hT5 A B C i hA hB hC ha' hb') ha hb

private theorem base3 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (∀ (a : Fin (4 : ℕ)), ∀ (T : ProtoTile),
            BandPrototile (q a) T → QuarterTurnSymmetric T) → ((∀ (T₀ : ProtoTile), ∀ (Tᵢ :
            ProtoTile), ∀ (Tⱼ : ProtoTile), ∀ (i : Fin (3 : ℕ)), BandPrototile (q (0 : Fin (4 :
            ℕ))) T₀ → BandPrototile (q i.succ) Tᵢ → BandPrototile (q (i + (1 : Fin (3 :
            ℕ))).succ) Tⱼ → TileCentroid Tᵢ - TileCentroid T₀ = (1 / 2 : ℝ) • (GaussianRealPoint
            (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) + GaussianRealPoint (BandVectors.1
            (q (0 : Fin (4 : ℕ))) (q i.succ))) → TileCentroid Tⱼ - TileCentroid T₀ = (1 / 2 : ℝ)
            • (GaussianRealPoint (BandVectors.1 (q (i + (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 :
            ℕ)))) - GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (i + (1 : Fin (3 :
            ℕ))).succ))) → TouchingTriple T₀ Tᵢ Tⱼ) → ((∀ (C : CircleCoordinates), ∀ (D :
            CircleCoordinates), ∀ (E : CircleCoordinates), ∀ (T : ProtoTile), ∀ (U : ProtoTile),
            ∀ (V : ProtoTile), ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (z : GaussianInt), ∀
            (w : GaussianInt), BandPrototile C T → BandPrototile D U → BandPrototile E V →
            QuarterTurnSymmetric T → QuarterTurnSymmetric U → QuarterTurnSymmetric V → (∀ (X :
            ProtoTile), ∀ (Y : ProtoTile), ∀ (Z : ProtoTile), BandPrototile C X → BandPrototile D
            Y → BandPrototile E Z → TileCentroid Y - TileCentroid X = (1 / 2 : Real) •
            (GaussianRealPoint x + GaussianRealPoint y) → TileCentroid Z - TileCentroid X = (1 /
            2 : Real) • (GaussianRealPoint z - GaussianRealPoint w) → TouchingTriple X Y Z) →
            TileCentroid U - TileCentroid T = (1 / 2 : Real) • (GaussianRealPoint
            (GaussianQuarterTurn x) + GaussianRealPoint (GaussianQuarterTurn y)) → TileCentroid V
            - TileCentroid T = (1 / 2 : Real) • (GaussianRealPoint (GaussianQuarterTurn z) -
            GaussianRealPoint (GaussianQuarterTurn w)) → TouchingTriple T U V) → (∀ (i : Fin (3 :
            ℕ)), ∀ (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (Z : ProtoTile), BandPrototile (q 0) X →
            BandPrototile (q i.succ) Y → BandPrototile (q ((i + 1).succ)) Z → TileCentroid Y -
            TileCentroid X = (1 / 2 : Real) • (GaussianRealPoint (GaussianQuarterTurn
            (BandVectors.1 (q i.succ) (q 0))) + GaussianRealPoint (GaussianQuarterTurn
            (BandVectors.1 (q 0) (q i.succ)))) → TileCentroid Z - TileCentroid X = (1 / 2 : Real)
            • (GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q ((i + 1).succ)) (q 0))) -
            GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q 0) (q ((i + 1).succ))))) →
            TouchingTriple X Y Z)))
    ) := by
  classical
  intro q hT2 hT5 turn5 i X Y Z hX hY hZ ha hb
  exact turn5 (q 0) (q i.succ) (q ((i + 1).succ)) X Y Z
    (BandVectors.1 (q i.succ) (q 0)) (BandVectors.1 (q 0) (q i.succ))
    (BandVectors.1 (q ((i + 1).succ)) (q 0)) (BandVectors.1 (q 0) (q ((i + 1).succ)))
    hX hY hZ (hT2 0 X hX) (hT2 i.succ Y hY) (hT2 (i + 1).succ Z hZ)
    (fun A B C hA hB hC ha' hb' => hT5 A B C i hA hB hC ha' hb') ha hb

private theorem firstAt570 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (∀ (a : Fin (4 : ℕ)), ∀ (T : ProtoTile),
            BandPrototile (q a) T → QuarterTurnSymmetric T) → ((∀ (C : CircleCoordinates), ∀ (D :
            CircleCoordinates), ∀ (E : CircleCoordinates), ∀ (T : ProtoTile), ∀ (U : ProtoTile),
            ∀ (V : ProtoTile), ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (z : GaussianInt), ∀
            (w : GaussianInt), BandPrototile C T → BandPrototile D U → BandPrototile E V →
            QuarterTurnSymmetric T → QuarterTurnSymmetric U → QuarterTurnSymmetric V → (∀ (X :
            ProtoTile), ∀ (Y : ProtoTile), ∀ (Z : ProtoTile), BandPrototile C X → BandPrototile D
            Y → BandPrototile E Z → TileCentroid Y - TileCentroid X = (1 / 2 : Real) •
            (GaussianRealPoint x + GaussianRealPoint y) → TileCentroid Z - TileCentroid X = (1 /
            2 : Real) • (GaussianRealPoint z - GaussianRealPoint w) → TouchingTriple X Y Z) →
            TileCentroid U - TileCentroid T = (1 / 2 : Real) • (GaussianRealPoint
            (GaussianQuarterTurn x) + GaussianRealPoint (GaussianQuarterTurn y)) → TileCentroid V
            - TileCentroid T = (1 / 2 : Real) • (GaussianRealPoint (GaussianQuarterTurn z) -
            GaussianRealPoint (GaussianQuarterTurn w)) → TouchingTriple T U V) → (∀ (i : Fin (3 :
            ℕ)), (∀ (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (Z : ProtoTile), BandPrototile (q 0) X
            → BandPrototile (q i.succ) Y → BandPrototile (q ((i + 1).succ)) Z → TileCentroid Y -
            TileCentroid X = (1 / 2 : Real) • (GaussianRealPoint (GaussianQuarterTurn
            (BandVectors.1 (q i.succ) (q 0))) + GaussianRealPoint (GaussianQuarterTurn
            (BandVectors.1 (q 0) (q i.succ)))) → TileCentroid Z - TileCentroid X = (1 / 2 : Real)
            • (GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q ((i + 1).succ)) (q 0))) -
            GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q 0) (q ((i + 1).succ))))) →
            TouchingTriple X Y Z) → (∀ (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (Z : ProtoTile),
            BandPrototile (q 0) X → BandPrototile (q i.succ) Y → BandPrototile (q ((i + 1).succ))
            Z → TileCentroid Y - TileCentroid X = (1 / 2 : Real) • (GaussianRealPoint
            (GaussianQuarterTurn (GaussianQuarterTurn (BandVectors.1 (q i.succ) (q 0)))) +
            GaussianRealPoint (GaussianQuarterTurn (GaussianQuarterTurn (BandVectors.1 (q 0) (q
            i.succ))))) → TileCentroid Z - TileCentroid X = (1 / 2 : Real) • (GaussianRealPoint
            (GaussianQuarterTurn (GaussianQuarterTurn (BandVectors.1 (q ((i + 1).succ)) (q 0))))
            - GaussianRealPoint (GaussianQuarterTurn (GaussianQuarterTurn (BandVectors.1 (q 0) (q
            ((i + 1).succ)))))) → TouchingTriple X Y Z)))
    ) := by
  classical
  intro q hT2 turn5 i base3 X Y Z hX hY hZ ha hb
  exact turn5 (q 0) (q i.succ) (q ((i + 1).succ)) X Y Z
    (GaussianQuarterTurn (BandVectors.1 (q i.succ) (q 0)))
    (GaussianQuarterTurn (BandVectors.1 (q 0) (q i.succ)))
    (GaussianQuarterTurn (BandVectors.1 (q ((i + 1).succ)) (q 0)))
    (GaussianQuarterTurn (BandVectors.1 (q 0) (q ((i + 1).succ)))) hX hY hZ
    (hT2 0 X hX) (hT2 i.succ Y hY) (hT2 (i + 1).succ Z hZ)
    base3 ha hb

end TouchingCovarianceProof

theorem OrientedTouchingCovariance :
    ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → ((∀ (a : Fin 4), ∀ (T :
        ProtoTile), BandPrototile (q a) T → QuarterTurnSymmetric T) → ((∀ (T₀ : ProtoTile), ∀ (Tᵢ
        : ProtoTile), ∀ (i : Fin 3), BandPrototile (q 0) T₀ → BandPrototile (q i.succ) Tᵢ →
      TileCentroid Tᵢ - TileCentroid T₀ =
        (1 / 2 : Real) •
          (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
            GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) →
      TouchingTriple T₀
        (TileTranslation T₀ (BandVectors.1 (q i.succ) (q 0))) Tᵢ) → ((∀ (T₀ : ProtoTile), ∀ (Tᵢ :
            ProtoTile), ∀ (Tⱼ : ProtoTile), ∀ (i : Fin 3), BandPrototile (q 0) T₀ → BandPrototile
            (q i.succ) Tᵢ →
      BandPrototile (q ((i + 1).succ)) Tⱼ →
      TileCentroid Tᵢ - TileCentroid T₀ =
        (1 / 2 : Real) •
          (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
            GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) →
      TileCentroid Tⱼ - TileCentroid T₀ =
        (1 / 2 : Real) •
          (GaussianRealPoint (BandVectors.1 (q ((i + 1).succ)) (q 0)) -
            GaussianRealPoint (BandVectors.1 (q 0) (q ((i + 1).succ)))) →
      TouchingTriple T₀ Tᵢ Tⱼ) → ((∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (i : Fin 3), ∀ (s :
          Fin 4), BandPrototile (q 0) T₀ → BandPrototile (q i.succ) Tᵢ →
      TileCentroid Tᵢ - TileCentroid T₀ =
        (1 / 2 : Real) •
          (GaussianRealPoint
              ((GaussianQuarterTurn^[s.val])
                (BandVectors.1 (q i.succ) (q 0))) +
            GaussianRealPoint
              ((GaussianQuarterTurn^[s.val])
                (BandVectors.1 (q 0) (q i.succ)))) →
      TouchingTriple T₀
        (TileTranslation T₀
          ((GaussianQuarterTurn^[s.val])
            (BandVectors.1 (q i.succ) (q 0)))) Tᵢ) ∧
    (∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (Tⱼ : ProtoTile), ∀ (i : Fin 3), ∀ (s : Fin 4),
        BandPrototile (q 0) T₀ → BandPrototile (q i.succ) Tᵢ →
      BandPrototile (q ((i + 1).succ)) Tⱼ →
      TileCentroid Tᵢ - TileCentroid T₀ =
        (1 / 2 : Real) •
          (GaussianRealPoint
              ((GaussianQuarterTurn^[s.val])
                (BandVectors.1 (q i.succ) (q 0))) +
            GaussianRealPoint
              ((GaussianQuarterTurn^[s.val])
                (BandVectors.1 (q 0) (q i.succ)))) →
      TileCentroid Tⱼ - TileCentroid T₀ =
        (1 / 2 : Real) •
          (GaussianRealPoint
              ((GaussianQuarterTurn^[s.val])
                (BandVectors.1 (q ((i + 1).succ)) (q 0))) -
            GaussianRealPoint
              ((GaussianQuarterTurn^[s.val])
                (BandVectors.1 (q 0) (q ((i + 1).succ))))) →
      TouchingTriple T₀ Tᵢ Tⱼ))))) := by
  intro q hq hT2 hT4 hT5
-- BODY
  have quarter_translate (T : ProtoTile) (x : GaussianInt) :
      TileQuarterTurn (TileTranslation T x) =
        TileTranslation (TileQuarterTurn T) (GaussianQuarterTurn x) :=
            TouchingCovarianceProof.quarter_translate T x
  have same_touch (A B C A' B' C' : ProtoTile)
      (ha : A.cells = A'.cells) (hb : B.cells = B'.cells)
      (hc : C.cells = C'.cells)
      (haa : A.cells = ∅ → A.anchor = A'.anchor)
      (hbb : B.cells = ∅ → B.anchor = B'.anchor)
      (hcc : C.cells = ∅ → C.anchor = C'.anchor) :
      TouchingTriple A B C ↔ TouchingTriple A' B' C' := TouchingCovarianceProof.same_touch A B C
          A' B' C' ha hb hc haa hbb hcc
  have shift_centroid (T U : ProtoTile) (uT uU : GaussianInt)
      (x y : GaussianInt)
      (huT : GaussianRealPoint uT =
        ((TileCentroid T).1 + (TileCentroid T).2,
          (TileCentroid T).2 - (TileCentroid T).1))
      (huU : GaussianRealPoint uU =
        ((TileCentroid U).1 + (TileCentroid U).2,
          (TileCentroid U).2 - (TileCentroid U).1))
      (hcent : TileCentroid U - TileCentroid T =
        (1 / 2 : Real) •
          (GaussianRealPoint (GaussianQuarterTurn x) +
            GaussianRealPoint (GaussianQuarterTurn y))) :
      TileCentroid (TileTranslation U ⟨uU.im, -uU.re⟩) -
          TileCentroid (TileTranslation T ⟨uT.im, -uT.re⟩) =
        (1 / 2 : Real) • (GaussianRealPoint x + GaussianRealPoint y) :=
            TouchingCovarianceProof.shift_centroid T U uT uU x y huT huU hcent
  have turn4 : ∀ (C D : CircleCoordinates) (T U : ProtoTile)
      (x y : GaussianInt),
      BandPrototile C T → BandPrototile D U →
      QuarterTurnSymmetric T → QuarterTurnSymmetric U →
      (∀ (X Y : ProtoTile), BandPrototile C X → BandPrototile D Y →
        TileCentroid Y - TileCentroid X =
          (1 / 2 : Real) •
            (GaussianRealPoint x + GaussianRealPoint y) →
        TouchingTriple X (TileTranslation X x) Y) →
      (TileCentroid U - TileCentroid T =
        (1 / 2 : Real) •
          (GaussianRealPoint (GaussianQuarterTurn x) +
            GaussianRealPoint (GaussianQuarterTurn y))) →
      TouchingTriple T
        (TileTranslation T (GaussianQuarterTurn x)) U := TouchingCovarianceProof.turn4
            quarter_translate same_touch
  have turn5 : ∀ (C D E : CircleCoordinates) (T U V : ProtoTile)
      (x y z w : GaussianInt),
      BandPrototile C T → BandPrototile D U → BandPrototile E V →
      QuarterTurnSymmetric T → QuarterTurnSymmetric U → QuarterTurnSymmetric V →
      (∀ (X Y Z : ProtoTile), BandPrototile C X → BandPrototile D Y →
        BandPrototile E Z →
        TileCentroid Y - TileCentroid X = (1 / 2 : Real) •
          (GaussianRealPoint x + GaussianRealPoint y) →
        TileCentroid Z - TileCentroid X = (1 / 2 : Real) •
          (GaussianRealPoint z - GaussianRealPoint w) →
        TouchingTriple X Y Z) →
      TileCentroid U - TileCentroid T = (1 / 2 : Real) •
        (GaussianRealPoint (GaussianQuarterTurn x) + GaussianRealPoint (GaussianQuarterTurn y)) →
      TileCentroid V - TileCentroid T = (1 / 2 : Real) •
        (GaussianRealPoint (GaussianQuarterTurn z) - GaussianRealPoint (GaussianQuarterTurn w)) →
      TouchingTriple T U V := TouchingCovarianceProof.turn5 quarter_translate same_touch
          shift_centroid
  have inverse_turn (x : GaussianInt) :
      GaussianQuarterTurn ⟨x.im, -x.re⟩ = x := by
    ext <;> simp [GaussianQuarterTurn]
  constructor
  · intro T₀ Tᵢ i s h₀ hᵢ hc
    fin_cases s
    · simpa using hT4 T₀ Tᵢ i h₀ hᵢ hc
    · exact turn4 (q 0) (q i.succ) T₀ Tᵢ
        (BandVectors.1 (q i.succ) (q 0))
        (BandVectors.1 (q 0) (q i.succ)) h₀ hᵢ
        (hT2 0 T₀ h₀) (hT2 i.succ Tᵢ hᵢ)
        (fun X Y hX hY hcent => hT4 X Y i hX hY hcent) hc
    · have first : ∀ (X Y : ProtoTile), BandPrototile (q 0) X →
          BandPrototile (q i.succ) Y →
          TileCentroid Y - TileCentroid X =
            (1 / 2 : Real) •
              (GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q i.succ) (q 0))) +
                GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q 0) (q i.succ)))) →
          TouchingTriple X (TileTranslation X
            (GaussianQuarterTurn (BandVectors.1 (q i.succ) (q 0)))) Y :=
                TouchingCovarianceProof.firstAt463 q hT2 hT4 turn4 i
      exact turn4 (q 0) (q i.succ) T₀ Tᵢ
        (GaussianQuarterTurn (BandVectors.1 (q i.succ) (q 0)))
        (GaussianQuarterTurn (BandVectors.1 (q 0) (q i.succ))) h₀ hᵢ
        (hT2 0 T₀ h₀) (hT2 i.succ Tᵢ hᵢ) first
        (by simpa [Function.iterate_succ_apply] using hc)
    · have first : ∀ (X Y : ProtoTile), BandPrototile (q 0) X →
          BandPrototile (q i.succ) Y →
          TileCentroid Y - TileCentroid X =
            (1 / 2 : Real) •
              (GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q i.succ) (q 0))) +
                GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q 0) (q i.succ)))) →
          TouchingTriple X (TileTranslation X
            (GaussianQuarterTurn (BandVectors.1 (q i.succ) (q 0)))) Y :=
                TouchingCovarianceProof.firstAt482 q hT2 hT4 turn4 i
      exact turn4 (q 0) (q i.succ) T₀ Tᵢ
        (GaussianQuarterTurn (GaussianQuarterTurn (BandVectors.1 (q i.succ) (q 0))))
        (GaussianQuarterTurn (GaussianQuarterTurn (BandVectors.1 (q 0) (q i.succ)))) h₀ hᵢ
        (hT2 0 T₀ h₀) (hT2 i.succ Tᵢ hᵢ)
        (fun X Y hX hY hz =>
          turn4 (q 0) (q i.succ) X Y
            (GaussianQuarterTurn (BandVectors.1 (q i.succ) (q 0)))
            (GaussianQuarterTurn (BandVectors.1 (q 0) (q i.succ))) hX hY
            (hT2 0 X hX) (hT2 i.succ Y hY) first hz)
        (by simpa [Function.iterate_succ_apply] using hc)
  · intro T₀ Tᵢ Tⱼ i s h₀ hᵢ hⱼ hcᵢ hcⱼ
    fin_cases s
    · simpa using hT5 T₀ Tᵢ Tⱼ i h₀ hᵢ hⱼ hcᵢ hcⱼ
    · exact turn5 (q 0) (q i.succ) (q ((i + 1).succ)) T₀ Tᵢ Tⱼ
        (BandVectors.1 (q i.succ) (q 0))
        (BandVectors.1 (q 0) (q i.succ))
        (BandVectors.1 (q ((i + 1).succ)) (q 0))
        (BandVectors.1 (q 0) (q ((i + 1).succ))) h₀ hᵢ hⱼ
        (hT2 0 T₀ h₀) (hT2 i.succ Tᵢ hᵢ)
        (hT2 (i + 1).succ Tⱼ hⱼ)
        (fun X Y Z hX hY hZ ha hb => hT5 X Y Z i hX hY hZ ha hb) hcᵢ hcⱼ
    · have base : ∀ (X Y Z : ProtoTile), BandPrototile (q 0) X →
          BandPrototile (q i.succ) Y → BandPrototile (q ((i + 1).succ)) Z →
          TileCentroid Y - TileCentroid X = (1 / 2 : Real) •
            (GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q i.succ) (q 0))) +
              GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q 0) (q i.succ)))) →
          TileCentroid Z - TileCentroid X = (1 / 2 : Real) •
            (GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q ((i + 1).succ)) (q 0))) -
              GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q 0) (q ((i + 1).succ))))) →
          TouchingTriple X Y Z := TouchingCovarianceProof.base q hT2 hT5 turn5 i
      have first : ∀ (X Y Z : ProtoTile), BandPrototile (q 0) X →
          BandPrototile (q i.succ) Y → BandPrototile (q ((i + 1).succ)) Z →
          TileCentroid Y - TileCentroid X = (1 / 2 : Real) •
            (GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q i.succ) (q 0))) +
              GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q 0) (q i.succ)))) →
          TileCentroid Z - TileCentroid X = (1 / 2 : Real) •
            (GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q ((i + 1).succ)) (q 0))) -
              GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q 0) (q ((i + 1).succ))))) →
          TouchingTriple X Y Z := TouchingCovarianceProof.firstAt532 q hT2 hT5 turn5 i
      exact turn5 (q 0) (q i.succ) (q ((i + 1).succ)) T₀ Tᵢ Tⱼ
        (GaussianQuarterTurn (BandVectors.1 (q i.succ) (q 0)))
        (GaussianQuarterTurn (BandVectors.1 (q 0) (q i.succ)))
        (GaussianQuarterTurn (BandVectors.1 (q ((i + 1).succ)) (q 0)))
        (GaussianQuarterTurn (BandVectors.1 (q 0) (q ((i + 1).succ)))) h₀ hᵢ hⱼ
        (hT2 0 T₀ h₀) (hT2 i.succ Tᵢ hᵢ) (hT2 (i + 1).succ Tⱼ hⱼ)
        first hcᵢ hcⱼ
    · have base3 : ∀ (X Y Z : ProtoTile), BandPrototile (q 0) X →
          BandPrototile (q i.succ) Y → BandPrototile (q ((i + 1).succ)) Z →
          TileCentroid Y - TileCentroid X = (1 / 2 : Real) •
            (GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q i.succ) (q 0))) +
              GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q 0) (q i.succ)))) →
          TileCentroid Z - TileCentroid X = (1 / 2 : Real) •
            (GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q ((i + 1).succ)) (q 0))) -
              GaussianRealPoint (GaussianQuarterTurn (BandVectors.1 (q 0) (q ((i + 1).succ))))) →
          TouchingTriple X Y Z := TouchingCovarianceProof.base3 q hT2 hT5 turn5 i
      have first : ∀ (X Y Z : ProtoTile), BandPrototile (q 0) X →
          BandPrototile (q i.succ) Y → BandPrototile (q ((i + 1).succ)) Z →
          TileCentroid Y - TileCentroid X = (1 / 2 : Real) •
            (GaussianRealPoint (GaussianQuarterTurn (GaussianQuarterTurn (BandVectors.1 (q
                i.succ) (q 0)))) +
              GaussianRealPoint (GaussianQuarterTurn (GaussianQuarterTurn (BandVectors.1 (q 0) (q
                  i.succ))))) →
          TileCentroid Z - TileCentroid X = (1 / 2 : Real) •
            (GaussianRealPoint (GaussianQuarterTurn (GaussianQuarterTurn (BandVectors.1 (q ((i +
                1).succ)) (q 0)))) -
              GaussianRealPoint (GaussianQuarterTurn (GaussianQuarterTurn (BandVectors.1 (q 0) (q
                  ((i + 1).succ)))))) →
          TouchingTriple X Y Z := TouchingCovarianceProof.firstAt570 q hT2 turn5 i base3
      exact turn5 (q 0) (q i.succ) (q ((i + 1).succ)) T₀ Tᵢ Tⱼ
        (GaussianQuarterTurn (GaussianQuarterTurn (BandVectors.1 (q i.succ) (q 0))))
        (GaussianQuarterTurn (GaussianQuarterTurn (BandVectors.1 (q 0) (q i.succ))))
        (GaussianQuarterTurn (GaussianQuarterTurn (BandVectors.1 (q ((i + 1).succ)) (q 0))))
        (GaussianQuarterTurn (GaussianQuarterTurn (BandVectors.1 (q 0) (q ((i + 1).succ))))) h₀
            hᵢ hⱼ
        (hT2 0 T₀ h₀) (hT2 i.succ Tᵢ hᵢ) (hT2 (i + 1).succ Tⱼ hⱼ)
        first hcᵢ hcⱼ

end ApollonianSuperharmonic

end
