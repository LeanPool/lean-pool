/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCircleAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryInversePhaseCancellation
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryProperCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryScopedPhase
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTilingTransport
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryVectorAction
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.GaussianQuarterTurn
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetricCenteredTransport
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurnFormulas
public import LeanPool.ApollonianSuperharmonic.TileReflectionFormulas
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.TouchingTriplePermutations
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: BandPackingSymmetryT3T5Covariance]

/-!
# BandPackingSymmetryT3T5Covariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PackingCovarianceProof

private theorem etranslate :
    (by
      classical
      exact
        let E (A B : ProtoTile) : Prop :=
          A.cells = B.cells ∧ (A.cells = ∅ → A.anchor = B.anchor)
        ∀ {A : ProtoTile}, ∀ {B : ProtoTile}, (E A B) → (∀ (v : GaussianInt), E (TileTranslation
            A v) (TileTranslation B v)) ) := by
  classical
  intro E A B h v
  refine ⟨congrArg (fun c => c.image (GaussianTranslation v)) h.1, ?_⟩
  intro he
  have ha := h.2 ((TileTranslationFormulas A v).2.2.1.mp he)
  exact congrArg (GaussianTranslation v) ha

private theorem equarter :
    (by
      classical
      exact
        let E (A B : ProtoTile) : Prop :=
          A.cells = B.cells ∧ (A.cells = ∅ → A.anchor = B.anchor)
        ∀ {A : ProtoTile}, ∀ {B : ProtoTile}, (E A B) → (E (TileQuarterTurn A) (TileQuarterTurn
            B)) ) := by
  classical
  intro E A B h
  refine ⟨congrArg (fun c => c.image (fun z => GaussianQuarterTurn z - 1)) h.1, ?_⟩
  intro he
  exact congrArg GaussianQuarterTurn (h.2 ((TileQuarterTurnFormulas A).2.2.1.mp he))

private theorem touching_obs :
    (by
      classical
      exact
        let E (A B : ProtoTile) : Prop :=
          A.cells = B.cells ∧ (A.cells = ∅ → A.anchor = B.anchor)
        ∀ {A : ProtoTile}, ∀ {A' : ProtoTile}, ∀ {B : ProtoTile}, ∀ {B' : ProtoTile}, (E A A') →
            ((E B B') → (TileTouching A B ↔ TileTouching A' B')) ) := by
  classical
  intro E A A' B B' ha hb
  have oa := ProtoTileObservableExtensionality A A' ha.1 ha.2
  have ob := ProtoTileObservableExtensionality B B' hb.1 hb.2
  simp only [TileTouching, ← ha.1, ← hb.1, ← oa.2.1, ← ob.2.1,
    ← oa.2.2.1, ← ob.2.2.1]
  by_cases ea : A.cells = ∅ <;> by_cases eb : B.cells = ∅
  · simp [ea, eb, ha.2 ea, hb.2 eb]
  · simp [ea, eb, ha.2 ea]
  · simp [ea, eb, hb.2 eb]
  · simp [ea, eb]

private theorem triple_obs :
    (by
      classical
      exact
        let E (A B : ProtoTile) : Prop :=
          A.cells = B.cells ∧ (A.cells = ∅ → A.anchor = B.anchor)
        (∀ {A : ProtoTile}, ∀ {A' : ProtoTile}, ∀ {B : ProtoTile}, ∀ {B' : ProtoTile}, (E A A') →
            ((E B B') → (TileTouching A B ↔ TileTouching A' B'))) → (∀ {A : ProtoTile}, ∀
            {A' : ProtoTile}, ∀ {B : ProtoTile}, ∀ {B' : ProtoTile}, ∀ {C : ProtoTile}, ∀
            {C' : ProtoTile}, (E A A') → ((E B B') → ((E C C') → (TouchingTriple A B C ↔
            TouchingTriple A' B' C')))) ) := by
  classical
  intro E touching_obs A A' B B' C C' ha hb hc
  have oa := ProtoTileObservableExtensionality A A' ha.1 ha.2
  have ob := ProtoTileObservableExtensionality B B' hb.1 hb.2
  have oc := ProtoTileObservableExtensionality C C' hc.1 hc.2
  simp only [TouchingTriple, touching_obs ha hb, touching_obs hb hc,
    touching_obs hc ha, oa.2.1, ob.2.1, oc.2.1]

private theorem translate_add :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (x : GaussianInt), ∀ (y : GaussianInt), TileTranslation
            (TileTranslation A x) y = TileTranslation A (x + y) ) := by
  classical
  intro A x y
  cases A
  simp only [TileTranslation, Finset.image_image, Function.comp_def,
    GaussianTranslation, add_assoc]
  rfl

private theorem translate_zero :
    (by
      classical
      exact
        ∀ (A : ProtoTile), TileTranslation A 0 = A ) := by
  classical
  intro A
  cases A
  have hz : GaussianTranslation 0 = id := by funext z; simp [GaussianTranslation]
  simp [TileTranslation, hz, GaussianTranslation]

private theorem quarter_translate :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (x : GaussianInt), TileQuarterTurn (TileTranslation A x) =
            TileTranslation (TileQuarterTurn A) (GaussianQuarterTurn x) ) := by
  classical
  intro A x
  exact (BandPackingSymmetryTilingTransport .negate).2.2.2.2.2.2.1 A x

private theorem qtwo :
    (by
      classical
      exact
        ∀ (x : GaussianInt), GaussianQuarterTurn (GaussianQuarterTurn x) = -x ) := by
  classical
  intro x
  ext <;> simp [GaussianQuarterTurn]

private theorem half_translate :
    (by
      classical
      exact
        (∀ (A : ProtoTile), ∀ (x : GaussianInt), ∀ (y : GaussianInt), TileTranslation
            (TileTranslation A x) y = TileTranslation A (x + y)) → ((∀ (A : ProtoTile), ∀ (x :
            GaussianInt), TileQuarterTurn (TileTranslation A x) = TileTranslation
            (TileQuarterTurn A) (GaussianQuarterTurn x)) → ((∀ (x : GaussianInt),
            GaussianQuarterTurn (GaussianQuarterTurn x) = -x) → (
        let H (w : GaussianInt) (A : ProtoTile) :=
          TileTranslation (TileQuarterTurn (TileQuarterTurn A)) w
        ∀ (w : GaussianInt), ∀ (x : GaussianInt), ∀ (A : ProtoTile), H w (TileTranslation A x) =
            TileTranslation (H w A) (-x)))) ) := by
  classical
  intro translate_add quarter_translate qtwo H w x A
  dsimp [H]
  rw [quarter_translate, quarter_translate, qtwo, translate_add, translate_add]
  rw [add_comm]

private theorem half_cov :
    (by
      classical
      exact
        let H (w : GaussianInt) (A : ProtoTile) :=
          TileTranslation (TileQuarterTurn (TileQuarterTurn A)) w
        ∀ (w : GaussianInt), ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile),
            TouchingTriple A B C ↔ TouchingTriple (H w A) (H w B) (H w C) ) := by
  classical
  intro H w A B C
  exact ((TouchingTripleCovariance A B C 0).2.1.trans
      (TouchingTripleCovariance (TileQuarterTurn A) (TileQuarterTurn B)
        (TileQuarterTurn C) 0).2.1).trans
      (TouchingTripleCovariance (TileQuarterTurn (TileQuarterTurn A))
        (TileQuarterTurn (TileQuarterTurn B)) (TileQuarterTurn (TileQuarterTurn C)) w).1

private theorem half_center :
    (by
      classical
      exact
        let E (A B : ProtoTile) : Prop :=
          A.cells = B.cells ∧ (A.cells = ∅ → A.anchor = B.anchor)
        (∀ {A : ProtoTile}, ∀ {B : ProtoTile}, ∀ {C : ProtoTile}, (E A B) → ((E B C) → (E A C)))
            → ((∀ {A : ProtoTile}, ∀ {B : ProtoTile}, (E A B) → (∀ (v : GaussianInt), E
            (TileTranslation A v) (TileTranslation B v))) → ((∀ {A : ProtoTile}, ∀
            {B : ProtoTile}, (E A B) → (E (TileQuarterTurn A) (TileQuarterTurn B))) → ((∀ (A :
            ProtoTile), ∀ (x : GaussianInt), ∀ (y : GaussianInt), TileTranslation
            (TileTranslation A x) y = TileTranslation A (x + y)) → ((∀ (A : ProtoTile), ∀ (x :
            GaussianInt), TileQuarterTurn (TileTranslation A x) = TileTranslation
            (TileQuarterTurn A) (GaussianQuarterTurn x)) → (
        let H (w : GaussianInt) (A : ProtoTile) :=
          TileTranslation (TileQuarterTurn (TileQuarterTurn A)) w
        ∀ (A : ProtoTile), (QuarterTurnSymmetric A) → (∃ w : GaussianInt, GaussianRealPoint w =
            (2 : Real) • TileCentroid A ∧ E (H w A) A)))))) ) := by
  classical
  intro E etrans etranslate equarter translate_add quarter_translate H A hs
  obtain ⟨u, hu, hc, ha, _⟩ := QuarterTurnSymmetricCenteredTransport A hs
  have he : E (TileTranslation (TileQuarterTurn A) u) A := ⟨hc, fun hz => ha (hc ▸ hz)⟩
  refine ⟨GaussianQuarterTurn u + u, ?_, ?_⟩
  · have hr := congrArg Prod.fst hu
    have hi := congrArg Prod.snd hu
    apply Prod.ext <;> simp [GaussianRealPoint, GaussianQuarterTurn] at hr hi ⊢ <;>
      linarith
  · have hh := etrans (etranslate (equarter he) u) he
    simpa only [quarter_translate, translate_add] using hh

private theorem half_other :
    (by
      classical
      exact
        let E (A B : ProtoTile) : Prop :=
          A.cells = B.cells ∧ (A.cells = ∅ → A.anchor = B.anchor)
        (∀ {A : ProtoTile}, ∀ {B : ProtoTile}, (E A B) → (∀ (v : GaussianInt), E (TileTranslation
            A v) (TileTranslation B v))) → ((∀ (A : ProtoTile), ∀ (x : GaussianInt), ∀ (y :
            GaussianInt), TileTranslation (TileTranslation A x) y = TileTranslation A (x + y)) → (
        let H (w : GaussianInt) (A : ProtoTile) :=
          TileTranslation (TileQuarterTurn (TileQuarterTurn A)) w
        (∀ (A : ProtoTile), (QuarterTurnSymmetric A) → (∃ w : GaussianInt, GaussianRealPoint w =
            (2 : Real) • TileCentroid A ∧ E (H w A) A)) → (∀ (A : ProtoTile),
            (QuarterTurnSymmetric A) → (∀ (w : GaussianInt), ∀ (z : GaussianInt),
            (GaussianRealPoint w - (2 : Real) • TileCentroid A = GaussianRealPoint z) → (E (H w
            A) (TileTranslation A z)))))) ) := by
  classical
  intro E etranslate translate_add H half_center A hs w z hz
  obtain ⟨v, hv, he⟩ := half_center A hs
  have wz : w = v + z := by
    rw [← hv] at hz
    apply Zsqrtd.ext
    · have hr := congrArg Prod.fst hz
      change (w.re : Real) - (v.re : Real) = (z.re : Real) at hr
      exact_mod_cast (show (w.re : Real) = (v.re : Real) + (z.re : Real) by linarith)
    · have hi := congrArg Prod.snd hz
      change (w.im : Real) - (v.im : Real) = (z.im : Real) at hi
      exact_mod_cast (show (w.im : Real) = (v.im : Real) + (z.im : Real) by linarith)
  have hh := etranslate he z
  simpa only [H, translate_add, ← wz] using hh

private theorem neg_triple :
    (by
      classical
      exact
        let E (A B : ProtoTile) : Prop :=
          A.cells = B.cells ∧ (A.cells = ∅ → A.anchor = B.anchor)
        (∀ {A : ProtoTile}, ∀ {B : ProtoTile}, (E A B) → (∀ (v : GaussianInt), E (TileTranslation
            A v) (TileTranslation B v))) → ((∀ {A : ProtoTile}, ∀ {A' : ProtoTile}, ∀
            {B : ProtoTile}, ∀ {B' : ProtoTile}, ∀ {C : ProtoTile}, ∀ {C' : ProtoTile}, (E A A')
            → ((E B B') → ((E C C') → (TouchingTriple A B C ↔ TouchingTriple A' B' C')))) → (
        let H (w : GaussianInt) (A : ProtoTile) :=
          TileTranslation (TileQuarterTurn (TileQuarterTurn A)) w
        (∀ (w : GaussianInt), ∀ (x : GaussianInt), ∀ (A : ProtoTile), H w (TileTranslation A x) =
            TileTranslation (H w A) (-x)) → ((∀ (w : GaussianInt), ∀ (A : ProtoTile), ∀ (B :
            ProtoTile), ∀ (C : ProtoTile), TouchingTriple A B C ↔ TouchingTriple (H w A) (H w B)
            (H w C)) → ((∀ (A : ProtoTile), (QuarterTurnSymmetric A) → (∃ w : GaussianInt,
            GaussianRealPoint w = (2 : Real) • TileCentroid A ∧ E (H w A) A)) → (∀ (A :
            ProtoTile), (QuarterTurnSymmetric A) → (∀ (x : GaussianInt), ∀ (y : GaussianInt),
            TouchingTriple A (TileTranslation A x) (TileTranslation A y) ↔ TouchingTriple A
            (TileTranslation A (-x)) (TileTranslation A (-y)))))))) ) := by
  classical
  intro E etranslate triple_obs H half_translate half_cov half_center A hs x y
  obtain ⟨w, _, he⟩ := half_center A hs
  exact (half_cov w A (TileTranslation A x) (TileTranslation A y)).trans
    (triple_obs he
      (by rw [half_translate]; exact etranslate he (-x))
      (by rw [half_translate]; exact etranslate he (-y)))

private theorem parent_half :
    (by
      classical
      exact
        let E (A B : ProtoTile) : Prop :=
          A.cells = B.cells ∧ (A.cells = ∅ → A.anchor = B.anchor)
        (∀ {A : ProtoTile}, ∀ {B : ProtoTile}, (E A B) → (∀ (v : GaussianInt), E (TileTranslation
            A v) (TileTranslation B v))) → ((∀ {A : ProtoTile}, ∀ {A' : ProtoTile}, ∀
            {B : ProtoTile}, ∀ {B' : ProtoTile}, ∀ {C : ProtoTile}, ∀ {C' : ProtoTile}, (E A A')
            → ((E B B') → ((E C C') → (TouchingTriple A B C ↔ TouchingTriple A' B' C')))) → ((∀
            (A : ProtoTile), ∀ (x : GaussianInt), ∀ (y : GaussianInt), TileTranslation
            (TileTranslation A x) y = TileTranslation A (x + y)) → ((∀ (A : ProtoTile),
            TileTranslation A 0 = A) → (
        let H (w : GaussianInt) (A : ProtoTile) :=
          TileTranslation (TileQuarterTurn (TileQuarterTurn A)) w
        (∀ (w : GaussianInt), ∀ (x : GaussianInt), ∀ (A : ProtoTile), H w (TileTranslation A x) =
            TileTranslation (H w A) (-x)) → ((∀ (w : GaussianInt), ∀ (A : ProtoTile), ∀ (B :
            ProtoTile), ∀ (C : ProtoTile), TouchingTriple A B C ↔ TouchingTriple (H w A) (H w B)
            (H w C)) → ((∀ (A : ProtoTile), (QuarterTurnSymmetric A) → (∃ w : GaussianInt,
            GaussianRealPoint w = (2 : Real) • TileCentroid A ∧ E (H w A) A)) → ((∀ (A :
            ProtoTile), (QuarterTurnSymmetric A) → (∀ (w : GaussianInt), ∀ (z : GaussianInt),
            (GaussianRealPoint w - (2 : Real) • TileCentroid A = GaussianRealPoint z) → (E (H w
            A) (TileTranslation A z)))) → (∀ (A : ProtoTile), ∀ (U : ProtoTile),
            (QuarterTurnSymmetric A) → ((QuarterTurnSymmetric U) → (∀ (x : GaussianInt), ∀ (z :
            GaussianInt), (TileCentroid U - TileCentroid A = (1 / 2 : Real) • GaussianRealPoint
            z) → (TouchingTriple A (TileTranslation A x) U ↔ TouchingTriple A (TileTranslation A
            x) (TileTranslation U (x - z))))))))))))) ) := by
  classical
  intro E etranslate triple_obs translate_add translate_zero H half_translate half_cov
      half_center half_other A U hsA hsU x z hcent
  obtain ⟨w, hw, he⟩ := half_center A hsA
  have hz : GaussianRealPoint w - (2 : Real) • TileCentroid U = GaussianRealPoint (-z) := by
    rw [hw]
    have hr := congrArg Prod.fst hcent
    have hi := congrArg Prod.snd hcent
    apply Prod.ext <;> simp [GaussianRealPoint] at hr hi ⊢ <;> linarith
  have hu := half_other U hsU w (-z) hz
  have hh := (half_cov w A (TileTranslation A x) U).trans
    (triple_obs he (by rw [half_translate]; exact etranslate he (-x)) hu)
  have ht := (TouchingTripleCovariance A (TileTranslation A (-x))
    (TileTranslation U (-z)) x).1
  rw [translate_add, translate_add, neg_add_cancel, translate_zero] at ht
  have perm : TouchingTriple (TileTranslation A x) A
      (TileTranslation U (-z + x)) ↔
      TouchingTriple A (TileTranslation A x) (TileTranslation U (-z + x)) := by
    constructor
    · intro h; exact ((TouchingTriplePermutations _ _ _).mp h).2.1
    · intro h; exact ((TouchingTriplePermutations _ _ _).mp h).2.1
  simpa only [sub_eq_add_neg, add_comm] using hh.trans (ht.trans perm)

private theorem point_add :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (y : GaussianInt), GaussianRealPoint (x + y) = GaussianRealPoint x
            + GaussianRealPoint y ) := by
  classical
  intro x y
  ext <;> simp [GaussianRealPoint]

private theorem point_sub :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (y : GaussianInt), GaussianRealPoint (x - y) = GaussianRealPoint x
            - GaussianRealPoint y ) := by
  classical
  intro x y
  ext <;> simp [GaussianRealPoint]

private theorem cent_translate :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (x : GaussianInt), TileCentroid (TileTranslation A x) = TileCentroid
            A + GaussianRealPoint x ) := by
  classical
  intro A x
  exact (TileTranslationFormulas A x).2.2.2.2.1

private theorem signs :
    (by
      classical
      exact
        (∀ (A : ProtoTile), ∀ (x : GaussianInt), ∀ (y : GaussianInt), TileTranslation
            (TileTranslation A x) y = TileTranslation A (x + y)) → ((∀ (A : ProtoTile),
            TileTranslation A 0 = A) → ((∀ (A : ProtoTile), ∀ (U : ProtoTile),
            (QuarterTurnSymmetric A) → ((QuarterTurnSymmetric U) → (∀ (x : GaussianInt), ∀ (z :
            GaussianInt), (TileCentroid U - TileCentroid A = (1 / 2 : Real) • GaussianRealPoint
            z) → (TouchingTriple A (TileTranslation A x) U ↔ TouchingTriple A (TileTranslation A
            x) (TileTranslation U (x - z)))))) → ((∀ (x : GaussianInt), ∀ (y : GaussianInt),
            GaussianRealPoint (x + y) = GaussianRealPoint x + GaussianRealPoint y) → ((∀ (x :
            GaussianInt), ∀ (y : GaussianInt), GaussianRealPoint (x - y) = GaussianRealPoint x -
            GaussianRealPoint y) → ((∀ (x : GaussianInt), GaussianRealPoint (-x) =
            -GaussianRealPoint x) → ((∀ (A : ProtoTile), ∀ (x : GaussianInt), TileCentroid
            (TileTranslation A x) = TileCentroid A + GaussianRealPoint x) → (
        let plus (x : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint x + GaussianRealPoint (GaussianQuarterTurn x))
        let minus (x : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint x - GaussianRealPoint (GaussianQuarterTurn x))
        ∀ (C : CircleCoordinates), ∀ (A : ProtoTile), (QuarterTurnSymmetric A) → ((∀ U,
            BandPrototile C U → QuarterTurnSymmetric U) → (∀ (x : GaussianInt), (∀ U,
            BandPrototile C U → TileCentroid U - TileCentroid A = plus x → TouchingTriple A
            (TileTranslation A x) U) ↔ (∀ U, BandPrototile C U → TileCentroid U - TileCentroid A
            = minus x → TouchingTriple A (TileTranslation A x) U)))))))))) ) := by
  classical
  intro translate_add translate_zero parent_half point_add point_sub point_neg cent_translate
      plus minus C A hsA hsC x
  constructor
  · intro hp U hU hc
    let U' := TileTranslation U (GaussianQuarterTurn x)
    have hU' := BandPrototileTranslation C U (GaussianQuarterTurn x) hU
    have hc' : TileCentroid U' - TileCentroid A = plus x := by
      rw [cent_translate]
      have hr := congrArg Prod.fst hc
      have hi := congrArg Prod.snd hc
      apply Prod.ext <;> simp [plus, minus] at hr hi ⊢ <;> linarith
    have hh := (parent_half A U' hsA (hsC U' hU') x (x + GaussianQuarterTurn x)
      (by simpa only [point_add] using hc')).mp (hp U' hU' hc')
    dsimp [U'] at hh
    rw [translate_add] at hh
    have hz : GaussianQuarterTurn x + (x - (x + GaussianQuarterTurn x)) = 0 := by ring
    simpa only [hz, translate_zero] using hh
  · intro hm U hU hc
    let U' := TileTranslation U (-GaussianQuarterTurn x)
    have hU' := BandPrototileTranslation C U (-GaussianQuarterTurn x) hU
    have hc' : TileCentroid U' - TileCentroid A = minus x := by
      rw [cent_translate, point_neg]
      have hr := congrArg Prod.fst hc
      have hi := congrArg Prod.snd hc
      apply Prod.ext <;> simp [plus, minus] at hr hi ⊢ <;> linarith
    have hh := (parent_half A U' hsA (hsC U' hU') x (x - GaussianQuarterTurn x)
      (by simpa only [point_sub] using hc')).mp (hm U' hU' hc')
    dsimp [U'] at hh
    rw [translate_add] at hh
    have hz : -GaussianQuarterTurn x + (x - (x - GaussianQuarterTurn x)) = 0 := by ring
    simpa only [hz, translate_zero] using hh

private theorem radd :
    (by
      classical
      exact
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        ∀ (h : BandPackingSymmetry), ∀ (p : Real × Real), ∀ (t : Real × Real), R h (p + t) = R h
            p + R h t ) := by
  classical
  intro R h p t
  induction h generalizing p t with
  | identity => rfl
  | negate => ext <;> simp [R]; ring
  | conjugate => ext <;> simp [R]; ring
  | shift w => rfl
  | comp h k ih ik => simp [R, ih, ik]

private theorem rsub :
    (by
      classical
      exact
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        ∀ (h : BandPackingSymmetry), ∀ (p : Real × Real), ∀ (t : Real × Real), R h (p - t) = R h
            p - R h t ) := by
  classical
  intro R h p t
  induction h generalizing p t with
  | identity => rfl
  | negate => ext <;> simp [R]; ring
  | conjugate => ext <;> simp [R]; ring
  | shift w => rfl
  | comp h k ih ik => simp [R, ih, ik]

private theorem rsmul :
    (by
      classical
      exact
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        ∀ (h : BandPackingSymmetry), ∀ (c : Real), ∀ (p : Real × Real), R h (c • p) = c • R h p )
            := by
  classical
  intro R h c p
  induction h generalizing p with
  | identity => rfl
  | negate => ext <;> simp [R]
  | conjugate => ext <;> simp [R]
  | shift w => rfl
  | comp h k ih ik => simp [R, ih, ik]

private theorem rpoint :
    (by
      classical
      exact
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        ∀ (h : BandPackingSymmetry), ∀ (w : GaussianInt), R h (GaussianRealPoint w) =
            GaussianRealPoint (BandPackingSymmetryVectorAction h w) ) := by
  classical
  intro R h w
  induction h generalizing w with
  | identity => rfl
  | negate => simp [R, BandPackingSymmetryVectorAction, GaussianRealPoint, GaussianQuarterTurn]
  | conjugate => simp [R, BandPackingSymmetryVectorAction, GaussianRealPoint, GaussianReflection]
  | shift w => rfl
  | comp h k ih ik => simp [R, BandPackingSymmetryVectorAction, ih, ik]

private theorem rminusq :
    (by
      classical
      exact
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        (∀ (h : BandPackingSymmetry), ∀ (p : Real × Real), R h (-p) = -R h p) → (∀ (h :
            BandPackingSymmetry), ∀ (p : Real × Real), R h (p.2, -p.1) = -R h (-p.2, p.1)) ) := by
  classical
  intro R rneg h p
  rw [show (p.2, -p.1) = -(-p.2, p.1) by simp, rneg]

private theorem rq :
    (by
      classical
      exact
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        (∀ (h : BandPackingSymmetry), ∀ (p : Real × Real), R h (p.2, -p.1) = -R h (-p.2, p.1)) →
            (∀ (h : BandPackingSymmetry), ∀ (p : Real × Real), R h (-p.2, p.1) = if
            BandPackingSymmetryReversesOrientation h then -(-(R h p).2, (R h p).1) else (-(R h
            p).2, (R h p).1)) ) := by
  classical
  intro R rminusq h p
  induction h generalizing p with
  | identity => rfl
  | negate => simp [R, BandPackingSymmetryReversesOrientation]
  | conjugate => simp [R, BandPackingSymmetryReversesOrientation]
  | shift w => rfl
  | comp h k ih ik =>
      change R h (R k (-p.2, p.1)) =
        if xor (BandPackingSymmetryReversesOrientation h)
          (BandPackingSymmetryReversesOrientation k) then
            -(-(R h (R k p)).2, (R h (R k p)).1)
        else (-(R h (R k p)).2, (R h (R k p)).1)
      rw [ik]
      cases hh : BandPackingSymmetryReversesOrientation h <;>
        cases hk : BandPackingSymmetryReversesOrientation k <;>
        simp [hh, rminusq, ih]

private theorem rinj :
    (by
      classical
      exact
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        ∀ (h : BandPackingSymmetry), Function.Injective (R h) ) := by
  classical
  intro R h
  induction h with
  | identity => exact Function.injective_id
  | shift w => exact Function.injective_id
  | negate =>
      intro p t he
      have hr := congrArg Prod.fst he
      have hi := congrArg Prod.snd he
      apply Prod.ext <;> simp [R] at hr hi ⊢ <;> linarith
  | conjugate =>
      intro p t he
      have hr := congrArg Prod.fst he
      have hi := congrArg Prod.snd he
      apply Prod.ext <;> simp [R] at hr hi ⊢ <;> linarith
  | comp h k ih ik => exact ih.comp ik

private theorem rcent :
    (by
      classical
      exact
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        ∀ (h : BandPackingSymmetry), ∀ (A : ProtoTile), TileCentroid
            (BandPackingSymmetryTileAction h A) = R h (TileCentroid A) ) := by
  classical
  intro R h A
  induction h generalizing A with
  | identity => rfl
  | shift w => rfl
  | negate => exact (TileQuarterTurnFormulas A).2.2.2.2.1
  | conjugate =>
      simp [BandPackingSymmetryTileAction, R,
        (TileQuarterTurnFormulas _).2.2.2.2.1,
        (TileReflectionFormulas _).2.2.2.2.1]
  | comp h k ih ik => simp [BandPackingSymmetryTileAction, R, ih, ik]

private theorem rplus :
    (by
      classical
      exact
        let plus (x : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint x + GaussianRealPoint (GaussianQuarterTurn x))
        let minus (x : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint x - GaussianRealPoint (GaussianQuarterTurn x))
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        (∀ (h : BandPackingSymmetry), ∀ (p : Real × Real), ∀ (t : Real × Real), R h (p + t) = R h
            p + R h t) → ((∀ (h : BandPackingSymmetry), ∀ (c : Real), ∀ (p : Real × Real), R h (c
            • p) = c • R h p) → ((∀ (h : BandPackingSymmetry), ∀ (w : GaussianInt), R h
            (GaussianRealPoint w) = GaussianRealPoint (BandPackingSymmetryVectorAction h w)) →
            ((∀ (h : BandPackingSymmetry), ∀ (p : Real × Real), R h (-p.2, p.1) = if
            BandPackingSymmetryReversesOrientation h then -(-(R h p).2, (R h p).1) else (-(R h
            p).2, (R h p).1)) → (∀ (h : BandPackingSymmetry), ∀ (x : GaussianInt), R h (plus x) =
            if BandPackingSymmetryReversesOrientation h then minus
            (BandPackingSymmetryVectorAction h x) else plus (BandPackingSymmetryVectorAction h
            x))))) ) := by
  classical
  intro plus minus R radd rsmul rpoint rq h x
  have hq : GaussianRealPoint (GaussianQuarterTurn x) =
      (-(GaussianRealPoint x).2, (GaussianRealPoint x).1) := by
    simp [GaussianRealPoint, GaussianQuarterTurn]
  dsimp only [plus, minus]
  rw [rsmul, radd, hq, rq, rpoint]
  cases hh : BandPackingSymmetryReversesOrientation h <;>
    simp [GaussianRealPoint, GaussianQuarterTurn, sub_eq_add_neg]

private theorem rminus :
    (by
      classical
      exact
        let plus (x : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint x + GaussianRealPoint (GaussianQuarterTurn x))
        let minus (x : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint x - GaussianRealPoint (GaussianQuarterTurn x))
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        (∀ (h : BandPackingSymmetry), ∀ (p : Real × Real), ∀ (t : Real × Real), R h (p - t) = R h
            p - R h t) → ((∀ (h : BandPackingSymmetry), ∀ (c : Real), ∀ (p : Real × Real), R h (c
            • p) = c • R h p) → ((∀ (h : BandPackingSymmetry), ∀ (w : GaussianInt), R h
            (GaussianRealPoint w) = GaussianRealPoint (BandPackingSymmetryVectorAction h w)) →
            ((∀ (h : BandPackingSymmetry), ∀ (p : Real × Real), R h (-p.2, p.1) = if
            BandPackingSymmetryReversesOrientation h then -(-(R h p).2, (R h p).1) else (-(R h
            p).2, (R h p).1)) → (∀ (h : BandPackingSymmetry), ∀ (x : GaussianInt), R h (minus x)
            = if BandPackingSymmetryReversesOrientation h then plus
            (BandPackingSymmetryVectorAction h x) else minus (BandPackingSymmetryVectorAction h
            x))))) ) := by
  classical
  intro plus minus R rsub rsmul rpoint rq h x
  have hq : GaussianRealPoint (GaussianQuarterTurn x) =
      (-(GaussianRealPoint x).2, (GaussianRealPoint x).1) := by
    simp [GaussianRealPoint, GaussianQuarterTurn]
  dsimp only [plus, minus]
  rw [rsmul, rsub, hq, rq, rpoint]
  cases hh : BandPackingSymmetryReversesOrientation h <;>
    simp [GaussianRealPoint, GaussianQuarterTurn, sub_eq_add_neg]

private theorem lneg :
    (by
      classical
      exact
        ∀ (h : BandPackingSymmetry), ∀ (x : GaussianInt), BandPackingSymmetryVectorAction h (-x)
            = -BandPackingSymmetryVectorAction h x ) := by
  classical
  intro h x
  induction h generalizing x with
  | identity => rfl
  | negate => ext <;> simp [BandPackingSymmetryVectorAction, GaussianQuarterTurn]
  | conjugate => ext <;> simp [BandPackingSymmetryVectorAction, GaussianReflection]
  | shift w => rfl
  | comp h k ih ik => simp only [BandPackingSymmetryVectorAction, ih, ik]

private theorem tile_surj :
    (by
      classical
      exact
        ∀ (h : BandPackingSymmetry), Function.Surjective (BandPackingSymmetryTileAction h) ) := by
  classical
  intro h
  obtain ⟨k, _, _, _, _, _, hright, _⟩ := BandPackingSymmetryInversePhaseCancellation.2 h
  intro U
  exact ⟨BandPackingSymmetryTileAction k U, hright U⟩

private theorem sigma_surj :
    (by
      classical
      exact
        let sigma (h : BandPackingSymmetry) (i : Fin 3) : Fin 3 :=
          if BandPackingSymmetryReversesOrientation h then -i else i
        (∀ (h : BandPackingSymmetry), ∀ (i : Fin 3), sigma h (sigma h i) = i) → (∀ (h :
            BandPackingSymmetry), Function.Surjective (sigma h)) ) := by
  classical
  intro sigma sigma_inv h i
  exact ⟨sigma h i, sigma_inv h i⟩

private theorem parent :
    (by
      classical
      exact
        let sigma (h : BandPackingSymmetry) (i : Fin 3) : Fin 3 :=
          if BandPackingSymmetryReversesOrientation h then -i else i
        ∀ (h : BandPackingSymmetry), ∀ (p : Fin 4 → CircleCoordinates), ∀ (i : Fin 3),
            BandPackingSymmetryQuadrupleAction h p (sigma h i).succ =
            BandPackingSymmetryCircleAction h (p i.succ) ) := by
  classical
  intro sigma h p i
  have neg1 : -(1 : Fin 3) = 2 := rfl
  have neg2 : -(2 : Fin 3) = 1 := rfl
  cases hh : BandPackingSymmetryReversesOrientation h <;> fin_cases i <;>
    simp [sigma, BandPackingSymmetryQuadrupleAction, hh, neg1, neg2]

private theorem forward :
    (by
      classical
      exact
        (∀ (A : ProtoTile), (QuarterTurnSymmetric A) → (∀ (x : GaussianInt), ∀ (y : GaussianInt),
            TouchingTriple A (TileTranslation A x) (TileTranslation A y) ↔ TouchingTriple A
            (TileTranslation A (-x)) (TileTranslation A (-y)))) → (
        let plus (x : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint x + GaussianRealPoint (GaussianQuarterTurn x))
        let minus (x : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint x - GaussianRealPoint (GaussianQuarterTurn x))
        (∀ (C : CircleCoordinates), ∀ (A : ProtoTile), (QuarterTurnSymmetric A) → ((∀ U,
            BandPrototile C U → QuarterTurnSymmetric U) → (∀ (x : GaussianInt), (∀ U,
            BandPrototile C U → TileCentroid U - TileCentroid A = plus x → TouchingTriple A
            (TileTranslation A x) U) ↔ (∀ U, BandPrototile C U → TileCentroid U - TileCentroid A
            = minus x → TouchingTriple A (TileTranslation A x) U)))) → (
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        (∀ (h : BandPackingSymmetry), ∀ (p : Real × Real), ∀ (t : Real × Real), R h (p - t) = R h
            p - R h t) → ((∀ (h : BandPackingSymmetry), Function.Injective (R h)) → ((∀ (h :
            BandPackingSymmetry), ∀ (A : ProtoTile), TileCentroid (BandPackingSymmetryTileAction
            h A) = R h (TileCentroid A)) → ((∀ (h : BandPackingSymmetry), ∀ (x : GaussianInt), R
            h (plus x) = if BandPackingSymmetryReversesOrientation h then minus
            (BandPackingSymmetryVectorAction h x) else plus (BandPackingSymmetryVectorAction h
            x)) → ((∀ (h : BandPackingSymmetry), ∀ (x : GaussianInt), R h (minus x) = if
            BandPackingSymmetryReversesOrientation h then plus (BandPackingSymmetryVectorAction h
            x) else minus (BandPackingSymmetryVectorAction h x)) → ((∀ (h : BandPackingSymmetry),
            ∀ (x : GaussianInt), BandPackingSymmetryVectorAction h (-x) =
            -BandPackingSymmetryVectorAction h x) → ((∀ (h : BandPackingSymmetry),
            Function.Surjective (BandPackingSymmetryTileAction h)) → (
        let incoming (p : Fin 4 → CircleCoordinates) (i : Fin 3) :=
          BandVectors.1 (p i.succ) (p 0)
        let P3 (p : Fin 4 → CircleCoordinates) (A : ProtoTile) : Prop :=
          ∀ i : Fin 3, TouchingTriple A (TileTranslation A (incoming p i))
            (TileTranslation A (-incoming p (i + 1)))
        let P4 (p : Fin 4 → CircleCoordinates) (A : ProtoTile) : Prop :=
          ∀ (i : Fin 3), ∀ (U : ProtoTile), BandPrototile (p i.succ) U →
            TileCentroid U - TileCentroid A = plus (incoming p i) →
            TouchingTriple A (TileTranslation A (incoming p i)) U
        let P5 (p : Fin 4 → CircleCoordinates) (A : ProtoTile) : Prop :=
          ∀ (i : Fin 3), ∀ (U : ProtoTile), ∀ (V : ProtoTile), BandPrototile (p i.succ) U →
            BandPrototile (p ((i + 1).succ)) V →
            TileCentroid U - TileCentroid A = plus (incoming p i) →
            TileCentroid V - TileCentroid A = minus (incoming p (i + 1)) →
            TouchingTriple A U V
        let P (p : Fin 4 → CircleCoordinates) (A : ProtoTile) : Prop :=
          (1 < (p 0).1 → P3 p A) ∧ (1 < (p 0).1 → P4 p A) ∧ P5 p A
        let sigma (h : BandPackingSymmetry) (i : Fin 3) : Fin 3 :=
          if BandPackingSymmetryReversesOrientation h then -i else i
        (∀ (h : BandPackingSymmetry), Function.Surjective (sigma h)) → ((∀ (h :
            BandPackingSymmetry), ∀ (p : Fin 4 → CircleCoordinates), ∀ (i : Fin 3),
            BandPackingSymmetryQuadrupleAction h p (sigma h i).succ =
            BandPackingSymmetryCircleAction h (p i.succ)) → (∀ (h : BandPackingSymmetry), ∀ (p :
            Fin 4 → CircleCoordinates), ∀ (A : ProtoTile), (BandPackingSymmetryScopedPhase h p
            false) → ((QuarterTurnSymmetric A) → ((∀ (i : Fin 3), ∀ (U : ProtoTile),
            BandPrototile (p i.succ) U → QuarterTurnSymmetric U) → (P p A → P
            (BandPackingSymmetryQuadrupleAction h p) (BandPackingSymmetryTileAction h
            A))))))))))))))) ) := by
  classical
  intro neg_triple plus minus signs R rsub rinj rcent rplus rminus lneg tile_surj incoming P3 P4
      P5 P sigma sigma_surj parent h p A hph hsA hsP
  let pg := BandPackingSymmetryQuadrupleAction h p
  let A' := BandPackingSymmetryTileAction h A
  have curv : (pg 0).1 = (p 0).1 := (BandPackingSymmetryCovariance h).1 (p 0)
  have hsA' : QuarterTurnSymmetric A' :=
    ((BandPackingSymmetryTilingTransport h).2.2.2.2.1 A).mp hsA
  have vec (i : Fin 3) : incoming pg (sigma h i) =
      BandPackingSymmetryVectorAction h (incoming p i) := by
    have hv := (hph i).1
    simpa only [BandPackingSymmetryScopedPhase, incoming, sigma,
      Bool.false_eq_true, ite_false, one_mul] using hv
  have proto (i : Fin 3) (U : ProtoTile) : BandPrototile (p i.succ) U ↔
      BandPrototile (pg (sigma h i).succ) (BandPackingSymmetryTileAction h U) := by
    dsimp only [pg]
    rw [parent]
    exact (BandPackingSymmetryCovariance h).2.1 (p i.succ) U
  have pull (i : Fin 3) (U : ProtoTile) (hU : BandPrototile (pg (sigma h i).succ) U) :
      ∃ V, BandPrototile (p i.succ) V ∧ BandPackingSymmetryTileAction h V = U := by
    obtain ⟨V, rfl⟩ := tile_surj h U
    exact ⟨V, (proto i V).mpr hU, rfl⟩
  have offset (U : ProtoTile) :
      TileCentroid (BandPackingSymmetryTileAction h U) - TileCentroid A' =
        R h (TileCentroid U - TileCentroid A) := by
    rw [rcent, rcent, rsub]
  have cp (i : Fin 3) : R h (plus (incoming p i)) =
      if BandPackingSymmetryReversesOrientation h then minus (incoming pg (sigma h i))
      else plus (incoming pg (sigma h i)) := by
    rw [rplus, vec]
  have cm (i : Fin 3) : R h (minus (incoming p i)) =
      if BandPackingSymmetryReversesOrientation h then plus (incoming pg (sigma h i))
      else minus (incoming pg (sigma h i)) := by
    rw [rminus, vec]
  have triple (U V W : ProtoTile) :=
    (BandPackingSymmetryTilingTransport h).2.2.2.2.2.1 U V W
  have translate (U : ProtoTile) (x : GaussianInt) :=
    (BandPackingSymmetryTilingTransport h).2.2.2.2.2.2.1 U x
  intro hpack
  rcases hpack with ⟨h3, h4, h5⟩
  cases hh : BandPackingSymmetryReversesOrientation h
  · have vp (i : Fin 3) : incoming pg i = BandPackingSymmetryVectorAction h (incoming p i) := by
      simpa only [sigma, hh, Bool.false_eq_true, ite_false] using vec i
    have cpp (i : Fin 3) : R h (plus (incoming p i)) = plus (incoming pg i) := by
      simpa only [sigma, hh, Bool.false_eq_true, ite_false] using cp i
    have cmm (i : Fin 3) : R h (minus (incoming p i)) = minus (incoming pg i) := by
      simpa only [sigma, hh, Bool.false_eq_true, ite_false] using cm i
    refine ⟨?_, ?_, ?_⟩
    · intro c i
      have ht := (triple _ _ _).mp (h3 (by rwa [curv] at c) i)
      rw [translate, translate, lneg, ← vp i, ← vp (i + 1)] at ht
      exact ht
    · intro c i U hU hc
      obtain ⟨V, hV, rfl⟩ := pull i U (by simpa only [sigma, hh, Bool.false_eq_true, ite_false]
          using hU)
      rw [offset] at hc
      have hc0 := rinj h (hc.trans (cpp i).symm)
      have ht := (triple _ _ _).mp (h4 (by rwa [curv] at c) i V hV hc0)
      rw [translate, ← vp i] at ht
      exact ht
    · intro i U V hU hV hcU hcV
      obtain ⟨U0, hU0, rfl⟩ := pull i U (by simpa only [sigma, hh, Bool.false_eq_true,
          ite_false] using hU)
      obtain ⟨V0, hV0, rfl⟩ := pull (i + 1) V
        (by simpa only [sigma, hh, Bool.false_eq_true, ite_false] using hV)
      rw [offset] at hcU hcV
      have hcU0 := rinj h (hcU.trans (cpp i).symm)
      have hcV0 := rinj h (hcV.trans (cmm (i + 1)).symm)
      exact (triple _ _ _).mp (h5 i U0 V0 hU0 hV0 hcU0 hcV0)
  · have spred (i : Fin 3) : sigma h (i - 1) = sigma h i + 1 := by
      simp only [sigma, hh, ite_true]
      abel
    have vpred (i : Fin 3) : incoming pg (sigma h i + 1) =
        BandPackingSymmetryVectorAction h (incoming p (i - 1)) := by
      rw [← spred]
      exact vec (i - 1)
    have cpm (i : Fin 3) : R h (plus (incoming p i)) = minus (incoming pg (sigma h i)) := by
      simpa only [hh, ite_true] using cp i
    have cmp (i : Fin 3) : R h (minus (incoming p i)) = plus (incoming pg (sigma h i)) := by
      simpa only [hh, ite_true] using cm i
    refine ⟨?_, ?_, ?_⟩
    · intro c k
      obtain ⟨i, rfl⟩ := sigma_surj h k
      have ht := (triple _ _ _).mp (h3 (by rwa [curv] at c) (i - 1))
      rw [translate, translate, lneg, sub_add_cancel, ← vpred i, ← vec i] at ht
      have hn := (neg_triple A' hsA' (incoming pg (sigma h i + 1))
        (-incoming pg (sigma h i))).mp ht
      simpa only [neg_neg] using ((TouchingTriplePermutations _ _ _).mp hn).1
    · intro c k U hU hc
      obtain ⟨i, rfl⟩ := sigma_surj h k
      obtain ⟨V, hV, rfl⟩ := pull i U hU
      rw [offset] at hc
      have hc0 := rinj h (hc.trans (cmp i).symm)
      have hm := (signs (p i.succ) A hsA (hsP i) (incoming p i)).mp
        (h4 (by rwa [curv] at c) i)
      have ht := (triple _ _ _).mp (hm V hV hc0)
      rw [translate, ← vec i] at ht
      exact ht
    · intro k U V hU hV hcU hcV
      obtain ⟨i, rfl⟩ := sigma_surj h k
      obtain ⟨U0, hU0, rfl⟩ := pull i U hU
      obtain ⟨V0, hV0, rfl⟩ := pull (i - 1) V (by simpa only [spred] using hV)
      rw [offset] at hcU hcV
      have hcU0 := rinj h (hcU.trans (cmp i).symm)
      have hcV0 := rinj h (hcV.trans (by simpa only [spred] using (cpm (i - 1)).symm))
      have ht := (triple _ _ _).mp (h5 (i - 1) V0 U0 hV0
        (by simpa only [sub_add_cancel] using hU0) hcV0
        (by simpa only [sub_add_cancel] using hcU0))
      exact ((TouchingTriplePermutations _ _ _).mp ht).1

private theorem flip :
    (by
      classical
      exact
        let incoming (p : Fin 4 → CircleCoordinates) (i : Fin 3) :=
          BandVectors.1 (p i.succ) (p 0)
        ∀ (p : Fin 4 → CircleCoordinates), (ProperBandQuadruple p) → (∀ (i : Fin 3),
            BandVectors.1 (p 0) (p i.succ) = GaussianQuarterTurn (incoming p i)) ) := by
  classical
  intro incoming p hp i
  have hf := ((VectorRecursionLaws p hp.1).2.2.2.2 hp i).1
  have hm (x : GaussianInt) : (⟨0, 1⟩ : GaussianInt) * x = GaussianQuarterTurn x := by
    ext <;> simp [GaussianQuarterTurn]
  exact hf.trans (hm _)

private theorem hsPg :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (∀ (i : Fin (3 :
            ℕ)), ∀ (U : ProtoTile), BandPrototile (q i.succ) U → QuarterTurnSymmetric U) → ((∀ (h
            : BandPackingSymmetry), Function.Surjective (BandPackingSymmetryTileAction h)) → (
        let sigma (h : BandPackingSymmetry) (i : Fin 3) : Fin 3 :=
          if BandPackingSymmetryReversesOrientation h then -i else i
        (∀ (h : BandPackingSymmetry), ∀ (i : Fin 3), sigma h (sigma h i) = i) → ((∀ (h :
            BandPackingSymmetry), ∀ (p : Fin 4 → CircleCoordinates), ∀ (i : Fin 3),
            BandPackingSymmetryQuadrupleAction h p (sigma h i).succ =
            BandPackingSymmetryCircleAction h (p i.succ)) → (∀ (i : Fin 3), ∀ (U : ProtoTile),
            BandPrototile ((BandPackingSymmetryQuadrupleAction g q) i.succ) U →
            QuarterTurnSymmetric U)))) ) := by
  classical
  intro g q hquarterParents tile_surj sigma sigma_inv parent i U hU
  obtain ⟨V, rfl⟩ := tile_surj g U
  have he := parent g q (sigma g i)
  rw [sigma_inv] at he
  rw [he] at hU
  have hV := ((BandPackingSymmetryCovariance g).2.1 (q (sigma g i).succ) V).mpr hU
  exact ((BandPackingSymmetryTilingTransport g).2.2.2.2.1 V).mp
    (hquarterParents (sigma g i) V hV)

end PackingCovarianceProof

theorem BandPackingSymmetryT3T5Covariance :
    ∀ (g : BandPackingSymmetry), ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) →
        ((BandPackingSymmetryScopedPhase g q false) → (∀ (T : ProtoTile), (BandPrototile (q 0) T)
        → ((QuarterTurnSymmetric T) → ((∀ (i : Fin 3), ∀ (U : ProtoTile), BandPrototile (q
        i.succ) U → QuarterTurnSymmetric U) → (
    let qg := BandPackingSymmetryQuadrupleAction g q
    let Tg := BandPackingSymmetryTileAction g T
    ((1 < (q 0).1 → ∀ i : Fin 3,
        TouchingTriple T
          (TileTranslation T (BandVectors.1 (q i.succ) (q 0)))
          (TileTranslation T
            (-BandVectors.1 (q ((i + 1).succ)) (q 0)))) ∧
      (1 < (q 0).1 → ∀ (i : Fin 3), ∀ (U : ProtoTile), BandPrototile (q i.succ) U →
        TileCentroid U - TileCentroid T = (1 / 2 : Real) •
          (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
            GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) →
        TouchingTriple T
          (TileTranslation T (BandVectors.1 (q i.succ) (q 0))) U) ∧
      (∀ (i : Fin 3), ∀ (U : ProtoTile), ∀ (V : ProtoTile), BandPrototile (q i.succ) U →
        BandPrototile (q ((i + 1).succ)) V →
        TileCentroid U - TileCentroid T = (1 / 2 : Real) •
          (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
            GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) →
        TileCentroid V - TileCentroid T = (1 / 2 : Real) •
          (GaussianRealPoint (BandVectors.1 (q ((i + 1).succ)) (q 0)) -
            GaussianRealPoint (BandVectors.1 (q 0) (q ((i + 1).succ)))) →
        TouchingTriple T U V)) ↔
      ((1 < (qg 0).1 → ∀ i : Fin 3,
          TouchingTriple Tg
            (TileTranslation Tg (BandVectors.1 (qg i.succ) (qg 0)))
            (TileTranslation Tg
              (-BandVectors.1 (qg ((i + 1).succ)) (qg 0)))) ∧
        (1 < (qg 0).1 → ∀ (i : Fin 3), ∀ (U : ProtoTile), BandPrototile (qg i.succ) U →
          TileCentroid U - TileCentroid Tg = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (qg i.succ) (qg 0)) +
              GaussianRealPoint (BandVectors.1 (qg 0) (qg i.succ))) →
          TouchingTriple Tg
            (TileTranslation Tg (BandVectors.1 (qg i.succ) (qg 0))) U) ∧
        (∀ (i : Fin 3), ∀ (U : ProtoTile), ∀ (V : ProtoTile), BandPrototile (qg i.succ) U →
          BandPrototile (qg ((i + 1).succ)) V →
          TileCentroid U - TileCentroid Tg = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (qg i.succ) (qg 0)) +
              GaussianRealPoint (BandVectors.1 (qg 0) (qg i.succ))) →
          TileCentroid V - TileCentroid Tg = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (qg ((i + 1).succ)) (qg 0)) -
              GaussianRealPoint (BandVectors.1 (qg 0) (qg ((i + 1).succ)))) →
          TouchingTriple Tg U V))))))) := by
  intro g q hq hphase T hT hquarterT hquarterParents
-- BODY
  classical
  -- Touching depends on cells and on anchors only for empty tiles.
  let E (A B : ProtoTile) : Prop :=
    A.cells = B.cells ∧ (A.cells = ∅ → A.anchor = B.anchor)
  have etrans {A B C : ProtoTile} (h : E A B) (k : E B C) : E A C :=
    ⟨h.1.trans k.1, fun he => (h.2 he).trans (k.2 (h.1 ▸ he))⟩
  have etranslate {A B : ProtoTile} (h : E A B) (v : GaussianInt) :=
      PackingCovarianceProof.etranslate (A := A) (B := B) h v
  have equarter {A B : ProtoTile} (h : E A B) := PackingCovarianceProof.equarter (A := A) (B := B) h
  have touching_obs {A A' B B' : ProtoTile} (ha : E A A') (hb : E B B') :=
      PackingCovarianceProof.touching_obs (A := A) (A' := A') (B := B) (B' := B') ha hb
  have triple_obs {A A' B B' C C' : ProtoTile}
      (ha : E A A') (hb : E B B') (hc : E C C') := PackingCovarianceProof.triple_obs touching_obs
          (A := A) (A' := A') (B := B) (B' := B') (C := C) (C' := C') ha hb hc
  have translate_add := PackingCovarianceProof.translate_add
  have translate_zero := PackingCovarianceProof.translate_zero
  have quarter_translate := PackingCovarianceProof.quarter_translate
  have qtwo := PackingCovarianceProof.qtwo
  -- Two centered integral quarter-turns give a common centered half-turn.
  let H (w : GaussianInt) (A : ProtoTile) :=
    TileTranslation (TileQuarterTurn (TileQuarterTurn A)) w
  have half_translate := PackingCovarianceProof.half_translate translate_add quarter_translate qtwo
  have half_cov := PackingCovarianceProof.half_cov
  have half_center := PackingCovarianceProof.half_center etrans etranslate equarter translate_add
      quarter_translate
  have half_other := PackingCovarianceProof.half_other etranslate translate_add half_center
  have neg_triple := PackingCovarianceProof.neg_triple etranslate triple_obs half_translate
      half_cov half_center
  have parent_half := PackingCovarianceProof.parent_half etranslate triple_obs translate_add
      translate_zero half_translate half_cov half_center half_other
  have point_add := PackingCovarianceProof.point_add
  have point_sub := PackingCovarianceProof.point_sub
  have point_neg (x : GaussianInt) : GaussianRealPoint (-x) = -GaussianRealPoint x := by
    ext <;> simp [GaussianRealPoint]
  have cent_translate := PackingCovarianceProof.cent_translate
  let plus (x : GaussianInt) : Real × Real :=
    (1 / 2 : Real) • (GaussianRealPoint x + GaussianRealPoint (GaussianQuarterTurn x))
  let minus (x : GaussianInt) : Real × Real :=
    (1 / 2 : Real) • (GaussianRealPoint x - GaussianRealPoint (GaussianQuarterTurn x))
  -- Half-turn, common translation, and permutation exchange the two offsets.
  have signs := PackingCovarianceProof.signs translate_add translate_zero parent_half point_add
      point_sub point_neg cent_translate
  -- Word induction is used only for generic linear grid-action facts.
  let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
    BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
      (fun p => (-p.1, p.2)) (fun _ p => p)
      (fun _ _ f k p => f (k p))
  have radd := PackingCovarianceProof.radd
  have rsub := PackingCovarianceProof.rsub
  have rsmul (h : BandPackingSymmetry) (c : Real) (p : Real × Real) :
      R h (c • p) = c • R h p := PackingCovarianceProof.rsmul h c p
  have rneg (h : BandPackingSymmetry) (p : Real × Real) : R h (-p) = -R h p := by
    simpa using rsmul h (-1) p
  have rpoint := PackingCovarianceProof.rpoint
  have rminusq := PackingCovarianceProof.rminusq rneg
  have rq := PackingCovarianceProof.rq rminusq
  have rinj := PackingCovarianceProof.rinj
  have rcent := PackingCovarianceProof.rcent
  have rplus := PackingCovarianceProof.rplus radd rsmul rpoint rq
  have rminus := PackingCovarianceProof.rminus rsub rsmul rpoint rq
  have lneg := PackingCovarianceProof.lneg
  have tile_surj := PackingCovarianceProof.tile_surj
  let incoming (p : Fin 4 → CircleCoordinates) (i : Fin 3) :=
    BandVectors.1 (p i.succ) (p 0)
  let P3 (p : Fin 4 → CircleCoordinates) (A : ProtoTile) : Prop :=
    ∀ i : Fin 3, TouchingTriple A (TileTranslation A (incoming p i))
      (TileTranslation A (-incoming p (i + 1)))
  let P4 (p : Fin 4 → CircleCoordinates) (A : ProtoTile) : Prop :=
    ∀ (i : Fin 3) (U : ProtoTile), BandPrototile (p i.succ) U →
      TileCentroid U - TileCentroid A = plus (incoming p i) →
      TouchingTriple A (TileTranslation A (incoming p i)) U
  let P5 (p : Fin 4 → CircleCoordinates) (A : ProtoTile) : Prop :=
    ∀ (i : Fin 3) (U V : ProtoTile), BandPrototile (p i.succ) U →
      BandPrototile (p ((i + 1).succ)) V →
      TileCentroid U - TileCentroid A = plus (incoming p i) →
      TileCentroid V - TileCentroid A = minus (incoming p (i + 1)) →
      TouchingTriple A U V
  let P (p : Fin 4 → CircleCoordinates) (A : ProtoTile) : Prop :=
    (1 < (p 0).1 → P3 p A) ∧ (1 < (p 0).1 → P4 p A) ∧ P5 p A
  let sigma (h : BandPackingSymmetry) (i : Fin 3) : Fin 3 :=
    if BandPackingSymmetryReversesOrientation h then -i else i
  have sigma_inv (h : BandPackingSymmetry) (i : Fin 3) : sigma h (sigma h i) = i := by
    cases hh : BandPackingSymmetryReversesOrientation h <;> simp [sigma, hh]
  have sigma_surj := PackingCovarianceProof.sigma_surj sigma_inv
  have parent := PackingCovarianceProof.parent
  -- The scoped phase identifies canonical vectors for the entire word.
  have forward := PackingCovarianceProof.forward neg_triple signs rsub rinj rcent rplus rminus
      lneg tile_surj sigma_surj parent
  have flip (p : Fin 4 → CircleCoordinates) (hp : ProperBandQuadruple p) (i : Fin 3) :
      BandVectors.1 (p 0) (p i.succ) = GaussianQuarterTurn (incoming p i) :=
          PackingCovarianceProof.flip p hp i
  have hqg := BandPackingSymmetryProperCovariance g q hq
  have hsTg : QuarterTurnSymmetric (BandPackingSymmetryTileAction g T) :=
    ((BandPackingSymmetryTilingTransport g).2.2.2.2.1 T).mp hquarterT
  have hsPg := PackingCovarianceProof.hsPg g q hquarterParents tile_surj sigma_inv parent
  dsimp only
  simp only [flip q hq, flip (BandPackingSymmetryQuadrupleAction g q) hqg]
  change P q T ↔ P (BandPackingSymmetryQuadrupleAction g q) (BandPackingSymmetryTileAction g T)
  constructor
  · exact forward g q T hphase hquarterT hquarterParents
  · intro hpack
    obtain ⟨k, _, _, hQ, _, hTile, _, _, _, _, _, hPh⟩ :=
      BandPackingSymmetryInversePhaseCancellation.2 g
    have hback := forward k (BandPackingSymmetryQuadrupleAction g q)
      (BandPackingSymmetryTileAction g T) (hPh q hq false hphase) hsTg hsPg hpack
    simpa only [hQ, hTile] using hback

end ApollonianSuperharmonic

end
