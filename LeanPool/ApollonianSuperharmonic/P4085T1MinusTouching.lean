/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetricCenteredTransport
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import LeanPool.ApollonianSuperharmonic.TouchingTripleCovariance
public import LeanPool.ApollonianSuperharmonic.TouchingTriplePermutations

-- [TABLET NODE: P4085T1MinusTouching]

/-!
# P4085T1MinusTouching

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4085T1MinusTouching (U W : ProtoTile) (y : GaussianInt)
    (hU : QuarterTurnSymmetric U) (hW : QuarterTurnSymmetric W)
    (hcent : TileCentroid W - TileCentroid U =
      (1 / 2 : Real) • GaussianRealPoint (y - GaussianQuarterTurn y))
    (hplus : TouchingTriple U (TileTranslation U y)
      (TileTranslation W (GaussianQuarterTurn y))) :
    TouchingTriple U (TileTranslation U y) W := by
-- BODY
  have shift_add (T : ProtoTile) (a b : GaussianInt) :
      TileTranslation (TileTranslation T a) b = TileTranslation T (a + b) := by
    cases T with
    | mk cells anchor =>
      apply congrArg₂ ProtoTile.mk
      · simp only [TileTranslation, Finset.image_image, Function.comp_def]
        congr 1
        funext z
        simp only [GaussianTranslation, add_assoc]
      · change (anchor + a) + b = anchor + (a + b)
        exact add_assoc _ _ _
  have turn_shift (T : ProtoTile) (a : GaussianInt) :
      TileQuarterTurn (TileTranslation T a) =
        TileTranslation (TileQuarterTurn T) (GaussianQuarterTurn a) := by
    cases T with
    | mk cells anchor =>
      have hm : (fun z : GaussianInt => GaussianQuarterTurn (z + a) - 1) =
          (fun z : GaussianInt => GaussianQuarterTurn z - 1 + GaussianQuarterTurn a) := by
        funext z
        ext <;> simp [GaussianQuarterTurn]; ring
      apply congrArg₂ ProtoTile.mk
      · simp [TileQuarterTurn, TileTranslation, GaussianTranslation,
          Finset.image_image, Function.comp_def, hm]
      · ext <;> simp [TileQuarterTurn, TileTranslation,
          GaussianTranslation, GaussianQuarterTurn, add_comm]
  have half_shift (T : ProtoTile) (a : GaussianInt) :
      TileQuarterTurn (TileQuarterTurn (TileTranslation T a)) =
        TileTranslation (TileQuarterTurn (TileQuarterTurn T)) (-a) := by
    rw [turn_shift, turn_shift]
    congr 1
  -- Compose two centered turns, retaining cells and empty-case anchors only.
  have half (T : ProtoTile) (hT : QuarterTurnSymmetric T) :
      ∃ b : GaussianInt,
        GaussianRealPoint b = (2 * (TileCentroid T).1, 2 * (TileCentroid T).2) ∧
        (TileTranslation (TileQuarterTurn (TileQuarterTurn T)) b).cells = T.cells ∧
        (T.cells = ∅ →
          (TileTranslation (TileQuarterTurn (TileQuarterTurn T)) b).anchor = T.anchor) := by
    obtain ⟨u, hu, hc, ha, _, _⟩ := QuarterTurnSymmetricCenteredTransport T hT
    let b := GaussianQuarterTurn u + u
    have heq : TileTranslation (TileQuarterTurn
        (TileTranslation (TileQuarterTurn T) u)) u =
        TileTranslation (TileQuarterTurn (TileQuarterTurn T)) b := by
      rw [turn_shift, shift_add]
    refine ⟨b, ?_, ?_, ?_⟩
    · have h₁ := congrArg Prod.fst hu
      have h₂ := congrArg Prod.snd hu
      simp [GaussianRealPoint, GaussianQuarterTurn, b] at h₁ h₂ ⊢
      constructor <;> linarith
    · rw [← heq]
      change ((TileTranslation (TileQuarterTurn T) u).cells.image
        (fun z => GaussianQuarterTurn z - 1)).image (GaussianTranslation u) = T.cells
      rw [hc]
      exact hc
    · intro ht
      rw [← heq]
      change GaussianTranslation u (GaussianQuarterTurn
        (TileTranslation (TileQuarterTurn T) u).anchor) = T.anchor
      rw [ha ht]
      exact ha ht
  have translated_same (A B : ProtoTile) (a : GaussianInt)
      (hc : A.cells = B.cells) (ha : A.cells = ∅ → A.anchor = B.anchor) :
      (TileTranslation A a).cells = (TileTranslation B a).cells ∧
      ((TileTranslation A a).cells = ∅ →
        (TileTranslation A a).anchor = (TileTranslation B a).anchor) := by
    constructor
    · exact congrArg (Finset.image (GaussianTranslation a)) hc
    · intro he
      exact congrArg (GaussianTranslation a)
        (ha ((TileTranslationFormulas A a).2.2.1.mp he))
  have pair_same (A B A' B' : ProtoTile)
      (hA : A.cells = A'.cells) (hB : B.cells = B'.cells)
      (ha : A.cells = ∅ → A.anchor = A'.anchor)
      (hb : B.cells = ∅ → B.anchor = B'.anchor) :
      TileTouching A B ↔ TileTouching A' B' := by
    have oa := ProtoTileObservableExtensionality A A' hA ha
    have ob := ProtoTileObservableExtensionality B B' hB hb
    have va := oa.2.1
    have vb := ob.2.1
    have ea := oa.2.2.1
    have eb := ob.2.2.1
    constructor
    · rintro (h | ⟨he, hm⟩ | ⟨he, hm⟩)
      · left
        simpa only [← hA, ← hB, ← va, ← vb, ← ea, ← eb] using h
      · right; left
        exact ⟨hA ▸ he, by simpa only [← va, ← vb, ← ha he] using hm⟩
      · right; right
        exact ⟨hB ▸ he, by simpa only [← va, ← vb, ← hb he] using hm⟩
    · rintro (h | ⟨he, hm⟩ | ⟨he, hm⟩)
      · left
        simpa only [hA, hB, va, vb, ea, eb] using h
      · right; left
        have he' : A.cells = ∅ := hA.trans he
        exact ⟨he', by simpa only [va, vb, ha he'] using hm⟩
      · right; right
        have he' : B.cells = ∅ := hB.trans he
        exact ⟨he', by simpa only [va, vb, hb he'] using hm⟩
  have triple_same (A B C A' B' C' : ProtoTile)
      (hA : A.cells = A'.cells) (hB : B.cells = B'.cells)
      (hC : C.cells = C'.cells)
      (ha : A.cells = ∅ → A.anchor = A'.anchor)
      (hb : B.cells = ∅ → B.anchor = B'.anchor)
      (hc : C.cells = ∅ → C.anchor = C'.anchor) :
      TouchingTriple A B C ↔ TouchingTriple A' B' C' := by
    unfold TouchingTriple
    rw [pair_same A B A' B' hA hB ha hb,
      pair_same B C B' C' hB hC hb hc, pair_same C A C' A' hC hA hc ha,
      (ProtoTileObservableExtensionality A A' hA ha).2.1,
      (ProtoTileObservableExtensionality B B' hB hb).2.1,
      (ProtoTileObservableExtensionality C C' hC hc).2.1]
  obtain ⟨bU, hbU, hcU, haU⟩ := half U hU
  obtain ⟨bW, hbW, hcW, haW⟩ := half W hW
  have hdiff : bW = bU + y - GaussianQuarterTurn y := by
    have u₁ := congrArg Prod.fst hbU
    have u₂ := congrArg Prod.snd hbU
    have w₁ := congrArg Prod.fst hbW
    have w₂ := congrArg Prod.snd hbW
    have d₁ := congrArg Prod.fst hcent
    have d₂ := congrArg Prod.snd hcent
    change (bU.re : Real) = 2 * (TileCentroid U).1 at u₁
    change (bU.im : Real) = 2 * (TileCentroid U).2 at u₂
    change (bW.re : Real) = 2 * (TileCentroid W).1 at w₁
    change (bW.im : Real) = 2 * (TileCentroid W).2 at w₂
    change (TileCentroid W).1 - (TileCentroid U).1 =
      (1 / 2 : Real) * ((y - GaussianQuarterTurn y).re : Real) at d₁
    change (TileCentroid W).2 - (TileCentroid U).2 =
      (1 / 2 : Real) * ((y - GaussianQuarterTurn y).im : Real) at d₂
    simp only [GaussianQuarterTurn, Zsqrtd.re_sub, Zsqrtd.im_sub,
      Int.cast_sub, sub_neg_eq_add, Int.cast_add] at d₁ d₂
    have re : (bW.re : Real) = (bU.re : Real) + (y.re : Real) + (y.im : Real) := by linarith
    have im : (bW.im : Real) = (bU.im : Real) + (y.im : Real) - (y.re : Real) := by linarith
    apply Zsqrtd.ext
    · change bW.re = bU.re + y.re - -y.im
      rw [sub_neg_eq_add]
      exact_mod_cast re
    · change bW.im = bU.im + y.im - y.re
      exact_mod_cast im
  let H := fun T => TileTranslation (TileQuarterTurn (TileQuarterTurn T)) (bU + y)
  have eU : H U = TileTranslation
      (TileTranslation (TileQuarterTurn (TileQuarterTurn U)) bU) y := by
    rw [shift_add]
  have eM : H (TileTranslation U y) =
      TileTranslation (TileQuarterTurn (TileQuarterTurn U)) bU := by
    dsimp [H]
    rw [half_shift, shift_add]
    congr 1
    abel
  have eW : H (TileTranslation W (GaussianQuarterTurn y)) =
      TileTranslation (TileQuarterTurn (TileQuarterTurn W)) bW := by
    dsimp [H]
    rw [half_shift, shift_add, hdiff]
    congr 1
    abel
  have certU := translated_same _ U y hcU (fun he => haU (hcU.symm.trans he))
  have certM : (H (TileTranslation U y)).cells = U.cells ∧
      ((H (TileTranslation U y)).cells = ∅ →
        (H (TileTranslation U y)).anchor = U.anchor) := by
    rw [eM]
    exact ⟨hcU, fun he => haU (hcU.symm.trans he)⟩
  have certW : (H (TileTranslation W (GaussianQuarterTurn y))).cells = W.cells ∧
      ((H (TileTranslation W (GaussianQuarterTurn y))).cells = ∅ →
        (H (TileTranslation W (GaussianQuarterTurn y))).anchor = W.anchor) := by
    rw [eW]
    exact ⟨hcW, fun he => haW (hcW.symm.trans he)⟩
  rw [← eU] at certU
  have h₁ := (TouchingTripleCovariance U (TileTranslation U y)
    (TileTranslation W (GaussianQuarterTurn y)) 0).2.1.mp hplus
  have h₂ := (TouchingTripleCovariance _ _ _ 0).2.1.mp h₁
  have h₃ := (TouchingTripleCovariance _ _ _ (bU + y)).1.mp h₂
  have hs := (triple_same (H U) (H (TileTranslation U y))
    (H (TileTranslation W (GaussianQuarterTurn y))) (TileTranslation U y) U W
    certU.1 certM.1 certW.1 certU.2 certM.2 certW.2).mp h₃
  exact ((TouchingTriplePermutations _ _ _).mp hs).2.1

end ApollonianSuperharmonic

end
