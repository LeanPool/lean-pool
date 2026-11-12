/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FordTile
public import LeanPool.ApollonianSuperharmonic.TileTranslation
public import LeanPool.ApollonianSuperharmonic.TouchingTriple
public import LeanPool.ApollonianSuperharmonic.P5110T1TranslationTriples
public import LeanPool.ApollonianSuperharmonic.P5110T1PositiveParentTriples
public import LeanPool.ApollonianSuperharmonic.P5110T1AnchoredTriples
public import LeanPool.ApollonianSuperharmonic.P5110T1ParentLocalization

-- [TABLET NODE: FordBaseTouching]

/-!
# FordBaseTouching

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem FordBaseTouching (P : FordFareyParameter) (hq : 1 < P.q) :
    let q := FordRecursiveQuadruple P
    let T := FordTile P.q
    (∀ i : Fin 3,
      TouchingTriple T
        (TileTranslation T (BandVectors.1 (q i.succ) (q 0)))
        (TileTranslation T (-BandVectors.1 (q ((i + 1).succ)) (q 0)))) ∧
    (∀ (i : Fin 3) (U : ProtoTile), BandPrototile (q i.succ) U →
      TileCentroid U - TileCentroid T =
        (1 / 2 : Real) •
          (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
            GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) →
      TouchingTriple T
        (TileTranslation T (BandVectors.1 (q i.succ) (q 0))) U) ∧
    (∀ (i : Fin 3) (U V : ProtoTile),
      BandPrototile (q i.succ) U →
      BandPrototile (q ((i + 1).succ)) V →
      TileCentroid U - TileCentroid T =
        (1 / 2 : Real) •
          (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
            GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) →
      TileCentroid V - TileCentroid T =
        (1 / 2 : Real) •
          (GaussianRealPoint (BandVectors.1 (q ((i + 1).succ)) (q 0)) -
            GaussianRealPoint (BandVectors.1 (q 0) (q ((i + 1).succ)))) →
      TouchingTriple T U V) := by
-- BODY
  have hr : 0 < P.q₁ := by
    by_contra h
    have hz : P.q₁ = 0 := by omega
    have hd := P.det₁
    simp only [hz, Nat.cast_zero, zero_mul, sub_zero] at hd
    have hdv : (P.q : Int) ∣ 1 := ⟨P.p₁, by simpa [mul_comm] using hd.symm⟩
    have := Int.eq_one_of_dvd_one (by omega : 0 ≤ (P.q : Int)) hdv
    omega
  have hs := P.q₂_pos
  obtain ⟨_, h10, h20, h30, _⟩ := (FordCoordinateConfiguration P).2 hq
  have ht := P5110T1TranslationTriples P.q₁ P.q₂ hr hs
  have hp := P5110T1PositiveParentTriples P.q₁ P.q₂ hr hs
  have he := P5110T1AnchoredTriples P.q₁ P.q₂ hr hs
  dsimp only at ht hp he ⊢
  rw [← P.sum_q] at ht hp he
  have touch_transport (A A' B B' : ProtoTile)
      (hA : A.cells = A'.cells ∧ (A.cells = ∅ → A.anchor = A'.anchor))
      (hB : B.cells = B'.cells ∧ (B.cells = ∅ → B.anchor = B'.anchor))
      (h : TileTouching A B) : TileTouching A' B' := by
    have oA := ProtoTileObservableExtensionality A A' hA.1 hA.2
    have oB := ProtoTileObservableExtensionality B B' hB.1 hB.2
    rcases h with h | h | h
    · rcases h with ⟨ha, hb, hd, hpath⟩
      left
      refine ⟨?_, ?_, ?_, ?_⟩
      · rwa [← hA.1]
      · rwa [← hB.1]
      · rwa [← hA.1, ← hB.1]
      · rwa [← oA.2.1, ← oB.2.1, ← oA.2.2.1, ← oB.2.2.1]
    · right; left
      refine ⟨?_, ?_⟩
      · exact hA.1 ▸ h.1
      · rw [← hA.2 h.1, ← oB.2.1]
        exact h.2
    · right; right
      refine ⟨?_, ?_⟩
      · exact hB.1 ▸ h.1
      · rw [← hB.2 h.1, ← oA.2.1]
        exact h.2
  have triple_transport (A A' B B' C C' : ProtoTile)
      (hA : A.cells = A'.cells ∧ (A.cells = ∅ → A.anchor = A'.anchor))
      (hB : B.cells = B'.cells ∧ (B.cells = ∅ → B.anchor = B'.anchor))
      (hC : C.cells = C'.cells ∧ (C.cells = ∅ → C.anchor = C'.anchor))
      (h : TouchingTriple A B C) : TouchingTriple A' B' C' := by
    refine ⟨touch_transport A A' B B' hA hB h.1,
      touch_transport B B' C C' hB hC h.2.1,
      touch_transport C C' A A' hC hA h.2.2.1, ?_⟩
    have oA := (ProtoTileObservableExtensionality A A' hA.1 hA.2).2.1
    have oB := (ProtoTileObservableExtensionality B B' hB.1 hB.2).2.1
    have oC := (ProtoTileObservableExtensionality C C' hC.1 hC.2).2.1
    simpa only [oA, oB, oC] using h.2.2.2
  have obs_symm (A B : ProtoTile)
      (h : A.cells = B.cells ∧ (A.cells = ∅ → A.anchor = B.anchor)) :
      B.cells = A.cells ∧ (B.cells = ∅ → B.anchor = A.anchor) :=
    ⟨h.1.symm, fun he => (h.2 (h.1.trans he)).symm⟩
  have obs_refl (A : ProtoTile) :
      A.cells = A.cells ∧ (A.cells = ∅ → A.anchor = A.anchor) := ⟨rfl, fun _ => rfl⟩
  have neg_pair (a b : Int) : -(⟨a, b⟩ : GaussianInt) = ⟨-a, -b⟩ := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa [h10, h20, h30, neg_pair] using ht.1
    · simpa [h10, h20, h30, neg_pair] using ht.2.1
    · simpa [h10, h20, h30, neg_pair] using ht.2.2
  · intro i U hU hcent
    have hloc := P5110T1ParentLocalization P hq i true U hU (by simpa using hcent)
    have hmodel : TouchingTriple (FordTile P.q)
        (TileTranslation (FordTile P.q)
          (BandVectors.1 ((FordRecursiveQuadruple P) i.succ) ((FordRecursiveQuadruple P) 0)))
        (P5110T1ParentModel P.q₁ P.q₂ i true) := by
      fin_cases i
      · simpa [h10, h20, h30] using hp.1
      · simpa [h10, h20, h30] using hp.2.1
      · simpa [h10, h20, h30] using he.1
    exact triple_transport _ _ _ _ _ _ (obs_refl _) (obs_refl _)
      (obs_symm _ _ hloc) hmodel
  · intro i U V hU hV hcentU hcentV
    have hlocU := P5110T1ParentLocalization P hq i true U hU (by simpa using hcentU)
    have hlocV := P5110T1ParentLocalization P hq (i + 1) false V hV (by
      simpa [sub_eq_add_neg] using hcentV)
    have hmodel : TouchingTriple (FordTile P.q)
        (P5110T1ParentModel P.q₁ P.q₂ i true)
        (P5110T1ParentModel P.q₁ P.q₂ (i + 1) false) := by
      fin_cases i
      · simpa using hp.2.2
      · simpa using he.2.1
      · simpa using he.2.2
    exact triple_transport _ _ _ _ _ _ (obs_refl _)
      (obs_symm _ _ hlocU) (obs_symm _ _ hlocV) hmodel

end ApollonianSuperharmonic

end
