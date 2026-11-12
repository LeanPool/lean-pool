/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5110T1ParentModel
public import LeanPool.ApollonianSuperharmonic.FordTileRecursiveIdentification
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.P4210T1FordSquareCentroid
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.P4210T1FordCellRectangles
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: P5110T1ParentLocalization]

/-!
# P5110T1ParentLocalization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5110T1ParentLocalization (P : FordFareyParameter) (hq : 1 < P.q)
    (i : Fin 3) (plus : Bool) (U : ProtoTile)
    (hU : BandPrototile ((FordRecursiveQuadruple P) i.succ) U)
    (hcent : TileCentroid U - TileCentroid (FordTile P.q) =
      (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 ((FordRecursiveQuadruple P) i.succ)
            ((FordRecursiveQuadruple P) 0)) +
          (if plus then
            GaussianRealPoint (BandVectors.1 ((FordRecursiveQuadruple P) 0)
              ((FordRecursiveQuadruple P) i.succ))
          else -GaussianRealPoint (BandVectors.1 ((FordRecursiveQuadruple P) 0)
              ((FordRecursiveQuadruple P) i.succ))))) :
    U.cells = (P5110T1ParentModel P.q₁ P.q₂ i plus).cells ∧
      (U.cells = ∅ → U.anchor = (P5110T1ParentModel P.q₁ P.q₂ i plus).anchor) := by
-- BODY
  have hr : 0 < P.q₁ := by
    by_contra h
    have hz : P.q₁ = 0 := by omega
    have hd := P.det₁
    simp only [hz, Nat.cast_zero, zero_mul, sub_zero] at hd
    have hdv : (P.q : Int) ∣ 1 := ⟨P.p₁, by simpa [mul_comm] using hd.symm⟩
    have := Int.eq_one_of_dvd_one (by omega : 0 ≤ (P.q : Int)) hdv
    omega
  obtain ⟨proper, S, hS, _, h0, _, h1, _, _, _, h2, ha2⟩ :=
    (FordTileRecursiveIdentification P).2.2 hq
  let N : Fin 3 → Bool → ProtoTile := fun j b =>
    if b then
      ![TileTranslation (S 0 true) ⟨(P.q₂ : Int), (P.q : Int)⟩,
        TileTranslation (S 1 true) ⟨-(P.q : Int), 0⟩,
        TileTranslation (S 2 false) ⟨(P.q₂ : Int), 0⟩] j
    else
      ![TileTranslation (S 0 true) ⟨(P.q : Int), 0⟩,
        TileTranslation (S 1 true) ⟨-(P.q₁ : Int), (P.q : Int)⟩,
        TileTranslation (S 2 false) ⟨-(P.q₁ : Int), 0⟩] j
  have hN (j : Fin 3) (b : Bool) :
      BandPrototile ((FordRecursiveQuadruple P) j.succ) (N j b) := by
    fin_cases j <;> cases b
    · exact BandPrototileTranslation _ _ _ (hS 0 true).1
    · exact BandPrototileTranslation _ _ _ (hS 0 true).1
    · exact BandPrototileTranslation _ _ _ (hS 1 true).1
    · exact BandPrototileTranslation _ _ _ (hS 1 true).1
    · exact BandPrototileTranslation _ _ _ (hS 2 false).1
    · exact BandPrototileTranslation _ _ _ (hS 2 false).1
  have ncells (j : Fin 3) (b : Bool) :
      (N j b).cells = (P5110T1ParentModel P.q₁ P.q₂ j b).cells := by
    fin_cases j <;> cases b
    all_goals simp? [N, P5110T1ParentModel, TileTranslation, h0, h1, h2,
      Finset.image_image, ← P.sum_q]
    all_goals
      apply Finset.image_congr
      intro z hz
      have hsum := P.sum_q
      apply Zsqrtd.ext
      all_goals simp? [GaussianTranslation]
      all_goals omega
  have square_nonempty (n : Nat) (hn : 0 < n) (u : GaussianInt) :
      (TileTranslation (FordTile n) u).cells.Nonempty := by
    have hbase : (0 : GaussianInt) ∈ (FordTile n).cells :=
      (P4210T1FordCellRectangles n 0).1.mpr (by simp; omega)
    exact ⟨GaussianTranslation u 0, Finset.mem_image.mpr ⟨0, hbase, rfl⟩⟩
  have nanchor (j : Fin 3) (b : Bool) (hempty : (N j b).cells = ∅) :
      (N j b).anchor = (P5110T1ParentModel P.q₁ P.q₂ j b).anchor := by
    have hmempty := (ncells j b).symm.trans hempty
    fin_cases j <;> cases b
    · exact ((square_nonempty P.q₁ hr _).ne_empty hmempty).elim
    · exact ((square_nonempty P.q₁ hr _).ne_empty hmempty).elim
    · exact ((square_nonempty P.q₂ P.q₂_pos _).ne_empty hmempty).elim
    · exact ((square_nonempty P.q₂ P.q₂_pos _).ne_empty hmempty).elim
    · simp? [N, P5110T1ParentModel, TileTranslation, ha2, GaussianTranslation]
      ext <;> simp
    · simp [N, P5110T1ParentModel, TileTranslation, ha2, GaussianTranslation]
  have ncent : TileCentroid (N i plus) =
      TileCentroid (P5110T1ParentModel P.q₁ P.q₂ i plus) :=
    (ProtoTileObservableExtensionality _ _ (ncells i plus) (nanchor i plus)).2.2.2.2
  obtain ⟨_, h10, h20, h30, _⟩ := (FordCoordinateConfiguration P).2 hq
  have flips := (VectorRecursionLaws _ proper.1).2.2.2.2 proper
  have f0 : BandVectors.1 ((FordRecursiveQuadruple P) 0) ((FordRecursiveQuadruple P) 1) =
      ⟨-(P.q₁ : Int), (P.q : Int)⟩ := by
    calc
      _ = (⟨0, 1⟩ : GaussianInt) *
          BandVectors.1 ((FordRecursiveQuadruple P) 1) ((FordRecursiveQuadruple P) 0) :=
        (flips 0).1
      _ = _ := by rw [h10]; ext <;> simp
  have f1 : BandVectors.1 ((FordRecursiveQuadruple P) 0) ((FordRecursiveQuadruple P) 2) =
      ⟨-(P.q₂ : Int), -(P.q : Int)⟩ := by
    calc
      _ = (⟨0, 1⟩ : GaussianInt) *
          BandVectors.1 ((FordRecursiveQuadruple P) 2) ((FordRecursiveQuadruple P) 0) :=
        (flips 1).1
      _ = _ := by rw [h20]; ext <;> simp
  have f2 : BandVectors.1 ((FordRecursiveQuadruple P) 0) ((FordRecursiveQuadruple P) 3) =
      ⟨(P.q : Int), 0⟩ := by
    calc
      _ = (⟨0, 1⟩ : GaussianInt) *
          BandVectors.1 ((FordRecursiveQuadruple P) 3) ((FordRecursiveQuadruple P) 0) :=
        (flips 2).1
      _ = _ := by rw [h30]; ext <;> simp
  have ct (n : Nat) (u : GaussianInt) :
      TileCentroid (TileTranslation (FordTile n) u) =
        ((TileCentroid (FordTile n)).1 + (u.re : Int),
          (TileCentroid (FordTile n)).2 + (u.im : Int)) :=
    (TileTranslationFormulas _ _).2.2.2.2.1
  have ce (a : GaussianInt) : TileCentroid (⟨∅, a⟩ : ProtoTile) = GaussianRealPoint a := by
    simp [TileCentroid, GaussianRealPoint]
  have croot := P4210T1FordSquareCentroid P.q P.q_pos
  have c1 := P4210T1FordSquareCentroid P.q₁ hr
  have c2 := P4210T1FordSquareCentroid P.q₂ P.q₂_pos
  have model_cent :
      TileCentroid (P5110T1ParentModel P.q₁ P.q₂ i plus) -
          TileCentroid (FordTile P.q) =
        (1 / 2 : Real) •
          (GaussianRealPoint (BandVectors.1 ((FordRecursiveQuadruple P) i.succ)
              ((FordRecursiveQuadruple P) 0)) +
            (if plus then GaussianRealPoint (BandVectors.1 ((FordRecursiveQuadruple P) 0)
                ((FordRecursiveQuadruple P) i.succ))
            else -GaussianRealPoint (BandVectors.1 ((FordRecursiveQuadruple P) 0)
                ((FordRecursiveQuadruple P) i.succ)))) := by
    fin_cases i <;> cases plus
    all_goals
      simp? [P5110T1ParentModel, ct, ce, croot, c1, c2,
        f0, f1, f2, h10, h20, h30, GaussianRealPoint]
      have hsum : (P.q : Real) = (P.q₁ : Real) + (P.q₂ : Real) := by
        exact_mod_cast P.sum_q
      first | (constructor <;> linarith) | linarith
  have hUN : TileCentroid U = TileCentroid (N i plus) := by
    rw [ncent]
    exact sub_left_injective (hcent.trans model_cent.symm)
  have obs := BandPrototileCentroidUnique _ U (N i plus) hU (hN i plus) hUN
  exact ⟨obs.1.trans (ncells i plus), fun he =>
    (obs.2 he).trans (nanchor i plus (obs.1.symm.trans he))⟩

end ApollonianSuperharmonic

end
