/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.P5124T1ParentPlacement
public import LeanPool.ApollonianSuperharmonic.P5124T1UnitParents
public import LeanPool.ApollonianSuperharmonic.P5124T1SmallerParents
public import LeanPool.ApollonianSuperharmonic.P5124T1EmptyParents
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality

-- [TABLET NODE: DiamondBaseTouching]

/-!
# DiamondBaseTouching

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem DiamondBaseTouching (K : DiamondParameter) :
    let q := DiamondRecursiveQuadruple K
    let T := DiamondTile K.1
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
  classical
  dsimp only
  let q := DiamondRecursiveQuadruple K
  let D := DiamondTile K.1
  have touching_ext (A A' B B' : ProtoTile)
      (hA : A.cells = A'.cells ∧ (A.cells = ∅ → A.anchor = A'.anchor))
      (hB : B.cells = B'.cells ∧ (B.cells = ∅ → B.anchor = B'.anchor)) :
      TileTouching A B ↔ TileTouching A' B' := by
    have oA := ProtoTileObservableExtensionality A A' hA.1 hA.2
    have oB := ProtoTileObservableExtensionality B B' hB.1 hB.2
    have hvA := oA.2.1
    have heA := oA.2.2.1
    have hvB := oB.2.1
    have heB := oB.2.2.1
    by_cases ha : A.cells = ∅ <;> by_cases hb : B.cells = ∅ <;>
      simp_all [TileTouching, Finset.nonempty_iff_ne_empty]
  have triple_ext (A B B' C C' : ProtoTile)
      (hB : B.cells = B'.cells ∧ (B.cells = ∅ → B.anchor = B'.anchor))
      (hC : C.cells = C'.cells ∧ (C.cells = ∅ → C.anchor = C'.anchor)) :
      TouchingTriple A B C ↔ TouchingTriple A B' C' := by
    have hA : A.cells = A.cells ∧ (A.cells = ∅ → A.anchor = A.anchor) :=
      ⟨rfl, fun _ => rfl⟩
    have oB := ProtoTileObservableExtensionality B B' hB.1 hB.2
    have oC := ProtoTileObservableExtensionality C C' hC.1 hC.2
    simp only [TouchingTriple, touching_ext A A B B' hA hB,
      touching_ext B B' C C' hB hC, touching_ext C C' A A hC hA,
      oB.2.1, oC.2.1]
  obtain ⟨_, hq, hv0, hv1, hv2, _⟩ := DiamondCoordinateConfiguration K
  obtain ⟨t0, t1, t2⟩ := P5124T1TranslatedDiamonds K.1 K.2
  obtain ⟨u0, u1, u2⟩ := P5124T1UnitParents K.1 K.2
  have more :
      TouchingTriple D (TileTranslation D ⟨0, -(2 * (K.1 : Int))⟩)
        (P5124T1ParentModel K.1 2 true) ∧
      TouchingTriple D (P5124T1ParentModel K.1 1 true)
        (P5124T1ParentModel K.1 2 false) ∧
      TouchingTriple D (P5124T1ParentModel K.1 2 true)
        (P5124T1ParentModel K.1 0 false) := by
    by_cases hk : 1 < K.1
    · exact P5124T1SmallerParents K.1 hk
    · have hk1 : K.1 = 1 := by have := K.2; omega
      simpa [D, hk1] using P5124T1EmptyParents
  have t4 (i : Fin 3) :
      TouchingTriple D (TileTranslation D (BandVectors.1 (q i.succ) (q 0)))
        (P5124T1ParentModel K.1 i true) := by
    fin_cases i
    · simpa [q, hv0] using u0
    · simpa [q, hv1] using u1
    · simpa [q, hv2] using more.1
  have t5 (i : Fin 3) :
      TouchingTriple D (P5124T1ParentModel K.1 i true)
        (P5124T1ParentModel K.1 (i + 1) false) := by
    fin_cases i
    · exact u2
    · exact more.2.1
    · exact more.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hn0 : -(⟨(K.1 : Int) + 1, (K.1 : Int)⟩ : GaussianInt) =
        ⟨-(K.1 : Int) - 1, -(K.1 : Int)⟩ := by
      ext <;> simp; ring
    have hn1 : -(⟨-(K.1 : Int) - 1, (K.1 : Int)⟩ : GaussianInt) =
        ⟨(K.1 : Int) + 1, -(K.1 : Int)⟩ := by
      ext <;> simp; ring
    have hn2 : -(⟨0, -(2 * (K.1 : Int))⟩ : GaussianInt) =
        ⟨0, 2 * (K.1 : Int)⟩ := by
      ext <;> simp
    fin_cases i
    · simpa [hv0, hv1, hn1] using t0
    · simpa [hv1, hv2, hn2] using t1
    · simpa [hv2, hv0, hn0] using t2
  · intro i U hU hc
    obtain ⟨hp, hpc⟩ := P5124T1ParentPlacement K i true
    have hcent : TileCentroid U = TileCentroid (P5124T1ParentModel K.1 i true) := by
      exact sub_left_inj.mp (hc.trans hpc.symm)
    have hobs := BandPrototileCentroidUnique _ _ _ hU hp hcent
    exact (triple_ext D _ _ U _ ⟨rfl, fun _ => rfl⟩ hobs).mpr (t4 i)
  · intro i U V hU hV hcU hcV
    obtain ⟨hp, hpc⟩ := P5124T1ParentPlacement K i true
    obtain ⟨hr, hrc⟩ := P5124T1ParentPlacement K (i + 1) false
    have hcentU : TileCentroid U = TileCentroid (P5124T1ParentModel K.1 i true) := by
      exact sub_left_inj.mp (hcU.trans hpc.symm)
    have hcentV : TileCentroid V =
        TileCentroid (P5124T1ParentModel K.1 (i + 1) false) := by
      apply sub_left_inj.mp
      exact hcV.trans (by simpa only [Bool.false_eq_true, ite_false, sub_eq_add_neg]
        using hrc.symm)
    have hoU := BandPrototileCentroidUnique _ _ _ hU hp hcentU
    have hoV := BandPrototileCentroidUnique _ _ _ hV hr hcentV
    exact (triple_ext D U _ V _ hoU hoV).mpr (t5 i)

end ApollonianSuperharmonic

end
