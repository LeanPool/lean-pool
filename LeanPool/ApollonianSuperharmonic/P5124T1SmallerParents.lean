/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.NormNum

public import LeanPool.ApollonianSuperharmonic.P5124T1ParentModel
public import LeanPool.ApollonianSuperharmonic.P5124T1TranslatedDiamonds
public import LeanPool.ApollonianSuperharmonic.P5157T1DiamondStaircaseIntersections
public import LeanPool.ApollonianSuperharmonic.P5157T1DiamondSingletonIntersections

-- [TABLET NODE: P5124T1SmallerParents]

/-!
# P5124T1SmallerParents

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5124T1SmallerParents (k : Nat) (hk : 1 < k) :
    let D := DiamondTile k
    TouchingTriple D (TileTranslation D ⟨0, -(2 * (k : Int))⟩)
      (P5124T1ParentModel k 2 true) ∧
    TouchingTriple D (P5124T1ParentModel k 1 true)
      (P5124T1ParentModel k 2 false) ∧
    TouchingTriple D (P5124T1ParentModel k 2 true)
      (P5124T1ParentModel k 0 false) := by
-- BODY
  let D := DiamondTile k
  let L := TileTranslation D ⟨0, -(2 * (k : Int))⟩
  let Eplus := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
  let Eminus := TileTranslation (DiamondTile (k - 1)) ⟨-(k : Int), 1 - (k : Int)⟩
  let a : GaussianInt := ⟨-(k : Int) - 1, (k : Int) - 1⟩
  let b : GaussianInt := ⟨(k : Int), (k : Int) - 1⟩
  let A : ProtoTile := ⟨{a}, a⟩
  let B : ProtoTile := ⟨{b}, b⟩
  let N := 2 * (k - 1)
  change TouchingTriple D L Eplus ∧ TouchingTriple D A Eminus ∧
    TouchingTriple D Eplus B
  obtain ⟨⟨dp, vp, ep⟩, ⟨dq, vq, eq⟩, ⟨dr, vr, er⟩⟩ :=
    P5157T1DiamondStaircaseIntersections k hk
  obtain ⟨⟨da, va, ea⟩, ⟨dma, vma, ema⟩, ⟨db, vb, eb⟩, ⟨dpb, vpb, epb⟩⟩ :=
    P5157T1DiamondSingletonIntersections k hk
  have diamondNonempty (n : Nat) (hn : 0 < n) : (DiamondTile n).cells.Nonempty := by
    refine ⟨0, (P4194T1DiamondCellRows n 0).1.mpr ?_⟩
    norm_num
    omega
  have dne := diamondNonempty k (by omega)
  have ene := diamondNonempty (k - 1) (by omega)
  have lne : L.cells.Nonempty := by
    simpa only [L, TileTranslation, Finset.image_nonempty] using dne
  have epne : Eplus.cells.Nonempty := by
    simpa only [Eplus, TileTranslation, Finset.image_nonempty] using ene
  have emne : Eminus.cells.Nonempty := by
    simpa only [Eminus, TileTranslation, Finset.image_nonempty] using ene
  have ane : A.cells.Nonempty := Finset.singleton_nonempty a
  have bne : B.cells.Nonempty := Finset.singleton_nonempty b
  have hp := (P5157T1AlternatingStaircase 1 false 1 (Or.inl rfl) N (by dsimp [N]; omega)).2
  have hq := (P5157T1AlternatingStaircase 1 false (-1) (Or.inr rfl) N (by dsimp [N]; omega)).2
  have hr := (P5157T1AlternatingStaircase ⟨-(k : Int), (k : Int) - 1⟩
    true (-1) (Or.inr rfl) N (by dsimp [N]; omega)).2
  have horizontalPath (z : GaussianInt) :
      SimpleGridPath {z, z + 1} {{z, z + 1}} := by
    have H := (P5157T1AlternatingStaircase z true 1 (Or.inl rfl) 1 (by decide)).2
    simp only [Nat.le_one_iff_eq_zero_or_eq_one, P5157T1StaircasePoint, Int.reduceNeg,
        ↓reduceIte, Int.natCast_ediv, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, one_mul,
        or_and_right, exists_or, ↓existsAndEq, CharP.cast_eq_zero, zero_add, Int.reduceDiv,
        EuclideanDomain.zero_div, show (⟨0, 0⟩ : GaussianInt) = 0 from rfl, add_zero,
        true_and, Int.reduceAdd, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        EuclideanDomain.div_self, show (⟨1, 0⟩ : GaussianInt) = 1 from rfl, Order.lt_one_iff,
        exists_eq_left, Set.ofPred_eq_eq_singleton] at H
    convert H using 1; ext v; simp
  have verticalPath (z : GaussianInt) :
      SimpleGridPath {z, z + ⟨0, 1⟩} {{z, z + ⟨0, 1⟩}} := by
    have H := (P5157T1AlternatingStaircase z false 1 (Or.inl rfl) 1 (by decide)).2
    simp only [Nat.le_one_iff_eq_zero_or_eq_one, P5157T1StaircasePoint, Int.reduceNeg,
        Bool.false_eq_true, ↓reduceIte, Int.natCast_ediv, Nat.cast_ofNat, Nat.cast_add,
        Nat.cast_one, one_mul, or_and_right, exists_or, ↓existsAndEq, CharP.cast_eq_zero,
        EuclideanDomain.zero_div, zero_add, Int.reduceDiv,
        show (⟨0, 0⟩ : GaussianInt) = 0 from rfl, add_zero, true_and, Int.reduceAdd, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, EuclideanDomain.div_self, Order.lt_one_iff,
        exists_eq_left, Set.ofPred_eq_eq_singleton] at H
    convert H using 1; ext v; simp
  have tp : TileTouching D Eplus := Or.inl ⟨dne, epne, dp, by rw [vp, ep]; exact hp⟩
  have tq : TileTouching L Eplus := Or.inl ⟨lne, epne, dq, by rw [vq, eq]; exact hq⟩
  have tr : TileTouching D Eminus := Or.inl ⟨dne, emne, dr, by rw [vr, er]; exact hr⟩
  have ta : TileTouching D A := Or.inl ⟨dne, ane, da, by rw [va, ea]; exact verticalPath (a + 1)⟩
  have tma : TileTouching Eminus A := by
    refine Or.inl ⟨emne, ane, dma, ?_⟩
    rw [vma, ema]
    exact horizontalPath a
  have tb : TileTouching D B := Or.inl ⟨dne, bne, db, by rw [vb, eb]; exact verticalPath b⟩
  have tpb : TileTouching Eplus B := by
    refine Or.inl ⟨epne, bne, dpb, ?_⟩
    rw [vpb, epb]
    exact horizontalPath b
  have swapTouch (T U : ProtoTile) (h : TileTouching T U) : TileTouching U T := by
    rcases h with ⟨hT, hU, hd, hpath⟩ | h | h
    · exact Or.inl ⟨hU, hT, hd.symm, by simpa only [Set.inter_comm] using hpath⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  obtain ⟨_, _, t2⟩ := P5124T1TranslatedDiamonds k (by omega)
  refine ⟨⟨t2.1, tq, swapTouch _ _ tp, ?_⟩,
    ⟨ta, swapTouch _ _ tma, swapTouch _ _ tr, ?_⟩,
    ⟨tp, tpb, swapTouch _ _ tb, ?_⟩⟩
  · have hp0 : (1 : GaussianInt) ∈ BoundaryFootprintVertices D ∩ BoundaryFootprintVertices Eplus
      := by
      rw [vp]
      exact ⟨0, by omega, by simp [P5157T1StaircasePoint, Zsqrtd.ext_iff]⟩
    have hq0 : (1 : GaussianInt) ∈ BoundaryFootprintVertices L ∩ BoundaryFootprintVertices Eplus
        := by
      rw [vq]
      exact ⟨0, by omega, by simp [P5157T1StaircasePoint, Zsqrtd.ext_iff]⟩
    refine ⟨1, ⟨hp0.1, hq0.1, hp0.2⟩, ?_⟩
    intro x hx
    have hxp : x ∈ BoundaryFootprintVertices D ∩ BoundaryFootprintVertices Eplus := ⟨hx.1, hx.2.2⟩
    have hxq : x ∈ BoundaryFootprintVertices L ∩ BoundaryFootprintVertices Eplus := hx.2
    rw [vp] at hxp
    rw [vq] at hxq
    obtain ⟨i, _, hi⟩ := hxp
    obtain ⟨j, _, hj⟩ := hxq
    have hir := congrArg Zsqrtd.re hi
    have hii := congrArg Zsqrtd.im hi
    have hji := congrArg Zsqrtd.im hj
    simp [P5157T1StaircasePoint] at hir hii hji
    apply Zsqrtd.ext <;> simp <;> omega
  · have hav : a + 1 ∈ BoundaryFootprintVertices D ∩ BoundaryFootprintVertices A := by
      rw [va]; simp [a, Zsqrtd.ext_iff]
    have ham : a + 1 ∈ BoundaryFootprintVertices Eminus ∩ BoundaryFootprintVertices A := by
      rw [vma]; simp [a]
    refine ⟨a + 1, ⟨hav.1, hav.2, ham.1⟩, ?_⟩
    intro x hx
    have hva : x ∈ BoundaryFootprintVertices D ∩ BoundaryFootprintVertices A := ⟨hx.1, hx.2.1⟩
    have hvm : x ∈ BoundaryFootprintVertices Eminus ∩ BoundaryFootprintVertices A := ⟨hx.2.2,
        hx.2.1⟩
    rw [va] at hva
    rw [vma] at hvm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hva hvm
    rcases hva with h | h
    · exact h
    · rcases hvm with h' | h' <;> simp [Zsqrtd.ext_iff] at h h' ⊢ <;> omega
  · have hbv : b ∈ BoundaryFootprintVertices D ∩ BoundaryFootprintVertices B := by
      rw [vb]; simp [b, Zsqrtd.ext_iff]
    have hbp : b ∈ BoundaryFootprintVertices Eplus ∩ BoundaryFootprintVertices B := by
      rw [vpb]; simp [b]
    refine ⟨b, ⟨hbv.1, hbp.1, hbv.2⟩, ?_⟩
    intro x hx
    have hvb : x ∈ BoundaryFootprintVertices D ∩ BoundaryFootprintVertices B := ⟨hx.1, hx.2.2⟩
    have hvp : x ∈ BoundaryFootprintVertices Eplus ∩ BoundaryFootprintVertices B := hx.2
    rw [vb] at hvb
    rw [vpb] at hvp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hvb hvp
    rcases hvb with h | h
    · exact h
    · rcases hvp with h' | h' <;> simp [Zsqrtd.ext_iff] at h h' ⊢ <;> omega

end ApollonianSuperharmonic

end
