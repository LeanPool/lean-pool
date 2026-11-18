/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P2999T1CompleteSquareTransport
public import LeanPool.ApollonianSuperharmonic.PartialOdometerSlope

-- [TABLET NODE: P2999T1OrthogonalSlopeTransport]

/-!
# P2999T1OrthogonalSlopeTransport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P2999T1OrthogonalSlopeTransport (h : PartialOdometer) :
    PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction .negate h) =
      (PartialOdometerSlope h).map (fun p => (-p.2, p.1)) ∧
    PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction .conjugate h) =
      (PartialOdometerSlope h).map (fun p => (-p.1, p.2)) := by
-- BODY
  classical
  let H (h : PartialOdometer) (x : GaussianInt) : ℝ :=
    (h.value (x + 1) - h.value x + h.value (x + 1 + ⟨0, 1⟩) -
      h.value (x + ⟨0, 1⟩) : ℤ)
  let V (h : PartialOdometer) (x : GaussianInt) : ℝ :=
    (h.value (x + ⟨0, 1⟩) - h.value x + h.value (x + 1 + ⟨0, 1⟩) -
      h.value (x + 1) : ℤ)
  have average (h' : PartialOdometer) (f : GaussianInt → GaussianInt) (b : Bool)
      (sq : PartialOdometerSquares h' = (PartialOdometerSquares h).image f)
      (inj : Function.Injective f)
      (grad : ∀ x ∈ PartialOdometerSquares h,
        H h' (f x) = -(if b then V h x else H h x) ∧
        V h' (f x) = (if b then H h x else V h x)) :
      PartialOdometerSlope h' = (PartialOdometerSlope h).map
        (fun p => if b then (-p.2, p.1) else (-p.1, p.2)) := by
    change (if (PartialOdometerSquares h').Nonempty then
      some ((∑ x ∈ PartialOdometerSquares h', H h' x) /
        (2 * ((PartialOdometerSquares h').card : ℝ)),
        (∑ x ∈ PartialOdometerSquares h', V h' x) /
        (2 * ((PartialOdometerSquares h').card : ℝ))) else none) = _
    rw [sq]
    by_cases hs : (PartialOdometerSquares h).Nonempty
    · have hs' := hs.image f
      simp only [hs', ↓reduceIte, PartialOdometerSlope, hs, Option.map_some]
      rw [Finset.card_image_of_injective _ inj,
        Finset.sum_image inj.injOn, Finset.sum_image inj.injOn]
      have hh : (∑ x ∈ PartialOdometerSquares h, H h' (f x)) =
          ∑ x ∈ PartialOdometerSquares h, -(if b then V h x else H h x) :=
        Finset.sum_congr rfl (fun x hx => (grad x hx).1)
      have hv : (∑ x ∈ PartialOdometerSquares h, V h' (f x)) =
          ∑ x ∈ PartialOdometerSquares h, (if b then H h x else V h x) :=
        Finset.sum_congr rfl (fun x hx => (grad x hx).2)
      rw [hh, hv]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte,
        Finset.sum_neg_distrib, neg_div, H, V]
    · simp [hs, PartialOdometerSlope]
  have valN (x : GaussianInt) :
      (BandPackingSymmetryPartialOdometerAction .negate h).value x =
        h.value (-GaussianQuarterTurn x) := by
    change (if x ∈ h.domain.image GaussianQuarterTurn then _ else 0) = _
    split
    · rfl
    · rename_i hx
      symm
      apply h.value_outside
      intro hm
      apply hx
      refine Finset.mem_image.mpr ⟨-GaussianQuarterTurn x, hm, ?_⟩
      ext <;> simp [GaussianQuarterTurn]
  have valK (x : GaussianInt) :
      (BandPackingSymmetryPartialOdometerAction .conjugate h).value x =
        h.value (-GaussianReflection x) := by
    change (if x ∈ h.domain.image (fun y => -GaussianReflection y) then _ else 0) = _
    split
    · rfl
    · rename_i hx
      symm
      apply h.value_outside
      intro hm
      apply hx
      refine Finset.mem_image.mpr ⟨-GaussianReflection x, hm, ?_⟩
      ext <;> simp [GaussianReflection]
  constructor
  · apply average _ (fun x => GaussianQuarterTurn x - 1) true
    · exact P2999T1CompleteSquareTransport .negate h ⟨PartialOdometerSquares h, 0⟩ rfl
    · intro x y he
      have he' := congrArg (fun z => -GaussianQuarterTurn (z + 1)) he
      ext
      · simpa [GaussianQuarterTurn] using congrArg (fun z : GaussianInt => z.re) he'
      · simpa [GaussianQuarterTurn] using congrArg (fun z : GaussianInt => z.im) he'
    · intro x hx
      have corners :
          -GaussianQuarterTurn (GaussianQuarterTurn x - 1) = x + ⟨0, 1⟩ ∧
          -GaussianQuarterTurn (GaussianQuarterTurn x - 1 + 1) = x ∧
          -GaussianQuarterTurn (GaussianQuarterTurn x - 1 + ⟨0, 1⟩) = x + 1 + ⟨0, 1⟩ ∧
          -GaussianQuarterTurn (GaussianQuarterTurn x - 1 + 1 + ⟨0, 1⟩) = x + 1 := by
        refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;> simp [GaussianQuarterTurn, add_comm]
      simp only [H, V, valN, corners.1, corners.2.1, corners.2.2.1,
        corners.2.2.2, ↓reduceIte]
      constructor <;> push_cast <;> ring
  · apply average _ (fun x => -GaussianReflection x - 1) false
    · have sq := P2999T1CompleteSquareTransport .conjugate h
        ⟨PartialOdometerSquares h, 0⟩ rfl
      simp only [BandPackingSymmetryTileAction, TileQuarterTurn, TileReflection,
        Finset.image_image] at sq
      convert sq using 1
      congr 1
      funext x
      ext <;> simp [GaussianQuarterTurn, GaussianReflection]
    · intro x y he
      have he' := congrArg (fun z => -GaussianReflection z - 1) he
      ext
      · simpa [GaussianReflection] using congrArg (fun z : GaussianInt => z.re) he'
      · simpa [GaussianReflection] using congrArg (fun z : GaussianInt => z.im) he'
    · intro x hx
      have corners :
          -GaussianReflection (-GaussianReflection x - 1) = x + 1 ∧
          -GaussianReflection (-GaussianReflection x - 1 + 1) = x ∧
          -GaussianReflection (-GaussianReflection x - 1 + ⟨0, 1⟩) = x + 1 + ⟨0, 1⟩ ∧
          -GaussianReflection (-GaussianReflection x - 1 + 1 + ⟨0, 1⟩) = x + ⟨0, 1⟩ := by
        refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;> simp [GaussianReflection, add_comm]
      simp only [H, V, valK, corners.1, corners.2.1, corners.2.2.1,
        corners.2.2.2, Bool.false_eq_true, ↓reduceIte]
      constructor <;> push_cast <;> ring

end ApollonianSuperharmonic

end
