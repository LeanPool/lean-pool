/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4217T2SquareRestriction
public import LeanPool.ApollonianSuperharmonic.PartialOdometerSquares
public import LeanPool.ApollonianSuperharmonic.P4210T1FordCellRectangles

-- [TABLET NODE: P4217T2SquareGeometry]

/-!
# P4217T2SquareGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4217T2SquareGeometry (q : Nat) (g : IntegerLatticeFunction)
    (hq : 0 < q) :
    ((P4217T2SquareRestriction q g).domain : Set GaussianInt) = FordVertexDomain q ∧
    (∀ x, x ∈ (P4217T2SquareRestriction q g).domain →
      (P4217T2SquareRestriction q g).value x = g x) ∧
    PartialOdometerSquares (P4217T2SquareRestriction q g) = (FordTile q).cells ∧
    (PartialOdometerSquares (P4217T2SquareRestriction q g)).card = q * q ∧
    (PartialOdometerSquares (P4217T2SquareRestriction q g)).Nonempty := by
-- BODY
  classical
  have dom (x : GaussianInt) : x ∈ (P4217T2SquareRestriction q g).domain ↔
      x ∈ FordVertexDomain q := by
    constructor
    · intro hx
      obtain ⟨⟨r, t⟩, hrt, rfl⟩ := Finset.mem_image.mp hx
      have hr := Finset.mem_range.mp (Finset.mem_product.mp hrt).1
      have ht := Finset.mem_range.mp (Finset.mem_product.mp hrt).2
      change 0 ≤ (r : Int) ∧ (r : Int) ≤ q ∧ 0 ≤ (t : Int) ∧ (t : Int) ≤ q
      omega
    · rintro ⟨hr, hrq, hi, hiq⟩
      apply Finset.mem_image.mpr
      refine ⟨(x.re.toNat, x.im.toNat), ?_, ?_⟩
      · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
          Finset.mem_range.mpr (by omega)⟩
      · apply Zsqrtd.ext <;> simp [hr, hi]
  have squares : PartialOdometerSquares (P4217T2SquareRestriction q g) =
      (FordTile q).cells := by
    ext x
    simp only [PartialOdometerSquares, Finset.mem_filter, dom]
    rw [(P4210T1FordCellRectangles q x).1]
    simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_add,
      Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one]
    omega
  have card : (FordTile q).cells.card = q * q := by
    change (Finset.image _ ((Finset.range q).product (Finset.range q))).card = _
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b hab
      have hr := congrArg (fun z : GaussianInt => z.re) hab
      have hi := congrArg (fun z : GaussianInt => z.im) hab
      apply Prod.ext <;> dsimp at * <;> omega
  refine ⟨Set.ext dom, ?_, squares, by rw [squares, card], ?_⟩
  · intro x hx
    exact ite_eq_left ((dom x).mp hx)
  · rw [squares, ← Finset.card_pos, card]
    exact Nat.mul_pos hq hq

end ApollonianSuperharmonic

end
