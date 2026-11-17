/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FordTile
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetric
public meta import Lean.Meta.Tactic.NormCast

-- [TABLET NODE: FordBaseT2]

/-!
# FordBaseT2

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem FordBaseT2 (q : Nat) (hq : 0 < q) :
    QuarterTurnSymmetric (FordTile q) := by
-- BODY
  let domain : Finset GaussianInt :=
    (Finset.range q).product (Finset.range q) |>.image
      (fun a => (⟨(a.1 : Int), (a.2 : Int)⟩ : GaussianInt))
  have domain_nonempty : domain.Nonempty := by
    refine ⟨(⟨(0 : Int), (0 : Int)⟩ : GaussianInt), ?_⟩
    have hz : (⟨(0 : Int), (0 : Int)⟩ : GaussianInt) ∈ domain := by
      apply Finset.mem_image.mpr
      exact ⟨(0, 0), by simpa using hq, rfl⟩
    exact hz
  have domain_injective : Set.InjOn
      (fun a : ℕ × ℕ => (⟨(a.1 : Int), (a.2 : Int)⟩ : GaussianInt))
      ↑((Finset.range q).product (Finset.range q)) := by
    intro a ha b hb hab
    apply Prod.ext
    · have coordinate := congrArg Zsqrtd.re hab
      change (a.1 : Int) = (b.1 : Int) at coordinate
      exact_mod_cast coordinate
    · have coordinate := congrArg Zsqrtd.im hab
      change (a.2 : Int) = (b.2 : Int) at coordinate
      exact_mod_cast coordinate
  have domain_card : domain.card = q * q := by
    calc
      domain.card = ((Finset.range q).product (Finset.range q)).card := by
        dsimp [domain]
        exact (Finset.card_image_iff.mpr domain_injective)
      _ = q * q := by simp
  have domain_re_sum : domain.sum (fun z : GaussianInt => z.re) =
      (q : Int) * ((q - 1 : Nat) : Int) / 2 * (q : Int) := by
    have range_sum : (Finset.range q).sum (fun x => (x : Int)) =
        (q : Int) * ((q - 1 : Nat) : Int) / 2 := by
      rw [← Nat.cast_sum]
      simp [Finset.sum_range_id]
    simp only [Int.reduceNeg, Finset.product_eq_sprod, Finset.coe_product, Finset.coe_range,
        Zsqrtd.mk.injEq, Nat.cast_inj, Prod.forall, Prod.mk.injEq, implies_true,
        Set.injOn_of_eq_iff_eq, Finset.sum_image, Finset.sum_product, Finset.sum_const,
        Finset.card_range, Int.nsmul_eq_mul, domain]
    conv_lhs => rw [← Finset.mul_sum (Finset.range q) (fun x => (x : Int)) (q : Int)]
    rw [range_sum]
    ring
  have domain_im_sum : domain.sum (fun z : GaussianInt => z.im) =
      (q : Int) * ((q - 1 : Nat) : Int) / 2 * (q : Int) := by
    have range_sum : (Finset.range q).sum (fun x => (x : Int)) =
        (q : Int) * ((q - 1 : Nat) : Int) / 2 := by
      rw [← Nat.cast_sum]
      simp [Finset.sum_range_id]
    simp only [Int.reduceNeg, Finset.product_eq_sprod, Finset.coe_product, Finset.coe_range,
        Zsqrtd.mk.injEq, Nat.cast_inj, Prod.forall, Prod.mk.injEq, implies_true,
        Set.injOn_of_eq_iff_eq, Finset.sum_image, Finset.sum_product, Finset.sum_const,
        Finset.card_range, Int.nsmul_eq_mul, domain]
    rw [range_sum]
    ring
  have centroid_formula : TileCentroid (FordTile q) =
      ((q : Real) / 2, (q : Real) / 2) := by
    change (if domain.Nonempty then
      ((↑(domain.sum (fun z : GaussianInt => z.re) : Int) /
          ↑domain.card + (1 / 2 : Real)),
       (↑(domain.sum (fun z : GaussianInt => z.im) : Int) /
          ↑domain.card + (1 / 2 : Real))) else _) = _
    rw [ite_eq_left domain_nonempty]
    rw [domain_card, domain_re_sum, domain_im_sum]
    norm_num
    field_simp
    have arithmetic := Finset.sum_range_id_mul_two q
    have range_sum : (Finset.range q).sum (fun x => (x : Int)) =
        (q : Int) * ((q - 1 : Nat) : Int) / 2 := by
      rw [← Nat.cast_sum]
      simp [Finset.sum_range_id]
    have arithmetic_cast :
        ((Finset.range q).sum (fun x => (x : Int))) * 2 =
          (q : Int) * ((q - 1 : Nat) : Int) := by
      rw [← Nat.cast_sum]
      exact_mod_cast arithmetic
    rw [range_sum] at arithmetic_cast
    have qcast : ((q - 1 : Nat) : Int) = (q : Int) - 1 := by omega
    rw [qcast] at arithmetic_cast
    have nat_identity : q * (q - 1) / 2 * 2 + q = q * q := by
      rw [← Finset.sum_range_id q]
      rw [Finset.sum_range_id_mul_two]
      rw [Nat.mul_sub_left_distrib]
      simp only [Nat.mul_one]
      have product_bound : q ≤ q * q := by nlinarith
      rw [Nat.sub_add_cancel product_bound]
    norm_num [Int.subNatNat, pow_two]
    exact_mod_cast nat_identity
  unfold QuarterTurnSymmetric
  rw [centroid_formula]
  intro p
  change p ∈ ⋃ x ∈ domain, ClosedSquareRealization x ↔
    ((q : Real) / 2 - (p.2 - (q : Real) / 2),
      (q : Real) / 2 + (p.1 - (q : Real) / 2)) ∈
        ⋃ x ∈ domain, ClosedSquareRealization x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨x, hx, hp⟩
    change x ∈ Finset.image _ ((Finset.range q).product (Finset.range q)) at hx
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_product.mp ha with ⟨ha, hb⟩
    simp only [ClosedSquareRealization, Set.mem_Icc] at hp ⊢
    change ((a.1 : Real) ≤ p.1 ∧ (a.2 : Real) ≤ p.2) ∧
      (p.1 ≤ (a.1 : Real) + 1 ∧ p.2 ≤ (a.2 : Real) + 1) at hp
    rcases hp with ⟨⟨hp1, hp2⟩, ⟨hp3, hp4⟩⟩
    let newbase : GaussianInt :=
      (⟨((q - 1 - a.2 : Nat) : Int), (a.1 : Int)⟩ : GaussianInt)
    refine ⟨newbase, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨(q - 1 - a.2, a.1), ?_, rfl⟩
      have first_bound : q - 1 - a.2 < q :=
        Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt hq Nat.zero_lt_one)
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr first_bound,
        Finset.mem_range.mpr (Finset.mem_range.mp ha)⟩
    · change ((q : Real) / 2 - (p.2 - (q : Real) / 2),
        (q : Real) / 2 + (p.1 - (q : Real) / 2)) ∈
        ClosedSquareRealization newbase
      simp only [ClosedSquareRealization, Set.mem_Icc]
      dsimp [newbase]
      change ((((q - 1 - a.2 : Nat) : Int) : Real) ≤
          (q : Real) / 2 - (p.2 - (q : Real) / 2) ∧
        (a.1 : Real) ≤ (q : Real) / 2 + (p.1 - (q : Real) / 2)) ∧
        ((q : Real) / 2 - (p.2 - (q : Real) / 2) ≤
          (((q - 1 - a.2 : Nat) : Int) : Real) + 1 ∧
        (q : Real) / 2 + (p.1 - (q : Real) / 2) ≤ (a.1 : Real) + 1)
      have base_relation : q - 1 - a.2 = q - (a.2 + 1) := by omega
      rw [base_relation]
      norm_num [Nat.cast_sub (show a.2 + 1 ≤ q from Nat.succ_le_of_lt (Finset.mem_range.mp hb))]
          at *
      have first_bound : (a.1 : Real) < q := by exact_mod_cast ha.1
      have second_bound : (a.2 : Real) < q := by exact_mod_cast hb
      constructor
      · constructor <;> linarith
      · constructor <;> linarith
  · rintro ⟨x, hx, hp⟩
    change x ∈ Finset.image _ ((Finset.range q).product (Finset.range q)) at hx
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_product.mp ha with ⟨ha, hb⟩
    simp only [ClosedSquareRealization, Set.mem_Icc] at hp ⊢
    change ((a.1 : Real) ≤ (q : Real) / 2 - (p.2 - (q : Real) / 2) ∧
        (a.2 : Real) ≤ (q : Real) / 2 + (p.1 - (q : Real) / 2)) ∧
      ((q : Real) / 2 - (p.2 - (q : Real) / 2) ≤ (a.1 : Real) + 1 ∧
        (q : Real) / 2 + (p.1 - (q : Real) / 2) ≤ (a.2 : Real) + 1) at hp
    rcases hp with ⟨⟨hp1, hp2⟩, ⟨hp3, hp4⟩⟩
    let newbase : GaussianInt :=
      (⟨(a.2 : Int), ((q - 1 - a.1 : Nat) : Int)⟩ : GaussianInt)
    refine ⟨newbase, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨(a.2, q - 1 - a.1), ?_, rfl⟩
      have second_bound : q - 1 - a.1 < q :=
        Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt hq Nat.zero_lt_one)
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Finset.mem_range.mp hb),
        Finset.mem_range.mpr second_bound⟩
    · change p ∈ ClosedSquareRealization newbase
      simp only [ClosedSquareRealization, Set.mem_Icc]
      dsimp [newbase]
      change ((((a.2 : Int) : Real) ≤ p.1 ∧
        (((q - 1 - a.1 : Nat) : Int) : Real) ≤ p.2)) ∧
        (p.1 ≤ ((a.2 : Int) : Real) + 1 ∧
        p.2 ≤ (((q - 1 - a.1 : Nat) : Int) : Real) + 1)
      have base_relation : q - 1 - a.1 = q - (a.1 + 1) := by omega
      rw [base_relation]
      norm_num [Nat.cast_sub (show a.1 + 1 ≤ q from Nat.succ_le_of_lt (Finset.mem_range.mp ha))]
          at *
      have first_bound : (a.1 : Real) < q := by exact_mod_cast ha.1
      have second_bound : (a.2 : Real) < q := by exact_mod_cast hb
      constructor
      · constructor <;> linarith
      · constructor <;> linarith

end ApollonianSuperharmonic

end
