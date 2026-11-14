/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FordTile
public import LeanPool.ApollonianSuperharmonic.TileCentroid
public meta import Lean.Meta.Tactic.NormCast

-- [TABLET NODE: P4210T1FordSquareCentroid]

/-!
# P4210T1FordSquareCentroid

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4210T1FordSquareCentroid (q : Nat) (hq : 0 < q) :
    TileCentroid (FordTile q) = ((q : Real) / 2, (q : Real) / 2) := by
-- BODY
  classical
  let domain : Finset GaussianInt := FordCellDomain q
  have domain_nonempty : domain.Nonempty := by
    refine ⟨(⟨(0 : Int), (0 : Int)⟩ : GaussianInt), ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨(0, 0), by simpa using hq, rfl⟩
  have domain_injective : Set.InjOn
      (fun a : Nat × Nat => (⟨(a.1 : Int), (a.2 : Int)⟩ : GaussianInt))
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
        dsimp [domain, FordCellDomain]
        exact Finset.card_image_iff.mpr domain_injective
      _ = q * q := by simp
  have range_sum : (Finset.range q).sum (fun x => (x : Int)) =
      (q : Int) * ((q - 1 : Nat) : Int) / 2 := by
    rw [← Nat.cast_sum]
    simp [Finset.sum_range_id]
  have domain_re_sum : domain.sum (fun z : GaussianInt => z.re) =
      (q : Int) * ((q - 1 : Nat) : Int) / 2 * (q : Int) := by
    simp only [FordCellDomain, Int.reduceNeg, Finset.product_eq_sprod, Finset.coe_product,
        Finset.coe_range, Zsqrtd.mk.injEq, Nat.cast_inj, Prod.forall, Prod.mk.injEq,
        implies_true, Set.injOn_of_eq_iff_eq, Finset.sum_image, Finset.sum_product,
        Finset.sum_const, Finset.card_range, Int.nsmul_eq_mul, domain]
    conv_lhs => rw [← Finset.mul_sum (Finset.range q) (fun x => (x : Int)) (q : Int)]
    rw [range_sum]
    ring
  have domain_im_sum : domain.sum (fun z : GaussianInt => z.im) =
      (q : Int) * ((q - 1 : Nat) : Int) / 2 * (q : Int) := by
    simp only [FordCellDomain, Int.reduceNeg, Finset.product_eq_sprod, Finset.coe_product,
        Finset.coe_range, Zsqrtd.mk.injEq, Nat.cast_inj, Prod.forall, Prod.mk.injEq,
        implies_true, Set.injOn_of_eq_iff_eq, Finset.sum_image, Finset.sum_product,
        Finset.sum_const, Finset.card_range, Int.nsmul_eq_mul, domain]
    rw [range_sum]
    ring
  change (if domain.Nonempty then
    ((↑(domain.sum (fun z : GaussianInt => z.re) : Int) /
        ↑domain.card + (1 / 2 : Real)),
     (↑(domain.sum (fun z : GaussianInt => z.im) : Int) /
        ↑domain.card + (1 / 2 : Real))) else _) = _
  rw [ite_eq_left domain_nonempty, domain_card, domain_re_sum, domain_im_sum]
  norm_num
  field_simp
  have nat_identity : q * (q - 1) / 2 * 2 + q = q * q := by
    rw [← Finset.sum_range_id q, Finset.sum_range_id_mul_two]
    rw [Nat.mul_sub_left_distrib]
    simp only [Nat.mul_one]
    have product_bound : q ≤ q * q := by nlinarith
    rw [Nat.sub_add_cancel product_bound]
  norm_num [Int.subNatNat, pow_two]
  exact_mod_cast nat_identity

end ApollonianSuperharmonic

end
