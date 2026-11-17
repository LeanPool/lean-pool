/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalPairCode.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import Mathlib.SetTheory.Ordinal.CantorNormalForm

/-!
# Ordinal Pair Code
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalCoding
universe u
open Ordinal

/-- Encode an ordered ordinal pair using leading and trailing omega powers and a branch
coefficient. -/
noncomputable def pairCode (x y : Ordinal.{u}) : Ordinal.{u} :=
  if y ≤ x then omega0 ^ (x+1) + omega0 ^ y
  else omega0 ^ (y+1) * 2 + omega0 ^ x

theorem cnf_monomial (x : Ordinal.{u}) :
    CNF omega0 (omega0 ^ x) = [(x,1)] := by
  simpa only [mul_one,add_zero,CNF.zero_right] using
    (CNF.opow_mul_add (b := omega0) (e := x) (x := 1) (y := 0)
      one_lt_omega0 one_ne_zero one_lt_omega0 (opow_pos x omega0_pos))

theorem pairCode_cnf_left (x y : Ordinal.{u}) (hy : y ≤ x) :
    CNF omega0 (pairCode x y) = [(x+1,1),(y,1)] := by
  rw [pairCode,ite_eq_left hy]
  have h := CNF.opow_mul_add (b := omega0) (e := x+1) (x := 1) (y := omega0 ^ y)
    one_lt_omega0 one_ne_zero one_lt_omega0
    ((opow_lt_opow_iff_right one_lt_omega0).mpr (hy.trans_lt (lt_add_one x)))
  simpa only [mul_one,cnf_monomial] using h

theorem pairCode_cnf_right (x y : Ordinal.{u}) (hy : ¬ y ≤ x) :
    CNF omega0 (pairCode x y) = [(y+1,2),(x,1)] := by
  rw [pairCode,ite_eq_right hy]
  have h := CNF.opow_mul_add (b := omega0) (e := y+1) (x := 2) (y := omega0 ^ x)
    one_lt_omega0 (by simp) (by exact_mod_cast natCast_lt_omega0 2)
    ((opow_lt_opow_iff_right one_lt_omega0).mpr
      ((lt_of_not_ge hy).trans (lt_add_one y)))
  simpa only [cnf_monomial] using h

/-- Decode an ordinal-pair code from the first two terms of its Cantor normal form. -/
noncomputable def unpairCode (a : Ordinal.{u}) : Ordinal.{u} × Ordinal.{u} :=
  let h := (CNF omega0 a).getD 0 (0,0)
  let t := (CNF omega0 a).getD 1 (0,0)
  if h.2 = 1 then (Ordinal.pred h.1,t.1) else (t.1,Ordinal.pred h.1)

theorem unpairCode_pairCode (x y : Ordinal.{u}) : unpairCode (pairCode x y) = (x,y) := by
  by_cases hy : y ≤ x
  · simp [unpairCode,pairCode_cnf_left x y hy,Ordinal.pred_add_one]
  · simp [unpairCode,pairCode_cnf_right x y hy,Ordinal.pred_add_one]

theorem pairCode_inj (x y x' y' : Ordinal.{u}) :
    pairCode x y = pairCode x' y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    have h' := congrArg unpairCode h
    simpa only [unpairCode_pairCode,Prod.mk.injEq] using h'
  · rintro ⟨rfl,rfl⟩; rfl

theorem max_lt_pairCode (x y : Ordinal.{u}) : max x y < pairCode x y := by
  by_cases hy : y ≤ x
  · rw [max_eq_left hy,pairCode,ite_eq_left hy]
    exact ((lt_add_one x).trans_le (right_le_opow (x+1) one_lt_omega0)).trans_le le_self_add
  · have hx : x ≤ y := (lt_of_not_ge hy).le
    rw [max_eq_right hx,pairCode,ite_eq_right hy]
    have hmul : omega0 ^ (y+1) ≤ omega0 ^ (y+1) * 2 :=
      Ordinal.le_mul_left _ (zero_lt_one.trans_le one_le_two)
    exact ((lt_add_one y).trans_le (right_le_opow (y+1) one_lt_omega0)).trans_le
      (hmul.trans le_self_add)

theorem left_lt_pairCode (x y : Ordinal.{u}) : x < pairCode x y :=
  (le_max_left x y).trans_lt (max_lt_pairCode x y)

theorem right_lt_pairCode (x y : Ordinal.{u}) : y < pairCode x y :=
  (le_max_right x y).trans_lt (max_lt_pairCode x y)

end TuringRigidity.OrdinalCoding

end OAI
