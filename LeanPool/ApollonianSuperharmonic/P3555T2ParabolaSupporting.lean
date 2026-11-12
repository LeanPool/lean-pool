/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

public import LeanPool.ApollonianSuperharmonic.P3381T1TriangleDeterminant
public meta import Lean.Meta.Tactic.NormCast

-- [TABLET NODE: P3555T2ParabolaSupporting]

/-!
# P3555T2ParabolaSupporting

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3555T2ParabolaSupporting {n : Nat}
    (q : Fin (n + 3) → Real × Real)
    (hq : ∀ i, q i = ((i.val : Real), (i.val : Real) ^ 2)) :
    Function.Injective q ∧
    (∀ f : Fin 3 → Fin (n + 3), Function.Injective f →
      P3381T1TriangleDeterminant (q ∘ f) ≠ 0) ∧
    (∀ i j : Fin (n + 3), j ≠ i → j ≠ i + 1 →
      0 < P3381T1TriangleDeterminant ![q i, q (i + 1), q j]) := by
-- BODY
  have cast_inj : Function.Injective (fun i : Fin (n + 3) => (i.val : Real)) := by
    intro i j hij
    change (i.val : Real) = (j.val : Real) at hij
    apply Fin.ext
    exact_mod_cast hij
  have formula (a b c : Fin (n + 3)) :
      P3381T1TriangleDeterminant ![q a, q b, q c] =
        ((b.val : Real) - a.val) * ((c.val : Real) - a.val) *
          ((c.val : Real) - b.val) := by
    simp [P3381T1TriangleDeterminant, hq]
    ring
  have injective : Function.Injective q := by
    intro i j hij
    apply cast_inj
    simpa only [hq, Prod.mk.injEq] using congrArg Prod.fst hij
  refine ⟨injective, ?_, ?_⟩
  · intro f hf
    have hf01 : f 1 ≠ f 0 := hf.ne (by decide)
    have hf02 : f 2 ≠ f 0 := hf.ne (by decide)
    have hf12 : f 2 ≠ f 1 := hf.ne (by decide)
    have hform : P3381T1TriangleDeterminant (q ∘ f) =
        ((f 1).val - (f 0).val : Real) *
          ((f 2).val - (f 0).val : Real) *
          ((f 2).val - (f 1).val : Real) := by
      simpa [P3381T1TriangleDeterminant, Function.comp_apply] using
          formula (f 0) (f 1) (f 2)
    rw [hform]
    exact mul_ne_zero
      (mul_ne_zero (sub_ne_zero.mpr (cast_inj.ne hf01))
        (sub_ne_zero.mpr (cast_inj.ne hf02)))
      (sub_ne_zero.mpr (cast_inj.ne hf12))
  · intro i j hji hjnext
    rw [formula]
    by_cases hi : i = Fin.last (n + 2)
    · have hiv : i.val = n + 2 := by simp [hi]
      have hnext : (i + 1).val = 0 := by simp [hi]
      have hjpos : 0 < j.val := by
        have hjne : j.val ≠ (i + 1).val := fun h => hjnext (Fin.ext h)
        omega
      have hjlt : j.val < i.val := by
        have hjne : j.val ≠ i.val := fun h => hji (Fin.ext h)
        have hjbound := j.isLt
        omega
      have hI : 0 < (i.val : Real) := by exact_mod_cast (show 0 < i.val by omega)
      have hJ : 0 < (j.val : Real) := by exact_mod_cast hjpos
      have hJI : (j.val : Real) < i.val := by exact_mod_cast hjlt
      simp only [hnext, Nat.cast_zero, zero_sub, sub_zero]
      exact mul_pos (mul_pos_of_neg_of_neg (neg_neg_of_pos hI) (sub_neg.mpr hJI)) hJ
    · have hnext : (i + 1).val = i.val + 1 := by simp [Fin.val_add_one, hi]
      have hjne : j.val ≠ i.val := fun h => hji (Fin.ext h)
      have hjnne : j.val ≠ i.val + 1 := by
        intro h
        apply hjnext
        apply Fin.ext
        exact h.trans hnext.symm
      have cases : j.val < i.val ∨ i.val + 1 < j.val := by omega
      simp only [hnext, Nat.cast_add, Nat.cast_one]
      have hfactor : (i.val : Real) + 1 - i.val = 1 := by ring
      rw [hfactor, one_mul]
      rcases cases with hj | hj
      · have hlt : (j.val : Real) < i.val := by exact_mod_cast hj
        exact mul_pos_of_neg_of_neg (sub_neg.mpr hlt) (by linarith)
      · have hlt : (i.val : Real) + 1 < j.val := by exact_mod_cast hj
        exact mul_pos (by linarith) (sub_pos.mpr hlt)

end ApollonianSuperharmonic

end
