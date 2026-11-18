/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/CutArithmetic.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.CutAddition
public import LeanPool.TuringConeRigidity.Computability.ScalarCoding
public import LeanPool.TuringConeRigidity.Representation.Assembly

/-!
# Cut Arithmetic
-/


@[expose] public section

namespace OAI

namespace TuringRigidity
open RationalCoding UniformOracle

theorem cut_smul_reduces (r : ℚ) (x : ℝ) : Reduces (cut ((r : ℝ)*x)) (cut x) := by
  by_cases hr : r=0
  · subst r
    simpa using rational_cut_reduces (0 : ℚ) (cut x)
  by_cases ht : Irrational ((r : ℝ)*x)
  swap
  · obtain ⟨q,hq⟩ := not_not.mp ht
    rw [←hq]
    exact rational_cut_reduces q _
  have hq : Nat.RecursiveIn {oracleFunction (cut x)} (oracleFunction (cut x)) :=
    .oracle _ (Set.mem_singleton _)
  have hread := Nat.RecursiveIn.comp hq (divideIndex_recursive (O := {oracleFunction (cut x)}) r hr)
  apply RecursiveIn.iff_nat.mpr
  by_cases hpos : 0<r
  · have hpos' : (0 : ℝ)<r := by exact_mod_cast hpos
    apply hread.of_eq
    intro n
    change (Part.some (divideIndex r n)).bind
      (fun input => Part.some (if cut x input then 1 else 0)) =
      oracleFunction (cut ((r : ℝ)*x)) n
    rw [Part.bind_some]
    have hiff : cut x (divideIndex r n)=true ↔ cut ((r : ℝ)*x) n=true := by
      rw [cut_eq_true,cut_eq_true,divideIndex_value,Rat.cast_div]
      simpa only [mul_comm] using (div_lt_iff₀ hpos' :
        (rationalEnumeration n : ℝ)/(r : ℝ)<x ↔ (rationalEnumeration n : ℝ)<x*(r : ℝ))
    have heq : cut x (divideIndex r n)=cut ((r : ℝ)*x) n := Bool.eq_iff_iff.mpr hiff
    simp only [oracleFunction,heq]
  · have hneg : r<0 := (lt_or_gt_of_ne hr).resolve_right hpos
    have hneg' : (r : ℝ)<0 := by exact_mod_cast hneg
    have hc : Primrec (fun b : ℕ => if b=0 then 1 else 0) :=
      Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 1) (Primrec.const 0)
    apply (Nat.RecursiveIn.comp (total_primrec hc) hread).of_eq
    intro n
    change ((Part.some (divideIndex r n)).bind
      (fun input => Part.some (if cut x input then 1 else 0))).bind
      (fun value => Part.some (if value = 0 then 1 else 0)) =
      oracleFunction (cut ((r : ℝ)*x)) n
    simp only [Part.bind_some]
    have hiff : cut x (divideIndex r n)=true ↔ (r : ℝ)*x<(rationalEnumeration n : ℝ) := by
      rw [cut_eq_true,divideIndex_value,Rat.cast_div]
      simpa only [mul_comm] using (div_lt_iff_of_neg hneg' :
        (rationalEnumeration n : ℝ)/(r : ℝ)<x ↔ x*(r : ℝ)<(rationalEnumeration n : ℝ))
    have hneq : (rationalEnumeration n : ℝ) ≠ (r : ℝ)*x :=
      fun h => ht ⟨rationalEnumeration n,h⟩
    by_cases hin : cut x (divideIndex r n)=true
    · have hout : cut ((r : ℝ)*x) n=false := Bool.eq_false_iff.mpr
        (fun h => (not_lt_of_gt (hiff.mp hin)) ((cut_eq_true _ _).mp h))
      simp [hin,hout,oracleFunction]
    · have hle : (rationalEnumeration n : ℝ) ≤ (r : ℝ)*x :=
        le_of_not_gt (fun h => hin (hiff.mpr h))
      have hout : cut ((r : ℝ)*x) n=true := (cut_eq_true _ _).mpr
        ((lt_or_eq_of_le hle).resolve_right hneq)
      have hin' := Bool.eq_false_iff.mpr hin
      simp [hin',hout,oracleFunction]

theorem cut_sub_reduces (x y : ℝ) : Reduces (cut (x-y)) (join (cut x) (cut y)) := by
  have hy : Reduces (cut (-y)) (cut y) := by simpa using cut_smul_reduces (-1 : ℚ) y
  have h := reduces_trans (cut_add_reduces x (-y)) (join_mono (reduces_refl (cut x)) hy)
  simpa only [sub_eq_add_neg] using h

theorem cut_translate_reduces (x : ℝ) (q : ℚ) : Reduces (cut (x+(q : ℝ))) (cut x) :=
  reduces_trans (cut_add_reduces x q)
    (join_reduces (reduces_refl (cut x)) (rational_cut_reduces q (cut x)))

theorem cut_arithmetic : CutArithmetic where
  add := cut_add_reduces
  sub := cut_sub_reduces
  smul := cut_smul_reduces
  translate := cut_translate_reduces

end TuringRigidity

end OAI
