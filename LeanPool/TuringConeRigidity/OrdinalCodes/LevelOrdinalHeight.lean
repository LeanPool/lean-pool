/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/LevelOrdinalHeight.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalCut

/-!
# Level Ordinal Height
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem ordinalHeight_level (R : ZFSet.{u}) (o : Ordinal.{u}) :
    ordinalHeight (level R o) = ordinalHeight (seed R) + o := by
  induction o using Ordinal.limitRecOn with
  | zero => simp only [level_zero,add_zero]
  | add_one o ih =>
    rw [level_succ,ordinalHeight_definablePower _ (level_transitive R o),ih,add_assoc]
  | limit o ho ih =>
    apply le_antisymm
    · by_contra h
      have hx := (ordinal_mem_iff_height _ (level_transitive R o) _).mpr (lt_of_not_ge h)
      obtain ⟨i,hi,hx⟩ := (mem_level_limit R _ o ho).mp hx
      have hx' := (ordinal_mem_iff_height _ (level_transitive R i) _).mp hx
      rw [ih i hi] at hx'
      exact (not_lt_of_ge (add_le_add (le_refl (ordinalHeight (seed R))) hi.le)) hx'
    · by_contra h
      obtain ⟨i,hi,hi'⟩ := Ordinal.lt_add_iff_of_isSuccLimit ho |>.mp (lt_of_not_ge h)
      rw [← ih i hi] at hi'
      have hx := (ordinal_mem_iff_height _ (level_transitive R i) _).mpr hi'
      have hx' := level_mono R hi.le hx
      exact (lt_irrefl _) ((ordinal_mem_iff_height _ (level_transitive R o) _).mp hx')

theorem ordinal_mem_level_iff (R : ZFSet.{u}) (o a : Ordinal.{u}) :
    a.toZFSet ∈ level R o ↔ a < ordinalHeight (seed R) + o := by
  rw [ordinal_mem_iff_height _ (level_transitive R o),ordinalHeight_level]

theorem largest_ordinal_level_succ (R : ZFSet.{u}) (o : Ordinal.{u}) :
    (ordinalHeight (seed R) + o).toZFSet ∈ level R (o+1) ∧
      ∀ a : Ordinal.{u}, a.toZFSet ∈ level R (o+1) ↔ a ≤ ordinalHeight (seed R) + o := by
  have h (a : Ordinal.{u}) : a.toZFSet ∈ level R (o+1) ↔ a ≤ ordinalHeight (seed R) + o := by
    rw [ordinal_mem_level_iff,← add_assoc]
    exact Order.lt_add_one_iff
  exact ⟨(h _).mpr le_rfl,h⟩

theorem largest_ordinal_at_difference (R : ZFSet.{u}) (a : Ordinal.{u})
    (ha : ordinalHeight (seed R) ≤ a) :
    a.toZFSet ∈ level R (a - ordinalHeight (seed R) + 1) ∧
      ∀ b : Ordinal.{u}, b.toZFSet ∈ level R (a - ordinalHeight (seed R) + 1) ↔ b ≤ a := by
  simpa only [Ordinal.add_sub_cancel_of_le ha] using
    largest_ordinal_level_succ R (a - ordinalHeight (seed R))

end TuringRigidity.RelativeConstructible

end OAI
