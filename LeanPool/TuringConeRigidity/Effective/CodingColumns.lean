/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/CodingColumns.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.CodingForcing
public import LeanPool.TuringConeRigidity.Computability.OracleEnumeration
public import LeanPool.TuringConeRigidity.Computability.Joins

/-!
# Coding Columns
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CodingColumns
open PrefixComputability OracleEnumeration

def column (A : Oracle) (k cutoff : ℕ) (m : ℕ) : Bool :=
  if cutoff ≤ m ∧ (Nat.unpair m).1 = k then A (Nat.unpair m).2 else false

@[simp] theorem column_pair (A : Oracle) (k cutoff a : ℕ) :
    column A k cutoff (Nat.pair k a) = (if cutoff ≤ Nat.pair k a then A a else false) := by
  simp [column]

theorem column_infinite (A : Oracle) (hA : {a | A a = true}.Infinite) (k cutoff : ℕ) :
    {m | column A k cutoff m = true}.Infinite := by
  have hi : (Nat.pair k '' {a | A a = true}).Infinite :=
    hA.image (fun a _ b _ h => (Nat.pair_eq_pair.mp h).2)
  apply (hi.sdiff (Set.finite_le_nat cutoff)).mono
  rintro m ⟨⟨a, ha, rfl⟩, hm⟩
  have hc : cutoff ≤ Nat.pair k a := Nat.le_of_lt (Nat.lt_of_not_ge hm)
  change A a = true at ha
  simp [hc, ha]

private def columnStep (k cutoff : ℕ) (p : ℕ) : ℕ :=
  if cutoff ≤ (Nat.unpair p).1 ∧ (Nat.unpair (Nat.unpair p).1).1 = k
  then (Nat.unpair p).2 else 0

private theorem columnStep_primrec (k cutoff : ℕ) : Primrec (columnStep k cutoff) :=
  Primrec.ite ((Primrec.nat_le.comp (Primrec.const cutoff) (Primrec.fst.comp Primrec.unpair)).and
    (Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
      (Primrec.const k))) (Primrec.snd.comp Primrec.unpair) (Primrec.const 0)

theorem column_reduces (A : Oracle) (k cutoff : ℕ) : Reduces (column A k cutoff) A := by
  apply RecursiveIn.iff_nat.mpr
  have hq : Nat.RecursiveIn {oracleFunction A} (oracleFunction A) :=
    .oracle _ (Set.mem_singleton _)
  have hm := total_primrec (O := {oracleFunction A}) Primrec.id
  have ha := total_primrec (O := {oracleFunction A}) (Primrec.snd.comp Primrec.unpair)
  have hh := total_comp (total_primrec (columnStep_primrec k cutoff))
    (total_pair hm (total_comp hq ha))
  apply hh.of_eq
  intro m
  by_cases hc : cutoff ≤ m ∧ (Nat.unpair m).1 = k <;>
    simp [columnStep, column, oracleFunction, hc]

noncomputable def location (A : Oracle) (hA : {a | A a = true}.Infinite)
    (k cutoff : ℕ) : ℕ → ℕ := enumerate (column A k cutoff) (column_infinite A hA k cutoff)

theorem location_mem (A : Oracle) (hA : {a | A a = true}.Infinite) (k cutoff n : ℕ) :
    column A k cutoff (location A hA k cutoff n) = true := enumerate_mem _ _ _

theorem le_location (A : Oracle) (hA : {a | A a = true}.Infinite) (k cutoff n : ℕ) :
    n ≤ location A hA k cutoff n := le_enumerate _ _ _

theorem location_recursive (A : Oracle) (hA : {a | A a = true}.Infinite) (k cutoff : ℕ) :
    Nat.RecursiveIn {oracleFunction A} (fun n => Part.some (location A hA k cutoff n)) := by
  apply (enumerate_recursive (column A k cutoff) (column_infinite A hA k cutoff)).subst
  intro f hf
  have he : f = oracleFunction (column A k cutoff) := Set.mem_singleton_iff.mp hf
  subst f
  exact RecursiveIn.iff_nat.mp (column_reduces A k cutoff)

noncomputable def readColumn (A : Oracle) (hA : {a | A a = true}.Infinite)
    (k cutoff : ℕ) (G : Oracle) : Oracle := fun n => G (location A hA k cutoff n)

theorem readColumn_reduces (A : Oracle) (hA : {a | A a = true}.Infinite)
    (k cutoff : ℕ) (G : Oracle) : Reduces (readColumn A hA k cutoff G) (join G A) := by
  apply RecursiveIn.iff_nat.mpr
  have hloc := (location_recursive A hA k cutoff).subst (O' := {oracleFunction (join G A)})
    (fun f hf => by
      have he : f = oracleFunction A := Set.mem_singleton_iff.mp hf
      subst f
      exact RecursiveIn.iff_nat.mp (reduces_join_right G A))
  have hG := RecursiveIn.iff_nat.mp (reduces_join_left G A)
  exact total_comp hG hloc

end TuringRigidity.CodingColumns

end OAI
