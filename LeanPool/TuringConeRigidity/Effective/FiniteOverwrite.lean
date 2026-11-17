/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/FiniteOverwrite.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.UniformOracleSimulation
public import LeanPool.TuringConeRigidity.Effective.FiniteShuffle

/-!
# Finite Overwrite
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.FiniteOverwrite
open UniformPrograms

def overwrite (s : List Bool) (A : Oracle) (n : ℕ) : Bool :=
  if n < s.length then s.getD n false else A n

theorem overwrite_below (s : List Bool) (A : Oracle) (n : ℕ) (hn : n < s.length) :
    overwrite s A n = s.getD n false := by simp [overwrite,hn]

theorem overwrite_above (s : List Bool) (A : Oracle) (n : ℕ) (hn : s.length ≤ n) :
    overwrite s A n = A n := by simp [overwrite,Nat.not_lt.mpr hn]

theorem overwrite_program (s : List Bool) :
    Runs oracleFunction (fun A => oracleFunction (overwrite s A)) := by
  have hp : Primrec (fun z : ℕ =>
      if (Nat.unpair z).1 < s.length then
        (if s.getD (Nat.unpair z).1 false then 1 else 0) else (Nat.unpair z).2) :=
    Primrec.ite (Primrec.nat_lt.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const s.length))
      (Primrec.ite (Primrec.eq.comp ((Primrec.list_getD false).comp (Primrec.const s)
        (Primrec.fst.comp Primrec.unpair)) (Primrec.const true)) (Primrec.const 1) (Primrec.const
          0))
      (Primrec.snd.comp Primrec.unpair)
  have hq : Runs oracleFunction (fun A n => Part.some (if A n then 1 else 0)) := query
  apply (total_comp (primrec hp) (total_pair (primrec Primrec.id) hq)).of_eq
  intro A n
  simp only [Nat.unpair_pair,oracleFunction,overwrite,id_eq]
  split <;> rfl

theorem overwrite_reduces (s : List Bool) (A : Oracle) : Reduces (overwrite s A) A := by
  obtain ⟨p,hp⟩ := overwrite_program s
  exact (OracleCode.turingReducible_iff_exists_code _ _).mpr ⟨p,hp A⟩

theorem restore_initial (s : List Bool) (A : Oracle) :
    overwrite (FiniteShuffle.initial A s.length) (overwrite s A) = A := by
  funext n
  by_cases hn : n < s.length
  · rw [overwrite_below _ _ _ (by simpa using hn),FiniteShuffle.prefix_getD _ _ _ hn]
  · simp [overwrite,hn]

theorem degree_overwrite (s : List Bool) (A : Oracle) : degree (overwrite s A) = degree A := by
  apply (degree_eq_iff _ _).mpr
  exact ⟨overwrite_reduces s A,by
    simpa only [restore_initial] using
      overwrite_reduces (FiniteShuffle.initial A s.length) (overwrite s A)⟩

theorem overwrite_join_program (s : List Bool) (R : Oracle) :
    Runs (fun A => oracleFunction (join A R))
      (fun A => oracleFunction (join (overwrite s A) R)) := by
  have hp : Primrec (fun z : ℕ =>
      if (Nat.unpair z).1.bodd = false ∧ (Nat.unpair z).1 / 2 < s.length then
        (if s.getD ((Nat.unpair z).1 / 2) false then 1 else 0) else (Nat.unpair z).2) :=
    Primrec.ite
      ((Primrec.eq.comp (Primrec.nat_bodd.comp (Primrec.fst.comp Primrec.unpair))
        (Primrec.const false)).and
        (Primrec.nat_lt.comp (Primrec.nat_div.comp (Primrec.fst.comp Primrec.unpair)
          (Primrec.const 2)) (Primrec.const s.length)))
      (Primrec.ite (Primrec.eq.comp ((Primrec.list_getD false).comp (Primrec.const s)
        (Primrec.nat_div.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 2))) (Primrec.const
          true))
        (Primrec.const 1) (Primrec.const 0))
      (Primrec.snd.comp Primrec.unpair)
  have hq : Runs (fun A => oracleFunction (join A R))
      (fun A n => Part.some (if join A R n then 1 else 0)) := query
  apply (total_comp (primrec hp) (total_pair (primrec Primrec.id) hq)).of_eq
  intro A n
  cases hb : n.bodd <;> by_cases hn : n / 2 < s.length <;>
    simp [oracleFunction,join,overwrite,hb,hn]

end TuringRigidity.FiniteOverwrite

end OAI
