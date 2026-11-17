/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/OracleEnumeration.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.PrefixComputability
public import Mathlib.Data.Set.Finite.Range
public import Lean.Elab.Tactic.Omega

/-!
# Oracle Enumeration
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OracleEnumeration
open PrefixComputability

theorem exists_ge {A : Oracle} (hA : {n | A n = true}.Infinite) (n : ℕ) :
    ∃ m, n ≤ m ∧ A m = true := by
  by_contra h
  apply hA
  apply (Set.finite_le_nat n).subset
  intro m hm
  exact Nat.le_of_lt (Nat.lt_of_not_ge (fun hnm => h ⟨m, hnm, hm⟩))

noncomputable def next (A : Oracle) (hA : {n | A n = true}.Infinite) (n : ℕ) : ℕ :=
  Nat.find (exists_ge hA n)

theorem next_spec (A : Oracle) (hA : {n | A n = true}.Infinite) (n : ℕ) :
    n ≤ next A hA n ∧ A (next A hA n) = true := Nat.find_spec (exists_ge hA n)

theorem next_min (A : Oracle) (hA : {n | A n = true}.Infinite) (n m : ℕ)
    (hm : n ≤ m) (hAm : A m = true) : next A hA n ≤ m :=
  Nat.find_min' (exists_ge hA n) ⟨hm, hAm⟩

private def searchFlag (p : ℕ) : ℕ :=
  if (Nat.unpair p).1 ≤ (Nat.unpair (Nat.unpair p).2).1 ∧
    (Nat.unpair (Nat.unpair p).2).2 = 1 then 0 else 1

private theorem searchFlag_primrec : Primrec searchFlag := by
  exact Primrec.ite ((Primrec.nat_le.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))).and
    (Primrec.eq.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
      (Primrec.const 1))) (Primrec.const 0) (Primrec.const 1)

theorem next_recursive (A : Oracle) (hA : {n | A n = true}.Infinite) :
    Nat.RecursiveIn {oracleFunction A} (fun n => Part.some (next A hA n)) := by
  have hq : Nat.RecursiveIn {oracleFunction A} (oracleFunction A) :=
    .oracle _ (Set.mem_singleton _)
  have hn := total_primrec (O := {oracleFunction A}) (Primrec.fst.comp Primrec.unpair)
  have hm := total_primrec (O := {oracleFunction A}) (Primrec.snd.comp Primrec.unpair)
  have hf := total_comp (total_primrec searchFlag_primrec)
    (total_pair hn (total_pair hm (total_comp hq hm)))
  apply (Nat.RecursiveIn.rfind hf).of_eq_tot
  intro n
  apply Nat.mem_rfind.mpr
  constructor
  · have hs := next_spec A hA n
    simp [searchFlag, hs.1, hs.2]
  · intro m hm'
    have hh : ¬(n ≤ m ∧ A m = true) := Nat.find_min (exists_ge hA n) hm'
    cases ha : A m <;> simp_all [searchFlag]

noncomputable def enumerate (A : Oracle) (hA : {n | A n = true}.Infinite) : ℕ → ℕ
  | 0 => next A hA 0
  | n+1 => next A hA (enumerate A hA n + 1)

theorem enumerate_mem (A : Oracle) (hA : {n | A n = true}.Infinite) (n : ℕ) :
    A (enumerate A hA n) = true := by
  cases n <;> exact (next_spec A hA _).2

theorem enumerate_strictMono (A : Oracle) (hA : {n | A n = true}.Infinite) :
    StrictMono (enumerate A hA) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (Nat.lt_succ_self _).trans_le (next_spec A hA _).1

theorem le_enumerate (A : Oracle) (hA : {n | A n = true}.Infinite) (n : ℕ) :
    n ≤ enumerate A hA n := (enumerate_strictMono A hA).id_le n

theorem enumerate_recursive (A : Oracle) (hA : {n | A n = true}.Infinite) :
    Nat.RecursiveIn {oracleFunction A} (fun n => Part.some (enumerate A hA n)) := by
  have hnext := next_recursive A hA
  have hbase := total_comp hnext (total_primrec (Primrec.const 0))
  have hstep := total_comp hnext (total_primrec
    (Primrec.succ.comp (Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.snd.comp Primrec.unpair)))))
  have hrec := Nat.RecursiveIn.prec hbase hstep
  have hr := Nat.RecursiveIn.comp hrec
    (total_pair (total_primrec (Primrec.const 0)) (total_primrec Primrec.id))
  apply hr.of_eq
  intro n
  change (Part.some (Nat.pair 0 n)).bind _ = _
  rw [Part.bind_some]
  simp only [Nat.unpair_pair]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ih]
    simp [enumerate]

end TuringRigidity.OracleEnumeration

end OAI
