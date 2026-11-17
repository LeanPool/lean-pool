/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/EffectiveWitness.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.JumpProperties

/-!
# Effective Witness
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.EffectiveWitness
open UniformOracle ArithmeticHierarchy OracleJump

noncomputable def least (P : ℕ → Prop) (ht : ∀ x, ∃ a, P (Nat.pair x a)) (x : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (ht x)

theorem least_spec (P : ℕ → Prop) (ht : ∀ x, ∃ a, P (Nat.pair x a)) (x : ℕ) :
    P (Nat.pair x (least P ht x)) := by
  classical
  exact Nat.find_spec (ht x)

theorem least_recursive {Y : Oracle} {P : ℕ → Prop} (hP : RecursivePred Y P)
    (ht : ∀ x, ∃ a, P (Nat.pair x a)) :
    Nat.RecursiveIn {oracleFunction Y} (fun x => Part.some (least P ht x)) := by
  classical
  have hr := Nat.RecursiveIn.rfind (recursive_not hP)
  apply hr.of_eq_tot
  intro x
  apply Nat.mem_rfind.mpr
  constructor
  · simp [least_spec P ht x]
  · intro a ha
    have hn := Nat.find_min (ht x) (show a < Nat.find (ht x) from ha)
    simp [hn]

def Accept (P : ℕ → Prop) (v : ℕ) : Prop :=
  ((Nat.unpair v).2 = 0 ∧ ¬ ∃ a, P (Nat.pair (Nat.unpair v).1 a)) ∨
    (0 < (Nat.unpair v).2 ∧ P (Nat.pair (Nat.unpair v).1 ((Nat.unpair v).2 - 1)))

theorem accept_total (P : ℕ → Prop) : ∀ x, ∃ a, Accept P (Nat.pair x a) := by
  intro x
  by_cases h : ∃ a, P (Nat.pair x a)
  · obtain ⟨a,ha⟩ := h
    exact ⟨a+1, Or.inr ⟨by simp, by simpa using ha⟩⟩
  · exact ⟨0, Or.inl ⟨by simp, by simpa using h⟩⟩

theorem accept_recursive {Y : Oracle} {P : ℕ → Prop} (hP : RecursivePred Y P) :
    RecursivePred (jump Y) (Accept P) := by
  classical
  let f := Primrec.fst.comp Primrec.unpair
  let s := Primrec.snd.comp Primrec.unpair
  have hz : RecursivePred (jump Y) (fun v => (Nat.unpair v).2 = 0) :=
    (total_primrec (Primrec.ite (Primrec.eq.comp s (Primrec.const 0)) (Primrec.const 1)
      (Primrec.const 0))).of_eq
      (fun v => by by_cases h : (Nat.unpair v).2 = 0 <;> simp [h])
  have hp : RecursivePred (jump Y) (fun v => 0 < (Nat.unpair v).2) :=
    (total_primrec (Primrec.ite (Primrec.nat_lt.comp (Primrec.const 0) s) (Primrec.const 1)
      (Primrec.const 0))).of_eq
      (fun v => by by_cases h : 0 < (Nat.unpair v).2 <;> simp [h])
  have hn := recursive_comp (recursive_not (exists_recursive_jump hP)) f
  have hy := recursive_comp (recursive_lift hP)
    (Primrec₂.natPair.comp f (Primrec.nat_sub.comp s (Primrec.const 1)))
  exact Form.or (n := 0) (s := true) (recursive_and hz hn) (recursive_and hp hy)

noncomputable def witness (P : ℕ → Prop) (x : ℕ) : ℕ :=
  least (Accept P) (accept_total P) x

theorem witness_recursive {Y : Oracle} {P : ℕ → Prop} (hP : RecursivePred Y P) :
    Nat.RecursiveIn {oracleFunction (jump Y)} (fun x => Part.some (witness P x)) :=
  least_recursive (accept_recursive hP) (accept_total P)

theorem witness_spec (P : ℕ → Prop) (x : ℕ) :
    (witness P x = 0 ∧ ¬ ∃ a, P (Nat.pair x a)) ∨
      (0 < witness P x ∧ P (Nat.pair x (witness P x - 1))) := by
  simpa only [Accept, Nat.unpair_pair, witness] using least_spec (Accept P) (accept_total P) x

theorem sigma1_choice {Y : Oracle} {P : ℕ → Prop} (hP : Sigma Y 1 P) :
    ∃ f : ℕ → ℕ, Nat.RecursiveIn {oracleFunction (jump Y)} (fun x => Part.some (f x)) ∧
      ∀ x, (f x = 0 ∧ ¬ ∃ a, P (Nat.pair x a)) ∨
        (0 < f x ∧ P (Nat.pair x (f x - 1))) := by
  obtain ⟨Q,hQ,he⟩ := hP
  let Q' : ℕ → Prop := fun v => Q
    (Nat.pair (Nat.pair (Nat.unpair v).1 (Nat.unpair (Nat.unpair v).2).1)
      (Nat.unpair (Nat.unpair v).2).2)
  let fst := Primrec.fst.comp Primrec.unpair
  let snd := Primrec.snd.comp Primrec.unpair
  have hQ' : RecursivePred Y Q' := recursive_comp hQ
    (Primrec₂.natPair.comp (Primrec₂.natPair.comp fst (fst.comp snd)) (snd.comp snd))
  let f : ℕ → ℕ := fun x => if witness Q' x = 0 then 0 else (Nat.unpair (witness Q' x - 1)).1 + 1
  have hf : Primrec (fun v : ℕ => if v = 0 then 0 else (Nat.unpair (v-1)).1+1) :=
    Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 0)
      (Primrec.succ.comp (fst.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))))
  have hrec := total_comp (total_primrec (O := {oracleFunction (jump Y)}) hf) (witness_recursive
    hQ')
  refine ⟨f, hrec.of_eq (fun x => rfl), fun x => ?_⟩
  rcases witness_spec Q' x with ⟨hz,hn⟩ | ⟨hp,hy⟩
  · refine Or.inl ⟨by simp [f,hz], ?_⟩
    rintro ⟨a,ha⟩
    obtain ⟨b,hb⟩ := (he _).mp ha
    exact hn ⟨Nat.pair a b, by simpa [Q'] using hb⟩
  · have hn : witness Q' x ≠ 0 := by omega
    refine Or.inr ⟨by simp [f,hn], ?_⟩
    simp only [f, ite_eq_right hn, Nat.add_sub_cancel]
    exact (he _).mpr ⟨(Nat.unpair (witness Q' x - 1)).2, by simpa [Q'] using hy⟩

end TuringRigidity.EffectiveWitness

end OAI
