/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/BoundedRecursive.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.UniformOracle

/-!
# Bounded Recursive
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedRecursive
open UniformOracle

def allBelow (f : ℕ → ℕ) (a : ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => if allBelow f a n = 1 ∧ f (Nat.pair a n) = 1 then 1 else 0

theorem allBelow_spec (f : ℕ → ℕ) (a n : ℕ) :
    allBelow f a n = 1 ↔ ∀ i < n, f (Nat.pair a i) = 1 := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
    simp only [allBelow, ite_eq_left_iff, Nat.zero_ne_one, imp_false, not_not, ih]
    exact ⟨fun ⟨h, hn⟩ i hi => (Nat.lt_succ_iff_lt_or_eq.mp hi).elim (h i) (fun he => he ▸ hn),
      fun h => ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩⟩

theorem allBelow_binary (f : ℕ → ℕ) (a n : ℕ) : allBelow f a n = 0 ∨ allBelow f a n = 1 := by
  cases n with
  | zero => exact Or.inr rfl
  | succ n => unfold allBelow; split <;> simp

theorem allBelow_recursive {O : Set (ℕ →. ℕ)} {f : ℕ → ℕ}
    (hf : Nat.RecursiveIn O (fun n => Part.some (f n))) :
    Nat.RecursiveIn O (fun z => Part.some (allBelow f (Nat.unpair z).1 (Nat.unpair z).2)) := by
  have harg := total_pair (O := O) (total_primrec (Primrec.fst.comp Primrec.unpair))
    (total_primrec (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  have hval := total_comp hf harg
  have hprev := total_primrec (O := O)
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  have htest := total_primrec (O := O)
    (Primrec.ite ((Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 1)).and
      (Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 1)))
      (Primrec.const 1) (Primrec.const 0))
  have hstep := total_comp htest (total_pair hprev hval)
  have hrec := Nat.RecursiveIn.prec (total_primrec (O := O) (Primrec.const 1)) hstep
  apply hrec.of_eq
  intro z
  generalize hz : Nat.unpair z = v
  obtain ⟨a, n⟩ := v
  simp only [Nat.unpair_pair, Part.bind_eq_bind]
  clear hz
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ih, Part.bind_some, allBelow]

end TuringRigidity.BoundedRecursive

end OAI
