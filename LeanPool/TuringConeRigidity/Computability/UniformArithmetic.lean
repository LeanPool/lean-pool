/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/UniformArithmetic.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticAtoms

/-!
# Uniform Arithmetic
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.UniformArithmetic
open Encodable

abbrev Oracles := ℕ → Oracle
abbrev Predicate := Oracles → ℕ → Prop
abbrev left (v : ℕ) := (Nat.unpair v).1
abbrev right (v : ℕ) := (Nat.unpair v).2

theorem left_primrec : Primrec left := Primrec.fst.comp Primrec.unpair
theorem right_primrec : Primrec right := Primrec.snd.comp Primrec.unpair

inductive Arith : Predicate → Prop where
  | pure (P : ℕ → Prop) : PrimrecPred P → Arith (fun _ v => P v)
  | query (i : ℕ) : Arith (fun O v => O i v = true)
  | neg {P} : Arith P → Arith (fun O v => ¬ P O v)
  | and {P Q} : Arith P → Arith Q → Arith (fun O v => P O v ∧ Q O v)
  | ex {P} : Arith P → Arith (fun O v => ∃ n, P O (Nat.pair v n))
  | comp {P} (f : ℕ → ℕ) : Arith P → Primrec f → Arith (fun O v => P O (f v))

theorem Arith.congr {P Q} (h : Arith P) (he : ∀ O v, P O v ↔ Q O v) : Arith Q := by
  have : P = Q := funext (fun O => funext (fun v => propext (he O v)))
  exact this ▸ h

theorem Arith.or {P Q} (hP : Arith P) (hQ : Arith Q) :
    Arith (fun O v => P O v ∨ Q O v) :=
  (hP.neg.and hQ.neg).neg.congr (fun _ _ => by
    classical
    tauto)

theorem Arith.imp {P Q} (hP : Arith P) (hQ : Arith Q) :
    Arith (fun O v => P O v → Q O v) :=
  (hP.neg.or hQ).congr (fun _ _ => by tauto)

theorem Arith.iff {P Q} (hP : Arith P) (hQ : Arith Q) :
    Arith (fun O v => P O v ↔ Q O v) :=
  ((hP.imp hQ).and (hQ.imp hP)).congr (fun _ _ => iff_def.symm)

theorem Arith.all {P} (h : Arith P) :
    Arith (fun O v => ∀ n, P O (Nat.pair v n)) :=
  h.neg.ex.neg.congr (fun _ _ => by simp)

theorem equal {f g : ℕ → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Arith (fun _ v => f v = g v) := .pure _ (Primrec.eq.comp hf hg)

theorem less {f g : ℕ → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Arith (fun _ v => f v < g v) := .pure _ (Primrec.nat_lt.comp hf hg)

theorem Arith.substitute {P} (h : Arith P)
    (F : Oracles → ℕ → Oracles)
    (hF : ∀ i, Arith (fun O v => F O (left v) i (right v) = true)) :
    Arith (fun O v => P (F O (left v)) (right v)) := by
  induction h with
  | pure P hP => exact .pure _ (hP.comp right_primrec)
  | query i => exact hF i
  | neg h ih => exact ih.neg
  | and h k ih ik => exact ih.and ik
  | ex h ih =>
    have hh := (ih.comp (fun v => Nat.pair (left (left v)) (Nat.pair (right (left v)) (right v)))
      (Primrec₂.natPair.comp (left_primrec.comp left_primrec)
        (Primrec₂.natPair.comp (right_primrec.comp left_primrec) right_primrec))).ex
    exact hh.congr (fun _ _ => by simp only [left,right,Nat.unpair_pair])
  | comp f h hf ih =>
    exact (ih.comp (fun v => Nat.pair (left v) (f (right v)))
      (Primrec₂.natPair.comp left_primrec (hf.comp right_primrec))).congr
        (fun _ _ => by simp only [left,right,Nat.unpair_pair])

end TuringRigidity.UniformArithmetic

end OAI
