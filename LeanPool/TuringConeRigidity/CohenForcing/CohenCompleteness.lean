/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenCompleteness.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.EffectiveCohen

/-!
# Cohen Completeness
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.EffectiveCohen
open Encodable UniformOracle ArithmeticHierarchy OracleJump

theorem sigma1_enumeration {Y : Oracle} {P : ℕ → Prop} (h : Sigma Y 1 P) :
    ∃ e, ∀ n, P n ↔ Halts Y e n := by
  classical
  obtain ⟨Q,hQ,he⟩ := h
  have hf := Nat.RecursiveIn.rfind (recursive_not hQ)
  obtain ⟨e,hd⟩ := partial_table hf
  refine ⟨e,fun n => (he n).trans ?_⟩
  rw [hd n]
  erw [Nat.rfind_dom]
  simp [Quant]

theorem OneGeneric.decides {Y G : Oracle} (hG : OneGeneric Y G)
    {P : ℕ → Prop} (hP : Sigma Y 1 P) : ∃ p : List Bool,
      (∀ n < p.length, G n = p.getD n false) ∧
        (P (encode p) ∨ ∀ q : List Bool, p <+: q → ¬ P (encode q)) := by
  obtain ⟨e,he⟩ := sigma1_enumeration hP
  obtain ⟨p,hp,hd⟩ := hG e
  refine ⟨p,hp,?_⟩
  simpa only [he] using hd

theorem relative_one_generic (Y : Oracle) : ∃ G : Oracle, Reduces G (jump Y) ∧
    ∀ P : ℕ → Prop, Sigma Y 1 P → ∃ p : List Bool,
      (∀ n < p.length, G n = p.getD n false) ∧
        (P (encode p) ∨ ∀ q : List Bool, p <+: q → ¬ P (encode q)) :=
  ⟨generic Y,generic_reduces Y,fun _ hP => (generic_oneGeneric Y).decides hP⟩

end TuringRigidity.EffectiveCohen

end OAI
