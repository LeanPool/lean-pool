/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticGenericTruth.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticTruthRequirements

/-!
# Arithmetic Generic Truth
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ArithmeticGenericTruth
open Encodable UniformArithmetic ArithmeticPrefixForcing FiniteShuffle ShuffleRequirements
open EncodedForcing (word word_primrec)

theorem open_constant (p : Prop) (G : Oracle) : G ∈ OpenSet (fun _ => p) ↔ p := by
  exact ArithmeticPrefixForcing.openSet_constant_iff p G

theorem arithmetic_generic_truth {P : Predicate} (hP : Arith P) :
    ∃ Q : PrefixPredicate, ArithmeticPrefix Q ∧ (∀ O v, Upward (Q O v)) ∧
      ∀ O v G, Generic O G →
        (P (Function.update O 0 G) v ↔ G ∈ OpenSet (Q O v)) := by
  obtain ⟨Q, D, hQ, hD, hup, hden, ht⟩ :=
    ArithmeticTruthRequirements.arithmetic_truth_requirements hP
  refine ⟨Q, hQ, hup, ?_⟩
  intro O v G hG
  exact ht O v G
    (ArithmeticPrefixFamilies.genericFor_of_generic hD O v (hden O v) G hG)

end TuringRigidity.ArithmeticGenericTruth

end OAI
