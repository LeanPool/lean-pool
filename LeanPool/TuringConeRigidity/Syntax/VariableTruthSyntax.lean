/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/VariableTruthSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.UniformInternalSatisfaction
public import LeanPool.TuringConeRigidity.Syntax.DefinableSubsetCertificates

/-!
# Variable Truth Syntax
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions SetModelReals
universe u
variable {M : ZFSet.{u}}

theorem tupleLookup_variable (C : Context M) (G t i x : ℕ) :
    Definable M (fun e => TupleLookup (e G) (e t) (e i) (e x)) := by
  exact tupleLookup_definable_variable C G t i x

theorem tupleAdequate_variable (C : Context M) {Q B : ZFSet.{u}}
    (hQ : Q ∈ M) (hB : B ∈ M) (G c t : ℕ) :
    Definable M (fun e => TupleAdequate Q B (e G) (e c) (e t)) := by
  exact tupleAdequate_definable_variable C hQ hB G c t

theorem tuplePrefix_variable (C : Context M) (a G t x s : ℕ) :
    Definable M (fun e => TuplePrefix (e a) (e G) (e t) (e x) (e s)) := by
  exact tuplePrefix_definable_variable C a G t x s

theorem setTruthStep_variable (C : Context M) (a G T S c t : ℕ) :
    Definable M (fun e => SetTruthStep (e a) (e G) (e T) (e S) (e c) (e t)) := by
  exact setTruthStep_definable_variable C a G T S c t

theorem setTruthRecursion_variable (C : Context M) {Q B : ZFSet.{u}}
    (hQ : Q ∈ M) (hB : B ∈ M) (a G T f s : ℕ) :
    Definable M (fun e => SetTruthRecursion Q B (e G) (e a) (e T) (e f) (e s)) := by
  have hn := defAllMem ((((tupleAdequate_variable C hQ hB (G+3) 1 0).and
    (defOrderedPair C 2 1 0)).existsMem (T+2)).existsMem (f+1)) s
  have hr := defAllMem (defAllMem (defImp (tupleAdequate_variable C hQ hB (G+2) 1 0)
    (defIff (defPairMem C 1 0 (s+2))
      (setTruthStep_variable C (a+2) (G+2) (T+2) (s+2) 1 0))) (T+1)) f
  exact hn.and hr

theorem truthWitness_variable (C : Context M) {Q B : ZFSet.{u}}
    (hQ : Q ∈ M) (hB : B ∈ M) (a G T c s : ℕ) :
    Definable M (fun e => TruthWitness Q B (e G) (e a) (e T) (e c) (e s)) :=
  ((leastFamily_param C hQ (c+1) 0).and
    (setTruthRecursion_variable C hQ hB (a+1) (G+1) (T+1) 0 (s+1))).existsParam hQ

theorem satisfactionWitness_variable (C : Context M) {Q B : ZFSet.{u}}
    (hQ : Q ∈ M) (hB : B ∈ M) (a G H T z : ℕ) :
    Definable M (fun e => SatisfactionWitness Q B (e G) (e H) (e a) (e T) (e z)) :=
  ((((truthWitness_variable C hQ hB (a+3) (G+3) (T+3) 2 0).and
    ((defPairMem C 2 1 0).and (defOrderedPair C (z+3) 2 1))).existsMem (H+2)).existsMem
      (T+1)).existsParam C.omega_mem

theorem parameterAdequate_variable (C : Context M) {Q B : ZFSet.{u}}
    (hQ : Q ∈ M) (hB : B ∈ M) (G c t : ℕ) :
    Definable M (fun e => ParameterAdequate Q B (e G) (e c) (e t)) :=
  ((((defOrderedPair C (t+3) 2 1).and ((boundWitness_definable C hQ hB (c+3) 0).and
    (defAllMem (defOr (member_definable C 0 3) (equal_definable C 0 3)) 0))).existsParam
      C.omega_mem).existsMem (G+1)).existsParam C.omega_mem

theorem definesSubset_variable (C : Context M) (a G T Z c t S : ℕ) :
    Definable M (fun e => DefinesSubset (e a) (e G) (e T) (e Z) (e c) (e t) (e S)) :=
  (defSubset C S a).and (defAllMem (defIff (member_definable C 0 (S+1))
    (((tuplePrefix_variable C (a+2) (G+2) (t+2) 1 0).and
      (defPairMem C (c+2) 0 (Z+2))).existsMem (T+1))) a)

theorem definitionWitness_variable (C : Context M) {Q B : ZFSet.{u}}
    (hQ : Q ∈ M) (hB : B ∈ M) (a G T Z S : ℕ) :
    Definable M (fun e => DefinitionWitness Q B (e G) (e a) (e T) (e Z) (e S)) :=
  (((parameterAdequate_variable C hQ hB (G+2) 1 0).and
    (definesSubset_variable C (a+2) (G+2) (T+2) (Z+2) 1 0 (S+2))).existsMem (T+1)).existsParam
      C.omega_mem

end TuringRigidity.RelativeConstructible

end OAI
