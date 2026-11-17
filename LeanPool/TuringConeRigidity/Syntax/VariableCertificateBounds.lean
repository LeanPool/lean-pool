/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/VariableCertificateBounds.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.DefSystemCertificate

/-!
# Variable Certificate Bounds
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions SetModelReals
universe u
variable {M : ZFSet.{u}}

theorem boundWitness_allBounds (C : Context M) (Q B c b : ℕ) :
    Definable M (fun e => BoundWitness (e Q) (e B) (e c) (e b)) :=
  (((leastFamily_definable C (Q+2) (c+2) 1).and
    ((setSupportRecursion_definable C 1 0).and (defPairMem C (c+2) (b+2) 0))).existsMem
      (B+1)).existsMem Q

theorem tupleAdequate_allBounds (C : Context M) (Q B G c t : ℕ) :
    Definable M (fun e => TupleAdequate (e Q) (e B) (e G) (e c) (e t)) :=
  ((((defOrderedPair C (t+3) 2 1).and
    ((boundWitness_allBounds C (Q+3) (B+3) (c+3) 0).and
      (defSubset C 0 2))).existsParam C.omega_mem).existsMem (G+1)).existsParam C.omega_mem

theorem setTruthRecursion_allBounds (C : Context M) (Q B a G T f s : ℕ) :
    Definable M (fun e => SetTruthRecursion (e Q) (e B) (e G) (e a) (e T) (e f) (e s)) := by
  have hn := defAllMem ((((tupleAdequate_allBounds C (Q+3) (B+3) (G+3) 1 0).and
    (defOrderedPair C 2 1 0)).existsMem (T+2)).existsMem (f+1)) s
  have hr := defAllMem (defAllMem (defImp
    (tupleAdequate_allBounds C (Q+2) (B+2) (G+2) 1 0)
    (defIff (defPairMem C 1 0 (s+2))
      (setTruthStep_variable C (a+2) (G+2) (T+2) (s+2) 1 0))) (T+1)) f
  exact hn.and hr

theorem truthWitness_allBounds (C : Context M) (Q B a G T c s : ℕ) :
    Definable M (fun e => TruthWitness (e Q) (e B) (e G) (e a) (e T) (e c) (e s)) :=
  ((leastFamily_definable C (Q+1) (c+1) 0).and
    (setTruthRecursion_allBounds C (Q+1) (B+1) (a+1) (G+1) (T+1) 0 (s+1))).existsMem Q

theorem satisfactionWitness_allBounds (C : Context M) (Q B a G H T z : ℕ) :
    Definable M (fun e => SatisfactionWitness (e Q) (e B) (e G) (e H) (e a) (e T) (e z)) :=
  ((((truthWitness_allBounds C (Q+3) (B+3) (a+3) (G+3) (T+3) 2 0).and
    ((defPairMem C 2 1 0).and (defOrderedPair C (z+3) 2 1))).existsMem (H+2)).existsMem
      (T+1)).existsParam C.omega_mem

theorem parameterAdequate_allBounds (C : Context M) (Q B G c t : ℕ) :
    Definable M (fun e => ParameterAdequate (e Q) (e B) (e G) (e c) (e t)) :=
  ((((defOrderedPair C (t+3) 2 1).and
    ((boundWitness_allBounds C (Q+3) (B+3) (c+3) 0).and
      (defAllMem (defOr (member_definable C 0 3) (equal_definable C 0 3)) 0))).existsParam
        C.omega_mem).existsMem (G+1)).existsParam C.omega_mem

theorem definitionWitness_allBounds (C : Context M) (Q B a G T Z S : ℕ) :
    Definable M (fun e => DefinitionWitness (e Q) (e B) (e G) (e a) (e T) (e Z) (e S)) :=
  (((parameterAdequate_allBounds C (Q+2) (B+2) (G+2) 1 0).and
    (definesSubset_variable C (a+2) (G+2) (T+2) (Z+2) 1 0 (S+2))).existsMem (T+1)).existsParam
      C.omega_mem

theorem satisfactionSystem_allBounds (C : Context M) (Q B a G T H Z : ℕ) :
    Definable M (fun e => SatisfactionSystem (e Q) (e B) (e a) (e G) (e T) (e H) (e Z)) := by
  have ht := defAllParam (defAllMem (defImp (leastFamily_definable C (Q+2) 1 0)
    ((setTruthRecursion_allBounds C (Q+3) (B+3) (a+3) (G+3) (T+3) 1 0).existsMem (H+2))) (Q+1))
      C.omega_mem
  have hn := defAllMem (satisfactionWitness_allBounds C (Q+1) (B+1) (a+1) (G+1) (H+1) (T+1) 0) Z
  have hc := defAllParam (defAllMem (defAllMem
    (defImp (truthWitness_allBounds C (Q+3) (B+3) (a+3) (G+3) (T+3) 2 0)
      (defImp (defPairMem C 2 1 0) (defPairMem C 2 1 (Z+3)))) (H+2)) (T+1)) C.omega_mem
  exact (tupleSystem_definable C a G T).and (ht.and (hn.and hc))

theorem defSystem_allBounds (C : Context M) (Q B a G T H Z D : ℕ) :
    Definable M (fun e => DefSystem (e Q) (e B) (e a) (e G) (e T) (e H) (e Z) (e D)) := by
  have hn := defAllMem (definitionWitness_allBounds C (Q+1) (B+1) (a+1) (G+1) (T+1) (Z+1) 0) D
  have hc := defAllParam (defAllMem (defImp (parameterAdequate_allBounds C (Q+2) (B+2) (G+2) 1 0)
    ((definesSubset_variable C (a+3) (G+3) (T+3) (Z+3) 2 1 0).existsMem (D+2))) (T+1)) C.omega_mem
  exact (satisfactionSystem_allBounds C Q B a G T H Z).and (hn.and hc)

end TuringRigidity.RelativeConstructible

end OAI
