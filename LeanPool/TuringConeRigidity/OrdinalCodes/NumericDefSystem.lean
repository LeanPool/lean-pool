/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/NumericDefSystem.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.NumericTruth
public import LeanPool.TuringConeRigidity.Syntax.VariableCertificateBounds

/-!
# Numeric Def System
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.NumericSyntax
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding RelativeConstructible
open BoundedDefinability SetModelFunctions SetModelReals
universe u
theorem boundWitness_allBounds (Q B c b : ℕ) :
    Numeric.{u} (fun e => BoundWitness (e Q) (e B) (e c) (e b)) :=
  (((leastFamily_definable (Q+2) (c+2) 1).and
    ((setSupportRecursion_definable 1 0).and (defPairMem (c+2) (b+2) 0))).existsMem
      (B+1)).existsMem Q

theorem tupleAdequate_allBounds (Q B G c t : ℕ) :
    Numeric.{u} (fun e => TupleAdequate (e Q) (e B) (e G) (e c) (e t)) :=
  ((((defOrderedPair (t+3) 2 1).and
    ((boundWitness_allBounds (Q+3) (B+3) (c+3) 0).and
      (defSubset 0 2))).existsNat).existsMem (G+1)).existsNat

theorem setTruthRecursion_allBounds (Q B a G T f s : ℕ) :
    Numeric.{u} (fun e => SetTruthRecursion (e Q) (e B) (e G) (e a) (e T) (e f) (e s)) := by
  have hn := defAllMem ((((tupleAdequate_allBounds (Q+3) (B+3) (G+3) 1 0).and
    (defOrderedPair 2 1 0)).existsMem (T+2)).existsMem (f+1)) s
  have hr := defAllMem (defAllMem (defImp
    (tupleAdequate_allBounds (Q+2) (B+2) (G+2) 1 0)
    (defIff (defPairMem 1 0 (s+2))
      (setTruthStep_variable (a+2) (G+2) (T+2) (s+2) 1 0))) (T+1)) f
  exact hn.and hr

theorem truthWitness_allBounds (Q B a G T c s : ℕ) :
    Numeric.{u} (fun e => TruthWitness (e Q) (e B) (e G) (e a) (e T) (e c) (e s)) :=
  ((leastFamily_definable (Q+1) (c+1) 0).and
    (setTruthRecursion_allBounds (Q+1) (B+1) (a+1) (G+1) (T+1) 0 (s+1))).existsMem Q

theorem satisfactionWitness_allBounds (Q B a G H T z : ℕ) :
    Numeric.{u} (fun e => SatisfactionWitness (e Q) (e B) (e G) (e H) (e a) (e T) (e z)) :=
  ((((truthWitness_allBounds (Q+3) (B+3) (a+3) (G+3) (T+3) 2 0).and
    ((defPairMem 2 1 0).and (defOrderedPair (z+3) 2 1))).existsMem (H+2)).existsMem
      (T+1)).existsNat

theorem parameterAdequate_allBounds (Q B G c t : ℕ) :
    Numeric.{u} (fun e => ParameterAdequate (e Q) (e B) (e G) (e c) (e t)) :=
  ((((defOrderedPair (t+3) 2 1).and
    ((boundWitness_allBounds (Q+3) (B+3) (c+3) 0).and
      (defAllMem (defOr (member_definable 0 3) (equal_definable 0 3)) 0))).existsNat).existsMem
        (G+1)).existsNat

theorem definitionWitness_allBounds (Q B a G T Z S : ℕ) :
    Numeric.{u} (fun e => DefinitionWitness (e Q) (e B) (e G) (e a) (e T) (e Z) (e S)) :=
  (((parameterAdequate_allBounds (Q+2) (B+2) (G+2) 1 0).and
    (definesSubset_variable (a+2) (G+2) (T+2) (Z+2) 1 0 (S+2))).existsMem (T+1)).existsNat

theorem satisfactionSystem_allBounds (Q B a G T H Z : ℕ) :
    Numeric.{u} (fun e => SatisfactionSystem (e Q) (e B) (e a) (e G) (e T) (e H) (e Z)) := by
  have ht := defAllNat (defAllMem (defImp (leastFamily_definable (Q+2) 1 0)
    ((setTruthRecursion_allBounds (Q+3) (B+3) (a+3) (G+3) (T+3) 1 0).existsMem (H+2))) (Q+1))
  have hn := defAllMem (satisfactionWitness_allBounds (Q+1) (B+1) (a+1) (G+1) (H+1) (T+1) 0) Z
  have hc := defAllNat (defAllMem (defAllMem
    (defImp (truthWitness_allBounds (Q+3) (B+3) (a+3) (G+3) (T+3) 2 0)
      (defImp (defPairMem 2 1 0) (defPairMem 2 1 (Z+3)))) (H+2)) (T+1))
  exact (tupleSystem_definable a G T).and (ht.and (hn.and hc))

theorem defSystem_allBounds (Q B a G T H Z D : ℕ) :
    Numeric.{u} (fun e => DefSystem (e Q) (e B) (e a) (e G) (e T) (e H) (e Z) (e D)) := by
  have hn := defAllMem (definitionWitness_allBounds (Q+1) (B+1) (a+1) (G+1) (T+1) (Z+1) 0) D
  have hc := defAllNat (defAllMem (defImp (parameterAdequate_allBounds (Q+2) (B+2) (G+2) 1 0)
    ((definesSubset_variable (a+3) (G+3) (T+3) (Z+3) 2 1 0).existsMem (D+2))) (T+1))
  exact (satisfactionSystem_allBounds Q B a G T H Z).and (hn.and hc)

end TuringRigidity.NumericSyntax

end OAI
