/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticSourceTruth.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticSourceEquation
public import LeanPool.TuringConeRigidity.Computability.ArithmeticGenericDensity

/-!
# Arithmetic Source Truth
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ArithmeticSourceTruth
open UniformArithmetic ArithmeticPrefixForcing GenericIdentity GenericTruth ShuffleRequirements

theorem binary_column_arith {B : OracleFamily} (hB : ArithmeticOracle B) (b : Bool) :
    ArithmeticOracle (fun O v => PairGenericSelection.column b (B O v)) := by
  have he := Primrec.nat_mul.comp (Primrec.const 2) right_primrec
  cases b with
  | false => exact query_at hB left_primrec he
  | true => exact query_at hB left_primrec (Primrec.succ.comp he)

theorem triple_equation_arith (p : OracleCode) :
    Arith (fun O _ => SourceEquation p (O 1) (triple (O 0))) :=
  ArithmeticSourceEquation.equation_arith p (parameter_arith 1)
    (binary_column_arith (parameter_arith 0) false)
    (binary_column_arith (binary_column_arith (parameter_arith 0) true) false)
    (binary_column_arith (binary_column_arith (parameter_arith 0) true) true)

theorem source_equation_truth (p : OracleCode) :
    ∃ Q : PrefixPredicate, ArithmeticPrefix Q ∧ (∀ O v, Upward (Q O v)) ∧
      ∀ P G : Oracle, Generic (fun _ => P) G →
        (SourceEquation p P (triple G) ↔
          G ∈ OpenSet (Q (fun _ => P) 0)) := by
  obtain ⟨Q,hQ,hup,ht⟩ := ArithmeticGenericTruth.arithmetic_generic_truth (triple_equation_arith p)
  refine ⟨Q,hQ,hup,?_⟩
  intro P G hG
  simpa using ht (fun _ => P) 0 G hG

theorem source_equation_of_dense (p : OracleCode) (P : Oracle)
    (hd : ∀ s : List Bool, ∃ H : Oracle,
      Generic (fun _ => P) H ∧ Realizes s H ∧ SourceEquation p P (triple H)) :
    ∀ G : Oracle, Generic (fun _ => P) G → SourceEquation p P (triple G) := by
  have hden : ∀ s : List Bool, ∃ H : Oracle,
      Generic (fun _ => P) H ∧ Realizes s H ∧
        SourceEquation p ((Function.update (fun _ => P) 0 H) 1)
          (triple ((Function.update (fun _ => P) 0 H) 0)) := by
    simpa using hd
  simpa using ArithmeticGenericDensity.truth_of_dense (triple_equation_arith p)
    (fun _ => P) 0 hden

end TuringRigidity.ArithmeticSourceTruth

end OAI
