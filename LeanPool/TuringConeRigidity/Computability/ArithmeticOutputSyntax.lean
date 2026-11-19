/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticOutputSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ExtensionArithmeticRepresentative
public import LeanPool.TuringConeRigidity.Computability.ArithmeticRelations
public import LeanPool.TuringConeRigidity.Computability.ArithmeticSetSyntax

/-!
# Arithmetic Output Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ExtensionArithmeticRepresentative
open OracleJump UniformArithmetic CommonIdeal IndexMatrix TableIndices BoundedSetTheory Encodable
open PersistentRestrictions

theorem fixed_output_arithmetic (d k : ℕ) :
    Arith (fun O _ => Represents (iterate (join (O 0) (O 1)) k) (machine d) (O 2)) :=
  represents_arith (parameter_arith 2)
    (iterate_arith (join_arith (parameter_arith 0) (parameter_arith 1)) k) (Primrec.const d)

theorem fixed_output_bounded (d k : ℕ) :
    ∃ φ : Formula, DefinesArithmetic.{0} φ
      (fun O _ => Represents (iterate (join (O 0) (O 1)) k) (machine d) (O 2)) :=
  arithmetic_bounded_definition (fixed_output_arithmetic d k)

theorem extension_table_program (I J : CountableIdeal)
    (hIJ : I.carrier ⊆ J.carrier) (ρ : I ≃o I) (σ : J ≃o J)
    (he : Extends hIJ ρ σ) (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (A R : Oracle) (hA : degree A ∈ J.carrier)
    (hR : degree R = (ρ.symm ⟨degree (jump FixedArithmetic.zero), hz⟩).val) :
    ∃ X : Oracle, degree X = (σ ⟨degree A,hA⟩).val ∧
      ∃ d : ℕ, Represents (iterate (join A R) 5) (machine d) X := by
  obtain ⟨X,hX,hred,_⟩ := extension_literal_join_program I J hIJ ρ σ he hz A R hA hR
  obtain ⟨c,hc⟩ := (TableIndices.reduces_iff_represents X _).mp hred
  exact ⟨X,hX,encode c,by simpa only [machine_encode] using hc⟩

end TuringRigidity.ExtensionArithmeticRepresentative

end OAI
