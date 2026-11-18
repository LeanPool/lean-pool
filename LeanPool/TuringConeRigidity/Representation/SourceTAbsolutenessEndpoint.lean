/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/SourceTAbsolutenessEndpoint.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.NativePersistenceSyntax

/-!
# Source TAbsoluteness Endpoint
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic ArithmeticPersistence BoundedSetTheory TransitiveNameModel
open SetModelReals SetModelFunctions SetModelSyntax SetDegreeDecoding SetModelCountability
open SetModelSatisfaction PersistentRestrictions
universe u
noncomputable section

theorem source_4_2_2_transitive_countable (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M)
    (I : CountableIdeal) (hI : idealSet I ∈ M) (hct : InternallyCountable M (idealSet I))
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    ∃ D ∈ M, ∃ L ∈ M,
      (∀ x, x ∈ D ↔ ∃ A ∈ reals M, x = degreeSet (degree A)) ∧
      (∀ A ∈ reals M, ∀ B ∈ reals M,
        ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B) ∧
      (∀ ρ : I ≃o I, automorphismSet ρ ∈ M →
        (persistenceFormula.Realize M (cons D (cons L (cons (idealSet I)
          (cons (automorphismSet ρ) (fun _ => ZFSet.omega))))) ↔ Persistent I ρ)) ∧
      (nonidentityFormula.Realize M (cons D (cons L (cons (idealSet I) (fun _ => ZFSet.omega)))) ↔
        ∃ ρ : I ≃o I, Persistent I ρ ∧ ∃ x : I, ρ x ≠ x) := by
  let C := sourceContext M hM hT
  obtain ⟨D,hDM,hD⟩ := degree_universe C
  obtain ⟨L,hLM,hL⟩ := degree_order C
  exact ⟨D,hDM,L,hLM,hD,hL,
    fun ρ hρ => native_persistence_absolute M hM hT hDM hLM hD hL I hI hct ρ hρ hz,
    (realize_nonidentityFormula M hM D L (idealSet I) hDM hLM hI C.omega_mem).trans
      (native_nonidentity_absolute M hM hT hDM hLM hD hL I hI hct hz)⟩

end
end TuringRigidity.ArithmeticTree

end OAI
