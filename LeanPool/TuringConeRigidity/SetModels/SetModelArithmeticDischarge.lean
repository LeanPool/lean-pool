/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetModelArithmeticDischarge.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelInternalRelations
public import LeanPool.TuringConeRigidity.SetModels.SetModelArithmeticInterface
public import LeanPool.TuringConeRigidity.SetModels.SetModelArithmeticClosure

/-!
# Set Model Arithmetic Discharge
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetModelSyntax
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelArithmetic SetModelFunctions
open SetDegreeDecoding PersistentRestrictions PersistentPresentation
universe u
noncomputable section
variable {M : ZFSet.{u}}

theorem realClosure (C : Context M) : PersistenceRealClosure.Closed (reals M) := by
  obtain ⟨g,hg,hgc⟩ := internal_jump_graph C
  exact realClosure_of_lower_and_jump M C.transitive C.pairing C.union C.power C.separation
    C.infinity
    (lower_mem C) (fun _ h => jump_mem C h) hg hgc

theorem persistent_sets (C : Context M)
    {I : CountableIdeal} {A : Oracle} (hA : Presented I A) (hAM : A ∈ reals M)
    (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    idealSet I ∈ M ∧ automorphismSet ρ ∈ M := by
  obtain ⟨g,hg,hgc⟩ := internal_jump_graph C
  obtain ⟨E,hE,hEc⟩ := internal_degreeEquality_graph C
  exact persistent_model_sets M C.transitive C.pairing C.union C.power C.separation C.infinity
    (lower_mem C) (fun _ h => jump_mem C h) hg hgc hE hEc hA hAM ρ hρ hz

theorem persistent_extension_sets (C : Context M)
    {I : CountableIdeal} {A : Oracle} (hA : Presented I A) (hAM : A ∈ reals M)
    (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
    {X : Oracle} (hX : X ∈ reals M) :
    ∃ (J : CountableIdeal) (σ : J ≃o J) (hIJ : I.carrier ⊆ J.carrier),
      degree X ∈ J.carrier ∧ Extends hIJ ρ σ ∧ Persistent J σ ∧
      idealSet J ∈ M ∧ automorphismSet σ ∈ M := by
  obtain ⟨g,hg,hgc⟩ := internal_jump_graph C
  obtain ⟨E,hE,hEc⟩ := internal_degreeEquality_graph C
  exact persistent_model_extension_sets M C.transitive C.pairing C.union C.power C.separation
    C.infinity
    (lower_mem C) (fun _ h => jump_mem C h) hg hgc hE hEc hA hAM ρ hρ hz hX

end
end TuringRigidity.SetModelSyntax

end OAI
