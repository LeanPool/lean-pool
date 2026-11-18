/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetModelCountableExtensions.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelPresentedCountability
public import LeanPool.TuringConeRigidity.SetModels.SetModelCountablePresentation

/-!
# Set Model Countable Extensions
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetModelCountability
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelSyntax
open SetDegreeDecoding PersistentRestrictions PersistentPresentation EncodedForcing
universe u
noncomputable section
variable {M : ZFSet.{u}}

theorem persistent_countable_extensions (C : Context M) (hCh : InternalChoice M)
    (I : CountableIdeal) (hI : idealSet I ∈ M) (hct : InternallyCountable M (idealSet I))
    (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
    {X : Oracle} (hX : X ∈ reals M) :
    ∃ (J : CountableIdeal) (σ : J ≃o J) (hIJ : I.carrier ⊆ J.carrier),
      degree X ∈ J.carrier ∧ Extends hIJ ρ σ ∧ Persistent J σ ∧
      idealSet J ∈ M ∧ automorphismSet σ ∈ M ∧ InternallyCountable M (idealSet J) := by
  obtain ⟨A,hAM,hA⟩ := countable_presentation C hCh I hI hct
  let B := join A X
  let J := JumpIdeal.generated (degree B)
  let H := JumpIdealPresentation.presentation B
  have hH : Presented J H := JumpIdealPresentation.presents B
  have hHM : H ∈ reals M := (realClosure C).presentation ((realClosure C).join hAM hX)
  have hIJ : I.carrier ⊆ J.carrier := by
    intro y hy
    obtain ⟨n,rfl⟩ := (hA y).mp hy
    exact J.lower ((CodingExtraction.column_projection_reduces A n).trans
      (reduces_join_left A X)) (JumpIdeal.includes _)
  have hXJ : degree X ∈ J.carrier := J.lower (reduces_join_right A X) (JumpIdeal.includes _)
  obtain ⟨σ,he,hσ⟩ := PersistentExtension.source_4_1_10 I J ρ hρ hz hIJ (JumpIdeal.closed _)
  have hs := persistent_sets C hH hHM σ hσ (hIJ hz)
  exact ⟨J,σ,hIJ,hXJ,he,hσ,hs.1,hs.2,countable_of_presentation C hH hHM⟩

end
end TuringRigidity.SetModelCountability

end OAI
