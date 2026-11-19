/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalBooleanIntermediate.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalBooleanExtension

/-!
# Internal Boolean Intermediate
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalBooleanIntermediate
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax InternalBooleanBits
open InternalProjectedGeneric InternalBooleanTop InternalBooleanName InternalBooleanExtension
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

theorem internal_boolean_intermediate (M c : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M) :
    ∃ B ∈ M, ∃ Q ∈ M, ∃ A ∈ M,
      (∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U) ∧
      (∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) ∧
      A = InternalGeneratedAlgebra.generated c B Q (seeds c B E) ∧ Closed c B Q A ∧
      ∃ σ : Name (Conditions (positive A)), σ.encode (label (positive A)) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), AtomicForcing.GroundGeneric M G → ⊤ ∈ G.carrier →
        ∃ H : GenericFilter (Conditions (positive A)), AtomicForcing.GroundGeneric M H ∧
          (∀ q, q ∈ H.carrier ↔ InternalBooleanGeneric.Hit G (label (positive A) q)) ∧
          σ.val H.carrier = (InternalNiceName.nice E : Name (Conditions c)).val G.carrier ∧
          Transitive (genericExtensionSet M (positive A) H.carrier) ∧
          SourceT (genericExtensionSet M (positive A) H.carrier) ∧
          M ⊆ genericExtensionSet M (positive A) H.carrier ∧
          σ.val H.carrier ∈ genericExtensionSet M (positive A) H.carrier ∧
          genericFilterSet (positive A) H.carrier ∈ genericExtensionSet M (positive A) H.carrier ∧
          genericExtensionSet M (positive A) H.carrier ⊆ genericExtensionSet M c G.carrier := by
  obtain ⟨B,hBM,Q,hQM,A,hAM,hB,hQ,heq,hA,hbits,_⟩ :=
    internal_bit_generated_part M c hM hT hc E hE hgraph
  have hcA := top_mem_part M c B Q A hM hT hc hBM hB hQ hA
  have hc0 : c ≠ ∅ := by
    intro h
    exact ZFSet.notMem_empty (label c ⊤)
      (Eq.mp (congrArg (fun d => label c ⊤ ∈ d) h) (label_mem c ⊤))
  let _ := booleanTop c A hcA hc0
  have ht : label (positive A) ⊤ = c := label_booleanTop c A hcA hc0
  let σ := booleanName c A E
  have hσ := booleanName_internal M c A hM hT hc hAM E hE hgraph
  refine ⟨B,hBM,Q,hQM,A,hAM,hB,hQ,heq,hA,σ,hσ,?_⟩
  intro G hG hTop
  let H := projected M c B Q A hM hT hc hBM hAM hB hQ hA G
  have hv := val_booleanName M c B Q A hM hT hc hBM hAM hB hQ hA ht E hE hbits G hG hTop
  obtain ⟨hN,hTN,hMN,_,hHN,hNG⟩ :=
    projected_extension_sandwich M c B Q A hM hT hc hBM hAM hB hQ hA ht E hE hgraph hbits G hG hTop
  exact ⟨H,projected_ground_generic M c B Q A hM hT hc hBM hAM hB hQ hA G hG,
    fun _ => Iff.rfl,hv,hN,hTN,hMN,(mem_extensionSet _ _ _ _).mpr ⟨σ,hσ,rfl⟩,hHN,hNG⟩

theorem extension_least_for_filter (M A : ZFSet.{0})
    (H : Set (Conditions (positive A))) (N : ZFSet.{0})
    (hN : Transitive N) (hTN : SourceT N) (hMN : M ⊆ N)
    (hH : genericFilterSet (positive A) H ∈ N) :
    genericExtensionSet M (positive A) H ⊆ N :=
  InternalNameEvaluation.extension_subset M N hN hTN hMN H hH

end TuringRigidity.InternalBooleanIntermediate

end OAI
