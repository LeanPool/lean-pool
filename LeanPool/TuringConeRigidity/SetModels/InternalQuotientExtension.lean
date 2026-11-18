/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalQuotientExtension.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalQuotientGeneric
public import LeanPool.TuringConeRigidity.SetModels.InternalBooleanExtension

/-!
# Internal Quotient Extension
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalQuotientExtension
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax
open InternalProjectedGeneric InternalBooleanTop InternalQuotientGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

theorem intermediate_properties (M c B Q A : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    let H := projected M c B Q A hM hT hc hBM hAM hB hQ hA G
    let N := genericExtensionSet M (positive A) H.carrier
    let h := genericFilterSet (positive A) H.carrier
    let q := InternalQuotientConditions.conditions c A h
    Transitive N ∧ SourceT N ∧ M ⊆ N ∧ h ∈ N ∧ q ∈ N ∧
      InternalCollapse.orderSet q ∈ N := by
  let H := projected M c B Q A hM hT hc hBM hAM hB hQ hA G
  have hcA := top_mem_part M c B Q A hM hT hc hBM hB hQ hA
  have hc0 : c ≠ ∅ := by
    obtain ⟨p,_⟩ := G.nonempty
    exact fun he => ZFSet.notMem_empty _
      (Eq.mp (congrArg (fun d => label c p ∈ d) he) (label_mem c p))
  let _ := booleanTop c A hcA hc0
  have ht := label_booleanTop c A hcA hc0
  have hHt := top_in_filter c A (fun U hU => ((hB U).mp (hA.1 hU)).2.1) ht H
  have hpM := positive_mem M A hM hT hAM
  have hHG := projected_ground_generic M c B Q A hM hT hc hBM hAM hB hQ hA G hG
  obtain ⟨hoM,ho⟩ := projected_order_code M A hM hT hAM
  have hN := genericExtensionSet_transitive M _ hM H.carrier
  have hTN := extension_sourceT M hM hT hpM hoM ho H hHG hHt
  have hMN := ground_inclusion_set M _ hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hpM H.carrier hHt
  have hhN := genericFilterSet_mem_extension M _ hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hpM H.carrier hHt
  have hqN := InternalQuotientConditions.conditions_mem _ c A _ hN hTN (hMN hc) (hMN hAM) hhN
    (fun U hU => ((hB U).mp (hA.1 hU)).2)
  exact ⟨hN,hTN,hMN,hhN,hqN,InternalCollapse.orderSet_mem _ hN hTN hqN⟩

theorem extension_eq (M c B Q A : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (hGt : ⊤ ∈
      G.carrier) :
    let H := projected M c B Q A hM hT hc hBM hAM hB hQ hA G
    let N := genericExtensionSet M (positive A) H.carrier
    let q := InternalQuotientConditions.conditions c A (genericFilterSet (positive A) H.carrier)
    let K := quotient M c B Q A hM hT hc hBM hAM hB hQ hA G
    genericExtensionSet N q K.carrier = genericExtensionSet M c G.carrier := by
  let H := projected M c B Q A hM hT hc hBM hAM hB hQ hA G
  let N := genericExtensionSet M (positive A) H.carrier
  let q := InternalQuotientConditions.conditions c A (genericFilterSet (positive A) H.carrier)
  let K := quotient M c B Q A hM hT hc hBM hAM hB hQ hA G
  obtain ⟨hN,hTN,hMN,_,hqN,hoN⟩ := intermediate_properties M c B Q A hM hT hc hBM hAM hB hQ hA G hG
  have hKG : AtomicForcing.GroundGeneric N K :=
    quotient_ground_generic M c B Q A hM hT hc hBM hAM hB hQ hA G hG
  have hcode : genericFilterSet q K.carrier = genericFilterSet c G.carrier :=
    RestrictedForcingFilter.filterSet_eq c q (InternalQuotientConditions.conditions_subset c A _) G
      (InternalQuotientConditions.original_condition_mem M c B Q A hM hT hc hBM hAM hB hQ hA G)
  let _ : Top (Conditions q) := ⟨Classical.choose K.nonempty⟩
  have hKt : ⊤ ∈ K.carrier := Classical.choose_spec K.nonempty
  have hV := genericExtensionSet_transitive N q hN K.carrier
  have hTV := extension_sourceT N hN hTN hqN hoN (InternalCollapse.orderSet_pair q) K hKG hKt
  have hNV := ground_inclusion_set N q hN hTN.pairing hTN.union hTN.powerSet
    hTN.separation.finitePrefix.bounded hTN.replacement.finitePrefix hTN.infinity hqN K.carrier hKt
  have hkV := genericFilterSet_mem_extension N q hN hTN.pairing hTN.union hTN.powerSet
    hTN.separation.finitePrefix.bounded hTN.replacement.finitePrefix hTN.infinity hqN K.carrier hKt
  have hgV : genericFilterSet c G.carrier ∈ genericExtensionSet N q K.carrier := hcode ▸ hkV
  have hO := genericExtensionSet_transitive M c hM G.carrier
  have hTO := extension_sourceT M hM hT hc (InternalCollapse.orderSet_mem M hM hT hc)
    (InternalCollapse.orderSet_pair c) G hG hGt
  have hgO := genericFilterSet_mem_extension M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier hGt
  have hNO := InternalBooleanExtension.projected_extension_subset_original M c B Q A
    hM hT hc hBM hAM hB hQ hA G hG hGt
  have hVO := InternalNameEvaluation.extension_subset N _ hO hTO hNO K.carrier (hcode.symm ▸ hgO)
  have hOV := InternalNameEvaluation.extension_subset M _ hV hTV
    (fun _ hx => hNV (hMN hx)) G.carrier hgV
  exact ZFSet.ext (fun x => ⟨fun hx => hVO hx,fun hx => hOV hx⟩)

theorem name_ranges (M c B Q A : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (hGt : ⊤ ∈
      G.carrier) :
    let H := projected M c B Q A hM hT hc hBM hAM hB hQ hA G
    let N := genericExtensionSet M (positive A) H.carrier
    let q := InternalQuotientConditions.conditions c A (genericFilterSet (positive A) H.carrier)
    let K := quotient M c B Q A hM hT hc hBM hAM hB hQ hA G
    (∀ τ : Name (Conditions c), τ.encode (label c) ∈ M →
      ∃ σ : Name (Conditions q), σ.encode (label q) ∈ N ∧ σ.val K.carrier = τ.val G.carrier) ∧
    (∀ σ : Name (Conditions q), σ.encode (label q) ∈ N →
      ∃ τ : Name (Conditions c), τ.encode (label c) ∈ M ∧ τ.val G.carrier = σ.val K.carrier) := by
  have he := extension_eq M c B Q A hM hT hc hBM hAM hB hQ hA G hG hGt
  dsimp only
  constructor
  · intro τ hτ
    apply (mem_extensionSet _ _ _ _).mp
    rw [he]
    exact (mem_extensionSet _ _ _ _).mpr ⟨τ,hτ,rfl⟩
  · intro σ hσ
    apply (mem_extensionSet _ _ _ _).mp
    rw [←he]
    exact (mem_extensionSet _ _ _ _).mpr ⟨σ,hσ,rfl⟩

end TuringRigidity.InternalQuotientExtension

end OAI
