/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/RegularTreeExtension.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.RegularTreeRecovery
public import LeanPool.TuringConeRigidity.SetModels.InternalNameEvaluation
public import LeanPool.TuringConeRigidity.SetModels.CountedRegularBasis

/-!
# Regular Tree Extension
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RegularTreeExtension
open TransitiveNameModel BoundedSetTheory CountableForcing InternalRegularOperations
open InternalRegularAlgebra InternalBooleanGeneric InternalBooleanDense RegularTreeFilter
open RegularTreeRecovery InternalCohen
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem extension_properties (M c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    let N := genericExtensionSet M c G.carrier
    Transitive N ∧ SourceT N ∧ M ⊆ N ∧ genericFilterSet c G.carrier ∈ N := by
  let _ : Top (Conditions c) := ⟨Classical.choose G.nonempty⟩
  have ht : ⊤ ∈ G.carrier := Classical.choose_spec G.nonempty
  exact ⟨genericExtensionSet_transitive M c hM G.carrier,
    extension_sourceT M hM hT hc (InternalCollapse.orderSet_mem M hM hT hc)
      (InternalCollapse.orderSet_pair c) G hG ht,
    ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht,
    genericFilterSet_mem_extension M c hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht⟩

theorem branch_extension_eq (M c B A : ZFSet.{0}) (f : List Bool → ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hAf : FunctionGraph conditions B A)
    (hAs : ∀ s U, ZFSet.pair (wordCode s) U ∈ A ↔ U = f s)
    (hf : ∀ s, f s ∈ B ∧ IsCode c (f s) ∧ f s ≠ ∅)
    (hroot : f [] = c)
    (hm : ∀ s t, s <+: t → f t ⊆ f s)
    (hd : ∀ a u v : List Bool, ∀ p ∈ f (a ++ [false] ++ u),
      p ∉ f (a ++ [true] ++ v))
    (hden : ∀ U, IsCode c U → U ≠ ∅ → ∃ s, f s ⊆ U)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    let W := pushFilter (RegularTreeFilter.branch c f hroot (fun s => (hf s).2.1) hm hd G)
    AtomicForcing.GroundGeneric M W ∧
      genericExtensionSet M conditions W.carrier = genericExtensionSet M c G.carrier := by
  let W := pushFilter (RegularTreeFilter.branch c f hroot (fun s => (hf s).2.1) hm hd G)
  have hW := branch_ground_generic M c B A f hM hT hBM hAM hAf hAs hf hroot hm hd hden G hG
  refine ⟨hW,?_⟩
  have hWM := conditions_mem M hM hT
  obtain ⟨hN,hTN,hMN,hgN⟩ := extension_properties M c hM hT hc G hG
  obtain ⟨hV,hTV,hMV,hwV⟩ := extension_properties M conditions hM hT hWM W hW
  obtain ⟨B',_,_,S,hSM,hSs,k,hkM,_,hks,_⟩ := CountedRegularBasis.internal_basis M c hM hT hc
  have hwN : genericFilterSet conditions W.carrier ∈ genericExtensionSet M c G.carrier := by
    rw [branchFilterSet_eq c f hroot (fun s => (hf s).2.1) hm hd G B A (fun s => (hf s).1) hAs]
    exact branchSet_mem _ B A _ hN hTN (hMN hBM) (hMN hAM) hgN
  have hgV : genericFilterSet c G.carrier ∈ genericExtensionSet M conditions W.carrier := by
    rw [originalFilterSet_eq c f hroot (fun s => (hf s).2.1) hm hd G M B A S k
      hM hT hc hBM hAM (fun s => (hf s).1) (fun s => (hf s).2.2) hAs hden
      (fun p hp => (hSs _).mpr ⟨p,hp,rfl⟩) hks hG]
    exact recoverySet_mem _ c B A S k _ hV hTV (hMV hc) (hMV hBM) (hMV hAM) (hMV hSM) (hMV hkM) hwV
  apply ZFSet.ext; intro x
  exact ⟨fun hx => InternalNameEvaluation.extension_subset M _ hN hTN hMN W.carrier hwN hx,
    fun hx => InternalNameEvaluation.extension_subset M _ hV hTV hMV G.carrier hgV hx⟩

end TuringRigidity.RegularTreeExtension

end OAI
