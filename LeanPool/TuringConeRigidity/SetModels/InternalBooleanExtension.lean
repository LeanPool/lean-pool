/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalBooleanExtension.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalBooleanName
public import LeanPool.TuringConeRigidity.SetModels.InternalNameEvaluation

/-!
# Internal Boolean Extension
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalBooleanExtension
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax
open InternalProjectedGeneric InternalBooleanTop InternalBooleanName InternalBooleanGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

noncomputable def hitSet (A g : ZFSet.{0}) : ZFSet.{0} :=
  (positive A).sep (fun U => ∃ p ∈ g, p ∈ U)

theorem hitSet_mem (N A g : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hA : A ∈ N) (hg : g ∈ N) : hitSet A g ∈ N := by
  have hs := sep_mem N hN hT.separation.finitePrefix.bounded
    (.existsMem 1 (.member 0 1)) (fun _ => g) (fun _ => hg)
    (positive_mem N A hN hT hA)
  simpa only [hitSet,Formula.Eval,cons_zero,cons_succ] using hs

theorem projected_filterSet (M c B Q A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) :
    genericFilterSet (positive A) (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier =
      hitSet A (genericFilterSet c G.carrier) := by
  apply ZFSet.ext; intro U
  rw [mem_genericFilterSet,hitSet,ZFSet.mem_sep]
  constructor
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨p,hp,hpq⟩ := hq
    exact ⟨label_mem _ q,label c p,(mem_genericFilterSet c G.carrier _).mpr ⟨p,hp,rfl⟩,hpq⟩
  · rintro ⟨hU,p,hp,hpU⟩
    obtain ⟨q,rfl⟩ := label_surjective (positive A) hU
    obtain ⟨r,hr,rfl⟩ := (mem_genericFilterSet c G.carrier p).mp hp
    exact ⟨q,⟨r,hr,hpU⟩,rfl⟩

theorem projected_extension_subset_model (M N c B Q A : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hN : Transitive N) (hTN : SourceT N) (hMN : M ⊆ N)
    (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) (hgN : genericFilterSet c G.carrier ∈ N) :
    genericExtensionSet M (positive A)
      (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier ⊆ N := by
  apply InternalNameEvaluation.extension_subset M N hN hTN hMN
  rw [projected_filterSet M c B Q A hM hT hc hBM hAM hB hQ hA G]
  exact hitSet_mem N A _ hN hTN (hMN hAM) hgN

theorem projected_extension_subset_original (M c B Q A : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (hTop : ⊤ ∈
      G.carrier) :
    genericExtensionSet M (positive A)
      (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier ⊆
        genericExtensionSet M c G.carrier := by
  have hN := genericExtensionSet_transitive M c hM G.carrier
  have hTN := extension_sourceT M hM hT hc (InternalCollapse.orderSet_mem M hM hT hc)
    (InternalCollapse.orderSet_pair c) G hG hTop
  have hMN := ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier hTop
  apply projected_extension_subset_model M _ c B Q A hM hT hN hTN hMN hc hBM hAM hB hQ hA G
  exact genericFilterSet_mem_extension M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier hTop

theorem projected_extension_sandwich (M c B Q A : ZFSet.{0})
    [Top (Conditions c)] [Top (Conditions (positive A))]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (ht : label (positive A) ⊤ = c)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M)
    (hbits : ∀ n, bitCode c (E n) ∈ A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (hTop : ⊤ ∈
      G.carrier) :
    let H := projected M c B Q A hM hT hc hBM hAM hB hQ hA G
    let N := genericExtensionSet M (positive A) H.carrier
    Transitive N ∧ SourceT N ∧ M ⊆ N ∧
      (InternalNiceName.nice E : Name (Conditions c)).val G.carrier ∈ N ∧
      genericFilterSet (positive A) H.carrier ∈ N ∧ N ⊆ genericExtensionSet M c G.carrier := by
  let H := projected M c B Q A hM hT hc hBM hAM hB hQ hA G
  have hHt := top_in_filter c A (fun U hU => ((hB U).mp (hA.1 hU)).2.1) ht H
  have hpM := positive_mem M A hM hT hAM
  have hHG := projected_ground_generic M c B Q A hM hT hc hBM hAM hB hQ hA G hG
  obtain ⟨hoM,ho⟩ := projected_order_code M A hM hT hAM
  refine ⟨genericExtensionSet_transitive M _ hM H.carrier,
    extension_sourceT M hM hT hpM hoM ho H hHG hHt,?_,?_,?_,
    projected_extension_subset_original M c B Q A hM hT hc hBM hAM hB hQ hA G hG hTop⟩
  · exact ground_inclusion_set M _ hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hpM H.carrier hHt
  · exact same_value_mem_projected_extension M c B Q A hM hT hc hBM hAM hB hQ hA ht E hE hgraph
      hbits G hG hTop
  · exact genericFilterSet_mem_extension M _ hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hpM H.carrier hHt

end TuringRigidity.InternalBooleanExtension

end OAI
