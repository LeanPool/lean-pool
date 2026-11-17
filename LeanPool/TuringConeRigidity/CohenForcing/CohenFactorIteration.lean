/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenFactorIteration.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenUntouchedGeneric
public import LeanPool.TuringConeRigidity.CohenForcing.CohenFactorReconstruction

/-!
# Cohen Factor Iteration
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenFactorIteration
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open CohenGroundPoset InternalCohenPartition InternalCohenProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] CohenNiceNameConstruction.cohenTop

theorem extension_eq (M A B : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) (hG : AtomicForcing.GroundGeneric M G) :
    let J := projected A B hBA G
    let L := projected A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) G
    genericExtensionSet (genericExtensionSet M (conditions B) J.carrier)
      (conditions (A \ B)) L.carrier = genericExtensionSet M (conditions A) G.carrier := by
  let J := projected A B hBA G
  let L := projected A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) G
  let N := genericExtensionSet M (conditions B) J.carrier
  let V := genericExtensionSet N (conditions (A \ B)) L.carrier
  let O := genericExtensionSet M (conditions A) G.carrier
  have hD := complement_mem M A B hM hT hA hB
  have hcA := conditions_mem M A hM hT hA
  have hcB := conditions_mem M B hM hT hB
  have hcD := conditions_mem M (A \ B) hM hT hD
  have hJG := projected_groundGeneric M A B hM hT hA hB hBA G hG
  have hLG := CohenUntouchedGeneric.untouched_ground_generic M A B hM hT hA hB hBA G hG
  have hGt : ⊤ ∈ G.carrier := by obtain ⟨p,hp⟩ := G.nonempty; exact G.upper le_top hp
  have hJt : ⊤ ∈ J.carrier := by obtain ⟨p,hp⟩ := J.nonempty; exact J.upper le_top hp
  have hLt : ⊤ ∈ L.carrier := by obtain ⟨p,hp⟩ := L.nonempty; exact L.upper le_top hp
  have hN : Transitive N := genericExtensionSet_transitive M _ hM J.carrier
  have hTN : SourceT N := extension_sourceT M hM hT hcB (InternalCollapse.orderSet_mem M hM hT hcB)
    (InternalCollapse.orderSet_pair _) J hJG hJt
  have hMN : M ⊆ N := ground_inclusion_set M _ hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hcB J.carrier hJt
  have hjN := genericFilterSet_mem_extension M _ hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hcB J.carrier hJt
  have hV : Transitive V := genericExtensionSet_transitive N _ hN L.carrier
  have hTV : SourceT V := extension_sourceT N hN hTN (hMN hcD)
    (InternalCollapse.orderSet_mem N hN hTN (hMN hcD)) (InternalCollapse.orderSet_pair _) L hLG hLt
  have hNV : N ⊆ V := ground_inclusion_set N _ hN hTN.pairing hTN.union hTN.powerSet
    hTN.separation.finitePrefix.bounded hTN.replacement.finitePrefix hTN.infinity (hMN hcD)
      L.carrier hLt
  have hlV := genericFilterSet_mem_extension N _ hN hTN.pairing hTN.union hTN.powerSet
    hTN.separation.finitePrefix.bounded hTN.replacement.finitePrefix hTN.infinity (hMN hcD)
      L.carrier hLt
  have hO : Transitive O := genericExtensionSet_transitive M _ hM G.carrier
  have hTO : SourceT O := extension_sourceT M hM hT hcA (InternalCollapse.orderSet_mem M hM hT hcA)
    (InternalCollapse.orderSet_pair _) G hG hGt
  have hMO : M ⊆ O := ground_inclusion_set M _ hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hcA G.carrier hGt
  have hgO := genericFilterSet_mem_extension M _ hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hcA G.carrier hGt
  have hNO : N ⊆ O := InternalColumnExtension.column_extension_subset M A B hM hT hA hB hBA G hG
  have hlO : genericFilterSet (conditions (A \ B)) L.carrier ∈ O := by
    rw [InternalColumnExtension.projected_filter_image]
    exact InternalColumnExtension.filterImage_mem O A (A \ B) _ hO hTO (hMO hA) (hMO hD) hgO
  have hVO : V ⊆ O := InternalNameEvaluation.extension_subset N O hO hTO hNO L.carrier hlO
  have hgV : genericFilterSet (conditions A) G.carrier ∈ V := by
    rw [←CohenFactorReconstruction.reconstruct_filter A B hBA G]
    exact CohenFactorReconstruction.reconstruct_mem V A B _ _ hV hTV
      (hNV (hMN hA)) (hNV (hMN hB)) (hNV hjN) hlV
  have hOV : O ⊆ V := InternalNameEvaluation.extension_subset M V hV hTV
    (fun _ hx => hNV (hMN hx)) G.carrier hgV
  exact ZFSet.ext (fun x => ⟨fun hx => hVO hx,fun hx => hOV hx⟩)

theorem name_ranges (M A B : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) (hG : AtomicForcing.GroundGeneric M G) :
    let J := projected A B hBA G
    let L := projected A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) G
    let N := genericExtensionSet M (conditions B) J.carrier
    (∀ τ : Name (Conditions (conditions A)), τ.encode (label (conditions A)) ∈ M →
      ∃ σ : Name (Conditions (conditions (A \ B))), σ.encode (label (conditions (A \ B))) ∈ N ∧
        σ.val L.carrier = τ.val G.carrier) ∧
    (∀ σ : Name (Conditions (conditions (A \ B))), σ.encode (label (conditions (A \ B))) ∈ N →
      ∃ τ : Name (Conditions (conditions A)), τ.encode (label (conditions A)) ∈ M ∧
        τ.val G.carrier = σ.val L.carrier) := by
  have he := extension_eq M A B hM hT hA hB hBA G hG
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

end TuringRigidity.CohenFactorIteration

end OAI
