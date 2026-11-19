/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/OriginalRealUniformDefinition.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.OriginalRealDefinitionTransport
public import LeanPool.TuringConeRigidity.Constructibility.UniformOrdinalDefinitionName

/-!
# Original Real Uniform Definition
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OriginalRealDefinitionTransport
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open CohenGroundPoset InternalCountableOrdinals RelativeConstructible ElementaryModel
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem original_uniform_definition (M K : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K)
    (τ f : Name (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hτ : τ.encode (label (conditions (ZFSet.prod K ZFSet.omega))) ∈ M)
    (hf : f.encode (label (conditions (ZFSet.prod K ZFSet.omega))) ∈ M)
    (G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hG : AtomicForcing.GroundGeneric M G) (hreal : τ.val G.carrier ⊆ ZFSet.omega)
    (δ : Ordinal.{0}) (hδ : δ.toZFSet ∈ M) (φ : SentenceForm)
    (hX : τ.val G.carrier ∈ level (groundReals
      (genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier)) δ)
    (hdef : f.val G.carrier = definedSubset (level (groundReals
      (genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier)) δ)
        φ (fun _ : Fin φ.bound => τ.val G.carrier)) :
    let c := conditions (ZFSet.prod K ZFSet.omega)
    let X := τ.val G.carrier
    let N := RealGeneratedModel.hull M X
    RealGeneratedModel.Contains M X N ∧
      ∃ fX : Name (Conditions c), fX.encode (label c) ∈ N ∧
        (∀ H : GenericFilter (Conditions c), AtomicForcing.GroundGeneric N H →
          fX.val H.carrier = definedSubset
            (level (groundReals (genericExtensionSet N c H.carrier)) δ)
              φ (fun _ : Fin φ.bound => X)) ∧
        ∃ GX : GenericFilter (Conditions c), AtomicForcing.GroundGeneric N GX ∧
          genericExtensionSet N c GX.carrier = genericExtensionSet M c G.carrier ∧
          fX.val GX.carrier = f.val G.carrier ∧
          X ∈ level (groundReals (genericExtensionSet N c GX.carrier)) δ := by
  intro c X N
  obtain ⟨hN,GX,hGX,hExt,f₀,_,hf₀,_,_,_,_,hXL,hdef₀⟩ :=
    original_definition_transport M K hM hT hK τ f hτ hf G hG hreal δ hδ φ hX hdef
  have hA := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK.2.1 (sourceT_omega_mem M hM hT)
  have hc : c ∈ N := hN.2.2.1 (conditions_mem M _ hM hT hA)
  obtain ⟨fX,hfX,hfv⟩ := uniform_ordinal_definition_name N hN.1 hN.2.1 hc
    (InternalCollapse.orderSet_mem N hN.1 hN.2.1 hc) (InternalCollapse.orderSet_pair c)
    δ (hN.2.2.1 hδ) X hN.2.2.2 φ
  have hall (H : GenericFilter (Conditions c)) (hH : AtomicForcing.GroundGeneric N H) :
      fX.val H.carrier = definedSubset
        (level (groundReals (genericExtensionSet N c H.carrier)) δ)
          φ (fun _ : Fin φ.bound => X) := by
    obtain ⟨q,hq⟩ := H.nonempty
    exact hfv H hH (H.upper le_top hq)
  exact ⟨hN,fX,hfX,hall,GX,hGX,hExt,(hall GX hGX).trans (hdef₀.symm.trans hf₀),hXL⟩

end TuringRigidity.OriginalRealDefinitionTransport

end OAI
