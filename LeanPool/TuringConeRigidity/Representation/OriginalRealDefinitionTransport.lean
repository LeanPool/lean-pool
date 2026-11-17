/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/OriginalRealDefinitionTransport.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.OriginalRealCohenFactorization
public import LeanPool.TuringConeRigidity.Constructibility.ConstructibleGroundReals

/-!
# Original Real Definition Transport
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OriginalRealDefinitionTransport
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open CohenGroundPoset InternalCountableOrdinals RelativeConstructible ElementaryModel
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] CohenNiceNameConstruction.cohenTop

/-- Transport data relating a real-generated hull and an alternative generic filter to the
prescribed real definition. -/
def Transported (M K : ZFSet.{0})
    (G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (f : Name (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (X : ZFSet.{0}) (δ : Ordinal.{0}) (φ : SentenceForm) : Prop :=
    let c := conditions (ZFSet.prod K ZFSet.omega)
    let N := RealGeneratedModel.hull M X
    RealGeneratedModel.Contains M X N ∧
      ∃ GX : GenericFilter (Conditions c), AtomicForcing.GroundGeneric N GX ∧
        genericExtensionSet N c GX.carrier = genericExtensionSet M c G.carrier ∧
        ∃ fX : Name (Conditions c), fX.encode (label c) ∈ N ∧
          fX.val GX.carrier = f.val G.carrier ∧
          (Name.check δ.toZFSet : Name (Conditions c)).encode (label c) ∈ N ∧
          (Name.check X : Name (Conditions c)).encode (label c) ∈ N ∧
          (Name.check δ.toZFSet : Name (Conditions c)).val GX.carrier = δ.toZFSet ∧
          (Name.check X : Name (Conditions c)).val GX.carrier = X ∧
          X ∈ level (groundReals (genericExtensionSet N c GX.carrier)) δ ∧
          fX.val GX.carrier = definedSubset
            (level (groundReals (genericExtensionSet N c GX.carrier)) δ)
              φ (fun _ : Fin φ.bound => X)

theorem original_definition_transport (M K : ZFSet.{0})
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
    Transported M K G f (τ.val G.carrier) δ φ := by
  let X := τ.val G.carrier
  unfold Transported
  intro c N
  obtain ⟨hN,GX,hGX,hE,_⟩ :=
    OriginalRealCohenFactorization.original_name_factorization M K hM hT hK τ hτ G hG hreal
  have hA := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK.2.1 (sourceT_omega_mem M hM hT)
  have hc : c ∈ N := hN.2.2.1 (conditions_mem M _ hM hT hA)
  have hcheck {z : ZFSet.{0}} (hz : z ∈ N) :
      (Name.check z : Name (Conditions c)).encode (label c) ∈ N :=
    encoded_check_mem N c hN.1 hN.2.1.pairing hN.2.1.union hN.2.1.powerSet
      hN.2.1.separation.finitePrefix.bounded hN.2.1.replacement.finitePrefix
        hN.2.1.infinity hc hz
  have ht : (⊤ : Conditions c) ∈ GX.carrier := by
    obtain ⟨q,hq⟩ := GX.nonempty
    exact GX.upper le_top hq
  have hfE : f.val G.carrier ∈ genericExtensionSet N c GX.carrier := by
    rw [hE]
    exact (mem_extensionSet M c G.carrier _).mpr ⟨f,hf,rfl⟩
  obtain ⟨fX,hfX,hval⟩ := (mem_extensionSet N c GX.carrier _).mp hfE
  exact ⟨hN,GX,hGX,hE,fX,hfX,hval,hcheck (hN.2.2.1 hδ),hcheck hN.2.2.2,
    Name.val_check GX.carrier ht δ.toZFSet,Name.val_check GX.carrier ht X,
    hE.symm ▸ hX,hval.trans (hE.symm ▸ hdef)⟩

end TuringRigidity.OriginalRealDefinitionTransport

end OAI
