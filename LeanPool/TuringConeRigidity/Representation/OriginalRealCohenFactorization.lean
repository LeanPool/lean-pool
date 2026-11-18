/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/OriginalRealCohenFactorization.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenManyAbsorption
public import LeanPool.TuringConeRigidity.CohenForcing.CohenUnusedTransport
public import LeanPool.TuringConeRigidity.Representation.OriginalRealFullIteration

/-!
# Original Real Cohen Factorization
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OriginalRealCohenFactorization
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open CohenGroundPoset InternalCountableOrdinals
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem original_name_factorization (M K : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K)
    (τ : Name (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hτ : τ.encode (label (conditions (ZFSet.prod K ZFSet.omega))) ∈ M)
    (G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hG : AtomicForcing.GroundGeneric M G) (hreal : τ.val G.carrier ⊆ ZFSet.omega) :
    let X := τ.val G.carrier
    let N := RealGeneratedModel.hull M X
    RealGeneratedModel.Contains M X N ∧
      ∃ GX : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))),
        AtomicForcing.GroundGeneric N GX ∧
          genericExtensionSet N (conditions (ZFSet.prod K ZFSet.omega)) GX.carrier =
            genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier ∧
          modelReals (genericExtensionSet N (conditions (ZFSet.prod K ZFSet.omega)) GX.carrier) =
            modelReals (genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier)
              := by
  obtain ⟨C,hC,hCK,hct,E,hgraph,hE,B,hB,Q,hQ,A,hA,hBs,hQs,hAe,hclosed,σ,hσ,hBA,hall⟩ :=
    OriginalRealFullIteration.original_name_full_iteration M K hM hT hK.2.1 τ hτ
  obtain ⟨a,ha,hSa,_,_⟩ := CohenFreshColumn.fresh_column M K C hM hT hK hC hCK hct
  obtain ⟨H,hH,hval,hHull,hprop,hq,ho,hcount,Gq,hGq,hext,hcode,hL,hiter,_,hcone⟩ := hall G hG hreal
  have haM := hM K hK.2.1 a (ZFSet.mem_sdiff.mp ha).1
  have hω := sourceT_omega_mem M hM hT
  have hKM := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    hK.2.1 hω
  have hCM := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    hC hω
  have hD := InternalCohenPartition.complement_mem M _ _ hM hT hKM hCM
  obtain ⟨U,hU,hUe⟩ := CohenManyAbsorption.same_generics_absorption
    (RealGeneratedModel.hull M (τ.val G.carrier)) _ _ a hprop.1 hprop.2.1
    hq hcount (hprop.2.2.1 hD) (hprop.2.2.1 haM) hSa Gq hGq _ hL
  obtain ⟨GX,hGX,hGXe⟩ := CohenUnusedTransport.transport M _ K C hM hT hprop.1 hprop.2.1
    hprop.2.2.1 hK hC hCK hct U hU
  have hfinal := hGXe.trans (hUe.trans hiter)
  exact ⟨hprop,GX,hGX,hfinal,congrArg modelReals hfinal⟩

theorem real_factorization (M K : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K)
    (G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hG : AtomicForcing.GroundGeneric M G) (X : ZFSet.{0})
    (hX : X ∈ genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier)
    (hreal : X ⊆ ZFSet.omega) :
    RealGeneratedModel.Contains M X (RealGeneratedModel.hull M X) ∧
      ∃ GX : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))),
        AtomicForcing.GroundGeneric (RealGeneratedModel.hull M X) GX ∧
          genericExtensionSet (RealGeneratedModel.hull M X)
            (conditions (ZFSet.prod K ZFSet.omega)) GX.carrier =
              genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier := by
  obtain ⟨τ,hτ,hτX⟩ := (mem_extensionSet _ _ _ X).mp hX
  obtain ⟨hprop,GX,hGX,hEq,_⟩ := original_name_factorization M K hM hT hK τ hτ G hG (hτX.symm ▸
    hreal)
  exact hτX ▸ ⟨hprop,GX,hGX,hEq⟩

end TuringRigidity.OriginalRealCohenFactorization

end OAI
