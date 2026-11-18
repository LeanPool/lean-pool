/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/SameExtensionCommonIdeal.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenDisjointPrefixPair
public import LeanPool.TuringConeRigidity.Representation.IteratedGenericCommonIdeal
public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenOddHits
public import LeanPool.TuringConeRigidity.Representation.OriginalRealCohenFactorization

/-!
# Same Extension Common Ideal
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.SameExtensionCommonIdeal
open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenColumnRealName InternalCountableOrdinals
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem exists_common_ideal_pair (M K : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (Y : Oracle) (hY : realCode Y ∈ genericExtensionSet M (poset K) G.carrier) :
    ∃ L R : Oracle,
      realCode L ∈ genericExtensionSet M (poset K) G.carrier ∧
      realCode R ∈ genericExtensionSet M (poset K) G.carrier ∧
      GroundGeneric M (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) ∧
      GroundGeneric M (InternalCohen.pushFilter (CohenBorelForcing.realFilter R)) ∧
      GenericCoding.InfiniteOdd L ∧ GenericCoding.InfiniteOdd R ∧
      GenericIdentity.PrincipalIntersection Y (join Y L) (join Y R) := by
  obtain ⟨hN,U,hU,hUE⟩ := OriginalRealCohenFactorization.real_factorization M K hM hT hK
    G hG (realCode Y) hY (realCode_subset Y)
  let N := RealGeneratedModel.hull M (realCode Y)
  obtain ⟨a,ha⟩ := InternalCountableOrdinals.nonempty M K hK
  have haM := hM K hK.2.1 a ha
  have hsingle := singleton_mem M hM hT.pairing haM
  have hsub : ({a} : ZFSet.{0}) ⊆ K := fun _ h => (ZFSet.mem_singleton.mp h) ▸ ha
  obtain ⟨b,hb,_,_,_⟩ := CohenFreshColumn.fresh_column M K {a} hM hT hK hsingle hsub
    (Or.inr (InternalCountableClosure.singleton_countable M a hM hT haM))
  have hbK := (ZFSet.mem_sdiff.mp hb).1
  have hba : b ≠ a := fun he => (ZFSet.mem_sdiff.mp hb).2 (ZFSet.mem_singleton.mpr he)
  obtain ⟨L,R,hLE,hRE,hL,hR⟩ := CohenDisjointPrefixPair.exists_iterated_pair N K a b
    hN.1 hN.2.1 (hN.2.2.1 hK.2.1) ha hbK hba U hU
  have hideal := IteratedGenericCommonIdeal.ideal_of_iterated_generics N hN.1 hN.2.1
    Y hN.2.2.2 L R hL hR
  obtain ⟨_,_,hNP,_⟩ := RegularTreeExtension.extension_properties N InternalCohen.conditions
    hN.1 hN.2.1 (InternalCohen.conditions_mem N hN.1 hN.2.1)
    (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) hL
  have hLM : GroundGeneric M (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) :=
    fun D hD hd => hL D (hN.2.2.1 hD) hd
  have hRM : GroundGeneric M (InternalCohen.pushFilter (CohenBorelForcing.realFilter R)) :=
    fun D hD hd => hR D (hNP (hN.2.2.1 hD)) hd
  exact ⟨L,R,hUE ▸ hLE,hUE ▸ hRE,hLM,hRM,
    InternalCohen.groundGeneric_infiniteOdd M hM hT L hLM,
    InternalCohen.groundGeneric_infiniteOdd M hM hT R hRM,hideal⟩

end TuringRigidity.SameExtensionCommonIdeal

end OAI
