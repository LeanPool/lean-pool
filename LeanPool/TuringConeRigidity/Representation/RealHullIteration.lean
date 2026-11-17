/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/RealHullIteration.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.TwoRealHull
public import LeanPool.TuringConeRigidity.Representation.SameExtensionIteration

/-!
# Real Hull Iteration
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RealHullIteration
open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenColumnRealName InternalCountableOrdinals RealGeneratedModel
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem exists_iterated_pair (M K : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (X Y : Oracle)
    (hX : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
    (hY : realCode Y ∈ genericExtensionSet M (poset K) G.carrier) :
    let N := RealGeneratedModel.hull M (realCode X)
    let H := RealGeneratedModel.hull N (realCode Y)
    Contains M (realCode X) N ∧ Contains N (realCode Y) H ∧ ∃ L R : Oracle,
      realCode L ∈ genericExtensionSet M (poset K) G.carrier ∧
      realCode R ∈ genericExtensionSet M (poset K) G.carrier ∧
      GroundGeneric H (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) ∧
      GroundGeneric (genericExtensionSet H InternalCohen.conditions
        (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)).carrier)
        (InternalCohen.pushFilter (CohenBorelForcing.realFilter R)) := by
  dsimp only
  obtain ⟨hN,hH,U,hU,hUE⟩ := TwoRealHull.joined_factorization M K hM hT hK G hG X Y hX hY
  obtain ⟨a,ha⟩ := InternalCountableOrdinals.nonempty M K hK
  have haM := hM K hK.2.1 a ha
  have hsingle := singleton_mem M hM hT.pairing haM
  have hsub : ({a} : ZFSet.{0}) ⊆ K := fun _ h => (ZFSet.mem_singleton.mp h) ▸ ha
  obtain ⟨b,hb,_,_,_⟩ := CohenFreshColumn.fresh_column M K {a} hM hT hK hsingle hsub
    (Or.inr (InternalCountableClosure.singleton_countable M a hM hT haM))
  have hbK := (ZFSet.mem_sdiff.mp hb).1
  have hba : b ≠ a := fun he => (ZFSet.mem_sdiff.mp hb).2 (ZFSet.mem_singleton.mpr he)
  obtain ⟨L,R,hLE,hRE,hL,hR⟩ := CohenDisjointPrefixPair.exists_iterated_pair
    _ K a b hH.1 hH.2.1 (hH.2.2.1 (hN.2.2.1 hK.2.1)) ha hbK hba U hU
  exact ⟨hN,hH,L,R,hUE ▸ hLE,hUE ▸ hRE,hL,hR⟩

theorem exists_iterated_prefix_pair (M K : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (X Y : Oracle)
    (hX : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
    (hY : realCode Y ∈ genericExtensionSet M (poset K) G.carrier) (s t : List Bool) :
    let N := RealGeneratedModel.hull M (realCode X)
    let H := RealGeneratedModel.hull N (realCode Y)
    Contains M (realCode X) N ∧ Contains N (realCode Y) H ∧ ∃ L R : Oracle,
      realCode L ∈ genericExtensionSet M (poset K) G.carrier ∧
      realCode R ∈ genericExtensionSet M (poset K) G.carrier ∧
      GroundGeneric H (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) ∧
      GroundGeneric (genericExtensionSet H InternalCohen.conditions
        (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)).carrier)
        (InternalCohen.pushFilter (CohenBorelForcing.realFilter R)) ∧
      ShuffleRequirements.Realizes s L ∧ ShuffleRequirements.Realizes t R := by
  dsimp only
  obtain ⟨hN,hH,L,R,hLE,hRE,hL,hR⟩ := exists_iterated_pair M K hM hT hK G hG X Y hX hY
  let H := RealGeneratedModel.hull (RealGeneratedModel.hull M (realCode X)) (realCode Y)
  obtain ⟨hE,hTE,_,_⟩ := RegularTreeExtension.extension_properties M (poset K) hM hT
    (CohenGroundPoset.conditions_mem M _ hM hT
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
        hK.2.1 (sourceT_omega_mem M hM hT))) G hG
  obtain ⟨hF,hTF,_,_⟩ := RegularTreeExtension.extension_properties H InternalCohen.conditions
    hH.1 hH.2.1 (InternalCohen.conditions_mem H hH.1 hH.2.1)
    (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) hL
  have hLs := GroundPrefixOverwrite.overwrite_generic H hH.1 hH.2.1 L hL s
  have hRt := GroundPrefixOverwrite.overwrite_generic _ hF hTF R hR t
  have he := FiniteOverwriteHull.overwrite_extension H hH.1 hH.2.1 L hL s
  refine ⟨hN,hH,FiniteOverwrite.overwrite s L,FiniteOverwrite.overwrite t R,
    sourceT_real_lower _ hE hTE hLE (FiniteOverwrite.overwrite_reduces s L),
    sourceT_real_lower _ hE hTE hRE (FiniteOverwrite.overwrite_reduces t R),
    hLs,?_,GroundPrefixOverwrite.overwrite_realizes s L,GroundPrefixOverwrite.overwrite_realizes t
      R⟩
  rw [he]
  exact hRt

end TuringRigidity.RealHullIteration

end OAI
