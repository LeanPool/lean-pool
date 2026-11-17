/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/SameExtensionGenericTriple.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.SameExtensionIteration
public import LeanPool.TuringConeRigidity.Representation.GroundIteratedTriple
public import LeanPool.TuringConeRigidity.Effective.TriplePrefix

/-!
# Same Extension Generic Triple
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.SameExtensionGenericTriple
open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenColumnRealName InternalCountableOrdinals UniformArithmetic
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem exists_prefix_real (M K : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (s : List Bool) : ∃ Y : Oracle,
      realCode Y ∈ genericExtensionSet M (poset K) G.carrier ∧
      GroundGeneric M (InternalCohen.pushFilter (CohenBorelForcing.realFilter Y)) ∧
      ShuffleRequirements.Realizes s Y := by
  obtain ⟨a,ha⟩ := InternalCountableOrdinals.nonempty M K hK
  obtain ⟨Y,hYv,_,hYE⟩ := generic_real_value M K a hM hT hK.2.1 ha G hG
  have hYg := selected_real_prefix_generic M K a hM hT hK.2.1 ha G hG Y hYv
  obtain ⟨hE,hTE,_,_⟩ := RegularTreeExtension.extension_properties M (poset K) hM hT
    (CohenGroundPoset.conditions_mem M _ hM hT
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
        hK.2.1 (sourceT_omega_mem M hM hT))) G hG
  exact ⟨FiniteOverwrite.overwrite s Y,
    sourceT_real_lower _ hE hTE hYE (FiniteOverwrite.overwrite_reduces s Y),
    GroundPrefixOverwrite.overwrite_generic M hM hT Y hYg s,
    GroundPrefixOverwrite.overwrite_realizes s Y⟩

theorem exists_generic_prefix_triple (M K : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (O : Oracles) (hO : ∀ i, realCode (O i) ∈ M) (s : List Bool) :
    ∃ Y L R : Oracle,
      (∀ A ∈ ({Y,L,R} : Set Oracle),
        realCode A ∈ genericExtensionSet M (poset K) G.carrier ∧
        GroundGeneric M (InternalCohen.pushFilter (CohenBorelForcing.realFilter A))) ∧
      GenericCoding.InfiniteOdd L ∧ GenericCoding.InfiniteOdd R ∧
      GenericIdentity.PrincipalIntersection Y (join Y L) (join Y R) ∧
      ArithmeticPrefixForcing.Generic O (join Y (join L R)) ∧
      ShuffleRequirements.Realizes s (join Y (join L R)) := by
  obtain ⟨Y,hYE,hYg,hYs⟩ := exists_prefix_real M K hM hT hK G hG (TriplePrefix.prefixes s).1
  obtain ⟨hN,L,R,hLE,hRE,hL,hR,hLs,hRs⟩ :=
    SameExtensionIteration.exists_iterated_prefix_pair M K hM hT hK G hG Y hYE
      (TriplePrefix.prefixes s).2.1 (TriplePrefix.prefixes s).2.2
  let N := RealGeneratedModel.hull M (realCode Y)
  obtain ⟨_,_,hNF,_⟩ := RegularTreeExtension.extension_properties N InternalCohen.conditions
    hN.1 hN.2.1 (InternalCohen.conditions_mem N hN.1 hN.2.1)
    (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) hL
  have hLM : GroundGeneric M (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) :=
    fun D hD hd => hL D (hN.2.2.1 hD) hd
  have hRM : GroundGeneric M (InternalCohen.pushFilter (CohenBorelForcing.realFilter R)) :=
    fun D hD hd => hR D (hNF (hN.2.2.1 hD)) hd
  have hideal := IteratedGenericCommonIdeal.ideal_of_iterated_generics N hN.1 hN.2.1
    Y hN.2.2.2 L R hL hR
  refine ⟨Y,L,R,?_,InternalCohen.groundGeneric_infiniteOdd M hM hT L hLM,
    InternalCohen.groundGeneric_infiniteOdd M hM hT R hRM,hideal,
    GroundIteratedTriple.generic_triple M hM hT O hO Y L R hYg hN hL hR,
    TriplePrefix.realizes_join hYs hLs hRs⟩
  intro A hA
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hA
  rcases hA with hA|hA|hA <;> rw [hA]
  · exact ⟨hYE,hYg⟩
  · exact ⟨hLE,hLM⟩
  · exact ⟨hRE,hRM⟩

end TuringRigidity.SameExtensionGenericTriple

end OAI
