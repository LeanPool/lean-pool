/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/RealHullGenericTriple.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.RealHullIteration
public import LeanPool.TuringConeRigidity.Representation.SameExtensionGenericTriple

/-!
# Real Hull Generic Triple
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RealHullGenericTriple
open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenColumnRealName InternalCountableOrdinals UniformArithmetic
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem exists_prefix_real (M K : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (X : Oracle) (hX : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
    (s : List Bool) : ∃ Y : Oracle,
      realCode Y ∈ genericExtensionSet M (poset K) G.carrier ∧
      GroundGeneric (RealGeneratedModel.hull M (realCode X))
        (InternalCohen.pushFilter (CohenBorelForcing.realFilter Y)) ∧
      ShuffleRequirements.Realizes s Y := by
  obtain ⟨hN,U,hU,hUE⟩ := OriginalRealCohenFactorization.real_factorization M K hM hT hK
    G hG (realCode X) hX (realCode_subset X)
  let N := RealGeneratedModel.hull M (realCode X)
  obtain ⟨a,ha⟩ := InternalCountableOrdinals.nonempty M K hK
  obtain ⟨Y,hYv,_,hYE⟩ := generic_real_value N K a hN.1 hN.2.1 (hN.2.2.1 hK.2.1) ha U hU
  have hYg := selected_real_prefix_generic N K a hN.1 hN.2.1 (hN.2.2.1 hK.2.1) ha U hU Y hYv
  obtain ⟨hE,hTE,_,_⟩ := RegularTreeExtension.extension_properties N (poset K) hN.1 hN.2.1
    (CohenGroundPoset.conditions_mem N _ hN.1 hN.2.1
      (product_mem N hN.1 hN.2.1.pairing hN.2.1.union hN.2.1.powerSet
        hN.2.1.separation.finitePrefix.bounded (hN.2.2.1 hK.2.1)
        (sourceT_omega_mem N hN.1 hN.2.1))) U hU
  exact ⟨FiniteOverwrite.overwrite s Y,
    hUE ▸ sourceT_real_lower _ hE hTE hYE (FiniteOverwrite.overwrite_reduces s Y),
    GroundPrefixOverwrite.overwrite_generic N hN.1 hN.2.1 Y hYg s,
    GroundPrefixOverwrite.overwrite_realizes s Y⟩

theorem exists_generic_prefix_triple (M K : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (X : Oracle) (hX : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
    (O : Oracles) (hO : ∀ i, realCode (O i) ∈ RealGeneratedModel.hull M (realCode X))
    (s : List Bool) : ∃ Y L R : Oracle,
      (∀ A ∈ ({Y,L,R} : Set Oracle),
        realCode A ∈ genericExtensionSet M (poset K) G.carrier ∧
        GroundGeneric (RealGeneratedModel.hull M (realCode X))
          (InternalCohen.pushFilter (CohenBorelForcing.realFilter A))) ∧
      GenericCoding.InfiniteOdd L ∧ GenericCoding.InfiniteOdd R ∧
      GenericIdentity.PrincipalIntersection Y (join Y L) (join Y R) ∧
      ArithmeticPrefixForcing.Generic O (join Y (join L R)) ∧
      ShuffleRequirements.Realizes s (join Y (join L R)) := by
  obtain ⟨Y,hYE,hYg,hYs⟩ := exists_prefix_real M K hM hT hK G hG X hX (TriplePrefix.prefixes s).1
  obtain ⟨hN,hH,L,R,hLE,hRE,hL,hR,hLs,hRs⟩ :=
    RealHullIteration.exists_iterated_prefix_pair M K hM hT hK G hG X Y hX hYE
      (TriplePrefix.prefixes s).2.1 (TriplePrefix.prefixes s).2.2
  let N := RealGeneratedModel.hull M (realCode X)
  let H := RealGeneratedModel.hull N (realCode Y)
  obtain ⟨_,_,hHF,_⟩ := RegularTreeExtension.extension_properties H InternalCohen.conditions
    hH.1 hH.2.1 (InternalCohen.conditions_mem H hH.1 hH.2.1)
    (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) hL
  have hLN : GroundGeneric N (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) :=
    fun D hD hd => hL D (hH.2.2.1 hD) hd
  have hRN : GroundGeneric N (InternalCohen.pushFilter (CohenBorelForcing.realFilter R)) :=
    fun D hD hd => hR D (hHF (hH.2.2.1 hD)) hd
  have hideal := IteratedGenericCommonIdeal.ideal_of_iterated_generics H hH.1 hH.2.1
    Y hH.2.2.2 L R hL hR
  refine ⟨Y,L,R,?_,InternalCohen.groundGeneric_infiniteOdd N hN.1 hN.2.1 L hLN,
    InternalCohen.groundGeneric_infiniteOdd N hN.1 hN.2.1 R hRN,hideal,
    GroundIteratedTriple.generic_triple N hN.1 hN.2.1 O hO Y L R hYg hH hL hR,
    TriplePrefix.realizes_join hYs hLs hRs⟩
  intro A hA
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hA
  rcases hA with hA|hA|hA <;> rw [hA]
  · exact ⟨hYE,hYg⟩
  · exact ⟨hLE,hLN⟩
  · exact ⟨hRE,hRN⟩

end TuringRigidity.RealHullGenericTriple

end OAI
