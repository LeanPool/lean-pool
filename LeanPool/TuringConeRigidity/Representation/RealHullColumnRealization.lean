/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/RealHullColumnRealization.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.TwoRealHull
public import LeanPool.TuringConeRigidity.CohenForcing.CohenPartitionRealization
public import LeanPool.TuringConeRigidity.CohenForcing.CohenRemainderTransport
public import LeanPool.TuringConeRigidity.Effective.PrefixSingletonRealization
public import LeanPool.TuringConeRigidity.Representation.CommonExtensionProgram
public import LeanPool.TuringConeRigidity.SetModels.InternalShuffleGeneric

/-!
# Real Hull Column Realization
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing InternalCountableOrdinals
open CohenColumnRealName
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem real_hull_generic_column_realizes (M K a : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : AtomicForcing.GroundGeneric M G)
    (X A : Oracle)
    (hXE : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
    (hAE : realCode A ∈ genericExtensionSet M (poset K) G.carrier)
    (hA : AtomicForcing.GroundGeneric (RealGeneratedModel.hull M (realCode X))
      (InternalCohen.pushFilter (CohenBorelForcing.realFilter A))) :
    ColumnRealizesExtension (RealGeneratedModel.hull M (realCode X)) K a
      (genericExtensionSet M (poset K) G.carrier) A := by
  obtain ⟨hN,hH,L,hL,hLE⟩ := TwoRealHull.joined_factorization M K hM hT hK G hG X A hXE hAE
  let N := RealGeneratedModel.hull M (realCode X)
  have haM := hM K hK.2.1 a ha
  have hsingle := singleton_mem M hM hT.pairing haM
  have hsK : ({a} : ZFSet.{0}) ⊆ K := fun _ hx => ZFSet.mem_singleton.mp hx ▸ ha
  obtain ⟨R,hR,hRE⟩ := CohenRemainderTransport.transport_to_remainder M _ K {a}
    hM hT hH.1 hH.2.1 (fun _ hz => hH.2.2.1 (hN.2.2.1 hz)) hK hsingle hsK
    (Or.inr (InternalCountableClosure.singleton_countable M a hM hT haM)) L hL
  obtain ⟨J,hJ,hJE,hJA⟩ := PrefixSingletonRealization.singleton_realization N a
    hN.1 hN.2.1 (hN.2.2.1 haM) A hA
  have hRJ : AtomicForcing.GroundGeneric (genericExtensionSet N (poset {a}) J.carrier) R := by
    rw [hJE]
    exact hR
  obtain ⟨U,hU,hUE,hUA⟩ := CohenPartitionRealization.reassemble_column N K a
    hN.1 hN.2.1 (hN.2.2.1 hK.2.1) ha A J hJ hJA R hRJ
  refine ⟨U,hU,hUE.trans ?_,hUA⟩
  rw [hJE]
  exact hRE.trans hLE

theorem real_hull_shuffled_column_realizes (M K a : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : AtomicForcing.GroundGeneric M G)
    (X Y L : Oracle)
    (hXE : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
    (hYE : realCode Y ∈ genericExtensionSet M (poset K) G.carrier)
    (hLE : realCode L ∈ genericExtensionSet M (poset K) G.carrier)
    (hL : AtomicForcing.GroundGeneric (RealGeneratedModel.hull M (realCode X))
      (InternalCohen.pushFilter (CohenBorelForcing.realFilter L))) :
    ColumnRealizesExtension (RealGeneratedModel.hull M (realCode X)) K a
      (genericExtensionSet M (poset K) G.carrier) (GenericCoding.code Y L) := by
  obtain ⟨hE,hTE,_,_⟩ := RegularTreeExtension.extension_properties M (poset K) hM hT
    (CohenGroundPoset.conditions_mem M _ hM hT
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
        hK.2.1 (sourceT_omega_mem M hM hT))) G hG
  obtain ⟨hN,_,_,_⟩ := OriginalRealCohenFactorization.real_factorization M K hM hT hK
    G hG (realCode X) hXE (realCode_subset X)
  exact real_hull_generic_column_realizes M K a hM hT hK ha G hG X _ hXE
    (sourceT_real_lower _ hE hTE (sourceT_real_join _ hE hTE hYE hLE) (GenericCoding.code_reduces
      Y L))
    (InternalCohen.groundGeneric_shuffle _ hN.1 hN.2.1 L hL Y)

end TuringRigidity.RelativeConstructible

end OAI
