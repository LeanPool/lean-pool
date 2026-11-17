/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenDisjointPrefixPair.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenUntouchedGeneric
public import LeanPool.TuringConeRigidity.CohenForcing.CohenColumnPrefixGeneric
public import LeanPool.TuringConeRigidity.CohenForcing.CohenPrefixHull
public import LeanPool.TuringConeRigidity.CohenForcing.CohenFreshColumn

/-!
# Cohen Disjoint Prefix Pair
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.CohenDisjointPrefixPair
open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenColumnRealName InternalCohenProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem exists_iterated_pair (M K a b : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (ha : a ∈ K) (hb : b ∈ K) (hab : b ≠ a)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G) :
    ∃ L R : Oracle,
      realCode L ∈ genericExtensionSet M (poset K) G.carrier ∧
      realCode R ∈ genericExtensionSet M (poset K) G.carrier ∧
      GroundGeneric M (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) ∧
      GroundGeneric (genericExtensionSet M InternalCohen.conditions
        (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)).carrier)
        (InternalCohen.pushFilter (CohenBorelForcing.realFilter R)) := by
  let C := ZFSet.prod K ZFSet.omega
  let B := ZFSet.prod {a} ZFSet.omega
  have hBC : B ⊆ C := singleton_coordinates_subset K a ha
  have hω := sourceT_omega_mem M hM hT
  have hsingle := singleton_mem M hM hT.pairing (hM K hK a ha)
  have hC : C ∈ M := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK hω
  have hB : B ∈ M := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hsingle hω
  let J := projected C B hBC G
  have hJ : GroundGeneric M J := projected_groundGeneric M C B hM hT hC hB hBC G hG
  let N := genericExtensionSet M (poset {a}) J.carrier
  obtain ⟨hN,hTN,hMN,_⟩ := RegularTreeExtension.extension_properties M (poset {a}) hM hT
    (CohenGroundPoset.conditions_mem M B hM hT hB) J hJ
  obtain ⟨L,hLv,_,hLN⟩ := generic_real_value M {a} a hM hT hsingle
    (ZFSet.mem_singleton.mpr rfl) J hJ
  have hL := selected_real_prefix_generic M {a} a hM hT hsingle
    (ZFSet.mem_singleton.mpr rfl) J hJ L hLv
  have hLE : realCode L ∈ genericExtensionSet M (poset K) G.carrier :=
    InternalColumnExtension.column_extension_subset M C B hM hT hC hB hBC G hG hLN
  have hrem : K \ {a} ∈ M := InternalCohenPartition.complement_mem M K {a} hM hT hK hsingle
  have hbrem : b ∈ K \ {a} := ZFSet.mem_sdiff.mpr ⟨hb,fun h => hab (ZFSet.mem_singleton.mp h)⟩
  have hsecond : ∃ U : GenericFilter (Conditions (poset (K \ {a}))),
      GroundGeneric N U ∧ genericExtensionSet M (poset (K \ {a})) U.carrier ⊆
        genericExtensionSet M (poset K) G.carrier := by
    have hDC : C \ B ⊆ C := fun _ h => (ZFSet.mem_sdiff.mp h).1
    have hD := InternalCohenPartition.complement_mem M C B hM hT hC hB
    have hU := CohenUntouchedGeneric.untouched_ground_generic M C B hM hT hC hB hBC G hG
    have hUE := InternalColumnExtension.column_extension_subset M C (C \ B) hM hT hC hD hDC G hG
    let F (D : ZFSet.{0}) : Prop :=
      ∃ U : GenericFilter (Conditions (CohenGroundPoset.conditions D)),
        GroundGeneric N U ∧ genericExtensionSet M (CohenGroundPoset.conditions D) U.carrier ⊆
          genericExtensionSet M (poset K) G.carrier
    have hF : F (C \ B) := ⟨projected C (C \ B) hDC G,hU,hUE⟩
    exact (congrArg F (CohenFreshColumn.product_difference K {a} ZFSet.omega)).mp hF
  obtain ⟨U,hUN,hUE⟩ := hsecond
  have hUM : GroundGeneric M U := fun D hD hd => hUN D (hMN hD) hd
  obtain ⟨R,hRv,_,hRMU⟩ := generic_real_value M (K \ {a}) b hM hT hrem hbrem U hUM
  have hRN := selected_real_prefix_generic N (K \ {a}) b hN hTN (hMN hrem) hbrem U hUN R hRv
  have hContains : RealGeneratedModel.Contains M (realCode L) N := ⟨hN,hTN,hMN,hLN⟩
  have hprefix : genericExtensionSet M InternalCohen.conditions
      (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)).carrier ⊆ N := by
    rw [InternalCohen.prefix_extension_eq_hull M hM hT L hL]
    intro z hz
    exact (RealGeneratedModel.mem_hull M (realCode L) z ⟨N,hContains⟩).mp hz N hContains
  exact ⟨L,R,hLE,hUE hRMU,hL,fun D hD hd => hRN D (hprefix hD) hd⟩

end TuringRigidity.CohenDisjointPrefixPair

end OAI
