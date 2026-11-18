/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenColumnPrefixGeneric.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.SparseCohenPrefixGeneric
public import LeanPool.TuringConeRigidity.CohenForcing.CohenColumnRealValue
public import LeanPool.TuringConeRigidity.SetModels.InternalSingletonColumn
public import LeanPool.TuringConeRigidity.SetModels.InternalOrderIsoTransport

/-!
# Cohen Column Prefix Generic
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenColumnRealName
open TransitiveNameModel BoundedSetTheory CountableForcing
open CohenGroundPoset InternalCohenProjectedGeneric AutomorphismName
open InternalCohen (bitSet mem_alphabet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem singleton_iso_bits (M a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) :
    ∃ e : Conditions (poset {a}) ≃o Conditions SparseCohenRealName.poset,
      ∃ f ∈ M,
        (∀ p q, ZFSet.pair (label _ p) (label _ q) ∈ f ↔ q = e p) ∧
        ∀ p n b, ZFSet.pair (natSet n) (bitSet b) ∈ label _ (e p) ↔
          ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ label _ p := by
  let B := ZFSet.prod {a} ZFSet.omega
  have hω := sourceT_omega_mem M hM hT
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded (singleton_mem M hM hT.pairing ha) hω
  obtain ⟨e,hf,he,_⟩ := InternalCohenReindex.internal_reindex M B ZFSet.omega
    (InternalSingletonColumn.graph a ZFSet.omega) hM hT hB hω
    (InternalSingletonColumn.graph_mem M a ZFSet.omega hM hT ha hω)
    (InternalSingletonColumn.graph_function a ZFSet.omega)
    (InternalSingletonColumn.graph_injective a ZFSet.omega)
    (InternalSingletonColumn.graph_onto a ZFSet.omega)
  refine ⟨e,_,hf,he,fun p n b => ?_⟩
  have hn : natSet n ∈ ZFSet.omega := (mem_omega _).mpr ⟨n,rfl⟩
  have hm := ((InternalCohenReindex.pair_reindexGraph B ZFSet.omega
    (InternalSingletonColumn.graph a ZFSet.omega) _ _).mp ((he p (e p)).mpr rfl)).2.2
  exact (hm _ (ZFSet.pair_mem_prod.mpr ⟨ZFSet.mem_singleton.mpr rfl,hn⟩) _ hn
    ((InternalSingletonColumn.pair_graph a ZFSet.omega _ _).mpr ⟨hn,rfl⟩)
    (bitSet b) ((mem_alphabet _).mpr ⟨b,rfl⟩)).symm

theorem selected_real_prefix_generic (M K a : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : AtomicForcing.GroundGeneric M G)
    (A : Oracle) (hv : (realName K a).val G.carrier = realCode A) :
    AtomicForcing.GroundGeneric M (InternalCohen.pushFilter (CohenBorelForcing.realFilter A)) := by
  let C := ZFSet.prod K ZFSet.omega
  let B := ZFSet.prod {a} ZFSet.omega
  let hBC := singleton_coordinates_subset K a ha
  let H := projected C B hBC G
  have haM := hM K hK a ha
  have hsingle := singleton_mem M hM hT.pairing haM
  have hC := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK (sourceT_omega_mem M hM hT)
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hsingle (sourceT_omega_mem M hM hT)
  have hH := projected_groundGeneric M C B hM hT hC hB hBC G hG
  obtain ⟨AH,hvH,hbits,_⟩ := generic_real_value M {a} a hM hT hsingle
    (ZFSet.mem_singleton.mpr rfl) H hH
  obtain ⟨AG,hvGH,hvG,_,_⟩ := projected_real_value M K a hM hT hK ha G hG
  have hAG : AG = A := realCode_injective (hvG.symm.trans hv)
  have hAH : AH = AG := realCode_injective (hvH.symm.trans hvGH)
  subst AG; subst AH
  obtain ⟨e,f,hf,he,hbit⟩ := singleton_iso_bits M a hM hT haM
  let L := mapFilter e H
  have hL := InternalOrderIsoTransport.map_ground_generic M (poset {a}) SparseCohenRealName.poset f
    hM hT (conditions_mem M B hM hT hB)
    (conditions_mem M ZFSet.omega hM hT (sourceT_omega_mem M hM hT)) hf e he H hH
  apply SparseCohenRealName.prefix_ground_generic M hM hT L hL A
  intro n b
  rw [←hbits n b,InternalCollapse.mem_unionGraph,InternalCollapse.mem_unionGraph]
  constructor
  · rintro ⟨p,hp,hpb⟩
    refine ⟨e.symm p,hp,?_⟩
    exact (hbit (e.symm p) n b).mp (by simpa only [e.apply_symm_apply] using hpb)
  · rintro ⟨p,hp,hpb⟩
    exact ⟨e p,by simpa only [L,mapFilter,Set.mem_ofPred_eq,e.symm_apply_apply] using hp,
      (hbit p n b).mpr hpb⟩

end TuringRigidity.CohenColumnRealName

end OAI
