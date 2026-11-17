/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/PrefixSingletonRealization.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenPrefixHull
public import LeanPool.TuringConeRigidity.CohenForcing.CohenColumnPrefixGeneric
public import LeanPool.TuringConeRigidity.SetModels.InternalInverseIso

/-!
# Prefix Singleton Realization
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.PrefixSingletonRealization
open TransitiveNameModel BoundedSetTheory CountableForcing CohenBorelForcing
open InternalCohen (bitSet wordCode)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem sparse_realization (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (A : Oracle) (hA : AtomicForcing.GroundGeneric M (InternalCohen.pushFilter (realFilter A))) :
    ∃ L : GenericFilter (Conditions SparseCohenRealName.poset),
      AtomicForcing.GroundGeneric M L ∧
      genericExtensionSet M SparseCohenRealName.poset L.carrier = RealGeneratedModel.hull M
        (realCode A) ∧
      ∀ n b, ZFSet.pair (natSet n) (bitSet b) ∈ InternalCollapse.unionGraph L ↔ A n = b := by
  let H := InternalCohen.pushFilter (realFilter A)
  let L := InternalDenseInclusion.push InternalCohen.conditions SparseCohenRealName.poset
    CohenPrefixDensity.conditions_subset H
  have hc := InternalCohen.conditions_mem M hM hT
  have hs := CohenGroundPoset.conditions_mem M ZFSet.omega hM hT (sourceT_omega_mem M hM hT)
  have hL := InternalDenseInclusion.push_ground_generic M _ _ hM hT hc hs
    CohenPrefixDensity.conditions_subset CohenPrefixDensity.dense_inclusion H hA
  have he := DenseInclusionExtension.extension_eq M _ _ hM hT hc hs
    CohenPrefixDensity.conditions_subset CohenPrefixDensity.dense_inclusion H hA
  obtain ⟨B,_,hfilter,hbits,_⟩ := SparseCohenRealName.generic_real_value M hM hT L hL
  have hBA : B = A := by
    funext n
    let p := InternalCohen.conditionEquiv (⟨FiniteShuffle.initial A (n+1)⟩ : Condition)
    have hp : p ∈ H.carrier := by
      change InternalCohen.conditionEquiv.symm p ∈ (realFilter A).carrier
      rw [show p = InternalCohen.conditionEquiv ⟨FiniteShuffle.initial A (n+1)⟩ from rfl,
        OrderIso.symm_apply_apply]
      exact (ShuffleRequirements.realizes_initial A A (n+1)).mpr (fun _ _ => rfl)
    let q := InternalDenseInclusion.embed InternalCohen.conditions SparseCohenRealName.poset
      CohenPrefixDensity.conditions_subset p
    have hq : q ∈ L.carrier := (InternalDenseInclusion.embed_mem_push _ _ _ H p).mpr hp
    apply (hfilter q).mp hq n (A n)
    rw [InternalDenseInclusion.label_embed,
      show label InternalCohen.conditions p = wordCode (FiniteShuffle.initial A (n+1)) from
        InternalCohen.label_encodeCondition ⟨FiniteShuffle.initial A (n+1)⟩]
    apply (InternalCohen.pair_mem_wordCode _ _ _).mpr
    exact ⟨by simp,by simp [FiniteShuffle.initial]⟩
  subst B
  exact ⟨L,hL,he.trans (InternalCohen.prefix_extension_eq_hull M hM hT A hA),hbits⟩

theorem singleton_realization (M a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (A : Oracle)
    (hA : AtomicForcing.GroundGeneric M (InternalCohen.pushFilter (realFilter A))) :
    ∃ J : GenericFilter (Conditions (CohenColumnRealName.poset {a})),
      AtomicForcing.GroundGeneric M J ∧
      genericExtensionSet M (CohenColumnRealName.poset {a}) J.carrier =
        RealGeneratedModel.hull M (realCode A) ∧
      (CohenColumnRealName.realName {a} a).val J.carrier = realCode A := by
  obtain ⟨L,hL,hLe,hbits⟩ := sparse_realization M hM hT A hA
  obtain ⟨e,f,hf,he,hbit⟩ := CohenColumnRealName.singleton_iso_bits M a hM hT ha
  have hω := sourceT_omega_mem M hM hT
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    (singleton_mem M hM hT.pairing ha) hω
  have hcB := CohenGroundPoset.conditions_mem M _ hM hT hB
  have hcω := CohenGroundPoset.conditions_mem M _ hM hT hω
  have hfi := InternalInverseGraph.inverse_mem M _ _ f hM hT hcB hcω hf
  have hfie : ∀ condition image,
      ZFSet.pair (label SparseCohenRealName.poset condition)
        (label (CohenColumnRealName.poset {a}) image) ∈
        InternalInverseGraph.inverse (CohenColumnRealName.poset {a}) SparseCohenRealName.poset f ↔
        image = e.symm condition := by
    intro condition image
    rw [InternalInverseGraph.pair_inverse]
    simp only [label_mem,true_and,he]
    constructor
    · intro equality
      apply e.injective
      rw [OrderIso.apply_symm_apply]
      exact equality.symm
    · intro equality
      rw [equality,OrderIso.apply_symm_apply]
  let J := AutomorphismName.mapFilter e.symm L
  have hJ := InternalOrderIsoTransport.map_ground_generic M _ _ _ hM hT hcω hcB hfi e.symm hfie L hL
  have hJe := InternalOrderIsoTransport.extension_eq M _ _ _ hM hT hcω hcB hfi e.symm hfie L hL
  refine ⟨J,hJ,hJe.trans hLe,CohenColumnRealName.val_realName {a} a J A ?_⟩
  intro n b
  rw [←hbits n b,InternalCollapse.mem_unionGraph,InternalCollapse.mem_unionGraph]
  constructor
  · rintro ⟨p,hp,hpb⟩
    exact ⟨e p,hp,(hbit p n b).mpr hpb⟩
  · rintro ⟨p,hp,hpb⟩
    exact ⟨e.symm p,by simpa only [J,AutomorphismName.mapFilter,Set.mem_ofPred_eq,
      OrderIso.symm_symm,OrderIso.apply_symm_apply] using hp,
      (hbit (e.symm p) n b).mp (by simpa only [OrderIso.apply_symm_apply] using hpb)⟩

end TuringRigidity.PrefixSingletonRealization

end OAI
