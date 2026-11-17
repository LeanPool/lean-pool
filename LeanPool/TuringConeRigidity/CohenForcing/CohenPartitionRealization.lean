/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenPartitionRealization.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenPartitionJoint
public import LeanPool.TuringConeRigidity.CohenForcing.CohenColumnRealValue

/-!
# Cohen Partition Realization
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.CohenPartitionRealization
open TransitiveNameModel BoundedSetTheory CountableForcing CohenGroundPoset
open InternalCohenFactor InternalCohenProjectedGeneric TaggedProductConditions CohenProductSplitting
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem reassemble_projected (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A)
    (J : GenericFilter (Conditions (conditions B))) (hJ : AtomicForcing.GroundGeneric M J)
    (R : GenericFilter (Conditions (conditions (A \ B))))
    (hR : AtomicForcing.GroundGeneric (genericExtensionSet M (conditions B) J.carrier) R) :
    ∃ U : GenericFilter (Conditions (conditions A)), AtomicForcing.GroundGeneric M U ∧
      genericExtensionSet M (conditions A) U.carrier =
        genericExtensionSet (genericExtensionSet M (conditions B) J.carrier)
          (conditions (A \ B)) R.carrier ∧ projected A B hBA U = J := by
  have hfac := factor_internal M A B hM hT hA hB
  have hcA := conditions_mem M A hM hT hA
  obtain ⟨c,hc,hcs,f,hf,_,hfs,_⟩ := internal_product M _ _ hM hT hfac.1 hfac.2.1
  let T := TaggedProductGeneric.joint _ _ c hcs J R
  have hTg := TaggedProductGeneric.joint_ground_generic M _ _ c hM hT hfac.1 hfac.2.1 hcs J hJ R hR
  have hTe := TaggedProductExtension.extension_eq M _ _ c hM hT hfac.1 hfac.2.1 hc hcs J hJ R hR
  let e := (productIso (conditions B) (conditions (A \ B)) c hcs).symm.trans (factorIso A B
    hBA).symm
  obtain ⟨g,hg,hge⟩ := CohenPartitionBridge.internal_union_iso M A B c f hM hT hA hB hBA hc hf hcs
    hfs
  let U := AutomorphismName.mapFilter e T
  have hU := InternalOrderIsoTransport.map_ground_generic M _ _ g hM hT hc hcA hg e hge T hTg
  have hUe := (InternalOrderIsoTransport.extension_eq M _ _ g hM hT hc hcA hg e hge T hTg).trans hTe
  have hmem (p : Conditions (conditions A)) : p ∈ U.carrier ↔
      project A B hBA p ∈ J.carrier ∧
      project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) p ∈ R.carrier := by
    change (productIso _ _ c hcs).symm ((productIso _ _ c hcs) ((factorIso A B hBA) p)) ∈
      (SourceEquationTail.productFilter J R).carrier ↔ _
    rw [OrderIso.symm_apply_apply]
    rfl
  refine ⟨U,hU,hUe,InternalCohen.filter_ext _ _ ?_⟩
  apply Set.ext
  intro p
  rw [mem_projected]
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact ((hmem q).mp hq).1
  · intro hp
    obtain ⟨r,hr⟩ := R.nonempty
    let q := (factorIso A B hBA).symm (p,r)
    have hq : factorIso A B hBA q = (p,r) := (factorIso A B hBA).apply_symm_apply _
    have hq1 : project A B hBA q = p := congrArg Prod.fst hq
    have hq2 : project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) q = r := congrArg Prod.snd hq
    exact ⟨q,(hmem q).mpr ⟨hq1.symm ▸ hp,hq2.symm ▸ hr⟩,hq1⟩

theorem reassemble_column (M K a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (ha : a ∈ K) (X : Oracle)
    (J : GenericFilter (Conditions (CohenColumnRealName.poset {a})))
    (hJ : AtomicForcing.GroundGeneric M J)
    (hJX : (CohenColumnRealName.realName {a} a).val J.carrier = realCode X)
    (R : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega \ ZFSet.prod {a}
      ZFSet.omega))))
    (hR : AtomicForcing.GroundGeneric (genericExtensionSet M (CohenColumnRealName.poset {a})
      J.carrier) R) :
    ∃ U : GenericFilter (Conditions (CohenColumnRealName.poset K)),
      AtomicForcing.GroundGeneric M U ∧
      genericExtensionSet M (CohenColumnRealName.poset K) U.carrier =
        genericExtensionSet (genericExtensionSet M (CohenColumnRealName.poset {a}) J.carrier)
          (conditions (ZFSet.prod K ZFSet.omega \ ZFSet.prod {a} ZFSet.omega)) R.carrier ∧
      (CohenColumnRealName.realName K a).val U.carrier = realCode X := by
  have hω := sourceT_omega_mem M hM hT
  have hsingle := singleton_mem M hM hT.pairing (hM K hK a ha)
  have hA := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    hK hω
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    hsingle hω
  obtain ⟨U,hU,hUe,hUJ⟩ := reassemble_projected M _ _ hM hT hA hB
    (CohenColumnRealName.singleton_coordinates_subset K a ha) J hJ R hR
  obtain ⟨Y,hYJ,hYU,_,_⟩ := CohenColumnRealName.projected_real_value M K a hM hT hK ha U hU
  rw [hUJ,hJX] at hYJ
  exact ⟨U,hU,hUe,hYU.trans hYJ.symm⟩

end TuringRigidity.CohenPartitionRealization

end OAI
