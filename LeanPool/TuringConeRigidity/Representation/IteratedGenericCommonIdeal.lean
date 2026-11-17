/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/IteratedGenericCommonIdeal.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalCommonRequirements
public import LeanPool.TuringConeRigidity.CohenForcing.TaggedProductGeneric
public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenFilters

/-!
# Iterated Generic Common Ideal
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.IteratedGenericCommonIdeal
open TransitiveNameModel BoundedSetTheory InternalCohen CountableForcing AtomicForcing
open CohenProductSplitting CohenBorelForcing InternalCommonRequirements
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem meets_requirements (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (A : Oracle) (hA : A ∈ modelReals M) (L R : Oracle)
    (hL : GroundGeneric M (pushFilter (realFilter L)))
    (hR : GroundGeneric (genericExtensionSet M conditions (pushFilter (realFilter L)).carrier)
      (pushFilter (realFilter R))) :
    ∀ p q : OracleCode, ∃ s t : List Bool,
      CommonIdeal.Extends L s ∧ CommonIdeal.Extends R t ∧ CommonIdeal.Requirement A p q s t := by
  have hcnd := conditions_mem M hM hT
  obtain ⟨c,hc,hcs,_⟩ := TaggedProductConditions.internal_product M conditions conditions hM hT
    hcnd hcnd
  let J := pushFilter (realFilter L)
  let H := pushFilter (realFilter R)
  have hJoint := TaggedProductGeneric.joint_ground_generic M conditions conditions c
    hM hT hcnd hcnd hcs J hL H hR
  intro p q
  obtain ⟨x,hx,hxD⟩ := hJoint (denseSet c A p q)
    (denseSet_mem M c hM hT hc A hA p q) (denseSet_dense c hcs A p q)
  let I := productIso conditions conditions c hcs
  let uv := I.symm x
  have hx' : productMap conditions conditions c hcs uv ∈
      (TaggedProductGeneric.joint conditions conditions c hcs J H).carrier := by
    change I uv ∈ _
    simpa only [uv,OrderIso.apply_symm_apply] using hx
  have huv := (TaggedProductGeneric.joint_mem conditions conditions c hcs J H uv.1 uv.2).mp hx'
  let s := conditionEquiv.symm uv.1
  let t := conditionEquiv.symm uv.2
  have hs : CommonIdeal.Extends L s.word := fun i hi => (huv.1 i hi).symm
  have ht : CommonIdeal.Extends R t.word := fun i hi => (huv.2 i hi).symm
  have hlabel (r : Conditions conditions) :
      label conditions r = wordCode (conditionEquiv.symm r).word := by
    rw [←label_encodeCondition]
    exact congrArg (label conditions) (conditionEquiv.apply_symm_apply r).symm
  have hxD' : label c (I uv) ∈ denseSet c A p q := by
    simpa only [uv,OrderIso.apply_symm_apply] using hxD
  change label c (productMap conditions conditions c hcs uv) ∈ denseSet c A p q at hxD'
  rw [label_productMap,hlabel,hlabel,denseSet_spec c hcs] at hxD'
  exact ⟨s.word,t.word,hs,ht,hxD'⟩

theorem ideal_of_iterated_generics (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (A : Oracle) (hA : A ∈ modelReals M) (L R : Oracle)
    (hL : GroundGeneric M (pushFilter (realFilter L)))
    (hR : GroundGeneric (genericExtensionSet M conditions (pushFilter (realFilter L)).carrier)
      (pushFilter (realFilter R))) :
    ∀ b : Degree, b ≤ degree A ↔ b ≤ degree (join A L) ∧ b ≤ degree (join A R) :=
  CommonIdeal.ideal_of_meets A L R (meets_requirements M hM hT A hA L R hL hR)

end TuringRigidity.IteratedGenericCommonIdeal

end OAI
