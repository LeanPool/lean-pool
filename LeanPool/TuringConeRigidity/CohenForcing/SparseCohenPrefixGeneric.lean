/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/SparseCohenPrefixGeneric.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.SparseCohenRealValue
public import LeanPool.TuringConeRigidity.CohenForcing.CohenPrefixDensity
public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenFilters

/-!
# Sparse Cohen Prefix Generic
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SparseCohenRealName
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalCohen (bitSet wordCode pair_mem_wordCode)
open CohenBorelForcing ShuffleRequirements InternalDenseInclusion
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem prefix_dense_expansion (D : ZFSet.{0})
    (hD : Dense {p : Conditions InternalCohen.conditions | label _ p ∈ D}) :
    Dense {q : Conditions poset | label _ q ∈ densePull poset InternalCohen.conditions D} := by
  intro p
  obtain ⟨s,hs⟩ := CohenPrefixDensity.condition_extends_prefix _ (label_mem poset p)
  let u : Conditions InternalCohen.conditions := InternalCohen.conditionEquiv ⟨s⟩
  have hu : label _ u = wordCode s := InternalCohen.label_encodeCondition ⟨s⟩
  obtain ⟨q,hqu,hqD⟩ := hD u
  let r := embed InternalCohen.conditions poset CohenPrefixDensity.conditions_subset q
  have hr : label poset r = label InternalCohen.conditions q := label_embed _ _ _ q
  refine ⟨r,?_,?_⟩
  · change label poset p ⊆ label poset r
    rw [hr]
    exact fun z hz => hqu (hu.symm ▸ hs hz)
  · apply ZFSet.mem_sep.mpr
    exact ⟨label_mem poset r,label _ q,label_mem _ q,hqD,by rw [hr]⟩

theorem prefix_ground_generic (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (G : GenericFilter (Conditions poset)) (hG : AtomicForcing.GroundGeneric M G)
    (A : Oracle)
    (hA : ∀ n b, ZFSet.pair (natSet n) (bitSet b) ∈ InternalCollapse.unionGraph G ↔ A n = b) :
    AtomicForcing.GroundGeneric M (InternalCohen.pushFilter (realFilter A)) := by
  intro D hDM hD
  have hc := CohenGroundPoset.conditions_mem M ZFSet.omega hM hT (sourceT_omega_mem M hM hT)
  have hp := InternalCohen.conditions_mem M hM hT
  obtain ⟨q,hq,hqD⟩ := hG (densePull poset InternalCohen.conditions D)
    (densePull_mem M poset InternalCohen.conditions D hM hT hc hp hDM)
    (prefix_dense_expansion D hD)
  obtain ⟨_,p,hp,hpD,hpq⟩ := ZFSet.mem_sep.mp hqD
  obtain ⟨s,rfl⟩ := (InternalCohen.prefix_iff_wordCode p).mp ((InternalCohen.mem_conditions p).mp
    hp)
  let t : Conditions InternalCohen.conditions := InternalCohen.conditionEquiv ⟨s⟩
  refine ⟨t,?_,?_⟩
  · have hreal : Realizes s A := by
      intro n hn
      have hb := (hA n s[n]).mp ((InternalCollapse.mem_unionGraph G _).mpr
        ⟨q,hq,hpq ((pair_mem_wordCode s n s[n]).mpr ⟨hn,rfl⟩)⟩)
      simpa only [List.getD,List.getElem?_eq_getElem hn,Option.getD_some] using hb.symm
    simpa only [t,InternalCohen.pushFilter,InternalCohen.conditionEquiv.symm_apply_apply,
      realFilter,Set.mem_ofPred_eq] using hreal
  · change label _ (InternalCohen.encodeCondition ⟨s⟩) ∈ D
    rwa [InternalCohen.label_encodeCondition]

theorem generic_real_prefix (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (G : GenericFilter (Conditions poset)) (hG : AtomicForcing.GroundGeneric M G) :
    ∃ A : Oracle, realName.val G.carrier = realCode A ∧
      (∀ p : Conditions poset, p ∈ G.carrier ↔ ∀ n b,
        ZFSet.pair (natSet n) (bitSet b) ∈ label _ p → A n = b) ∧
      AtomicForcing.GroundGeneric M (InternalCohen.pushFilter (realFilter A)) := by
  obtain ⟨A,hv,hfilter,hbits,_⟩ := generic_real_value M hM hT G hG
  exact ⟨A,hv,hfilter,prefix_ground_generic M hM hT G hG A hbits⟩

end TuringRigidity.SparseCohenRealName

end OAI
