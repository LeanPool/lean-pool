/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalQuotientLifting.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalQuotientConditions

/-!
# Internal Quotient Lifting
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalQuotientLifting
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
open InternalBooleanProjection InternalBooleanDense InternalProjectedGeneric InternalBooleanGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

theorem extension_in_code (c A : ZFSet.{0}) (hAc : ∀ U ∈ A, IsCode c U)
    (hneg : ∀ U ∈ A, neg c U ∈ A) (p : Conditions c)
    (V : ZFSet.{0}) (hVA : V ∈ A) (hV0 : V ≠ ∅)
    (hVP : V ⊆ project c A (basicCode c (label c p))) :
    ∃ r : Conditions c, r ≤ p ∧ label c r ∈ V := by
  classical
  have hVc := hAc V hVA
  have hex : ∃ r ∈ V, label c p ⊆ r := by
    by_contra hn
    have hpN : label c p ∈ neg c V := ZFSet.mem_sep.mpr
      ⟨label_mem c p,fun r hr hpr => hn ⟨r,hr,hpr⟩⟩
    have hbN := (basicCode_le_iff c _ _ (label_mem c p) (neg_isCode c V hVc)).mpr hpN
    have hPN := (project_le_iff c A _ _ (regular_isCode c _).1 (hneg V hVA)).mpr hbN
    apply hV0
    apply ZFSet.ext; intro r
    constructor
    · intro hr
      exact False.elim ((ZFSet.mem_sep.mp (hPN (hVP hr))).2 r hr (fun _ h => h))
    · exact fun hr => False.elim (ZFSet.notMem_empty r hr)
  obtain ⟨r,hr,hpr⟩ := hex
  obtain ⟨r,rfl⟩ := label_surjective c (hVc.1 hr)
  exact ⟨r,hpr,hr⟩

theorem quotient_compatible (c A : ZFSet.{0})
    (hAc : ∀ U ∈ A, IsCode c U) (hneg : ∀ U ∈ A, neg c U ∈ A)
    (H : GenericFilter (Conditions (positive A)))
    (p : Conditions c)
    (hp : label c p ∈ InternalQuotientConditions.conditions c A
      (genericFilterSet (positive A) H.carrier))
    (a : Conditions (positive A)) (ha : a ∈ H.carrier) :
    ∃ r : Conditions c, r ≤ p ∧ label c r ∈ label (positive A) a := by
  obtain ⟨b,hb,hbe⟩ := (mem_genericFilterSet _ _ _).mp (ZFSet.mem_sep.mp hp).2
  obtain ⟨v,_,hvb,hva⟩ := H.directed hb ha
  have hvp : label (positive A) v ⊆ project c A (basicCode c (label c p)) := by
    change label (positive A) v ⊆ label (positive A) b at hvb
    rwa [hbe] at hvb
  obtain ⟨r,hr,hrv⟩ := extension_in_code c A hAc hneg p _
    (label_info A v).1 (label_info A v).2 hvp
  exact ⟨r,hr,hva hrv⟩

end TuringRigidity.InternalQuotientLifting

end OAI
