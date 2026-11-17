/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalQuotientGeneric.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalQuotientRequirement
public import LeanPool.TuringConeRigidity.CohenForcing.RestrictedForcingFilter
public import LeanPool.TuringConeRigidity.CohenForcing.CheckedForcingRelation
public import LeanPool.TuringConeRigidity.SetModels.InternalBooleanTop
public import LeanPool.TuringConeRigidity.SetModels.InternalQuotientLifting

/-!
# Internal Quotient Generic
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalQuotientGeneric
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames AtomicForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
open InternalBooleanProjection InternalBooleanDense InternalProjectedGeneric InternalBooleanGeneric
open InternalBooleanTop InternalQuotientRequirement
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

theorem meets_named_dense (M c B Q A : ZFSet.{0}) [Top (Conditions (positive A))]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (ht : label (positive A) ⊤ = c)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G)
    (τ : Name (Conditions (positive A))) (hτ : τ.encode (label (positive A)) ∈ M)
    (hD : Dense {p : Conditions (InternalQuotientConditions.conditions c A
      (genericFilterSet (positive A) (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier)) |
      label _ p ∈ τ.val (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier}) :
    ∃ p ∈ G.carrier, label c p ∈ τ.val (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier
      := by
  let H := projected M c B Q A hM hT hc hBM hAM hB hQ hA G
  let q := InternalQuotientConditions.conditions c A (genericFilterSet (positive A) H.carrier)
  have hAc : ∀ U ∈ A, IsCode c U := fun U hU => ((hB U).mp (hA.1 hU)).2
  have hpos := positive_mem M A hM hT hAM
  have hH := projected_ground_generic M c B Q A hM hT hc hBM hAM hB hQ hA G hG
  have hHt : ⊤ ∈ H.carrier := top_in_filter c A (fun U hU => (hAc U hU).1) ht H
  obtain ⟨hoM,ho⟩ := projected_order_code M A hM hT hAM
  let R := CheckedForcingRelation.relation c τ
  have hR : R ∈ M := CheckedForcingRelation.relation_mem M c hM hT hpos hc hoM ho τ hτ
  have htruth (r : Conditions c) : label c r ∈ τ.val H.carrier ↔
      ∃ a ∈ H.carrier, MemForces (Name.check (label c r)) τ a := by
    have hcheck := encoded_check_mem M (positive A) hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hpos
      (hM c hc _ (label_mem c r))
    have h := (internal_atomic_truth M hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hpos
      hoM ho H hH (Name.check (label c r)) τ hcheck hτ).2
    simpa only [Name.val_check _ hHt] using h
  have hGq : ∀ p ∈ G.carrier, label c p ∈ q :=
    InternalQuotientConditions.original_condition_mem M c B Q A hM hT hc hBM hAM hB hQ hA G
  let U := requirement c (positive A) R
  have hUM : U ∈ M := requirement_mem M c (positive A) R hM hT hc hpos hR
  rcases generic_decision M c U hM hT hc hUM (requirement_subset c (positive A) R) G hG with hU | hn
  · obtain ⟨p,hp,hpU⟩ := hU
    obtain ⟨_,r,hr,hrp,V,hV,hpV,hrV⟩ := ZFSet.mem_sep.mp hpU
    obtain ⟨r,rfl⟩ := label_surjective c hr
    obtain ⟨a,rfl⟩ := label_surjective (positive A) hV
    have ha : a ∈ H.carrier := ⟨p,hp,hpV⟩
    have hf := (CheckedForcingRelation.pair_relation c (label c r) τ a).mp hrV
    exact ⟨r,G.upper hrp hp,(htruth r).mpr ⟨a,ha,hf.2⟩⟩
  · obtain ⟨p,hp,hpn⟩ := hn
    obtain ⟨pq,hpq⟩ := label_surjective q (hGq p hp)
    obtain ⟨rq,hrq,hrD⟩ := hD pq
    let r := RestrictedForcingFilter.inclusion c q (InternalQuotientConditions.conditions_subset c
      A _) rq
    have hre : label c r = label q rq := RestrictedForcingFilter.label_inclusion c q _ rq
    have hpr : r ≤ p := by
      change label c p ⊆ label c r
      rw [hre,←hpq]
      exact hrq
    obtain ⟨a,ha,hforce⟩ := (htruth r).mp (hre.symm ▸ hrD)
    have hrqcode : label c r ∈ q := hre.symm ▸ label_mem q rq
    obtain ⟨s,hsr,hsa⟩ := InternalQuotientLifting.quotient_compatible c A hAc hA.2.1 H r hrqcode a
      ha
    have hsU : label c s ∈ U := ZFSet.mem_sep.mpr ⟨label_mem c s,label c r,label_mem c r,hsr,
      label (positive A) a,label_mem (positive A) a,hsa,
      (CheckedForcingRelation.pair_relation c (label c r) τ a).mpr ⟨label_mem c r,hforce⟩⟩
    exact False.elim ((ZFSet.mem_sep.mp hpn).2 (label c s) hsU (hsr.trans hpr))

/-- Regard the original condition filter as a filter on the quotient poset over its projected
filter. -/
noncomputable def quotient (M c B Q A : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) :
    GenericFilter (Conditions (InternalQuotientConditions.conditions c A
      (genericFilterSet (positive A) (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier))) :=
  RestrictedForcingFilter.restrict c _ (InternalQuotientConditions.conditions_subset c A _) G
    (InternalQuotientConditions.original_condition_mem M c B Q A hM hT hc hBM hAM hB hQ hA G)

theorem quotient_ground_generic (M c B Q A : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) :
    GroundGeneric (genericExtensionSet M (positive A)
      (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier)
      (quotient M c B Q A hM hT hc hBM hAM hB hQ hA G) := by
  have hcA := top_mem_part M c B Q A hM hT hc hBM hB hQ hA
  have hc0 : c ≠ ∅ := by
    obtain ⟨p,_⟩ := G.nonempty
    exact fun he => ZFSet.notMem_empty _
      (Eq.mp (congrArg (fun d => label c p ∈ d) he) (label_mem c p))
  let _ := booleanTop c A hcA hc0
  have ht := label_booleanTop c A hcA hc0
  intro D hDN hD
  obtain ⟨τ,hτ,hval⟩ := (mem_extensionSet _ _ _ D).mp hDN
  have hD' := hD
  rw [←hval] at hD'
  obtain ⟨p,hp,hpD⟩ := meets_named_dense M c B Q A hM hT hc hBM hAM hB hQ hA ht G hG τ hτ hD'
  obtain ⟨r,hr,he⟩ := RestrictedForcingFilter.original_condition c _
    (InternalQuotientConditions.conditions_subset c A _) G
    (InternalQuotientConditions.original_condition_mem M c B Q A hM hT hc hBM hAM hB hQ hA G) p hp
  exact ⟨r,hr,he.symm ▸ hval ▸ hpD⟩

end TuringRigidity.InternalQuotientGeneric

end OAI
