/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenUntouchedGeneric.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenFactorRequirement
public import LeanPool.TuringConeRigidity.SetModels.InternalBooleanGeneric
public import LeanPool.TuringConeRigidity.SetModels.InternalColumnExtension

/-!
# Cohen Untouched Generic
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenUntouchedGeneric
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames AtomicForcing
open CohenGroundPoset InternalCohenFactor InternalCohenPartition InternalCohenProjectedGeneric
open CohenFactorRequirement
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem meets_named_dense (M A B : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) (hG : GroundGeneric M G)
    (τ : Name (Conditions (conditions B))) (hτ : τ.encode (label (conditions B)) ∈ M)
    (hD : Dense {p : Conditions (conditions (A \ B)) |
      label _ p ∈ τ.val (projected A B hBA G).carrier}) :
    ∃ r ∈ (projected A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) G).carrier,
      label _ r ∈ τ.val (projected A B hBA G).carrier := by
  let J := projected A B hBA G
  let hDA : A \ B ⊆ A := fun _ h => (ZFSet.mem_sdiff.mp h).1
  let L := projected A (A \ B) hDA G
  have hcA := conditions_mem M A hM hT hA
  have hcB := conditions_mem M B hM hT hB
  have hDM := complement_mem M A B hM hT hA hB
  have hcD := conditions_mem M (A \ B) hM hT hDM
  have ho := InternalCollapse.orderSet_mem M hM hT hcB
  have hJ : GroundGeneric M J := projected_groundGeneric M A B hM hT hA hB hBA G hG
  obtain ⟨a₀,ha₀⟩ := J.nonempty
  have hJt : ⊤ ∈ J.carrier := J.upper le_top ha₀
  let R := CheckedForcingRelation.relation (conditions (A \ B)) τ
  have hRM : R ∈ M := CheckedForcingRelation.relation_mem M _ hM hT hcB hcD ho
    (InternalCollapse.orderSet_pair _) τ hτ
  have truth (r : Conditions (conditions (A \ B))) : label _ r ∈ τ.val J.carrier ↔
      ∃ a ∈ J.carrier, MemForces (Name.check (label _ r)) τ a := by
    have hcheck := encoded_check_mem M (conditions B) hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hcB
      (hM _ hcD _ (label_mem _ r))
    have h := (internal_atomic_truth M hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hcB
      ho (InternalCollapse.orderSet_pair _) J hJ (Name.check (label _ r)) τ hcheck hτ).2
    simpa only [Name.val_check _ hJt] using h
  let U := requirement A B R
  have hUM := requirement_mem M A B R hM hT hA hB hRM
  rcases InternalBooleanGeneric.generic_decision M (conditions A) U hM hT hcA hUM
    (fun _ h => (ZFSet.mem_sep.mp h).1) G hG with hU|hn
  · obtain ⟨p,hp,hpU⟩ := hU
    obtain ⟨r,a,hpr,hpa,hra⟩ := (label_requirement A B R hBA p).mp hpU
    have hrL : r ∈ L.carrier := L.upper hpr (projected_contains A (A \ B) hDA G hp)
    have haJ : a ∈ J.carrier := J.upper hpa (projected_contains A B hBA G hp)
    exact ⟨r,hrL,(truth r).mpr ⟨a,haJ,
      ((CheckedForcingRelation.pair_relation _ _ τ a).mp hra).2⟩⟩
  · obtain ⟨p,hp,hpn⟩ := hn
    obtain ⟨r,hrp,hrD⟩ := hD (project A (A \ B) hDA p)
    obtain ⟨a,ha,hforce⟩ := (truth r).mp hrD
    obtain ⟨b,_,hba,hbp⟩ := J.directed ha (projected_contains A B hBA G hp)
    let e := factorIso A B hBA
    let s := e.symm (b,r)
    have hs : e s = (b,r) := e.apply_symm_apply _
    have hsb : project A B hBA s = b := congrArg Prod.fst hs
    have hsr : project A (A \ B) hDA s = r := congrArg Prod.snd hs
    have hsp : s ≤ p := e.le_iff_le.mp (by rw [hs]; exact ⟨hbp,hrp⟩)
    have hsU : label _ s ∈ U := by
      apply (label_requirement A B R hBA s).mpr
      refine ⟨r,a,?_,?_,(CheckedForcingRelation.pair_relation _ _ τ a).mpr ⟨label_mem _ r,hforce⟩⟩
      · rw [hsr]
      · rw [hsb]; exact hba
    exact False.elim ((ZFSet.mem_sep.mp hpn).2 (label _ s) hsU hsp)

theorem untouched_ground_generic (M A B : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) (hG : GroundGeneric M G) :
    GroundGeneric (genericExtensionSet M (conditions B) (projected A B hBA G).carrier)
      (projected A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) G) := by
  intro D hDN hD
  obtain ⟨τ,hτ,hval⟩ := (mem_extensionSet _ _ _ D).mp hDN
  have hd := hD
  rw [←hval] at hd
  obtain ⟨r,hr,hrD⟩ := meets_named_dense M A B hM hT hA hB hBA G hG τ hτ hd
  exact ⟨r,hr,hval ▸ hrD⟩

end TuringRigidity.CohenUntouchedGeneric

end OAI
