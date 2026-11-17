/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/TaggedProductExtension.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.TaggedProductRecovery

/-!
# Tagged Product Extension
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.TaggedProductExtension
open TransitiveNameModel BoundedSetTheory CountableForcing TaggedProductConditions
open TaggedProductGeneric TaggedProductRecovery RegularTreeExtension
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem extension_eq (M a b c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hc : c ∈ M)
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
    (G : GenericFilter (Conditions a)) (hG : AtomicForcing.GroundGeneric M G)
    (H : GenericFilter (Conditions b))
    (hH : AtomicForcing.GroundGeneric (genericExtensionSet M a G.carrier) H) :
    genericExtensionSet M c (joint a b c hcs G H).carrier =
      genericExtensionSet (genericExtensionSet M a G.carrier) b H.carrier := by
  let N := genericExtensionSet M a G.carrier
  let V := genericExtensionSet N b H.carrier
  let J := joint a b c hcs G H
  let O := genericExtensionSet M c J.carrier
  obtain ⟨hN,hTN,hMN,hgN⟩ := extension_properties M a hM hT ha G hG
  obtain ⟨hV,hTV,hNV,hhV⟩ := extension_properties N b hN hTN (hMN hb) H hH
  have hJ := joint_ground_generic M a b c hM hT ha hb hcs G hG H hH
  obtain ⟨hO,hTO,hMO,hjO⟩ := extension_properties M c hM hT hc J hJ
  have hgO : genericFilterSet a G.carrier ∈ O := by
    rw [leftFilterSet_eq a b c hcs G H]
    exact sectionSet_mem O a b _ ∅ hO hTO (hMO ha) (hMO hb) hjO
      (hO _ (sourceT_omega_mem O hO hTO) _ ZFSet.omega_zero)
  have hhO : genericFilterSet b H.carrier ∈ O := by
    rw [rightFilterSet_eq a b c hcs G H]
    exact fiberSet_mem O b _ a hO hTO (hMO hb) hjO (hMO ha)
  have hNO : N ⊆ O := InternalNameEvaluation.extension_subset M O hO hTO hMO G.carrier hgO
  have hVO : V ⊆ O := InternalNameEvaluation.extension_subset N O hO hTO hNO H.carrier hhO
  have hjV : genericFilterSet c J.carrier ∈ V := by
    rw [jointFilterSet_eq a b c hcs G H]
    exact jointSet_mem V c _ _ hV hTV (hNV (hMN hc)) (hNV hgN) hhV
  have hOV : O ⊆ V := InternalNameEvaluation.extension_subset M V hV hTV
    (fun _ hx => hNV (hMN hx)) J.carrier hjV
  exact ZFSet.ext (fun x => ⟨fun hx => hOV hx,fun hx => hVO hx⟩)

end TuringRigidity.TaggedProductExtension

end OAI
