/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/CommonGenericModels.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalDenseFamily
public import LeanPool.TuringConeRigidity.SetModels.InternalCollapseExistence

/-!
# Common Generic Models
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalGeneric
open TransitiveNameModel CountableForcing
universe u

instance extension_countable (M c : ZFSet.{u}) [Countable (Conditions M)] (G : Set (Conditions c)) :
    Countable (Conditions (genericExtensionSet M c G)) := by
  have hM : (M : Set ZFSet.{u}).Countable := by
    apply (Set.countable_range (label M)).mono
    intro x hx
    exact label_surjective M hx
  have hE : (genericExtensionSet M c G : Set ZFSet.{u}).Countable := by
    rw [genericExtensionSet_coe]
    exact genericExtension_countable M c hM G
  let : Countable (genericExtensionSet M c G : Set ZFSet.{u}) := hE.to_subtype
  exact Function.Injective.countable (f := fun p : Conditions (genericExtensionSet M c G) =>
    (⟨label _ p,label_mem _ p⟩ : (genericExtensionSet M c G : Set ZFSet.{u})))
    (fun x y h => label_injective _ (congrArg (fun z : (genericExtensionSet M c G : Set ZFSet.{u})
      => z.val) h))

theorem counting_model_with_generic (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) {c o : ZFSet.{u}} [Preorder (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ p q : Conditions c, ZFSet.pair (label c p) (label c q) ∈ o ↔ p ≤ q)
    (p₀ : Conditions c) :
    ∃ N : ZFSet.{u}, M ⊆ N ∧ Transitive N ∧ SourceT N ∧ Countable (Conditions N) ∧
      ∃ G : GenericFilter (Conditions c), p₀ ∈ G.carrier ∧
        genericFilterSet c G.carrier ∈ N ∧ AtomicForcing.GroundGeneric M G := by
  obtain ⟨D,hDM,hD,hcD⟩ := dense_family M hM hT hc hoM ho
  obtain ⟨d,hd,_,_,H,_,hMN,hN,hTN,hcount⟩ :=
    InternalCollapse.exists_internal_counting_extension M hM hT hDM ⟨c,hcD⟩
  let : Preorder (Conditions d) := InternalCollapse.collapsePreorder d
  let N := genericExtensionSet M d H.carrier
  obtain ⟨G,hp,hGN,hG⟩ := internal_ground_generic M N hM hN hT hTN hMN hc hoM hDM ho hD hcount p₀
  exact ⟨N,hMN,hN,hTN,inferInstance,G,hp,hGN,hG⟩

theorem common_generic_model (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    {c o d v : ZFSet.{u}} [Preorder (Conditions c)] [Preorder (Conditions d)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ p q : Conditions c, ZFSet.pair (label c p) (label c q) ∈ o ↔ p ≤ q)
    (hd : d ∈ M) (hvM : v ∈ M)
    (hv : ∀ p q : Conditions d, ZFSet.pair (label d p) (label d q) ∈ v ↔ p ≤ q)
    (p₀ : Conditions c) (q₀ : Conditions d) :
    ∃ N : ZFSet.{u}, M ⊆ N ∧ Transitive N ∧ SourceT N ∧ Countable (Conditions N) ∧
      ∃ G : GenericFilter (Conditions c), ∃ H : GenericFilter (Conditions d),
        p₀ ∈ G.carrier ∧ q₀ ∈ H.carrier ∧ genericFilterSet c G.carrier ∈ N ∧
        genericFilterSet d H.carrier ∈ N ∧ AtomicForcing.GroundGeneric M G ∧
          AtomicForcing.GroundGeneric M H := by
  obtain ⟨N,hMN,hN,hTN,hcount,G,hp,hGN,hG⟩ := counting_model_with_generic M hM hT hc hoM ho p₀
  let : Countable (Conditions N) := hcount
  obtain ⟨K,hNK,hK,hTK,hcountK,H,hq,hHK,hH⟩ :=
    counting_model_with_generic N hN hTN (hMN hd) (hMN hvM) hv q₀
  refine ⟨K,fun _ hx => hNK (hMN hx),hK,hTK,hcountK,G,H,hp,hq,hNK hGN,hHK,hG,?_⟩
  intro E hEM hE
  exact hH E (hMN hEM) hE

end TuringRigidity.BoundedSetTheory.InternalGeneric

end OAI
