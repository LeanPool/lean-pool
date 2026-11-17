/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/WeakNameAvoidance.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.CountableNameAvoidance
public import LeanPool.TuringConeRigidity.SetModels.WeakNameDifference
public import LeanPool.TuringConeRigidity.Representation.GroundGenericRequirements

/-!
# Weak Name Avoidance
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.FullSetForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)] [OrderTop (Conditions c)]

theorem exists_generic_omitting_subset_without_choice (M N : ZFSet.{u}) [Countable (Conditions N)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hMN : M ⊆ N)
    (hc : c ∈ M) {o a S : ZFSet.{u}} (hoM : o ∈ M) (ha : a ∈ M)
    (hSa : S ⊆ a) (hSM : S ∉ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (p : Conditions c) :
    ∃ G : GenericFilter (Conditions c), p ∈ G.carrier ∧ GroundGeneric N G ∧
      S ∉ genericExtensionSet M c G.carrier := by
  have ht₀ := encoded_check_mem M c hM hP hU hPow
    hS.bounded hR hI hc hc
  obtain ⟨ts,hts,hcover⟩ := ground_name_sequence M N hMN (Name.check c) ht₀
  let E : ℕ → Set (Conditions c) := fun n => NameDifference a S (ts n)
  have hE : ∀ n, Dense (E n) := fun n =>
    nameDifference_dense_without_choice M hM hP hU hPow hS hR hI hc hoM ha hSa hSM ho (ts n) (hts n)
  obtain ⟨G,hp,hG,hGE⟩ := ground_generic_with_requirements N ⟨c,hMN hc⟩ E hE p
  refine ⟨G,hp,hG,?_⟩
  intro hSG
  obtain ⟨t,ht,hval⟩ := (mem_extensionSet M c G.carrier S).mp hSG
  obtain ⟨n,hn⟩ := hcover t ht
  obtain ⟨q,hq,hqn⟩ := hGE n
  have hGM : GroundGeneric M G := fun D hD hd => hG D (hMN hD) hd
  have hne := nameDifference_ne_value_without_choice M hM hP hU hPow hS hR hI hc hoM ha ho (ts n)
    (hts n) G hGM hq hqn
  apply hne
  exact (Name.val_eq_of_encode_eq (label c) (label_injective c) G.carrier (ts n) t hn).trans hval

theorem subset_mem_iff_all_generic_extensions_without_choice (M N : ZFSet.{u}) [Countable
  (Conditions N)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hMN : M ⊆ N)
    (hc : c ∈ M) {o a S : ZFSet.{u}} (hoM : o ∈ M) (ha : a ∈ M) (hSa : S ⊆ a)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (p : Conditions c) :
    S ∈ M ↔ ∀ G : GenericFilter (Conditions c), GroundGeneric N G → p ∈ G.carrier →
      S ∈ genericExtensionSet M c G.carrier := by
  classical
  constructor
  · intro hSM G _ hp
    exact ground_inclusion_set M c hM hP hU hPow
      hS.bounded hR hI hc
      G.carrier (G.upper le_top hp) hSM
  · intro h
    by_contra hSM
    obtain ⟨G,hp,hG,hSG⟩ := exists_generic_omitting_subset_without_choice M N hM hP hU hPow hS hR
      hI hMN hc hoM ha hSa hSM ho p
    exact hSG (h G hG hp)

end TuringRigidity.FullSetForcing

end OAI
