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
  exact exists_generic_omitting_subset_of_axioms M N hM hP hU hPow hS hR hI
    hMN hc hoM ha hSa hSM ho p

theorem subset_mem_iff_all_generic_extensions_without_choice (M N : ZFSet.{u}) [Countable
  (Conditions N)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hMN : M ⊆ N)
    (hc : c ∈ M) {o a S : ZFSet.{u}} (hoM : o ∈ M) (ha : a ∈ M) (hSa : S ⊆ a)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (p : Conditions c) :
    S ∈ M ↔ ∀ G : GenericFilter (Conditions c), GroundGeneric N G → p ∈ G.carrier →
      S ∈ genericExtensionSet M c G.carrier := by
  exact subset_mem_iff_all_generic_extensions_of_axioms M N hM hP hU hPow hS hR hI
    hMN hc hoM ha hSa ho p

end TuringRigidity.FullSetForcing

end OAI
