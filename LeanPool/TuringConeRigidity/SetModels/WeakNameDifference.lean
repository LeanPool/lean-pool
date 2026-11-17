/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/WeakNameDifference.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.NameDifferenceDense

/-!
# Weak Name Difference
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.FullSetForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)] [OrderTop (Conditions c)]

theorem nameDifference_dense_without_choice (M : ZFSet.{u})
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M)
    (hc : c ∈ M) {o a S : ZFSet.{u}} (hoM : o ∈ M) (ha : a ∈ M)
    (hSa : S ⊆ a) (hSM : S ∉ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (t : Name (Conditions c)) (ht : t.encode (label c) ∈ M) :
    Dense (NameDifference a S t) := by
  exact nameDifference_dense_of_axioms M hM hP hU hPow hS hR hI hc hoM ha hSa hSM ho t ht

theorem nameDifference_ne_value_without_choice (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing
  M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M)
    (hc : c ∈ M) {o a S : ZFSet.{u}} (hoM : o ∈ M) (ha : a ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (t : Name (Conditions c)) (ht : t.encode (label c) ∈ M)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G)
    {p : Conditions c} (hp : p ∈ G.carrier) (hd : p ∈ NameDifference a S t) :
    t.val G.carrier ≠ S := by
  exact nameDifference_ne_value_of_axioms M hM hP hU hPow hS hR hI hc hoM ha ho t ht G hG hp hd

end TuringRigidity.FullSetForcing

end OAI
