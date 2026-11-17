/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/CountableGroundGeneric.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.GroundGenericRequirements

/-!
# Countable Ground Generic
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.AtomicForcing
open TransitiveNameModel BoundedSetTheory CountableForcing
universe u

theorem countable_ground_generic (M : ZFSet.{u}) [Countable (Conditions M)]
    (hne : ∃ x, x ∈ M) {c : ZFSet.{u}} [Preorder (Conditions c)] (p : Conditions c) :
    ∃ G : GenericFilter (Conditions c), p ∈ G.carrier ∧ GroundGeneric M G := by
  obtain ⟨G,hp,hG,_⟩ := ground_generic_with_requirements M hne
    (fun _ => Set.univ) (fun _ q => ⟨q,le_rfl,Set.mem_univ _⟩) p
  exact ⟨G,hp,hG⟩

end TuringRigidity.AtomicForcing

end OAI
