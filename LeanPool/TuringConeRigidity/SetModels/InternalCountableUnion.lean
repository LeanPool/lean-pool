/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalCountableUnion.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalCountableEnumeration

/-!
# Internal Countable Union
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalCountableUnion
open TransitiveNameModel BoundedSetTheory InternalCountableFiniteUnion InternalCountableEnumeration

theorem internally_countable_union (M U S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hU : U ∈ M) (hS : S ∈ M)
    (hsub : ∀ H ∈ S, H ⊆ U) (hct : ∀ H ∈ S, H = ∅ ∨ InternallyCountable M H)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ S)
    (hB : orbitGraph E ∈ M) (hcover : ∀ p ∈ U, ∃ n, p ∈ E n)
    (hne : ∃ p, p ∈ U) : InternallyCountable M U := by
  obtain ⟨d,hd⟩ := hne
  obtain ⟨C,hCM,T,hTM,hTfun,hEnum⟩ := internal_countable_selector M U S hM hT hU hS hsub hct
  apply internally_countable_union_of_selector M U S C T
    hM hT hU hS hCM hTM hTfun E hE hB hcover d hd
  · intro H hH g _ hHg k hk
    exact enumerates_entry U H g d k (hsub H hH) (hEnum H hH g hHg) hd hk
  · intro H hH g hHg
    exact enumerates_ranges U H g (hsub H hH) (hEnum H hH g hHg)

end TuringRigidity.InternalCountableUnion

end OAI
