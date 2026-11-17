/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/GeneratedBooleanPart.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BooleanProjection

/-!
# Generated Boolean Part
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.GeneratedBooleanPart
open Set BooleanProjection
universe u
variable {B : Type u} [CompleteBooleanAlgebra B]

def carrier (S : Set B) : Set B :=
  {b | ∀ A : CompleteSublattice B, (∀ a ∈ A, aᶜ ∈ A) → S ⊆ A → b ∈ A}

noncomputable def generated (S : Set B) : CompleteSublattice B :=
  CompleteSublattice.mk' (carrier S)
    (fun _ ht A hc hs => A.sSupClosed (fun _ hb => ht hb A hc hs))
    (fun _ ht A hc hs => A.sInfClosed (fun _ hb => ht hb A hc hs))

theorem subset_generated (S : Set B) : S ⊆ generated S :=
  fun _ hb _ _ hs => hs hb

theorem generated_compl (S : Set B) (b : B) (hb : b ∈ generated S) :
    bᶜ ∈ generated S := fun A hc hs => hc b (hb A hc hs)

theorem generated_le (S : Set B) (A : CompleteSublattice B)
    (hc : ∀ a ∈ A, aᶜ ∈ A) (hs : S ⊆ A) : generated S ≤ A :=
  fun _ hb => hb A hc hs

theorem generated_mono {S T : Set B} (h : S ⊆ T) : generated S ≤ generated T :=
  generated_le S (generated T) (generated_compl T) (h.trans (subset_generated T))

theorem generated_congr {S T : Set B} (h : S = T) : generated S = generated T :=
  congrArg generated h

end TuringRigidity.GeneratedBooleanPart

end OAI
