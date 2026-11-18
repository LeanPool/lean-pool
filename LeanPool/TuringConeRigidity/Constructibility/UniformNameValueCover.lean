/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/UniformNameValueCover.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.NameValueCover

/-!
# Uniform Name Value Cover
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing
universe u
variable {c : ZFSet.{u}}

theorem uniform_name_value_cover (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {W : ZFSet.{u}} (hW : W ∈ M) [Top (Conditions c)] :
    ∃ N : Name (Conditions c), N.encode (label c) ∈ M ∧
      ∀ g : Set (Conditions c), ⊤ ∈ g → ∀ b : Name (Conditions c),
        b.encode (label c) ∈ W → b.val g ∈ N.val g := by
  exact name_value_cover_for_condition M hM hP hU hPow hS hR hI hc hW (⊤ : Conditions c)

end TuringRigidity.BoundedForcing

end OAI
