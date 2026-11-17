/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/DegreeUniverseWithoutChoice.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ModelDegreeUniverse

/-!
# Degree Universe Without Choice
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

theorem internal_degreeCode_without_choice (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
  (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hω : ZFSet.omega.{u} ∈ M)
    (R : ZFSet.{u}) (hRM : R ∈ M)
    (hR : ∀ x ∈ R, ∃ B : Oracle, realCode B = x)
    {A : Oracle} (hA : A ∈ modelReals M) : degreeCode R A ∈ M := by
  exact internal_degreeCode_of_axioms M hM hP hU hPow hS hω R hRM hR hA

theorem internal_degreeUniverse_without_choice (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing
  M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hω : ZFSet.omega.{u} ∈ M)
    (R : ZFSet.{u}) (hRM : R ∈ M)
    (hR : ∀ w ∈ R, ∃ B : Oracle, realCode B = w) : degreeUniverse R ∈ M := by
  exact internal_degreeUniverse_of_axioms M hM hP hU hPow hS hω R hRM hR

end TuringRigidity.BoundedSetTheory

end OAI
