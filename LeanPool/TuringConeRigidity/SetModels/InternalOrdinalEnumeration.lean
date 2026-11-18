/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalOrdinalEnumeration.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.SelectorOrdinalEnumeration

/-!
# Internal Ordinal Enumeration
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse
universe u
namespace InternalWellOrder

theorem internal_ordinal_enumeration (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M)
    {a : ZFSet.{u}} (ha : a ∈ M) :
    ∃ δ ∈ M, δ.IsOrdinal ∧ ∃ F ∈ M, TransitiveNameModel.FunctionGraph δ a F ∧
      (∀ x ∈ a, ∃ i ∈ δ, ZFSet.pair i x ∈ F) ∧
      (∀ i ∈ δ, ∀ j ∈ δ, ∀ x, ZFSet.pair i x ∈ F → ZFSet.pair j x ∈ F → i = j) := by
  classical
  obtain ⟨q,hq,s,hsM,hs,hqdef⟩ := internal_selector M hM hPow hS.bounded hAC ha
  obtain ⟨δ,hδ,hδord,F,hF,hfun,hsurj,hinj,_⟩ :=
    internal_enumeration_from_selector M hM hP hU hPow hS hR hI ha hq hsM hs hqdef
  exact ⟨δ,hδ,hδord,F,hF,hfun,hsurj,hinj⟩

end InternalWellOrder
end TuringRigidity.BoundedSetTheory

end OAI
