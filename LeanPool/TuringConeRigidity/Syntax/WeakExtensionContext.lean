/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/WeakExtensionContext.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ExtensionSigmaSeparation
public import LeanPool.TuringConeRigidity.SetModels.ExtensionPowerSet
public import LeanPool.TuringConeRigidity.Representation.SourceTheory
public import LeanPool.TuringConeRigidity.SetModels.SetModelFunctionGraphs

/-!
# Weak Extension Context
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedForcing
open TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]

theorem extension_context_without_choice (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M)
    (hc : c ∈ M) {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) (htop : ⊤ ∈ G.carrier) :
    SetModelFunctions.Context (genericExtensionSet M c G.carrier) := by
  exact ⟨genericExtensionSet_transitive M c hM G.carrier,
    extension_pairing M c hM hP hc G.carrier htop,
    extension_union M c o hM hP hU hPow hS.bounded hc hoM ho G,
    extension_powerSet M hM hP hU hPow hS.bounded hR hI hc hoM ho G hG htop,
    (extension_sigmaSeparation M hM hP hU hPow hS hR hI hc hoM ho G hG).bounded,
    extension_infinity M c hM hP hU hPow hS.bounded hR hI hc G.carrier htop⟩

end TuringRigidity.BoundedForcing

end OAI
