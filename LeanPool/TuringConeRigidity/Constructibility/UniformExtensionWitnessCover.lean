/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/UniformExtensionWitnessCover.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ExtensionWitnessCover

/-!
# Uniform Extension Witness Cover
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem uniform_extension_witness_cover (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M) (hc : c
      ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (φ : SigmaFormula) (e : ℕ → Name (Conditions c)) (he : ∀ i, (e i).encode (label c) ∈ M)
    (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M) [Top (Conditions c)] :
    ∃ N : Name (Conditions c), N.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
      ∀ x ∈ a.val G.carrier,
        (∃ y ∈ genericExtensionSet M c G.carrier,
          φ.Realize (genericExtensionSet M c G.carrier) (cons y (cons x (fun i => (e i).val
            G.carrier)))) →
        ∃ y ∈ N.val G.carrier,
          φ.Realize (genericExtensionSet M c G.carrier) (cons y (cons x (fun i => (e i).val
            G.carrier))) := by
  exact extension_witness_cover_for_condition
    M hM hP hU hPow hS hR hI hAC hc hoM ho φ e he a ha ⊤

end TuringRigidity.BoundedForcing

end OAI
