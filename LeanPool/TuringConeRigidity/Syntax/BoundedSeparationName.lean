/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/BoundedSeparationName.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.UniformSeparationName

/-!
# Bounded Separation Name
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem separation_name (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G)
    (φ : BoundedSetTheory.Formula) (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M)
    (e : ℕ → Name (Conditions c)) (he : ∀ i, (e i).encode (label c) ∈ M) :
    ∃ B ∈ M, B ⊆ a.support (label c) ∧ ∀ x,
      x ∈ (a.restrict (label c) B).val G.carrier ↔ x ∈ a.val G.carrier ∧
        φ.Eval (cons x (fun i => (e i).val G.carrier)) := by
  obtain ⟨B,hBM,hBsub,hB⟩ :=
    uniform_separation_name M hM hP hU hPow hS hR hI hc hoM ho φ a ha e he
  exact ⟨B,hBM,hBsub,hB G hG⟩

end TuringRigidity.BoundedForcing

end OAI
