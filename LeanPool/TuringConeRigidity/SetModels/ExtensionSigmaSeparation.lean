/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ExtensionSigmaSeparation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.SigmaSeparationName

/-!
# Extension Sigma Separation
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem extension_sigmaSeparation (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : SigmaSeparation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) :
    SigmaSeparation (genericExtensionSet M c G.carrier) := by
  classical
  intro φ env henv x hx
  obtain ⟨a,ha,rfl⟩ := (mem_extensionSet M c G.carrier x).mp hx
  have names_exist (i) := (mem_extensionSet M c G.carrier (env i)).mp (henv i)
  choose e he hval using names_exist
  obtain ⟨B,hB,hBS,hBval⟩ := sigma_separation_name M hM hP hU hPow hS hR hI hc hoM ho G hG φ a ha
    e he
  have hcode : (a.restrict (label c) B).encode (label c) ∈ M := by
    rw [Name.encode_restrict _ _ _ hBS]
    exact hB
  refine ⟨(a.restrict (label c) B).val G.carrier,
    (mem_extensionSet M c G.carrier _).mpr ⟨_,hcode,rfl⟩,?_⟩
  intro z _
  rw [hBval z]
  have hev : (fun i => (e i).val G.carrier) = env := funext hval
  rw [hev]

end TuringRigidity.BoundedForcing

end OAI
