/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/SourceTheory.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.LevySigmaSchemas
public import LeanPool.TuringConeRigidity.SetModels.ExtensionChoice
public import LeanPool.TuringConeRigidity.SetModels.ExtensionSigmaReplacement

/-!
# Source Theory
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

/-- The set-theoretic fragment with basic axioms, choice, and Levy-sigma separation and
replacement. -/
structure SourceT (M : ZFSet.{u}) : Prop where
  extensionality : BasicAxioms.Extensionality M
  empty : BasicAxioms.EmptySet M
  pairing : Pairing M
  union : BoundedSetTheory.Union M
  powerSet : PowerSet M
  infinity : Infinity M
  foundation : BasicAxioms.Foundation M
  choice : Choice M
  separation : LevySigmaSeparation M
  replacement : LevySigmaReplacement M

theorem sourceT_of_finite_schemas (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M) :
      SourceT M := by
  obtain ⟨hLS,hLR⟩ := levy_sigma_schemas M hM hP hU hPow hS hR hI hAC
  have hω := omega_mem M hM hS.bounded hI
  have h0 := hM _ hω _ ZFSet.omega_zero
  exact ⟨BasicAxioms.extensionality M hM,⟨∅,h0,fun x _ => ZFSet.notMem_empty x⟩,
    hP,hU,hPow,hI,BasicAxioms.foundation M hM,hAC,hLS,hLR⟩

theorem extension_sourceT (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)] (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : CountableForcing.GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G)
    (htop : ⊤ ∈ G.carrier) :
    SourceT (genericExtensionSet M c G.carrier) := by
  have hS := hT.separation.finitePrefix
  have hR := hT.replacement.finitePrefix
  have hP := hT.pairing
  have hU := hT.union
  have hPow := hT.powerSet
  have hI := hT.infinity
  have hAC := hT.choice
  apply sourceT_of_finite_schemas _ (genericExtensionSet_transitive M c hM G.carrier)
    (extension_pairing M c hM hP hc G.carrier htop)
    (extension_union M c o hM hP hU hPow hS.bounded hc hoM ho G)
    (AtomicForcing.extension_powerSet M hM hP hU hPow hS.bounded hR hI hc hoM ho G hG htop)
    (BoundedForcing.extension_sigmaSeparation M hM hP hU hPow hS hR hI hc hoM ho G hG)
    (BoundedForcing.extension_sigmaReplacement M hM hP hU hPow hS hR hI hAC hc hoM ho G hG)
    (extension_infinity M c hM hP hU hPow hS.bounded hR hI hc G.carrier htop)
    (BoundedForcing.extension_choice M hM hP hU hPow hS hR hI hAC hc hoM ho G hG htop)

end TuringRigidity.BoundedSetTheory

end OAI
