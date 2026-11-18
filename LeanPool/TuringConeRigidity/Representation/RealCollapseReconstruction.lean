/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/RealCollapseReconstruction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.CountedRealsPresentation
public import LeanPool.TuringConeRigidity.Syntax.WeakExtensionContext
public import LeanPool.TuringConeRigidity.SetModels.CollapseInternalCountingWithoutChoice

/-!
# Real Collapse Reconstruction
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedSetTheory.InternalCollapse
open TransitiveNameModel CountableForcing AtomicForcing SetDegreeDecoding
open PersistentRestrictions
universe u
attribute [local instance] order collapsePreorder

/-- Reconstruct a set after collapsing its real parameter family, using any
presentation that only requires the resulting internal enumeration. -/
theorem set_mem_of_counted_real_collapse (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M)
    {R c S : ZFSet.{u}} (hRM : R ∈ M) (hcM : c ∈ M)
    (hc : ∀ p, p ∈ c ↔ p ∈ M ∧ Prefix R p) (hne : ∃ x, x ∈ R)
    (hconstruct : ∀ E : ZFSet.{u}, SetModelFunctions.Context E → R ∈ E →
      BoundedSetTheory.InternallyCountable E R → S ∈ E)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) :
    S ∈ genericExtensionSet M c G.carrier := by
  have hω := omega_mem M hM hS.bounded hI
  have h0 : (∅ : ZFSet.{u}) ∈ c :=
    (hc ∅).mpr ⟨hM _ hω _ ZFSet.omega_zero,prefix_empty R⟩
  let _ := top c h0
  have htop : ⊤ ∈ G.carrier := by
    obtain ⟨p,hp⟩ := G.nonempty
    exact G.upper le_top hp
  have ho := orderSet_mem_without_choice M hM hP hU hPow hS.bounded hcM
  have C := BoundedForcing.extension_context_without_choice M hM hP hU hPow hS hR hI
    hcM ho (orderSet_pair c) G hG htop
  have hME := ground_inclusion_set M c hM hP hU hPow hS.bounded hR hI hcM G.carrier htop
  have hcount := internal_counting_without_choice M hM hP hU hPow hS.bounded hR hI
    hRM hcM hc hne G hG
  exact hconstruct _ C (hME hRM) hcount

theorem real_collapse_reconstructs (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M)
    {R c : ZFSet.{u}} (hRM : R ∈ M) (hcM : c ∈ M)
    (hc : ∀ p, p ∈ c ↔ p ∈ M ∧ Prefix R p) (hne : ∃ x, x ∈ R)
    (hreal : ∀ x ∈ R, ∃ B : Oracle, SetModelReals.realSet B = x)
    (I : CountableIdeal)
    (hIR : ∀ d, d ∈ I.carrier ↔ ∃ B : Oracle, SetModelReals.realSet B ∈ R ∧ degree B = d)
    (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) :
    automorphismSet ρ ∈ genericExtensionSet M c G.carrier := by
  exact set_mem_of_counted_real_collapse M hM hP hU hPow hS hR hI hRM hcM hc hne
    (fun _ C hRE hcount => SetModelCountability.persistent_mem_of_counted_reals
      C hRE hreal hcount I hIR ρ hρ hz) G hG

end TuringRigidity.BoundedSetTheory.InternalCollapse

end OAI
