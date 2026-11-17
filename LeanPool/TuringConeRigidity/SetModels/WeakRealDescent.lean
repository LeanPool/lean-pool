/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/WeakRealDescent.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.RealCollapseReconstruction
public import LeanPool.TuringConeRigidity.SetModels.WeakNameAvoidance

/-!
# Weak Real Descent
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.FullSetForcing
open TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
open SetDegreeDecoding PersistentRestrictions
universe u
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem persistent_graph_mem_of_real_family (M N : ZFSet.{u}) [Countable (Conditions N)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : SigmaSeparation M) (hR : SigmaReplacement M)
    (hI : Infinity M) (hMN : M ⊆ N)
    {R : ZFSet.{u}} (hRM : R ∈ M)
    (hreal : ∀ x ∈ R, ∃ B : Oracle, SetModelReals.realSet B = x)
    (I : CountableIdeal) (hIM : idealSet I ∈ M)
    (hIR : ∀ d, d ∈ I.carrier ↔ ∃ B : Oracle, SetModelReals.realSet B ∈ R ∧ degree B = d)
    (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    automorphismSet ρ ∈ M := by
  have hω := omega_mem M hM hS.bounded hI
  obtain ⟨c,hc,hcdef⟩ := InternalCollapse.conditions_exist_without_choice M hM hP hU hPow
    hS.bounded hω hRM
  have h0 : (∅ : ZFSet.{u}) ∈ c :=
    (hcdef ∅).mpr ⟨hM _ hω _ ZFSet.omega_zero,InternalCollapse.prefix_empty R⟩
  let _ := InternalCollapse.top c h0
  have hoM := InternalCollapse.orderSet_mem_without_choice M hM hP hU hPow hS.bounded hc
  have hprod := product_mem M hM hP hU hPow hS.bounded hIM hIM
  have hbound : automorphismSet.{u} ρ ⊆ ZFSet.prod (idealSet I) (idealSet I) :=
    fun _ h => (ZFSet.mem_sep.mp h).1
  have hne : ∃ x, x ∈ R := by
    obtain ⟨d,hd⟩ := I.nonempty
    obtain ⟨B,hB,_⟩ := (hIR d).mp hd
    exact ⟨_,hB⟩
  apply (subset_mem_iff_all_generic_extensions_without_choice M N hM hP hU hPow hS hR hI hMN
    hc hoM hprod hbound (InternalCollapse.orderSet_pair c) (⊤ : Conditions c)).mpr
  intro G hG _
  exact InternalCollapse.real_collapse_reconstructs M hM hP hU hPow hS hR hI hRM hc hcdef
    hne hreal I hIR ρ hρ hz G (fun D hD hd => hG D (hMN hD) hd)

end TuringRigidity.FullSetForcing

end OAI
