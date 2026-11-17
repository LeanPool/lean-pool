/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringConeForcingDescent.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeModelGraphs
public import LeanPool.TuringConeRigidity.Representation.RealCollapseReconstruction
public import LeanPool.TuringConeRigidity.SetModels.WeakNameAvoidance

/-!
# Collapse and descent of persistent cone graphs

The collapse forcing enumerates the old family of reals. In each generic
extension this enumeration and the arithmetic presentation theorem reconstruct
the given persistent cone graph. The general name-avoidance/intersection
argument then places the graph back in the original model. The ground model
need not satisfy Choice.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeForcingDescent

open TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
open SetDegreeDecoding PersistentRestrictions ConePersistence ConeSetGraphs
open OracleJump

universe u
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

/-- Reconstruct the graph after the old real family has been collapsed. -/
theorem real_collapse_reconstructs (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M)
    {R c : ZFSet.{u}} (hRM : R ∈ M) (hcM : c ∈ M)
    (hc : ∀ p, p ∈ c ↔ p ∈ M ∧ InternalCollapse.Prefix R p)
    (hne : ∃ x, x ∈ R)
    (hreal : ∀ x ∈ R, ∃ B : Oracle, SetModelReals.realSet B = x)
    (I : CountableIdeal)
    (hIR : ∀ d, d ∈ I.carrier ↔
      ∃ B : Oracle, SetModelReals.realSet B ∈ R ∧ degree B = d)
    {a : Degree} (ρ : I ≃o Cone I a) (hρ : ConePersistence.Persistent I ρ)
    (hza : degreeJump a ∈ I.carrier)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) :
    coneGraph ρ ∈ genericExtensionSet M c G.carrier := by
  have hω := omega_mem M hM hS.bounded hI
  have h0 : (∅ : ZFSet.{u}) ∈ c :=
    (hc ∅).mpr ⟨hM _ hω _ ZFSet.omega_zero, InternalCollapse.prefix_empty R⟩
  let _ := InternalCollapse.top c h0
  have htop : ⊤ ∈ G.carrier := by
    obtain ⟨p, hp⟩ := G.nonempty
    exact G.upper le_top hp
  have ho := InternalCollapse.orderSet_mem_without_choice M hM hP hU hPow hS.bounded hcM
  have C := BoundedForcing.extension_context_without_choice M hM hP hU hPow hS hR hI
    hcM ho (InternalCollapse.orderSet_pair c) G hG htop
  have hME := ground_inclusion_set M c hM hP hU hPow hS.bounded hR hI hcM G.carrier htop
  have hcount := InternalCollapse.internal_counting_without_choice M hM hP hU hPow hS.bounded hR hI
    hRM hcM hc hne G hG
  exact ConeModelGraphs.persistent_mem_of_counted_reals C (hME hRM) hreal hcount I hIR ρ hρ hza

/-- Membership in all the relevant generic extensions descends to the ground
model. This is the full graph, not an externally supplied internality assumption. -/
theorem persistent_graph_mem_of_real_family (M N : ZFSet.{u}) [Countable (Conditions N)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : SigmaSeparation M) (hR : SigmaReplacement M)
    (hI : Infinity M) (hMN : M ⊆ N)
    {R : ZFSet.{u}} (hRM : R ∈ M)
    (hreal : ∀ x ∈ R, ∃ B : Oracle, SetModelReals.realSet B = x)
    (I : CountableIdeal) (hIM : idealSet I ∈ M)
    (hIR : ∀ d, d ∈ I.carrier ↔
      ∃ B : Oracle, SetModelReals.realSet B ∈ R ∧ degree B = d)
    {a : Degree} (ρ : I ≃o Cone I a) (hρ : ConePersistence.Persistent I ρ)
    (hza : degreeJump a ∈ I.carrier) : coneGraph ρ ∈ M := by
  have hω := omega_mem M hM hS.bounded hI
  obtain ⟨c, hc, hcdef⟩ := InternalCollapse.conditions_exist_without_choice
    M hM hP hU hPow hS.bounded hω hRM
  have h0 : (∅ : ZFSet.{u}) ∈ c :=
    (hcdef ∅).mpr ⟨hM _ hω _ ZFSet.omega_zero, InternalCollapse.prefix_empty R⟩
  let _ := InternalCollapse.top c h0
  have hoM := InternalCollapse.orderSet_mem_without_choice M hM hP hU hPow hS.bounded hc
  have hprod := product_mem M hM hP hU hPow hS.bounded hIM hIM
  have hbound := coneGraph_subset.{u} ρ
  have hne : ∃ x, x ∈ R := by
    obtain ⟨d, hd⟩ := I.nonempty
    obtain ⟨B, hB, _⟩ := (hIR d).mp hd
    exact ⟨_, hB⟩
  apply (FullSetForcing.subset_mem_iff_all_generic_extensions_without_choice
    M N hM hP hU hPow hS hR hI hMN hc hoM hprod hbound
    (InternalCollapse.orderSet_pair c) (⊤ : Conditions c)).mpr
  intro G hG _
  exact real_collapse_reconstructs M hM hP hU hPow hS hR hI hRM hc hcdef
    hne hreal I hIR ρ hρ hza G (fun D hD hd => hG D (hMN hD) hd)

end OAI.TuringRigidity.ConeForcingDescent
