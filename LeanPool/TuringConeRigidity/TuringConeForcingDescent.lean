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
public import LeanPool.TuringConeRigidity.SetModels.WeakRealDescent

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
  exact InternalCollapse.set_mem_of_counted_real_collapse M hM hP hU hPow hS hR hI
    hRM hcM hc hne (fun _ C hRE hcount =>
      ConeModelGraphs.persistent_mem_of_counted_reals C hRE hreal hcount I hIR ρ hρ hza) G hG

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
  have hprod := product_mem M hM hP hU hPow hS.bounded hIM hIM
  have hbound := coneGraph_subset.{u} ρ
  have hne : ∃ x, x ∈ R := by
    obtain ⟨d, hd⟩ := I.nonempty
    obtain ⟨B, hB, _⟩ := (hIR d).mp hd
    exact ⟨_, hB⟩
  exact FullSetForcing.set_mem_of_real_collapse_reconstruction M N hM hP hU hPow hS hR hI
    hMN hRM hprod hbound (fun _ hc hcdef G hG =>
      real_collapse_reconstructs M hM hP hU hPow hS hR hI hRM hc hcdef
        hne hreal I hIR ρ hρ hza G hG)

end OAI.TuringRigidity.ConeForcingDescent
