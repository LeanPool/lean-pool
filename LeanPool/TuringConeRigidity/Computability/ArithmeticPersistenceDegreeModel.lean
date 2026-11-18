/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticPersistenceDegreeModel.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.PersistenceExtensionAbsoluteness
public import LeanPool.TuringConeRigidity.Representation.SourceTModelBridge

/-!
# Arithmetic Persistence Degree Model
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel EncodedForcing PersistentRestrictions PersistentPresentation OracleJump
open ArithmeticTree ArithmeticPersistence
universe u

theorem sourceT_arithmetic_persistent_graph (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (S : ZFSet.{u}) (hSM : S ∈ M)
    (hS : ∀ A : Oracle, realCode A ∈ S ↔ A ∈ modelReals M)
    (hSd : ∀ x ∈ S, ∃ A : Oracle, realCode A = x)
    (A R : Oracle) (hA : A ∈ modelReals M) (hR : R ∈ modelReals M)
    (hp : ∀ H ∈ modelReals M, Base A R ∧ Matrix (parameters A R H) 0) :
    ∃ I : CountableIdeal, ∃ hAI : Presented I A, ∃ ρ : I ≃o I,
      (∀ v, R v = true ↔ Graph ρ hAI v) ∧ Persistent I ρ ∧
      presentationGraph S A R ∈ M ∧
      (LevySigma.persistent 0 1 2 3 4).Realize M
        (modelDegreeEnv S (presentationSet S A) (presentationGraph S A R)) := by
  obtain ⟨I,hAI,hz,ρ,hgraph,hpers⟩ := (sourceT_persistence_presentation M hM hT A R hA hR).mp hp
  have hc : ∀ n, realCode (columns A n) ∈ S :=
    fun n => (hS _).mpr (sourceT_real_column M hM hT hA n)
  have hbridge := sourceT_arbitrary_persistent_graph M hM hT S hSM hS hSd hAI hA ρ hpers hz
    (presentationGraph S A R) (fun _ h => (ZFSet.mem_sep.mp h).1)
    (presentationGraph_actual S hAI hc ρ hgraph)
  exact ⟨I,hAI,ρ,hgraph,hpers,hbridge⟩

theorem sourceT_presentation_transfer (M N : ZFSet.{u})
    (hM : Transitive M) (hN : Transitive N) (hTM : SourceT M) (hTN : SourceT N)
    (A R : Oracle) (hAM : A ∈ modelReals M) (hRM : R ∈ modelReals M)
    (hAN : A ∈ modelReals N) (hRN : R ∈ modelReals N)
    (hp : ∀ H ∈ modelReals M, Base A R ∧ Matrix (parameters A R H) 0) :
    ∃ S ∈ N, degreeUniverse S ∈ N ∧ degreeOrder S ∈ N ∧
      presentationGraph S A R ∈ N ∧
      (LevySigma.persistent 0 1 2 3 4).Realize N
        (modelDegreeEnv S (presentationSet S A) (presentationGraph S A R)) := by
  have hpN := (persistence_between_models M N hM hN hTM hTN A R hAM hRM hAN hRN).mp hp
  obtain ⟨S,hSN,hS,hSd⟩ := internal_real_power N hN hTN
  have hd : ∀ x ∈ S, ∃ B : Oracle, realCode B = x := by
    intro x hx; obtain ⟨B,_,hB⟩ := hSd x hx; exact ⟨B,hB⟩
  obtain ⟨_,_,_,_,_,hgraph,hpers⟩ := sourceT_arithmetic_persistent_graph N hN hTN S hSN hS hd A R
    hAN hRN hpN
  exact ⟨S,hSN,internal_degreeUniverse N hN hTN S hSN hd,
    internal_degreeOrder N hN hTN S hSN hd,hgraph,hpers⟩

theorem generic_extension_persistent_degree_model (M : ZFSet.{u}) (hM : Transitive M) (hT :
  SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)] (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : CountableForcing.GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G)
    (htop : ⊤ ∈ G.carrier) (A R : Oracle) (hA : A ∈ modelReals M) (hR : R ∈ modelReals M)
    (hp : ∀ H ∈ modelReals M, Base A R ∧ Matrix (parameters A R H) 0) :
    let E := genericExtensionSet M c G.carrier
    ∃ S ∈ E, degreeUniverse S ∈ E ∧ degreeOrder S ∈ E ∧
      presentationGraph S A R ∈ E ∧
      (LevySigma.persistent 0 1 2 3 4).Realize E
        (modelDegreeEnv S (presentationSet S A) (presentationGraph S A R)) := by
  have hi := ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier htop
  have hAE : A ∈ modelReals (genericExtensionSet M c G.carrier) := by
    change realCode A ∈ genericExtensionSet M c G.carrier
    exact hi hA
  have hRE : R ∈ modelReals (genericExtensionSet M c G.carrier) := by
    change realCode R ∈ genericExtensionSet M c G.carrier
    exact hi hR
  exact sourceT_presentation_transfer M _ hM (genericExtensionSet_transitive M c hM G.carrier)
    hT (extension_sourceT M hM hT hc hoM ho G hG htop) A R hA hR hAE hRE hp

end TuringRigidity.BoundedSetTheory

end OAI
