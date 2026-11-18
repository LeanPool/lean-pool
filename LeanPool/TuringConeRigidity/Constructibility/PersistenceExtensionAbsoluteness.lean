/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/PersistenceExtensionAbsoluteness.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.PiOneOneSatisfaction

/-!
# Persistence Extension Absoluteness
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ArithmeticTree
open UniformArithmetic BoundedSetTheory TransitiveNameModel ArithmeticPersistence
universe u

theorem arithmetic_real_between_models (M N : ZFSet.{u})
    (hM : Transitive M) (hN : Transitive N) (hTM : SourceT M) (hTN : SourceT N)
    {Q : Predicate} (hQ : Arith Q) (A R : Oracle)
    (hAM : A ∈ modelReals M) (hRM : R ∈ modelReals M)
    (hAN : A ∈ modelReals N) (hRN : R ∈ modelReals N) (v : ℕ) :
    (∀ H ∈ modelReals M, Q (parameters A R H) v) ↔
      ∀ H ∈ modelReals N, Q (parameters A R H) v :=
  (sourceT_forall_arithmetic_real M hM hTM hQ A R hAM hRM v).trans
    (sourceT_forall_arithmetic_real N hN hTN hQ A R hAN hRN v).symm

theorem persistence_between_models (M N : ZFSet.{u})
    (hM : Transitive M) (hN : Transitive N) (hTM : SourceT M) (hTN : SourceT N)
    (A R : Oracle) (hAM : A ∈ modelReals M) (hRM : R ∈ modelReals M)
    (hAN : A ∈ modelReals N) (hRN : R ∈ modelReals N) :
    (∀ H ∈ modelReals M, Base A R ∧ Matrix (parameters A R H) 0) ↔
      ∀ H ∈ modelReals N, Base A R ∧ Matrix (parameters A R H) 0 :=
  (sourceT_persistence_presentation M hM hTM A R hAM hRM).trans
    (sourceT_persistence_presentation N hN hTN A R hAN hRN).symm

theorem persistence_in_generic_extension (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)] (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : CountableForcing.GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G)
    (htop : ⊤ ∈ G.carrier) (A R : Oracle) (hA : A ∈ modelReals M) (hR : R ∈ modelReals M) :
    (∀ H ∈ modelReals M, Base A R ∧ Matrix (parameters A R H) 0) ↔
      ∀ H ∈ modelReals (genericExtensionSet M c G.carrier),
        Base A R ∧ Matrix (parameters A R H) 0 := by
  have hi := ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier htop
  have hAE : A ∈ modelReals (genericExtensionSet M c G.carrier) := by
    change realCode A ∈ genericExtensionSet M c G.carrier
    exact hi hA
  have hRE : R ∈ modelReals (genericExtensionSet M c G.carrier) := by
    change realCode R ∈ genericExtensionSet M c G.carrier
    exact hi hR
  exact persistence_between_models M _ hM (genericExtensionSet_transitive M c hM G.carrier)
    hT (extension_sourceT M hM hT hc hoM ho G hG htop) A R hA hR hAE hRE

theorem piOneOne_formula {P : Oracle → Oracle → Prop} (hp : PiOneOne P) :
    ∃ φ : Formula, ∀ M : ZFSet.{u}, Transitive M → SourceT M →
      ∃ S Q : ZFSet.{u}, S ∈ M ∧ Q ∈ M ∧
        ∀ A R : Oracle, A ∈ modelReals M → R ∈ modelReals M →
          ((Formula.piOneOneMatrix φ).Realize M (piOneOneEnv S Q A R 0) ↔ P A R) := by
  obtain ⟨P',hP,hiff⟩ := hp
  obtain ⟨φ,hφ⟩ := arithmetic_bounded_definition.{u} hP
  refine ⟨φ,fun M hM hT => ?_⟩
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded (sourceT_omega_mem M hM hT)
  obtain ⟨S,hSM,hS,hSd⟩ := internal_real_power M hM hT
  have hd : ∀ x ∈ S, ∃ H : Oracle, realCode H = x := by
    intro x hx; obtain ⟨H,_,hH⟩ := hSd x hx; exact ⟨H,hH⟩
  exact ⟨S,Q,hSM,hQM,fun A R hA hR =>
    (sourceT_piOneOne_satisfaction M hM hT hφ hP S Q hSM hQM hS hd hQ A R hA hR 0).trans
      (hiff A R).symm⟩

theorem nonidentity_presentation_formula :
    ∃ φ : Formula, ∀ M : ZFSet.{u}, Transitive M → SourceT M →
      ∃ S Q : ZFSet.{u}, S ∈ M ∧ Q ∈ M ∧
        ∀ A R : Oracle, A ∈ modelReals M → R ∈ modelReals M →
          ((Formula.piOneOneMatrix φ).Realize M (piOneOneEnv S Q A R 0) ↔
            Property A R ∧ Moved A R) := piOneOne_formula nonidentity_piOneOne

end TuringRigidity.ArithmeticTree

end OAI
