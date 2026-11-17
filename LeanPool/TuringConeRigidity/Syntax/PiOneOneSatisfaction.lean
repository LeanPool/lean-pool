/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/PiOneOneSatisfaction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.SourceTArithmeticAbsoluteness
public import LeanPool.TuringConeRigidity.Computability.ArithmeticParameterFormula

/-!
# Pi One One Satisfaction
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel UniformArithmetic ArithmeticPersistence ArithmeticTree
universe u

namespace Formula

/-- Bounded formula universally testing the arithmetic matrix over the supplied real-code
family. -/
def piOneOneMatrix (φ : Formula) : Formula :=
  allMem 0 (oracleParameters φ 2 3 4 (fun i => match i with | 0 => 5 | 1 => 6 | _+2 => 0))
end Formula

/-- The parameter environment for the universally quantified arithmetic predicate matrix. -/
noncomputable def piOneOneEnv (S Q : ZFSet.{u}) (A R : Oracle) (v : ℕ) : ℕ → ZFSet.{u} :=
  cons S (cons ZFSet.omega (cons Q (cons (natSet v) (cons (realCode A) (fun _ => realCode R)))))

theorem eval_piOneOneMatrix {φ : Formula} {P : Predicate} (hφ : DefinesArithmetic.{u} φ P)
    (S Q : ZFSet.{u}) (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ Q)
    (hS : ∀ x ∈ S, ∃ H : Oracle, realCode H = x) (A R : Oracle) (v : ℕ) :
    (Formula.piOneOneMatrix φ).Eval (piOneOneEnv S Q A R v) ↔
      ∀ H : Oracle, realCode H ∈ S → P (parameters A R H) v := by
  simp only [Formula.piOneOneMatrix,Formula.eval_allMem]
  have he (H : Oracle) :
      (Formula.oracleParameters φ 2 3 4 (fun i => match i with | 0 => 5 | 1 => 6 | _+2 => 0)).Eval
        (cons (realCode H) (piOneOneEnv S Q A R v)) ↔ P (parameters A R H) v := by
    apply Formula.oracleParameters_spec hφ 2 3 4 _ _ rfl hQ _ _ v rfl
    intro i
    rcases i with _ | i
    · rfl
    rcases i with _|i <;> rfl
  constructor
  · intro h H hH
    exact (he H).mp (h (realCode H) hH)
  · intro h x hx
    obtain ⟨H,rfl⟩ := hS x hx
    exact (he H).mpr (h H hx)

theorem sourceT_piOneOne_satisfaction (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {φ : Formula} {P : Predicate} (hφ : DefinesArithmetic.{u} φ P) (hP : Arith P)
    (S Q : ZFSet.{u}) (hSM : S ∈ M) (hQM : Q ∈ M)
    (hS : ∀ H : Oracle, realCode H ∈ S ↔ H ∈ modelReals M)
    (hSd : ∀ x ∈ S, ∃ H : Oracle, realCode H = x)
    (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ Q)
    (A R : Oracle) (hA : A ∈ modelReals M) (hR : R ∈ modelReals M) (v : ℕ) :
    (Formula.piOneOneMatrix φ).Realize M (piOneOneEnv S Q A R v) ↔
      ∀ H : Oracle, P (parameters A R H) v := by
  have hω := sourceT_omega_mem M hM hT
  have he : ∀ i, piOneOneEnv S Q A R v i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hSM
    rcases i with _ | i
    · exact hω
    rcases i with _ | i
    · exact hQM
    rcases i with _ | i
    · exact hM _ hω _ ((mem_omega _).mpr ⟨v,rfl⟩)
    rcases i with _ | i
    · exact hA
    exact hR
  rw [Formula.absolute _ M hM _ he,eval_piOneOneMatrix hφ S Q hQ hSd A R v]
  simp only [hS]
  exact sourceT_forall_arithmetic_real M hM hT hP A R hA hR v

theorem sourceT_persistence_formula : ∃ φ : Formula, ∀ M : ZFSet.{u},
    Transitive M → SourceT M → ∃ S Q : ZFSet.{u}, S ∈ M ∧ Q ∈ M ∧
      ∀ A R : Oracle, A ∈ modelReals M → R ∈ modelReals M →
        ((Formula.piOneOneMatrix φ).Realize M (piOneOneEnv S Q A R 0) ↔ Property A R) := by
  obtain ⟨P,hP,hiff⟩ := source_4_2_1
  obtain ⟨φ,hφ⟩ := arithmetic_bounded_definition.{u} hP
  refine ⟨φ,fun M hM hT => ?_⟩
  have hS := hT.separation.finitePrefix.bounded
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union hT.powerSet hS
    (sourceT_omega_mem M hM hT)
  obtain ⟨S,hSM,hS,hSd⟩ := internal_real_power M hM hT
  have hd : ∀ x ∈ S, ∃ H : Oracle, realCode H = x := by
    intro x hx; obtain ⟨H,_,hH⟩ := hSd x hx; exact ⟨H,hH⟩
  exact ⟨S,Q,hSM,hQM,fun A R hA hR =>
    (sourceT_piOneOne_satisfaction M hM hT hφ hP S Q hSM hQM hS hd hQ A R hA hR 0).trans
      (hiff A R).symm⟩

end TuringRigidity.BoundedSetTheory

end OAI
