/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/ContextDefinablePower.lean.
Also incorporates the shared Context definability proof from upstream
OAI/Computability/DegreeRigidity/Constructibility/ContextHierarchyGraph.lean
under the same Apache-2.0 terms.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.DefSystemCertificate
public import LeanPool.TuringConeRigidity.SetModels.InternalDefinablePower
public import LeanPool.TuringConeRigidity.Syntax.SigmaParameterized

/-!
# Context Definable Power
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem tupleSpace_mem_of_context (M A : ZFSet.{u}) (C : Context M) (hA : A ∈ M) : tupleSpace A ∈
  M := by
  exact tupleSpace_mem_of_axioms M A C.transitive C.pairing C.union C.power C.separation
    C.omega_mem hA

theorem truthSlice_mem_of_context (M A : ZFSet.{u}) (C : Context M) (hA : A ∈ M) (p :
  SentenceForm) : truthSlice A p ∈ M := by
  exact truthSlice_mem_of_axioms M A C.transitive C.pairing C.union C.power C.separation
    C.omega_mem hA p

theorem finiteSatisfaction_mem_of_context (M A : ZFSet.{u}) (C : Context M) (hA : A ∈ M) (ps :
  List SentenceForm) : finiteSatisfaction A ps ∈ M := by
  exact finiteSatisfaction_mem_of_axioms M A C.transitive C.pairing C.union C.power C.separation
    C.omega_mem hA ps

theorem internal_certificate_bound_of_context (M A : ZFSet.{u}) (C : Context M) (hA : A ∈ M) :
    ∃ Q ∈ M,
      (∀ S, S ∈ Q ↔ S ∈ M ∧ S ⊆ ZFSet.prod ZFSet.omega (tupleSpace A)) ∧
      ∀ ps : List SentenceForm, finiteSatisfaction A ps ∈ Q := by
  exact internal_certificate_bound_of_axioms M A C.transitive C.pairing C.union C.power
    C.separation C.omega_mem hA

theorem satisfactionSet_mem_of_context (M A : ZFSet.{u}) (C : Context M) (hA : A ∈ M) :
  satisfactionSet A ∈ M := by
  exact satisfactionSet_mem_in_context M A C hA

theorem definablePower_mem_of_context (M A : ZFSet.{u}) (C : Context M) (hA : A ∈ M) :
  definablePower A ∈ M := by
  exact definablePower_mem_in_context M A C hA

theorem internal_defSystem_of_context (M : ZFSet.{u}) (C : Context M)
    (Q B A : ZFSet.{u}) (hA : A ∈ M)
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B) :
    ∃ G ∈ M, ∃ T ∈ M, ∃ H ∈ M, ∃ Z ∈ M,
      DefSystem Q B A G T H Z (definablePower A) := by
  exact internal_defSystem_in_context M C Q B A hA hQ hB

/-- Definable power is sigma definable under the bounded model Context alone. -/
theorem definablePower_sigmaDefinable_of_context (M : ZFSet.{u}) (C : Context M) :
    SigmaDefinable M (fun e => e 0 = definablePower (e 1)) := by
  obtain ⟨Q,hQ,_,hq⟩ := internal_family_bound M C.transitive C.pairing C.union C.power C.omega_mem
  obtain ⟨B,hB,hb⟩ := internal_support_bound C
  have hc := (defSystem_definable C hQ hB 5 3 2 1 0 4).toSigma C.transitive
  have hs := hc.existsSet.existsSet.existsSet.existsSet
  apply hs.congr
  intro e he
  change (∃ G ∈ M, ∃ T ∈ M, ∃ H ∈ M, ∃ Z ∈ M,
    DefSystem Q B (e 1) G T H Z (e 0)) ↔ e 0 = definablePower (e 1)
  constructor
  · rintro ⟨G,_,T,_,H,_,Z,_,h⟩
    exact h.exact hq hb
  · intro h
    rw [h]
    exact internal_defSystem_of_context M C Q B (e 1) (he 1) hq hb

end TuringRigidity.RelativeConstructible

end OAI
