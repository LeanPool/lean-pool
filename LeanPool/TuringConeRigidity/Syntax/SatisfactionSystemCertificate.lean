/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/SatisfactionSystemCertificate.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.TupleSystemCertificate

/-!
# Satisfaction System Certificate
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

def SatisfactionSystem (Q B A G T H Z : ZFSet.{u}) : Prop :=
  TupleSystem A G T ∧
  (∀ c ∈ ZFSet.omega, ∀ F ∈ Q, LeastFamily Q c F →
    ∃ S ∈ H, SetTruthRecursion Q B G A T F S) ∧
  (∀ z ∈ Z, SatisfactionWitness Q B G H A T z) ∧
  ∀ c ∈ ZFSet.omega, ∀ t ∈ T, ∀ S ∈ H,
    TruthWitness Q B G A T c S → ZFSet.pair c t ∈ S → ZFSet.pair c t ∈ Z

theorem satisfactionSystem_definable {M : ZFSet.{u}} (C : Context M)
    {Q B : ZFSet.{u}} (hQ : Q ∈ M) (hB : B ∈ M) (a G T H Z : ℕ) :
    Definable M (fun e => SatisfactionSystem Q B (e a) (e G) (e T) (e H) (e Z)) := by
  have ht := defAllParam (defAllParam (defImp (leastFamily_param C hQ 1 0)
    ((setTruthRecursion_variable C hQ hB (a+3) (G+3) (T+3) 1 0).existsMem (H+2))) hQ) C.omega_mem
  have hn := defAllMem (satisfactionWitness_variable C hQ hB (a+1) (G+1) (H+1) (T+1) 0) Z
  have hc := defAllParam (defAllMem (defAllMem
    (defImp (truthWitness_variable C hQ hB (a+3) (G+3) (T+3) 2 0)
      (defImp (defPairMem C 2 1 0) (defPairMem C 2 1 (Z+3)))) (H+2)) (T+1)) C.omega_mem
  exact (tupleSystem_definable C a G T).and (ht.and (hn.and hc))

theorem SatisfactionSystem.exact {Q B A G T H Z : ZFSet.{u}}
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B)
    (h : SatisfactionSystem Q B A G T H Z) :
    T = tupleSpace A ∧ Z = satisfactionSet A ∧
      (∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ A) → tupleGraph v ∈ G) ∧
      ∀ p : SentenceForm, finiteSatisfaction A (subformulas p) ∈ H := by
  obtain ⟨ht,hg⟩ := h.1.exact
  subst T
  have hh (p : SentenceForm) : finiteSatisfaction A (subformulas p) ∈ H := by
    obtain ⟨S,hS,hs⟩ := h.2.1 _ ((mem_omega _).mpr ⟨Encodable.encode p,rfl⟩)
      (family p) (hQ p) ((leastFamily_spec Q _ p (hQ p)).mpr rfl)
    have he := ((setTruthRecursion_spec Q B G A S hQ hB hg p).mp hs).unique
      (finiteSatisfaction_recursion A p)
    exact he ▸ hS
  refine ⟨rfl,?_,hg,hh⟩
  apply ZFSet.ext; intro z
  rw [← satisfactionWitness_spec Q B G H A z hQ hB hg hh]
  constructor
  · exact h.2.2.1 z
  · rintro ⟨c,hc,t,ht,S,hS,hs,hct,rfl⟩
    exact h.2.2.2 c hc t ht S hS hs hct

theorem satisfactionSystem_canonical (Q B A G H : ZFSet.{u})
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B)
    (hG : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ A) → tupleGraph v ∈ G)
    (hH : ∀ p : SentenceForm, finiteSatisfaction A (subformulas p) ∈ H) :
    SatisfactionSystem Q B A G (tupleSpace A) H (satisfactionSet A) := by
  refine ⟨tupleSystem_canonical A G hG,?_,?_,?_⟩
  · intro c _ F _ hf
    obtain ⟨p,rfl⟩ := setClosed_valid F hf.2.1 c hf.1
    have he := (leastFamily_spec Q F p (hQ p)).mp hf
    subst F
    exact ⟨_,hH p,(setTruthRecursion_spec Q B G A _ hQ hB hG p).mpr
      (finiteSatisfaction_recursion A p)⟩
  · intro z hz
    exact (satisfactionWitness_spec Q B G H A z hQ hB hG hH).mpr hz
  · intro c hc t ht S hS hs hct
    exact (satisfactionWitness_spec Q B G H A _ hQ hB hG hH).mp
      ⟨c,hc,t,ht,S,hS,hs,hct,rfl⟩

end TuringRigidity.RelativeConstructible

end OAI
