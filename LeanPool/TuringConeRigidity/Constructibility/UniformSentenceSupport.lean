/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/UniformSentenceSupport.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.SentenceSupportFormula

/-!
# Uniform Sentence Support
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.SentenceCoding
open ElementaryModel RelativeConstructible BoundedSetTheory TransitiveNameModel
open BoundedDefinability SetModelFunctions
universe u

variable {M : ZFSet.{u}}

theorem leastFamily_param (C : Context M) {Q : ZFSet.{u}} (hQ : Q ∈ M) (c s : ℕ) :
    Definable M (fun e => LeastFamily Q (e c) (e s)) := by
  have hs : ({Q} : ZFSet.{u}) ∈ M := singleton_mem M C.transitive C.pairing hQ
  exact (((equal_param hQ 0).and (leastFamily_definable C 0 (c+1) (s+1))).existsParam hs).congr
    (fun e => by simp only [ZFSet.mem_singleton,cons_zero,cons_succ]; simp)

def BoundWitness (Q B c b : ZFSet.{u}) : Prop :=
  ∃ F ∈ Q, ∃ G ∈ B, LeastFamily Q c F ∧ SetSupportRecursion F G ∧ ZFSet.pair c b ∈ G

theorem boundWitness_definable (C : Context M) {Q B : ZFSet.{u}}
    (hQ : Q ∈ M) (hB : B ∈ M) (c b : ℕ) :
    Definable M (fun e => BoundWitness Q B (e c) (e b)) :=
  (((leastFamily_param C hQ (c+2) 1).and ((setSupportRecursion_definable C 1 0).and
    (defPairMem C (c+2) (b+2) 0))).existsParam hB).existsParam hQ

theorem boundWitness_spec (Q B c b : ZFSet.{u})
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B) :
    BoundWitness Q B c b ↔
      ∃ p : SentenceForm, c = natSet (Encodable.encode p) ∧ b = natSet p.bound := by
  constructor
  · rintro ⟨F,_,G,_,hf,hg,hcb⟩
    obtain ⟨p,rfl⟩ := setClosed_valid F hf.2.1 c hf.1
    have hF := (leastFamily_spec Q F p (hQ p)).mp hf
    subst F
    have hG := ((setSupportRecursion_spec p G).mp hg).unique
    rw [hG] at hcb
    obtain ⟨q,_,he⟩ := (mem_supportGraph p _).mp hcb
    obtain ⟨hc,hb⟩ := ZFSet.pair_inj.mp he
    have hpq : p = q := Encodable.encode_injective (natSet_injective hc)
    subst q
    exact ⟨p,rfl,hb⟩
  · rintro ⟨p,rfl,rfl⟩
    exact ⟨family p,hQ p,supportGraph p,hB p,
      (leastFamily_spec Q (family p) p (hQ p)).mpr rfl,
      (setSupportRecursion_spec p _).mpr (supportGraph_recursion p),
      (supportGraph_bound p p p.bound).mpr ⟨self_mem_subformulas p,rfl⟩⟩

theorem internal_support_bound (C : Context M) :
    ∃ B ∈ M, ∀ p : SentenceForm, supportGraph p ∈ B := by
  obtain ⟨B,hB,hdef⟩ := internal_power M C.transitive C.power (C.prod_mem C.omega_mem C.omega_mem)
  exact ⟨B,hB,fun p => (hdef _).mpr
    ⟨supportGraph_mem M C.transitive C.pairing C.union C.omega_mem p,supportGraph_subset p⟩⟩

theorem uniform_support_definition (C : Context M) :
    ∃ p : Formula, ∃ d : ℕ → ZFSet.{u}, (∀ i, d i ∈ M) ∧
      ∀ c b, p.Eval (mix (cons c (fun _ => b)) d) ↔
        ∃ root : SentenceForm, c = natSet (Encodable.encode root) ∧ b = natSet root.bound := by
  obtain ⟨Q,hQ,_,hf⟩ := internal_family_bound M C.transitive C.pairing C.union C.power C.omega_mem
  obtain ⟨B,hB,hb⟩ := internal_support_bound C
  obtain ⟨p,d,hd,hdef⟩ := boundWitness_definable C hQ hB 0 1
  exact ⟨p,d,hd,fun c b => (hdef _).trans (boundWitness_spec Q B c b hf hb)⟩

end TuringRigidity.SentenceCoding

end OAI
