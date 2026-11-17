/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/UniformTruthRecursion.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.UniformTruthStep

/-!
# Uniform Truth Recursion
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

variable {M : ZFSet.{u}}

/-- A set-coded truth relation obeys the recursive truth clauses on an adequate subformula
family. -/
def SetTruthRecursion (Q B G A T F S : ZFSet.{u}) : Prop :=
  (∀ z ∈ S, ∃ c ∈ F, ∃ t ∈ T, TupleAdequate Q B G c t ∧ z = ZFSet.pair c t) ∧
    ∀ c ∈ F, ∀ t ∈ T, TupleAdequate Q B G c t →
      (ZFSet.pair c t ∈ S ↔ SetTruthStep A G T S c t)

theorem setTruthRecursion_definable (C : Context M) {Q B G : ZFSet.{u}}
    (hQ : Q ∈ M) (hB : B ∈ M) (hG : G ∈ M) (a T f s : ℕ) :
    Definable M (fun e => SetTruthRecursion Q B G (e a) (e T) (e f) (e s)) := by
  have hn := defAllMem ((((tupleAdequate_definable C hQ hB hG 1 0).and
    (defOrderedPair C 2 1 0)).existsMem (T+2)).existsMem (f+1)) s
  have hr := defAllMem (defAllMem (defImp (tupleAdequate_definable C hQ hB hG 1 0)
    (defIff (defPairMem C 1 0 (s+2))
      (setTruthStep_definable C hG (a+2) (T+2) (s+2) 1 0))) (T+1)) f
  exact hn.and hr

theorem setTruthRecursion_spec (Q B G A S : ZFSet.{u})
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B)
    (hG : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ A) → tupleGraph v ∈ G)
    (root : SentenceForm) :
    SetTruthRecursion Q B G A (tupleSpace A) (family root) S ↔ TruthRecursion A root S := by
  constructor
  · rintro ⟨hn,hr⟩
    constructor
    · intro z hz
      obtain ⟨c,hc,t,ht,ha,rfl⟩ := hn z hz
      obtain ⟨p,hp,rfl⟩ := (mem_family root c).mp hc
      obtain ⟨n,v,hv,rfl⟩ := (mem_tupleSpace A t).mp ht
      exact ⟨p,hp,n,v,hv,(tupleAdequate_spec Q B G hQ hB p v (hG n v hv)).mp ha,rfl⟩
    · intro p hp n v hv hb
      have ht := (mem_tupleSpace A _).mpr ⟨n,v,hv,rfl⟩
      have ha := (tupleAdequate_spec Q B G hQ hB p v (hG n v hv)).mpr hb
      exact (hr _ ((code_mem_family root p).mpr hp) _ ht ha).trans
        (setTruthStep_encode A G S hG p v hv hb)
  · rintro ⟨hn,hr⟩
    constructor
    · intro z hz
      obtain ⟨p,hp,n,v,hv,hb,rfl⟩ := hn z hz
      exact ⟨_,(code_mem_family root p).mpr hp,_,(mem_tupleSpace A _).mpr ⟨n,v,hv,rfl⟩,
        (tupleAdequate_spec Q B G hQ hB p v (hG n v hv)).mpr hb,rfl⟩
    · intro c hc t ht ha
      obtain ⟨p,hp,rfl⟩ := (mem_family root c).mp hc
      obtain ⟨n,v,hv,rfl⟩ := (mem_tupleSpace A t).mp ht
      have hb := (tupleAdequate_spec Q B G hQ hB p v (hG n v hv)).mp ha
      exact (hr p hp n v hv hb).trans (setTruthStep_encode A G S hG p v hv hb).symm

/-- A truth relation on the least subformula family containing the formula code `c`. -/
def TruthWitness (Q B G A T c S : ZFSet.{u}) : Prop :=
  ∃ F ∈ Q, LeastFamily Q c F ∧ SetTruthRecursion Q B G A T F S

theorem truthWitness_definable (C : Context M) {Q B G : ZFSet.{u}}
    (hQ : Q ∈ M) (hB : B ∈ M) (hG : G ∈ M) (a T c s : ℕ) :
    Definable M (fun e => TruthWitness Q B G (e a) (e T) (e c) (e s)) :=
  ((leastFamily_param C hQ (c+1) 0).and
    (setTruthRecursion_definable C hQ hB hG (a+1) (T+1) 0 (s+1))).existsParam hQ

theorem truthWitness_spec (Q B G A c S : ZFSet.{u})
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B)
    (hG : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ A) → tupleGraph v ∈ G) :
    TruthWitness Q B G A (tupleSpace A) c S ↔
      ∃ root : SentenceForm, c = natSet (Encodable.encode root) ∧ TruthRecursion A root S := by
  constructor
  · rintro ⟨F,_,hf,hr⟩
    obtain ⟨root,rfl⟩ := setClosed_valid F hf.2.1 c hf.1
    have he := (leastFamily_spec Q F root (hQ root)).mp hf
    subst F
    exact ⟨root,rfl,(setTruthRecursion_spec Q B G A S hQ hB hG root).mp hr⟩
  · rintro ⟨root,rfl,hr⟩
    exact ⟨family root,hQ root,(leastFamily_spec Q _ root (hQ root)).mpr rfl,
      (setTruthRecursion_spec Q B G A S hQ hB hG root).mpr hr⟩

end TuringRigidity.RelativeConstructible

end OAI
