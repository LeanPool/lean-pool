/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/DefinableSubsetCertificates.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.UniformInternalSatisfaction

/-!
# Definable Subset Certificates
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

variable {M : ZFSet.{u}}

def ParameterAdequate (Q B G c t : ZFSet.{u}) : Prop :=
  ∃ n ∈ ZFSet.omega, ∃ g ∈ G, ∃ b ∈ ZFSet.omega,
    t = ZFSet.pair n g ∧ BoundWitness Q B c b ∧ ∀ x ∈ b, x ∈ n ∨ x = n

theorem parameterAdequate_definable (C : Context M) {Q B G : ZFSet.{u}}
    (hQ : Q ∈ M) (hB : B ∈ M) (hG : G ∈ M) (c t : ℕ) :
    Definable M (fun e => ParameterAdequate Q B G (e c) (e t)) :=
  ((((defOrderedPair C (t+3) 2 1).and ((boundWitness_definable C hQ hB (c+3) 0).and
    (defAllMem (defOr (member_definable C 0 3) (equal_definable C 0 3)) 0))).existsParam
      C.omega_mem).existsParam hG).existsParam C.omega_mem

theorem parameterAdequate_spec (Q B G c : ZFSet.{u})
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hG : tupleGraph v ∈ G) :
    ParameterAdequate Q B G c (tupleCode v) ↔
      ∃ p : SentenceForm, c = natSet (Encodable.encode p) ∧ p.bound ≤ n+1 := by
  constructor
  · rintro ⟨m,_,g,_,b,_,he,hb,hle⟩
    have hm : m = natSet n := (ZFSet.pair_inj.mp he).1.symm
    obtain ⟨p,hp,rfl⟩ := (boundWitness_spec Q B c b hQ hB).mp hb
    refine ⟨p,hp,(natSet_subset_iff p.bound (n+1)).mp ?_⟩
    intro x hx
    have h := hle x hx
    rw [hm] at h
    exact ZFSet.mem_insert_iff.mpr h.symm
  · rintro ⟨p,rfl,hp⟩
    refine ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,tupleGraph v,hG,
      natSet p.bound,(mem_omega _).mpr ⟨p.bound,rfl⟩,rfl,
      (boundWitness_spec Q B _ _ hQ hB).mpr ⟨p,rfl,rfl⟩,?_⟩
    intro x hx
    have hs := (natSet_subset_iff p.bound (n+1)).mpr hp hx
    exact (ZFSet.mem_insert_iff.mp hs).symm

def DefinesSubset (A G T Z c t S : ZFSet.{u}) : Prop :=
  S ⊆ A ∧ ∀ x ∈ A, x ∈ S ↔
    ∃ s ∈ T, TuplePrefix A G t x s ∧ ZFSet.pair c s ∈ Z

theorem definesSubset_definable (C : Context M) {G : ZFSet.{u}}
    (hG : G ∈ M) (a T Z c t S : ℕ) :
    Definable M (fun e => DefinesSubset (e a) G (e T) (e Z) (e c) (e t) (e S)) :=
  (defSubset C S a).and (defAllMem (defIff (member_definable C 0 (S+1))
    (((tuplePrefix_definable C hG (a+2) (t+2) 1 0).and
      (defPairMem C (c+2) 0 (Z+2))).existsMem (T+1))) a)

theorem definesSubset_spec (A G S : ZFSet.{u})
    (hG : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ A) → tupleGraph v ∈ G)
    (p : SentenceForm) {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A)
    (hb : p.bound ≤ n + 1) :
    DefinesSubset A G (tupleSpace A) (satisfactionSet A)
      (natSet (Encodable.encode p)) (tupleCode v) S ↔ S = definedSubset A p v := by
  have hstep (x : ZFSet.{u}) (hx : x ∈ A) :
      (∃ s ∈ tupleSpace A, TuplePrefix A G (tupleCode v) x s ∧
        ZFSet.pair (natSet (Encodable.encode p)) s ∈ satisfactionSet A) ↔
      p.Sat (A : Set ZFSet) (cons x (tupleEnv v)) := by
    let w : Fin (n+1) → ZFSet.{u} := Fin.cases (motive := fun _ => ZFSet.{u}) x v
    have hw : ∀ i : Fin (n+1), w i ∈ A := fun i => Fin.cases hx hv i
    have ht : tupleCode w ∈ tupleSpace A := (mem_tupleSpace A _).mpr ⟨n+1,w,hw,rfl⟩
    have he : tupleEnv w = cons x (tupleEnv v) := tupleEnv_cons x v
    constructor
    · rintro ⟨s,_,hs,hp⟩
      have hs' := (tuplePrefix_spec A G hG v hv x s hx).mp hs
      rw [hs'] at hp
      exact he ▸ (satisfactionSet_spec A p w hw hb).mp hp
    · intro hp
      refine ⟨tupleCode w,ht,(tuplePrefix_spec A G hG v hv x _ hx).mpr rfl,?_⟩
      exact (satisfactionSet_spec A p w hw hb).mpr (he ▸ hp)
  constructor
  · rintro ⟨hsub,hdef⟩
    apply ZFSet.ext; intro x
    rw [mem_definedSubset]
    exact ⟨fun hx => ⟨hsub hx,(hstep x (hsub hx)).mp ((hdef x (hsub hx)).mp hx)⟩,
      fun ⟨hx,hp⟩ => (hdef x hx).mpr ((hstep x hx).mpr hp)⟩
  · rintro rfl
    refine ⟨fun x hx => (mem_definedSubset A x p v).mp hx |>.1,?_⟩
    intro x hx
    rw [mem_definedSubset]
    exact (and_iff_right hx).trans (hstep x hx).symm

def DefinitionWitness (Q B G A T Z S : ZFSet.{u}) : Prop :=
  ∃ c ∈ ZFSet.omega, ∃ t ∈ T,
    ParameterAdequate Q B G c t ∧ DefinesSubset A G T Z c t S

theorem definitionWitness_definable (C : Context M) {Q B G : ZFSet.{u}}
    (hQ : Q ∈ M) (hB : B ∈ M) (hG : G ∈ M) (a T Z S : ℕ) :
    Definable M (fun e => DefinitionWitness Q B G (e a) (e T) (e Z) (e S)) :=
  (((parameterAdequate_definable C hQ hB hG 1 0).and
    (definesSubset_definable C hG (a+2) (T+2) (Z+2) 1 0 (S+2))).existsMem (T+1)).existsParam
      C.omega_mem

theorem definitionWitness_spec (Q B G A S : ZFSet.{u})
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B)
    (hG : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ A) → tupleGraph v ∈ G) :
    DefinitionWitness Q B G A (tupleSpace A) (satisfactionSet A) S ↔ DefinableOver A S := by
  constructor
  · rintro ⟨c,_,t,ht,ha,hd⟩
    obtain ⟨n,v,hv,rfl⟩ := (mem_tupleSpace A t).mp ht
    obtain ⟨p,rfl,hp⟩ := (parameterAdequate_spec Q B G c hQ hB v (hG n v hv)).mp ha
    exact ⟨n,p,v,hp,hv,(definesSubset_spec A G S hG p v hv hp).mp hd⟩
  · rintro ⟨n,p,v,hp,hv,rfl⟩
    exact ⟨_,(mem_omega _).mpr ⟨Encodable.encode p,rfl⟩,
      _,(mem_tupleSpace A _).mpr ⟨n,v,hv,rfl⟩,
      (parameterAdequate_spec Q B G _ hQ hB v (hG n v hv)).mpr ⟨p,rfl,hp⟩,
      (definesSubset_spec A G _ hG p v hv hp).mpr rfl⟩

end TuringRigidity.RelativeConstructible

end OAI
