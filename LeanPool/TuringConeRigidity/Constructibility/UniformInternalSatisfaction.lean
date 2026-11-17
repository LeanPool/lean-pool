/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/UniformInternalSatisfaction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.UniformTruthRecursion
public import LeanPool.TuringConeRigidity.Syntax.SatisfactionCertificateBound

/-!
# Uniform Internal Satisfaction
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

variable {M : ZFSet.{u}}

def SatisfactionWitness (Q B G H A T z : ZFSet.{u}) : Prop :=
  ∃ c ∈ ZFSet.omega, ∃ t ∈ T, ∃ S ∈ H,
    TruthWitness Q B G A T c S ∧ ZFSet.pair c t ∈ S ∧ z = ZFSet.pair c t

theorem satisfactionWitness_definable (C : Context M) {Q B G H : ZFSet.{u}}
    (hQ : Q ∈ M) (hB : B ∈ M) (hG : G ∈ M) (hH : H ∈ M) (a T z : ℕ) :
    Definable M (fun e => SatisfactionWitness Q B G H (e a) (e T) (e z)) :=
  ((((truthWitness_definable C hQ hB hG (a+3) (T+3) 2 0).and
    ((defPairMem C 2 1 0).and (defOrderedPair C (z+3) 2 1))).existsParam hH).existsMem
      (T+1)).existsParam C.omega_mem

theorem satisfactionWitness_spec (Q B G H A z : ZFSet.{u})
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B)
    (hG : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ A) → tupleGraph v ∈ G)
    (hH : ∀ p : SentenceForm, finiteSatisfaction A (subformulas p) ∈ H) :
    SatisfactionWitness Q B G H A (tupleSpace A) z ↔ z ∈ satisfactionSet A := by
  constructor
  · rintro ⟨c,_,t,ht,S,_,hw,hs,rfl⟩
    obtain ⟨p,rfl,hr⟩ := (truthWitness_spec Q B G A c S hQ hB hG).mp hw
    obtain ⟨n,v,hv,rfl⟩ := (mem_tupleSpace A t).mp ht
    have he := hr.unique (finiteSatisfaction_recursion A p)
    rw [he] at hs
    exact (finiteSatisfaction_covers A p v hv).mp hs
  · intro hz
    obtain ⟨⟨⟨n,p,w⟩,hb,hp⟩,rfl⟩ := ZFSet.mem_range.mp hz
    let v : Fin n → ZFSet.{u} := fun i => label A (w i)
    have hv : ∀ i, v i ∈ A := fun i => label_mem A (w i)
    refine ⟨_,(mem_omega _).mpr ⟨Encodable.encode p,rfl⟩,
      tupleCode v,(mem_tupleSpace A _).mpr ⟨n,v,hv,rfl⟩,
      finiteSatisfaction A (subformulas p),hH p,?_,?_,rfl⟩
    · exact (truthWitness_spec Q B G A _ _ hQ hB hG).mpr
        ⟨p,rfl,finiteSatisfaction_recursion A p⟩
    · exact (certificate_correct A p p (self_mem_subformulas p) v hv hb).mpr hp

theorem satisfactionSet_mem (M A : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) : satisfactionSet A ∈ M := by
  let C : Context M :=
    ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  obtain ⟨Q,hQ,_,hf⟩ := internal_family_bound M hM C.pairing C.union C.power C.omega_mem
  obtain ⟨B,hB,hb⟩ := internal_support_bound C
  obtain ⟨G,hG,hg⟩ := internal_tuple_graph_bound C hA
  obtain ⟨H,hH,_,hh⟩ := internal_certificate_bound M A hM hT hA
  have ht := tupleSpace_mem M A hM hT hA
  let e := cons A (cons (tupleSpace A) (fun _ => ZFSet.omega))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    · exact hA
    · exact ht
    · exact C.omega_mem
  have hd := satisfactionWitness_definable C hQ hB hG hH 1 2 0
  have hs := hd.sep_mem C e he (C.prod_mem C.omega_mem ht)
  have heq : (ZFSet.prod ZFSet.omega (tupleSpace A)).sep
      (fun z => SatisfactionWitness Q B G H A (tupleSpace A) z) = satisfactionSet A := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,satisfactionWitness_spec Q B G H A z hf hb hg (fun p => hh (subformulas p))]
    exact ⟨And.right,fun hz => ⟨satisfactionSet_subset_product A hz,hz⟩⟩
  exact heq ▸ hs

theorem satisfactionMembership_definable (M A : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (c t : ℕ) :
    Definable M (fun e => ZFSet.pair (e c) (e t) ∈ satisfactionSet A) :=
  pairMem_param (satisfactionSet_mem M A hM hT hA) c t

end TuringRigidity.RelativeConstructible

end OAI
