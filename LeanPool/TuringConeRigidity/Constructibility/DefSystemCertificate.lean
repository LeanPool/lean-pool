/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/DefSystemCertificate.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.SatisfactionSystemCertificate

/-!
# Def System Certificate
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

def DefSystem (Q B A G T H Z D : ZFSet.{u}) : Prop :=
  SatisfactionSystem Q B A G T H Z ∧
  (∀ S ∈ D, DefinitionWitness Q B G A T Z S) ∧
  ∀ c ∈ ZFSet.omega, ∀ t ∈ T, ParameterAdequate Q B G c t →
    ∃ S ∈ D, DefinesSubset A G T Z c t S

theorem defSystem_definable {M : ZFSet.{u}} (C : Context M)
    {Q B : ZFSet.{u}} (hQ : Q ∈ M) (hB : B ∈ M) (a G T H Z D : ℕ) :
    Definable M (fun e => DefSystem Q B (e a) (e G) (e T) (e H) (e Z) (e D)) := by
  have hn := defAllMem (definitionWitness_variable C hQ hB (a+1) (G+1) (T+1) (Z+1) 0) D
  have hc := defAllParam (defAllMem (defImp (parameterAdequate_variable C hQ hB (G+2) 1 0)
    ((definesSubset_variable C (a+3) (G+3) (T+3) (Z+3) 2 1 0).existsMem (D+2))) (T+1)) C.omega_mem
  exact (satisfactionSystem_definable C hQ hB a G T H Z).and (hn.and hc)

theorem DefSystem.exact {Q B A G T H Z D : ZFSet.{u}}
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B)
    (h : DefSystem Q B A G T H Z D) : D = definablePower A := by
  obtain ⟨ht,hz,hg,_⟩ := h.1.exact hQ hB
  subst T; subst Z
  apply ZFSet.ext; intro S
  rw [mem_definablePower]
  constructor
  · intro hS
    exact (definitionWitness_spec Q B G A S hQ hB hg).mp (h.2.1 S hS)
  · rintro ⟨n,p,v,hp,hv,rfl⟩
    obtain ⟨S,hS,hs⟩ := h.2.2 _ ((mem_omega _).mpr ⟨Encodable.encode p,rfl⟩)
      _ ((mem_tupleSpace A _).mpr ⟨n,v,hv,rfl⟩)
      ((parameterAdequate_spec Q B G _ hQ hB v (hg n v hv)).mpr ⟨p,rfl,hp⟩)
    exact (definesSubset_spec A G S hg p v hv hp).mp hs ▸ hS

theorem defSystem_canonical (Q B A G H : ZFSet.{u})
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B)
    (hG : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ A) → tupleGraph v ∈ G)
    (hH : ∀ p : SentenceForm, finiteSatisfaction A (subformulas p) ∈ H) :
    DefSystem Q B A G (tupleSpace A) H (satisfactionSet A) (definablePower A) := by
  refine ⟨satisfactionSystem_canonical Q B A G H hQ hB hG hH,?_,?_⟩
  · intro S hS
    exact (definitionWitness_spec Q B G A S hQ hB hG).mpr ((mem_definablePower A S).mp hS)
  · intro c _ t ht ha
    obtain ⟨n,v,hv,rfl⟩ := (mem_tupleSpace A t).mp ht
    obtain ⟨p,rfl,hp⟩ := (parameterAdequate_spec Q B G c hQ hB v (hG n v hv)).mp ha
    exact ⟨definedSubset A p v,(mem_definablePower A _).mpr ⟨n,p,v,hp,hv,rfl⟩,
      (definesSubset_spec A G _ hG p v hv hp).mpr rfl⟩

theorem internal_defSystem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (Q B A : ZFSet.{u}) (hA : A ∈ M)
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B) :
    ∃ G ∈ M, ∃ T ∈ M, ∃ H ∈ M, ∃ Z ∈ M,
      DefSystem Q B A G T H Z (definablePower A) := by
  let C : Context M :=
    ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  obtain ⟨G,hG,hg⟩ := internal_tuple_graph_bound C hA
  obtain ⟨H,hH,_,hh⟩ := internal_certificate_bound M A hM hT hA
  exact ⟨G,hG,tupleSpace A,tupleSpace_mem M A hM hT hA,H,hH,
    satisfactionSet A,satisfactionSet_mem M A hM hT hA,
    defSystem_canonical Q B A G H hQ hB hg (fun p => hh (subformulas p))⟩

end TuringRigidity.RelativeConstructible

end OAI
