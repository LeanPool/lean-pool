/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalDefinablePower.lean.
Also shares the bounded Context proof from upstream
OAI/Computability/DegreeRigidity/Constructibility/ContextDefinablePower.lean
under the same OpenAI Apache-2.0 attribution.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.DefinableSubsetCertificates
public import LeanPool.TuringConeRigidity.Constructibility.UniformInternalSatisfaction

/-!
# Internal Definable Power
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

/-- The bounded Context suffices for this closure construction. -/
theorem definablePower_mem_in_context (M A : ZFSet.{u}) (C : SetModelFunctions.Context M) (hA :
    A ∈ M) :
  definablePower A ∈ M := by
  obtain ⟨Q,hQ,_,hf⟩ := internal_family_bound M C.transitive C.pairing C.union C.power C.omega_mem
  obtain ⟨B,hB,hb⟩ := internal_support_bound C
  obtain ⟨G,hG,hg⟩ := internal_tuple_graph_bound C hA
  have ht := tupleSpace_mem_of_axioms M A C.transitive C.pairing C.union C.power C.separation
    C.omega_mem hA
  have hz := satisfactionSet_mem_in_context M A C hA
  obtain ⟨P,hP,_,hsub⟩ := definablePower_internal_bound M A C.transitive C.separation C.power hA
  let e := cons A (cons (tupleSpace A) (cons (satisfactionSet A) (fun _ => ZFSet.omega)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|i
    · exact hA
    · exact ht
    · exact hz
    · exact C.omega_mem
  have hd := definitionWitness_definable C hQ hB hG 1 2 3 0
  have hs := hd.sep_mem C e he hP
  have heq : P.sep (fun S => DefinitionWitness Q B G A (tupleSpace A) (satisfactionSet A) S) =
      definablePower A := by
    apply ZFSet.ext; intro S
    rw [ZFSet.mem_sep,definitionWitness_spec Q B G A S hf hb hg,← mem_definablePower]
    exact ⟨And.right,fun h => ⟨hsub h,h⟩⟩
  exact heq ▸ hs


theorem definablePower_mem (M A : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) : definablePower A ∈ M := by
  let C : SetModelFunctions.Context M :=
    ⟨hM, hT.pairing, hT.union, hT.powerSet, hT.separation.finitePrefix.bounded, hT.infinity⟩
  exact definablePower_mem_in_context M A C hA

theorem internal_definable_successor (M A : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) :
    ∃ D ∈ M, (∀ S, S ∈ D ↔ DefinableOver A S) ∧
      ∀ E, (∀ S, S ∈ E ↔ DefinableOver A S) → E = D := by
  refine ⟨definablePower A,definablePower_mem M A hM hT hA,mem_definablePower A,?_⟩
  intro E hE
  exact ZFSet.ext (fun S => (hE S).trans (mem_definablePower A S).symm)

end TuringRigidity.RelativeConstructible

end OAI
