/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/ConstructionDefinition.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.RelativeConstruction
public import LeanPool.TuringConeRigidity.Constructibility.ConstructibleSuccessorCode

/-!
# Construction Definition
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory ElementaryModel
universe u

theorem Construction.value_mem (t : Construction.{u}) (M R : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (hR : R ∈ M) (P : Oracle)
    (ht : t.Certified R P) (hi : t.Indexed M) : t.value R P ∈ M :=
  (t.value_in_relativeModel M R hM hT P ht hi).mem_ground hM hT hR

theorem Construction.define_record (R : ZFSet.{u}) (P : Oracle)
    (o : Ordinal.{u}) (n : ℕ) (p : SentenceForm) (c : Fin n → Construction.{u})
    (ht : (Construction.define o n p c).Certified R P) (x : ZFSet.{u}) :
    x ∈ (Construction.define o n p c).value R P ↔ x ∈ level R o ∧
      ZFSet.pair (natSet (Encodable.encode p))
        (tupleCode (Fin.cases x (fun i => (c i).value R (realPart P i)))) ∈
          satisfactionSet (level R o) :=
  definedSubset_record _ x p _ (fun i => (ht.2 i).2) ht.1

theorem Construction.define_satisfaction_mem (M R : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (hR : R ∈ M)
    (o : Ordinal.{u}) (n : ℕ) (p : SentenceForm) (c : Fin n → Construction.{u})
    (hi : (Construction.define o n p c).Indexed M) :
    satisfactionSet (level R o) ∈ M :=
  satisfactionSet_mem M _ hM hT (level_mem M R hM hT hR o hi.1)

theorem construction_definition_of_relativeModel (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (x : ZFSet.{u})
    (hx : x ∈ relativeModel M (groundReals M)) :
    ∃ (o : Ordinal.{u}) (n : ℕ) (p : SentenceForm)
      (c : Fin n → Construction.{u}) (P : Oracle),
      o.toZFSet ∈ M ∧ P ∈ modelReals M ∧
      (Construction.define o n p c).Indexed M ∧
      (Construction.define o n p c).Certified (groundReals M) P ∧
      satisfactionSet (level (groundReals M) o) ∈ M ∧
      ∀ z, z ∈ x ↔ z ∈ level (groundReals M) o ∧
        p.Sat (level (groundReals M) o : Set ZFSet)
          (cons z (tupleEnv (fun i => (c i).value (groundReals M) (realPart P i)))) := by
  obtain ⟨t,P,hP,hi,ht,he⟩ := construction_of_relativeModel M hM hT x hx
  obtain ⟨_,o,ho,hxo⟩ := ZFSet.mem_sep.mp hx
  let c : Fin 1 → Construction.{u} := fun _ => t
  let Q : Oracle := packedReal (fun _ : Fin 1 => P)
  have hpart (i : Fin 1) : realPart Q i = P := realPart_packed _ i
  have hcert : (Construction.define o 1 (.member 0 1) c).Certified (groundReals M) Q := by
    refine ⟨by decide,fun i => ?_⟩
    change t.Certified _ _ ∧ t.value _ _ ∈ _
    rw [hpart]
    exact ⟨ht,he.symm ▸ hxo⟩
  refine ⟨o,1,.member 0 1,c,Q,ho,packedReal_internal M hM hT _ (fun _ => hP),
    ⟨ho,fun _ => hi⟩,hcert,
    satisfactionSet_mem M _ hM hT (level_mem M _ hM hT (groundReals_mem M hM hT) o ho),?_⟩
  intro z
  have hv : tupleEnv (fun i : Fin 1 => (c i).value (groundReals M) (realPart Q i)) 0 = x := by
    rw [show (0 : ℕ) = (⟨0,by decide⟩ : Fin 1).val from rfl,tupleEnv_lt,hpart]
    exact he
  change z ∈ x ↔ z ∈ level (groundReals M) o ∧ z ∈ _
  simp only [cons_succ,hv]
  exact ⟨fun hz => ⟨level_transitive _ o x hxo z hz,hz⟩,And.right⟩

end TuringRigidity.RelativeConstructible

end OAI
