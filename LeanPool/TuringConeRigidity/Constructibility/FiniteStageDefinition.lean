/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/FiniteStageDefinition.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.SingleRealConstruction

/-!
# Finite Stage Definition
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelArithmetic
universe u

/-- The ordinal associated with a construction input, when the input is an ordinal stage. -/
noncomputable def Construction.ordinalData (t : Construction.{u}) (k : ℕ) : Option Ordinal.{u} :=
  match t.inputData k with
  | .stage o => some o
  | _ => none

/-- Interpret an optional stage parameter as the corresponding level, or as the real set when
absent. -/
noncomputable def stageParameter (R : ZFSet.{u}) : Option Ordinal.{u} → ZFSet.{u}
  | none => R
  | some o => level R o

theorem Construction.stageInputs_eq (t : Construction.{u}) (R : ZFSet.{u}) (k : ℕ) :
    t.stageInputs R k = stageParameter R (t.ordinalData k) := by
  unfold Construction.stageInputs Construction.ordinalData
  cases t.inputData k <;> rfl

theorem Construction.ordinalData_mem (t : Construction.{u}) (M : ZFSet.{u})
    (hi : t.Indexed M) (k : ℕ) (o : Ordinal.{u}) (ho : t.ordinalData k = some o) :
    o.toZFSet ∈ M := by
  have hk := t.inputData_indexed M hi k
  unfold Construction.ordinalData at ho
  cases hd : t.inputData k with
  | reals => simp [hd] at ho
  | realPath path => simp [hd] at ho
  | stage a =>
    rw [hd] at hk
    simp only [hd] at ho
    have he : a = o := Option.some.inj ho
    exact he ▸ hk

theorem Construction.finite_stage_definition (t : Construction.{u}) :
    ∃ (n : ℕ) (p : SentenceForm) (o : Fin n → Option Ordinal.{u}),
      p.bound ≤ n+6 ∧
      ∀ (M R : ZFSet.{u}) (_hM : Transitive M) (_hT : SourceT M) (_hR : R ∈ M)
        (P : Oracle) (_hP : P ∈ modelReals M) (_ht : t.Certified R P) (_hi : t.Indexed M),
        (∀ i a, o i = some a → a.toZFSet ∈ M) ∧
        (∀ i, stageParameter R (o i) ∈ M) ∧
        ∀ z ∈ M, p.Sat (M : Set ZFSet)
          (cons z (cons R (cons (realCode P) (cons ZFSet.omega (cons additionSet
            (cons pairNumbers (tupleEnv (fun i => stageParameter R (o i))))))))) ↔
          z ∈ t.value R P := by
  let p := t.singleMembership
  refine ⟨p.bound,p,fun i => t.ordinalData i,by omega,?_⟩
  intro M R hM hT hR P hP ht hi
  refine ⟨fun i a ha => t.ordinalData_mem M hi i a ha,?_,?_⟩
  · intro i
    rw [← t.stageInputs_eq]
    exact t.stageInputs_mem M R hM hT hR hi i
  · intro z hz
    have hf : p.Sat (M : Set ZFSet)
        (cons z (cons R (cons (realCode P) (cons ZFSet.omega (cons additionSet
          (cons pairNumbers (tupleEnv (fun i : Fin p.bound => stageParameter R (t.ordinalData
            i))))))))) ↔
        p.Sat (M : Set ZFSet) (cons z (t.singleInputs R P)) := by
      apply p.finite_support
      intro i hin
      rcases i with _|_|_|_|_|_|i <;> simp only [Construction.singleInputs,cons_zero,cons_succ]
      rw [tupleEnv,dite_eq_left (show i < p.bound by omega)]
      exact (t.stageInputs_eq R i).symm
    exact hf.trans (t.singleMembership_spec M R hM hT hR P hP ht hi z hz)

end TuringRigidity.RelativeConstructible

end OAI
