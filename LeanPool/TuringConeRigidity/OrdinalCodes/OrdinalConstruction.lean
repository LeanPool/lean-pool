/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalConstruction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalInputSyntax
public import LeanPool.TuringConeRigidity.Constructibility.FiniteDefinitionTransfer
public import LeanPool.TuringConeRigidity.Constructibility.ParameterFreeOrdinalStage
public import LeanPool.TuringConeRigidity.OrdinalCodes.LevelInlinedDefinition

/-!
# Ordinal Construction
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u
attribute [local irreducible] Construction.ownRealsMembership SentenceForm.bound

theorem Construction.ordinal_definition (t : Construction.{u}) :
    ∃ q : SentenceForm, ∀ M : ZFSet.{u}, Transitive M → SourceT M →
      ∀ P : Oracle, P ∈ modelReals M → t.Certified (groundReals M) P → t.Indexed M →
        ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧
          ∀ δ : Ordinal.{u}, δ.toZFSet ∈ M → γ ≤ δ →
            t.value (groundReals M) P ∈ level (groundReals M) δ ∧
            (∀ i, t.ordinalInputs P i ∈ level (groundReals M) δ) ∧
            ∀ z ∈ level (groundReals M) δ,
              q.Sat (level (groundReals M) δ : Set ZFSet) (cons z (t.ordinalInputs P)) ↔
                z ∈ t.value (groundReals M) P := by
  classical
  obtain ⟨p,hp⟩ := parameter_free_ordinal_stage.{u}
  refine ⟨t.ordinalMembership p,?_⟩
  intro M hM hT P hP ht hi
  let R := groundReals M
  let n := t.ownRealsMembership.bound
  obtain ⟨α,hα,hvα,heα,_⟩ := t.inlined_at_level M hM hT P hP ht hi
  have hbound (k : Fin n) : ∃ β : Ordinal.{u}, β.toZFSet ∈ M ∧
      ∀ δ : Ordinal.{u}, δ.toZFSet ∈ M → β ≤ δ →
        ∀ o : Ordinal.{u}, t.ordinalData k = some o →
          o.toZFSet ∈ level R δ ∧ level R o ∈ level R δ ∧
          ∀ A ∈ level R δ,
            p.Sat (level R δ : Set ZFSet) (cons A (cons o.toZFSet (fun _ => R))) ↔ A = level R o
              := by
    cases hk : t.ordinalData k with
    | none =>
      refine ⟨0,internal_ordinal_zero M hM hT,?_⟩
      intro δ hδ hle o ho
      cases ho
    | some o =>
      obtain ⟨β,hβ,hβspec⟩ := hp M hM hT o (t.ordinalData_mem M hi k o hk)
      refine ⟨β,hβ,?_⟩
      intro δ hδ hle o' ho'
      have heq : o = o' := Option.some.inj ho'
      subst o'
      obtain ⟨hoL,hsL,_,hdef⟩ := hβspec δ hδ hle
      exact ⟨hoL,hsL,hdef⟩
  choose b hb hbs using hbound
  let β : Ordinal.{u} := Finset.univ.sup b
  have hβ : β.toZFSet ∈ M := internal_ordinal_finite_sup M hM hT Finset.univ b (fun i _ => hb i)
  refine ⟨max α β,internal_ordinal_max M hα hβ,?_⟩
  intro δ hδ hle
  have hαδ : α ≤ δ := (le_max_left α β).trans hle
  have hβδ : β ≤ δ := (le_max_right α β).trans hle
  have hbδ (k : Fin n) : b k ≤ δ := (Finset.le_sup (Finset.mem_univ k)).trans hβδ
  have hL := level_transitive R δ
  have hv : t.value R P ∈ level R δ := level_mono R hαδ hvα
  have he : ∀ i, t.singleInputs R P i ∈ level R δ := fun i => level_mono R hαδ (heα i)
  have hown := t.ownRealsInputs_mem (level R δ) R P he
  have hR := groundReals_mem M hM hT
  have hsame : groundReals (level R δ) = R := groundReals_between M (level R δ) hL
    (level_subset_model M R hM hT hR δ hδ) (he 0)
  have hord : ∀ i, t.ordinalInputs P i ∈ level R δ := by
    intro i
    cases i with
    | zero => exact he 1
    | succ k =>
      change (if k < n then match t.ordinalData k with | none => realCode P | some o => o.toZFSet
        else realCode P) ∈ level R δ
      by_cases hk : k < n
      · rw [ite_eq_left hk]
        cases ho : t.ordinalData k with
        | none => exact he 1
        | some o => exact (hbs ⟨k,hk⟩ δ hδ (hbδ ⟨k,hk⟩) o ho).1
      · rw [ite_eq_right hk]; exact he 1
  refine ⟨hv,hord,?_⟩
  intro z hz
  have hf (k : ℕ) (hk : k < n) (A : ZFSet.{u}) (hA : A ∈ level R δ) :
      (t.ordinalInputFormula p k).Sat (level R δ : Set ZFSet) (cons A (cons z (t.ordinalInputs
        P))) ↔
      A = t.ownRealsInputs R P (k+1) := by
    cases ho : t.ordinalData k with
    | none =>
      simp only [Construction.ordinalInputFormula,ho,SentenceForm.Sat,cons_zero,cons_succ,
        Construction.ordinalInputs,Construction.ownRealsInputs]
    | some o =>
      have hstage := hbs ⟨k,hk⟩ δ hδ (hbδ ⟨k,hk⟩) o ho
      simp only [Construction.ordinalInputFormula,ho,SentenceForm.sat_rename]
      have henv : (fun i => cons A (cons z (t.ordinalInputs P)) (if i = 0 then 0 else k+3)) =
          cons A (fun _ => o.toZFSet) := by
        funext i
        cases i with
        | zero => rfl
        | succ i => simp [Construction.ordinalInputs,show k < t.ownRealsMembership.bound from hk,ho]
      rw [henv,ownStageFormula_spec p (level R δ) R o.toZFSet A hL (he 2) hsame (he 0) hA hstage.1]
      simpa only [Construction.ownRealsInputs,cons_succ,ho] using hstage.2.2 A hA
  exact (t.ordinalMembership_spec p (level R δ) R P z (fun k _ => hown (k+1)) hf).trans
    (t.ownRealsMembership_spec (level R δ) R hL hsame P ht he hv z hz)

theorem Construction.ordinal_subset_definition (t : Construction.{u}) :
    ∃ q : SentenceForm, ∀ M : ZFSet.{u}, Transitive M → SourceT M →
      ∀ P : Oracle, P ∈ modelReals M → t.Certified (groundReals M) P → t.Indexed M →
        ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧
          (∀ i, t.ordinalInputs P i ∈ level (groundReals M) γ) ∧
          t.value (groundReals M) P = definedSubset (level (groundReals M) γ) q
            (fun i : Fin q.bound => t.ordinalInputs P i) := by
  obtain ⟨q,hq⟩ := t.ordinal_definition
  refine ⟨q,?_⟩
  intro M hM hT P hP ht hi
  obtain ⟨γ,hγ,hγspec⟩ := hq M hM hT P hP ht hi
  obtain ⟨hv,he,hf⟩ := hγspec γ hγ le_rfl
  exact ⟨γ,hγ,he,definedSubset_of_membership _ _ (level_transitive _ γ) hv q (t.ordinalInputs P) hf⟩

end TuringRigidity.RelativeConstructible

end OAI
