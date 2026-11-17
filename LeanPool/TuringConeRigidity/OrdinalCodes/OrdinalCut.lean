/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalCut.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.RelativeModelSyntax
public import LeanPool.TuringConeRigidity.SetModels.ElementarySatisfaction

/-!
# Ordinal Cut
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

noncomputable def ordinalCut (A : ZFSet.{u}) : ZFSet.{u} := A.sep ZFSet.IsOrdinal

theorem mem_ordinalCut (A x : ZFSet.{u}) :
    x ∈ ordinalCut A ↔ x ∈ A ∧ x.IsOrdinal := ZFSet.mem_sep

theorem ordinalCut_isOrdinal (A : ZFSet.{u}) (hA : Transitive A) :
    (ordinalCut A).IsOrdinal := by
  apply ZFSet.isOrdinal_iff_forall_mem_isOrdinal.mpr
  constructor
  · intro x hx y hy
    obtain ⟨hx,ho⟩ := (mem_ordinalCut A x).mp hx
    exact (mem_ordinalCut A y).mpr ⟨hA x hx y hy,ho.mem hy⟩
  · intro x hx; exact ((mem_ordinalCut A x).mp hx).2

noncomputable def ordinalHeight (A : ZFSet.{u}) : Ordinal.{u} := (ordinalCut A).rank

theorem ordinalHeight_toZFSet (A : ZFSet.{u}) (hA : Transitive A) :
    (ordinalHeight A).toZFSet = ordinalCut A := (ordinalCut_isOrdinal A hA).toZFSet_rank_eq

theorem ordinal_mem_iff_height (A : ZFSet.{u}) (hA : Transitive A) (o : Ordinal.{u}) :
    o.toZFSet ∈ A ↔ o < ordinalHeight A := by
  rw [← Ordinal.toZFSet_mem_toZFSet_iff,ordinalHeight_toZFSet A hA,mem_ordinalCut]
  exact (and_iff_left (ZFSet.isOrdinal_toZFSet o)).symm

theorem ordinal_subset_iff_height (A : ZFSet.{u}) (hA : Transitive A) (o : Ordinal.{u}) :
    o.toZFSet ⊆ A ↔ o ≤ ordinalHeight A := by
  rw [← Ordinal.toZFSet_subset_toZFSet_iff,ordinalHeight_toZFSet A hA]
  constructor
  · intro h x hx
    exact (mem_ordinalCut A x).mpr ⟨h hx,(ZFSet.isOrdinal_toZFSet o).mem hx⟩
  · intro h x hx; exact ((mem_ordinalCut A x).mp (h hx)).1

noncomputable def ordinalSentence : SentenceForm := fromBounded (ordinalFormula 0)

theorem ordinalSentence_bound : ordinalSentence.bound = 1 := by rfl

theorem ordinalSentence_spec (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : e 0 ∈ A) :
    ordinalSentence.Sat (A : Set ZFSet) e ↔ (e 0).IsOrdinal := by
  have hs := ordinalSentence.finite_support (A : Set ZFSet) e (fun _ => e 0) (by
    intro i hi
    rw [ordinalSentence_bound] at hi
    have : i = 0 := by omega
    subst i; rfl)
  rw [hs]
  exact (bounded_sat _ _ _).trans
    (((ordinalFormula 0).absolute A hA _ (fun _ => he)).trans (eval_ordinalFormula 0 _))

theorem ordinalCut_mem_definablePower (A : ZFSet.{u}) (hA : Transitive A) :
    ordinalCut A ∈ definablePower A := by
  apply (mem_definablePower A _).mpr
  refine ⟨0,ordinalSentence,Fin.elim0,by rw [ordinalSentence_bound],fun i => Fin.elim0 i,?_⟩
  apply ZFSet.ext; intro x
  rw [mem_ordinalCut,mem_definedSubset]
  apply and_congr_right; intro hx
  exact (ordinalSentence_spec A hA (cons x (tupleEnv (Fin.elim0 : Fin 0 → ZFSet.{u}))) hx).symm

theorem ordinal_definablePower_iff (A : ZFSet.{u}) (hA : Transitive A) (o : Ordinal.{u}) :
    o.toZFSet ∈ definablePower A ↔ o ≤ ordinalHeight A := by
  constructor
  · intro ho
    exact (ordinal_subset_iff_height A hA o).mp (subset_of_mem_definablePower ho)
  · intro ho
    rcases lt_or_eq_of_le ho with ho|rfl
    · exact subset_definablePower hA ((ordinal_mem_iff_height A hA o).mpr ho)
    · rw [ordinalHeight_toZFSet A hA]
      exact ordinalCut_mem_definablePower A hA

theorem ordinalHeight_definablePower (A : ZFSet.{u}) (hA : Transitive A) :
    ordinalHeight (definablePower A) = ordinalHeight A + 1 := by
  apply le_antisymm
  · by_contra h
    have hm := (ordinal_mem_iff_height _ (definablePower_transitive hA) _).mpr (lt_of_not_ge h)
    have := (ordinal_definablePower_iff A hA _).mp hm
    exact (not_le_of_gt (lt_add_one (ordinalHeight A))) this
  · apply Order.add_one_le_iff.mpr
    exact (ordinal_mem_iff_height _ (definablePower_transitive hA) _).mp
      ((ordinal_definablePower_iff A hA _).mpr le_rfl)

end TuringRigidity.RelativeConstructible

end OAI
