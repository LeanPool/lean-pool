/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/ConstructibleStages.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.ConstructibleBase
public import Mathlib.SetTheory.ZFC.Ordinal

/-!
# Constructible Stages
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel
universe u

noncomputable def stage (R o : ZFSet.{u}) : ZFSet.{u} :=
  seed R ∪ ZFSet.sUnion (ZFSet.range (fun i : Shrink o =>
    definablePower (stage R ((equivShrink o).symm i).val)))
termination_by o
decreasing_by exact ((equivShrink o).symm i).property

theorem mem_stage (R o x : ZFSet.{u}) :
    x ∈ stage R o ↔ x ∈ seed R ∨ ∃ i ∈ o, x ∈ definablePower (stage R i) := by
  rw [stage,ZFSet.mem_union,ZFSet.mem_sUnion]
  apply or_congr_right
  constructor
  · rintro ⟨a,ha,hx⟩
    obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp ha
    exact ⟨_,((equivShrink o).symm i).property,hx⟩
  · rintro ⟨i,hi,hx⟩
    refine ⟨_,ZFSet.mem_range.mpr ⟨equivShrink o ⟨i,hi⟩,rfl⟩,?_⟩
    simpa using hx

theorem seed_subset_stage (R o : ZFSet.{u}) : seed R ⊆ stage R o :=
  fun x hx => (mem_stage R o x).mpr (Or.inl hx)

theorem stage_zero (R : ZFSet.{u}) : stage R ∅ = seed R := by
  apply ZFSet.ext; intro x
  simp [mem_stage]

theorem stage_transitive (R o : ZFSet.{u}) : Transitive (stage R o) := by
  induction o using ZFSet.inductionOn with
  | h o ih =>
    intro x hx y hy
    rcases (mem_stage R o x).mp hx with hx|⟨i,hi,hx⟩
    · exact seed_subset_stage R o (seed_transitive R x hx y hy)
    · exact (mem_stage R o y).mpr (Or.inr ⟨i,hi,definablePower_transitive (ih i hi) x hx y hy⟩)

theorem stage_mono (R : ZFSet.{u}) {i j : ZFSet.{u}} (hij : i ⊆ j) : stage R i ⊆ stage R j := by
  intro x hx
  rcases (mem_stage R i x).mp hx with hx|⟨k,hk,hx⟩
  · exact seed_subset_stage R j hx
  · exact (mem_stage R j x).mpr (Or.inr ⟨k,hij hk,hx⟩)

theorem definablePower_subset_stage (R : ZFSet.{u}) {i j : ZFSet.{u}} (hi : i ∈ j) :
    definablePower (stage R i) ⊆ stage R j :=
  fun x hx => (mem_stage R j x).mpr (Or.inr ⟨i,hi,hx⟩)

theorem stage_mem_stage (R : ZFSet.{u}) {i j : ZFSet.{u}} (hi : i ∈ j) :
    stage R i ∈ stage R j :=
  definablePower_subset_stage R hi (self_mem_definablePower _)

theorem stage_succ (R o : ZFSet.{u}) :
    stage R (insert o o) = definablePower (stage R o) := by
  apply ZFSet.ext; intro x
  constructor
  · intro hx
    rcases (mem_stage R (insert o o) x).mp hx with hseed|⟨i,hi,hdef⟩
    · exact subset_definablePower (stage_transitive R o) (seed_subset_stage R o hseed)
    · rcases ZFSet.mem_insert_iff.mp hi with he|hi
      · simpa only [he] using hdef
      · exact subset_definablePower (stage_transitive R o) (definablePower_subset_stage R hi hdef)
  · intro hx; exact definablePower_subset_stage R (ZFSet.mem_insert o o) hx

noncomputable def level (R : ZFSet.{u}) (o : Ordinal.{u}) : ZFSet.{u} := stage R o.toZFSet

theorem level_zero (R : ZFSet.{u}) : level R 0 = seed R := by
  rw [level,Ordinal.toZFSet_zero,stage_zero]

theorem level_succ (R : ZFSet.{u}) (o : Ordinal.{u}) :
    level R (o+1) = definablePower (level R o) := by
  simp only [level,Ordinal.toZFSet_add_one,stage_succ]

theorem level_mono (R : ZFSet.{u}) {i j : Ordinal.{u}} (hij : i ≤ j) : level R i ⊆ level R j :=
  stage_mono R (Ordinal.toZFSet_monotone hij)

theorem level_mem_level (R : ZFSet.{u}) {i j : Ordinal.{u}} (hij : i < j) : level R i ∈ level R j :=
  stage_mem_stage R (Ordinal.toZFSet_mem_toZFSet_iff.mpr hij)

theorem level_transitive (R : ZFSet.{u}) (o : Ordinal.{u}) : Transitive (level R o) :=
  stage_transitive R o.toZFSet

theorem mem_level_limit (R x : ZFSet.{u}) (o : Ordinal.{u}) (ho : Order.IsSuccLimit o) :
    x ∈ level R o ↔ ∃ i < o, x ∈ level R i := by
  constructor
  · intro hx
    rcases (mem_stage R o.toZFSet x).mp hx with hx|⟨a,ha,hx⟩
    · refine ⟨0,Ordinal.natCast_lt_of_isSuccLimit ho 0,?_⟩
      rwa [level_zero]
    · obtain ⟨i,hi,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ha
      refine ⟨i+1,ho.succ_lt hi,?_⟩
      rwa [level_succ]
  · rintro ⟨i,hi,hx⟩
    exact level_mono R hi.le hx

def InRelativeL (R x : ZFSet.{u}) : Prop := ∃ o : Ordinal.{u}, x ∈ level R o

theorem parameter_in_relativeL (R : ZFSet.{u}) : InRelativeL R R := by
  exact ⟨0,level_zero R ▸ parameter_mem_seed R⟩

theorem relativeL_transitive (R : ZFSet.{u}) {x y : ZFSet.{u}}
    (hx : InRelativeL R x) (hy : y ∈ x) : InRelativeL R y := by
  obtain ⟨o,ho⟩ := hx
  exact ⟨o,level_transitive R o x ho y hy⟩

end TuringRigidity.RelativeConstructible

end OAI
