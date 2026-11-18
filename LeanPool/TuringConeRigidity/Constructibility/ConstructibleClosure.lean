/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/ConstructibleClosure.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.ConstructibleStages

/-!
# Constructible Closure
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel SentenceForm BoundedSetTheory TransitiveNameModel
universe u

theorem empty_mem_definablePower (A : ZFSet.{u}) : (∅ : ZFSet.{u}) ∈ definablePower A := by
  apply (mem_definablePower A ∅).mpr
  refine ⟨0,.neg (.equal 0 0),Fin.elim0,by decide,fun i => Fin.elim0 i,?_⟩
  apply ZFSet.ext; intro x
  simp [mem_definedSubset,Sat]

theorem pair_mem_definablePower (A a b : ZFSet.{u}) (ha : a ∈ A) (hb : b ∈ A) :
    ({a,b} : ZFSet.{u}) ∈ definablePower A := by
  apply (mem_definablePower A _).mpr
  let v : Fin 2 → ZFSet.{u} := Fin.cases a (fun _ => b)
  refine ⟨2,disj (.equal 0 1) (.equal 0 2),v,by decide,?_,?_⟩
  · intro i; exact Fin.cases ha (fun _ => hb) i
  · apply ZFSet.ext; intro x
    simp only [ZFSet.mem_pair,mem_definedSubset,sat_disj,Sat,cons_zero,cons_succ]
    have h0 : tupleEnv v 0 = a := by simp [tupleEnv,v]
    have h1 : tupleEnv v 1 = b := by simp [tupleEnv,v]; rfl
    rw [h0,h1]
    exact ⟨fun h => ⟨h.elim (fun h => h ▸ ha) (fun h => h ▸ hb),h⟩,And.right⟩

theorem union_mem_definablePower (A a : ZFSet.{u}) (hA : Transitive A) (ha : a ∈ A) :
    ZFSet.sUnion a ∈ definablePower A := by
  apply (mem_definablePower A _).mpr
  refine ⟨1,.ex (.conj (.member 0 2) (.member 1 0)),fun _ => a,
    by decide,fun _ => ha,?_⟩
  apply ZFSet.ext; intro x
  simp only [ZFSet.mem_sUnion,mem_definedSubset,Sat,cons_zero,cons_succ]
  have h0 : tupleEnv (fun _ : Fin 1 => a) 0 = a := by simp [tupleEnv]
  rw [h0]
  constructor
  · rintro ⟨y,hy,hx⟩
    have hyA := hA a ha y hy
    exact ⟨hA y hyA x hx,y,hyA,hy,hx⟩
  · rintro ⟨_,y,_,hy,hx⟩
    exact ⟨y,hy,hx⟩

theorem empty_in_relativeL (R : ZFSet.{u}) : InRelativeL R ∅ := by
  refine ⟨1,?_⟩
  rw [show (1 : Ordinal) = 0+1 by simp,level_succ]
  exact empty_mem_definablePower _

theorem pair_in_relativeL (R : ZFSet.{u}) {a b : ZFSet.{u}}
    (ha : InRelativeL R a) (hb : InRelativeL R b) : InRelativeL R ({a,b} : ZFSet) := by
  obtain ⟨i,hi⟩ := ha
  obtain ⟨j,hj⟩ := hb
  refine ⟨max i j + 1,?_⟩
  rw [level_succ]
  exact pair_mem_definablePower _ a b (level_mono R (le_max_left i j) hi)
    (level_mono R (le_max_right i j) hj)

theorem union_in_relativeL (R : ZFSet.{u}) {a : ZFSet.{u}}
    (ha : InRelativeL R a) : InRelativeL R (ZFSet.sUnion a) := by
  obtain ⟨i,hi⟩ := ha
  refine ⟨i+1,?_⟩
  rw [level_succ]
  exact union_mem_definablePower _ a (level_transitive R i) hi

theorem finite_parameters_in_level (R : ZFSet.{u}) (e : ℕ → ZFSet.{u}) (n : ℕ)
    (he : ∀ i, i < n → InRelativeL R (e i)) :
    ∃ o : Ordinal.{u}, ∀ i, i < n → e i ∈ level R o := by
  induction n with
  | zero => exact ⟨0,fun _ hi => (Nat.not_lt_zero _ hi).elim⟩
  | succ n ih =>
    obtain ⟨o,ho⟩ := ih (fun i hi => he i (Nat.lt_succ_of_lt hi))
    obtain ⟨p,hp⟩ := he n (Nat.lt_succ_self n)
    refine ⟨max o p,fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi|rfl
    · exact level_mono R (le_max_left o p) (ho i hi)
    · exact level_mono R (le_max_right o p) hp

end TuringRigidity.RelativeConstructible

end OAI
