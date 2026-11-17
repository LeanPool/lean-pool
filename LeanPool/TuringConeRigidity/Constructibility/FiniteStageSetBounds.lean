/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/FiniteStageSetBounds.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.ConstructibleClosure

/-!
# Finite Stage Set Bounds
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel
universe u

theorem pair_mem_level_succ (R : ZFSet.{u}) (a : Ordinal.{u})
    {x y : ZFSet.{u}} (hx : x ∈ level R a) (hy : y ∈ level R a) :
    ({x,y} : ZFSet.{u}) ∈ level R (a+1) := by
  rw [level_succ]
  exact pair_mem_definablePower _ _ _ hx hy

theorem orderedPair_mem_level_add_two (R : ZFSet.{u}) (a : Ordinal.{u})
    {x y : ZFSet.{u}} (hx : x ∈ level R a) (hy : y ∈ level R a) :
    ZFSet.pair x y ∈ level R (a+2) := by
  have hs : ({x} : ZFSet.{u}) ∈ level R (a+1) := by
    simpa using pair_mem_level_succ R a hx hx
  simpa only [ZFSet.pair,add_assoc,one_add_one_eq_two] using
    pair_mem_level_succ R (a+1) hs (pair_mem_level_succ R a hx hy)

theorem union_mem_level_succ (R : ZFSet.{u}) (a : Ordinal.{u})
    {x : ZFSet.{u}} (hx : x ∈ level R a) : ZFSet.sUnion x ∈ level R (a+1) := by
  rw [level_succ]
  exact union_mem_definablePower _ _ (level_transitive R a) hx

theorem iterUnion_mem_level_add (R : ZFSet.{u}) (a : Ordinal.{u})
    {x : ZFSet.{u}} (hx : x ∈ level R a) (n : ℕ) :
    iterUnion n x ∈ level R (a+n) := by
  induction n with
  | zero => simpa only [iterUnion,Nat.cast_zero,add_zero] using hx
  | succ n ih =>
    simpa only [iterUnion,Nat.cast_add,Nat.cast_one,add_assoc] using
      union_mem_level_succ R (a+n) ih

theorem orderedPair_mem_level_limit (R : ZFSet.{u}) (a : Ordinal.{u})
    (ha : Order.IsSuccLimit a) {x y : ZFSet.{u}}
    (hx : x ∈ level R a) (hy : y ∈ level R a) : ZFSet.pair x y ∈ level R a := by
  obtain ⟨i,hi,hx⟩ := (mem_level_limit R x a ha).mp hx
  obtain ⟨j,hj,hy⟩ := (mem_level_limit R y a ha).mp hy
  have h := orderedPair_mem_level_add_two R (max i j)
    (level_mono R (le_max_left i j) hx) (level_mono R (le_max_right i j) hy)
  have hlt := ha.succ_lt (ha.succ_lt (max_lt hi hj))
  apply level_mono R (show max i j + 2 ≤ a from ?_) h
  simpa only [Order.succ_eq_add_one,add_assoc,one_add_one_eq_two] using hlt.le

theorem insert_mem_level_succ (R : ZFSet.{u}) (a : Ordinal.{u})
    {x y : ZFSet.{u}} (hx : x ∈ level R a) (hy : y ∈ level R a) :
    insert x y ∈ level R (a+1) := by
  let A := level R a
  let p : ElementaryModel.SentenceForm := .disj (.equal 0 1) (.member 0 2)
  let e := BoundedSetTheory.cons x (fun _ => y)
  have h := separation_mem_definablePower A p e (fun i _ => by
    cases i with
    | zero => exact hx
    | succ i => exact hy)
  have heq : A.sep (fun z => p.Sat (A : Set ZFSet) (BoundedSetTheory.cons z e)) = insert x y := by
    apply ZFSet.ext; intro z
    simp only [ZFSet.mem_sep,ZFSet.mem_insert_iff,p,ElementaryModel.SentenceForm.sat_disj,
      ElementaryModel.SentenceForm.Sat,e,BoundedSetTheory.cons_zero,BoundedSetTheory.cons_succ]
    exact ⟨And.right,fun h => ⟨h.elim (fun h => h ▸ hx)
      (fun h => level_transitive R a y hy z h),h⟩⟩
  rw [heq] at h
  rwa [level_succ]

end TuringRigidity.RelativeConstructible

end OAI
