/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
import LeanPool.GraphMinor.GM09.Basic
public import LeanPool.GraphMinor.GM16.FiniteCircleCycle
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Transporting the finite rotation to boundary vertices

A finite listing of boundary vertices identifies its index set with
the boundary set. Transport rotation through this identification,
fixing all points outside the boundary. First visits to a subset,
and hence clockwise triples, are preserved by this transport.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.GM09
universe u

/-- The cyclic order on a finite set induced by an indexed listing. -/
@[expose] noncomputable def cyclicPermOnSet {α : Type u} {Y : Set α} (hY : Y.Finite)
    {n : ℕ} (e : Fin n ≃ Y) : CyclicPerm α := by
  classical
  let f : α → α := fun x => if hx : x ∈ Y then (e (finRotate n (e.symm ⟨x, hx⟩))).val else x
  have hStep : ∀ i : Fin n, f (e i).val = (e (finRotate n i)).val := by
    intro i
    dsimp only [f]
    rw [dite_eq_left (e i).property]
    simp only [e.symm_apply_apply]
  have hIter : ∀ k : ℕ, ∀ i : Fin n, (f^[k]) (e i).val = (e ((finRotate n)^[k] i)).val := by
    intro k
    induction k with
    | zero => exact fun _ => rfl
    | succ k ih =>
      intro i
      rw [Function.iterate_succ_apply', ih, hStep, Function.iterate_succ_apply']
  refine ⟨Y, f, hY, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      dsimp only [f]
      rw [dite_eq_left hx]
      exact (e _).property
    · intro x hx y hy hxy
      have hx' : (e (e.symm ⟨x, hx⟩)).val = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
      have hy' : (e (e.symm ⟨y, hy⟩)).val = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
      rw [← hx', ← hy', hStep, hStep] at hxy
      have hIdx := (finRotate n).injective (e.injective (Subtype.ext hxy))
      exact hx'.symm.trans ((congrArg (fun i => (e i).val) hIdx).trans hy')
    · intro y hy
      let i := (finRotate n).symm (e.symm ⟨y, hy⟩)
      refine ⟨(e i).val, (e i).property, ?_⟩
      rw [hStep]
      simp only [i, Equiv.apply_symm_apply, e.apply_symm_apply]
  · intro x hx y hy
    let i := e.symm ⟨x, hx⟩
    let j := e.symm ⟨y, hy⟩
    obtain ⟨k, hk⟩ := (finCyclicPerm n).single_orbit i (mem_univ i) j (mem_univ j)
    have hx' : (e i).val = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
    have hy' : (e j).val = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
    refine ⟨k, ?_⟩
    rw [← hx', hIter, show (finRotate n)^[k] i = j from hk, hy']

/-- Iterating the transported cyclic order agrees with iterating the
rotation of its index set. -/
theorem cyclicPermOnSet_iterate {α : Type u} {Y : Set α} (hY : Y.Finite)
    {n : ℕ} (e : Fin n ≃ Y) (k : ℕ) (i : Fin n) :
    ((cyclicPermOnSet hY e).toFun^[k]) (e i).val = (e ((finCyclicPerm n).toFun^[k] i)).val := by
  classical
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    change (if hx : (e ((finCyclicPerm n).toFun^[k] i)).val ∈ Y then
      (e (finRotate n (e.symm ⟨(e ((finCyclicPerm n).toFun^[k] i)).val, hx⟩))).val
      else (e ((finCyclicPerm n).toFun^[k] i)).val) = _
    rw [dite_eq_left (e _).property]
    simp only [e.symm_apply_apply]
    rfl

/-- First visits to a subset are unchanged under the boundary listing. -/
theorem cyclicPermOnSet_firstHit_iff {α : Type u} {Y : Set α} (hY : Y.Finite)
    {n : ℕ} (e : Fin n ≃ Y) (X : Set (Fin n)) (i j : Fin n) :
    (cyclicPermOnSet hY e).FirstHitIn ((fun q => (e q).val) '' X) (e i).val (e j).val ↔
      (finCyclicPerm n).FirstHitIn X i j := by
  have hInj : Function.Injective (fun q => (e q).val) := Subtype.val_injective.comp e.injective
  unfold CyclicPerm.FirstHitIn
  simp only [cyclicPermOnSet_iterate, hInj.eq_iff, mem_image]
  simp only [exists_eq_right]

/-- Clockwise triples are preserved by the transported order. -/
theorem cyclicPermOnSet_clockwise3_iff {α : Type u} {Y : Set α} (hY : Y.Finite)
    {n : ℕ} (e : Fin n ≃ Y) (i j k : Fin n) :
    (cyclicPermOnSet hY e).IsClockwise3 (e i).val (e j).val (e k).val ↔
      (finCyclicPerm n).IsClockwise3 i j k := by
  have hInj : Function.Injective (fun q => (e q).val) := Subtype.val_injective.comp e.injective
  have hSet : ({(e i).val, (e j).val, (e k).val} : Set α) =
      (fun q => (e q).val) '' ({i, j, k} : Set (Fin n)) := by
    rw [image_insert_eq, image_insert_eq, image_singleton]
  rw [CyclicPerm.isClockwise3_iff, CyclicPerm.isClockwise3_iff, hSet]
  rw [cyclicPermOnSet_firstHit_iff, cyclicPermOnSet_firstHit_iff, cyclicPermOnSet_firstHit_iff]
  simp only [ne_eq, Subtype.val_inj, e.injective.eq_iff, show (cyclicPermOnSet hY e).bar
    = Y from rfl,
    show (finCyclicPerm n).bar = univ from rfl, (e i).property, (e j).property, (e k).property,
    mem_univ, true_and]

end GraphMinor.GM16
