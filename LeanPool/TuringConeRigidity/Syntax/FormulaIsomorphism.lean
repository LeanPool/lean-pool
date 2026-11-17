/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/FormulaIsomorphism.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.SigmaSyntax

/-!
# Formula Isomorphism
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u

theorem map_cons (j : ZFSet.{u} → ZFSet.{u}) (x : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (fun i => j (cons x e i)) = cons (j x) (fun i => j (e i)) := by
  funext i; cases i <;> rfl

theorem Formula.realize_isomorphism (A B : ZFSet.{u}) (j : ZFSet.{u} → ZFSet.{u})
    (hin : ∀ x ∈ A, j x ∈ B)
    (hout : ∀ y ∈ B, ∃ x ∈ A, j x = y)
    (hi : ∀ x ∈ A, ∀ y ∈ A, j x = j y → x = y)
    (hm : ∀ x ∈ A, ∀ y ∈ A, j x ∈ j y ↔ x ∈ y)
    (φ : Formula) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) :
    φ.Realize A e ↔ φ.Realize B (fun i => j (e i)) := by
  induction φ generalizing e with
  | equal i k =>
    exact ⟨congrArg j,hi _ (he i) _ (he k)⟩
  | member i k => exact (hm _ (he i) _ (he k)).symm
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ e he) (ihψ e he)
  | neg φ ih => exact not_congr (ih e he)
  | existsMem i φ ih =>
    have he' (x : ZFSet.{u}) (hx : x ∈ A) : ∀ n, cons x e n ∈ A := by
      intro n; cases n with
      | zero => exact hx
      | succ n => exact he n
    constructor
    · rintro ⟨x,hx,hxi,hφ⟩
      refine ⟨j x,hin x hx,(hm x hx (e i) (he i)).mpr hxi,?_⟩
      have h := (ih (cons x e) (he' x hx)).mp hφ
      rwa [map_cons] at h
    · rintro ⟨y,hy,hyi,hφ⟩
      obtain ⟨x,hx,rfl⟩ := hout y hy
      refine ⟨x,hx,(hm x hx (e i) (he i)).mp hyi,?_⟩
      apply (ih (cons x e) (he' x hx)).mpr
      rwa [map_cons]

theorem SigmaFormula.realize_isomorphism (A B : ZFSet.{u}) (j : ZFSet.{u} → ZFSet.{u})
    (hin : ∀ x ∈ A, j x ∈ B)
    (hout : ∀ y ∈ B, ∃ x ∈ A, j x = y)
    (hi : ∀ x ∈ A, ∀ y ∈ A, j x = j y → x = y)
    (hm : ∀ x ∈ A, ∀ y ∈ A, j x ∈ j y ↔ x ∈ y)
    (φ : SigmaFormula) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) :
    φ.Realize A e ↔ φ.Realize B (fun i => j (e i)) := by
  induction φ generalizing e with
  | bounded φ => exact φ.realize_isomorphism A B j hin hout hi hm e he
  | existsSet φ ih =>
    have he' (x : ZFSet.{u}) (hx : x ∈ A) : ∀ n, cons x e n ∈ A := by
      intro n; cases n with
      | zero => exact hx
      | succ n => exact he n
    constructor
    · rintro ⟨x,hx,hφ⟩
      refine ⟨j x,hin x hx,?_⟩
      have h := (ih (cons x e) (he' x hx)).mp hφ
      rwa [map_cons] at h
    · rintro ⟨y,hy,hφ⟩
      obtain ⟨x,hx,rfl⟩ := hout y hy
      apply Exists.intro x
      refine ⟨hx,?_⟩
      apply (ih (cons x e) (he' x hx)).mpr
      rwa [map_cons]

end TuringRigidity.BoundedSetTheory

end OAI
