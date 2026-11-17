/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ElementaryLanguage.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BoundedSetTheory
public import LeanPool.TuringConeRigidity.Effective.EncodableTree

/-!
# Elementary Language
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory
universe u

inductive SentenceForm where
  | equal (i j : ℕ)
  | member (i j : ℕ)
  | conj (p q : SentenceForm)
  | neg (p : SentenceForm)
  | ex (p : SentenceForm)

namespace SentenceForm

/-- Preserve the constructor-tag layout of the former Encodable derivation. -/
def toTree : SentenceForm → EncodableTree
  | .equal i j => .cons (.nat 0) (.cons (.nat i) (.cons (.nat j) (.nat 0)))
  | .member i j => .cons (.nat 1) (.cons (.nat i) (.cons (.nat j) (.nat 0)))
  | .conj p q => .cons (.nat 2) (.cons (toTree p) (.cons (toTree q) (.nat 0)))
  | .neg p => .cons (.nat 3) (.cons (toTree p) (.nat 0))
  | .ex p => .cons (.nat 4) (.cons (toTree p) (.nat 0))

def fromTree : EncodableTree → Option SentenceForm
  | .cons (.nat 0) (.cons (.nat i) (.cons (.nat j) (.nat 0))) => some (.equal i j)
  | .cons (.nat 1) (.cons (.nat i) (.cons (.nat j) (.nat 0))) => some (.member i j)
  | .cons (.nat 2) (.cons p (.cons q (.nat 0))) => do
    return .conj (← fromTree p) (← fromTree q)
  | .cons (.nat 3) (.cons p (.nat 0)) => do
    return .neg (← fromTree p)
  | .cons (.nat 4) (.cons p (.nat 0)) => do
    return .ex (← fromTree p)
  | _ => none

theorem fromTree_toTree (p : SentenceForm) : fromTree (toTree p) = some p := by
  induction p <;> simp_all [toTree, fromTree]

end SentenceForm

-- Module-port repair: no generated reference to Mathlib's private helper type.
instance : Encodable SentenceForm :=
  Encodable.ofLeftInjection SentenceForm.toTree SentenceForm.fromTree SentenceForm.fromTree_toTree

namespace SentenceForm

def Sat (D : Set ZFSet.{u}) (e : ℕ → ZFSet.{u}) : SentenceForm → Prop
  | .equal i j => e i = e j
  | .member i j => e i ∈ e j
  | .conj p q => p.Sat D e ∧ q.Sat D e
  | .neg p => ¬ p.Sat D e
  | .ex p => ∃ x ∈ D, p.Sat D (cons x e)

def bound : SentenceForm → ℕ
  | .equal i j | .member i j => max i j + 1
  | .conj p q => max p.bound q.bound
  | .neg p => p.bound
  | .ex p => p.bound - 1

theorem finite_support (p : SentenceForm) (D : Set ZFSet.{u})
    (e f : ℕ → ZFSet.{u}) (h : ∀ i, i < p.bound → e i = f i) :
    p.Sat D e ↔ p.Sat D f := by
  induction p generalizing e f with
  | equal i j =>
    have hi := h i (by simp only [bound]; omega)
    have hj := h j (by simp only [bound]; omega)
    simp only [Sat,hi,hj]
  | member i j =>
    have hi := h i (by simp only [bound]; omega)
    have hj := h j (by simp only [bound]; omega)
    simp only [Sat,hi,hj]
  | conj p q ihp ihq =>
    exact and_congr (ihp e f (fun i hi => h i (by simp only [bound]; omega)))
      (ihq e f (fun i hi => h i (by simp only [bound]; omega)))
  | neg p ih => exact not_congr (ih e f h)
  | ex p ih =>
    apply exists_congr; intro x
    apply and_congr_right; intro _
    apply ih
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact h i (by simp only [bound] at h ⊢; omega)

def disj (p q : SentenceForm) : SentenceForm := .neg (.conj (.neg p) (.neg q))
def imp (p q : SentenceForm) : SentenceForm := .neg (.conj p (.neg q))
def iff (p q : SentenceForm) : SentenceForm := .conj (imp p q) (imp q p)
def all (p : SentenceForm) : SentenceForm := .neg (.ex (.neg p))

@[simp] theorem sat_disj (p q : SentenceForm) (D : Set ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (disj p q).Sat D e ↔ p.Sat D e ∨ q.Sat D e := by classical simp only [disj,Sat]; tauto
@[simp] theorem sat_imp (p q : SentenceForm) (D : Set ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (imp p q).Sat D e ↔ (p.Sat D e → q.Sat D e) := by classical simp [imp,Sat]
@[simp] theorem sat_iff (p q : SentenceForm) (D : Set ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (iff p q).Sat D e ↔ (p.Sat D e ↔ q.Sat D e) := by simp [iff,Sat,iff_def]
@[simp] theorem sat_all (p : SentenceForm) (D : Set ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (all p).Sat D e ↔ ∀ x ∈ D, p.Sat D (cons x e) := by classical simp [all,Sat]

def rename (v : ℕ → ℕ) : SentenceForm → SentenceForm
  | .equal i j => .equal (v i) (v j)
  | .member i j => .member (v i) (v j)
  | .conj p q => .conj (p.rename v) (q.rename v)
  | .neg p => .neg (p.rename v)
  | .ex p => .ex (p.rename (fun i => match i with | 0 => 0 | j+1 => v j+1))

theorem sat_rename (p : SentenceForm) (v : ℕ → ℕ)
    (D : Set ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (p.rename v).Sat D e ↔ p.Sat D (fun i => e (v i)) := by
  induction p generalizing v e with
  | equal => rfl
  | member => rfl
  | conj p q ihp ihq => exact and_congr (ihp v e) (ihq v e)
  | neg p ih => exact not_congr (ih v e)
  | ex p ih =>
    apply exists_congr; intro x
    apply and_congr_right; intro _
    have he : (fun i => cons x e (match i with | 0 => 0 | j+1 => v j+1)) =
        cons x (fun i => e (v i)) := by funext i; cases i <;> rfl
    exact (ih _ _).trans (he ▸ Iff.rfl)
end SentenceForm

def Elementary (D : Set ZFSet.{u}) : Prop :=
  ∀ p : SentenceForm, ∀ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ D) →
    (p.Sat D e ↔ p.Sat Set.univ e)

end TuringRigidity.ElementaryModel

end OAI
