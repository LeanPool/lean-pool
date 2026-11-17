/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/BoundedRelations.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ModelProducts

/-!
# Bounded Relations
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

namespace Formula
def imp (φ ψ : Formula) : Formula := disj (.neg φ) ψ
def iff (φ ψ : Formula) : Formula := .conj (imp φ ψ) (imp ψ φ)

@[simp] theorem eval_imp (φ ψ : Formula) (e : ℕ → ZFSet.{u}) :
    (imp φ ψ).Eval e ↔ (φ.Eval e → ψ.Eval e) := by
  classical
  simp only [imp, eval_disj, Eval]
  constructor
  · intro h hp; exact h.elim (fun hn => False.elim (hn hp)) id
  · intro h; by_cases hp : φ.Eval e
    · exact Or.inr (h hp)
    · exact Or.inl hp

@[simp] theorem eval_iff (φ ψ : Formula) (e : ℕ → ZFSet.{u}) :
    (iff φ ψ).Eval e ↔ (φ.Eval e ↔ ψ.Eval e) := by
  simp only [iff, Eval, eval_imp, iff_def]

def subset (a b : ℕ) : Formula := allMem a (.member 0 (b+1))
def transitive (a : ℕ) : Formula := allMem a (subset 0 (a+1))

@[simp] theorem eval_subset (a b : ℕ) (e : ℕ → ZFSet.{u}) :
    (subset a b).Eval e ↔ e a ⊆ e b := by
  simp only [subset, eval_allMem, Eval, cons_zero, cons_succ]
  rfl

@[simp] theorem eval_transitive (a : ℕ) (e : ℕ → ZFSet.{u}) :
    (transitive a).Eval e ↔ Transitive (e a) := by
  simp only [transitive, eval_allMem, eval_subset, cons_zero, cons_succ]
  rfl

def functionGraph (f d v : ℕ) : Formula :=
  .conj (allMem f (.existsMem (d+1) (.existsMem (v+2) (orderedPair 2 1 0))))
    (allMem d (.existsMem (v+1)
      (.conj (pairMem 1 0 (f+2))
        (allMem (v+2) (imp (pairMem 2 0 (f+3)) (.equal 0 1))))))

@[simp] theorem eval_functionGraph (f d v : ℕ) (e : ℕ → ZFSet.{u}) :
    (functionGraph f d v).Eval e ↔
      (∀ z ∈ e f, ∃ x ∈ e d, ∃ y ∈ e v, z = ZFSet.pair x y) ∧
      (∀ x ∈ e d, ∃ y ∈ e v, ZFSet.pair x y ∈ e f ∧
        ∀ z ∈ e v, ZFSet.pair x z ∈ e f → z = y) := by
  simp only [functionGraph, Eval, eval_allMem, eval_orderedPair,
    eval_pairMem, eval_imp, cons_zero, cons_succ]

end Formula

inductive SigmaFormula where
  | bounded (φ : Formula)
  | existsSet (φ : SigmaFormula)

def SigmaFormula.Realize (M : ZFSet.{u}) (e : ℕ → ZFSet.{u}) : SigmaFormula → Prop
  | .bounded φ => φ.Realize M e
  | .existsSet φ => ∃ x ∈ M, φ.Realize M (cons x e)

def SigmaReplacement (M : ZFSet.{u}) : Prop :=
  ∀ (φ : SigmaFormula) (e : ℕ → ZFSet.{u}), (∀ i, e i ∈ M) →
    ∀ a ∈ M,
    (∀ x ∈ a, ∃ y ∈ M, φ.Realize M (cons y (cons x e)) ∧
      ∀ z ∈ M, φ.Realize M (cons z (cons x e)) → z = y) →
    ∃ b ∈ M, ∀ y ∈ M, y ∈ b ↔ ∃ x ∈ a, φ.Realize M (cons y (cons x e))

theorem replacement_image (M : ZFSet.{u}) (hM : Transitive M)
    (hR : SigmaReplacement M) (φ : SigmaFormula) (e : ℕ → ZFSet.{u})
    (he : ∀ i, e i ∈ M) {a : ZFSet.{u}} (ha : a ∈ M)
    (F : ZFSet.{u} → ZFSet.{u}) (hF : ∀ x ∈ a, F x ∈ M)
    (hφ : ∀ x ∈ a, ∀ y ∈ M, φ.Realize M (cons y (cons x e)) ↔ y = F x) :
    ∃ b ∈ M, ∀ y, y ∈ b ↔ ∃ x ∈ a, F x = y := by
  obtain ⟨b,hb,hbdef⟩ := hR φ e he a ha (fun x hx =>
    ⟨F x,hF x hx,(hφ x hx _ (hF x hx)).mpr rfl,
      fun z hz h => (hφ x hx z hz).mp h⟩)
  refine ⟨b,hb,fun y => ?_⟩
  constructor
  · intro hy
    have hyM := hM b hb y hy
    obtain ⟨x,hx,hxy⟩ := (hbdef y hyM).mp hy
    exact ⟨x,hx,((hφ x hx y hyM).mp hxy).symm⟩
  · rintro ⟨x,hx,rfl⟩
    exact (hbdef _ (hF x hx)).mpr ⟨x,hx,(hφ x hx _ (hF x hx)).mpr rfl⟩

end TuringRigidity.BoundedSetTheory

end OAI
