/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/SigmaDisjunction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.SigmaBoundedUniversal

/-!
# Sigma Disjunction
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u
namespace SigmaFormula

def boundedDisj (b : Formula) : SigmaFormula → SigmaFormula
  | .bounded c => .bounded (.disj b c)
  | .existsSet φ => .existsSet (boundedDisj (b.rename Nat.succ) φ)

def disj : SigmaFormula → SigmaFormula → SigmaFormula
  | .bounded b,ψ => boundedDisj b ψ
  | .existsSet φ,ψ => .existsSet (disj φ (ψ.rename Nat.succ))

theorem realize_boundedDisj (M : ZFSet.{u}) (h0 : (∅ : ZFSet.{u}) ∈ M)
    (b : Formula) (φ : SigmaFormula) (e : ℕ → ZFSet.{u}) :
    (boundedDisj b φ).Realize M e ↔ b.Realize M e ∨ φ.Realize M e := by
  induction φ generalizing b e with
  | bounded c => simp only [boundedDisj,Realize,Formula.disj,Formula.Realize]; tauto
  | existsSet φ ih =>
    change (∃ x ∈ M, (boundedDisj (b.rename Nat.succ) φ).Realize M (cons x e)) ↔ _
    simp_rw [ih,Formula.realize_rename]
    change (∃ x ∈ M, b.Realize M e ∨ φ.Realize M (cons x e)) ↔
      b.Realize M e ∨ ∃ x ∈ M, φ.Realize M (cons x e)
    constructor
    · rintro ⟨x,hx,h|h⟩
      · exact Or.inl h
      · exact Or.inr ⟨x,hx,h⟩
    · rintro (h|⟨x,hx,h⟩)
      · exact ⟨∅,h0,Or.inl h⟩
      · exact ⟨x,hx,Or.inr h⟩

theorem realize_disj (M : ZFSet.{u}) (h0 : (∅ : ZFSet.{u}) ∈ M)
    (φ ψ : SigmaFormula) (e : ℕ → ZFSet.{u}) :
    (disj φ ψ).Realize M e ↔ φ.Realize M e ∨ ψ.Realize M e := by
  induction φ generalizing ψ e with
  | bounded b => exact realize_boundedDisj M h0 b ψ e
  | existsSet φ ih =>
    change (∃ x ∈ M, (disj φ (ψ.rename Nat.succ)).Realize M (cons x e)) ↔ _
    simp_rw [ih,realize_rename]
    change (∃ x ∈ M, φ.Realize M (cons x e) ∨ ψ.Realize M e) ↔
      (∃ x ∈ M, φ.Realize M (cons x e)) ∨ ψ.Realize M e
    constructor
    · rintro ⟨x,hx,h|h⟩
      · exact Or.inl ⟨x,hx,h⟩
      · exact Or.inr h
    · rintro (⟨x,hx,h⟩|h)
      · exact ⟨x,hx,Or.inl h⟩
      · exact ⟨∅,h0,Or.inr h⟩

def existsMem (a : ℕ) (φ : SigmaFormula) : SigmaFormula :=
  .existsSet (.andBounded (.member 0 (a+1)) φ)

theorem realize_existsMem (M : ZFSet.{u}) (a : ℕ) (φ : SigmaFormula) (e : ℕ → ZFSet.{u}) :
    (existsMem a φ).Realize M e ↔ ∃ x ∈ M, x ∈ e a ∧ φ.Realize M (cons x e) := by
  simp only [existsMem,Realize,realize_andBounded,Formula.Realize,cons_zero,cons_succ]
end SigmaFormula

end TuringRigidity.BoundedSetTheory

end OAI
