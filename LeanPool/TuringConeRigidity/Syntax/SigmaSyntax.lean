/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/SigmaSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BoundedRelations

/-!
# Sigma Syntax
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u

/-- Lift a variable renaming past one newly bound variable. -/
def liftMap (v : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => v i+1

namespace Formula

/-- Rename variables throughout bounded formula syntax, lifting the renaming under each bound
variable. -/
def rename (v : ℕ → ℕ) : Formula → Formula
  | .equal i j => .equal (v i) (v j)
  | .member i j => .member (v i) (v j)
  | .conj φ ψ => .conj (rename v φ) (rename v ψ)
  | .neg φ => .neg (rename v φ)
  | .existsMem i φ => .existsMem (v i) (rename (liftMap v) φ)

theorem realize_rename (φ : Formula) (M : ZFSet.{u}) (v : ℕ → ℕ)
    (e : ℕ → ZFSet.{u}) : (φ.rename v).Realize M e ↔ φ.Realize M (fun i => e (v i)) := by
  induction φ generalizing v e with
  | equal => rfl
  | member => rfl
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ v e) (ihψ v e)
  | neg φ ih => exact not_congr (ih v e)
  | existsMem i φ ih =>
    simp only [rename,Realize]
    apply exists_congr
    intro x
    apply and_congr_right
    intro _
    apply and_congr_right
    intro _
    have he : (fun i => cons x e (liftMap v i)) = cons x (fun i => e (v i)) := by
      funext i; cases i <;> rfl
    exact (ih (liftMap v) (cons x e)).trans (he ▸ Iff.rfl)
end Formula

namespace SigmaFormula

/-- Rename variables throughout sigma syntax, lifting the renaming under each existential set
variable. -/
def rename (v : ℕ → ℕ) : SigmaFormula → SigmaFormula
  | .bounded φ => .bounded (φ.rename v)
  | .existsSet φ => .existsSet (rename (liftMap v) φ)

theorem realize_rename (φ : SigmaFormula) (M : ZFSet.{u}) (v : ℕ → ℕ)
    (e : ℕ → ZFSet.{u}) : (φ.rename v).Realize M e ↔ φ.Realize M (fun i => e (v i)) := by
  induction φ generalizing v e with
  | bounded φ => exact φ.realize_rename M v e
  | existsSet φ ih =>
    simp only [rename,Realize]
    apply exists_congr
    intro x
    apply and_congr_right
    intro _
    have he : (fun i => cons x e (liftMap v i)) = cons x (fun i => e (v i)) := by
      funext i; cases i <;> rfl
    exact (ih (liftMap v) (cons x e)).trans (he ▸ Iff.rfl)

/-- Conjoin a bounded formula with a sigma formula while moving through its existential
prefix. -/
def andBounded (b : Formula) : SigmaFormula → SigmaFormula
  | .bounded φ => .bounded (.conj b φ)
  | .existsSet φ => .existsSet (andBounded (b.rename Nat.succ) φ)

theorem realize_andBounded (b : Formula) (φ : SigmaFormula) (M : ZFSet.{u})
    (e : ℕ → ZFSet.{u}) :
    (andBounded b φ).Realize M e ↔ b.Realize M e ∧ φ.Realize M e := by
  induction φ generalizing b e with
  | bounded => rfl
  | existsSet φ ih =>
    simp only [andBounded,Realize,ih,Formula.realize_rename,cons_succ]
    constructor
    · rintro ⟨x,hx,hb,hφ⟩; exact ⟨hb,x,hx,hφ⟩
    · rintro ⟨hb,x,hx,hφ⟩; exact ⟨x,hx,hb,hφ⟩

/-- Conjoin two sigma formulas while combining their existential prefixes. -/
def conj : SigmaFormula → SigmaFormula → SigmaFormula
  | .bounded b, ψ => andBounded b ψ
  | .existsSet φ, ψ => .existsSet (conj φ (ψ.rename Nat.succ))

theorem realize_conj (φ ψ : SigmaFormula) (M : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (conj φ ψ).Realize M e ↔ φ.Realize M e ∧ ψ.Realize M e := by
  induction φ generalizing ψ e with
  | bounded b => exact realize_andBounded b ψ M e
  | existsSet φ ih =>
    simp only [conj,Realize,ih,realize_rename,cons_succ]
    constructor
    · rintro ⟨x,hx,hφ,hψ⟩; exact ⟨⟨x,hx,hφ⟩,hψ⟩
    · rintro ⟨⟨x,hx,hφ⟩,hψ⟩; exact ⟨x,hx,hφ,hψ⟩
end SigmaFormula

end TuringRigidity.BoundedSetTheory

end OAI
