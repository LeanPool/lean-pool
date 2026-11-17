/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/LevySigmaNormalization.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.SigmaDisjunction
public import LeanPool.TuringConeRigidity.Syntax.SigmaBoundedUniversal

/-!
# Levy Sigma Normalization
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

/-- Levy-sigma syntax with bounded formulas, positive Boolean operations, and existential or
bounded quantifiers. -/
inductive LevySigma where
  | bounded (φ : Formula)
  | conj (φ ψ : LevySigma)
  | disj (φ ψ : LevySigma)
  | existsSet (φ : LevySigma)
  | existsMem (a : ℕ) (φ : LevySigma)
  | allMem (a : ℕ) (φ : LevySigma)

namespace LevySigma
/-- Interpret Levy-sigma syntax with set witnesses restricted to the model. -/
def Realize (M : ZFSet.{u}) (e : ℕ → ZFSet.{u}) : LevySigma → Prop
  | .bounded φ => φ.Realize M e
  | .conj φ ψ => φ.Realize M e ∧ ψ.Realize M e
  | .disj φ ψ => φ.Realize M e ∨ ψ.Realize M e
  | .existsSet φ => ∃ x ∈ M, φ.Realize M (cons x e)
  | .existsMem a φ => ∃ x ∈ M, x ∈ e a ∧ φ.Realize M (cons x e)
  | .allMem a φ => ∀ x ∈ M, x ∈ e a → φ.Realize M (cons x e)

/-- Normalize Levy-sigma syntax to an existential set prefix over a bounded matrix. -/
def normalize : LevySigma → SigmaFormula
  | .bounded φ => .bounded φ
  | .conj φ ψ => .conj φ.normalize ψ.normalize
  | .disj φ ψ => .disj φ.normalize ψ.normalize
  | .existsSet φ => .existsSet φ.normalize
  | .existsMem a φ => .existsMem a φ.normalize
  | .allMem a φ => .allMem a φ.normalize

theorem normalize_correct (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hC : SigmaCollection M)
    (φ : LevySigma) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    φ.normalize.Realize M e ↔ φ.Realize M e := by
  have hω := omega_mem M hM hS hI
  have h0 := hM _ hω _ ZFSet.omega_zero
  induction φ generalizing e with
  | bounded φ => rfl
  | conj φ ψ ihφ ihψ => exact (SigmaFormula.realize_conj _ _ _ _).trans (and_congr (ihφ e he) (ihψ
    e he))
  | disj φ ψ ihφ ihψ => exact (SigmaFormula.realize_disj M h0 _ _ _).trans (or_congr (ihφ e he)
    (ihψ e he))
  | existsSet φ ih =>
    simp only [normalize,SigmaFormula.Realize,Realize]
    apply exists_congr; intro x
    apply and_congr_right; intro hx
    exact ih (cons x e) (by intro i; cases i <;> simp [cons,he,hx])
  | existsMem a φ ih =>
    rw [normalize,SigmaFormula.realize_existsMem]
    change (∃ x ∈ M, x ∈ e a ∧ _) ↔ ∃ x ∈ M, x ∈ e a ∧ _
    apply exists_congr; intro x
    apply and_congr_right; intro hx
    exact and_congr_right (fun _ => ih (cons x e) (by intro i; cases i <;> simp [cons,he,hx]))
  | allMem a φ ih =>
    rw [normalize,SigmaFormula.realize_allMem M hM hP hU hS hR hI hC _ _ _ he]
    change (∀ x ∈ e a, _) ↔ ∀ x ∈ M, x ∈ e a → _
    constructor
    · intro h x hx hxa
      exact (ih (cons x e) (by intro i; cases i <;> simp [cons,he,hx])).mp (h x hxa)
    · intro h x hxa
      have hx := hM _ (he a) x hxa
      exact (ih (cons x e) (by intro i; cases i <;> simp [cons,he,hx])).mpr (h x hx hxa)
end LevySigma

/-- The model admits separation for Levy-sigma formulas with model parameters. -/
def LevySigmaSeparation (M : ZFSet.{u}) : Prop :=
  ∀ (φ : LevySigma) (e : ℕ → ZFSet.{u}), (∀ i, e i ∈ M) → ∀ a ∈ M,
    ∃ b ∈ M, ∀ x ∈ M, x ∈ b ↔ x ∈ a ∧ φ.Realize M (cons x e)

/-- The model admits replacement for internally single-valued Levy-sigma relations with model
parameters. -/
def LevySigmaReplacement (M : ZFSet.{u}) : Prop :=
  ∀ (φ : LevySigma) (e : ℕ → ZFSet.{u}), (∀ i, e i ∈ M) → ∀ a ∈ M,
    (∀ x ∈ a, ∃ y ∈ M, φ.Realize M (cons y (cons x e)) ∧
      ∀ z ∈ M, φ.Realize M (cons z (cons x e)) → z = y) →
    ∃ b ∈ M, ∀ y ∈ M, y ∈ b ↔ ∃ x ∈ a, φ.Realize M (cons y (cons x e))

end TuringRigidity.BoundedSetTheory

end OAI
