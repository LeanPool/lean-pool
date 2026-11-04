/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Tarski.Operator
public import LeanPool.PointwiseComposition.Foundation.Vorspiel.Fin.Matrix

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

namespace FFL
namespace FirstOrder

namespace Semiformula

variable {L : Language} {ξ : Type*}

/--
`nestFormulae φ(x₁,…,xₙ) ![Ψ₁(x₁,y₁,…,yₘ), …, Ψₙ(xₙ,y₁,…,yₘ)]` is the formula `∀ x₁, …, xₙ
((Ψ₁(x₁,y₁,…,yₘ) ∧ … ∧ Ψₙ(xₙ,y₁,…,yₘ)) → φ(x₁,…,xₙ))`.

Here, each formula `Ψᵢ` has `m + 1` bound variables, one for expressing a predicate of an `xᵢ`,
and `m` remaining ones. In the resulting formula, the bound variables are the `m` remaining
bound variables, while all of the original `n` bound variables of `φ` get bounded to a `∀`
quantifier.

Intuitively, nestFormulae gives `R(f₁(y₁,…,yₘ), …, fₙ(y₁,…,yₘ))`, the result of substituting
functions `f₁, … fₙ` into a relation `R`, using the defining formulae of their graphs (`xᵢ =
fᵢ(y₁,…,yₘ)` iff `Ψᵢ(xᵢ,y₁,…,yₘ)`, and `R(x₁,…,xₙ)` iff `φ(x₁,…,xₙ)`). -/
def nestFormulae (φ : Semiformula L ξ n) (Ψ : Fin n → Semiformula L ξ (m + 1)) :
    Semiformula L ξ m :=
  let σ : Semiformula L ξ (m + n) :=
    (Matrix.conj fun i : Fin n ↦
        Rewriting.subst (Ψ i) (#((Fin.addCast m i)) :> fun j ↦ #(j.addNat n))) ⇒ₗ
      Rewriting.subst φ fun i ↦ #((Fin.addCast m i))
  ∀¹^[n] σ

/--
`nestFormulaeFunc φ(x,x₁,…,xₙ) ![Ψ₁(x₁,y₁,…,yₘ), …, Ψₙ(xₙ,y₁,…,yₘ)]` is the formula `∀ x₁, …, xₙ
((Ψ₁(x₁,y₁,…,yₘ) ∧ … ∧ Ψₙ(xₙ,y₁,…,yₘ)) → φ(x,x₁,…,xₙ))`.

Here, each formula `Ψᵢ` has `m + 1` bound variables, one for expressing a predicate of an `xᵢ`,
and `m` remaining ones. In the resulting formula, the bound variables are the `m` remaining
bound variables plus `x`, while all of the original bound variables `x₁,…,xₙ` get bounded to a
`∀` quantifier.

Intuitively, nestFormulaeFunc gives `F(f₁(y₁,…,yₘ), …, fₙ(y₁,…,yₘ))`, the result of substituting
functions `f₁, … fₙ` into a function `F`, using the defining formulae of their graphs (`xᵢ =
fᵢ(y₁,…,yₘ)` iff `Ψᵢ(xᵢ,y₁,…,yₘ)`, and `x = F(x₁,…,xₙ)` iff `φ(x,x₁,…,xₙ)`). -/
def nestFormulaeFunc (φ : Semiformula L ξ (n + 1)) (Ψ : Fin n → Semiformula L ξ (m + 1)) :
    Semiformula L ξ (m + 1) :=
  let σ : Semiformula L ξ ((m + 1) + n) :=
    (Matrix.conj fun i : Fin n ↦
        Rewriting.subst (Ψ i) (#((Fin.addCast m.succ i)) :> fun j ↦ #(j.succ.addNat n))) ⇒ₗ
      Rewriting.subst φ (#((0 : Fin (m + 1)).addNat n) :> fun i ↦ #((Fin.addCast m.succ i)))
  ∀¹^[n] σ

variable {M : Type*} [s : Tarski.Structure L M] {f : ξ → M}

lemma eval_nestFormulae {φ : Semiformula L ξ n} {Ψ : Fin n → Semiformula L ξ (m + 1)} :
    Eval e f (φ.nestFormulae Ψ) ↔
      ∀ v : Fin n → M, (∀ i, Eval (v i :> e) f (Ψ i)) → Eval v f φ :=
  by simp [nestFormulae, Matrix.comp_vecCons', Function.comp_def]

@[simp]
lemma eval_nestFormulae₀ {φ : Semiformula L ξ 0} :
    Eval e f (φ.nestFormulae ![]) ↔ Eval ![] f φ := by simp [eval_nestFormulae, Matrix.empty_eq]

@[simp]
lemma eval_nestFormulae₁ {φ : Semiformula L ξ 1} {ψ : Semiformula L ξ (m + 1)} :
    Eval e f (φ.nestFormulae ![ψ]) ↔ ∀ x : M, Eval (x :> e) f ψ → Eval ![x] f φ := by
  simp [eval_nestFormulae, Matrix.vecForall_iff, Matrix.empty_eq]

@[simp]
lemma eval_nestFormulae₂ {φ : Semiformula L ξ 2} {ψ₁ ψ₂ : Semiformula L ξ (m + 1)} :
    Eval e f (φ.nestFormulae ![ψ₁, ψ₂]) ↔
      ∀ x₁, Eval (x₁ :> e) f ψ₁ → ∀ x₂, Eval (x₂ :> e) f ψ₂ → Eval ![x₁, x₂] f φ :=
  by
  suffices
    (∀ x₁ x₂, Eval (x₁ :> e) f ψ₁ → Eval (x₂ :> e) f ψ₂ → Eval ![x₁, x₂] f φ) ↔
      ∀ x₁, Eval (x₁ :> e) f ψ₁ → ∀ x₂, Eval (x₂ :> e) f ψ₂ → Eval ![x₁, x₂] f φ
    by simpa [eval_nestFormulae, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_two]
  grind

@[simp]
lemma eval_nestFormulae₃ {φ : Semiformula L ξ 3} {ψ₁ ψ₂ ψ₃ : Semiformula L ξ (m + 1)} :
    Eval e f (φ.nestFormulae ![ψ₁, ψ₂, ψ₃]) ↔
      ∀ x₁,
        Eval (x₁ :> e) f ψ₁ →
          ∀ x₂, Eval (x₂ :> e) f ψ₂ → ∀ x₃, Eval (x₃ :> e) f ψ₃ → Eval ![x₁, x₂, x₃] f φ :=
  by
  suffices
    (∀ x₁ x₂ x₃,
        Eval (x₁ :> e) f ψ₁ →
          Eval (x₂ :> e) f ψ₂ → Eval (x₃ :> e) f ψ₃ → Eval ![x₁, x₂, x₃] f φ) ↔
      ∀ x₁,
        Eval (x₁ :> e) f ψ₁ →
          ∀ x₂, Eval (x₂ :> e) f ψ₂ → ∀ x₃, Eval (x₃ :> e) f ψ₃ → Eval ![x₁, x₂, x₃] f φ
    by simpa [eval_nestFormulae, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  grind

@[simp]
lemma eval_nestFormulae₄ {φ : Semiformula L ξ 4} {ψ₁ ψ₂ ψ₃ ψ₄ : Semiformula L ξ (m + 1)} :
    Eval e f (φ.nestFormulae ![ψ₁, ψ₂, ψ₃, ψ₄]) ↔
      ∀ x₁,
        Eval (x₁ :> e) f ψ₁ →
          ∀ x₂,
            Eval (x₂ :> e) f ψ₂ →
              ∀ x₃,
                Eval (x₃ :> e) f ψ₃ → ∀ x₄, Eval (x₄ :> e) f ψ₄ → Eval ![x₁, x₂, x₃, x₄] f φ :=
  by
  suffices
    (∀ x₁ x₂ x₃ x₄,
        Eval (x₁ :> e) f ψ₁ →
          Eval (x₂ :> e) f ψ₂ →
            Eval (x₃ :> e) f ψ₃ → Eval (x₄ :> e) f ψ₄ → Eval ![x₁, x₂, x₃, x₄] f φ) ↔
      (∀ x₁,
        Eval (x₁ :> e) f ψ₁ →
          ∀ x₂,
            Eval (x₂ :> e) f ψ₂ →
              ∀ x₃,
                Eval (x₃ :> e) f ψ₃ → ∀ x₄, Eval (x₄ :> e) f ψ₄ → Eval ![x₁, x₂, x₃, x₄] f φ)
    by simpa [eval_nestFormulae, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  grind

lemma eval_nestFormulaeFunc {φ : Semiformula L ξ (n + 1)}
    {Ψ : Fin n → Semiformula L ξ (m + 1)} :
    Eval (z :> e) f (φ.nestFormulaeFunc Ψ) ↔
      ∀ v : Fin n → M, (∀ i, Eval (v i :> e) f (Ψ i)) → Eval (z :> v) f φ :=
  by simp [nestFormulaeFunc, Matrix.comp_vecCons', Function.comp_def]

@[simp]
lemma eval_nestFormulaeFunc₀ {φ : Semiformula L ξ 1} :
    Eval (z :> e) f (φ.nestFormulaeFunc ![]) ↔ Eval ![z] f φ := by
  simp [eval_nestFormulaeFunc, Matrix.empty_eq]

@[simp]
lemma eval_nestFormulaeFunc₁ {φ : Semiformula L ξ 2} {ψ : Semiformula L ξ (m + 1)} :
    Eval (z :> e) f (φ.nestFormulaeFunc ![ψ]) ↔ ∀ x, Eval (x :> e) f ψ → Eval ![z, x] f φ := by
  simp [eval_nestFormulaeFunc, Matrix.vecForall_iff, Matrix.empty_eq]

@[simp]
lemma eval_nestFormulaeFunc₂ {φ : Semiformula L ξ 3} {ψ₁ ψ₂ : Semiformula L ξ (m + 1)} :
    Eval (z :> e) f (φ.nestFormulaeFunc ![ψ₁, ψ₂]) ↔
      ∀ x₁, Eval (x₁ :> e) f ψ₁ → ∀ x₂, Eval (x₂ :> e) f ψ₂ → Eval ![z, x₁, x₂] f φ :=
  by
  suffices
    (∀ x₁ x₂, Eval (x₁ :> e) f ψ₁ → Eval (x₂ :> e) f ψ₂ → Eval ![z, x₁, x₂] f φ) ↔
      ∀ x₁, Eval (x₁ :> e) f ψ₁ → ∀ x₂, Eval (x₂ :> e) f ψ₂ → Eval ![z, x₁, x₂] f φ
    by simpa [eval_nestFormulaeFunc, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_two]
  grind

@[simp]
lemma eval_nestFormulaeFunc₃ {φ : Semiformula L ξ 4} {ψ₁ ψ₂ ψ₃ : Semiformula L ξ (m + 1)} :
    Eval (z :> e) f (φ.nestFormulaeFunc ![ψ₁, ψ₂, ψ₃]) ↔
      ∀ x₁,
        Eval (x₁ :> e) f ψ₁ →
          ∀ x₂, Eval (x₂ :> e) f ψ₂ → ∀ x₃, Eval (x₃ :> e) f ψ₃ → Eval ![z, x₁, x₂, x₃] f φ :=
  by
  suffices
    (∀ x₁ x₂ x₃,
        Eval (x₁ :> e) f ψ₁ →
          Eval (x₂ :> e) f ψ₂ → Eval (x₃ :> e) f ψ₃ → Eval ![z, x₁, x₂, x₃] f φ) ↔
      ∀ x₁,
        Eval (x₁ :> e) f ψ₁ →
          ∀ x₂, Eval (x₂ :> e) f ψ₂ → ∀ x₃, Eval (x₃ :> e) f ψ₃ → Eval ![z, x₁, x₂, x₃] f φ
    by simpa [eval_nestFormulaeFunc, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  grind

@[simp]
lemma eval_nestFormulaeFunc₄ {φ : Semiformula L ξ 5} {ψ₁ ψ₂ ψ₃ ψ₄ : Semiformula L ξ (m + 1)} :
    Eval (z :> e) f (φ.nestFormulaeFunc ![ψ₁, ψ₂, ψ₃, ψ₄]) ↔
      ∀ x₁,
        Eval (x₁ :> e) f ψ₁ →
          ∀ x₂,
            Eval (x₂ :> e) f ψ₂ →
              ∀ x₃,
                Eval (x₃ :> e) f ψ₃ →
                  ∀ x₄, Eval (x₄ :> e) f ψ₄ → Eval ![z, x₁, x₂, x₃, x₄] f φ :=
  by
  suffices
    (∀ x₁ x₂ x₃ x₄,
        Eval (x₁ :> e) f ψ₁ →
          Eval (x₂ :> e) f ψ₂ →
            Eval (x₃ :> e) f ψ₃ → Eval (x₄ :> e) f ψ₄ → Eval ![z, x₁, x₂, x₃, x₄] f φ) ↔
      (∀ x₁,
        Eval (x₁ :> e) f ψ₁ →
          ∀ x₂,
            Eval (x₂ :> e) f ψ₂ →
              ∀ x₃,
                Eval (x₃ :> e) f ψ₃ → ∀ x₄, Eval (x₄ :> e) f ψ₄ → Eval ![z, x₁, x₂, x₃, x₄] f φ)
    by simpa [eval_nestFormulaeFunc, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  grind

end Semiformula

end FirstOrder
end FFL

end

end PointwiseComposition
