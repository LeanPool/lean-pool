/-
Copyright (c) 2026 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import LeanPool.RigidDescent.Defs.Purity
public import LeanPool.RigidDescent.Defs.Holim
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Descent and effective descent type

Paper, Definition 1.1. As in the paper, `I →δ 𝟙 →η B → ΣI` is the exact triangle of the unit
of `B`. Descent type depends only on `δ`, so we state it for `δ`; effective descent type
depends only on `B`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated ZeroObject

universe v u

namespace RigidDescent

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [MonoidalCategory T]

/-- The tower `{I^{⊗ n} ⊗ X}_{n ≥ 0}`, with transition maps `δ ⊗ I^{⊗ n} ⊗ X` (followed by
`𝟙 ⊗ I^{⊗ n} ≅ I^{⊗ n}`). -/
noncomputable def tensorPowTower {I : T} (δ : I ⟶ 𝟙_ T) (X : T) : ℕᵒᵖ ⥤ T :=
  Functor.ofOpSequence (X := fun n => tensorPow I n ⊗ X)
    fun n => (δ ▷ tensorPow I n ≫ (λ_ (tensorPow I n)).hom) ▷ X

variable [HasCountableProducts T]

/-- Paper, Definition 1.1. `B` is *of descent type* if `holim_n (I^{⊗ n} ⊗ X) = 0` for every
`X`, stated as: `0` is a homotopy limit (homotopy limits are unique up to isomorphism).
Equivalently, `1 - shift` is an isomorphism of `∏ I^{⊗ n} ⊗ X`. -/
def IsDescentType {I : T} (δ : I ⟶ 𝟙_ T) : Prop :=
  ∀ X : T, IsHolim (tensorPowTower δ X) 0 0

/-- Paper, Definition 1.1. `B` is *of effective descent type* if `B ⊗ X = 0` implies `X = 0`,
and `B ⊗ -` preserves the homotopy limit of every tower `Y` with `B ⊗ Y` pro-constant: if
`(L, p)` is a homotopy limit of `Y`, then `(B ⊗ L, B ⊗ p)` is one of `B ⊗ Y`.

The paper instead asks that the unique map `τ : B ⊗ L ⟶ holim (B ⊗ Y)` compatible with the
projections be an isomorphism. The two agree by Lemma 3.3, since both sides are then limits
of `B ⊗ Y`. -/
def IsEffectiveDescentType (B : T) : Prop :=
  (∀ X : T, IsZero (B ⊗ X) → IsZero X) ∧
  ∀ Y : ℕᵒᵖ ⥤ T, IsProConstant (Y ⋙ tensorLeft B) →
    ∀ (L : T) (p : ∀ m : ℕ, L ⟶ Y.obj (op m)), IsHolim Y L p →
    IsHolim (Y ⋙ tensorLeft B) (B ⊗ L) fun m => B ◁ p m

end RigidDescent
