/-
Copyright (c) 2026 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import LeanPool.RigidDescent.Defs.Setting
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Phantom maps, pure monomorphisms, tensor powers, thick tensor ideals

Paper: Definitions 2.1 and 2.4, and the Conventions (`Thick^⊗(B)`).
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Opposite

universe v u

namespace RigidDescent

variable {T : Type u} [Category.{v} T] [Preadditive T]

section Purity

/-- Paper, Definition 2.1. A map `f` is *phantom* if `Hom(K, f) = 0` for every compact `K`.
Since compact objects are closed under shifts, this is the paper's `Hom(K, f)_* = 0`. -/
def IsPhantom {X Y : T} (f : X ⟶ Y) : Prop :=
  ∀ K : T, IsCompactObj K → ∀ k : K ⟶ X, k ≫ f = 0

/-- Paper, Definition 2.1. A map `f` is a *pure monomorphism* if `Hom(K, f)` is injective for
every compact `K`, stated as `Hom(K, f)` having zero kernel. -/
def IsPureMono {X Y : T} (f : X ⟶ Y) : Prop :=
  ∀ K : T, IsCompactObj K → ∀ k : K ⟶ X, k ≫ f = 0 → k = 0

end Purity

section TensorPowers

variable [MonoidalCategory T]

/-- The tensor powers `I^{⊗ n}`, with `I^{⊗ 0} = 𝟙` and `I^{⊗ (n+1)} = I ⊗ I^{⊗ n}`. -/
def tensorPow (I : T) : ℕ → T
  | 0 => 𝟙_ T
  | n + 1 => I ⊗ tensorPow I n

/-- The tensor powers `δ^{⊗ n} : I^{⊗ n} ⟶ 𝟙` of `δ : I ⟶ 𝟙`: `δ^{⊗ 0} = 𝟙`, and
`δ^{⊗ (n+1)}` is `δ ⊗ δ^{⊗ n}` followed by `𝟙 ⊗ 𝟙 ≅ 𝟙`. -/
def tensorPowHom {I : T} (δ : I ⟶ 𝟙_ T) : (n : ℕ) → tensorPow I n ⟶ 𝟙_ T
  | 0 => 𝟙 _
  | n + 1 => (δ ⊗ₘ tensorPowHom δ n) ≫ (λ_ (𝟙_ T)).hom

/-- Paper, Definition 2.4. With `I →δ 𝟙 → B → ΣI` the exact triangle of the unit of `B`,
`B` is *nil-pure* if `δ^{⊗ n}` is phantom for some `n ≥ 1`. It depends only on `δ`, so we
state it for `δ`.

We drop `n ≥ 1`. When `𝟙` is compact this changes nothing: if `δ^{⊗ 0} = 𝟙_𝟙` is phantom then
`𝟙 = 0`, so every `δ^{⊗ n}`, being a map into `𝟙`, is phantom. -/
def IsNilPure {I : T} (δ : I ⟶ 𝟙_ T) : Prop :=
  ∃ n, IsPhantom (tensorPowHom δ n)

end TensorPowers

section ThickTensorIdeal

variable [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T] [MonoidalCategory T]

/-- A *thick tensor ideal*: a triangulated subcategory (contains `0`, closed under shifts and
extensions) that is closed under retracts and under `W ⊗ -` for every `W`. -/
def IsThickTensorIdeal (P : ObjectProperty T) : Prop :=
  P.IsTriangulated ∧ P.IsStableUnderRetracts ∧ ∀ W M : T, P M → P (W ⊗ M)

/-- Paper, Conventions. `Thick^⊗(B)`, the smallest thick tensor ideal containing `B`:
`thickTensorIdeal B M` says `M ∈ Thick^⊗(B)`. -/
def thickTensorIdeal (B : T) : ObjectProperty T :=
  fun M => ∀ P : ObjectProperty T, IsThickTensorIdeal P → P B → P M

end ThickTensorIdeal

end RigidDescent
