/-
Copyright (c) 2026 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Tactic.TypeStar

/-!
# Towers and pro-constancy

Paper, Conventions. A *tower* in `S` is a functor `ℕᵒᵖ ⥤ S`, i.e. a sequence
`⋯ → Y₂ → Y₁ → Y₀`. We don't build the pro-category `Pro(S)`; instead we say directly when a
level map `cst U → Y` is an isomorphism in `Pro(S)`.

## Why `IsProIso` is the paper's notion

In `Pro(S)`, maps out of a constant tower are compatible families,
`Hom(cst U, Y) = lim_m Hom(U, Y_m)` (the dual of [KS06, (2.6.4)]), and maps into one are germs,
`Hom(Y, cst U) = colim_k Hom(Y_k, U)`. So a level map `u : cst U → Y` is an isomorphism in
`Pro(S)` exactly when there is some `v : Y_k → U` with

* `v ∘ u_k = 1_U` (`cst U → Y → cst U` is the identity), and
* for every `m`, some `k' ≥ k, m` with `u_m ∘ v ∘ t_{k'k} = t_{k'm}` (`Y → cst U → Y` is the
  identity at level `m`, far enough up the tower).

Every isomorphism `cst U ≅ Y` in `Pro(S)` is represented by a level map, so `IsProConstant`
is the paper's pro-constancy.
-/

@[expose] public section

open CategoryTheory Opposite

namespace RigidDescent

variable {S : Type*} [Category S]

/-- The transition map `Y_{m'} ⟶ Y_m` of a tower, for `m ≤ m'`. -/
abbrev Tower.t (Y : ℕᵒᵖ ⥤ S) {m m' : ℕ} (h : m ≤ m') : Y.obj (op m') ⟶ Y.obj (op m) :=
  Y.map (homOfLE h).op

/-- The level map `u : cst U ⟶ Y`, with components `u.app (op m) : U ⟶ Y_m`, is an
isomorphism in `Pro(S)` (see the module docstring). -/
def IsProIso {Y : ℕᵒᵖ ⥤ S} {U : S} (u : (Functor.const ℕᵒᵖ).obj U ⟶ Y) : Prop :=
  ∃ (k : ℕ) (v : Y.obj (op k) ⟶ U), u.app (op k) ≫ v = 𝟙 U ∧
    ∀ m : ℕ, ∃ (k' : ℕ) (hk : k ≤ k') (hm : m ≤ k'),
      Tower.t Y hk ≫ v ≫ u.app (op m) = Tower.t Y hm

/-- A tower is *pro-constant* if it is isomorphic in `Pro(S)` to a constant tower. -/
def IsProConstant (Y : ℕᵒᵖ ⥤ S) : Prop :=
  ∃ (U : S) (u : (Functor.const ℕᵒᵖ).obj U ⟶ Y), IsProIso u

end RigidDescent
