/-
Copyright (c) 2026 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import LeanPool.RigidDescent.Defs.Tower
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Limits.Shapes.Countable

/-!
# Homotopy limits of towers

Paper, Conventions: a homotopy limit of a tower `Y` is an object `holim Y` with maps
`p_m : holim Y → Y_m` fitting into an exact triangle `holim Y → ∏ Y_m → ∏ Y_m → Σ holim Y`
whose first map is `(p_m)` and whose second is `1 - shift` [Stacks, Tag 08TC]. Homotopy limits
are not functorial, so we define the property of being one.

This needs countable products, as in the paper. For compactly generated `T` they come from
`CompactlyGenerated.hasProducts`.
-/

@[expose] public section

open CategoryTheory Limits Opposite Pretriangulated

universe v u

namespace RigidDescent

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [HasCountableProducts T]

/-- The map `1 - shift : ∏ Y_m ⟶ ∏ Y_m`, whose `m`-th component is
`pr_m - t_{m+1,m} ∘ pr_{m+1}`. -/
noncomputable def oneSubShift (Y : ℕᵒᵖ ⥤ T) :
    (∏ᶜ fun m : ℕ => Y.obj (op m)) ⟶ ∏ᶜ fun m : ℕ => Y.obj (op m) :=
  𝟙 _ - Pi.lift fun m => Pi.π (fun m : ℕ => Y.obj (op m)) (m + 1) ≫ Tower.t Y (Nat.le_succ m)

/-- `L`, with the maps `p m : L ⟶ Y_m`, is a homotopy limit of `Y`: there is a distinguished
triangle `L ⟶ ∏ Y_m ⟶ ∏ Y_m ⟶ L⟦1⟧` whose first map is `(p m)_m` and whose second is
`1 - shift`. -/
def IsHolim (Y : ℕᵒᵖ ⥤ T) (L : T) (p : ∀ m : ℕ, L ⟶ Y.obj (op m)) : Prop :=
  ∃ e : (∏ᶜ fun m : ℕ => Y.obj (op m)) ⟶ L⟦(1 : ℤ)⟧,
    Triangle.mk (Pi.lift p) (oneSubShift Y) e ∈ distTriang T

end RigidDescent
