/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.CategoryTheory.Comma.CardinalArrow
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# `κ`-small limits

We define, for a cardinal `κ : Cardinal.{w}`, the property `HasCardinalSmallLimits X κ` of a
category `X` (it has limits of all shapes `J : Type w` with fewer than `κ` arrows) and the
property `PreservesCardinalSmallLimits F κ` of a functor (it preserves such limits). These are
the conventions of target 0.1 of the Tau Ceti roadmap *Locally presentable categories*.
-/

@[expose] public section

namespace LeanPool.LocallyPresentableCategories

open CategoryTheory Limits

universe w v v' u u'

/-- A functor preserves `κ`-small limits: limits of every shape `J : Type w` with fewer than `κ`
morphisms. -/
def PreservesCardinalSmallLimits {X : Type u} [Category.{v} X] {Y : Type u'} [Category.{v'} Y]
    (F : X ⥤ Y) (κ : Cardinal.{w}) : Prop :=
  ∀ (J : Type w) [SmallCategory J], HasCardinalLT (Arrow J) κ → PreservesLimitsOfShape J F

/-- A category has `κ`-small limits: limits of every shape `J : Type w` with fewer than `κ`
morphisms. -/
def HasCardinalSmallLimits (X : Type u) [Category.{v} X] (κ : Cardinal.{w}) : Prop :=
  ∀ (J : Type w) [SmallCategory J], HasCardinalLT (Arrow J) κ → HasLimitsOfShape J X

end LeanPool.LocallyPresentableCategories
