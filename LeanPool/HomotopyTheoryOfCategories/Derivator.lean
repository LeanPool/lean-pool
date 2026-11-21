/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.Opposites
public import Mathlib.CategoryTheory.PUnit
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Prederivators and the axioms Der2, Der3

A prederivator is a pseudofunctor `D : (Cat.{w, w})ᵒᵖ ⥤ᵖ Cat.{v₁, u₁}`, the opposite reversing
1-cells only (Groth 2013, *Derivators, pointed derivators and stable derivators*, Definition
1.1, with "strict" relaxed to "pseudo"). We define its values `value D J`, the restrictions
`restrict D F = F^*`, and the axioms `SatisfiesDer2` (isomorphisms are detected pointwise) and
`SatisfiesDer3` (every restriction has both adjoints) of Groth 2013, Definition 1.10.

This file contains definitions only. Der1, Der4, homotopy exact squares, Kan extensions, pointed
and stable derivators and the triangulated structure of Groth's Theorem 4.15 (roadmap 10.3–10.5)
are not formalised.

This is Layer 10.1–10.2 of the roadmap *Homotopy theory of small categories*.
-/

@[expose] public section

universe w v₁ u₁

namespace LeanPool.HomotopyTheoryOfCategories

open CategoryTheory Opposite

variable (D : Pseudofunctor (Cat.{w, w})ᵒᵖ Cat.{v₁, u₁})

/-- **Layer 10.1.** The value `D(J)` of a prederivator. -/
abbrev value (J : Type w) [SmallCategory J] : Cat.{v₁, u₁} := D.obj (op (Cat.of J))

/-- **Layer 10.1.** Restriction `F^* : D(K) ⥤ D(J)` along `F : J ⥤ K`. -/
abbrev restrict {J K : Type w} [SmallCategory J] [SmallCategory K] (F : J ⥤ K) :
    value D K ⟶ value D J :=
  D.map F.toCatHom.op

/-- **Layer 10.2.** Der2: isomorphisms are detected pointwise (Groth 2013, Definition 1.10). -/
def SatisfiesDer2 : Prop :=
  ∀ (J : Type w) [SmallCategory J] {X Y : value D J} (f : X ⟶ Y),
    (∀ j : J, IsIso ((restrict D (Functor.fromPUnit j :
      Discrete PUnit.{w + 1} ⥤ J)).toFunctor.map f)) → IsIso f

/-- **Layer 10.2.** Der3: every restriction has both adjoints (Groth 2013, Definition 1.10). -/
def SatisfiesDer3 : Prop :=
  ∀ {J K : Type w} [SmallCategory J] [SmallCategory K] (F : J ⥤ K),
    (restrict D F).toFunctor.IsLeftAdjoint ∧ (restrict D F).toFunctor.IsRightAdjoint


end LeanPool.HomotopyTheoryOfCategories
