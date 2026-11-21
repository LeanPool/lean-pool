/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Opposites

/-!
# Morita equivalence of small categories

Two small categories are *Morita equivalent* when their presheaf topoi are equivalent. This is
the notion the bridges of this project are read along: an invariant of the presheaf topos, read
on two Morita-equivalent categories, gives a correspondence between properties of the two.
-/

@[expose] public section

namespace LeanPool.ToposTheoreticBridges

open CategoryTheory

universe u

/-- Two small categories are Morita equivalent when their presheaf topoi are equivalent. -/
def MoritaEquivalentCat (C D : Type u) [SmallCategory C] [SmallCategory D] : Prop :=
  Nonempty ((Cᵒᵖ ⥤ Type u) ≌ (Dᵒᵖ ⥤ Type u))

namespace MoritaEquivalentCat

theorem refl (C : Type u) [SmallCategory C] : MoritaEquivalentCat C C :=
  ⟨CategoryTheory.Equivalence.refl⟩

theorem symm {C D : Type u} [SmallCategory C] [SmallCategory D] (h : MoritaEquivalentCat C D) :
    MoritaEquivalentCat D C :=
  h.elim fun e => ⟨e.symm⟩

theorem trans {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (h : MoritaEquivalentCat C D) (h' : MoritaEquivalentCat D E) : MoritaEquivalentCat C E :=
  h.elim fun e => h'.elim fun e' => ⟨e.trans e'⟩

end MoritaEquivalentCat

end LeanPool.ToposTheoreticBridges
