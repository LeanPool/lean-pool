/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Group.End
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Non-singular presheaves and discrete fibrations

A presheaf `X` on a category `C` is *non-singular* (`Presheaf.IsNonsingular`) if, for every
element `x ∈ X(c)`, the map `(c' ⟶ c) → X(c')`, `u ↦ X(u)(x)`, is injective (compare Cisinski,
Astérisque 308, 8.2.2). We prove:

* `Presheaf.isNonsingular_iff_isThin`: `X` is non-singular iff its category of elements is thin;
* `Presheaf.isNonsingular_iff_mono`: on a small category, `X` is non-singular iff every map
  `yoneda c ⟶ X` classifying an element is a monomorphism;
* `isDiscreteFibration_elements`: the projection from the opposite of the category of elements
  of a presheaf is a discrete fibration (`Functor.IsDiscreteFibration`).

The comparison with Mathlib's `SSet.Nonsingular` for simplicial sets and the regularity results
of roadmap 9.2 are not formalised.

This is Layer 9 of the roadmap *Homotopy theory of small categories*.
-/

@[expose] public section

universe w v u

namespace LeanPool.HomotopyTheoryOfCategories

open CategoryTheory Opposite

variable {C : Type u} [Category.{v} C]

/-- **Layer 9.1.** A presheaf is non-singular if, for every element `x ∈ X(c)`, the map
`(c' ⟶ c) → X(c')`, `u ↦ X(u)(x)`, is injective. -/
def Presheaf.IsNonsingular (X : Cᵒᵖ ⥤ Type w) : Prop :=
  ∀ ⦃c c' : C⦄ (x : X.obj (op c)) (u v : c' ⟶ c), X.map u.op x = X.map v.op x → u = v

/-- **Layer 9.1.** A presheaf is non-singular iff its category of elements is thin. -/
theorem Presheaf.isNonsingular_iff_isThin (X : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsNonsingular X ↔ Quiver.IsThin X.Elements := by
  constructor
  · rintro h @⟨⟨c⟩, x⟩ @⟨⟨c'⟩, y⟩
    refine ⟨fun f g ↦ Functor.Elements.Hom.ext (Quiver.Hom.unop_inj ?_)⟩
    exact h x f.hom.unop g.hom.unop (f.map_val.trans g.map_val.symm)
  · intro h c c' x u v huv
    let f : X.elementsMk (op c) x ⟶ X.elementsMk (op c') (X.map u.op x) :=
      { hom := u.op, map_val := rfl }
    let g : X.elementsMk (op c) x ⟶ X.elementsMk (op c') (X.map u.op x) :=
      { hom := v.op, map_val := huv.symm }
    exact Quiver.Hom.op_inj (congrArg Functor.Elements.Hom.hom (Subsingleton.elim f g))

/-- **Layer 9.1.** A presheaf is non-singular iff every map from a representable classifying an
element is a monomorphism. -/
theorem Presheaf.isNonsingular_iff_mono {C : Type u} [SmallCategory C] (X : Cᵒᵖ ⥤ Type u) :
    Presheaf.IsNonsingular X ↔
      ∀ (c : C) (x : X.obj (op c)), Mono (yonedaEquiv.symm x) := by
  simp only [NatTrans.mono_iff_mono_app, mono_iff_injective]
  constructor
  · rintro h c x ⟨c'⟩ u v huv
    exact h x u v huv
  · intro h c c' x u v huv
    exact h c x (op c') huv

/-- **Layer 9.3.** A functor `p : E ⥤ C` is a discrete fibration if every morphism into `p.obj e`
lifts uniquely to a morphism into `e`. -/
def Functor.IsDiscreteFibration {E : Type*} [Category* E] (p : E ⥤ C) : Prop :=
  ∀ e : E, Function.Bijective
    (fun φ : (e' : E) × (e' ⟶ e) ↦ (⟨p.obj φ.1, p.map φ.2⟩ : (c : C) × (c ⟶ p.obj e)))

/-- **Layer 9.3.** The projection from the opposite of the category of elements of a presheaf is
a discrete fibration. -/
theorem isDiscreteFibration_elements (X : Cᵒᵖ ⥤ Type w) :
    Functor.IsDiscreteFibration (Functor.Elements.π X).leftOp := by
  rintro ⟨@⟨⟨c⟩, x⟩⟩
  constructor
  · rintro ⟨⟨@⟨⟨c₁⟩, x₁⟩⟩, ⟨⟨⟨u₁⟩, h₁⟩⟩⟩ ⟨⟨@⟨⟨c₂⟩, x₂⟩⟩, ⟨⟨⟨u₂⟩, h₂⟩⟩⟩ h
    simp only [Functor.leftOp_obj, Functor.Elements.π_obj, Functor.leftOp_map,
      Functor.Elements.π_map, Sigma.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain rfl : u₁ = u₂ := eq_of_heq h
    obtain rfl : x₁ = x₂ := h₁.symm.trans h₂
    rfl
  · rintro ⟨c', u⟩
    exact ⟨⟨op (X.elementsMk (op c') (X.map u.op x)),
      Quiver.Hom.op ({ hom := u.op, map_val := rfl } : X.elementsMk (op c) x ⟶ _)⟩, rfl⟩

end LeanPool.HomotopyTheoryOfCategories
