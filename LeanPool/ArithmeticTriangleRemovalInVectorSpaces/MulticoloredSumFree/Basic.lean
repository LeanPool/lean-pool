/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic

/-!
# Multicolored sum-free families

A family of triples `(x i, y i, z i)` in an abelian group is multicolored sum-free if
`x i + y j + z k = 0` holds exactly when `i = j = k`.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree x y z`: the family of triples
  `(x i, y i, z i)` is multicolored sum-free.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.pi`: the coordinatewise power of a
  multicolored sum-free family, indexed by `κ → ι`, is multicolored sum-free.
* `ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.map`: the image of a multicolored
  sum-free family under an injective additive map is multicolored sum-free.
* `ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.comp`: a subfamily of a
  multicolored sum-free family is multicolored sum-free.
-/

@[expose] public section

namespace ArithmeticTriangleRemovalInVectorSpaces

variable {ι G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- A family of triples `(x i, y i, z i)` is multicolored sum-free if `x i + y j + z k = 0` holds
exactly when `i = j = k`. -/
def IsMulticoloredSumFree (x y z : ι → G) : Prop :=
  ∀ i j k, x i + y j + z k = 0 ↔ i = j ∧ j = k

namespace IsMulticoloredSumFree

variable {x y z : ι → G}

/-- The coordinatewise power of a multicolored sum-free family is multicolored sum-free. -/
lemma pi (h : IsMulticoloredSumFree x y z) (κ : Type*) :
    IsMulticoloredSumFree (fun (I : κ → ι) t ↦ x (I t)) (fun I t ↦ y (I t)) fun I t ↦ z (I t) := by
  intro I J K
  simp only [funext_iff, Pi.add_apply, Pi.zero_apply, h _ _ _]
  grind

/-- The image of a multicolored sum-free family under an injective additive map is multicolored
sum-free. -/
lemma map (h : IsMulticoloredSumFree x y z) (e : G →+ H) (he : Function.Injective e) :
    IsMulticoloredSumFree (e ∘ x) (e ∘ y) (e ∘ z) := by
  intro i j k
  rw [← h, Function.comp_apply, Function.comp_apply, Function.comp_apply, ← map_add, ← map_add,
    ← e.map_zero, he.eq_iff]

/-- A subfamily of a multicolored sum-free family, indexed through an injective map, is
multicolored sum-free. -/
lemma comp {κ : Type*} (h : IsMulticoloredSumFree x y z) {f : κ → ι} (hf : Function.Injective f) :
    IsMulticoloredSumFree (x ∘ f) (y ∘ f) (z ∘ f) := by
  intro i j k
  rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, h, hf.eq_iff, hf.eq_iff]

end IsMulticoloredSumFree

end ArithmeticTriangleRemovalInVectorSpaces
