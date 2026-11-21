/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Elements of pullbacks of presheaves of types

A pullback of presheaves of types is computed objectwise, so its elements at `e` are the pairs of
elements of the two factors with the same image (`LeanPool.ClassifyingTopoi.exists_pullback_app`,
`LeanPool.ClassifyingTopoi.pullback_ext_app`, `LeanPool.ClassifyingTopoi.pullback_condition_app`).
They are used both by the existence half of Diaconescu's theorem and by the local semantics in
sheaf topoi.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace LeanPool.ClassifyingTopoi

section PullbackElements

variable {E : Type u} [SmallCategory E] {X Y Z : Eᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z)

/-- Two elements of a pullback of presheaves with the same projections are equal. -/
theorem pullback_ext_app {e : Eᵒᵖ} {z z' : (pullback f g).obj e}
    (h₁ : (pullback.fst f g).app e z = (pullback.fst f g).app e z')
    (h₂ : (pullback.snd f g).app e z = (pullback.snd f g).app e z') : z = z' := by
  have hinj : Function.Injective (pullbackObjIso f g e).hom :=
    ((isIso_iff_bijective _).1 inferInstance).1
  apply hinj
  apply PullbackCone.IsLimit.type_ext (pullbackIsPullback (f.app e) (g.app e))
  · change ((pullbackObjIso f g e).hom ≫ pullback.fst _ _) z =
      ((pullbackObjIso f g e).hom ≫ pullback.fst _ _) z'
    rw [pullbackObjIso_hom_comp_fst]
    exact h₁
  · change ((pullbackObjIso f g e).hom ≫ pullback.snd _ _) z =
      ((pullbackObjIso f g e).hom ≫ pullback.snd _ _) z'
    rw [pullbackObjIso_hom_comp_snd]
    exact h₂

/-- A pair of elements with the same image is the pair of projections of an element of the
pullback. -/
theorem exists_pullback_app {e : Eᵒᵖ} {x : X.obj e} {y : Y.obj e} (h : f.app e x = g.app e y) :
    ∃ z : (pullback f g).obj e,
      (pullback.fst f g).app e z = x ∧ (pullback.snd f g).app e z = y := by
  let w := (Types.pullbackIsoPullback (f.app e) (g.app e)).inv ⟨⟨x, y⟩, h⟩
  refine ⟨(pullbackObjIso f g e).inv w, ?_, ?_⟩
  · change ((pullbackObjIso f g e).inv ≫ (pullback.fst f g).app e) w = x
    rw [pullbackObjIso_inv_comp_fst]
    exact Types.pullbackIsoPullback_inv_fst_apply _ _ _
  · change ((pullbackObjIso f g e).inv ≫ (pullback.snd f g).app e) w = y
    rw [pullbackObjIso_inv_comp_snd]
    exact Types.pullbackIsoPullback_inv_snd_apply _ _ _

/-- The commutativity of a pullback square, on elements. -/
theorem pullback_condition_app {e : Eᵒᵖ} (z : (pullback f g).obj e) :
    f.app e ((pullback.fst f g).app e z) = g.app e ((pullback.snd f g).app e z) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (pullback.condition (f := f) (g := g)) e) z

end PullbackElements

end LeanPool.ClassifyingTopoi
