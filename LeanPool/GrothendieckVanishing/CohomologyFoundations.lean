/-
Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import LeanPool.GrothendieckVanishing.AbelianSheaves
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Grothendieck abelian and Ext instances for abelian sheaves
-/

@[expose] public section

universe w' w v u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

instance : HasSeparator AddCommGrpCat.{u} where
  hasSeparator := by
    use AddCommGrpCat.of (ULift ℤ)
    intro A B f g h
    simp_all only [ObjectProperty.singleton_iff, AddCommGrpCat.ext_iff,
      AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply, forall_eq',
      ULift.forall]
    intro x
    specialize h (AddCommGrpCat.ofHom
      (AddMonoidHom.mk' (fun y ↦ y • x) fun y z ↦ by simp only [add_smul])) 1
    aesop

instance : IsGrothendieckAbelian.{u} AddCommGrpCat.{u} where

instance (X : TopCat.{u}) : IsGrothendieckAbelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (IsGrothendieckAbelian (CategoryTheory.Sheaf _ _))

instance instPreadditivePresheafLeanPool
    {C : Type*} [Category C] [Preadditive C] {X : TopCat.{u}} :
    Preadditive (TopCat.Presheaf C X) := by
  delta TopCat.Presheaf
  exact functorCategoryPreadditive

noncomputable instance sheafHasExt (X : TopCat.{u}) :
    HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} X))
