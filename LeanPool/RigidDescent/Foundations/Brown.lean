/-
Copyright (c) 2026 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import LeanPool.RigidDescent.Foundations.Extension

/-!
# Brown representability

* `brown_representability`: on a compactly generated triangulated category, an additive
  cohomological functor `H : Tᵒᵖ ⥤ AddCommGrpCat` sending coproducts to products is
  representable. Take the cellular tower of `H` with respect to the shifted generators
  (`Foundations/CellularTower.lean`); the natural transformation `Hom(-, X∞) ⟶ H`,
  `a ↦ a^* u∞` (`yonedaElem`), is an isomorphism at every shifted generator, hence everywhere
  (`Foundations/Extension.lean`).
* `CompactlyGenerated.hasProducts`: paper, Conventions: a compactly generated triangulated
  category has small products [Nee01, Cor. 1.18]. For a family `Xⱼ`, the functor
  `∏ⱼ Hom(-, Xⱼ)` (`piYoneda`) is cohomological and sends coproducts to products, and an
  object representing it is a product.
-/

@[expose] public section

open CategoryTheory Limits Opposite Pretriangulated

universe v u

namespace RigidDescent

variable {T : Type u} [Category.{v} T] [Preadditive T]

/-- The natural transformation `Hom(-, X) ⟶ H` sending `a` to `a^* u`, for `u ∈ H(X)`. -/
noncomputable def yonedaElem (H : Tᵒᵖ ⥤ AddCommGrpCat.{v}) [H.Additive] {X : T}
    (u : H.obj (op X)) : preadditiveYoneda.obj X ⟶ H where
  app Y :=
    have h0 : H.map (0 : unop Y ⟶ X).op u = 0 := by
      rw [op_zero, H.map_zero]
      rfl
    have hadd : ∀ a b : unop Y ⟶ X, H.map (a + b).op u = H.map a.op u + H.map b.op u := by
      intro a b
      rw [op_add, H.map_add]
      rfl
    AddCommGrpCat.ofHom
      { toFun := fun (a : unop Y ⟶ X) => H.map a.op u
        map_zero' := h0
        map_add' := hadd }
  naturality Y Y' f := by
    ext a
    have : ∀ a : unop Y ⟶ X, H.map (f.unop ≫ a).op u = H.map f (H.map a.op u) := by
      intro a
      rw [op_comp, Quiver.Hom.op_unop, H.map_comp, ConcreteCategory.comp_apply]
    exact this a

/-- `∏ⱼ Hom(-, Xⱼ)`. -/
@[simps]
noncomputable def piYoneda {J : Type v} (Xs : J → T) : Tᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj Y := AddCommGrpCat.of (∀ j, unop Y ⟶ Xs j)
  map f := AddCommGrpCat.ofHom
    { toFun := fun a j => f.unop ≫ a j
      map_zero' := by funext j; simp
      map_add' := fun a b => by funext j; simp }

instance {J : Type v} (Xs : J → T) : (piYoneda Xs).Additive where
  map_add {Y Y' f g} := by
    ext a
    funext j
    change (f + g).unop ≫ a j = f.unop ≫ a j + g.unop ≫ a j
    rw [unop_add, Preadditive.add_comp]

section Triangulated

variable [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T]

lemma isCohomological_piYoneda {J : Type v} (Xs : J → T) : IsCohomological (piYoneda Xs) := by
  intro Tr hTr y hy
  have : ∀ j, ∃ z : Tr.obj₃ ⟶ Xs j, Tr.mor₂ ≫ z = y j := fun j => by
    obtain ⟨z, hz⟩ := Triangle.yoneda_exact₂ Tr hTr (y j) (congrFun hy j)
    exact ⟨z, hz.symm⟩
  choose z hz using this
  exact ⟨z, funext hz⟩

end Triangulated

lemma sendsCoproductsToProducts_piYoneda [HasCoproducts.{v} T] {J : Type v} (Xs : J → T) :
    SendsCoproductsToProducts (piYoneda Xs) := by
  intro I Y
  constructor
  · intro a b hab
    funext j
    exact Sigma.hom_ext _ _ fun i => congrFun (congrFun hab i) j
  · intro b
    exact ⟨fun j => Sigma.desc fun i => b i j,
      funext fun i => funext fun j => Sigma.ι_comp_desc _ _⟩

variable [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T] [CompactlyGenerated T]

open CompactlyGenerated

/-- **Brown representability.** An additive cohomological functor `H : Tᵒᵖ ⥤ AddCommGrpCat`
sending coproducts to products is representable: there are `X` and `u ∈ H(X)` such that
`a ↦ a^* u` is a bijection `Hom(Y, X) ≅ H(Y)` for every `Y`. -/
theorem brown_representability (H : Tᵒᵖ ⥤ AddCommGrpCat.{v}) [H.Additive]
    (hH : IsCohomological H) (hHc : SendsCoproductsToProducts H) :
    ∃ (X : T) (u : H.obj (op X)), ∀ Y : T, Function.Bijective fun a : Y ⟶ X => H.map a.op u := by
  obtain ⟨ct⟩ := CellularTower.nonempty hH hHc (isCompactObj_shiftedGen (T := T))
  refine ⟨ct.tel.obj, ct.u, fun Y => ?_⟩
  have := NatTrans.isIso_app_of_cohomological (isCohomological_preadditiveYoneda _) hH
    (sendsCoproductsToProducts_preadditiveYoneda _) hHc (yonedaElem H ct.u)
    (fun i n => (ConcreteCategory.isIso_iff_bijective _).2 (ct.bijective (i, n))) Y
  exact (ConcreteCategory.isIso_iff_bijective _).1 this

/-- Every family of objects has a limit fan, an object representing `∏ⱼ Hom(-, Xⱼ)`. -/
lemma exists_isLimit_fan {J : Type v} (Xs : J → T) : ∃ c : Fan Xs, Nonempty (IsLimit c) := by
  obtain ⟨P, u, hu⟩ := brown_representability (piYoneda Xs) (isCohomological_piYoneda Xs)
    (sendsCoproductsToProducts_piYoneda Xs)
  refine ⟨Fan.mk P u, ⟨Fan.IsLimit.mk _ (fun s => ((hu s.pt).2 s.proj).choose)
    (fun s j => congrFun ((hu s.pt).2 s.proj).choose_spec j) (fun s m hm => ?_)⟩⟩
  exact (hu s.pt).1 ((funext hm).trans ((hu s.pt).2 s.proj).choose_spec.symm)

/-- Paper, Conventions: a compactly generated triangulated category has small products
[Nee01, Cor. 1.18]. -/
instance CompactlyGenerated.hasProducts : HasProducts.{v} T :=
  hasProducts_of_limit_fans (fun Xs => (exists_isLimit_fan Xs).choose)
    (fun Xs => (exists_isLimit_fan Xs).choose_spec.some)

end RigidDescent
