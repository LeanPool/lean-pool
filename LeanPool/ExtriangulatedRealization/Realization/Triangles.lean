/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Realization.Extensions
public import LeanPool.ExtriangulatedRealization.Triangulated.Reflect
public import LeanPool.ExtriangulatedRealization.Triangulated.Biproduct

/-!
# Realizations go to distinguished triangles (Proposition 2.3, Step 4)

The shadow functor `Γ` is fully faithful on the objects `e₀ X` of `K(Q)` with `X ∈ K(Q₀)` whose
image in `K(Rep k I)` is K-injective; these objects are stable under `⟦1⟧` and cones. The
realization functor sends `X`-free objects of `C_J` to such objects, and `Γ` sends the triangle of
a realization to the triangle of the short exact sequence `ρA → ρB → ρC` in the derived category.
So realizations between `X`-free objects go to distinguished triangles; in general the `X`-parts
split off as a direct sum with a split triangle.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel ZeroObject DerivedCategory
  Pretriangulated

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I]

attribute [local instance] HasDerivedCategory.standard

/-- The K-injective objects of `K(Rep k I)`. -/
abbrev kInj : ObjectProperty (HomotopyCategory (Rep k I) (ComplexShape.up ℤ)) :=
  (HomotopyCategory.subcategoryAcyclic (Rep k I)).rightOrthogonal

lemma kInj_resK (l : IntervalCat k I) :
    kInj ((ι₀.mapHomotopyCategory (ComplexShape.up ℤ)).obj (resK l)) :=
  CochainComplex.IsKInjective.rightOrthogonal (resRep l)

namespace RealizationData

variable {D : Iᵒᵖ ⥤ ModuleCat.{u} k} {J : Set I} (R : RealizationData D J)

/-- The objects `e₀ X` of `K(Q)` with `ι₀ X` K-injective, up to isomorphism. -/
def goodObj : ObjectProperty (HomotopyCategory R.Q (ComplexShape.up ℤ)) := fun T =>
  ∃ X : HomotopyCategory (Q₀ k I) (ComplexShape.up ℤ),
    kInj ((ι₀.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ∧
      Nonempty (T ≅ (R.e₀.mapHomotopyCategory (ComplexShape.up ℤ)).obj X)

lemma goodObj_shift {T : HomotopyCategory R.Q (ComplexShape.up ℤ)} (hT : R.goodObj T) :
    R.goodObj (T⟦(1 : ℤ)⟧) := by
  obtain ⟨X, hX, ⟨e⟩⟩ := hT
  refine ⟨X⟦(1 : ℤ)⟧, ?_, ⟨(shiftFunctor _ (1 : ℤ)).mapIso e ≪≫
    (((R.e₀.mapHomotopyCategory (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).app X).symm⟩⟩
  exact ObjectProperty.prop_of_iso _
    (((ι₀.mapHomotopyCategory (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).app X).symm
    (kInj.le_shift (1 : ℤ) _ hX)

lemma shadow_map_bijective_of_goodObj {T₁ T₂ : HomotopyCategory R.Q (ComplexShape.up ℤ)}
    (h₁ : R.goodObj T₁) (h₂ : R.goodObj T₂) :
    Function.Bijective (R.shadow.map : (T₁ ⟶ T₂) → _) := by
  obtain ⟨X₁, -, ⟨e₁⟩⟩ := h₁
  obtain ⟨X₂, hX₂, ⟨e₂⟩⟩ := h₂
  refine map_bijective_of_iso R.shadow e₁ e₂ ?_
  let e₀K := R.e₀.mapHomotopyCategory (ComplexShape.up ℤ)
  have he : Function.Bijective (e₀K.map : (X₁ ⟶ X₂) → _) :=
    ⟨e₀K.map_injective, e₀K.map_surjective⟩
  refine (Function.Bijective.of_comp_iff _ he).mp ?_
  have hcomp : R.shadow.map ∘ (e₀K.map : (X₁ ⟶ X₂) → _) = (Gfun k I).map :=
    funext fun φ => R.e₀_comp_shadow_map (X := X₁.as) (Y := X₂.as) φ
  rw [hcomp]
  have hι : Function.Bijective ((ι₀.mapHomotopyCategory (ComplexShape.up ℤ)).map :
      (X₁ ⟶ X₂) → _) :=
    ⟨(ι₀.mapHomotopyCategory _).map_injective, (ι₀.mapHomotopyCategory _).map_surjective⟩
  exact (ObjectProperty.rightOrthogonal.map_bijective_of_isTriangulated hX₂ Qh _).comp hι

lemma goodObj_cone {T₁ T₂ : HomotopyCategory R.Q (ComplexShape.up ℤ)} (f : T₁ ⟶ T₂)
    (h₁ : R.goodObj T₁) (h₂ : R.goodObj T₂) :
    ∃ (Z : HomotopyCategory R.Q (ComplexShape.up ℤ)) (g : T₂ ⟶ Z) (h : Z ⟶ T₁⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang _ ∧ R.goodObj Z := by
  obtain ⟨X₁, hX₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨X₂, hX₂, ⟨e₂⟩⟩ := h₂
  let e₀K := R.e₀.mapHomotopyCategory (ComplexShape.up ℤ)
  let ι₀K := (ι₀ (k := k) (I := I)).mapHomotopyCategory (ComplexShape.up ℤ)
  let g₀ : X₁ ⟶ X₂ := e₀K.preimage (e₁.inv ≫ f ≫ e₂.hom)
  obtain ⟨Z₀, g₁, h₁, hT₀⟩ := distinguished_cocone_triangle g₀
  have hZ₀ : kInj (ι₀K.obj Z₀) := by
    obtain ⟨Z', hZ', g', h', hT'⟩ := kInj.distinguished_cocone_triangle (ι₀K.map g₀) hX₁ hX₂
    let e := isoTriangleOfIso₁₂ _ _ hT' (ι₀K.map_distinguished _ hT₀) (Iso.refl _) (Iso.refl _)
      (by simp)
    exact ObjectProperty.prop_of_iso _ (Triangle.π₃.mapIso e) hZ'
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  refine ⟨Z, g, h, hT, Z₀, hZ₀, ?_⟩
  have hT₀' := e₀K.map_distinguished _ hT₀
  let a : Arrow.mk (Triangle.mk f g h).mor₁ ≅ Arrow.mk (e₀K.mapTriangle.obj
      (Triangle.mk g₀ g₁ h₁)).mor₁ :=
    Arrow.isoMk e₁ e₂ (by
      change e₁.hom ≫ e₀K.map g₀ = f ≫ e₂.hom
      simp [g₀])
  obtain ⟨e, -, -⟩ := exists_iso_of_arrow_iso _ _ hT hT₀' a
  exact ⟨Triangle.π₃.mapIso e⟩

/-! ### `X`-free objects -/

omit R in
lemma hom_to_X_eq_zero {M : CD D} (hM : XFree D M) (f : M ⟶ single D none) : f = 0 := by
  funext i j
  have key : ∀ (x : IndCat D), x.isSome → ∀ g : x ⟶ (show IndCat D from none), g = 0 := by
    rintro (_ | l) hx g
    · exact absurd hx (by simp)
    · exact Subsingleton.elim (α := PUnit) _ _
  exact key (M.X i) (hM i) (f i j)

omit R in
/-- Being `X`-free is invariant under isomorphism. -/
lemma XFree.of_iso {M N : CD D} (e : M ≅ N) (hN : XFree D N) : XFree D M := by
  intro i
  by_contra hi
  have hX : M.X i = none := Option.not_isSome_iff_eq_none.mp hi
  classical
  let f : M ⟶ single D none := fun i' _ =>
    if h : i' = i then eqToHom (h ▸ hX) else 0
  have hf : f = 0 := by
    rw [← Category.id_comp f, ← e.hom_inv_id, Category.assoc,
      hom_to_X_eq_zero hN (e.inv ≫ f), comp_zero]
  have h1 : f i PUnit.unit = eqToHom hX := dite_eq_left rfl
  have hne : ∀ (x : IndCat D) (hx : x = (show IndCat D from none)),
      (eqToHom hx : x ⟶ (show IndCat D from none)) ≠ 0 := by
    intro x hx h
    subst hx
    rw [eqToHom_refl] at h
    exact one_ne_zero (α := k) h
  exact hne _ hX (h1.symm.trans (congrFun (congrFun hf i) PUnit.unit))

variable (hR : R.IsCompatible)

lemma goodObj_realF {N : CDJ J D} (hN : ∀ i, (N.X i).isSome) :
    R.goodObj ((R.realF hR).obj N) := by
  let a : N.ι → IntervalJ (k := k) J := fun i => (N.X i).get (hN i)
  let Y : N.ι → HomotopyCategory (Q₀ k I) (ComplexShape.up ℤ) := fun i => resK (a i).obj
  let e₀K := R.e₀.mapHomotopyCategory (ComplexShape.up ℤ)
  let ι₀K := (ι₀ (k := k) (I := I)).mapHomotopyCategory (ComplexShape.up ℤ)
  refine ⟨⨁ Y, ?_, ⟨?_⟩⟩
  · refine ObjectProperty.prop_of_iso _ (ι₀K.mapBiproduct Y).symm ?_
    exact kInj.prop_of_isLimit_fan (biproduct.isLimit _) fun i => kInj_resK _
  · refine biproduct.mapIso (fun i => eqToIso (congrArg (R.F₁ hR).obj
      (Option.some_get (hN i)).symm)) ≪≫ (e₀K.mapBiproduct Y).symm

lemma goodObj_realP {M : (labelsIn D J).FullSubcategory} (hM : XFree D M.obj) :
    R.goodObj ((R.realP hR).obj M) := by
  apply R.goodObj_realF hR
  have h : XFree D ((cdjIncl J D).obj ((cdjEquiv J D).inverse.obj M)) :=
    XFree.of_iso ((labelsIn D J).ι.mapIso ((cdjEquiv J D).counitIso.app M)) hM
  intro i
  have := h i
  revert this
  change ((indJIncl J D).obj (((cdjEquiv J D).inverse.obj M).X i)).isSome → _
  generalize ((cdjEquiv J D).inverse.obj M).X i = x
  rcases x with _ | x
  · intro h; exact h
  · intro _; rfl

/-! ### The triangle of a realization -/

attribute [local instance] HasExt.standard

/-- The triangle `F A → F B → F C → (F A)⟦1⟧` attached to a sequence and an extension. -/
noncomputable def realTriangle {A B C : (labelsIn D J).FullSubcategory} (x : A ⟶ B) (y : B ⟶ C)
    (δ : (dataJ (D := D) (J := J)).Ext C A) : Triangle (HomotopyCategory R.Q (ComplexShape.up ℤ)) :=
  Triangle.mk ((R.realP hR).map x) ((R.realP hR).map y) (R.eta hR C A δ)

/-- `Γ` sends the triangle of a realization to the triangle of the short exact sequence
`ρA → ρB → ρC` in the derived category, which is distinguished. -/
lemma shadow_realTriangle_distinguished {A B C : (labelsIn D J).FullSubcategory} {x : A ⟶ B}
    {y : B ⟶ C} {δ : (dataJ (D := D) (J := J)).Ext C A} (w : x.hom ≫ y.hom = 0)
    (hS : (ShortComplex.mk ((rho D).map x.hom) ((rho D).map y.hom)
      (by rw [← Functor.map_comp, w, Functor.map_zero])).ShortExact) (hcls : hS.extClass = δ) :
    R.shadow.mapTriangle.obj (R.realTriangle hR x y δ) ∈ distTriang _ := by
  refine isomorphic_distinguished _ hS.singleTriangle_distinguished _
    (Triangle.isoMk _ _ ((R.shadowRealPIso hR).app A) ((R.shadowRealPIso hR).app B)
      ((R.shadowRealPIso hR).app C) ((R.shadowRealPIso hR).hom.naturality x)
      ((R.shadowRealPIso hR).hom.naturality y) ?_)
  change (R.shadow.map (R.eta hR C A δ) ≫ (R.shadow.commShiftIso (1 : ℤ)).hom.app _) ≫
      (((R.shadowRealPIso hR).app A).hom)⟦(1 : ℤ)⟧' =
    ((R.shadowRealPIso hR).app C).hom ≫ hS.singleδ
  rw [R.shadow_map_eta, etaTarget_apply, ← hS.extClass_hom, hcls]
  simp only [Category.assoc, Iso.app_inv, Iso.app_hom, Iso.inv_hom_id_app]
  erw [Category.id_comp, ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  exact congrArg _ (Category.comp_id _)

/-- A triangle between `X`-free objects of `C_J` whose image under `Γ` is distinguished is
distinguished. -/
lemma realTriangle_distinguished_of_xFree {A B C : (labelsIn D J).FullSubcategory} (x : A ⟶ B)
    (y : B ⟶ C) (δ : (dataJ (D := D) (J := J)).Ext C A) (hA : XFree D A.obj)
    (hB : XFree D B.obj) (hC : XFree D C.obj)
    (hΓ : R.shadow.mapTriangle.obj (R.realTriangle hR x y δ) ∈ distTriang _) :
    R.realTriangle hR x y δ ∈ distTriang _ :=
  reflect_distinguished R.shadow R.goodObj (fun f h₁ h₂ => R.goodObj_cone f h₁ h₂)
    (fun _ hX => R.goodObj_shift hX) (fun _ _ hX hY => R.shadow_map_bijective_of_goodObj hX hY)
    _ (R.goodObj_realP hR hA) (R.goodObj_realP hR hB) (R.goodObj_realP hR hC) hΓ

end RealizationData

end ExtriangulatedRealization
