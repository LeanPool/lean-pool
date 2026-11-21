/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Functor
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.WalkingPair
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Group.End
import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# Presheaves on a small category, `i_A ⊣ i_A^*` and test categories

For a small category `A` and a presheaf `X : Aᵒᵖ ⥤ Type u`, `i_A X := A/X` is the category
`CostructuredArrow yoneda X`; `iAFunctor A : Â ⥤ Cat` is Mathlib's `CostructuredArrow.functor
yoneda`, and `iAStarFunctor A : Cat ⥤ Â` sends `C` to `a ↦ (Over a ⥤ C)`, with restriction along
`Over.map`. We construct the adjunction `iAAdjunction A : iAFunctor A ⊣ iAStarFunctor A` and
prove `nonempty_iAAdjunction`.

The bijection `(A/X ⥤ C) ≃ (X ⟶ i_A^* C)` sends `Φ` to `x ↦ Φ ∘ overToIA X x`, where
`overToIA X x : Over a ⥤ A/X` is `(b → a) ↦ (b, x|_b)`, and `τ` to the functor
`(a, x) ↦ τ_a(x)(𝟙_a)`; its action on morphisms (`overTransport`) transports along the
naturality equation `τ_a(X(f) y) = τ_b(y) ∘ Over.map f`. The inverse laws are checked with
`Functor.ext`, writing every `eqToHom` as the image of an `eqToHom` of `Over a` or of `A/X`.
`iAFunctor` is an `abbrev` (the roadmap has a `def`) so that `A/X` and `↑(iAFunctor A).obj X` are
identified by instance unification.

We also define the weak equivalences of presheaves `presheafWeq A W = i_A⁻¹ W` and, following
Maltsiniotis (2009, §2.3), weak test, local test, test and strict test categories. That `Δ` is a
strict test category (roadmap 6.4) needs the identification `W∞ = W_N` of Layer 4 and is not
formalised; nor are the properties of `W_Â` stated in roadmap 3.2–3.3.

This is Layers 3.1–3.2 and 6.1 of the roadmap *Homotopy theory of small categories*.
-/

@[expose] public section

universe u

namespace LeanPool.HomotopyTheoryOfCategories

open CategoryTheory CategoryTheory.Limits Opposite

/-- If `e : P = P'`, composing `F.map φ` with `eqToHom` on the left is `F` of the composite. -/
lemma eqToHom_comp_map {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E) {P P' Q : D}
    (e : P = P') (φ : P' ⟶ Q) (p : F.obj P = F.obj P') :
    eqToHom p ≫ F.map φ = F.map (eqToHom e ≫ φ) := by
  subst e; simp

/-- If `e : Q = Q'`, composing `F.map φ` with `eqToHom` on the right is `F` of the composite. -/
lemma map_comp_eqToHom {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E) {P Q Q' : D}
    (e : Q = Q') (φ : P ⟶ Q) (p : F.obj Q = F.obj Q') :
    F.map φ ≫ eqToHom p = F.map (φ ≫ eqToHom e) := by
  subst e; simp

section Presheaf

variable (A : Type u) [SmallCategory A]

/-- **Layer 3.1.** `i_A X = A/X`, the category `CostructuredArrow yoneda X`. -/
abbrev iA (X : Aᵒᵖ ⥤ Type u) : Type u := CostructuredArrow yoneda X

/-- **Layer 3.1.** `i_A : Â ⥤ Cat`, `X ↦ A/X`, functorial through `CostructuredArrow.map`. -/
abbrev iAFunctor : (Aᵒᵖ ⥤ Type u) ⥤ Cat.{u, u} :=
  CostructuredArrow.functor yoneda

/-- **Layer 3.1.** `i_A^* : Cat ⥤ Â`, `C ↦ (a ↦ (Over a ⥤ C))`, with restriction along
`Over.map`. -/
def iAStarFunctor : Cat.{u, u} ⥤ (Aᵒᵖ ⥤ Type u) :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.mapFunctor A).op

variable {A}

section
variable {C : Cat.{u, u}}

/-- The morphism `G(𝟙_a) ⟶ H(𝟙_b)` induced by `f : a ⟶ b` when `G = H ∘ Over.map f`. -/
def overTransport {a b : A} (f : a ⟶ b) (G : Cat.of (Over a) ⟶ C) (H : Cat.of (Over b) ⟶ C)
    (h : G = (Over.map f).toCatHom ≫ H) :
    G.toFunctor.obj (Over.mk (𝟙 a)) ⟶ H.toFunctor.obj (Over.mk (𝟙 b)) :=
  eqToHom (by rw [h]; rfl) ≫
    H.toFunctor.map (Over.homMk f (by simp) : Over.mk (𝟙 a ≫ f) ⟶ Over.mk (𝟙 b))

/-- `overTransport` along an identity is the identity. -/
lemma overTransport_id {a : A} (G : Cat.of (Over a) ⟶ C) (h : G = (Over.map (𝟙 a)).toCatHom ≫ G) :
    overTransport (𝟙 a) G G h = 𝟙 _ := by
  have e : (Over.mk (𝟙 a ≫ 𝟙 a)) = Over.mk (𝟙 a) := by simp
  have : (Over.homMk (𝟙 a) (by simp) : Over.mk (𝟙 a ≫ 𝟙 a) ⟶ Over.mk (𝟙 a)) = eqToHom e := by
    ext; simp
  rw [overTransport, this, eqToHom_map, eqToHom_trans, eqToHom_refl]

/-- `overTransport` is compatible with composition. -/
lemma overTransport_comp {a b c : A} (f : a ⟶ b) (g : b ⟶ c) (G : Cat.of (Over a) ⟶ C)
    (H : Cat.of (Over b) ⟶ C) (K : Cat.of (Over c) ⟶ C)
    (hf : G = (Over.map f).toCatHom ≫ H) (hg : H = (Over.map g).toCatHom ≫ K)
    (hfg : G = (Over.map (f ≫ g)).toCatHom ≫ K) :
    overTransport (f ≫ g) G K hfg = overTransport f G H hf ≫ overTransport g H K hg := by
  subst hf hg
  have e : Over.mk ((𝟙 a ≫ f) ≫ g) = Over.mk (𝟙 a ≫ f ≫ g) := by simp
  simp only [overTransport]
  rw [eqToHom_comp_map K.toFunctor e, eqToHom_comp_map K.toFunctor rfl,
    eqToHom_comp_map ((Over.map g).toCatHom ≫ K).toFunctor rfl]
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_map, ← Functor.map_comp]
  congr 1
  apply Over.OverMorphism.ext
  simp

/-- `Over.map u` sends `𝟙 a` to `u`. -/
lemma over_map_obj_mk_id {a c : A} (u : a ⟶ c) : (Over.map u).obj (Over.mk (𝟙 a)) = Over.mk u :=
  congrArg Over.mk (Category.id_comp u)

/-- `overTransport` between two restrictions of one functor `T` is `T` applied to `Over.homMk`. -/
lemma overTransport_eq {a b c : A} (u : a ⟶ c) (v : b ⟶ c) (ψ : a ⟶ b) (hψ : ψ ≫ v = u)
    (T : Cat.of (Over c) ⟶ C) (G : Cat.of (Over a) ⟶ C) (H : Cat.of (Over b) ⟶ C)
    (hG : G = (Over.map u).toCatHom ≫ T) (hH : H = (Over.map v).toCatHom ≫ T)
    (h : G = (Over.map ψ).toCatHom ≫ H) :
    overTransport ψ G H h =
      eqToHom (by subst hG; exact congrArg T.toFunctor.obj (over_map_obj_mk_id u)) ≫
      T.toFunctor.map (Over.homMk ψ hψ : Over.mk u ⟶ Over.mk v) ≫
        eqToHom (by subst hH; exact congrArg T.toFunctor.obj (over_map_obj_mk_id v).symm) := by
  subst hG hH
  have e : Over.mk (𝟙 a ≫ u) = Over.mk u := by simp
  have e' : Over.mk v = Over.mk (𝟙 b ≫ v) := by simp
  simp only [overTransport, Cat.Hom.comp_toFunctor, Functor.comp_map]
  rw [eqToHom_comp_map T.toFunctor ?e1, map_comp_eqToHom T.toFunctor ?e2,
    eqToHom_comp_map T.toFunctor ?e3]
  case e1 => exact congrArg Over.mk (by simp [hψ])
  case e2 => exact congrArg Over.mk (by simp)
  case e3 => exact congrArg Over.mk (by simp)
  congr 1
  apply Over.OverMorphism.ext
  simp

end

variable (X : Aᵒᵖ ⥤ Type u) (C : Cat.{u, u})

/-- The functor `Over a ⥤ A/X` attached to `x ∈ X(a)`. -/
@[simps]
def overToIA {a : A} (x : X.obj (op a)) : Over a ⥤ CostructuredArrow yoneda X where
  obj g := CostructuredArrow.mk (yoneda.map g.hom ≫ yonedaEquiv.symm x)
  map φ := CostructuredArrow.homMk φ.left (by
    dsimp
    rw [← Category.assoc, ← yoneda.map_comp, Over.w φ])

variable {X} in
/-- `overToIA` is natural: restricting `x` along `g` is precomposing with `Over.map g`. -/
lemma overToIA_naturality {a b : A} (g : b ⟶ a) (x : X.obj (op a)) :
    overToIA X (X.map g.op x) = Over.map g ⋙ overToIA X x :=
  CategoryTheory.Functor.ext_of_iso
    (NatIso.ofComponents (fun P ↦ CostructuredArrow.isoMk (Iso.refl _) (by
      change yoneda.map (𝟙 _) ≫ yoneda.map (P.hom ≫ g) ≫ yonedaEquiv.symm x =
        yoneda.map P.hom ≫ yonedaEquiv.symm (X.map g.op x)
      rw [← yonedaEquiv_symm_naturality_left]
      simp)) (fun φ ↦ by
        apply CostructuredArrow.hom_ext
        exact (Category.comp_id _).trans (Category.id_comp _).symm))
    (fun P ↦ by simp [← yonedaEquiv_symm_naturality_left])
    (fun P ↦ by
      apply CostructuredArrow.hom_ext
      simp only [CostructuredArrow.eqToHom_left]
      rfl)

variable {X C}

/-- The bijection `(A/X ⥤ C) → (X ⟶ i_A^* C)`, `Φ ↦ (x ↦ Φ ∘ overToIA X x)`. -/
def iAHomEquivFun (Φ : (iAFunctor A).obj X ⟶ C) : X ⟶ (iAStarFunctor A).obj C where
  app a := ↾fun x ↦ (overToIA X (a := a.unop) x).toCatHom ≫ Φ
  naturality a b f := by
    ext x
    change (overToIA X (X.map f x)).toCatHom ≫ Φ = (Over.map f.unop).toCatHom ≫
      (overToIA X x).toCatHom ≫ Φ
    rw [show f = f.unop.op from rfl, overToIA_naturality]
    rfl

/-- The naturality of `τ` at a morphism of `A/X`. -/
lemma app_eq_overMap_comp (τ : X ⟶ (iAStarFunctor A).obj C) {P Q : CostructuredArrow yoneda X}
    (φ : P ⟶ Q) :
    τ.app (op P.left) (yonedaEquiv P.hom) =
      (Over.map φ.left).toCatHom ≫ τ.app (op Q.left) (yonedaEquiv Q.hom) := by
  have h : yonedaEquiv P.hom = X.map φ.left.op (yonedaEquiv Q.hom) := by
    rw [yonedaEquiv_naturality, CostructuredArrow.w φ]
  rw [h]
  exact NatTrans.naturality_apply τ φ.left.op _

/-- The bijection `(X ⟶ i_A^* C) → (A/X ⥤ C)`, `τ ↦ ((a, x) ↦ τ_a(x)(𝟙_a))`. -/
def iAHomEquivInv (τ : X ⟶ (iAStarFunctor A).obj C) : (iAFunctor A).obj X ⟶ C :=
  Functor.toCatHom
  { obj P := (τ.app (op P.left) (yonedaEquiv P.hom)).toFunctor.obj (Over.mk (𝟙 _))
    map φ := overTransport φ.left _ _ (app_eq_overMap_comp τ φ)
    map_id _ := overTransport_id _ _
    map_comp _ _ := overTransport_comp _ _ _ _ _ _ _ _ }

/-- `overTransport` between two functors factoring through `Φ` is `Φ` of a morphism. -/
lemma overTransport_comp_right {D : Cat.{u, u}} {a b : A} (f : a ⟶ b) (ι₁ : Over a ⥤ D)
    (ι₂ : Over b ⥤ D) (Φ : D ⟶ C)
    (h : ι₁.toCatHom ≫ Φ = (Over.map f).toCatHom ≫ ι₂.toCatHom ≫ Φ)
    (e : ι₁.obj (Over.mk (𝟙 a)) = ι₂.obj ((Over.map f).obj (Over.mk (𝟙 a)))) :
    overTransport f (ι₁.toCatHom ≫ Φ) (ι₂.toCatHom ≫ Φ) h =
      Φ.toFunctor.map (eqToHom e ≫ ι₂.map (Over.homMk f (by simp) :
        Over.mk (𝟙 a ≫ f) ⟶ Over.mk (𝟙 b))) := by
  rw [← eqToHom_comp_map _ e]
  rfl

/-- The left part of `eqToHom e ≫ m` in `A/X`. -/
lemma costructuredArrow_eqToHom_comp_left {P P' Q : CostructuredArrow yoneda X} (e : P = P')
    (m : P' ⟶ Q) :
    (eqToHom e ≫ m).left = eqToHom (congrArg CostructuredArrow.left e) ≫ m.left := by
  subst e; simp

/-- `iAHomEquivInv` is a left inverse of `iAHomEquivFun`. -/
lemma iAHomEquivInv_fun (Φ : (iAFunctor A).obj X ⟶ C) : iAHomEquivInv (iAHomEquivFun Φ) = Φ := by
  ext : 1
  refine CategoryTheory.Functor.ext_of_iso
    (NatIso.ofComponents (fun P ↦ Φ.toFunctor.mapIso (CostructuredArrow.isoMk (Iso.refl _) ?_))
      (fun {P Q} φ ↦ ?_)) (fun P ↦ ?_) (fun P ↦ ?_)
  · change yoneda.map (𝟙 P.left) ≫ P.hom =
      yoneda.map (𝟙 P.left) ≫ yonedaEquiv.symm (yonedaEquiv P.hom)
    simp
  · refine Eq.trans (congrArg (· ≫ _) (overTransport_comp_right (D := (iAFunctor A).obj X) φ.left
      (overToIA X (yonedaEquiv P.hom)) (overToIA X (yonedaEquiv Q.hom))
      Φ (app_eq_overMap_comp (iAHomEquivFun Φ) φ) ?e)) ?_
    case e =>
      refine CostructuredArrow.obj_ext _ _ rfl ?_
      change yoneda.map (𝟙 _) ≫ yoneda.map (𝟙 _ ≫ φ.left) ≫ yonedaEquiv.symm (yonedaEquiv Q.hom) =
        yoneda.map (𝟙 _) ≫ yonedaEquiv.symm (yonedaEquiv P.hom)
      simpa using CostructuredArrow.w φ
    refine ((Φ.toFunctor.map_comp _ _).symm.trans ?_).trans (Φ.toFunctor.map_comp _ _)
    congr 1
    apply CostructuredArrow.hom_ext
    refine (CostructuredArrow.comp_left _ _).trans
      (Eq.trans ?_ (CostructuredArrow.comp_left _ _).symm)
    refine (congrArg (· ≫ _) (costructuredArrow_eqToHom_comp_left _ _)).trans ?_
    change (𝟙 _ ≫ φ.left) ≫ 𝟙 _ = 𝟙 _ ≫ φ.left
    simp
  · exact congrArg Φ.toFunctor.obj (CostructuredArrow.obj_ext _ _ rfl (by
      change yoneda.map (𝟙 _) ≫ P.hom = yoneda.map (𝟙 _) ≫ yonedaEquiv.symm (yonedaEquiv P.hom)
      simp))
  · have e : (overToIA X (yonedaEquiv P.hom)).obj (Over.mk (𝟙 P.left)) = P :=
      CostructuredArrow.obj_ext _ _ rfl (by
        change yoneda.map (𝟙 _) ≫ P.hom = yoneda.map (𝟙 _) ≫ yonedaEquiv.symm (yonedaEquiv P.hom)
        simp)
    refine Eq.trans ?_ (eqToHom_map Φ.toFunctor e)
    change Φ.toFunctor.map _ = _
    congr 1
    apply CostructuredArrow.hom_ext
    exact (CostructuredArrow.eqToHom_left e).symm

/-- `iAHomEquivInv` is a right inverse of `iAHomEquivFun`. -/
lemma iAHomEquivFun_inv (τ : X ⟶ (iAStarFunctor A).obj C) :
    iAHomEquivFun (iAHomEquivInv τ) = τ := by
  ext ⟨a⟩ : 3
  refine TypeCat.Fun.ext (funext fun x ↦ ?_)
  change (overToIA X x).toCatHom ≫ iAHomEquivInv τ = τ.app (op a) x
  ext : 1
  have hT : ∀ g : Over a,
      τ.app (op g.left) (yonedaEquiv (yoneda.map g.hom ≫ yonedaEquiv.symm x)) =
      (Over.map g.hom).toCatHom ≫ τ.app (op a) x := fun g ↦ by
    rw [yonedaEquiv_symm_naturality_left, Equiv.apply_symm_apply]
    exact NatTrans.naturality_apply τ g.hom.op x
  refine CategoryTheory.Functor.ext (fun g ↦ ?_) (fun g g' ψ ↦ ?_)
  · change (τ.app (op g.left) (yonedaEquiv (yoneda.map g.hom ≫ yonedaEquiv.symm x))).toFunctor.obj
      (Over.mk (𝟙 g.left)) = _
    rw [hT]
    exact congrArg (τ.app (op a) x).toFunctor.obj (over_map_obj_mk_id g.hom)
  · exact (overTransport_eq g.hom g'.hom ψ.left (Over.w ψ) (τ.app (op a) x) _ _ (hT g) (hT g')
      (app_eq_overMap_comp τ ((overToIA X x).map ψ))).trans rfl

variable (A) in
/-- **Layer 3.1.** The adjunction `i_A ⊣ i_A^*`. -/
def iAAdjunction : iAFunctor A ⊣ iAStarFunctor A :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ :=
        { toFun := iAHomEquivFun
          invFun := iAHomEquivInv
          left_inv := iAHomEquivInv_fun
          right_inv := iAHomEquivFun_inv }
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := rfl }

variable (A) in
/-- **Layer 3.1.** `i_A` is left adjoint to `i_A^*`. -/
theorem nonempty_iAAdjunction : Nonempty (iAFunctor A ⊣ iAStarFunctor A) :=
  ⟨iAAdjunction A⟩

variable (A) in
/-- **Layer 3.2.** The weak equivalences `W_Â = i_A⁻¹ W` of presheaves. -/
abbrev presheafWeq (W : MorphismProperty Cat.{u, u}) : MorphismProperty (Aᵒᵖ ⥤ Type u) :=
  W.inverseImage (iAFunctor A)

end Presheaf

section TestCategory

variable (A : Type u) [SmallCategory A]

/-- **Layer 6.1.** The functor `Â[W_Â⁻¹] ⥤ Cat[W⁻¹]` induced by `i_A`, which sends `W_Â` into
`W` by definition. -/
noncomputable def iALocalized (W : MorphismProperty Cat.{u, u}) :
    (presheafWeq A W).Localization ⥤ W.Localization :=
  Localization.Construction.lift (iAFunctor A ⋙ W.Q) fun _ _ _ hf ↦
    Localization.inverts W.Q W _ hf

/-- **Layer 6.1.** A weak test category (Maltsiniotis 2009, 2.3). Since `i_A ⊣ i_A^*`, asking
that `i_A^*` reflect and preserve weak equivalences and that the functor induced by `i_A` be an
equivalence makes the two induced functors quasi-inverse. -/
structure IsWeakTestCategory (W : MorphismProperty Cat.{u, u}) : Prop where
  /-- `W = (i_A^*)⁻¹ W_Â`. -/
  iAStar_mem_iff : ∀ ⦃C D : Cat.{u, u}⦄ (F : C ⟶ D),
    W F ↔ presheafWeq A W ((iAStarFunctor A).map F)
  /-- `i_A` induces an equivalence of localizations. -/
  isEquivalence : (iALocalized A W).IsEquivalence

/-- **Layer 6.1.** A local test category: every `A/a` is a weak test category. -/
def IsLocalTestCategory (W : MorphismProperty Cat.{u, u}) : Prop :=
  ∀ a : A, IsWeakTestCategory (Over a) W

/-- **Layer 6.1.** A test category: a weak test category that is a local test category. -/
def IsTestCategory (W : MorphismProperty Cat.{u, u}) : Prop :=
  IsWeakTestCategory A W ∧ IsLocalTestCategory A W

/-- **Layer 6.1.** A strict test category: a test category whose localization functor preserves
binary products. -/
def IsStrictTestCategory (W : MorphismProperty Cat.{u, u}) : Prop :=
  IsTestCategory A W ∧
    ∀ X Y : Aᵒᵖ ⥤ Type u, PreservesLimit (pair X Y) (presheafWeq A W).Q

end TestCategory

end LeanPool.HomotopyTheoryOfCategories
