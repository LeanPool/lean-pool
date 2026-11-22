/-
Copyright (c) 2026 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import LeanPool.RigidDescent.Foundations.ColimitFormula
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Triangulated.Yoneda

/-!
# `A(T)`, restricted Yoneda, and `h(W ⊗ -)`

Paper, §2. `A(T) = Mod-T^ω` (`AT T`) is the category of functors from the small model of the
compact objects, contravariantly, to abelian groups; mathlib makes it abelian. Restricted Yoneda
`h : T ⥤ A(T)` (`restrictedYoneda T`) sends `X` to `Hom(-, X)`.

The paper uses [BKS20, Prop. A.14], that `h` is strong monoidal for Day convolution, in
Lemma 2.3 (`lem:ideal`) and Prop. 3.5 (`prop:tails`). What the proofs need is that `h(W ⊗ -)`
factors through `h` up to natural isomorphism: a functor `F_W = tensorLeftAT W : A(T) ⥤ A(T)`
with `h ⋙ F_W ≅ tensorLeft W ⋙ h` (`tensorLeftATIso`).

We take `F_W` to be the left Kan extension of `c ↦ h(W ⊗ c)` along the Yoneda embedding of the
small model, `F_W(M) = colim_{(c, h(c) → M)} h(W ⊗ c)`; on representables this is Day
convolution with `hW`. At `M = h(Z)`, maps `h(c) → h(Z)` are maps `c → Z` (`yonedaMap`), so
`F_W(h Z)(K) = colim_{c → Z} Hom(K, W ⊗ c)`, which is `Hom(K, W ⊗ Z)` by the colimit formula
for the homological, coproduct-preserving functor `Hom(K, W ⊗ -)`
(`Foundations/ColimitFormula.lean`). No duals are needed.
-/

@[expose] public section

open CategoryTheory Limits Opposite Pretriangulated MonoidalCategory

universe v u

namespace RigidDescent

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [IsTriangulated T]
  [CompactlyGenerated T]

variable (T) in
/-- Paper, §2: `A(T)`, the functors from (the small model of) the compact objects of `T`,
contravariantly, to abelian groups. It is abelian (`functorCategoryAbelian`). -/
noncomputable abbrev AT : Type (v + 1) := (CompactModel T)ᵒᵖ ⥤ AddCommGrpCat.{v}

example : Nonempty (Abelian (AT T)) := ⟨inferInstance⟩

variable (T) in
/-- Paper, §2: restricted Yoneda `h : T ⥤ A(T)`, `h(X) = Hom(-, X)` on compact objects. -/
noncomputable abbrev restrictedYoneda : T ⥤ AT T :=
  preadditiveYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (compactIncl T).op

lemma restrictedYoneda_map_app {X X' : T} (f : X ⟶ X') (c : CompactModel T)
    (a : compactObj T c ⟶ X) : ((restrictedYoneda T).map f).app (op c) a = a ≫ f :=
  rfl

lemma restrictedYoneda_obj_map {X : T} {c c' : CompactModel T} (g : c ⟶ c')
    (a : compactObj T c' ⟶ X) : ((restrictedYoneda T).obj X).map g.op a = g.hom ≫ a :=
  rfl

variable (T) in
/-- The Yoneda embedding of the small model, `c ↦ h(c)`. -/
noncomputable abbrev yonedaAT : CompactModel T ⥤ AT T := compactIncl T ⋙ restrictedYoneda T

/-! ### Yoneda for `h` -/

/-- The map `c ⟶ Z` corresponding to `f : h(c) ⟶ h(Z)` by the Yoneda lemma. -/
noncomputable def yonedaMap {c : CompactModel T} {Z : T}
    (f : (yonedaAT T).obj c ⟶ (restrictedYoneda T).obj Z) : compactObj T c ⟶ Z :=
  f.app (op c) (𝟙 (compactObj T c))

lemma app_eq_comp_yonedaMap {c K : CompactModel T} {Z : T}
    (f : (yonedaAT T).obj c ⟶ (restrictedYoneda T).obj Z)
    (x : compactObj T K ⟶ compactObj T c) : f.app (op K) x = x ≫ yonedaMap f := by
  have h : f.app (op K) (x ≫ 𝟙 (compactObj T c)) = x ≫ yonedaMap f :=
    ConcreteCategory.congr_hom (f.naturality (InducedCategory.homMk x : K ⟶ c).op)
      (𝟙 (compactObj T c))
  rwa [Category.comp_id] at h

lemma yonedaMap_comp {c c' : CompactModel T} {Z : T} (g : c' ⟶ c)
    (f : (yonedaAT T).obj c ⟶ (restrictedYoneda T).obj Z) :
    yonedaMap ((yonedaAT T).map g ≫ f) = g.hom ≫ yonedaMap f :=
  (app_eq_comp_yonedaMap f (𝟙 _ ≫ g.hom)).trans (by rw [Category.id_comp])

lemma yonedaMap_comp_map {c : CompactModel T} {Z Z' : T}
    (f : (yonedaAT T).obj c ⟶ (restrictedYoneda T).obj Z) (u : Z ⟶ Z') :
    yonedaMap (f ≫ (restrictedYoneda T).map u) = yonedaMap f ≫ u :=
  rfl

lemma yonedaMap_map {c : CompactModel T} {Z : T} (l : compactObj T c ⟶ Z) :
    yonedaMap (c := c) ((restrictedYoneda T).map l) = l :=
  Category.id_comp l

lemma restrictedYoneda_map_yonedaMap {c : CompactModel T} {Z : T}
    (f : (yonedaAT T).obj c ⟶ (restrictedYoneda T).obj Z) :
    (restrictedYoneda T).map (yonedaMap f) = f := by
  ext K x
  exact (app_eq_comp_yonedaMap (K := K.unop) f x).symm

/-! ### The index categories at `h(Z)` are filtered -/

section Filtered

variable (Z : T)

instance : (CostructuredArrow.post (compactIncl T) (restrictedYoneda T) Z).Full where
  map_surjective {X Y} f := by
    refine ⟨CostructuredArrow.homMk f.left ?_, CostructuredArrow.hom_ext _ _ rfl⟩
    have h := congrArg yonedaMap (CostructuredArrow.w f)
    rw [yonedaMap_comp] at h
    have e : ∀ W : CostructuredArrow (compactIncl T) Z,
        yonedaMap ((CostructuredArrow.post (compactIncl T) (restrictedYoneda T) Z).obj W).hom =
          W.hom :=
      fun W => yonedaMap_map W.hom
    rw [e, e] at h
    exact h

instance : (CostructuredArrow.post (compactIncl T) (restrictedYoneda T) Z).EssSurj where
  mem_essImage X := ⟨CostructuredArrow.mk (Y := X.left) (yonedaMap X.hom),
    ⟨CostructuredArrow.isoMk (Iso.refl _) (by
      rw [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.id_comp]
      exact (restrictedYoneda_map_yonedaMap X.hom).symm)⟩⟩

instance : (CostructuredArrow.post (compactIncl T) (restrictedYoneda T) Z).IsEquivalence where

/-- The index category of `F_W(h Z)` is equivalent to that of the colimit formula at `Z`,
hence filtered. -/
instance isFiltered_costructuredArrow_yonedaAT :
    IsFiltered (CostructuredArrow (yonedaAT T) ((restrictedYoneda T).obj Z)) :=
  IsFiltered.of_equivalence
    (CostructuredArrow.post (compactIncl T) (restrictedYoneda T) Z).asEquivalence

end Filtered

/-! ### `F_W` -/

variable [MonoidalCategory T]

variable (T) in
/-- `c ↦ h(W ⊗ c)` on the small model. -/
noncomputable abbrev tensorYonedaAT (W : T) : CompactModel T ⥤ AT T :=
  compactIncl T ⋙ tensorLeft W ⋙ restrictedYoneda T

/-- `F_W : A(T) ⥤ A(T)`, the left Kan extension of `c ↦ h(W ⊗ c)` along the Yoneda embedding:
`F_W(M) = colim_{(c, h(c) → M)} h(W ⊗ c)`. -/
noncomputable abbrev tensorLeftAT (W : T) : AT T ⥤ AT T :=
  (yonedaAT T).pointwiseLeftKanExtension (tensorYonedaAT T W)

/-- The diagram whose colimit is `F_W(h Z)`. -/
noncomputable abbrev tensorDiagram (W Z : T) :
    CostructuredArrow (yonedaAT T) ((restrictedYoneda T).obj Z) ⥤ AT T :=
  CostructuredArrow.proj (yonedaAT T) ((restrictedYoneda T).obj Z) ⋙ tensorYonedaAT T W

/-- The cocone `h(W ⊗ c) ⟶ h(W ⊗ Z)` over `tensorDiagram W Z`, given by `h(W ⊗ l)` for
`h(l) : h(c) ⟶ h(Z)`. -/
noncomputable def tensorCocone (W Z : T) : Cocone (tensorDiagram W Z) where
  pt := (restrictedYoneda T).obj (W ⊗ Z)
  ι :=
    { app := fun j => (restrictedYoneda T).map (W ◁ yonedaMap j.hom)
      naturality := fun j j' g => by
        have hg := congrArg yonedaMap (CostructuredArrow.w g)
        rw [yonedaMap_comp] at hg
        change (restrictedYoneda T).map (W ◁ g.left.hom) ≫
            (restrictedYoneda T).map (W ◁ yonedaMap j'.hom) =
          (restrictedYoneda T).map (W ◁ yonedaMap j.hom) ≫ 𝟙 _
        rw [Category.comp_id, ← Functor.map_comp, ← MonoidalCategory.whiskerLeft_comp, hg] }

@[reassoc]
lemma ι_tensorLeftAT_map (W : T) {Z Z' : T} (u : Z ⟶ Z')
    (j : CostructuredArrow (yonedaAT T) ((restrictedYoneda T).obj Z)) :
    colimit.ι (tensorDiagram W Z) j ≫ (tensorLeftAT W).map ((restrictedYoneda T).map u) =
      colimit.ι (tensorDiagram W Z')
        ((CostructuredArrow.map ((restrictedYoneda T).map u)).obj j) :=
  colimit.ι_desc _ _

/-- The component at `Z` of the comparison map `F_W(h Z) ⟶ h(W ⊗ Z)`. -/
noncomputable def tensorLeftATπApp (W Z : T) :
    (tensorLeftAT W).obj ((restrictedYoneda T).obj Z) ⟶ (restrictedYoneda T).obj (W ⊗ Z) :=
  colimit.desc (tensorDiagram W Z) (tensorCocone W Z)

@[reassoc]
lemma ι_tensorLeftATπApp (W Z : T)
    (j : CostructuredArrow (yonedaAT T) ((restrictedYoneda T).obj Z)) :
    colimit.ι (tensorDiagram W Z) j ≫ tensorLeftATπApp W Z =
      (restrictedYoneda T).map (W ◁ yonedaMap j.hom) :=
  colimit.ι_desc _ _

/-- The comparison map `F_W(h Z) ⟶ h(W ⊗ Z)`. -/
noncomputable def tensorLeftATπ (W : T) :
    restrictedYoneda T ⋙ tensorLeftAT W ⟶ tensorLeft W ⋙ restrictedYoneda T where
  app Z := tensorLeftATπApp W Z
  naturality Z Z' u := colimit.hom_ext fun j => by
    have h1 := ι_tensorLeftAT_map_assoc W u j (tensorLeftATπApp W Z')
    have h2 := ι_tensorLeftATπApp W Z'
      ((CostructuredArrow.map ((restrictedYoneda T).map u)).obj j)
    have h3 := ι_tensorLeftATπApp_assoc W Z j ((restrictedYoneda T).map (W ◁ u))
    have h4 : (restrictedYoneda T).map
          (W ◁ yonedaMap ((CostructuredArrow.map ((restrictedYoneda T).map u)).obj j).hom) =
        (restrictedYoneda T).map (W ◁ yonedaMap j.hom) ≫ (restrictedYoneda T).map (W ◁ u) := by
      refine Eq.trans ?_ (Functor.map_comp _ _ _)
      exact congrArg (restrictedYoneda T).map
        (MonoidalCategory.whiskerLeft_comp W (yonedaMap j.hom) u)
    exact h1.trans (h2.trans (h4.trans h3.symm))

lemma tensorLeftATπ_ι {W Z : T} {K : CompactModel T}
    (j : CostructuredArrow (yonedaAT T) ((restrictedYoneda T).obj Z))
    (x : compactObj T K ⟶ W ⊗ compactObj T j.left) :
    ((tensorLeftATπ W).app Z).app (op K) ((colimit.ι (tensorDiagram W Z) j).app (op K) x) =
      x ≫ (W ◁ yonedaMap j.hom) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (ι_tensorLeftATπApp W Z j) (op K)) x

lemma exists_ι_app_eq {W Z : T} {K : CompactModel T}
    (e : ((colimit (tensorDiagram W Z)).obj (op K))) :
    ∃ (j : CostructuredArrow (yonedaAT T) ((restrictedYoneda T).obj Z))
      (x : compactObj T K ⟶ W ⊗ compactObj T j.left),
      (colimit.ι (tensorDiagram W Z) j).app (op K) x = e := by
  obtain ⟨j, x, hx⟩ := Concrete.colimit_exists_rep
    (tensorDiagram W Z ⋙ (evaluation _ _).obj (op K))
    ((colimitObjIsoColimitCompEvaluation (tensorDiagram W Z) (op K)).hom e)
  refine ⟨j, x, ?_⟩
  have h := ConcreteCategory.congr_hom
    (colimitObjIsoColimitCompEvaluation_ι_inv (tensorDiagram W Z) j (op K)) x
  rw [ConcreteCategory.comp_apply, hx] at h
  exact h.symm.trans (Iso.hom_inv_id_apply _ _)

lemma ι_app_eq {W Z : T} {K : CompactModel T}
    {j j' : CostructuredArrow (yonedaAT T) ((restrictedYoneda T).obj Z)} (g : j ⟶ j')
    (x : ((tensorDiagram W Z).obj j).obj (op K)) :
    (colimit.ι (tensorDiagram W Z) j).app (op K) x =
      (colimit.ι (tensorDiagram W Z) j').app (op K) (((tensorDiagram W Z).map g).app (op K) x) := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (colimit.w (tensorDiagram W Z) g) (op K)) x
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
  exact h.symm

/-! ### `F_W ∘ h ≅ h ∘ (W ⊗ -)` -/

variable [TensorTriangulated T] [MonoidalClosed T]

/-- `Hom(K, W ⊗ -)`, for `K` in the small model. -/
noncomputable abbrev homTensor (W : T) (K : CompactModel T) : T ⥤ AddCommGrpCat.{v} :=
  tensorLeft W ⋙ preadditiveCoyoneda.obj (op (compactObj T K))

omit [MonoidalClosed T] in
lemma isHomological_homTensor (W : T) (K : CompactModel T) : (homTensor W K).IsHomological :=
  inferInstanceAs ((tensorLeft W ⋙ preadditiveCoyoneda.obj (op (compactObj T K))).IsHomological)

omit [TensorTriangulated T] in
lemma spannedBySummands_homTensor (W : T) (K : CompactModel T) :
    SpannedBySummands (homTensor W K) := by
  have : ∀ J : Type v,
      PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (op (compactObj T K))) :=
    isCompactObj_compactObj K
  exact spannedBySummands_of_preserves _

/-- `F_W(h Z) ⟶ h(W ⊗ Z)` is bijective at every compact `K`. -/
lemma bijective_tensorLeftATπ_app_app (W Z : T) (K : CompactModel T) :
    Function.Bijective (((tensorLeftATπ W).app Z).app (op K)) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun e he => ?_, fun z => ?_⟩
  · obtain ⟨j, x, rfl⟩ := exists_ι_app_eq e
    rw [tensorLeftATπ_ι] at he
    obtain ⟨i, g, l', hgl, hg⟩ := exists_compactObj_factor_of_map_eq_zero
      (isHomological_homTensor W K) (spannedBySummands_homTensor W K)
      (isCompactObj_compactObj j.left) (yonedaMap j.hom) x he
    let j' : CostructuredArrow (yonedaAT T) ((restrictedYoneda T).obj Z) :=
      CostructuredArrow.mk (Y := CompactModel.of i) ((restrictedYoneda T).map l')
    let γ : j ⟶ j' := CostructuredArrow.homMk (InducedCategory.homMk g) (by
      rw [← restrictedYoneda_map_yonedaMap j.hom, ← hgl, Functor.map_comp]
      rfl)
    have hg' : x ≫ W ◁ g = 0 := hg
    calc (colimit.ι (tensorDiagram W Z) j).app (op K) x
        = (colimit.ι (tensorDiagram W Z) j').app (op K) (x ≫ W ◁ g) := ι_app_eq γ x
      _ = (colimit.ι (tensorDiagram W Z) j').app (op K) 0 := by rw [hg']; rfl
      _ = 0 := map_zero _
  · obtain ⟨i, l, x, hx⟩ := exists_compactObj_map_eq (isHomological_homTensor W K)
      (spannedBySummands_homTensor W K) (W := Z) z
    have e : yonedaMap (CostructuredArrow.mk (Y := CompactModel.of i)
        ((restrictedYoneda T).map l)).hom = l := yonedaMap_map l
    refine ⟨(colimit.ι (tensorDiagram W Z)
      (CostructuredArrow.mk (Y := CompactModel.of i) ((restrictedYoneda T).map l))).app (op K) x,
      ?_⟩
    refine (tensorLeftATπ_ι (W := W) (Z := Z) (K := K)
      (CostructuredArrow.mk (Y := CompactModel.of i) ((restrictedYoneda T).map l)) x).trans ?_
    rw [e]
    exact hx

instance isIso_tensorLeftATπ_app (W Z : T) : IsIso ((tensorLeftATπ W).app Z) := by
  have : ∀ K : (CompactModel T)ᵒᵖ, IsIso (((tensorLeftATπ W).app Z).app K) := fun K =>
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_tensorLeftATπ_app_app W Z K.unop)
  exact NatIso.isIso_of_isIso_app _

instance isIso_tensorLeftATπ (W : T) : IsIso (tensorLeftATπ W) :=
  NatIso.isIso_of_isIso_app _

/-- [BKS20, Prop. A.14] in the form the paper uses (Lemma 2.3, Prop. 3.5): `h(W ⊗ -)` factors
through `h`, as `F_W ∘ h ≅ h ∘ (W ⊗ -)`. -/
noncomputable def tensorLeftATIso (W : T) :
    restrictedYoneda T ⋙ tensorLeftAT W ≅ tensorLeft W ⋙ restrictedYoneda T :=
  asIso (tensorLeftATπ W)

end RigidDescent
