/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.HomotopyTheoryOfCategories.FundamentalGroupoid
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.Order.BourbakiWitt
import Mathlib.Algebra.Group.End
import Mathlib.CategoryTheory.Adjunction.Comma
import Mathlib.CategoryTheory.Groupoid.Discrete
import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# Basic localizers and asphericity

Following Cisinski (« Le localisateur fondamental minimal », Cahiers 2004, §1.1), we define
`W`-aspherical small categories and functors, basic localizers (`IsBasicLocalizer`: FS1–FS3,
LF2, LF3) and the minimal basic localizer `Winfty`, the intersection of all basic localizers.
We prove:

* `isBasicLocalizer_Winfty` and `Winfty_le`: `W∞` is a basic localizer, contained in every one;
* `isBasicLocalizer_W₀`: functors bijective on connected components form a basic localizer
  (Cisinski 2004, proof of Proposition 2.3.4), by an explicit inverse on `π₀` built from the
  slices `A/G b`;
* `isBasicLocalizer_WNeg₁`: `W₋₁` (nonemptiness reflected and preserved) is a basic localizer,
  and `W₀_le_WNeg₁`;
* `isAspherical_W₁_iff`: `A` is `W₁`-aspherical iff `Π₁ A` is equivalent to the point;
* `mem_of_isAsphericalFunctor`: **Quillen's Theorem A** for an arbitrary basic localizer
  (Cisinski 2004, Remark 1.1.4), from LF3 with `G = 𝟭`;
* `mem_of_isLeftAdjoint` and `mem_of_isRightAdjoint`: functors with a right, resp. left,
  adjoint are in every basic localizer (Cisinski 2004, Corollary 1.1.10), through
  `mem_iff_of_natTrans` (Proposition 1.1.9), proved with the cylinder `Fin 2 × A`.

We also define `IsLocallyConstant` (Cisinski 2004, 2.3.1). The stability of basic localizers
under coproducts, products and integration (Propositions 1.1.5, 1.1.7, 1.2.4) is not
formalised here.

This is Layer 2 of the roadmap *Homotopy theory of small categories*.
-/

@[expose] public section

universe u

namespace LeanPool.HomotopyTheoryOfCategories

open CategoryTheory CategoryTheory.Limits

/-- **Layer 2.1.** `A` is `W`-aspherical when `A ⥤ e` lies in `W`. -/
def IsAspherical (W : MorphismProperty Cat.{u, u}) (A : Type u) [SmallCategory A] : Prop :=
  W (Functor.star A : A ⥤ Discrete PUnit.{u + 1}).toCatHom

/-- **Layer 2.1.** `F` is `W`-aspherical when every slice `A/b` is `W`-aspherical. -/
def IsAsphericalFunctor (W : MorphismProperty Cat.{u, u}) {A B : Type u} [SmallCategory A]
    [SmallCategory B] (F : A ⥤ B) : Prop :=
  ∀ b : B, IsAspherical W (CostructuredArrow F b)

/-- **Layer 2.1.** A basic localizer (Cisinski 2004, 1.1.1 and Definition 1.1.3). -/
structure IsBasicLocalizer (W : MorphismProperty Cat.{u, u}) : Prop where
  /-- FS1: `W` contains the identities. -/
  containsIdentities : W.ContainsIdentities
  /-- FS2: `W` has two-out-of-three. -/
  twoOutOfThree : W.HasTwoOutOfThreeProperty
  /-- FS3: a retraction `r` of `i` with `r ≫ i` in `W` is in `W`. -/
  retract : ∀ {X Y : Cat.{u, u}} (i : X ⟶ Y) (r : Y ⟶ X), i ≫ r = 𝟙 X → W (r ≫ i) → W r
  /-- LF2: a small category with a terminal object is aspherical. -/
  aspherical_of_hasTerminal : ∀ (A : Type u) [SmallCategory A] [HasTerminal A],
    IsAspherical W A
  /-- LF3, the relative Theorem A. -/
  of_slices : ∀ {A B C : Type u} [SmallCategory A] [SmallCategory B] [SmallCategory C]
    (F : A ⥤ B) (G : B ⥤ C), (∀ c : C, W (CostructuredArrow.pre F G c).toCatHom) →
      W F.toCatHom

namespace IsBasicLocalizer

variable {W : MorphismProperty Cat.{u, u}} (hW : IsBasicLocalizer W)
include hW

/-- Identities are in a basic localizer. -/
lemma id_mem (X : Cat.{u, u}) : W (𝟙 X) :=
  hW.containsIdentities.id_mem X

/-- A basic localizer is stable under composition. -/
lemma comp_mem {X Y Z : Cat.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) (hg : W g) :
    W (f ≫ g) :=
  hW.twoOutOfThree.comp_mem f g hf hg

/-- Two-out-of-three in a basic localizer: `g` and `f ≫ g` in `W` give `f` in `W`. -/
lemma of_postcomp {X Y Z : Cat.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W g) (hfg : W (f ≫ g)) :
    W f :=
  hW.twoOutOfThree.of_postcomp f g hg hfg

/-- Two-out-of-three in a basic localizer: `f` and `f ≫ g` in `W` give `g` in `W`. -/
lemma of_precomp {X Y Z : Cat.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) (hfg : W (f ≫ g)) :
    W g :=
  hW.twoOutOfThree.of_precomp f g hf hfg

end IsBasicLocalizer

/-- **Layer 2.1.** The minimal basic localizer, as the intersection of all of them. -/
def Winfty : MorphismProperty Cat.{u, u} :=
  fun _ _ F ↦ ∀ W : MorphismProperty Cat.{u, u}, IsBasicLocalizer W → W F

/-- **Layer 2.1.** `W∞` is contained in every basic localizer. -/
theorem Winfty_le {W : MorphismProperty Cat.{u, u}} (hW : IsBasicLocalizer W) : Winfty ≤ W :=
  fun _ _ _ hF ↦ hF W hW

/-- **Layer 2.1.** The intersection of all basic localizers is a basic localizer. -/
theorem isBasicLocalizer_Winfty : IsBasicLocalizer Winfty.{u} where
  containsIdentities := ⟨fun X _ hW ↦ hW.id_mem X⟩
  twoOutOfThree :=
    { comp_mem := fun f g hf hg W hW ↦ hW.comp_mem f g (hf W hW) (hg W hW)
      of_postcomp := fun f g hg hfg W hW ↦ hW.of_postcomp f g (hg W hW) (hfg W hW)
      of_precomp := fun f g hf hfg W hW ↦ hW.of_precomp f g (hf W hW) (hfg W hW) }
  retract i r h hri W hW := hW.retract i r h (hri W hW)
  aspherical_of_hasTerminal A _ _ _ hW := hW.aspherical_of_hasTerminal A
  of_slices F G h W hW := hW.of_slices F G fun c ↦ h c W hW

/-- `Π₀` of the identity is the identity. -/
lemma mapConnectedComponents_id (A : Type u) [SmallCategory A] :
    (𝟭 A).mapConnectedComponents = id := by
  ext ⟨a⟩
  rfl

/-- `Π₀` of a composite is the composite. -/
lemma mapConnectedComponents_comp {A B C : Type u} [SmallCategory A] [SmallCategory B]
    [SmallCategory C] (F : A ⥤ B) (G : B ⥤ C) :
    (F ⋙ G).mapConnectedComponents = G.mapConnectedComponents ∘ F.mapConnectedComponents := by
  ext ⟨a⟩
  rfl

/-- A category with a terminal object has exactly one connected component. -/
lemma subsingleton_connectedComponents_of_hasTerminal (A : Type u) [SmallCategory A]
    [HasTerminal A] : Subsingleton (ConnectedComponents A) :=
  ⟨by
    rintro ⟨a⟩ ⟨b⟩
    exact Quotient.sound ((Zigzag.of_hom (terminal.from a)).trans
      (Zigzag.of_inv (terminal.from b)))⟩

/-- A function constant along morphisms factors through connected components. -/
lemma eq_of_zigzag_of_forall_hom {B : Type u} [SmallCategory B] {α : Type u} (φ : B → α)
    (hφ : ∀ ⦃b b' : B⦄, (b ⟶ b') → φ b = φ b') {b b' : B} (h : Zigzag b b') : φ b = φ b' := by
  induction h with
  | refl => rfl
  | tail _ hz ih =>
    rcases hz with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
    · exact ih.trans (hφ f)
    · exact ih.trans (hφ f).symm

section W₀

variable {A B C : Type u} [SmallCategory A] [SmallCategory B] [SmallCategory C]
  (F : A ⥤ B) (G : B ⥤ C)
  (h : ∀ c : C, Function.Bijective (CostructuredArrow.pre F G c).mapConnectedComponents)

/-- The component of `A` attached to `b : B` when every `A/c ⥤ B/c` is bijective on `π₀`:
the image in `π₀ A` of the component of `A/G b` lying over the component of `(b, 𝟙)`. -/
noncomputable def W₀Inv (b : B) : ConnectedComponents A :=
  (CostructuredArrow.proj (F ⋙ G) (G.obj b)).mapConnectedComponents
    ((Equiv.ofBijective _ (h (G.obj b))).symm
      (Quotient.mk'' (CostructuredArrow.mk (𝟙 (G.obj b)))))

/-- `W₀Inv` is constant along morphisms of `B`. -/
lemma W₀Inv_eq_of_hom {b b' : B} (f : b ⟶ b') : W₀Inv F G h b = W₀Inv F G h b' := by
  let e := Equiv.ofBijective _ (h (G.obj b))
  let e' := Equiv.ofBijective _ (h (G.obj b'))
  let x := e.symm (Quotient.mk'' (CostructuredArrow.mk (𝟙 (G.obj b))))
  have hx : (CostructuredArrow.pre F G (G.obj b)).mapConnectedComponents x =
      Quotient.mk'' (CostructuredArrow.mk (𝟙 (G.obj b))) := e.apply_symm_apply _
  have hcomm : ∀ y, (CostructuredArrow.pre F G (G.obj b')).mapConnectedComponents
      ((CostructuredArrow.map (S := F ⋙ G) (G.map f)).mapConnectedComponents y) =
      (CostructuredArrow.map (S := G) (G.map f)).mapConnectedComponents
        ((CostructuredArrow.pre F G (G.obj b)).mapConnectedComponents y) := by
    rintro ⟨y⟩
    rfl
  have hy : (CostructuredArrow.map (S := F ⋙ G) (G.map f)).mapConnectedComponents x =
      e'.symm (Quotient.mk'' (CostructuredArrow.mk (𝟙 (G.obj b')))) := by
    refine (e'.symm_apply_eq.2 ?_).symm
    change _ = (CostructuredArrow.pre F G (G.obj b')).mapConnectedComponents _
    rw [hcomm, hx]
    exact Quotient.sound (Zigzag.of_inv
      (CostructuredArrow.homMk f (by simp) : CostructuredArrow.mk (𝟙 (G.obj b) ≫ G.map f) ⟶
        CostructuredArrow.mk (𝟙 (G.obj b'))))
  have hproj : ∀ y, (CostructuredArrow.proj (F ⋙ G) (G.obj b')).mapConnectedComponents
      ((CostructuredArrow.map (S := F ⋙ G) (G.map f)).mapConnectedComponents y) =
      (CostructuredArrow.proj (F ⋙ G) (G.obj b)).mapConnectedComponents y := by
    rintro ⟨y⟩
    rfl
  change (CostructuredArrow.proj (F ⋙ G) (G.obj b)).mapConnectedComponents x = _
  rw [← hproj, hy]
  rfl

/-- `W₀Inv` sends `F a` to the component of `a`. -/
lemma W₀Inv_obj (a : A) : W₀Inv F G h (F.obj a) = Quotient.mk'' a := by
  let e := Equiv.ofBijective _ (h (G.obj (F.obj a)))
  have : e.symm (Quotient.mk'' (CostructuredArrow.mk (𝟙 (G.obj (F.obj a))))) =
      Quotient.mk'' (CostructuredArrow.mk (𝟙 ((F ⋙ G).obj a))) := by
    exact e.symm_apply_eq.2 rfl
  change (CostructuredArrow.proj (F ⋙ G) (G.obj (F.obj a))).mapConnectedComponents
    (e.symm _) = _
  rw [this]
  rfl

include h in
/-- LF3 for `W₀`: if every `A/c ⥤ B/c` is bijective on `π₀`, so is `F`. -/
lemma bijective_mapConnectedComponents_of_slices :
    Function.Bijective F.mapConnectedComponents := by
  refine ⟨fun x y hxy ↦ ?_, ?_⟩
  · let φ : ConnectedComponents B → ConnectedComponents A :=
      Quotient.lift (W₀Inv F G h) fun _ _ hb ↦
        eq_of_zigzag_of_forall_hom _ (fun _ _ f ↦ W₀Inv_eq_of_hom F G h f) hb
    have hφ : ∀ z, φ (F.mapConnectedComponents z) = z := by
      rintro ⟨a⟩
      exact W₀Inv_obj F G h a
    rw [← hφ x, ← hφ y, hxy]
  · rintro ⟨b⟩
    obtain ⟨⟨x⟩, hx⟩ := (h (G.obj b)).2 (Quotient.mk'' (CostructuredArrow.mk (𝟙 (G.obj b))))
    refine ⟨Quotient.mk'' x.left, ?_⟩
    have hz : Zigzag ((CostructuredArrow.pre F G (G.obj b)).obj x)
        (CostructuredArrow.mk (𝟙 (G.obj b))) := Quotient.exact' hx
    exact Quotient.sound (zigzag_obj_of_zigzag (CostructuredArrow.proj G (G.obj b)) hz)

end W₀

/-- **Layer 2.2.** `W₀` is a basic localizer (Cisinski 2004, proof of Proposition 2.3.4). -/
theorem isBasicLocalizer_W₀ : IsBasicLocalizer W₀.{u} where
  containsIdentities := ⟨fun X ↦ by
    change Function.Bijective (𝟭 X).mapConnectedComponents
    rw [mapConnectedComponents_id]
    exact Function.bijective_id⟩
  twoOutOfThree :=
    { comp_mem := fun f g hf hg ↦ by
        change Function.Bijective (f.toFunctor ⋙ g.toFunctor).mapConnectedComponents
        rw [mapConnectedComponents_comp]
        exact hg.comp hf
      of_postcomp := fun f g hg hfg ↦ by
        change Function.Bijective (f.toFunctor ⋙ g.toFunctor).mapConnectedComponents at hfg
        rw [mapConnectedComponents_comp] at hfg
        exact (Function.Bijective.of_comp_iff' hg _).1 hfg
      of_precomp := fun f g hf hfg ↦ by
        change Function.Bijective (f.toFunctor ⋙ g.toFunctor).mapConnectedComponents at hfg
        rw [mapConnectedComponents_comp] at hfg
        exact (Function.Bijective.of_comp_iff _ hf).1 hfg }
  retract i r hir hri := by
    change Function.Bijective (r.toFunctor ⋙ i.toFunctor).mapConnectedComponents at hri
    rw [mapConnectedComponents_comp] at hri
    have hid : r.toFunctor.mapConnectedComponents ∘ i.toFunctor.mapConnectedComponents = id := by
      rw [← mapConnectedComponents_comp]
      change (i ≫ r).toFunctor.mapConnectedComponents = id
      rw [hir]
      exact mapConnectedComponents_id _
    exact ⟨hri.1.of_comp, Function.RightInverse.surjective (congrFun hid)⟩
  aspherical_of_hasTerminal A _ _ := by
    change Function.Bijective (Functor.star A).mapConnectedComponents
    have := subsingleton_connectedComponents_of_hasTerminal A
    have : Subsingleton (ConnectedComponents (Discrete PUnit.{u + 1})) :=
      ⟨by rintro ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟩⟩⟩; rfl⟩
    refine ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨Quotient.mk'' (⊤_ A), ?_⟩⟩
    exact Subsingleton.elim _ _
  of_slices F G h := bijective_mapConnectedComponents_of_slices F G h

/-- **Layer 2.2.** `W₋₁`: the functors `F : A ⥤ B` with `A` nonempty iff `B` is. -/
def WNeg₁ : MorphismProperty Cat.{u, u} :=
  fun X Y _ ↦ (Nonempty X ↔ Nonempty Y)

/-- **Layer 2.2.** `W₋₁` is a basic localizer. -/
theorem isBasicLocalizer_WNeg₁ : IsBasicLocalizer WNeg₁.{u} where
  containsIdentities := ⟨fun _ ↦ Iff.rfl⟩
  twoOutOfThree :=
    { comp_mem := fun _ _ hf hg ↦ hf.trans hg
      of_postcomp := fun _ _ hg hfg ↦ hfg.trans hg.symm
      of_precomp := fun _ _ hf hfg ↦ hf.symm.trans hfg }
  retract i r _ _ := ⟨fun ⟨y⟩ ↦ ⟨r.toFunctor.obj y⟩, fun ⟨x⟩ ↦ ⟨i.toFunctor.obj x⟩⟩
  aspherical_of_hasTerminal A _ _ := ⟨fun _ ↦ ⟨⟨⟨⟩⟩⟩, fun _ ↦ ⟨(⊤_ A : A)⟩⟩
  of_slices {A B C} _ _ _ F G h := by
    refine ⟨fun ⟨a⟩ ↦ ⟨F.obj a⟩, fun ⟨b⟩ ↦ ?_⟩
    obtain ⟨x⟩ := (h (G.obj b)).2 ⟨(CostructuredArrow.mk (𝟙 (G.obj b)) :
      CostructuredArrow G (G.obj b))⟩
    exact ⟨(x : CostructuredArrow (F ⋙ G) (G.obj b)).left⟩

/-- **Layer 2.2.** `W₀ ⊆ W₋₁`. -/
theorem W₀_le_WNeg₁ : W₀.{u} ≤ WNeg₁ := fun X Y F hF ↦
  ⟨fun ⟨x⟩ ↦ ⟨F.toFunctor.obj x⟩, fun ⟨y⟩ ↦ by
    obtain ⟨⟨x⟩, -⟩ := hF.2 (Quotient.mk'' y)
    exact ⟨x⟩⟩

/-- **Layer 2.2.** A small category is `W₁`-aspherical iff its fundamental groupoid is equivalent
to the point. -/
theorem isAspherical_W₁_iff (A : Type u) [SmallCategory A] :
    IsAspherical W₁ A ↔ Nonempty (FreeGroupoid A ≌ Discrete PUnit.{u + 1}) := by
  have := isEquivalence_freeGroupoidLift_id (Discrete PUnit.{u + 1})
  change (FreeGroupoid.map (Functor.star A)).IsEquivalence ↔ _
  constructor
  · intro _
    exact ⟨(FreeGroupoid.map (Functor.star A) ⋙ FreeGroupoid.lift (𝟭 _)).asEquivalence⟩
  · rintro ⟨e⟩
    have : (FreeGroupoid.map (Functor.star A) ⋙ FreeGroupoid.lift (𝟭 _)).IsEquivalence := by
      rw [Functor.punit_ext' (FreeGroupoid.map (Functor.star A) ⋙ FreeGroupoid.lift (𝟭 _))
        e.functor]
      infer_instance
    exact Functor.isEquivalence_of_comp_right _ (FreeGroupoid.lift (𝟭 _))

section TheoremA

variable {W : MorphismProperty Cat.{u, u}} (hW : IsBasicLocalizer W)
include hW

/-- **Layer 2.4.** Quillen's Theorem A for an arbitrary basic localizer (Cisinski 2004,
Remark 1.1.4). -/
theorem mem_of_isAsphericalFunctor {A B : Type u} [SmallCategory A] [SmallCategory B]
    (F : A ⥤ B) (hF : IsAsphericalFunctor W F) : W F.toCatHom := by
  refine hW.of_slices F (𝟭 B) fun c ↦ ?_
  have : HasTerminal (CostructuredArrow (𝟭 B) c) :=
    (CostructuredArrow.mkIdTerminal (S := 𝟭 B) (Y := c)).hasTerminal
  refine hW.of_postcomp _ (Functor.star _).toCatHom (hW.aspherical_of_hasTerminal _) ?_
  have e : (CostructuredArrow.pre F (𝟭 B) c).toCatHom ≫ (Functor.star _).toCatHom =
      (Functor.star (CostructuredArrow F c)).toCatHom :=
    congrArg Functor.toCatHom (Functor.punit_ext' _ _)
  rw [e]
  exact hF c

/-- **Layer 2.3.** Functors with a right adjoint are in every basic localizer
(Cisinski 2004, Corollary 1.1.10). -/
theorem mem_of_isLeftAdjoint {A B : Type u} [SmallCategory A] [SmallCategory B] (F : A ⥤ B)
    [F.IsLeftAdjoint] : W F.toCatHom :=
  mem_of_isAsphericalFunctor hW F fun b ↦
    have := isLeftAdjoint_iff_hasTerminal_costructuredArrow (F := F) |>.1 inferInstance b
    hW.aspherical_of_hasTerminal _

/-- The cylinder `Fin 2 × A ⥤ B` of a natural transformation `α : u ⟶ v`. -/
def cylinder {A B : Type u} [SmallCategory A] [SmallCategory B] {u v : A ⥤ B} (α : u ⟶ v) :
    Fin 2 × A ⥤ B :=
  Functor.uncurry.obj (ComposableArrows.mk₁ α)

omit hW in
/-- The cylinder of `α : u ⟶ v` restricts to `u` at `0`. -/
lemma sectR_zero_comp_cylinder {A B : Type u} [SmallCategory A] [SmallCategory B]
    {u v : A ⥤ B} (α : u ⟶ v) : Prod.sectR 0 A ⋙ cylinder α = u :=
  CategoryTheory.Functor.ext (fun _ ↦ rfl) fun _ _ f ↦ by
    change ((ComposableArrows.mk₁ α).map (𝟙 0)).app _ ≫ u.map f = 𝟙 _ ≫ u.map f ≫ 𝟙 _
    simp

omit hW in
/-- The cylinder of `α : u ⟶ v` restricts to `v` at `1`. -/
lemma sectR_one_comp_cylinder {A B : Type u} [SmallCategory A] [SmallCategory B]
    {u v : A ⥤ B} (α : u ⟶ v) : Prod.sectR 1 A ⋙ cylinder α = v :=
  CategoryTheory.Functor.ext (fun _ ↦ rfl) fun _ _ f ↦ by
    change ((ComposableArrows.mk₁ α).map (𝟙 1)).app _ ≫ v.map f = 𝟙 _ ≫ v.map f ≫ 𝟙 _
    simp

omit hW in
/-- The projection `Fin 2 × A ⥤ A` is left adjoint to `a ↦ (1, a)`. -/
def sndAdjunctionSectROne (A : Type u) [SmallCategory A] :
    CategoryTheory.Prod.snd (Fin 2) A ⊣ Prod.sectR 1 A where
  unit :=
    { app x := (homOfLE (Fin.le_last x.1), 𝟙 x.2)
      naturality _ _ f := by
        ext
        exacts [Subsingleton.elim _ _, (Category.comp_id _).trans (Category.id_comp _).symm] }
  counit := 𝟙 _
  left_triangle_components _ := Category.id_comp _
  right_triangle_components _ := by
    ext
    exacts [Subsingleton.elim _ _, Category.id_comp _]

/-- The inclusion `a ↦ (i, a)` into the cylinder is in every basic localizer. -/
lemma mem_sectR {A : Type u} [SmallCategory A] (i : Fin 2) :
    W (Prod.sectR i A).toCatHom := by
  have := (sndAdjunctionSectROne A).isLeftAdjoint
  exact hW.of_postcomp _ (CategoryTheory.Prod.snd (Fin 2) A).toCatHom
    (mem_of_isLeftAdjoint hW _) (hW.id_mem (Cat.of A))

/-- **Layer 2.3.** Two functors related by a natural transformation are both in a basic
localizer or both outside it (Cisinski 2004, Proposition 1.1.9). -/
theorem mem_iff_of_natTrans {A B : Type u} [SmallCategory A] [SmallCategory B] {u v : A ⥤ B}
    (α : u ⟶ v) : W u.toCatHom ↔ W v.toCatHom := by
  have h₀ := mem_sectR hW (A := A) 0
  have h₁ := mem_sectR hW (A := A) 1
  have e₀ : (Prod.sectR 0 A).toCatHom ≫ (cylinder α).toCatHom = u.toCatHom :=
    congrArg Functor.toCatHom (sectR_zero_comp_cylinder α)
  have e₁ : (Prod.sectR 1 A).toCatHom ≫ (cylinder α).toCatHom = v.toCatHom :=
    congrArg Functor.toCatHom (sectR_one_comp_cylinder α)
  constructor
  · intro hu
    rw [← e₁]
    exact hW.comp_mem _ _ h₁ (hW.of_precomp _ _ h₀ (e₀ ▸ hu))
  · intro hv
    rw [← e₀]
    exact hW.comp_mem _ _ h₀ (hW.of_precomp _ _ h₁ (e₁ ▸ hv))

/-- **Layer 2.3.** Functors with a left adjoint are in every basic localizer
(Cisinski 2004, Corollary 1.1.10). -/
theorem mem_of_isRightAdjoint {A B : Type u} [SmallCategory A] [SmallCategory B] (F : A ⥤ B)
    [F.IsRightAdjoint] : W F.toCatHom := by
  let adj := Adjunction.ofIsRightAdjoint F
  have hL : W F.leftAdjoint.toCatHom := by
    have := adj.isLeftAdjoint
    exact mem_of_isLeftAdjoint hW _
  have hLF : W (F.leftAdjoint ⋙ F).toCatHom :=
    (mem_iff_of_natTrans hW adj.unit).1 (hW.id_mem (Cat.of B))
  exact hW.of_precomp _ _ hL hLF

end TheoremA

/-- **Layer 2.5.** `W`-locally constant functors (Cisinski 2004, 2.3.1): every `A/b ⥤ A/b'` is
in `W`. -/
def IsLocallyConstant (W : MorphismProperty Cat.{u, u}) {A B : Type u} [SmallCategory A]
    [SmallCategory B] (F : A ⥤ B) : Prop :=
  ∀ ⦃b b' : B⦄ (g : b ⟶ b'), W (CostructuredArrow.map (S := F) g).toCatHom

end LeanPool.HomotopyTheoryOfCategories
