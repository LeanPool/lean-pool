/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Functor.KanExtension.RestrictedYoneda
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Diaconescu's theorem: the existence half

Diaconescu's theorem identifies the left exact left adjoints `Sh(C, J) ⥤ E` with the flat
`J`-continuous functors `C ⥤ E`. This file proves the existence half (a flat continuous functor
extends to a left exact left adjoint) in two cases: for presheaf topoi `E = Dᵒᵖ ⥤ Type u`, and
for left exact functors `C ⥤ Sh(D, K)` when `C` has finite limits.

**Presheaf topoi.** A functor `F : C ⥤ (Dᵒᵖ ⥤ Type u)` is *flat and `J`-continuous pointwise*
when, for every object `d` of `D`, the functor `F(-)(d) : C ⥤ Type u` is flat (its category of
elements is cofiltered) and sends the `J`-covering sieves to jointly surjective families. These
are exactly the conditions for `F(-)(d)` to be the fiber functor of a point of the site
(`GrothendieckTopology.Point`, SGA 4 IV 6.3). The extension is computed at each `d` by the fiber
functor of this point: a filtered colimit over the elements of `F(-)(d)`, which commutes with
finite limits in `Type u` and inverts the morphisms inverted by sheafification.

**Left exact functors.** When `C` has finite limits, a left exact `F : C ⥤ Sh(D, K)` is
pointwise flat as a functor to presheaves, so it extends to presheaves on `C` by the fiber
functors of the points of `(C, ⊥)`; after `K`-sheafification this extension inverts the
inclusions of the `J`-covering sieves exactly when `F` sends them to epimorphic families (the
image of an inclusion is a monomorphism, since the extension is left exact, and an epimorphism,
by continuity; `Sh(D, K)` is balanced).

In both cases the descent from presheaves to `J`-sheaves is
`LeanPool.ClassifyingTopoi.exists_presheafToSheaf_comp_iso`: a left exact left adjoint out of
presheaves inverting the inclusions of the covering sieves factors through `J`-sheafification.

## Main definitions

* `LeanPool.ClassifyingTopoi.pointsExtension`: the extension `Psh(C) ⥤ Psh(D)` of a functor
  `Dᵒᵖ ⥤ (J.Point)ᵒᵖ`, by the fiber functors of the points;
* `LeanPool.ClassifyingTopoi.IsPointwiseContinuous`, `LeanPool.ClassifyingTopoi.pointsOfFunctor`:
  pointwise `J`-continuity, and the points of `(C, J)` given by a pointwise flat and continuous
  functor;
* `LeanPool.ClassifyingTopoi.MapsCoversToEpimorphicFamilies`: `J`-continuity of a functor to
  `Sh(D, K)`.

## Main results

* `LeanPool.ClassifyingTopoi.exists_presheafToSheaf_comp_iso`: the descent to `J`-sheaves;
* `LeanPool.ClassifyingTopoi.exists_leftAdjoint_of_points`: for every functor
  `Φ : Dᵒᵖ ⥤ (J.Point)ᵒᵖ`, there is a left exact left adjoint `Sh(C, J) ⥤ (Dᵒᵖ ⥤ Type u)` whose
  composite with the sheafified Yoneda embedding is the functor of the fibers of the points;
* `LeanPool.ClassifyingTopoi.exists_leftAdjoint_of_flat` (**presheaf topoi**): a functor
  `C ⥤ (Dᵒᵖ ⥤ Type u)` which is flat and `J`-continuous pointwise extends to a left exact left
  adjoint `Sh(C, J) ⥤ (Dᵒᵖ ⥤ Type u)`; `exists_leftAdjoint_sheaf_of_flat`: so does its
  `K`-sheafification, to `Sh(D, K)`;
* `LeanPool.ClassifyingTopoi.exists_leftAdjoint_of_preservesFiniteLimits` (**left exact case**):
  for `C` with finite limits, a left exact functor `C ⥤ Sh(D, K)` sending the `J`-covering sieves
  to epimorphic families extends to a left exact left adjoint `Sh(C, J) ⥤ Sh(D, K)`.

## Not formalised

The existence half for an arbitrary site `C` and a functor `C ⥤ Sh(D, K)` that is flat in the
internal sense of `Sh(D, K)` (filtering): internal flatness is a local condition, weaker than
the existence of a pointwise flat lift to presheaves, and is not defined in Mathlib.

## References

* S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic*, VII.5–VII.9 (Theorem VII.7.2 for
  presheaf topoi, Theorem VII.9.1 for sites).
* P. T. Johnstone, *Sketches of an Elephant*, B3.2.7 (presheaf topoi) and C2.3.8 (sites).
* M. Artin, A. Grothendieck, J.-L. Verdier, SGA 4, IV 6.3 (points of a site).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite GrothendieckTopology

namespace LeanPool.ClassifyingTopoi

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

section Points

variable (J) in
/-- The fiber functors on presheaves of the points of a site, as a functor of the point. -/
noncomputable def pointPresheafFiberFunctor :
    (Point.{u} J)ᵒᵖ ⥤ (Cᵒᵖ ⥤ Type u) ⥤ Type u where
  obj Φ := Φ.unop.presheafFiber
  map f := Point.Hom.presheafFiber f.unop
  map_id _ := Point.Hom.presheafFiber_id _
  map_comp _ _ := Point.Hom.presheafFiber_comp _ _

variable (J) in
/-- The fiber functors `C ⥤ Type u` of the points of a site, as a functor of the point. -/
def pointFiberFunctor : (Point.{u} J)ᵒᵖ ⥤ (C ⥤ Type u) where
  obj Φ := Φ.unop.fiber
  map f := f.unop.hom

variable {Φ₁ Φ₂ : Point.{u} J} (f : Φ₁ ⟶ Φ₂)

/-- The fiber of a representable presheaf at a point is the fiber of the point. -/
noncomputable def yonedaCompPointPresheafFiberIso (Φ : Point.{u} J) :
    yoneda ⋙ Φ.presheafFiber ≅ Φ.fiber :=
  Functor.isoWhiskerRight shrinkYonedaIsoYoneda.symm _ ≪≫ Φ.shrinkYonedaCompPresheafFiberIso

/-- The isomorphism `shrinkYonedaCompPresheafFiberIso` is natural in the point. -/
theorem shrinkYonedaCompPresheafFiberIso_naturality (X : C) :
    f.presheafFiber.app (shrinkYoneda.obj X) ≫ Φ₁.shrinkYonedaCompPresheafFiberIso.hom.app X =
      Φ₂.shrinkYonedaCompPresheafFiberIso.hom.app X ≫ f.hom.app X := by
  have h : Φ₂.shrinkYonedaCompPresheafFiberIso.inv.app X ≫
      f.presheafFiber.app (shrinkYoneda.obj X) =
        f.hom.app X ≫ Φ₁.shrinkYonedaCompPresheafFiberIso.inv.app X := by
    ext x
    change f.presheafFiber.app (shrinkYoneda.obj X)
      (Φ₂.shrinkYonedaCompPresheafFiberIso.inv.app X x) =
        Φ₁.shrinkYonedaCompPresheafFiberIso.inv.app X (f.hom.app X x)
    rw [Point.shrinkYonedaCompPresheafFiberIso_inv_app_toPresheafFiber,
      Point.shrinkYonedaCompPresheafFiberIso_inv_app_toPresheafFiber]
    simp only [Point.Hom.presheafFiber_app]
    rw [← types_comp_apply (Φ₂.toPresheafFiber X x _)]
    exact types_congr_hom (Φ₂.toPresheafFiber_presheafFiberDesc _ _ X x) _
  rw [← cancel_epi (Φ₂.shrinkYonedaCompPresheafFiberIso.inv.app X), Iso.inv_hom_id_app_assoc,
    reassoc_of% h, Iso.inv_hom_id_app, Category.comp_id]

/-- The isomorphism `yonedaCompPointPresheafFiberIso` is natural in the point. -/
theorem yonedaCompPointPresheafFiberIso_naturality (X : C) :
    f.presheafFiber.app (yoneda.obj X) ≫ (yonedaCompPointPresheafFiberIso Φ₁).hom.app X =
      (yonedaCompPointPresheafFiberIso Φ₂).hom.app X ≫ f.hom.app X := by
  simp only [yonedaCompPointPresheafFiberIso, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Iso.symm_hom, Category.assoc]
  rw [← NatTrans.naturality_assoc, shrinkYonedaCompPresheafFiberIso_naturality]

end Points

section Descent

variable {E : Type*} [Category E] (G₀ : (Cᵒᵖ ⥤ Type u) ⥤ E) [G₀.IsLeftAdjoint]

/-- A left adjoint out of presheaves which inverts the inclusions of the `J`-covering sieves has a
right adjoint with values in `J`-sheaves. -/
theorem isSheaf_rightAdjoint_of_isIso_map
    (h : ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → IsIso (G₀.map (Sieve.shrinkFunctor.{u} S).ι))
    (Y : E) : Presheaf.IsSheaf J (G₀.rightAdjoint.obj Y) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro X S hS
  have := h S hS
  rw [Presieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp,
    ← (Adjunction.ofIsLeftAdjoint G₀).map_comp_bijective_iff]
  exact (Function.bijective_iff_has_inverse).2
    ⟨fun g => inv (G₀.map (Sieve.shrinkFunctor.{u} S).ι) ≫ g, fun g => by simp,
      fun g => by simp⟩

/-- A left adjoint out of presheaves which inverts the inclusions of the `J`-covering sieves
inverts every morphism inverted by `J`-sheafification. -/
theorem isIso_map_of_W
    (h : ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → IsIso (G₀.map (Sieve.shrinkFunctor.{u} S).ι))
    {P Q : Cᵒᵖ ⥤ Type u} (g : P ⟶ Q) (hg : J.W g) : IsIso (G₀.map g) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro T
  rw [(Adjunction.ofIsLeftAdjoint G₀).map_comp_bijective_iff]
  exact hg _ (isSheaf_rightAdjoint_of_isIso_map G₀ h T)

/-- A left exact left adjoint `G₀` out of presheaves which inverts the inclusions of the
`J`-covering sieves factors through `J`-sheafification, by a left exact left adjoint out of
`Sh(C, J)` (the restriction of `G₀` to `J`-sheaves). -/
theorem exists_presheafToSheaf_comp_iso [PreservesFiniteLimits G₀]
    (h : ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → IsIso (G₀.map (Sieve.shrinkFunctor.{u} S).ι)) :
    ∃ (G : Sheaf J (Type u) ⥤ E) (_ : PreservesFiniteLimits G), G.IsLeftAdjoint ∧
      Nonempty (presheafToSheaf J (Type u) ⋙ G ≅ G₀) := by
  let R : E ⥤ Sheaf J (Type u) :=
    ObjectProperty.lift _ G₀.rightAdjoint (isSheaf_rightAdjoint_of_isIso_map G₀ h)
  let adj : sheafToPresheaf J (Type u) ⋙ G₀ ⊣ R :=
    (Adjunction.ofIsLeftAdjoint G₀).restrictFullyFaithful
      (iC := sheafToPresheaf J (Type u)) (iD := 𝟭 _) (.ofFullyFaithful _)
      (Functor.FullyFaithful.id _) (Functor.rightUnitor _).symm
      (NatIso.ofComponents fun _ => Iso.refl _)
  have : IsIso (Functor.whiskerRight (sheafificationAdjunction J (Type u)).unit G₀) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun P => isIso_map_of_W G₀ h _ (J.W_adj_unit_app _ P)
  exact ⟨_, comp_preservesFiniteLimits _ _, adj.isLeftAdjoint,
    ⟨((Functor.leftUnitor _).symm ≪≫
      asIso (Functor.whiskerRight (sheafificationAdjunction J (Type u)).unit G₀) ≪≫
        Functor.associator _ _ _).symm⟩⟩

end Descent

section Extension

variable {D : Type u} [SmallCategory D] (Φ : Dᵒᵖ ⥤ (Point.{u} J)ᵒᵖ)

/-- The extension `Psh(C) ⥤ Psh(D)` of a functor `Φ : Dᵒᵖ ⥤ (J.Point)ᵒᵖ`: its value at a
presheaf `P` and an object `d` is the fiber of `P` at the point `Φ(d)`. -/
noncomputable def pointsExtension : (Cᵒᵖ ⥤ Type u) ⥤ (Dᵒᵖ ⥤ Type u) :=
  (Φ ⋙ pointPresheafFiberFunctor J).flip

/-- Evaluating the extension at an object is the fiber functor of the corresponding point. -/
noncomputable def pointsExtensionCompEvaluationIso (d : Dᵒᵖ) :
    pointsExtension Φ ⋙ (evaluation _ _).obj d ≅ (Φ.obj d).unop.presheafFiber :=
  Iso.refl _

instance : PreservesFiniteLimits (pointsExtension Φ) :=
  preservesFiniteLimits_of_evaluation _ fun d =>
    preservesFiniteLimits_of_natIso (pointsExtensionCompEvaluationIso Φ d).symm

instance : PreservesColimitsOfSize.{u, u} (pointsExtension Φ) :=
  preservesColimits_of_evaluation _ fun d =>
    preservesColimits_of_natIso (pointsExtensionCompEvaluationIso Φ d).symm

/-- The extension inverts the morphisms inverted by sheafification. -/
theorem isIso_pointsExtension_map {P Q : Cᵒᵖ ⥤ Type u} (g : P ⟶ Q) (hg : J.W g) :
    IsIso ((pointsExtension Φ).map g) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro d
  exact (Φ.obj d).unop.W_isInvertedBy_presheafFiber g hg

/-- The extension, composed with the Yoneda embedding, is the functor of the fibers of the
points. -/
noncomputable def yonedaCompPointsExtensionIso :
    yoneda ⋙ pointsExtension Φ ≅ (Φ ⋙ pointFiberFunctor J).flip :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun d => (yonedaCompPointPresheafFiberIso (Φ.obj d).unop).app X)
      (fun g => yonedaCompPointPresheafFiberIso_naturality _ X))
    (fun g => by
      ext d : 2
      exact ((yonedaCompPointPresheafFiberIso (Φ.obj d).unop).hom.naturality g))

instance : (pointsExtension Φ).IsLeftAdjoint :=
  Presheaf.isLeftAdjoint_of_preservesColimits _

/-- The extension of a functor `Φ : Dᵒᵖ ⥤ (J.Point)ᵒᵖ` to `J`-sheaves is a left exact left
adjoint `Sh(C, J) ⥤ (Dᵒᵖ ⥤ Type u)` whose composite with the sheafified Yoneda embedding is the
functor of the fibers of the points. -/
theorem exists_leftAdjoint_of_points :
    ∃ (G : Sheaf J (Type u) ⥤ (Dᵒᵖ ⥤ Type u)) (_ : PreservesFiniteLimits G), G.IsLeftAdjoint ∧
      Nonempty (yoneda ⋙ presheafToSheaf J (Type u) ⋙ G ≅ (Φ ⋙ pointFiberFunctor J).flip) :=
  have h X S hS : IsIso ((pointsExtension Φ).map (Sieve.shrinkFunctor.{u} S).ι) :=
    isIso_pointsExtension_map Φ _ (Sieve.W_shrinkFunctor_ι_of_mem (X := X) J S hS)
  let ⟨G, hG, hG', ⟨e⟩⟩ := exists_presheafToSheaf_comp_iso (J := J) (pointsExtension Φ) h
  ⟨G, hG, hG', ⟨Functor.isoWhiskerLeft yoneda e ≪≫ yonedaCompPointsExtensionIso Φ⟩⟩

end Extension

section Flat

variable {D : Type u} [SmallCategory D] (F : C ⥤ (Dᵒᵖ ⥤ Type u))

/-- A functor `F : C ⥤ (Dᵒᵖ ⥤ Type u)` is `J`-continuous pointwise when, for every object `d`,
the functor `F(-)(d)` sends the `J`-covering sieves to jointly surjective families: every
element of `F(X)(d)` comes from an element of `F(Y)(d)` along a morphism `Y ⟶ X` of the sieve. -/
def IsPointwiseContinuous : Prop :=
  ∀ (d : Dᵒᵖ) {X : C} (S : Sieve X), S ∈ J X → ∀ x : (F.obj X).obj d,
    ∃ (Y : C) (f : Y ⟶ X) (_ : S f) (y : (F.obj Y).obj d), (F.map f).app d y = x

variable [∀ d, IsCofiltered (F ⋙ (evaluation Dᵒᵖ (Type u)).obj d).Elements]
  (hF : IsPointwiseContinuous (J := J) F)

/-- The points of `(C, J)` given by a functor `F : C ⥤ (Dᵒᵖ ⥤ Type u)` which is flat and
`J`-continuous pointwise: the point at `d` has fiber functor `F(-)(d)`. -/
noncomputable def pointsOfFunctor : Dᵒᵖ ⥤ (Point.{u} J)ᵒᵖ where
  obj d := op
    { fiber := F ⋙ (evaluation Dᵒᵖ (Type u)).obj d
      initiallySmall := initiallySmall_of_essentiallySmall _
      jointly_surjective := fun S hS x => hF d S hS x }
  map g := op ⟨Functor.whiskerLeft F ((evaluation Dᵒᵖ (Type u)).map g)⟩
  map_id d := by
    apply Quiver.Hom.unop_inj
    apply Point.hom_ext
    ext X x
    simp
  map_comp g g' := by
    apply Quiver.Hom.unop_inj
    apply Point.hom_ext
    ext X x
    simp

/-- The functor of the fibers of the points given by `F` is `F`. -/
noncomputable def pointsOfFunctorFiberIso :
    (pointsOfFunctor F hF ⋙ pointFiberFunctor J).flip ≅ F :=
  NatIso.ofComponents (fun X => NatIso.ofComponents (fun d => Iso.refl _) (fun g => by
    ext x
    simp [pointsOfFunctor, pointFiberFunctor])) (fun g => by
    ext d x
    simp [pointsOfFunctor, pointFiberFunctor])

include hF in
/-- **Existence half of Diaconescu's theorem for presheaf topoi.** A functor
`F : C ⥤ (Dᵒᵖ ⥤ Type u)` such that every `F(-)(d)` is flat (its category of elements is
cofiltered) and sends the `J`-covering sieves to jointly surjective families extends to a left
exact left adjoint `G : Sh(C, J) ⥤ (Dᵒᵖ ⥤ Type u)`: the composite of `G` with the sheafified
Yoneda embedding is isomorphic to `F`. -/
theorem exists_leftAdjoint_of_flat :
    ∃ (G : Sheaf J (Type u) ⥤ (Dᵒᵖ ⥤ Type u)) (_ : PreservesFiniteLimits G), G.IsLeftAdjoint ∧
      Nonempty (yoneda ⋙ presheafToSheaf J (Type u) ⋙ G ≅ F) := by
  obtain ⟨G, hG, hG', ⟨e⟩⟩ := exists_leftAdjoint_of_points (pointsOfFunctor F hF)
  exact ⟨G, hG, hG', ⟨e ≪≫ pointsOfFunctorFiberIso F hF⟩⟩

include hF in
/-- For a Grothendieck topology `K` on `D`, the sheafification `F ⋙ a_K` of a functor
`F : C ⥤ (Dᵒᵖ ⥤ Type u)` which is flat and `J`-continuous pointwise extends to a left exact left
adjoint `Sh(C, J) ⥤ Sh(D, K)`. -/
theorem exists_leftAdjoint_sheaf_of_flat (K : GrothendieckTopology D) :
    ∃ (G : Sheaf J (Type u) ⥤ Sheaf K (Type u)) (_ : PreservesFiniteLimits G), G.IsLeftAdjoint ∧
      Nonempty (yoneda ⋙ presheafToSheaf J (Type u) ⋙ G ≅ F ⋙ presheafToSheaf K (Type u)) := by
  obtain ⟨G, hG, hG', ⟨e⟩⟩ := exists_leftAdjoint_of_flat F hF
  have : (presheafToSheaf K (Type u)).IsLeftAdjoint :=
    (sheafificationAdjunction K (Type u)).isLeftAdjoint
  exact ⟨G ⋙ presheafToSheaf K (Type u), comp_preservesFiniteLimits _ _, inferInstance,
    ⟨(Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
      ((Functor.associator _ _ _).symm ≪≫ e) _⟩⟩

end Flat

section LeftExact

variable {D : Type u} [SmallCategory D]

/-- Every functor to presheaves is continuous pointwise for the trivial topology, whose only
covering sieves are the maximal ones. -/
theorem isPointwiseContinuous_bot (F : C ⥤ (Dᵒᵖ ⥤ Type u)) :
    IsPointwiseContinuous (J := (⊥ : GrothendieckTopology C)) F := by
  intro d X S hS x
  rw [GrothendieckTopology.bot_covering] at hS
  subst hS
  exact ⟨X, 𝟙 X, trivial, x, by simp⟩

variable [HasFiniteLimits C] {K : GrothendieckTopology D} (F : C ⥤ Sheaf K (Type u))
  [PreservesFiniteLimits F]

/-- A functor `F : C ⥤ Sh(D, K)` is `J`-continuous when it sends the `J`-covering sieves to
epimorphic families: two morphisms out of `F(X)` that agree after every `F(f)`, `f` in a covering
sieve of `X`, are equal. -/
def MapsCoversToEpimorphicFamilies : Prop :=
  ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → ∀ {Z : Sheaf K (Type u)} (g h : F.obj X ⟶ Z),
    (∀ ⦃Y : C⦄ (f : Y ⟶ X), S f → F.map f ≫ g = F.map f ≫ h) → g = h

instance (d : Dᵒᵖ) : IsCofiltered
    ((F ⋙ sheafToPresheaf K (Type u)) ⋙ (evaluation Dᵒᵖ (Type u)).obj d).Elements := by
  have := flat_of_preservesFiniteLimits
    ((F ⋙ sheafToPresheaf K (Type u)) ⋙ (evaluation Dᵒᵖ (Type u)).obj d)
  exact IsCofiltered.of_equivalence (Functor.Elements.structuredArrowEquivalence _).symm

/-- **Existence half of Diaconescu's theorem, left exact case.** Let `C` have finite limits. A
left exact functor `F : C ⥤ Sh(D, K)` which sends the `J`-covering sieves to epimorphic families
extends to a left exact left adjoint `G : Sh(C, J) ⥤ Sh(D, K)`: the composite of `G` with the
sheafified Yoneda embedding is isomorphic to `F`. -/
theorem exists_leftAdjoint_of_preservesFiniteLimits
    (hF : MapsCoversToEpimorphicFamilies (J := J) F) :
    ∃ (G : Sheaf J (Type u) ⥤ Sheaf K (Type u)) (_ : PreservesFiniteLimits G), G.IsLeftAdjoint ∧
      Nonempty (yoneda ⋙ presheafToSheaf J (Type u) ⋙ G ≅ F) := by
  let F' := F ⋙ sheafToPresheaf K (Type u)
  let Φ := pointsOfFunctor (J := (⊥ : GrothendieckTopology C)) F' (isPointwiseContinuous_bot F')
  let G₀ := pointsExtension Φ ⋙ presheafToSheaf K (Type u)
  have : (presheafToSheaf K (Type u)).IsLeftAdjoint :=
    (sheafificationAdjunction K (Type u)).isLeftAdjoint
  have : PreservesFiniteLimits G₀ := comp_preservesFiniteLimits _ _
  let e : yoneda ⋙ G₀ ≅ F := (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (yonedaCompPointsExtensionIso Φ ≪≫
      pointsOfFunctorFiberIso F' (isPointwiseContinuous_bot F')) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F (asIso (sheafificationAdjunction K (Type u)).counit) ≪≫
    Functor.rightUnitor F
  let es : shrinkYoneda.{u} ⋙ G₀ ≅ F := Functor.isoWhiskerRight shrinkYonedaIsoYoneda G₀ ≪≫ e
  have h : ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X →
      IsIso (G₀.map (Sieve.shrinkFunctor.{u} S).ι) := by
    intro X S hS
    have : Epi (G₀.map (Sieve.shrinkFunctor.{u} S).ι) := ⟨fun {Z} g g' hgg' => by
      have key : es.inv.app X ≫ g = es.inv.app X ≫ g' := hF S hS _ _ fun Y f hf => by
        have hr : Subfunctor.range (shrinkYoneda.{u}.map f) ≤ Sieve.shrinkFunctor.{u} S := by
          rintro Z _ ⟨x, rfl⟩
          obtain ⟨x, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective x
          simp only [Sieve.shrinkFunctor_obj, Set.mem_ofPred_eq,
            shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm, Equiv.apply_symm_apply]
          exact S.downward_closed hf x
        rw [es.inv.naturality_assoc, es.inv.naturality_assoc, Functor.comp_map,
          ← Subfunctor.lift_ι _ hr, G₀.map_comp, Category.assoc, Category.assoc, hgg']
      simpa using congrArg (es.hom.app X ≫ ·) key⟩
    exact isIso_of_mono_of_epi _
  obtain ⟨G, hG, hG', ⟨e'⟩⟩ := exists_presheafToSheaf_comp_iso (J := J) G₀ h
  exact ⟨G, hG, hG', ⟨Functor.isoWhiskerLeft yoneda e' ≪≫ e⟩⟩

end LeftExact

end LeanPool.ClassifyingTopoi
