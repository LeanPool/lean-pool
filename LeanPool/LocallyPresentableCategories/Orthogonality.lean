/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.CategoryTheory.Presentable.OrthogonalReflection
public import Mathlib.CategoryTheory.Presentable.Presheaf
public import Mathlib.CategoryTheory.Presentable.Limits
public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Limit preservation as an orthogonality condition

Let `T` be a small category and `c` a cone over `K : J ⥤ T`, with `J` small. In the functor
category `T ⥤ Type w` we consider the comparison map
`limitComparison c : colim_j coyoneda (K j) ⟶ coyoneda c.pt`.
We show (`bijective_limitComparison_iff`) that a functor `F : T ⥤ Type w` is orthogonal to
this map exactly when `F` sends `c` to a limit cone.

Given a small family of small shapes `S : ι → Type w`, the comparison maps attached to all limit
cones of shape `S i` form a small class `limitComparisons S T` of morphisms, whose local objects
are exactly the functors preserving limits of all shapes `S i`
(`isLocal_limitComparisons`). When every `S i` has fewer than `κ` arrows, these maps are maps
between `κ`-presentable objects (`isCardinalPresentable_limitComparisons`), so that Mathlib's
orthogonal-reflection theorem applies: the functors preserving these limits form a reflective,
locally `κ`-presentable subcategory of `T ⥤ Type w`
(`isRightAdjoint_ι_preservesLimitsOfShapes`,
`isCardinalLocallyPresentable_preservesLimitsOfShapes`).
This is Kelly's Theorem 6.11 (*Basic concepts of enriched category theory*) at `V = Set`.
-/

@[expose] public section

namespace LeanPool.LocallyPresentableCategories

open CategoryTheory Limits Opposite

universe w

section LimitComparison

variable {T : Type w} [SmallCategory T] {J : Type w} [SmallCategory J] {K : J ⥤ T}

/-- The comparison map `colim_j coyoneda (K j) ⟶ coyoneda c.pt` in `T ⥤ Type w` attached to a
cone `c` over `K`. -/
noncomputable def limitComparison (c : Cone K) :
    colimit (K.op ⋙ coyoneda) ⟶ coyoneda.obj (op c.pt) :=
  colimit.desc _ (coyoneda.mapCocone c.op)

/-- A morphism `colim_j coyoneda (K j) ⟶ F` gives a section of `K ⋙ F`. -/
noncomputable def colimitHomToSections (F : T ⥤ Type w)
    (g : colimit (K.op ⋙ coyoneda) ⟶ F) : (K ⋙ F).sections :=
  ⟨fun j ↦ coyonedaEquiv (X := K.obj j) (colimit.ι (K.op ⋙ coyoneda) (op j) ≫ g),
    fun {j j'} u ↦ by
    change F.map (K.map u) (coyonedaEquiv (colimit.ι (K.op ⋙ coyoneda) (op j) ≫ g)) =
      coyonedaEquiv (colimit.ι (K.op ⋙ coyoneda) (op j') ≫ g)
    rw [coyonedaEquiv_naturality, ← colimit.w (K.op ⋙ coyoneda) u.op, Category.assoc]
    rfl⟩

lemma bijective_colimitHomToSections (F : T ⥤ Type w) :
    Function.Bijective (colimitHomToSections (K := K) F) := by
  refine ⟨fun g₁ g₂ h ↦ colimit.hom_ext fun j ↦ ?_, fun s ↦ ?_⟩
  · exact coyonedaEquiv.injective (congr_arg (fun s ↦ s.1 j.unop) h :)
  · refine ⟨colimit.desc _
      { pt := F
        ι := { app j := (coyonedaEquiv (X := K.obj j.unop)).symm (s.1 j.unop)
               naturality {j j'} u := by
                 dsimp
                 rw [Category.comp_id, ← s.2 u.unop]
                 exact (coyonedaEquiv_symm_map (K.map u.unop) _).symm } }, ?_⟩
    ext j
    simp [colimitHomToSections]

lemma colimitHomToSections_limitComparison_comp (c : Cone K) (F : T ⥤ Type w)
    (g : coyoneda.obj (op c.pt) ⟶ F) :
    colimitHomToSections F (limitComparison c ≫ g) =
      Types.sectionOfCone (F.mapCone c) (coyonedaEquiv g) := by
  ext j
  simp [colimitHomToSections, limitComparison, coyonedaEquiv_naturality]

/-- A functor `F : T ⥤ Type w` is orthogonal to `limitComparison c` iff it sends `c` to a limit
cone. -/
theorem bijective_limitComparison_iff (c : Cone K) (F : T ⥤ Type w) :
    Function.Bijective (fun g : coyoneda.obj (op c.pt) ⟶ F ↦ limitComparison c ≫ g) ↔
      Nonempty (IsLimit (F.mapCone c)) := by
  rw [Types.isLimit_iff_bijective_sectionOfCone,
    ← Function.Bijective.of_comp_iff' (bijective_colimitHomToSections F),
    ← Function.Bijective.of_comp_iff _ coyonedaEquiv.symm.bijective]
  have h (x : F.obj c.pt) : colimitHomToSections F (limitComparison c ≫ coyonedaEquiv.symm x) =
      Types.sectionOfCone (F.mapCone c) x := by
    rw [colimitHomToSections_limitComparison_comp, Equiv.apply_symm_apply]
  exact Iff.of_eq (congrArg Function.Bijective (funext h))

end LimitComparison

section Presentable

variable {T : Type w} [SmallCategory T]

/-- Corepresentable functors `T ⥤ Type w` are `κ`-presentable for every regular `κ`. -/
instance isCardinalPresentable_coyoneda_obj (t : T) (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    IsCardinalPresentable (coyoneda.obj (op t)) κ where
  preservesColimitOfShape J _ _ := by
    let e : coyoneda.obj (op (coyoneda.obj (op t))) ≅ (evaluation T (Type w)).obj t :=
      NatIso.ofComponents (fun F ↦ Equiv.toIso coyonedaEquiv)
        (fun f ↦ by ext g; exact coyonedaEquiv_comp g f)
    exact preservesColimitsOfShape_of_natIso e.symm

/-- For a `κ`-small shape `J`, the source of `limitComparison c` is `κ`-presentable. -/
lemma isCardinalPresentable_colimit_coyoneda {J : Type w} [SmallCategory J] (K : J ⥤ T)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] (hJ : HasCardinalLT (Arrow J) κ) :
    IsCardinalPresentable (colimit (K.op ⋙ coyoneda)) κ := by
  have (j : Jᵒᵖ) : IsCardinalPresentable ((K.op ⋙ coyoneda).obj j) κ :=
    isCardinalPresentable_coyoneda_obj _ κ
  exact isCardinalPresentable_of_isColimit _ (colimit.isColimit _) κ (by simpa using hJ)

end Presentable

section Family

variable {ι : Type w} (S : ι → Type w) [∀ i, SmallCategory (S i)] (T : Type w) [SmallCategory T]

/-- The index type of all limit cones of the shapes `S i` in `T`. -/
def LimitConeIndex : Type w :=
  Σ (i : ι) (K : S i ⥤ T), {c : Cone K // Nonempty (IsLimit c)}

/-- The small class of comparison maps `limitComparison c`, for all limit cones `c` of all
the shapes `S i` in `T`. -/
noncomputable def limitComparisons : MorphismProperty (T ⥤ Type w) :=
  MorphismProperty.ofHoms (fun d : LimitConeIndex S T ↦ limitComparison d.2.2.1)

instance : MorphismProperty.IsSmall.{w} (limitComparisons S T) := by
  dsimp [limitComparisons]
  infer_instance

/-- The functors `T ⥤ Type w` preserving limits of every shape `S i`. -/
def preservesLimitsOfShapes : ObjectProperty (T ⥤ Type w) :=
  fun F ↦ ∀ i, PreservesLimitsOfShape (S i) F

/-- The functors local with respect to `limitComparisons S T` are exactly those preserving the
limits of all shapes `S i`. -/
theorem isLocal_limitComparisons :
    (limitComparisons S T).isLocal = preservesLimitsOfShapes S T := by
  ext F
  constructor
  · intro h i
    refine ⟨fun {K} ↦ ⟨fun {c} hc ↦ ?_⟩⟩
    exact (bijective_limitComparison_iff c F).1
      (h _ (MorphismProperty.ofHoms.mk (⟨i, K, c, ⟨hc⟩⟩ : LimitConeIndex S T)))
  · rintro h _ _ _ ⟨⟨i, K, c, ⟨hc⟩⟩⟩
    have := h i
    exact (bijective_limitComparison_iff c F).2 ⟨isLimitOfPreserves F hc⟩

variable {S T}

/-- When all shapes `S i` are `κ`-small, the maps in `limitComparisons S T` are maps between
`κ`-presentable objects. -/
lemma isCardinalPresentable_limitComparisons (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (hS : ∀ i, HasCardinalLT (Arrow (S i)) κ) ⦃X Y : T ⥤ Type w⦄ (f : X ⟶ Y)
    (hf : limitComparisons S T f) : IsCardinalPresentable X κ ∧ IsCardinalPresentable Y κ := by
  rcases hf with ⟨⟨i, K, c, _⟩⟩
  exact ⟨isCardinalPresentable_colimit_coyoneda K κ (hS i), inferInstance⟩

/-- The functors preserving limits of the `κ`-small shapes `S i` form a reflective subcategory
of `T ⥤ Type w` (Kelly, Theorem 6.11). -/
theorem isRightAdjoint_ι_preservesLimitsOfShapes (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (hS : ∀ i, HasCardinalLT (Arrow (S i)) κ) :
    (preservesLimitsOfShapes S T).ι.IsRightAdjoint := by
  rw [← isLocal_limitComparisons]
  exact MorphismProperty.isRightAdjoint_ι_isLocal _ κ
    (isCardinalPresentable_limitComparisons κ hS)

/-- The functors preserving limits of the `κ`-small shapes `S i` form a locally
`κ`-presentable category (Kelly, Theorem 6.11). -/
theorem isCardinalLocallyPresentable_preservesLimitsOfShapes (κ : Cardinal.{w})
    [Fact κ.IsRegular] (hS : ∀ i, HasCardinalLT (Arrow (S i)) κ) :
    IsCardinalLocallyPresentable (preservesLimitsOfShapes S T).FullSubcategory κ := by
  rw [← isLocal_limitComparisons]
  exact MorphismProperty.isLocallyPresentable_isLocal _ κ
    (isCardinalPresentable_limitComparisons κ hS)

end Family

end LeanPool.LocallyPresentableCategories
