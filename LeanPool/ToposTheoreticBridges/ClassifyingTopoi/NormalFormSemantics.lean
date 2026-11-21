/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.NormalForm
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.TypeSemantics
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Homomorphisms
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Images

/-!
# The normal form of geometric formulas in sheaf topoi

We prove roadmap 2.2 (b), `GeometricFormula.exists_interp_eq_iSup_exs`: in every topos of
sheaves on a small site, a geometric formula has the same interpretation as a `u`-small
disjunction of existential quantifications of Horn formulas, its normal form
(`GeometricFormula.normalForm`).

## Method

The normal form is equivalent to the formula in every structure on a type
(`GeometricFormula.realize_iSup_exs_normalForm`). We transfer such set-theoretic equivalences to
every sheaf topos (`CatStructure.interp_eq_of_realize_iff`):

* in `Type u`, every structure is isomorphic to the structure on a type it induces
  (`CatStructure.isomorphic_ofStructure`), where the categorical semantics is the
  set-theoretic one (`CatStructure.interp_ofStructure_le_iff`), and isomorphic structures have
  corresponding interpretations (`CatStructure.Isomorphic.interp_eq`);
* in a presheaf topos, the evaluations at the objects of the site preserve finite limits,
  epimorphisms and coproducts, so commute with interpretations (`CatStructure.interp_map`), and
  jointly detect the order of subobjects (`CatStructure.presheaf_le_of_range_subset`);
* in a sheaf topos, every structure is isomorphic to the sheafification of its underlying
  presheaf structure, and sheafification commutes with interpretations.

No regularity or extensivity property of sheaf topoi is needed beyond those used in
`LeanPool.ClassifyingTopoi.InverseImage`.
-/

@[expose] public section

universe w u₁ u₂ v u

open CategoryTheory CategoryTheory.Limits

namespace LeanPool.ClassifyingTopoi

variable {L : FirstOrder.Language.{u₁, u₂}}

namespace CatStructure

/-- Isomorphic structures have interpretations related by the isomorphism. -/
theorem Isomorphic.interp_eq {E : Type u} [Category.{v} E] [HasFiniteLimits E] [HasImages E]
    [HasCoproducts.{w} E] {M N : CatStructure L E} (h : M.Isomorphic N)
    {n : ℕ} {φ ψ : GeometricFormula.{w} L n} (hφψ : M.interp φ = M.interp ψ) :
    N.interp φ = N.interp ψ := by
  obtain ⟨e, h₁, h₂⟩ := h
  have key : ∀ χ : GeometricFormula.{w} L n, N.interp χ =
      (Subobject.pullback (Limits.Pi.map fun _ : Fin n => e.inv)).obj (M.interp χ) := fun χ => by
    refine le_antisymm (h₂.interp_le χ) (((Subobject.pullback _).monotone
      (h₁.interp_le χ)).trans (le_of_eq ?_))
    rw [← Subobject.pullback_comp]
    have : (Limits.Pi.map fun _ : Fin n => e.inv) ≫ (Limits.Pi.map fun _ => e.hom) = 𝟙 _ := by
      ext
      simp
    rw [this, Subobject.pullback_id]
  rw [key, key, hφψ]

/-- The order of subobjects of a functor to types is the objectwise inclusion of ranges. -/
theorem _root_.LeanPool.ClassifyingTopoi.Syntactic.le_iff_range_app_subset {D : Type*} [Category D]
    {X : D ⥤ Type w} (S T : Subobject X) :
    S ≤ T ↔ ∀ d, Set.range (S.arrow.app d) ⊆ Set.range (T.arrow.app d) := by
  constructor
  · intro h d
    rintro _ ⟨s, rfl⟩
    exact ⟨(Subobject.ofLE S T h).app d s, by
      rw [← NatTrans.comp_app_apply, Subobject.ofLE_arrow]⟩
  · intro h
    have inj : ∀ d, Function.Injective (T.arrow.app d) := fun d =>
      (mono_iff_injective _).1 inferInstance
    choose g hg using fun d (s : (S : D ⥤ Type w).obj d) => h d ⟨s, rfl⟩
    refine Subobject.le_of_comm { app := fun d => TypeCat.ofHom (g d), naturality := ?_ } ?_
    · intro d d' f
      ext s
      apply inj d'
      simp [hg, NatTrans.naturality_apply]
    · ext d s
      exact hg d s

section Types

/-- The `L`-structure on the carrier of a structure in `Type u`. -/
@[instance_reducible]
noncomputable def toStructure (M : CatStructure L (Type u)) : L.Structure M.carrier where
  funMap f x := M.funMap f ((Types.productIso _).inv x)
  RelMap R x := (Types.productIso _).inv x ∈ Set.range (M.relMap R).hom

/-- A structure in `Type u` is a structure on a type, through the identity. -/
theorem isHom_ofStructure_id (M : CatStructure L (Type u)) :
    M.IsHom (@ofStructure L M.carrier M.toStructure) (𝟙 _) := by
  let := M.toStructure
  refine ⟨fun {k} f => ?_, fun {k} R => ?_⟩
  · simp only [Limits.Pi.map_id, Category.comp_id, Category.id_comp]
    ext x
    change _ = M.funMap f ((Types.productIso _).inv ((Types.productIso _).hom x))
    simp
  · simp only [Limits.Pi.map_id, Subobject.pullback_id]
    rw [TypeSubobject.le_iff_range_subset, TypeSubobject.range_imageSubobject_arrow,
      TypeSubobject.range_imageSubobject_arrow]
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨(Types.productIso _).hom ((M.relMap R).hom z), z, ?_⟩, ?_⟩
    · simp
    · simp

/-- A structure on a type is a structure in `Type u`, through the identity. -/
theorem isHom_ofStructure_id' (M : CatStructure L (Type u)) :
    (@ofStructure L M.carrier M.toStructure).IsHom M (𝟙 _) := by
  let := M.toStructure
  refine ⟨fun {k} f => ?_, fun {k} R => ?_⟩
  · simp only [Limits.Pi.map_id, Category.comp_id, Category.id_comp]
    ext x
    change M.funMap f ((Types.productIso _).inv ((Types.productIso _).hom x)) = _
    simp
  · simp only [Limits.Pi.map_id, Subobject.pullback_id]
    rw [TypeSubobject.le_iff_range_subset, TypeSubobject.range_imageSubobject_arrow,
      TypeSubobject.range_imageSubobject_arrow]
    rintro _ ⟨⟨x, z, hz⟩, rfl⟩
    exact ⟨z, hz⟩

/-- A structure in `Type u` is isomorphic to the structure on a type that it induces. -/
theorem isomorphic_ofStructure (M : CatStructure L (Type u)) :
    M.Isomorphic (@ofStructure L M.carrier M.toStructure) :=
  ⟨Iso.refl _, isHom_ofStructure_id M, isHom_ofStructure_id' M⟩

/-- In `Type u`, two geometric formulas equivalent in every structure on a type have the same
interpretation. -/
theorem interp_eq_of_realize_iff_of_type (M : CatStructure L (Type u)) {n : ℕ}
    {φ ψ : GeometricFormula.{u} L n}
    (h : ∀ (N : Type u) [L.Structure N] (x : Fin n → N), φ.Realize x ↔ ψ.Realize x) :
    M.interp φ = M.interp ψ := by
  let := M.toStructure
  exact (isomorphic_ofStructure M).symm.interp_eq (le_antisymm
    ((interp_ofStructure_le_iff M.carrier φ ψ).2 fun x => (h _ x).1)
    ((interp_ofStructure_le_iff M.carrier ψ φ).2 fun x => (h _ x).2))

end Types

section Presheaves

variable {D : Type u} [SmallCategory D]

/-- A subobject of a presheaf of types lies below another when it does so objectwise. -/
theorem presheaf_le_of_range_subset {X : Dᵒᵖ ⥤ Type u} {S T : Subobject X}
    (h : ∀ d, Set.range (S.arrow.app d) ⊆ Set.range (T.arrow.app d)) : S ≤ T :=
  (Syntactic.le_iff_range_app_subset S T).2 h

/-- The evaluation of a presheaf subobject at an object, through an isomorphism. -/
theorem range_subset_of_mapSubobject_evaluation_le {X : Dᵒᵖ ⥤ Type u} {Y : Type u} (d : Dᵒᵖ)
    (c : ((evaluation Dᵒᵖ (Type u)).obj d).obj X ⟶ Y) [IsIso c] {S T : Subobject X}
    (h : mapSubobject ((evaluation Dᵒᵖ (Type u)).obj d) c S ≤
      mapSubobject ((evaluation Dᵒᵖ (Type u)).obj d) c T) :
    Set.range (S.arrow.app d) ⊆ Set.range (T.arrow.app d) := by
  rw [TypeSubobject.le_iff_range_subset, TypeSubobject.range_mk_arrow,
    TypeSubobject.range_mk_arrow] at h
  have inj : Function.Injective c := ((isIso_iff_bijective c).1 inferInstance).1
  rintro _ ⟨s, rfl⟩
  obtain ⟨t, ht⟩ := h ⟨s, rfl⟩
  exact ⟨t, inj ht⟩

/-- In a presheaf topos, two geometric formulas whose interpretations agree after evaluation at
every object have the same interpretation. -/
theorem interp_eq_of_evaluation (M : CatStructure L (Dᵒᵖ ⥤ Type u)) {n : ℕ}
    {φ ψ : GeometricFormula.{u} L n}
    (h : ∀ d, (M.map ((evaluation Dᵒᵖ (Type u)).obj d)).interp φ =
      (M.map ((evaluation Dᵒᵖ (Type u)).obj d)).interp ψ) :
    M.interp φ = M.interp ψ := by
  simp only [interp_map] at h
  exact le_antisymm
    (presheaf_le_of_range_subset fun d => range_subset_of_mapSubobject_evaluation_le d _
      (h d).le)
    (presheaf_le_of_range_subset fun d => range_subset_of_mapSubobject_evaluation_le d _
      (h d).ge)

end Presheaves

attribute [local instance high] Sheaf.instHasColimitsOfShape in
/-- A structure in a sheaf topos is isomorphic to the sheafification of its underlying
presheaf structure. -/
theorem isomorphic_map_sheafToPresheaf_map_presheafToSheaf {D : Type u} [SmallCategory D]
    {K : GrothendieckTopology D} (M : CatStructure L (Sheaf K (Type u))) :
    M.Isomorphic ((M.map (sheafToPresheaf K (Type u))).map (presheafToSheaf K (Type u))) :=
  (M.isomorphic_map_id).symm.trans ((M.isomorphic_map_of_iso
    (asIso (sheafificationAdjunction K (Type u)).counit).symm).trans
      (M.isomorphic_map_comp _ _))

attribute [local instance high] Sheaf.instHasColimitsOfShape in
/-- Two geometric formulas equivalent in every structure on a type have the same interpretation
in every structure in a topos of sheaves on a small site. -/
theorem interp_eq_of_realize_iff {n : ℕ} {φ ψ : GeometricFormula.{u} L n}
    (h : ∀ (N : Type u) [L.Structure N] (x : Fin n → N), φ.Realize x ↔ ψ.Realize x)
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    (M : CatStructure L (Sheaf K (Type u))) : M.interp φ = M.interp ψ := by
  refine (isomorphic_map_sheafToPresheaf_map_presheafToSheaf M).symm.interp_eq ?_
  rw [interp_map (M.map (sheafToPresheaf K (Type u))) (presheafToSheaf K (Type u)),
    interp_map (M.map (sheafToPresheaf K (Type u))) (presheafToSheaf K (Type u)),
    interp_eq_of_evaluation _ fun d =>
    interp_eq_of_realize_iff_of_type _ h]

end CatStructure

attribute [local instance high] Sheaf.instHasColimitsOfShape in
/-- **2.2 (b).** The normal form: in every sheaf topos, a geometric formula has the
interpretation of a `u`-small disjunction of existential quantifications of Horn formulas. -/
theorem GeometricFormula.exists_interp_eq_iSup_exs {n : ℕ} (φ : GeometricFormula.{u} L n) :
    ∃ (ι : Type u) (m : ι → ℕ) (θ : ∀ i, GeometricFormula.{u} L (n + m i)),
      (∀ i, (θ i).IsHorn) ∧ ∀ (D : Type u) [SmallCategory D] (K : GrothendieckTopology D)
        (M : CatStructure L (Sheaf K (Type u))),
        M.interp φ = M.interp (.iSup fun i => (θ i).exs) :=
  ⟨_, _, (normalForm φ).θ, (normalForm φ).isHorn, fun _ _ _ M =>
    CatStructure.interp_eq_of_realize_iff (fun _ _ x => realize_iSup_exs_normalForm φ x) M⟩

end LeanPool.ClassifyingTopoi
