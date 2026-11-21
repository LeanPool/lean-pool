/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Bridges
public import LeanPool.ToposTheoreticBridges.Subtopos
public import Mathlib.CategoryTheory.Localization.Adjunction

/-!
# Diaconescu's theorem: the localisation half and uniqueness

Diaconescu's theorem identifies the inverse images of geometric morphisms
`E ⥤ Sh(C, J)`, the left exact left adjoints `Sh(C, J) ⥤ E`, with the `J`-continuous flat
functors `C ⥤ E`: a left exact left adjoint `F` gives `yoneda ⋙ presheafToSheaf J _ ⋙ F`, and
conversely a flat continuous functor extends along the Yoneda embedding and then through
sheafification. This file proves the parts of this correspondence that are needed to compare
the topologies `J₁ ≥ J` on `C` (roadmap 2.5, `LeanPool.ClassifyingTopoi.Quotients`).

## Main results

* `LeanPool.ClassifyingTopoi.nonempty_iso_of_yoneda_comp_iso` (uniqueness): two left adjoints
  out of `Sh(C, J)` with isomorphic restrictions along the sheafified Yoneda embedding are
  isomorphic. Both composites with `presheafToSheaf J _` are left Kan extensions along the
  Yoneda embedding (they preserve colimits), hence isomorphic, and precomposition with the
  localisation `presheafToSheaf J _` is fully faithful;
* `LeanPool.ClassifyingTopoi.isSheaf_rightAdjoint_iff`: for `J ≤ J₁`, the right adjoint of a
  functor `F` out of `Sh(C, J)` takes values in `J₁`-sheaves iff `F` inverts the
  sheafified inclusions `a(S) ⟶ a(yoneda X)` of the `J₁`-covering sieves (`F` is
  `J₁`-continuous);
* `LeanPool.ClassifyingTopoi.exists_iso_sheafify_comp_iff` (localisation half): for `J ≤ J₁`, a
  left exact left adjoint `F` out of `Sh(C, J)` factors through the sheafification
  `Sh(C, J) ⥤ Sh(C, J₁)` by a left exact left adjoint iff it is `J₁`-continuous in the sense
  above; the factorisation is the restriction of `F` to `J₁`-sheaves
  (`exists_iso_sheafify_comp`);
* `LeanPool.ClassifyingTopoi.bijective_whiskerLeft_sheafify`: natural transformations between
  functors out of `Sh(C, J₁)` are those between their composites with the sheafification
  `Sh(C, J) ⥤ Sh(C, J₁)`, which is a localisation.

## Not formalised

The existence half of Diaconescu's theorem in general (a flat `J`-continuous functor
`C ⥤ Sh(D, K)` extends to a left exact left adjoint `Sh(C, J) ⥤ Sh(D, K)`) is not formalised: it
needs the internal notion of flatness in a sheaf topos (filtering functors), which Mathlib does
not have. For the Horn sites it is proved in `Syntactic/Extension.lean` through points
(`GrothendieckTopology.Point`), which is all the classifying sites need.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits LeanPool.ToposTheoreticBridges

namespace LeanPool.ClassifyingTopoi

section Orthogonal

variable {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]

/-- A morphism to which every object is orthogonal is an isomorphism. -/
theorem isIso_of_forall_isOrthogonal {A B : 𝒞} (m : A ⟶ B) (h : ∀ X, IsOrthogonal m X) :
    IsIso m := by
  obtain ⟨g, hg, -⟩ := h A (𝟙 A)
  obtain ⟨k, -, hk⟩ := h B m
  refine ⟨g, hg, ?_⟩
  rw [hk (g ≫ m) (show m ≫ g ≫ m = m by rw [reassoc_of% hg]),
    hk (𝟙 B) (Category.comp_id m)]

/-- A pullback-preserving left adjoint `F ⊣ G` inverting a monomorphism `m` makes `m` dense for
the image of `G`: every pullback of `m` is orthogonal to the objects `G.obj Y`. -/
theorem isDenseFor_of_isIso_map_of_adjunction {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G)
    [PreservesLimitsOfShape WalkingCospan F] {A B : 𝒞} (m : A ⟶ B) [Mono m]
    [IsIso (F.map m)] : IsDenseFor (fun X => ∃ Y, X = G.obj Y) m := by
  refine ⟨inferInstance, fun T A' t n a hp H ⟨Y, hY⟩ => ?_⟩
  subst hY
  have := (F.map_isPullback hp).isIso_fst_of_isIso
  exact (isOrthogonal_map_iff_of_adjunction adj n Y).1 (Subtopos.isOrthogonal_of_isIso _ _)

end Orthogonal

section Factorisation

variable {C : Type u} [SmallCategory C] {J J₁ : GrothendieckTopology C}
  {E : Type*} [Category E]

/-- A left exact left adjoint `F : Sh(C, J) ⥤ E` whose right adjoint takes values in
`J₁`-sheaves, for `J ≤ J₁`, factors through the sheafification `Sh(C, J) ⥤ Sh(C, J₁)`, by a
left exact left adjoint `Sh(C, J₁) ⥤ E` (its restriction to `J₁`-sheaves). -/
theorem exists_iso_sheafify_comp (h : J ≤ J₁) (F : Sheaf J (Type u) ⥤ E) [F.IsLeftAdjoint]
    [PreservesFiniteLimits F]
    (hF : ∀ Y, Presheaf.IsSheaf J₁ (F.rightAdjoint.obj Y).obj) :
    ∃ (F' : Sheaf J₁ (Type u) ⥤ E) (_ : PreservesFiniteLimits F'), F'.IsLeftAdjoint ∧
      Nonempty (F ≅ (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u)) ⋙ F') := by
  let G' : E ⥤ Sheaf J₁ (Type u) :=
    ObjectProperty.lift _ (F.rightAdjoint ⋙ sheafToPresheaf J (Type u)) hF
  let adj : sheafInclusion h ⋙ F ⊣ G' :=
    (Adjunction.ofIsLeftAdjoint F).restrictFullyFaithful (iC := sheafInclusion h)
      (iD := 𝟭 E) (ObjectProperty.fullyFaithfulιOfLE _) (Functor.FullyFaithful.id _)
      (Functor.rightUnitor _).symm (NatIso.ofComponents fun _ => Iso.refl _)
  have : PreservesFiniteLimits (sheafInclusion h) :=
    have := (sheafifyAdjunction h).rightAdjoint_preservesLimits
    inferInstance
  refine ⟨sheafInclusion h ⋙ F, inferInstance, adj.isLeftAdjoint, ⟨?_⟩⟩
  have adj₂ : (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u)) ⋙
      (sheafInclusion h ⋙ F) ⊣ F.rightAdjoint :=
    ((sheafifyAdjunction h).comp adj).ofNatIsoRight (NatIso.ofComponents fun _ => Iso.refl _)
  exact (Adjunction.ofIsLeftAdjoint F).leftAdjointUniq adj₂

end Factorisation

section Definable

variable {𝒞 : Type*} [Category 𝒞]

/-- Orthogonality to a morphism is invariant under isomorphism of arrows. -/
theorem isOrthogonal_of_arrow_iso {A B A' B' : 𝒞} {f : A ⟶ B} {g : A' ⟶ B'}
    (e : Arrow.mk f ≅ Arrow.mk g) {X : 𝒞} (h : IsOrthogonal f X) : IsOrthogonal g X := by
  have w : f ≫ e.hom.right = e.hom.left ≫ g := (Arrow.w e.hom).symm
  have w' : g ≫ e.inv.right = e.inv.left ≫ f := (Arrow.w e.inv).symm
  intro k
  obtain ⟨l, hl, hu⟩ := h (e.hom.left ≫ k)
  refine ⟨e.inv.right ≫ l, ?_, fun l' hl' => ?_⟩
  · dsimp only
    rw [reassoc_of% w', hl]
    simp
  · rw [← hu (e.hom.right ≫ l') (by dsimp only; rw [reassoc_of% w, hl'])]
    simp

variable {C : Type u} [SmallCategory C] {J J₁ : GrothendieckTopology C}

/-- For `J ≤ J₁` and a `J₁`-covering sieve `S`, the `J₁`-sheaves are orthogonal to the
`J`-sheafification of the inclusion of `S` in the representable presheaf. -/
theorem isOrthogonal_sheafify_functorInclusion (h : J ≤ J₁) {X : C} {S : Sieve X}
    (hS : S ∈ J₁ X) (Y : Sheaf J₁ (Type u)) :
    IsOrthogonal ((presheafToSheaf J (Type u)).map S.functorInclusion)
      ((sheafInclusion h).obj Y) := by
  rw [isOrthogonal_map_iff_of_adjunction (sheafificationAdjunction J (Type u))]
  exact Presieve.isSheafFor_iff_yonedaSheafCondition.1
    ((isSheaf_iff_isSheaf_of_type _ _).1 Y.property S hS)

end Definable

section Localisation

variable {C : Type u} [SmallCategory C] {J J₁ : GrothendieckTopology C} {E : Type*} [Category E]

/-- For `J ≤ J₁` and a `J₁`-covering sieve `S`, sheafification `Sh(C, J) ⥤ Sh(C, J₁)` inverts
the `J`-sheafification of the inclusion of `S` in the representable presheaf. -/
theorem isIso_sheafify_map_functorInclusion (h : J ≤ J₁) {X : C} {S : Sieve X}
    (hS : S ∈ J₁ X) :
    IsIso ((sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u)).map
      ((presheafToSheaf J (Type u)).map S.functorInclusion)) :=
  isIso_of_forall_isOrthogonal _ fun Y => by
    rw [isOrthogonal_map_iff_of_adjunction (sheafifyAdjunction h)]
    exact isOrthogonal_sheafify_functorInclusion h hS Y

/-- For `J ≤ J₁`, the right adjoint of a functor `F` out of `Sh(C, J)` takes values in
`J₁`-sheaves iff `F` inverts the `J`-sheafified inclusions of the `J₁`-covering sieves: `F`
is "`J₁`-continuous". -/
theorem isSheaf_rightAdjoint_iff (h : J ≤ J₁) (F : Sheaf J (Type u) ⥤ E) [F.IsLeftAdjoint] :
    (∀ Y, Presheaf.IsSheaf J₁ (F.rightAdjoint.obj Y).obj) ↔
      ∀ (X : C) (S : Sieve X), S ∈ J₁ X →
        IsIso (F.map ((presheafToSheaf J (Type u)).map S.functorInclusion)) := by
  have adj := Adjunction.ofIsLeftAdjoint F
  constructor
  · intro hF X S hS
    refine isIso_of_forall_isOrthogonal _ fun Y => ?_
    rw [isOrthogonal_map_iff_of_adjunction adj]
    exact isOrthogonal_sheafify_functorInclusion h hS ⟨_, hF Y⟩
  · intro hF Y
    rw [isSheaf_iff_isSheaf_of_type]
    intro X S hS
    have := hF X S hS
    have h₁ := (isOrthogonal_map_iff_of_adjunction adj
      ((presheafToSheaf J (Type u)).map S.functorInclusion) Y).1
      (Subtopos.isOrthogonal_of_isIso _ _)
    rw [isOrthogonal_map_iff_of_adjunction (sheafificationAdjunction J (Type u))] at h₁
    exact Presieve.isSheafFor_iff_yonedaSheafCondition.2 h₁

/-- **Localisation half of Diaconescu's theorem.** For `J ≤ J₁`, a left exact left adjoint
`F` out of `Sh(C, J)` factors, up to isomorphism, through the sheafification
`Sh(C, J) ⥤ Sh(C, J₁)` by a left exact left adjoint iff it inverts the `J`-sheafified
inclusions of the `J₁`-covering sieves. -/
theorem exists_iso_sheafify_comp_iff (h : J ≤ J₁) (F : Sheaf J (Type u) ⥤ E) [F.IsLeftAdjoint]
    [PreservesFiniteLimits F] :
    (∃ (F' : Sheaf J₁ (Type u) ⥤ E) (_ : PreservesFiniteLimits F'), F'.IsLeftAdjoint ∧
      Nonempty (F ≅ (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u)) ⋙ F')) ↔
      ∀ (X : C) (S : Sieve X), S ∈ J₁ X →
        IsIso (F.map ((presheafToSheaf J (Type u)).map S.functorInclusion)) := by
  refine ⟨fun ⟨F', _, _, ⟨e⟩⟩ X S hS => ?_,
    fun hF => exists_iso_sheafify_comp h F ((isSheaf_rightAdjoint_iff h F).2 hF)⟩
  have := isIso_sheafify_map_functorInclusion h hS
  rw [NatIso.isIso_map_iff e]
  exact (inferInstance : IsIso (F'.map ((sheafToPresheaf J (Type u) ⋙
    presheafToSheaf J₁ (Type u)).map ((presheafToSheaf J (Type u)).map S.functorInclusion))))

end Localisation


section Whiskering

variable {C : Type u} [SmallCategory C] {J J₁ : GrothendieckTopology C} {E : Type*} [Category E]

/-- For `J ≤ J₁`, precomposition with the sheafification `Sh(C, J) ⥤ Sh(C, J₁)` is a bijection
on natural transformations between functors out of `Sh(C, J₁)`: the sheafification is a
localisation. -/
theorem bijective_whiskerLeft_sheafify (h : J ≤ J₁) (F G : Sheaf J₁ (Type u) ⥤ E) :
    Function.Bijective (fun α : F ⟶ G =>
      Functor.whiskerLeft (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u)) α) := by
  have := (sheafifyAdjunction h).isLocalization
  let W := (MorphismProperty.isomorphisms (Sheaf J₁ (Type u))).inverseImage
    (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u))
  have := Localization.full_whiskeringLeft
    (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u)) W E
  have := Localization.faithful_whiskeringLeft
    (sheafToPresheaf J (Type u) ⋙ presheafToSheaf J₁ (Type u)) W E
  exact ⟨fun _ _ hαβ => ((Functor.whiskeringLeft _ _ _).obj _).map_injective hαβ,
    fun β => ⟨_, ((Functor.whiskeringLeft _ _ _).obj _).map_preimage β⟩⟩

end Whiskering

section Uniqueness

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- **Uniqueness half of Diaconescu's theorem.** Two left adjoints out of `Sh(C, J)` whose
restrictions `C ⥤ D` along the sheafified Yoneda embedding are isomorphic are isomorphic. -/
theorem nonempty_iso_of_yoneda_comp_iso {D : Type*} [Category.{u} D]
    [HasColimitsOfSize.{u, u} D] (F G : Sheaf J (Type u) ⥤ D) [F.IsLeftAdjoint]
    [G.IsLeftAdjoint]
    (e : yoneda ⋙ presheafToSheaf J (Type u) ⋙ F ≅ yoneda ⋙ presheafToSheaf J (Type u) ⋙ G) :
    Nonempty (F ≅ G) := by
  let a := presheafToSheaf J (Type u)
  let e' : shrinkYoneda.{u} ⋙ a ⋙ F ≅ shrinkYoneda.{u} ⋙ a ⋙ G :=
    Functor.isoWhiskerRight shrinkYonedaIsoYoneda _ ≪≫ e ≪≫
      Functor.isoWhiskerRight shrinkYonedaIsoYoneda.symm _
  have := Presheaf.isLeftKanExtension_along_shrinkYoneda_of_preservesColimits (L := a ⋙ F) e'
  have := Presheaf.isLeftKanExtension_along_shrinkYoneda_of_preservesColimits (L := a ⋙ G)
    (Iso.refl _)
  have := Localization.full_whiskeringLeft a J.W D
  have := Localization.faithful_whiskeringLeft a J.W D
  have i : a ⋙ F ≅ a ⋙ G := Functor.leftKanExtensionUnique _ e'.inv _ (Iso.refl _).inv
  exact ⟨((Functor.whiskeringLeft _ _ _).obj a).preimageIso i⟩

end Uniqueness

end LeanPool.ClassifyingTopoi
