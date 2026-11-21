/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Closed
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Localization.Bousfield
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.Order.Hom.Basic

/-!
# Topologies finer than a given one, and equivalences of sheaf topoi

Let `(C, J)` and `(D, K)` be small sites and `e : Sheaf J (Type u) ≌ Sheaf K (Type u)`.
We prove `exists_orderIso_ici_of_sheafEquiv`: there is an order isomorphism
`φ : Set.Ici J ≃o Set.Ici K` such that a `J`-sheaf `F` is a sheaf for `J' ≥ J` iff
`e.functor.obj F` is a sheaf for `φ J'`. This is the correspondence between topologies finer
than `J` and (some) subtopoi of `Sh(J)` (SGA 4 IV 9.1, Johnstone's Elephant A4.5 and C2.3),
transported along `e`.

## Method

* Comparison lemmas (from Mathlib's sheaf of closed sieves, `Sites/Closed.lean`): for
  `J ≤ J₁, J₂`, `J₁ ≤ J₂` iff every `J₂`-sheaf among the `J`-sheaves is a `J₁`-sheaf
  (`le_iff_forall_isSheaf`), and `J₁ = J₂` iff they have the same sheaves among the `J`-sheaves
  (`eq_iff_forall_isSheaf`).
* An intrinsic, equivalence-invariant description of `J'`-sheaves among `J`-sheaves. Given a
  class `P` of objects of a category, a morphism is *dense for `P`* (`IsDenseFor`) when it is a
  monomorphism all of whose pullbacks are orthogonal to the objects of `P`, and an object is
  *local for `P`* (`IsLocalFor`) when it is orthogonal to all morphisms dense for `P`. For a
  class `P` of `J`-sheaves, a `J`-sheaf is local for `P` iff it is a sheaf for the finest
  topology `topologyOfSheaves J P` making the sheaves of `P` sheaves (`isLocalFor_iff_isSheaf`).
  The proof uses that sheafification preserves pullbacks and is locally surjective, and a local
  extension lemma for presheaves (`isOrthogonal_of_isSheafFor_imageSieve`). With
  `P` the class of `J'`-sheaves, `topologyOfSheaves J P = J'`, so a `J`-sheaf is a `J'`-sheaf
  iff it is local for `P` (`isSheaf_iff_isLocalFor`).
* Locality is transported along equivalences (`isLocalFor_functor_obj_iff`). This gives
  `transportTopology e J'` with `isSheaf_iff_isSheaf_transportTopology`, and the order
  isomorphism is assembled from `transportTopology e` and `transportTopology e.symm`, which are
  monotone because `topologyOfSheaves J P` is antitone in `P` (`topologyOfSheaves_anti`).

`IsOrthogonal`, `IsDenseFor` and `IsLocalFor` are stated with unique extensions; they agree with
Mathlib's `ObjectProperty.isLocal`, `MorphismProperty.universally` and
`MorphismProperty.isLocal` (`isOrthogonal_iff_bijective`, `forall_isOrthogonal_iff_isLocal`,
`isDenseFor_iff_universally`, `isLocalFor_iff_isLocal`).

Subtopoi and their correspondence with finer topologies are formalised in
`LeanPool.ToposTheoreticBridges.Subtopos`. Lawvere–Tierney topologies are not formalised.
-/

@[expose] public section

open CategoryTheory Limits

universe w u

namespace LeanPool.ToposTheoreticBridges

section General

variable {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]

/-- `X` is *right orthogonal* to `m : A ⟶ B` (or `m`-local): every morphism `A ⟶ X` extends
uniquely along `m`. Equivalently, precomposition with `m` is a bijection
`(B ⟶ X) → (A ⟶ X)` (`isOrthogonal_iff_bijective`), which is the condition used by Mathlib's
`ObjectProperty.isLocal` and `MorphismProperty.isLocal` (`forall_isOrthogonal_iff_isLocal`). -/
def IsOrthogonal {A B : 𝒞} (m : A ⟶ B) (X : 𝒞) : Prop :=
  ∀ f : A ⟶ X, ∃! g : B ⟶ X, m ≫ g = f

/-- Orthogonality is bijectivity of precomposition with `m`. -/
theorem isOrthogonal_iff_bijective {A B : 𝒞} (m : A ⟶ B) (X : 𝒞) :
    IsOrthogonal m X ↔ Function.Bijective (fun g : B ⟶ X => m ≫ g) :=
  (Function.bijective_iff_existsUnique _).symm

/-- A morphism is orthogonal to every object of `P` iff it is `P`-local in the sense of
Mathlib's `ObjectProperty.isLocal`. -/
theorem forall_isOrthogonal_iff_isLocal (P : ObjectProperty 𝒞) {A B : 𝒞} (m : A ⟶ B) :
    (∀ X, P X → IsOrthogonal m X) ↔ P.isLocal m := by
  simp only [isOrthogonal_iff_bijective]
  rfl

/-- Orthogonality is reflected and preserved by a fully faithful functor. -/
theorem isOrthogonal_map_iff {F : 𝒞 ⥤ 𝒟} (hF : F.FullyFaithful) {A B : 𝒞} (m : A ⟶ B)
    (X : 𝒞) : IsOrthogonal (F.map m) (F.obj X) ↔ IsOrthogonal m X := by
  constructor
  · intro h f
    obtain ⟨g, hg, hu⟩ := h (F.map f)
    refine ⟨hF.preimage g, hF.map_injective (by simp [hg]), fun g' hg' => hF.map_injective ?_⟩
    simp only [Functor.FullyFaithful.map_preimage]
    exact hu _ (by dsimp only at hg' ⊢; rw [← F.map_comp, hg'])
  · intro h f
    obtain ⟨g, hg, hu⟩ := h (hF.preimage f)
    refine ⟨F.map g, by dsimp only; rw [← F.map_comp, hg]; simp, fun g' hg' => ?_⟩
    rw [← hF.map_preimage g', hu (hF.preimage g') (hF.map_injective (by simp [hg']))]

/-- Orthogonality to `m` is invariant under isomorphism of the target object. -/
theorem IsOrthogonal.of_iso {A B : 𝒞} {m : A ⟶ B} {X Y : 𝒞} (h : IsOrthogonal m X)
    (i : X ≅ Y) : IsOrthogonal m Y := by
  intro f
  obtain ⟨g, hg, hu⟩ := h (f ≫ i.inv)
  refine ⟨g ≫ i.hom, by simp [reassoc_of% hg], fun g' hg' => ?_⟩
  rw [← hu (g' ≫ i.inv) (by simp [reassoc_of% hg'])]
  simp

/-- For an adjunction `L ⊣ R`, `Y` is orthogonal to `L.map m` iff `R.obj Y` is orthogonal
to `m`. -/
theorem isOrthogonal_map_iff_of_adjunction {L : 𝒞 ⥤ 𝒟} {R : 𝒟 ⥤ 𝒞} (adj : L ⊣ R)
    {A B : 𝒞} (m : A ⟶ B) (Y : 𝒟) :
    IsOrthogonal (L.map m) Y ↔ IsOrthogonal m (R.obj Y) := by
  constructor
  · intro h f
    obtain ⟨g, hg, hu⟩ := h ((adj.homEquiv _ _).symm f)
    refine ⟨adj.homEquiv _ _ g, ?_, fun g' hg' => ?_⟩ <;> dsimp only at *
    · rw [← adj.homEquiv_naturality_left, hg, Equiv.apply_symm_apply]
    · rw [← hu ((adj.homEquiv _ _).symm g') ?_, Equiv.apply_symm_apply]
      rw [← adj.homEquiv_naturality_left_symm, hg']
  · intro h f
    obtain ⟨g, hg, hu⟩ := h (adj.homEquiv _ _ f)
    refine ⟨(adj.homEquiv _ _).symm g, ?_, fun g' hg' => ?_⟩ <;> dsimp only at *
    · rw [← adj.homEquiv_naturality_left_symm, hg, Equiv.symm_apply_apply]
    · rw [← hu (adj.homEquiv _ _ g') ?_, Equiv.symm_apply_apply]
      rw [← adj.homEquiv_naturality_left, hg']

/-- A morphism `m : A ⟶ B` is *dense for* a class `P` of objects when it is a monomorphism and
every pullback of `m` (along any morphism `t : T ⟶ B`) is orthogonal to every object of `P`.
In Mathlib's terms, `m` is a monomorphism which is universally `P`-local
(`(ObjectProperty.isLocal P).universally`, see `isDenseFor_iff_universally`); the definition
spells this out with `IsOrthogonal`. This notion only uses the category structure, hence is
invariant under equivalences. -/
def IsDenseFor (P : 𝒞 → Prop) {A B : 𝒞} (m : A ⟶ B) : Prop :=
  Mono m ∧ ∀ ⦃T A' : 𝒞⦄ (t : T ⟶ B) (n : A' ⟶ T) (a : A' ⟶ A), IsPullback n a t m →
    ∀ H, P H → IsOrthogonal n H

/-- An object `X` is *local for* a class `P` when it is orthogonal to every morphism which is
dense for `P` (`IsDenseFor`). In Mathlib's terms, `X` is local for the class of morphisms dense
for `P` (`MorphismProperty.isLocal`, see `isLocalFor_iff_isLocal`). -/
def IsLocalFor (P : 𝒞 → Prop) (X : 𝒞) : Prop :=
  ∀ ⦃A B : 𝒞⦄ (m : A ⟶ B), IsDenseFor P m → IsOrthogonal m X

/-- Density for `P` is being a monomorphism which is universally `P`-local, in the sense of
Mathlib's `ObjectProperty.isLocal` and `MorphismProperty.universally`. -/
theorem isDenseFor_iff_universally (P : ObjectProperty 𝒞) {A B : 𝒞} (m : A ⟶ B) :
    IsDenseFor P m ↔ Mono m ∧ P.isLocal.universally m := by
  refine and_congr Iff.rfl ⟨fun h _ _ i₁ i₂ f' hp => ?_, fun h _ _ t n a hp => ?_⟩
  · exact (forall_isOrthogonal_iff_isLocal P f').1 (h i₂ f' i₁ hp)
  · exact (forall_isOrthogonal_iff_isLocal P n).2 (h a t n hp)

/-- Locality for `P` is locality, in the sense of Mathlib's `MorphismProperty.isLocal`, with
respect to the class of morphisms dense for `P`. -/
theorem isLocalFor_iff_isLocal (P : ObjectProperty 𝒞) (X : 𝒞) :
    IsLocalFor P X ↔ MorphismProperty.isLocal (fun _ _ m => IsDenseFor P m) X := by
  simp only [IsLocalFor, isOrthogonal_iff_bijective]
  rfl

/-- Being dense for `P` is antitone in the class `P`. -/
theorem IsDenseFor.mono_class {P P' : 𝒞 → Prop} (hPP' : ∀ H, P' H → P H) {A B : 𝒞}
    {m : A ⟶ B} (h : IsDenseFor P m) : IsDenseFor P' m :=
  ⟨h.1, fun _ _ t n a hp H hH => h.2 t n a hp H (hPP' H hH)⟩

/-- An equivalence `e` sends a morphism dense for `P` to a morphism dense for the class of objects
whose image under `e.inverse` lies in `P`. -/
theorem IsDenseFor.map (e : 𝒞 ≌ 𝒟) {P : 𝒞 → Prop} {A B : 𝒞} {m : A ⟶ B}
    (h : IsDenseFor P m) : IsDenseFor (fun Y => P (e.inverse.obj Y)) (e.functor.map m) := by
  have := h.1
  refine ⟨inferInstance, fun T A' t n a hp H hH => ?_⟩
  rw [← isOrthogonal_map_iff e.fullyFaithfulInverse]
  refine h.2 (e.inverse.map t ≫ (e.unitIso.app B).inv) _
    (e.inverse.map a ≫ (e.unitIso.app A).inv) ?_ _ hH
  exact (e.inverse.map_isPullback hp).of_iso (Iso.refl _) (Iso.refl _)
    (e.unitIso.app A).symm (e.unitIso.app B).symm (by simp) (by simp) (by simp) (by simp)

/-- Transport of locality along an equivalence `e`, for an isomorphism-closed class `P`. -/
theorem isLocalFor_functor_obj_iff (e : 𝒞 ≌ 𝒟) {P : 𝒞 → Prop}
    (hP : ∀ X Y, (X ≅ Y) → P X → P Y) (X : 𝒞) :
    IsLocalFor (fun Y => P (e.inverse.obj Y)) (e.functor.obj X) ↔ IsLocalFor P X := by
  constructor
  · intro h A B m hm
    exact (isOrthogonal_map_iff e.fullyFaithfulFunctor m X).1 (h _ (hm.map e))
  · intro h A B m hm
    have hm' : IsDenseFor P (e.inverse.map m) :=
      (hm.map e.symm).mono_class fun H hH => hP _ _ (e.unitIso.app H) hH
    exact (isOrthogonal_map_iff e.fullyFaithfulInverse m _).1
      ((h _ hm').of_iso (e.unitIso.app X))

end General


section Presheaf

open Opposite

variable {C : Type*} [Category C]

/-- Local extension lemma: let `m : A ⟶ B` be an objectwise injective morphism of presheaves of
types and `G` a presheaf which is a sheaf for every sieve `imageSieve m b` (the arrows along
which the section `b` of `B` comes from `A`). Then every morphism `A ⟶ G` extends uniquely
along `m`. -/
theorem isOrthogonal_of_isSheafFor_imageSieve {A B G : Cᵒᵖ ⥤ Type w} (m : A ⟶ B)
    (hm : ∀ c, Function.Injective (m.app c))
    (hG : ∀ (d : C) (b : B.obj (op d)),
      Presieve.IsSheafFor G (Presheaf.imageSieve m b).arrows) :
    IsOrthogonal m G := by
  intro f
  have key : ∀ (d : Cᵒᵖ) (b : B.obj d), ∃! y : G.obj d, ∀ ⦃c : C⦄ (g : c ⟶ d.unop)
      (a : A.obj (op c)), m.app _ a = B.map g.op b → G.map g.op y = f.app _ a := by
    intro d b
    have hS := hG d.unop b
    let x : Presieve.FamilyOfElements G (Presheaf.imageSieve m b).arrows :=
      fun c g hg => f.app _ hg.choose
    have hx : x.Compatible := by
      intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
      simp only [x]
      rw [← NatTrans.naturality_apply f, ← NatTrans.naturality_apply f]
      congr 1
      apply hm
      rw [NatTrans.naturality_apply m, NatTrans.naturality_apply m, h₁.choose_spec,
        h₂.choose_spec, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, w]
    refine ⟨hS.amalgamate x hx, fun c g a ha => ?_, fun y hy => ?_⟩
    · have hg : Presheaf.imageSieve m b g := ⟨a, ha⟩
      rw [hS.valid_glue hx g hg]
      simp only [x]
      congr 1
      apply hm
      rw [hg.choose_spec, ha]
    · apply hS.isSeparatedFor.ext
      intro c g hg
      rw [hS.valid_glue hx g hg, hy g _ hg.choose_spec]
  choose y hy hyu using key
  have nat : ∀ (d d' : Cᵒᵖ) (h : d ⟶ d') (b : B.obj d), G.map h (y d b) = y d' (B.map h b) := by
    intro d d' h b
    apply hyu
    intro c g a ha
    rw [← ConcreteCategory.comp_apply, ← G.map_comp]
    have := hy d b (g ≫ h.unop) a (by
      rw [ha, op_comp, Quiver.Hom.op_unop, B.map_comp, ConcreteCategory.comp_apply])
    rwa [op_comp, Quiver.Hom.op_unop] at this
  let g : B ⟶ G :=
    { app := fun d => ↾(y d)
      naturality := fun d d' h => by ext b; exact (nat d d' h b).symm }
  refine ⟨g, ?_, fun g' hg' => ?_⟩
  · ext d a
    refine (hyu d (m.app d a) (f.app d a) fun c g a' ha' => ?_).symm
    rw [← NatTrans.naturality_apply m] at ha'
    rw [hm _ ha', NatTrans.naturality_apply f]
  · ext d b
    refine hyu d b _ fun c g a ha => ?_
    change G.map g.op (g'.app d b) = f.app (op c) a
    rw [← NatTrans.naturality_apply g', ← ha, ← hg']
    rfl

end Presheaf


section Site

open Opposite


variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- The finest Grothendieck topology for which every sheaf of a class `P` of `J`-sheaves is a
sheaf. -/
def topologyOfSheaves (P : Sheaf J (Type u) → Prop) : GrothendieckTopology C :=
  Sheaf.finestTopology {Q | ∃ F, P F ∧ F.obj = Q}

variable {J} in
/-- The topology `topologyOfSheaves J P` is finer than `J`. -/
theorem le_topologyOfSheaves (P : Sheaf J (Type u) → Prop) : J ≤ topologyOfSheaves J P :=
  Sheaf.le_finestTopology _ _ (by
    rintro _ ⟨F, -, rfl⟩
    exact (isSheaf_iff_isSheaf_of_type _ _).1 F.property)

variable {J} in
/-- Every sheaf of `P` is a sheaf for `topologyOfSheaves J P`. -/
theorem isSheaf_topologyOfSheaves {P : Sheaf J (Type u) → Prop} {F : Sheaf J (Type u)}
    (hF : P F) : Presieve.IsSheaf (topologyOfSheaves J P) F.obj :=
  Sheaf.sheaf_for_finestTopology _ ⟨F, hF, rfl⟩

variable {J} in
/-- `topologyOfSheaves J P` is antitone in the class `P`: fewer sheaves, finer topology. -/
theorem topologyOfSheaves_anti {P P' : Sheaf J (Type u) → Prop} (h : ∀ F, P' F → P F) :
    topologyOfSheaves J P ≤ topologyOfSheaves J P' :=
  Sheaf.le_finestTopology _ _ (by
    rintro _ ⟨F, hF, rfl⟩
    exact isSheaf_topologyOfSheaves (h F hF))

variable {J} in
/-- If `S` is a covering sieve for `topologyOfSheaves J P`, the sheafification of the inclusion
`S ⟶ yoneda.obj X` is dense for `P`: pullbacks of it are orthogonal to the sheaves of `P`. -/
theorem isDenseFor_sheafify_functorInclusion {P : Sheaf J (Type u) → Prop} {X : C}
    {S : Sieve X} (hS : S ∈ topologyOfSheaves J P X) :
    IsDenseFor P ((presheafToSheaf J (Type u)).map S.functorInclusion) := by
  refine ⟨inferInstance, fun T A' t n a hp H hH => ?_⟩
  rw [← isOrthogonal_map_iff (fullyFaithfulSheafToPresheaf J (Type u))]
  have hp' : ∀ c : Cᵒᵖ, IsPullback (n.hom.app c) (a.hom.app c) (t.hom.app c)
      (((presheafToSheaf J _).map S.functorInclusion).hom.app c) :=
    fun c => ((hp.map (sheafToPresheaf J _)).map ((evaluation _ _).obj c))
  have : Mono n := hp.mono_fst_of_mono
  apply isOrthogonal_of_isSheafFor_imageSieve
  · intro c
    rw [← mono_iff_injective]
    infer_instance
  · intro d τ
    apply isSheaf_topologyOfSheaves hH
    refine (topologyOfSheaves J P).transitive (le_topologyOfSheaves P _
      (Presheaf.imageSieve_mem J (toSheafify J (yoneda.obj X)) (t.hom.app _ τ))) _ ?_
    rintro Y r ⟨h₀, hh₀⟩
    refine (topologyOfSheaves J P).superset_covering ?_
      ((topologyOfSheaves J P).pullback_stable h₀ hS)
    intro Z g hg
    have key : t.hom.app (op Z) (T.obj.map (g ≫ r).op τ) =
        ((presheafToSheaf J _).map S.functorInclusion).hom.app (op Z)
          ((toSheafify J S.functor).app _ ⟨g ≫ h₀, hg⟩) := by
      rw [NatTrans.naturality_apply t.hom, op_comp, Functor.map_comp,
        ConcreteCategory.comp_apply, ← hh₀, ← NatTrans.naturality_apply (toSheafify J _)]
      have := congr_arg (fun φ => φ.app (op Z) ⟨g ≫ h₀, hg⟩)
        (toSheafify_naturality J S.functorInclusion)
      exact this
    obtain ⟨x, hx, -⟩ := Types.exists_of_isPullback (hp' (op Z)) _ _ key
    exact ⟨x, hx⟩


variable {J} in
/-- If `m : A ⟶ B` is dense for `P`, every sheaf of `P` is a sheaf for the sieves
`imageSieve m.hom b`. The proof pulls `m` back along the sheafification of
`yonedaEquiv.symm b`. -/
theorem isSheafFor_imageSieve_of_isDenseFor {P : Sheaf J (Type u) → Prop}
    {A B : Sheaf J (Type u)} {m : A ⟶ B} (hm : IsDenseFor P m) {H : Sheaf J (Type u)}
    (hH : P H) {d : C} (b : B.obj.obj (op d)) :
    Presieve.IsSheafFor H.obj (Presheaf.imageSieve m.hom b).arrows := by
  have : Mono m := hm.1
  have hinj : ∀ c, Function.Injective (m.hom.app c) := fun c => by
    rw [← mono_iff_injective]; infer_instance
  set S := Presheaf.imageSieve m.hom b
  let α : S.functor ⟶ A.obj :=
    { app := fun c => ↾fun g => g.2.choose
      naturality := fun c c' h => by
        ext g
        apply hinj
        change m.hom.app c' (S.functor.map h g).2.choose = m.hom.app c' (A.obj.map h g.2.choose)
        rw [(S.functor.map h g).2.choose_spec, NatTrans.naturality_apply m.hom,
          g.2.choose_spec, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl }
  have hα : ∀ c (g : S.functor.obj c), m.hom.app c (α.app c g) = B.obj.map g.1.op b :=
    fun c g => g.2.choose_spec
  have sq : IsPullback S.functorInclusion α (yonedaEquiv.symm b) m.hom := by
    refine IsPullback.of_forall_isPullback_app fun c => ?_
    rw [Types.isPullback_iff]
    refine ⟨?_, fun x y h => Subtype.ext h.1, fun x₂ x₃ h => ⟨⟨x₂, x₃, h.symm⟩, rfl, hinj _ ?_⟩⟩
    · ext g; exact (hα c g).symm
    · exact (hα c _).trans h
  let ε := (sheafificationAdjunction J (Type u)).counit
  have sq' : IsPullback ((presheafToSheaf J _).map S.functorInclusion)
      ((presheafToSheaf J _).map α ≫ ε.app A)
      ((presheafToSheaf J _).map (yonedaEquiv.symm b) ≫ ε.app B) m :=
    ((presheafToSheaf J (Type u)).map_isPullback sq).of_iso (Iso.refl _) (Iso.refl _)
      (asIso (ε.app A)) (asIso (ε.app B)) (by simp) (by simp) (by simp) (ε.naturality m)
  have := hm.2 _ _ _ sq' H hH
  rw [isOrthogonal_map_iff_of_adjunction (sheafificationAdjunction J _)] at this
  exact Presieve.isSheafFor_iff_yonedaSheafCondition.2 this


/-- **Intrinsic description of the sheaves of `topologyOfSheaves J P`.** A `J`-sheaf is local
for `P` (an equivalence-invariant notion of `Sheaf J (Type u)`) iff it is a sheaf for the
finest topology `topologyOfSheaves J P` making the sheaves of `P` sheaves. -/
theorem isLocalFor_iff_isSheaf (P : Sheaf J (Type u) → Prop) (G : Sheaf J (Type u)) :
    IsLocalFor P G ↔ Presheaf.IsSheaf (topologyOfSheaves J P) G.obj := by
  rw [isSheaf_iff_isSheaf_of_type]
  constructor
  · intro h X S hS
    have := h _ (isDenseFor_sheafify_functorInclusion hS)
    rw [isOrthogonal_map_iff_of_adjunction (sheafificationAdjunction J _)] at this
    exact Presieve.isSheafFor_iff_yonedaSheafCondition.2 this
  · intro h A B m hm
    rw [← isOrthogonal_map_iff (fullyFaithfulSheafToPresheaf J (Type u))]
    have : Mono m := hm.1
    apply isOrthogonal_of_isSheafFor_imageSieve
    · intro c
      rw [← mono_iff_injective]
      infer_instance
    · intro d b
      apply h
      apply Sheaf.mem_finestTopology_of_forall_isSheafFor
      rintro _ ⟨H, hH, rfl⟩ Y f
      rw [Presheaf.pullback_imageSieve]
      exact isSheafFor_imageSieve_of_isDenseFor hm hH _

variable {J} in
/-- For a topology `J₂ ≥ J`, `J₁ ≤ J₂` iff every `J`-sheaf which is a `J₂`-sheaf is a
`J₁`-sheaf. -/
theorem le_iff_forall_isSheaf {J₁ J₂ : GrothendieckTopology C} (h₂ : J ≤ J₂) :
    J₁ ≤ J₂ ↔ ∀ F : Sheaf J (Type u), Presheaf.IsSheaf J₂ F.obj → Presheaf.IsSheaf J₁ F.obj := by
  refine ⟨fun h F hF => hF.of_le h, fun h => le_topology_of_closedSieves_isSheaf ?_⟩
  have h₂' : Presheaf.IsSheaf J₂ (Functor.closedSieves J₂).toFunctor :=
    (isSheaf_iff_isSheaf_of_type _ _).2 (classifier_isSheaf J₂)
  exact (isSheaf_iff_isSheaf_of_type _ _).1 (h ⟨_, h₂'.of_le h₂⟩ h₂')

variable {J} in
/-- Two topologies finer than `J` are equal iff they have the same sheaves among the
`J`-sheaves. -/
theorem eq_iff_forall_isSheaf {J₁ J₂ : GrothendieckTopology C} (h₁ : J ≤ J₁) (h₂ : J ≤ J₂) :
    J₁ = J₂ ↔ ∀ F : Sheaf J (Type u), Presheaf.IsSheaf J₁ F.obj ↔ Presheaf.IsSheaf J₂ F.obj := by
  refine ⟨fun h F => h ▸ Iff.rfl, fun h => le_antisymm ?_ ?_⟩
  · exact (le_iff_forall_isSheaf h₂).2 fun F => (h F).2
  · exact (le_iff_forall_isSheaf h₁).2 fun F => (h F).1

variable {J} in
/-- For `J ≤ J'`, the finest topology for which the `J'`-sheaves are sheaves is `J'` itself. -/
theorem topologyOfSheaves_isSheaf {J' : GrothendieckTopology C} (h : J ≤ J') :
    topologyOfSheaves J (fun F => Presheaf.IsSheaf J' F.obj) = J' := by
  apply le_antisymm
  · apply le_topology_of_closedSieves_isSheaf
    have h1 : Presheaf.IsSheaf J' (Functor.closedSieves J').toFunctor :=
      (isSheaf_iff_isSheaf_of_type _ _).2 (classifier_isSheaf J')
    exact isSheaf_topologyOfSheaves (F := ⟨_, h1.of_le h⟩) h1
  · exact Sheaf.le_finestTopology _ _ (by
      rintro _ ⟨F, hF, rfl⟩
      exact (isSheaf_iff_isSheaf_of_type _ _).1 hF)

variable {J} in
/-- **Intrinsic characterisation of `J'`-sheaves inside `Sheaf J (Type u)`.** For `J ≤ J'`, a
`J`-sheaf is a `J'`-sheaf iff it is local for the class of `J'`-sheaves. -/
theorem isSheaf_iff_isLocalFor {J' : GrothendieckTopology C} (h : J ≤ J')
    (F : Sheaf J (Type u)) :
    Presheaf.IsSheaf J' F.obj ↔ IsLocalFor (fun G => Presheaf.IsSheaf J' G.obj) F := by
  rw [isLocalFor_iff_isSheaf, topologyOfSheaves_isSheaf h]

variable {J} in
/-- Being a sheaf for another topology is invariant under isomorphism of `J`-sheaves. -/
theorem isSheaf_obj_iff_of_iso (J' : GrothendieckTopology C) {F G : Sheaf J (Type u)}
    (i : F ≅ G) : Presheaf.IsSheaf J' F.obj ↔ Presheaf.IsSheaf J' G.obj :=
  Presheaf.isSheaf_of_iso_iff ((sheafToPresheaf J _).mapIso i)

variable {D : Type u} [SmallCategory D] {J} {K : GrothendieckTopology D}

/-- The topology on `D` obtained by transporting the topology `J'` on `C` along an equivalence
`e` of sheaf categories: the finest topology for which the sheaves `G` with `e.inverse.obj G`
a `J'`-sheaf are sheaves. -/
def transportTopology (e : Sheaf J (Type u) ≌ Sheaf K (Type u))
    (J' : GrothendieckTopology C) : GrothendieckTopology D :=
  topologyOfSheaves K (fun G => Presheaf.IsSheaf J' (e.inverse.obj G).obj)

/-- The transported topology is finer than `K`. -/
theorem le_transportTopology (e : Sheaf J (Type u) ≌ Sheaf K (Type u))
    (J' : GrothendieckTopology C) : K ≤ transportTopology e J' :=
  le_topologyOfSheaves _

/-- **Transport of the sheaf condition.** For `J ≤ J'`, a `J`-sheaf `F` is a `J'`-sheaf iff
`e.functor.obj F` is a sheaf for `transportTopology e J'`. -/
theorem isSheaf_iff_isSheaf_transportTopology (e : Sheaf J (Type u) ≌ Sheaf K (Type u))
    {J' : GrothendieckTopology C} (h : J ≤ J') (F : Sheaf J (Type u)) :
    Presheaf.IsSheaf J' F.obj ↔
      Presheaf.IsSheaf (transportTopology e J') (e.functor.obj F).obj := by
  rw [transportTopology, ← isLocalFor_iff_isSheaf,
    isLocalFor_functor_obj_iff e (fun X Y i => (isSheaf_obj_iff_of_iso J' i).1),
    isSheaf_iff_isLocalFor h]

/-- Transport of topologies is monotone. -/
theorem transportTopology_mono (e : Sheaf J (Type u) ≌ Sheaf K (Type u))
    {J₁ J₂ : GrothendieckTopology C} (h : J₁ ≤ J₂) :
    transportTopology e J₁ ≤ transportTopology e J₂ :=
  topologyOfSheaves_anti fun _ hG => hG.of_le h

/-- Transporting back along `e.symm` recovers the topology. -/
theorem transportTopology_symm_transportTopology (e : Sheaf J (Type u) ≌ Sheaf K (Type u))
    {J' : GrothendieckTopology C} (h : J ≤ J') :
    transportTopology e.symm (transportTopology e J') = J' := by
  rw [eq_iff_forall_isSheaf (le_transportTopology _ _) h]
  intro F
  rw [isSheaf_iff_isSheaf_transportTopology e h,
    isSheaf_iff_isSheaf_transportTopology e.symm (le_transportTopology e J')]
  exact isSheaf_obj_iff_of_iso _ (e.unitIso.app F)

end Site

/-- An equivalence `e` of the sheaf topoi of two small sites gives an order isomorphism `φ`
between the topologies finer than the two given ones, under which a sheaf `F` is a sheaf for
`J'` exactly when its image under `e` is a sheaf for `φ J'`. -/
theorem exists_orderIso_ici_of_sheafEquiv {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (e : Sheaf J (Type u) ≌ Sheaf K (Type u)) :
    ∃ φ : Set.Ici J ≃o Set.Ici K, ∀ (J' : Set.Ici J) (F : Sheaf J (Type u)),
      Presheaf.IsSheaf J'.1 F.obj ↔ Presheaf.IsSheaf (φ J').1 (e.functor.obj F).obj := by
  let φ : Set.Ici J ≃ Set.Ici K :=
    { toFun := fun J' => ⟨transportTopology e J'.1, le_transportTopology e _⟩
      invFun := fun K' => ⟨transportTopology e.symm K'.1, le_transportTopology e.symm _⟩
      left_inv := fun J' => Subtype.ext (transportTopology_symm_transportTopology e J'.2)
      right_inv := fun K' => Subtype.ext (transportTopology_symm_transportTopology e.symm K'.2) }
  refine ⟨Equiv.toOrderIso φ (fun _ _ h => transportTopology_mono e h)
    (fun _ _ h => transportTopology_mono e.symm h), fun J' F => ?_⟩
  exact isSheaf_iff_isSheaf_transportTopology e J'.2 F

end LeanPool.ToposTheoreticBridges
