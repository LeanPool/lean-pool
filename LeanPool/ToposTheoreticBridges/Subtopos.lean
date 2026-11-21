/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.Sites
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# Subtopoi, and the subtopoi of a sheaf topos

A *subtopos* of a category `E` (`Subtopos E`) is a class of objects `P : ObjectProperty E`,
closed under isomorphisms, whose inclusion `P.ι` has a left adjoint preserving finite limits.
Subtopoi are ordered by inclusion, which is a partial order (roadmap 4.1).

## Main results

* `Subtopos.prop_iff_isLocalFor`: in a category with pullbacks, a subtopos is determined by its
  dense monomorphisms: an object is in `S` iff it is local for `S.prop` (`IsLocalFor`, from
  `Sites.lean`). If `X` is local, the diagonal of the kernel pair of the unit `η : X ⟶ L X` is a
  monomorphism inverted by the (pullback-preserving) reflector `L`, hence dense; orthogonality
  forces the two projections to agree, so `η` is mono. Then `η` is itself dense, so it has a
  retraction, and the universal property of the unit makes `η` an isomorphism.
* `Subtopos.ofFullyFaithful`: the essential image of a fully faithful functor with a left
  exact left adjoint is a subtopos.
* `sheafSubtopos` (roadmap 4.2(a)): the essential image of `sheafToPresheaf J (Type u)` is a
  subtopos of `Cᵒᵖ ⥤ Type u` (`sheafSubtopos_prop_iff`: it consists of the `J`-sheaves).
* `subtoposOfLE`: for `J ≤ J'`, the `J'`-sheaves form a subtopos of `Sheaf J (Type u)`.
* `subtoposOrderIso` (roadmap 4.2(b)): for a small site `(C, J)`, an order isomorphism
  `(Set.Ici J)ᵒᵈ ≃o Subtopos (Sheaf J (Type u))` sending `J'` to the `J'`-sheaves, with inverse
  `S ↦ topologyOfSheaves J S.prop`. Surjectivity combines `Subtopos.prop_iff_isLocalFor` with
  `isLocalFor_iff_isSheaf`. The order dual is needed: a finer topology has fewer sheaves, so
  `J' ↦ (J'-sheaves)` is antitone.

We do not formalise Lawvere–Tierney topologies, nor subtopoi of an arbitrary elementary topos
beyond the definition; `Subtopos` is stated for any category, and no topos structure is assumed.
-/

@[expose] public section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂ u

namespace LeanPool.ToposTheoreticBridges

variable (E : Type u₁) [Category.{v₁} E]

/-- A *subtopos* of a category `E` (thought of as a topos): a class of objects `prop`, closed
under isomorphisms, whose inclusion `prop.ι` has a left adjoint preserving finite limits. -/
@[ext]
structure Subtopos where
  /-- The class of objects of the subtopos. -/
  prop : ObjectProperty E
  /-- The class of objects is closed under isomorphisms. -/
  isClosedUnderIsomorphisms : prop.IsClosedUnderIsomorphisms
  /-- The inclusion has a left adjoint which preserves finite limits. -/
  exists_leftAdjoint : ∃ L : E ⥤ prop.FullSubcategory, Nonempty (L ⊣ prop.ι) ∧
    PreservesFiniteLimits L

namespace Subtopos

variable {E}

/-- Subtopoi are ordered by inclusion of their classes of objects. -/
instance : PartialOrder (Subtopos E) :=
  PartialOrder.lift Subtopos.prop fun _ _ h => Subtopos.ext h

/-- `S ≤ T` iff every object of `S` is an object of `T`. -/
theorem le_iff {S T : Subtopos E} : S ≤ T ↔ ∀ X, S.prop X → T.prop X :=
  Iff.rfl

/-- Every object is orthogonal to an isomorphism. -/
theorem isOrthogonal_of_isIso {A B : E} (m : A ⟶ B) [IsIso m] (X : E) : IsOrthogonal m X :=
  (forall_isOrthogonal_iff_isLocal ⊤ m).2 (ObjectProperty.isLocal_of_isIso _ m) X trivial

section Localisation

variable {P : ObjectProperty E} {L : E ⥤ P.FullSubcategory} (adj : L ⊣ P.ι)
  [PreservesLimitsOfShape WalkingCospan L]

include adj in
/-- For a reflective class `P` with pullback-preserving reflector `L`, a monomorphism inverted
by `L` is dense for `P`: its pullbacks are inverted by `L`, hence `P`-local
(`ObjectProperty.isLocal_iff_isIso_map`). -/
theorem isDenseFor_of_isIso_map {A B : E} (m : A ⟶ B) [Mono m] [IsIso (L.map m)] :
    IsDenseFor P m := by
  refine (isDenseFor_iff_universally P m).2 ⟨inferInstance, fun _ _ _ _ n hp H hH => ?_⟩
  have := (L.map_isPullback hp).isIso_fst_of_isIso
  exact (ObjectProperty.isLocal_iff_isIso_map adj n).2 this H ⟨⟨H, hH⟩, rfl⟩

omit [PreservesLimitsOfShape WalkingCospan L] in
include adj in
/-- The reflector inverts the unit. -/
theorem isIso_map_unit_app (X : E) : IsIso (L.map (adj.unit.app X)) := by
  have h := adj.left_triangle_components X
  have : IsIso (L.map (adj.unit.app X) ≫ adj.counit.app (L.obj X)) := by
    rw [h]; exact IsIso.id _
  exact IsIso.of_isIso_comp_right _ (adj.counit.app (L.obj X))

include adj in
/-- **A reflective subcategory with pullback-preserving reflector is determined by its dense
monomorphisms.** If `P` is closed under isomorphisms and reflective, with reflector preserving
pullbacks, then an object is in `P` iff it is local for `P` (orthogonal to the monomorphisms
dense for `P`). -/
theorem prop_iff_isLocalFor_of_adjunction [HasPullbacks E] [P.IsClosedUnderIsomorphisms]
    (X : E) : P X ↔ IsLocalFor P X := by
  constructor
  · intro hX A B m hm
    exact hm.2 (𝟙 B) m (𝟙 A) (IsPullback.id_vert m) X hX
  · intro hX
    let η := adj.unit.app X
    have hη := isIso_map_unit_app adj X
    -- the diagonal of the kernel pair of the unit is dense, hence the unit is mono
    have hfst : IsIso (L.map (pullback.fst η η)) :=
      (L.map_isPullback (IsPullback.of_hasPullback η η)).isIso_fst_of_isIso
    have hδ : IsIso (L.map (pullback.diagonal η)) := by
      have : IsIso (L.map (pullback.diagonal η) ≫ L.map (pullback.fst η η)) := by
        rw [← L.map_comp, pullback.diagonal_fst, L.map_id]; infer_instance
      exact IsIso.of_isIso_comp_right _ (L.map (pullback.fst η η))
    obtain ⟨g, -, hg⟩ := hX _ (isDenseFor_of_isIso_map adj (pullback.diagonal η)) (𝟙 X)
    have hfs : pullback.fst η η = pullback.snd η η :=
      (hg _ (pullback.diagonal_fst η)).trans (hg _ (pullback.diagonal_snd η)).symm
    have : Mono η := ⟨fun a b h =>
      calc a = pullback.lift a b h ≫ pullback.fst η η := (pullback.lift_fst _ _ _).symm
        _ = pullback.lift a b h ≫ pullback.snd η η := by rw [hfs]
        _ = b := pullback.lift_snd _ _ _⟩
    -- the unit is dense, so it has a retraction
    obtain ⟨r, hr, -⟩ := hX _ (isDenseFor_of_isIso_map adj η) (𝟙 X)
    have hr' : r ≫ η = 𝟙 _ := by
      have h1 : adj.homEquiv _ _ (P.fullyFaithfulι.preimage (r ≫ η)) =
          adj.homEquiv _ _ (𝟙 _) := by
        rw [adj.homEquiv_unit, adj.homEquiv_unit, Functor.FullyFaithful.map_preimage,
          P.ι.map_id, ← Category.assoc]
        exact (congrArg (· ≫ η) hr).trans (by simp [η])
      have h2 := congrArg P.ι.map ((adj.homEquiv _ _).injective h1)
      rwa [Functor.FullyFaithful.map_preimage, P.ι.map_id] at h2
    let i : X ≅ P.ι.obj (L.obj X) :=
      { hom := η, inv := r, hom_inv_id := hr, inv_hom_id := hr' }
    exact P.prop_of_iso i.symm (L.obj X).property

end Localisation

/-- **A subtopos is determined by its dense monomorphisms.** In a category with pullbacks, an
object belongs to a subtopos `S` iff it is local for `S.prop`, i.e. orthogonal to every
monomorphism dense for `S.prop` (`IsDenseFor`). -/
theorem prop_iff_isLocalFor [HasPullbacks E] (S : Subtopos E) (X : E) :
    S.prop X ↔ IsLocalFor S.prop X := by
  obtain ⟨L, ⟨adj⟩, _⟩ := S.exists_leftAdjoint
  have := S.isClosedUnderIsomorphisms
  exact prop_iff_isLocalFor_of_adjunction adj X

/-- The essential image of a fully faithful functor `i` with a left adjoint preserving finite
limits is a subtopos. -/
noncomputable def ofFullyFaithful {D : Type u₂} [Category.{v₂} D] (i : D ⥤ E) [i.Full]
    [i.Faithful] {L : E ⥤ D} (adj : L ⊣ i) [PreservesFiniteLimits L] : Subtopos E where
  prop := i.essImage
  isClosedUnderIsomorphisms := inferInstance
  exists_leftAdjoint := by
    let e : D ≌ i.EssImageSubcategory := i.toEssImage.asEquivalence
    refine ⟨L ⋙ e.functor, ⟨(adj.comp e.toAdjunction).ofNatIsoRight ?_⟩, inferInstance⟩
    exact Functor.isoWhiskerLeft e.inverse i.toEssImageCompι.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e.counitIso _ ≪≫
      Functor.leftUnitor _

/-- The class of objects of `ofFullyFaithful i adj` is the essential image of `i`. -/
@[simp]
theorem ofFullyFaithful_prop {D : Type u₂} [Category.{v₂} D] (i : D ⥤ E) [i.Full]
    [i.Faithful] {L : E ⥤ D} (adj : L ⊣ i) [PreservesFiniteLimits L] :
    (ofFullyFaithful i adj).prop = i.essImage :=
  rfl

end Subtopos

section Sheaves

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- **The sheaves form a subtopos of the presheaves** (roadmap 4.2(a)): the essential image of
`sheafToPresheaf J (Type u)`, reflected by sheafification. -/
noncomputable def sheafSubtopos : Subtopos (Cᵒᵖ ⥤ Type u) :=
  Subtopos.ofFullyFaithful (sheafToPresheaf J (Type u)) (sheafificationAdjunction J (Type u))

/-- A presheaf belongs to `sheafSubtopos J` iff it is a `J`-sheaf. -/
theorem sheafSubtopos_prop_iff (F : Cᵒᵖ ⥤ Type u) :
    (sheafSubtopos J).prop F ↔ Presheaf.IsSheaf J F := by
  constructor
  · rintro ⟨G, ⟨i⟩⟩
    exact (Presheaf.isSheaf_of_iso_iff i).1 G.property
  · intro h
    exact ⟨⟨F, h⟩, ⟨Iso.refl _⟩⟩

variable {J}

/-- For `J ≤ J'`, the inclusion of `J'`-sheaves into `J`-sheaves. -/
def sheafInclusionOfLE {J' : GrothendieckTopology C} (h : J ≤ J') :
    Sheaf J' (Type u) ⥤ Sheaf J (Type u) :=
  ObjectProperty.lift (Presheaf.IsSheaf J) (sheafToPresheaf J' (Type u)) fun F => F.property.of_le h

/-- The inclusion of `J'`-sheaves into `J`-sheaves is full. -/
instance {J' : GrothendieckTopology C} (h : J ≤ J') : (sheafInclusionOfLE h).Full := by
  dsimp [sheafInclusionOfLE]; infer_instance

/-- The inclusion of `J'`-sheaves into `J`-sheaves is faithful. -/
instance {J' : GrothendieckTopology C} (h : J ≤ J') : (sheafInclusionOfLE h).Faithful := by
  dsimp [sheafInclusionOfLE]; infer_instance

/-- For `J ≤ J'`, the `J'`-sheafification of the underlying presheaf is left adjoint to the
inclusion of `J'`-sheaves into `J`-sheaves. -/
noncomputable def sheafInclusionOfLEAdjunction {J' : GrothendieckTopology C} (h : J ≤ J') :
    sheafToPresheaf J (Type u) ⋙ presheafToSheaf J' (Type u) ⊣ sheafInclusionOfLE h :=
  (sheafificationAdjunction J' (Type u)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf J (Type u)) (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm (Iso.refl _)

/-- For `J ≤ J'`, the `J'`-sheaves form a subtopos of the `J`-sheaves. -/
noncomputable def subtoposOfLE {J' : GrothendieckTopology C} (h : J ≤ J') :
    Subtopos (Sheaf J (Type u)) :=
  Subtopos.ofFullyFaithful (sheafInclusionOfLE h) (sheafInclusionOfLEAdjunction h)

/-- A `J`-sheaf belongs to `subtoposOfLE h` iff it is a `J'`-sheaf. -/
theorem subtoposOfLE_prop_iff {J' : GrothendieckTopology C} (h : J ≤ J')
    (F : Sheaf J (Type u)) : (subtoposOfLE h).prop F ↔ Presheaf.IsSheaf J' F.obj := by
  constructor
  · rintro ⟨G, ⟨i⟩⟩
    exact (isSheaf_obj_iff_of_iso J' i).1 G.property
  · intro hF
    exact ⟨⟨F.obj, hF⟩, ⟨Iso.refl _⟩⟩

/-- The class of objects of `subtoposOfLE h` is the class of `J'`-sheaves. -/
theorem subtoposOfLE_prop {J' : GrothendieckTopology C} (h : J ≤ J') :
    (subtoposOfLE h).prop = fun F => Presheaf.IsSheaf J' F.obj :=
  funext fun F => propext (subtoposOfLE_prop_iff h F)

/-- Every subtopos of `Sheaf J (Type u)` is the subtopos of sheaves for the topology
`topologyOfSheaves J S.prop`. -/
theorem subtoposOfLE_topologyOfSheaves (S : Subtopos (Sheaf J (Type u))) :
    subtoposOfLE (le_topologyOfSheaves S.prop) = S := by
  ext F
  rw [subtoposOfLE_prop_iff, ← isLocalFor_iff_isSheaf, ← S.prop_iff_isLocalFor]

variable (J) in
/-- **Subtopoi of a sheaf topos** (roadmap 4.2(b)). For a small site `(C, J)`, the topologies
finer than `J` correspond, order-reversingly, to the subtopoi of `Sheaf J (Type u)`: `J'`
is sent to the subtopos of `J'`-sheaves (`subtoposOfLE`), and a subtopos `S` to
`topologyOfSheaves J S.prop`. A finer topology has fewer sheaves, whence the order dual. -/
noncomputable def subtoposOrderIso : (Set.Ici J)ᵒᵈ ≃o Subtopos (Sheaf J (Type u)) where
  toFun J' := subtoposOfLE (OrderDual.ofDual J').2
  invFun S := OrderDual.toDual ⟨topologyOfSheaves J S.prop, le_topologyOfSheaves _⟩
  left_inv J' := by
    refine congrArg OrderDual.toDual (Subtype.ext ?_)
    dsimp only
    rw [subtoposOfLE_prop, topologyOfSheaves_isSheaf (OrderDual.ofDual J').2]
    rfl
  right_inv S := by exact subtoposOfLE_topologyOfSheaves S
  map_rel_iff' {J₁ J₂} := by
    change (∀ F, (subtoposOfLE _).prop F → (subtoposOfLE _).prop F) ↔
      (OrderDual.ofDual J₂).1 ≤ (OrderDual.ofDual J₁).1
    rw [le_iff_forall_isSheaf (OrderDual.ofDual J₁).2]
    simp only [subtoposOfLE_prop_iff]

/-- The subtopos attached to `J'` by `subtoposOrderIso` consists of the `J'`-sheaves. -/
theorem subtoposOrderIso_apply_prop_iff (J' : (Set.Ici J)ᵒᵈ) (F : Sheaf J (Type u)) :
    (subtoposOrderIso J J').prop F ↔ Presheaf.IsSheaf (OrderDual.ofDual J').1 F.obj :=
  subtoposOfLE_prop_iff _ F

/-- The topology attached to a subtopos `S` by `subtoposOrderIso` is `topologyOfSheaves J S`. -/
theorem subtoposOrderIso_symm_apply (S : Subtopos (Sheaf J (Type u))) :
    (OrderDual.ofDual ((subtoposOrderIso J).symm S)).1 = topologyOfSheaves J S.prop :=
  rfl

end Sheaves

end LeanPool.ToposTheoreticBridges
