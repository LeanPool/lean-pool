/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.DiaconescuExistence
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Fiber
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Generic
public import Mathlib.CategoryTheory.Functor.KanExtension.RestrictedYoneda
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Extending a presheaf structure along the Yoneda embedding of the Horn category

Let `P` be an `L`-structure in a presheaf topos `Dᵒᵖ ⥤ Type _` on a small category. At each
object `d`, the fiber structure on `P(d)` is a point of the site `(HornCat L, ⊥)`
(`LeanPool.ClassifyingTopoi.Syntactic.HornCat.point`), and the restriction maps of `P` are
homomorphisms, hence morphisms of points. The fiber functors of these points on presheaves
assemble into a functor `HornCat.extension P` from the presheaf topos on `HornCat L` to the
presheaf topos on `D`. It preserves finite limits and colimits, since each fiber functor does
(the categories of elements of the fibers are cofiltered), and its composite with the Yoneda
embedding is the functor of the fibers, `X ↦ (d ↦ {x ∈ P(d)ⁿ | x ⊨ X})`
(`HornCat.yonedaCompExtensionIso`), whose structure is `P` (`HornCat.isomorphic_fibers`).

This is the existence half of Diaconescu's theorem for the Horn site: the presheaf topos on
`HornCat L` classifies `L`-structures. No internal flatness is needed: every fiber functor is
flat in `Type _`.
-/

@[expose] public section

universe u u₁ u₂

namespace LeanPool.ClassifyingTopoi.Syntactic

open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits LeanPool.ClassifyingTopoi
  Opposite

variable {L : Language.{u₁, u₂}}

namespace HornCat

variable {D : Type (max u₁ u₂ u)} [SmallCategory D]
  (P : CatStructure L (Dᵒᵖ ⥤ Type (max u₁ u₂ u)))

/-- The restriction maps of a presheaf structure are homomorphisms of the fiber structures. -/
noncomputable def restrictHom {d d' : Dᵒᵖ} (g : d ⟶ d') :
    @Language.Hom L (P.carrier.obj d) (P.carrier.obj d') (P.fiberStr d) (P.fiberStr d') :=
  @Language.Hom.mk L _ _ (P.fiberStr d) (P.fiberStr d') (P.carrier.map g)
    (fun {k} f x => by
      rw [CatStructure.fiberStr_funMap, CatStructure.fiberStr_funMap, ← NatTrans.naturality_apply]
      congr 1
      rw [Equiv.eq_symm_apply, secEquiv_map, Equiv.apply_symm_apply])
    (fun {k} R x hx => by
      rw [CatStructure.fiberStr_relMap] at hx ⊢
      obtain ⟨y, hy⟩ := hx
      refine ⟨(P.relMap R).left.map g y, ?_⟩
      rw [NatTrans.naturality_apply, hy, Equiv.eq_symm_apply, secEquiv_map,
        Equiv.apply_symm_apply])

/-- The functor of the fibers of a presheaf structure. -/
noncomputable def fibers : Dᵒᵖ ⥤ (HornCat.{u} L ⥤ Type (max u₁ u₂ u)) where
  obj d := @fiber L _ (P.fiberStr d)
  map g := @fiberMap L _ (P.fiberStr _) _ (P.fiberStr _) (restrictHom.{u} P g)
  map_id d := by
    ext X x
    exact Subtype.ext (funext fun i => Functor.map_id_apply P.carrier _ _)
  map_comp g g' := by
    ext X x
    exact Subtype.ext (funext fun i => Functor.map_comp_apply P.carrier g g' _)

/-- The points of the Horn site given by the fibers of a presheaf structure. -/
noncomputable def pointsFunctor :
    Dᵒᵖ ⥤ (GrothendieckTopology.Point.{max u₁ u₂ u}
      (⊥ : GrothendieckTopology (HornCat.{u} L)))ᵒᵖ where
  obj d := op (@point L _ (P.fiberStr d))
  map g := (@pointHom L _ (P.fiberStr _) _ (P.fiberStr _) (restrictHom.{u} P g)).op
  map_id d := by
    apply Quiver.Hom.unop_inj
    ext X x
    exact Subtype.ext (funext fun i => Functor.map_id_apply P.carrier _ _)
  map_comp g g' := by
    apply Quiver.Hom.unop_inj
    ext X x
    exact Subtype.ext (funext fun i => Functor.map_comp_apply P.carrier g g' _)

variable (L) in
/-- The fiber functors on presheaves of the points of the Horn site. -/
noncomputable def presheafFiberFunctor :
    (GrothendieckTopology.Point.{max u₁ u₂ u} (⊥ : GrothendieckTopology (HornCat.{u} L)))ᵒᵖ ⥤
      ((HornCat.{u} L)ᵒᵖ ⥤ Type (max u₁ u₂ u)) ⥤ Type (max u₁ u₂ u) :=
  pointPresheafFiberFunctor (C := HornCat.{u} L) ⊥

/-- The extension of a presheaf structure along the Yoneda embedding of the Horn category:
the presheaf of fibers, at the points given by the fiber structures. -/
noncomputable def extension :
    ((HornCat.{u} L)ᵒᵖ ⥤ Type (max u₁ u₂ u)) ⥤ (Dᵒᵖ ⥤ Type (max u₁ u₂ u)) :=
  pointsExtension (pointsFunctor.{u} P)

/-- Evaluating the extension at an object is the fiber functor of the corresponding point. -/
noncomputable def extensionCompEvaluationIso (d : Dᵒᵖ) :
    extension.{u} P ⋙ (evaluation _ _).obj d ≅ (@point L _ (P.fiberStr d)).presheafFiber :=
  Iso.refl _

instance : PreservesFiniteLimits (extension.{u} P) :=
  inferInstanceAs (PreservesFiniteLimits (pointsExtension _))

instance : PreservesColimitsOfSize.{max u₁ u₂ u, max u₁ u₂ u} (extension.{u} P) :=
  inferInstanceAs (PreservesColimitsOfSize (pointsExtension _))

section PointIso

variable {Φ₁ Φ₂ : GrothendieckTopology.Point.{max u₁ u₂ u}
  (⊥ : GrothendieckTopology (HornCat.{u} L))} (f : Φ₁ ⟶ Φ₂)

/-- The fiber of a representable presheaf at a point is the fiber of the point, through the
Yoneda embedding. -/
noncomputable def yonedaCompPresheafFiberIso
    (Φ : GrothendieckTopology.Point.{max u₁ u₂ u} (⊥ : GrothendieckTopology (HornCat.{u} L))) :
    yoneda ⋙ Φ.presheafFiber ≅ Φ.fiber :=
  yonedaCompPointPresheafFiberIso Φ

/-- The isomorphism `shrinkYonedaCompPresheafFiberIso` is natural in the point. -/
theorem shrinkYonedaCompPresheafFiberIso_naturality (X : HornCat.{u} L) :
    f.presheafFiber.app (shrinkYoneda.obj X) ≫ Φ₁.shrinkYonedaCompPresheafFiberIso.hom.app X =
      Φ₂.shrinkYonedaCompPresheafFiberIso.hom.app X ≫ f.hom.app X :=
  LeanPool.ClassifyingTopoi.shrinkYonedaCompPresheafFiberIso_naturality f X

/-- The isomorphism `yonedaCompPresheafFiberIso` is natural in the point. -/
theorem yonedaCompPresheafFiberIso_naturality (X : HornCat.{u} L) :
    f.presheafFiber.app (yoneda.obj X) ≫ (yonedaCompPresheafFiberIso Φ₁).hom.app X =
      (yonedaCompPresheafFiberIso Φ₂).hom.app X ≫ f.hom.app X :=
  yonedaCompPointPresheafFiberIso_naturality f X

end PointIso

/-- The extension of a presheaf structure, composed with the Yoneda embedding, is the functor of
the fibers. -/
noncomputable def yonedaCompExtensionIso : yoneda ⋙ extension.{u} P ≅ (fibers.{u} P).flip :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun d => (yonedaCompPointPresheafFiberIso (@point L _ (P.fiberStr d))).app X)
      (fun g => yonedaCompPointPresheafFiberIso_naturality _ X))
    (fun g => by
      ext d : 2
      exact ((yonedaCompPointPresheafFiberIso (@point L _ (P.fiberStr d))).hom.naturality g))

instance (n : ℕ) :
    PreservesLimit (Discrete.functor fun _ : Fin n => top.{u} (L := L) 1) (fibers.{u} P).flip :=
  preservesLimit_of_natIso _ (yonedaCompExtensionIso P)

/-- The isomorphism between the carrier of the structure of the fibers and the carrier. -/
noncomputable def fibersCarrierIso : (fibers.{u} P).flip.obj (top 1) ≅ P.carrier :=
  NatIso.ofComponents (fun d => Equiv.toIso
    { toFun := fun x => x.1 0
      invFun := fun a => ⟨fun _ => a, fun _ h => nomatch h⟩
      left_inv := fun x => Subtype.ext (funext fun i => by rw [Subsingleton.elim i 0])
      right_inv := fun _ => rfl })
    (fun _ => rfl)

/-- The tuple of a section of a power of the carrier of the structure of the fibers. -/
theorem secEquiv_isoPow_fibers {k : ℕ} (d : Dᵒᵖ) (z : ((fibers.{u} P).flip.obj (top k)).obj d) :
    secEquiv _ k d ((isoPow (fibers.{u} P).flip k).hom.app d z) =
      fun i => ⟨fun _ => z.1 i, fun _ h => nomatch h⟩ := by
  rw [secEquiv_isoPow_hom]
  rfl

/-- The section of a power of the carrier of the structure of the fibers with a given tuple. -/
theorem isoPow_fibers_inv_secEquiv_symm {k : ℕ} (d : Dᵒᵖ)
    (x : Fin k → ((fibers.{u} P).flip.obj (top 1)).obj d) :
    (isoPow (fibers.{u} P).flip k).inv.app d ((secEquiv _ k d).symm x) =
      ⟨fun i => (x i).1 0, fun _ h => nomatch h⟩ := by
  have : (secEquiv _ k d).symm x = (isoPow (fibers.{u} P).flip k).hom.app d
      ⟨fun i => (x i).1 0, fun _ h => nomatch h⟩ := by
    rw [Equiv.symm_apply_eq]
    erw [secEquiv_isoPow_fibers]
    funext i
    exact Subtype.ext (funext fun j => by rw [Subsingleton.elim j 0])
  rw [this]
  exact Iso.hom_inv_id_app_apply _ _ _

/-- The structure of the fibers of a presheaf structure is isomorphic to it. -/
theorem isomorphic_fibers : (hornStructure (fibers.{u} P).flip).Isomorphic P := by
  refine ⟨fibersCarrierIso P, isHom_of_forall _ (fun d k f x => ?_) (fun d k R x hx => ?_),
    isHom_of_forall _ (fun d k f x => ?_) (fun d k R x hx => ?_)⟩
  · rw [CatStructure.fiberStr_funMap, CatStructure.fiberStr_funMap]
    change (fibersCarrierIso P).hom.app d (((fibers.{u} P).flip.map (funMor f)).app d
      ((isoPow (fibers.{u} P).flip k).inv.app d ((secEquiv _ k d).symm x))) = _
    rw [isoPow_fibers_inv_secEquiv_symm]
    rfl
  · rw [CatStructure.fiberStr_relMap] at hx
    obtain ⟨y, hy⟩ := hx
    have h₁ := congrArg ((isoPow (fibers.{u} P).flip k).inv.app d) hy
    change (isoPow (fibers.{u} P).flip k).inv.app d ((isoPow (fibers.{u} P).flip k).hom.app d
      (((fibers.{u} P).flip.map (ι (relObj R))).app d y)) = _ at h₁
    rw [Iso.hom_inv_id_app_apply, isoPow_fibers_inv_secEquiv_symm] at h₁
    have h₂ : y.1 = fun i => (x i).1 0 := congrArg Subtype.val h₁
    have hR := y.2 _ (List.mem_singleton_self _)
    rw [h₂] at hR
    exact hR
  · rw [CatStructure.fiberStr_funMap, CatStructure.fiberStr_funMap]
    change _ = ((fibers.{u} P).flip.map (funMor f)).app d
      ((isoPow (fibers.{u} P).flip k).inv.app d ((secEquiv _ k d).symm _))
    rw [isoPow_fibers_inv_secEquiv_symm]
    rfl
  · rw [CatStructure.fiberStr_relMap]
    refine ⟨⟨x, fun a ha => ?_⟩, ?_⟩
    · rw [List.mem_singleton] at ha
      subst ha
      exact hx
    · rw [Equiv.eq_symm_apply]
      change secEquiv _ k d ((isoPow (fibers.{u} P).flip k).hom.app d
        (((fibers.{u} P).flip.map (ι (relObj R))).app d ⟨x, _⟩)) = _
      rw [secEquiv_isoPow_fibers]
      rfl

variable {K : GrothendieckTopology D}

/-- The extension of a presheaf structure followed by sheafification is a left adjoint. -/
theorem isLeftAdjoint_extension_comp :
    (extension.{u} P ⋙ presheafToSheaf K (Type (max u₁ u₂ u))).IsLeftAdjoint :=
  Presheaf.isLeftAdjoint_of_preservesColimits _

end HornCat

end LeanPool.ClassifyingTopoi.Syntactic
