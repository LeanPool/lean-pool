/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.DenseAtCoyoneda
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# The tensor product of a presheaf and a functor to types

For a small category `C`, a functor `A : C ⥤ Type u` and a presheaf `P : Cᵒᵖ ⥤ Type u`, the
tensor product `P ⊗_C A` is the colimit of `P` over the opposite of the category of elements of
`A`: its elements are classes of triples `(c, a, p)` with `a : A(c)` and `p : P(c)`, the class
of `(c, A(f) a, p)` being that of `(c', a, P(f) p)` for `f : c' ⟶ c`
(`LeanPool.ClassifyingTopoi.tensorι_map`). It is functorial in `A` and in `P`
(`LeanPool.ClassifyingTopoi.tensorFunctor`), and for a functor `F : C ⥤ (Dᵒᵖ ⥤ Type u)` it
gives the extension `P ↦ (d ↦ P ⊗_C F(-)(d))` of `F` along the Yoneda embedding
(`LeanPool.ClassifyingTopoi.tensorExtension`), which preserves colimits and restricts to `F` on
representable presheaves (`LeanPool.ClassifyingTopoi.shrinkYonedaCompTensorExtensionIso`).

## References

* S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic*, VII.2 (the tensor product
  `P ⊗_C A`).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace LeanPool.ClassifyingTopoi

variable {C : Type u} [SmallCategory C]

section Tensor

/-- The tensor product `P ⊗_C A` as a functor of the presheaf `P`: the colimit of `P` over the
opposite of the category of elements of `A : C ⥤ Type u`. -/
noncomputable abbrev tensorObj (A : C ⥤ Type u) : (Cᵒᵖ ⥤ Type u) ⥤ Type u :=
  (Functor.whiskeringLeft _ _ _).obj (Functor.Elements.π A).op ⋙ colim

/-- The map of tensor products induced by a natural transformation `A ⟶ A'`. -/
noncomputable def tensorMap {A A' : C ⥤ Type u} (α : A ⟶ A') : tensorObj A ⟶ tensorObj A' where
  app P := colimit.desc ((Functor.Elements.π A).op ⋙ P)
    { pt := colimit ((Functor.Elements.π A').op ⋙ P)
      ι :=
        { app x := colimit.ι ((Functor.Elements.π A').op ⋙ P)
            (op (A'.elementsMk _ (α.app _ x.unop.val)))
          naturality x y f := by
            have h : A'.map f.unop.hom (α.app _ y.unop.val) = α.app _ x.unop.val := by
              rw [← NatTrans.naturality_apply, f.unop.map_val]
            simpa using colimit.w ((Functor.Elements.π A').op ⋙ P)
              (Functor.Elements.homMk (x := A'.elementsMk _ (α.app _ y.unop.val))
                (y := A'.elementsMk _ (α.app _ x.unop.val)) f.unop.hom h).op } }
  naturality P Q φ := colimit.hom_ext fun j => by simp

variable (C) in
/-- The tensor product `P ⊗_C A`, functorial in `A : C ⥤ Type u` and `P : Cᵒᵖ ⥤ Type u`. -/
noncomputable def tensorFunctor : (C ⥤ Type u) ⥤ (Cᵒᵖ ⥤ Type u) ⥤ Type u where
  obj A := tensorObj A
  map α := tensorMap α
  map_id A := by
    ext P : 2
    exact colimit.hom_ext fun j => by simp [tensorMap]
  map_comp α β := by
    ext P : 2
    exact colimit.hom_ext fun j => by simp [tensorMap]

variable (A : C ⥤ Type u) (P : Cᵒᵖ ⥤ Type u)

/-- The class of the triple `(c, a, p)` in the tensor product `P ⊗_C A`. -/
noncomputable def tensorι (c : C) (a : A.obj c) (p : P.obj (op c)) :
    ((tensorFunctor C).obj A).obj P :=
  colimit.ι ((Functor.Elements.π A).op ⋙ P) (op (A.elementsMk c a)) p

/-- Every element of the tensor product is the class of a triple. -/
theorem tensorι_surjective (z : ((tensorFunctor C).obj A).obj P) :
    ∃ (c : C) (a : A.obj c) (p : P.obj (op c)), tensorι A P c a p = z := by
  obtain ⟨⟨x⟩, p, rfl⟩ := Types.jointly_surjective' z
  exact ⟨x.obj, x.val, p, rfl⟩

/-- The defining relation of the tensor product: `(c, A(f) a, p)` and `(c', a, P(f) p)` have
the same class, for `f : c' ⟶ c`. -/
theorem tensorι_map {c c' : C} (f : c' ⟶ c) (a : A.obj c') (p : P.obj (op c)) :
    tensorι A P c (A.map f a) p = tensorι A P c' a (P.map f.op p) := by
  exact (colimit.w_apply ((Functor.Elements.π A).op ⋙ P)
    (Functor.Elements.homMk (x := A.elementsMk c' a) (y := A.elementsMk c (A.map f a)) f).op
      p).symm

/-- The tensor product is functorial in the presheaf. -/
@[simp]
theorem tensor_map_tensorι {Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) (c : C) (a : A.obj c)
    (p : P.obj (op c)) :
    ((tensorFunctor C).obj A).map φ (tensorι A P c a p) = tensorι A Q c a (φ.app _ p) :=
  ConcreteCategory.congr_hom
    (ι_colimMap ((Functor.Elements.π A).op.whiskerLeft φ) (op (A.elementsMk c a))) p

/-- The tensor product is functorial in the functor. -/
@[simp]
theorem tensorFunctor_map_tensorι {A' : C ⥤ Type u} (α : A ⟶ A') (c : C) (a : A.obj c)
    (p : P.obj (op c)) :
    ((tensorFunctor C).map α).app P (tensorι A P c a p) = tensorι A' P c (α.app c a) p :=
  ConcreteCategory.congr_hom (colimit.ι_desc (F := (Functor.Elements.π A).op ⋙ P) _
    (op (A.elementsMk c a))) p

/-- Two triples with the same class are related by a zigzag of the defining relation. -/
theorem eqvGen_of_tensorι_eq {c c' : C} {a : A.obj c} {a' : A.obj c'} {p : P.obj (op c)}
    {p' : P.obj (op c')} (h : tensorι A P c a p = tensorι A P c' a' p') :
    Relation.EqvGen ((Functor.Elements.π A).op ⋙ P).ColimitTypeRel
      ⟨op (A.elementsMk c a), p⟩ ⟨op (A.elementsMk c' a'), p'⟩ :=
  Types.colimit_eq h

end Tensor

section Extension

variable {D : Type u} [SmallCategory D] (F : C ⥤ (Dᵒᵖ ⥤ Type u))

/-- The extension of `F : C ⥤ (Dᵒᵖ ⥤ Type u)` along the Yoneda embedding: the presheaf
`d ↦ P ⊗_C F(-)(d)`. -/
noncomputable def tensorExtension : (Cᵒᵖ ⥤ Type u) ⥤ (Dᵒᵖ ⥤ Type u) :=
  (F.flip ⋙ tensorFunctor C).flip

/-- The restriction maps of the extension act on the second component of a triple. -/
@[simp]
theorem tensorExtension_map_tensorι (P : Cᵒᵖ ⥤ Type u) {d d' : Dᵒᵖ} (g : d ⟶ d') (c : C)
    (a : (F.obj c).obj d) (p : P.obj (op c)) :
    ((tensorExtension F).obj P).map g (tensorι (F.flip.obj d) P c a p) =
      tensorι (F.flip.obj d') P c ((F.obj c).map g a) p :=
  tensorFunctor_map_tensorι (F.flip.obj d) P (F.flip.map g) c a p

/-- The extension acts on the third component of a triple. -/
@[simp]
theorem tensorExtension_map_app_tensorι {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) (d : Dᵒᵖ) (c : C)
    (a : (F.obj c).obj d) (p : P.obj (op c)) :
    ((tensorExtension F).map φ).app d (tensorι (F.flip.obj d) P c a p) =
      tensorι (F.flip.obj d) Q c a (φ.app _ p) :=
  tensor_map_tensorι (F.flip.obj d) P φ c a p

variable {F} in
/-- The class of the triple `(c, a, p)` in `P ⊗_C F(-)(d)`, as an element of the extension. -/
noncomputable def extι (P : Cᵒᵖ ⥤ Type u) (d : Dᵒᵖ) (c : C) (a : (F.obj c).obj d)
    (p : P.obj (op c)) : ((tensorExtension F).obj P).obj d :=
  tensorι (F.flip.obj d) P c a p

/-- Every element of the extension is the class of a triple. -/
theorem extι_surjective (P : Cᵒᵖ ⥤ Type u) {d : Dᵒᵖ} (z : ((tensorExtension F).obj P).obj d) :
    ∃ (c : C) (a : (F.obj c).obj d) (p : P.obj (op c)), extι P d c a p = z :=
  tensorι_surjective _ _ z

/-- The defining relation of the tensor product, in the extension. -/
theorem extι_map (P : Cᵒᵖ ⥤ Type u) {d : Dᵒᵖ} {c c' : C} (f : c' ⟶ c) (a : (F.obj c').obj d)
    (p : P.obj (op c)) :
    extι P d c ((F.map f).app d a) p = extι P d c' a (P.map f.op p) :=
  tensorι_map (F.flip.obj d) P f a p

/-- The restriction maps of the extension on classes of triples. -/
@[simp]
theorem tensorExtension_map_extι (P : Cᵒᵖ ⥤ Type u) {d d' : Dᵒᵖ} (g : d ⟶ d') (c : C)
    (a : (F.obj c).obj d) (p : P.obj (op c)) :
    ((tensorExtension F).obj P).map g (extι P d c a p) = extι P d' c ((F.obj c).map g a) p :=
  tensorExtension_map_tensorι F P g c a p

/-- The extension on classes of triples. -/
@[simp]
theorem tensorExtension_map_app_extι {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) (d : Dᵒᵖ) (c : C)
    (a : (F.obj c).obj d) (p : P.obj (op c)) :
    ((tensorExtension F).map φ).app d (extι P d c a p) = extι Q d c a (φ.app _ p) :=
  tensorExtension_map_app_tensorι F φ d c a p

/-- Evaluating the extension at an object is the tensor product with the corresponding
functor. -/
noncomputable def tensorExtensionCompEvaluationIso (d : Dᵒᵖ) :
    tensorExtension F ⋙ (evaluation _ _).obj d ≅ tensorObj (F.flip.obj d) :=
  Iso.refl _

instance : PreservesColimitsOfSize.{u, u} (tensorExtension F) :=
  preservesColimits_of_evaluation _ fun d =>
    preservesColimits_of_natIso (tensorExtensionCompEvaluationIso F d).symm

/-- The value of the extension on a representable presheaf, through the class of the identity. -/
theorem shrinkYonedaCompWhiskeringLeftObjπCompColimIso_inv_app_eq (d : Dᵒᵖ) (c : C)
    (a : (F.obj c).obj d) :
    (Functor.Elements.shrinkYonedaCompWhiskeringLeftObjπCompColimIso.{u}
      (F.flip.obj d)).inv.app c a =
        tensorι (F.flip.obj d) (shrinkYoneda.{u}.obj c) c a
          (shrinkYonedaObjObjEquiv.symm (𝟙 c)) :=
  Functor.Elements.shrinkYonedaCompWhiskeringLeftObjπCompColimIso_inv_app_apply _
    ((F.flip.obj d).elementsMk c a)

/-- The extension restricts to `F` on representable presheaves. -/
noncomputable def shrinkYonedaCompTensorExtensionIso :
    shrinkYoneda.{u} ⋙ tensorExtension F ≅ F :=
  let e := fun d : Dᵒᵖ =>
    Functor.Elements.shrinkYonedaCompWhiskeringLeftObjπCompColimIso.{u} (F.flip.obj d)
  (NatIso.ofComponents
    (fun c => NatIso.ofComponents (fun d => ((e d).app c).symm)
      (fun {d d'} g => by
        ext a
        change (e d').inv.app c ((F.obj c).map g a) =
          ((tensorExtension F).obj (shrinkYoneda.{u}.obj c)).map g ((e d).inv.app c a)
        rw [shrinkYonedaCompWhiskeringLeftObjπCompColimIso_inv_app_eq,
          shrinkYonedaCompWhiskeringLeftObjπCompColimIso_inv_app_eq,
          tensorExtension_map_tensorι]))
    (fun {c c'} f => by
      refine NatTrans.ext (funext fun d => ?_)
      exact (e d).inv.naturality f)).symm

end Extension

end LeanPool.ClassifyingTopoi
