/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.CategoryTheory.Subfunctor.Subobject
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Images
public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Groupoid

/-!
# Pointwise description of subfunctor lattices

For a type-valued functor `F : C ⥤ Type w` (in particular a presheaf `Cᵒᵖ ⥤ Type w`), the
lattice `Subfunctor F` is computed objectwise: `⊓`, `⊔`, `⊥`, `⊤` are intersection, union,
empty set and full set. Mathlib identifies this lattice with `Subobject F` through the order
isomorphism `Subfunctor.orderIsoSubobject F`. We record:

* `Subfunctor.disjoint_iff_forall`, `Subfunctor.codisjoint_iff_forall`,
  `Subfunctor.isCompl_iff_forall`: disjointness, codisjointness and complementation of
  subfunctors are checked objectwise, on the sets `S.obj U`;
* `Subfunctor.isCompl_subobject_iff`: the same statement for subobjects of `F`, through the
  order isomorphism with subfunctors;
* `Subfunctor.compl`: when every morphism of `C` is an isomorphism, the objectwise set
  complement of a subfunctor is a subfunctor, and it is a lattice complement
  (`Subfunctor.isCompl_compl`).

We also record two facts used to transport the Boolean and De Morgan conditions along
equivalences of categories (`Boolean.lean`, `DeMorgan.lean`):

* `LeanPool.ToposTheoreticBridges.subobjectOrderIsoOfEquivalence`: an equivalence
  `e : E ≌ E'` induces order isomorphisms `Subobject X ≃o Subobject (e.functor.obj X)`;
* `LeanPool.ToposTheoreticBridges.disjoint_orderIso_apply_iff`,
  `LeanPool.ToposTheoreticBridges.codisjoint_orderIso_apply_iff`,
  `LeanPool.ToposTheoreticBridges.isCompl_orderIso_apply_iff`: order isomorphisms preserve and
  reflect disjointness, codisjointness and complementation, for partial orders with the
  relevant bounds only (Mathlib's `disjoint_map_orderIso_iff` and `OrderIso.isCompl_iff` ask for
  (semi)lattices, which `Subobject X` only is under extra limit assumptions).
-/

@[expose] public section

universe w v u

namespace CategoryTheory

namespace Subfunctor

variable {C : Type u} [Category.{v} C] {F : C ⥤ Type w}

/-- Two subfunctors are disjoint iff their sections are disjoint on every object. -/
theorem disjoint_iff_forall {S T : Subfunctor F} :
    Disjoint S T ↔ ∀ U, Disjoint (S.obj U) (T.obj U) := by
  rw [disjoint_iff]
  constructor
  · intro h U
    rw [Set.disjoint_iff_inter_eq_empty, ← min_obj, h, bot_obj]
  · intro h
    ext U x
    simpa using fun hS hT => Set.disjoint_left.1 (h U) hS hT

/-- Two subfunctors are codisjoint iff their sections cover every `F.obj U`. -/
theorem codisjoint_iff_forall {S T : Subfunctor F} :
    Codisjoint S T ↔ ∀ U, Codisjoint (S.obj U) (T.obj U) := by
  rw [codisjoint_iff]
  constructor
  · intro h U
    rw [codisjoint_iff, ← max_obj, h, top_obj, Set.top_eq_univ]
  · intro h
    ext U x
    simp only [max_obj, top_obj, Set.mem_univ, iff_true]
    have hU := codisjoint_iff.1 (h U)
    rw [Set.top_eq_univ] at hU
    exact Set.eq_univ_iff_forall.1 hU x

/-- Two subfunctors are complements of each other iff they are so on every object. -/
theorem isCompl_iff_forall {S T : Subfunctor F} :
    IsCompl S T ↔ ∀ U, IsCompl (S.obj U) (T.obj U) := by
  simp only [isCompl_iff, disjoint_iff_forall, codisjoint_iff_forall]
  exact ⟨fun h U => ⟨h.1 U, h.2 U⟩, fun h => ⟨fun U => (h U).1, fun U => (h U).2⟩⟩

/-- Two subobjects of a type-valued functor are complements of each other iff the
corresponding subfunctors (images of their arrows) are so on every object. -/
theorem isCompl_subobject_iff {A B : Subobject F} :
    IsCompl A B ↔
      ∀ U, IsCompl ((range A.arrow).obj U) ((range B.arrow).obj U) := by
  rw [(orderIsoSubobject F).symm.isCompl_iff, isCompl_iff_forall]
  rfl

/-- A subfunctor has a lattice complement iff the corresponding subobject has one. -/
theorem exists_isCompl_iff_subobject (S : Subfunctor F) :
    (∃ T : Subfunctor F, IsCompl S T) ↔
      ∃ B : Subobject F, IsCompl (orderIsoSubobject F S) B := by
  constructor
  · rintro ⟨T, hT⟩
    exact ⟨orderIsoSubobject F T, (orderIsoSubobject F).isCompl_iff.1 hT⟩
  · rintro ⟨B, hB⟩
    refine ⟨(orderIsoSubobject F).symm B, ?_⟩
    rw [(orderIsoSubobject F).isCompl_iff, OrderIso.apply_symm_apply]
    exact hB

/-- When every morphism of `C` is an isomorphism, the objectwise complement of a subfunctor
is a subfunctor. -/
def compl [IsGroupoid C] (S : Subfunctor F) : Subfunctor F where
  obj U := (S.obj U)ᶜ
  map {U V} i x hx hix := hx (by
    have := S.map (inv i) hix
    simpa using this)

@[simp]
theorem compl_obj [IsGroupoid C] (S : Subfunctor F) (U : C) :
    S.compl.obj U = (S.obj U)ᶜ :=
  rfl

/-- Over a groupoid, the objectwise complement is a lattice complement. -/
theorem isCompl_compl [IsGroupoid C] (S : Subfunctor F) : IsCompl S S.compl :=
  isCompl_iff_forall.2 fun _ => _root_.isCompl_compl

end Subfunctor

end CategoryTheory

namespace LeanPool.ToposTheoreticBridges

open CategoryTheory

section OrderIso

variable {α β : Type*}

/-- An order isomorphism between partial orders with a bottom element preserves and reflects
disjointness. -/
theorem disjoint_orderIso_apply_iff [PartialOrder α] [OrderBot α] [PartialOrder β] [OrderBot β]
    (f : α ≃o β) {a b : α} : Disjoint (f a) (f b) ↔ Disjoint a b := by
  constructor
  · intro h x ha hb
    rw [← f.le_iff_le, f.map_bot]
    exact h (f.monotone ha) (f.monotone hb)
  · intro h y ha hb
    rw [← f.apply_symm_apply y, ← f.map_bot, f.le_iff_le]
    exact h (f.symm_apply_le.2 ha) (f.symm_apply_le.2 hb)

/-- An order isomorphism between partial orders with a top element preserves and reflects
codisjointness. -/
theorem codisjoint_orderIso_apply_iff [PartialOrder α] [OrderTop α] [PartialOrder β]
    [OrderTop β] (f : α ≃o β) {a b : α} : Codisjoint (f a) (f b) ↔ Codisjoint a b := by
  rw [← disjoint_toDual_iff, ← disjoint_toDual_iff]
  exact disjoint_orderIso_apply_iff f.dual

/-- An order isomorphism between bounded partial orders preserves and reflects
complementation. -/
theorem isCompl_orderIso_apply_iff [PartialOrder α] [BoundedOrder α] [PartialOrder β]
    [BoundedOrder β] (f : α ≃o β) {a b : α} : IsCompl (f a) (f b) ↔ IsCompl a b := by
  rw [isCompl_iff, isCompl_iff, disjoint_orderIso_apply_iff, codisjoint_orderIso_apply_iff]

end OrderIso

/-- An equivalence of categories `e : E ≌ E'` induces an order isomorphism between the
subobjects of `X` and those of `e.functor.obj X`. -/
noncomputable def subobjectOrderIsoOfEquivalence {E E' : Type*} [Category E] [Category E']
    (e : E ≌ E') (X : E) : Subobject X ≃o Subobject (e.functor.obj X) :=
  (Subobject.lowerEquivalence (MonoOver.congr X e)).toOrderIso

end LeanPool.ToposTheoreticBridges
