/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Examples.PresheafType
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.CategoryTheory.Sites.Canonical

/-!
# Irreducible formulae and finitely presentable models (roadmap 3.5)

The definitions of roadmap 3.5:

* `LeanPool.ClassifyingTopoi.GeometricFormula.IsIrreducible`: a formula is irreducible for a
  generic model `U` when only the maximal sieve covers its interpretation in the canonical
  topology of the topos;
* `LeanPool.ClassifyingTopoi.SetModel`, with the homomorphisms of structures as morphisms, and
  `LeanPool.ClassifyingTopoi.FPModel`, the finitely presentable set-models;
* `LeanPool.ClassifyingTopoi.SetModel.IsPresentedBy`: a set-model presented by a formula, with
  a generic assignment sent uniquely to every assignment satisfying the formula;
* `LeanPool.ClassifyingTopoi.SetModel.forget`: the underlying type of a set-model;
* `LeanPool.ClassifyingTopoi.irreducibleFormulaObjects`: the objects of the topos isomorphic to
  the interpretation of an irreducible formula.

The identity, composition and the laws of the category of set-models are those of Mathlib's
homomorphisms of first-order structures (`FirstOrder.Language.Hom`).

## Not formalised

The theorems of roadmap 3.5 on theories of presheaf type (`isOfPresheafType_iff_forall_covered`,
`exists_isClassifyingSite_fpModel`, `isIrreducible_iff_exists_presentedBy`,
`exists_isPresentedBy_irreducible_of_isFinitelyPresentable`,
`nonempty_equivalence_irreducible_fpModel`, `isIdempotentComplete_irreducible`) are not
formalised: they need the identification of the points of a classifying topos with the set-models
and of the finitely presentable models with the irreducible objects (Caramello, *Theories, Sites,
Toposes*, chapter 6), for which the completeness of geometric logic for set-models is missing.
-/

@[expose] public section

universe u u₁ u₂

namespace LeanPool.ClassifyingTopoi

open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits

attribute [local instance high] Sheaf.instHasColimitsOfShape

variable {L : Language.{u₁, u₂}}

/-- **3.5.** A geometric formula is irreducible for a generic model `U`: the object interpreting
it in the topos is irreducible, that is, only the maximal sieve covers it in the canonical
topology. -/
def GeometricFormula.IsIrreducible {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (U : CatStructure L (Sheaf J (Type u))) {n : ℕ} (φ : GeometricFormula.{u} L n) : Prop :=
  ∀ S : Sieve (Subobject.underlying.obj (U.interp φ)),
    S ∈ Sheaf.canonicalTopology (Sheaf J (Type u)) (Subobject.underlying.obj (U.interp φ)) →
      S = ⊤

/-- **3.5.** A set-model of a geometric theory: a structure on a type in `Type u` satisfying every
axiom. -/
structure SetModel (T : GeometricTheory.{u} L) where
  /-- The underlying type. -/
  carrier : Type u
  /-- The structure. -/
  [str : L.Structure carrier]
  /-- Every axiom holds. -/
  isModel : T.IsSetModel carrier

attribute [instance] SetModel.str

/-- **3.5.** The category of set-models of `T` with the homomorphisms of structures. -/
instance (T : GeometricTheory.{u} L) : Category.{u} (SetModel T) where
  Hom M N := M.carrier →[L] N.carrier
  id M := FirstOrder.Language.Hom.id L M.carrier
  comp f g := g.comp f

/-- **3.5.** The finitely presentable set-models of `T`. -/
abbrev FPModel (T : GeometricTheory.{u} L) : Type _ :=
  ObjectProperty.FullSubcategory (fun M : SetModel T => IsFinitelyPresentable.{u} M)

/-- **3.5.** A set-model `M` is presented by `φ` when some assignment `ξ` in `M` satisfying `φ`
is sent, by a unique homomorphism, to each assignment `b` satisfying `φ` in a model `N`. -/
def SetModel.IsPresentedBy {T : GeometricTheory.{u} L} (M : SetModel T) {n : ℕ}
    (φ : GeometricFormula.{u} L n) : Prop :=
  ∃ ξ : Fin n → M.carrier, φ.Realize ξ ∧ ∀ (N : SetModel T) (b : Fin n → N.carrier),
    φ.Realize b → ∃! f : M ⟶ N, ⇑(show M.carrier →[L] N.carrier from f) ∘ ξ = b

/-- **3.5.** The underlying type of a set-model, as a functor. -/
def SetModel.forget (T : GeometricTheory.{u} L) : SetModel T ⥤ Type u where
  obj M := M.carrier
  map {M N} f := TypeCat.ofHom (show M.carrier →[L] N.carrier from f)

/-- **3.5.** The objects of the topos isomorphic to the interpretation of an irreducible
formula. -/
def irreducibleFormulaObjects {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (U : CatStructure L (Sheaf J (Type u))) : ObjectProperty (Sheaf J (Type u)) :=
  fun A => ∃ (n : ℕ) (φ : GeometricFormula.{u} L n), φ.IsIrreducible U ∧
    Nonempty (A ≅ Subobject.underlying.obj (U.interp φ))

end LeanPool.ClassifyingTopoi
