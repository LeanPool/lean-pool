/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntax
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Geometric logic: categorical semantics

Structures for a first-order language `L` in a category `E` with finite products, and the
interpretation of geometric formulas as subobjects of the powers of the carrier, when `E` moreover
has finite limits, images and coproducts indexed by `Type w`.

## Main definitions

* `LeanPool.ClassifyingTopoi.CatStructure`: an `L`-structure in `E`: a carrier `A`, a morphism
  `Aᵏ ⟶ A` for each `k`-ary function symbol and an object over `Aᵏ` for each `k`-ary relation
  symbol, whose image interprets the relation;
* `LeanPool.ClassifyingTopoi.CatStructure.termMap`: terms as morphisms `Aⁿ ⟶ A`;
* `LeanPool.ClassifyingTopoi.CatStructure.interp`: geometric formulas as subobjects of `Aⁿ`
  (meets, images of coproducts, equalizers, pullbacks of images, images along projections);
* `LeanPool.ClassifyingTopoi.CatStructure.IsModel`: models of a geometric theory;
* `LeanPool.ClassifyingTopoi.CatStructure.IsHom`,
  `LeanPool.ClassifyingTopoi.CatStructure.Isomorphic`: homomorphisms and isomorphisms of
  structures.

## References

* P. T. Johnstone, *Sketches of an Elephant*, D1.2.
* O. Caramello, *Theories, Sites, Toposes*, 1.3 (categorical structures) and 1.3.3
  (interpretation of formulas).
-/

@[expose] public section

universe w u₁ u₂ v u

namespace LeanPool.ClassifyingTopoi

open CategoryTheory CategoryTheory.Limits

/-- An `L`-structure in a category with finite products: an object, a morphism
`Aᵏ ⟶ A` for each `k`-ary function symbol and an object over `Aᵏ` for each `k`-ary relation
symbol, whose image is the interpretation of the relation. -/
structure CatStructure (L : FirstOrder.Language.{u₁, u₂}) (E : Type u) [Category.{v} E]
    [HasFiniteProducts E] where
  /-- The underlying object. -/
  carrier : E
  /-- The interpretation of a function symbol. -/
  funMap : ∀ {k : ℕ}, L.Functions k → ((∏ᶜ fun _ : Fin k => carrier) ⟶ carrier)
  /-- An object over `Aᵏ` whose image interprets a relation symbol. -/
  relMap : ∀ {k : ℕ}, L.Relations k → Over (∏ᶜ fun _ : Fin k => carrier)

variable {L : FirstOrder.Language.{u₁, u₂}} {E : Type u} [Category.{v} E]

namespace CatStructure

/-- The `n`-th power of the carrier, the object of assignments of the context
`Fin n`. -/
noncomputable abbrev pow [HasFiniteProducts E] (M : CatStructure L E) (n : ℕ) : E :=
  ∏ᶜ fun _ : Fin n => M.carrier

/-- The interpretation of a term in the context `Fin n` as a morphism `Aⁿ ⟶ A`. -/
noncomputable def termMap [HasFiniteProducts E] (M : CatStructure L E) {n : ℕ} :
    L.Term (Fin n) → (M.pow n ⟶ M.carrier)
  | .var i => Pi.π _ i
  | .func f ts => Pi.lift (fun j => M.termMap (ts j)) ≫ M.funMap f

/-- The interpretation of a geometric formula in the context `Fin n` as a subobject of
`Aⁿ`: meets, images of coproducts, equalizers, pullbacks of images, and images along the
projection forgetting the last variable. -/
noncomputable def interp [HasFiniteLimits E] [HasImages E] [HasCoproducts.{w} E]
    (M : CatStructure L E) : {n : ℕ} → GeometricFormula.{w} L n → Subobject (M.pow n)
  | _, .top => ⊤
  | _, .and φ ψ => M.interp φ ⊓ M.interp ψ
  | _, .iSup φ => imageSubobject (Sigma.desc fun i => (M.interp (φ i)).arrow)
  | _, .equal t₁ t₂ => equalizerSubobject (M.termMap t₁) (M.termMap t₂)
  | _, .rel R ts =>
      (Subobject.pullback (Pi.lift fun i => M.termMap (ts i))).obj (imageSubobject (M.relMap R).hom)
  | n, .ex φ =>
      (Subobject.exists (Pi.lift fun i : Fin n =>
        Pi.π (fun _ : Fin (n + 1) => M.carrier) i.castSucc)).obj (M.interp φ)

/-- A model of a geometric theory: the interpretation of the hypothesis of every axiom
lies below that of its conclusion. -/
def IsModel [HasFiniteLimits E] [HasImages E] [HasCoproducts.{w} E]
    (M : CatStructure L E) (T : GeometricTheory.{w} L) : Prop :=
  ∀ σ ∈ T, M.interp σ.lhs ≤ M.interp σ.rhs

/-- A homomorphism of structures: a morphism of carriers commuting with the function
symbols and mapping each relation into its counterpart. -/
structure IsHom [HasFiniteLimits E] [HasImages E] (M N : CatStructure L E)
    (h : M.carrier ⟶ N.carrier) : Prop where
  /-- Compatibility with the function symbols. -/
  funMap : ∀ {k : ℕ} (f : L.Functions k),
    M.funMap f ≫ h = Limits.Pi.map (fun _ => h) ≫ N.funMap f
  /-- The relations are mapped into the relations. -/
  relMap : ∀ {k : ℕ} (R : L.Relations k), imageSubobject (M.relMap R).hom ≤
    (Subobject.pullback (Limits.Pi.map fun _ : Fin k => h)).obj (imageSubobject (N.relMap R).hom)

/-- Two structures are isomorphic when an isomorphism of carriers is a homomorphism in
both directions. -/
def Isomorphic [HasFiniteLimits E] [HasImages E] (M N : CatStructure L E) : Prop :=
  ∃ e : M.carrier ≅ N.carrier, M.IsHom N e.hom ∧ N.IsHom M e.inv

end CatStructure

end LeanPool.ClassifyingTopoi
