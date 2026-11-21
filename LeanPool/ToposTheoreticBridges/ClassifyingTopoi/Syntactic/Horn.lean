/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Semantics
public import Mathlib.CategoryTheory.Category.Basic

/-!
# The Horn category of a language

For a first-order language `L`, the *Horn category* `HornCat L` has as objects the Horn
formulas in context: a context `Fin n` with a finite list of atomic formulas (equalities of terms
and relation symbols applied to terms). A morphism `X ⟶ Y` is a tuple of terms `σ` in the context
of `X`, indexed by the variables of `Y`, such that every assignment satisfying `X` in a structure
satisfies `Y` after substitution by `σ`; two tuples are identified when they agree at every
assignment satisfying `X`. Composition is substitution.

The conditions are semantic (validity in every structure on a type of the universe
`max u₁ u₂ u`), which is equivalent to provability in Horn logic but needs no proof theory. The
category is equivalent to the opposite of the category of finitely presented `L`-structures; its
presheaf topos classifies the empty theory over `L`
(`LeanPool.ClassifyingTopoi.Syntactic.isClassifyingSite_hornCat`).

## Main definitions

* `LeanPool.ClassifyingTopoi.Syntactic.Atom`: atomic formulas, in the universe `max u₁ u₂ u`;
* `LeanPool.ClassifyingTopoi.Syntactic.HornCat`: the objects, Horn formulas in context, with
  `HornCat.Holds` (satisfaction) and `HornCat.toFormula` (the geometric formula);
* the category structure on `HornCat L`, a small category in the universe `max u₁ u₂ u`.
-/

@[expose] public section

universe u w u₁ u₂

namespace LeanPool.ClassifyingTopoi.Syntactic

open FirstOrder FirstOrder.Language CategoryTheory

/-- Atomic formulas in the context `Fin n`: equalities of terms and relation symbols applied to
terms. The universe is raised to `max u₁ u₂ u` so that the Horn category is small there. -/
inductive Atom (L : Language.{u₁, u₂}) (n : ℕ) : Type (max u₁ u₂ u)
  /-- Equality of two terms. -/
  | equal (t₁ t₂ : L.Term (Fin n))
  /-- A relation symbol applied to terms. -/
  | rel {k : ℕ} (R : L.Relations k) (ts : Fin k → L.Term (Fin n))

variable {L : Language.{u₁, u₂}}

namespace Atom

/-- Satisfaction of an atomic formula at an assignment. -/
def Realize {M : Type*} [L.Structure M] {n : ℕ} : Atom.{u} L n → (Fin n → M) → Prop
  | .equal t₁ t₂, x => t₁.realize x = t₂.realize x
  | .rel R ts, x => Structure.RelMap R fun i => (ts i).realize x

/-- An atomic formula as a geometric formula. -/
def toFormula {n : ℕ} : Atom.{u} L n → GeometricFormula.{w} L n
  | .equal t₁ t₂ => .equal t₁ t₂
  | .rel R ts => .rel R ts

/-- The geometric formula of an atom is realized exactly where the atom is. -/
@[simp]
theorem realize_toFormula {M : Type*} [L.Structure M] {n : ℕ} (a : Atom.{u} L n)
    (x : Fin n → M) : (a.toFormula : GeometricFormula.{w} L n).Realize x ↔ a.Realize x := by
  cases a <;> rfl

/-- Renaming the variables of an atomic formula. -/
def relabel {n m : ℕ} (ρ : Fin n → Fin m) : Atom.{u} L n → Atom.{u} L m
  | .equal t₁ t₂ => .equal (t₁.relabel ρ) (t₂.relabel ρ)
  | .rel R ts => .rel R fun i => (ts i).relabel ρ

/-- Satisfaction of a renamed atomic formula. -/
@[simp]
theorem realize_relabel {M : Type*} [L.Structure M] {n m : ℕ} (ρ : Fin n → Fin m)
    (a : Atom.{u} L n) (x : Fin m → M) : (a.relabel ρ).Realize x ↔ a.Realize (x ∘ ρ) := by
  cases a <;> simp [relabel, Realize, Term.realize_relabel]

/-- Homomorphisms preserve atomic formulas. -/
theorem realize_hom {M N : Type*} [L.Structure M] [L.Structure N] (f : M →[L] N) {n : ℕ}
    (a : Atom.{u} L n) (x : Fin n → M) (h : a.Realize x) : a.Realize (f ∘ x) := by
  cases a with
  | equal t₁ t₂ =>
    change t₁.realize (f ∘ x) = t₂.realize (f ∘ x)
    rw [HomClass.realize_term f, HomClass.realize_term f]
    exact congrArg f h
  | rel R ts =>
    change Structure.RelMap R fun i => (ts i).realize (f ∘ x)
    simp_rw [HomClass.realize_term f]
    exact f.map_rel R _ h

end Atom

/-- Horn formulas in context, the objects of the Horn category: a context `Fin n` and a finite
list of atomic formulas, understood as their conjunction. -/
structure HornCat (L : Language.{u₁, u₂}) : Type (max u₁ u₂ u) where
  /-- The length of the context. -/
  n : ℕ
  /-- The atomic formulas. -/
  atoms : List (Atom.{u} L n)

namespace HornCat

/-- Satisfaction of a Horn formula in context: all its atoms hold. -/
def Holds (X : HornCat.{u} L) {M : Type*} [L.Structure M] (x : Fin X.n → M) : Prop :=
  ∀ a ∈ X.atoms, a.Realize x

/-- The Horn formula `⊤` in the context `Fin n`. -/
abbrev top (n : ℕ) : HornCat.{u} L :=
  ⟨n, []⟩

/-- Every assignment satisfies `⊤`. -/
@[simp]
theorem holds_top {M : Type*} [L.Structure M] {n : ℕ} (x : Fin n → M) :
    (top.{u} (L := L) n).Holds x :=
  fun _ h => nomatch h

/-- The geometric formula of a Horn formula in context: the conjunction of its atoms. -/
def toFormula (X : HornCat.{u} L) : GeometricFormula.{w} L X.n :=
  X.atoms.foldr (fun a φ => .and a.toFormula φ) .top

/-- The geometric formula of a list of atoms is realized where all the atoms are. -/
theorem realize_foldr {M : Type*} [L.Structure M] {n : ℕ} (l : List (Atom.{u} L n))
    (x : Fin n → M) :
    (l.foldr (fun a (φ : GeometricFormula.{w} L n) => .and a.toFormula φ) .top).Realize x ↔
      ∀ a ∈ l, a.Realize x := by
  induction l with
  | nil => simp [GeometricFormula.Realize]
  | cons a l ih =>
    simp only [List.foldr_cons, List.mem_cons, forall_eq_or_imp, ← ih]
    exact and_congr (Atom.realize_toFormula a x) Iff.rfl

/-- The geometric formula of a Horn formula is realized exactly where it holds. -/
@[simp]
theorem realize_toFormula (X : HornCat.{u} L) {M : Type*} [L.Structure M] (x : Fin X.n → M) :
    (X.toFormula : GeometricFormula.{w} L X.n).Realize x ↔ X.Holds x :=
  realize_foldr X.atoms x

/-- Homomorphisms preserve Horn formulas. -/
theorem holds_hom {M N : Type*} [L.Structure M] [L.Structure N] (f : M →[L] N)
    (X : HornCat.{u} L) {x : Fin X.n → M} (h : X.Holds x) : X.Holds (f ∘ x) :=
  fun a ha => a.realize_hom f x (h a ha)

/-- A tuple of terms of the context of `X`, indexed by the variables of `Y`, is a morphism
`X ⟶ Y` when every assignment satisfying `X` in a structure on a type of the universe
`max u₁ u₂ u` satisfies `Y` after substitution. -/
def IsMor (X Y : HornCat.{u} L) (σ : Fin Y.n → L.Term (Fin X.n)) : Prop :=
  ∀ (M : Type (max u₁ u₂ u)) [L.Structure M] (x : Fin X.n → M), X.Holds x →
    Y.Holds fun i => (σ i).realize x

/-- Two morphisms `X ⟶ Y` are identified when they agree on all assignments satisfying `X`. -/
def homSetoid (X Y : HornCat.{u} L) : Setoid {σ // IsMor X Y σ} where
  r σ τ := ∀ (M : Type (max u₁ u₂ u)) [L.Structure M] (x : Fin X.n → M), X.Holds x →
    ∀ i, (σ.1 i).realize x = (τ.1 i).realize x
  iseqv :=
    { refl := fun _ _ _ _ _ _ => rfl
      symm := fun h M _ x hx i => (h M x hx i).symm
      trans := fun h h' M _ x hx i => (h M x hx i).trans (h' M x hx i) }

/-- Morphisms of the Horn category: tuples of terms up to agreement. -/
structure Arrow (X Y : HornCat.{u} L) : Type (max u₁ u₂ u) where
  /-- The underlying class of tuples of terms. -/
  q : Quotient (homSetoid X Y)

/-- The morphism given by a tuple of terms. -/
def Arrow.mk' {X Y : HornCat.{u} L} (σ : Fin Y.n → L.Term (Fin X.n)) (hσ : IsMor X Y σ) :
    Arrow X Y :=
  ⟨⟦⟨σ, hσ⟩⟧⟩

/-- Every morphism is given by a tuple of terms. -/
theorem Arrow.exists_eq_mk' {X Y : HornCat.{u} L} (f : Arrow X Y) :
    ∃ (σ : Fin Y.n → L.Term (Fin X.n)) (hσ : IsMor X Y σ), f = Arrow.mk' σ hσ := by
  obtain ⟨q⟩ := f
  induction q using Quotient.ind with | _ σ => exact ⟨σ.1, σ.2, rfl⟩

/-- Two tuples give the same morphism iff they agree on all assignments satisfying the
source. -/
theorem Arrow.mk'_eq_mk'_iff {X Y : HornCat.{u} L} {σ τ : Fin Y.n → L.Term (Fin X.n)}
    (hσ : IsMor X Y σ) (hτ : IsMor X Y τ) :
    Arrow.mk' σ hσ = Arrow.mk' τ hτ ↔ ∀ (M : Type (max u₁ u₂ u)) [L.Structure M]
      (x : Fin X.n → M), X.Holds x → ∀ i, (σ i).realize x = (τ i).realize x := by
  constructor
  · intro h
    exact Quotient.exact (congrArg Arrow.q h)
  · intro h
    exact congrArg Arrow.mk (Quotient.sound h)

/-- Composition of tuples of terms is a morphism. -/
theorem isMor_comp {X Y Z : HornCat.{u} L} {σ : Fin Y.n → L.Term (Fin X.n)}
    {τ : Fin Z.n → L.Term (Fin Y.n)} (hσ : IsMor X Y σ) (hτ : IsMor Y Z τ) :
    IsMor X Z fun i => (τ i).subst σ := fun M _ x hx => by
  simpa [Term.realize_subst] using hτ M _ (hσ M x hx)

/-- The identity tuple is a morphism. -/
theorem isMor_id (X : HornCat.{u} L) : IsMor X X fun i => Term.var i :=
  fun _ _ _ hx => hx

instance : Category (HornCat.{u} L) where
  Hom := Arrow
  id X := Arrow.mk' _ (isMor_id X)
  comp f g := ⟨Quotient.map₂ (fun σ τ => ⟨_, isMor_comp σ.2 τ.2⟩)
    (fun σ σ' hσ τ τ' hτ M _ x hx i => by
      simp only [Term.realize_subst]
      rw [show (fun a => (σ.1 a).realize x) = fun a => (σ'.1 a).realize x from
        funext (hσ M x hx)]
      exact hτ M _ (σ'.2 M x hx) i) f.q g.q⟩
  id_comp f := by
    obtain ⟨σ, hσ, rfl⟩ := f.exists_eq_mk'
    exact (Arrow.mk'_eq_mk'_iff _ _).2 fun _ _ _ _ _ => by simp [Term.realize_subst]
  comp_id f := by
    obtain ⟨σ, hσ, rfl⟩ := f.exists_eq_mk'
    exact (Arrow.mk'_eq_mk'_iff _ _).2 fun _ _ _ _ _ => by simp
  assoc f g h := by
    obtain ⟨σ, hσ, rfl⟩ := f.exists_eq_mk'
    obtain ⟨τ, hτ, rfl⟩ := g.exists_eq_mk'
    obtain ⟨ρ, hρ, rfl⟩ := h.exists_eq_mk'
    exact (Arrow.mk'_eq_mk'_iff _ _).2 fun _ _ _ _ _ => by simp [Term.realize_subst]

/-- The morphism of the Horn category given by a tuple of terms. -/
def mor {X Y : HornCat.{u} L} (σ : Fin Y.n → L.Term (Fin X.n)) (hσ : IsMor X Y σ) : X ⟶ Y :=
  Arrow.mk' σ hσ

/-- Every morphism of the Horn category is given by a tuple of terms. -/
theorem exists_eq_mor {X Y : HornCat.{u} L} (f : X ⟶ Y) :
    ∃ (σ : Fin Y.n → L.Term (Fin X.n)) (hσ : IsMor X Y σ), f = mor σ hσ :=
  Arrow.exists_eq_mk' f

/-- Equality of morphisms of the Horn category. -/
theorem mor_eq_mor_iff {X Y : HornCat.{u} L} {σ τ : Fin Y.n → L.Term (Fin X.n)}
    (hσ : IsMor X Y σ) (hτ : IsMor X Y τ) :
    mor σ hσ = mor τ hτ ↔ ∀ (M : Type (max u₁ u₂ u)) [L.Structure M]
      (x : Fin X.n → M), X.Holds x → ∀ i, (σ i).realize x = (τ i).realize x :=
  Arrow.mk'_eq_mk'_iff hσ hτ

/-- Composition in the Horn category is substitution. -/
theorem mor_comp_mor {X Y Z : HornCat.{u} L} {σ : Fin Y.n → L.Term (Fin X.n)}
    {τ : Fin Z.n → L.Term (Fin Y.n)} (hσ : IsMor X Y σ) (hτ : IsMor Y Z τ) :
    mor σ hσ ≫ mor τ hτ = mor (fun i => (τ i).subst σ) (isMor_comp hσ hτ) :=
  rfl

/-- The identity of the Horn category is the tuple of variables. -/
theorem id_eq_mor (X : HornCat.{u} L) : 𝟙 X = mor (fun i => Term.var i) (isMor_id X) :=
  rfl

end HornCat

end LeanPool.ClassifyingTopoi.Syntactic
