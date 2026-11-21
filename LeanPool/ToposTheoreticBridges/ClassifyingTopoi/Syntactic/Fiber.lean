/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Horn
public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.CategoryTheory.Limits.FinallySmall

/-!
# Structures on types as points of the Horn site

An `L`-structure `M` on a type of the universe `max u₁ u₂ u` gives a functor
`HornCat.fiber M : HornCat L ⥤ Type _` sending a Horn formula in context to the set of
assignments satisfying it, and a morphism (a tuple of terms) to the substitution. Its category
of elements is cofiltered (`HornCat.isCofiltered_fiber`): two elements have a common refinement
in the concatenated context, and two parallel morphisms are equalised by adding the equations
between their terms. Hence `M` is a point of the site `(HornCat L, ⊥)` (`HornCat.point M`), whose
fiber functor on presheaves preserves finite limits and colimits; homomorphisms of structures
give morphisms of points (`HornCat.pointHom`).

## Main definitions

* `LeanPool.ClassifyingTopoi.Syntactic.HornCat.fiber`, `HornCat.fiberMap`;
* `LeanPool.ClassifyingTopoi.Syntactic.HornCat.point`, `HornCat.pointHom`.
-/

@[expose] public section

universe u u₁ u₂

namespace LeanPool.ClassifyingTopoi.Syntactic

open FirstOrder FirstOrder.Language CategoryTheory

variable {L : Language.{u₁, u₂}}

namespace HornCat

/-- The substitution of a morphism of the Horn category, on assignments of a structure. -/
def subst {X Y : HornCat.{u} L} (f : X ⟶ Y) (M : Type (max u₁ u₂ u)) [L.Structure M] :
    {x : Fin X.n → M // X.Holds x} → {y : Fin Y.n → M // Y.Holds y} :=
  Quotient.lift (fun σ x => ⟨fun i => (σ.1 i).realize x.1, σ.2 M x.1 x.2⟩)
    (fun _ _ (h : ∀ (N : Type (max u₁ u₂ u)) [L.Structure N] (x : Fin X.n → N), X.Holds x →
        ∀ _, _ = _) => funext fun x => Subtype.ext (funext (h M x.1 x.2))) (f : Arrow X Y).q

/-- The substitution of the morphism given by a tuple of terms. -/
@[simp]
theorem subst_mor {X Y : HornCat.{u} L} (σ : Fin Y.n → L.Term (Fin X.n)) (hσ : IsMor X Y σ)
    (M : Type (max u₁ u₂ u)) [L.Structure M] (x : {x : Fin X.n → M // X.Holds x}) :
    subst (mor σ hσ) M x = ⟨fun i => (σ i).realize x.1, hσ M x.1 x.2⟩ :=
  rfl

variable (M : Type (max u₁ u₂ u)) [L.Structure M]

/-- The fiber functor of a structure: a Horn formula in context goes to the set of assignments
satisfying it, a tuple of terms to the substitution. -/
def fiber : HornCat.{u} L ⥤ Type (max u₁ u₂ u) where
  obj X := {x : Fin X.n → M // X.Holds x}
  map f := TypeCat.ofHom (subst f M)
  map_id X := by
    ext x
    rfl
  map_comp f g := by
    obtain ⟨σ, hσ, rfl⟩ := exists_eq_mor f
    obtain ⟨τ, hτ, rfl⟩ := exists_eq_mor g
    ext x
    simp [mor_comp_mor, Term.realize_subst]

/-- The fiber functor on a morphism given by a tuple of terms. -/
@[simp]
theorem fiber_map_mor {X Y : HornCat.{u} L} (σ : Fin Y.n → L.Term (Fin X.n)) (hσ : IsMor X Y σ)
    (x : (fiber M).obj X) :
    (fiber M).map (mor σ hσ) x = ⟨fun i => (σ i).realize x.1, hσ M x.1 x.2⟩ :=
  rfl

/-- The concatenation of two Horn formulas in context, in the concatenated context. -/
def append (X Y : HornCat.{u} L) : HornCat.{u} L :=
  ⟨X.n + Y.n, X.atoms.map (Atom.relabel (Fin.castAdd Y.n)) ++
    Y.atoms.map (Atom.relabel (Fin.natAdd X.n))⟩

/-- Satisfaction of a concatenation. -/
theorem holds_append {N : Type*} [L.Structure N] (X Y : HornCat.{u} L)
    (x : Fin (X.n + Y.n) → N) :
    (append X Y).Holds x ↔ X.Holds (x ∘ Fin.castAdd Y.n) ∧ Y.Holds (x ∘ Fin.natAdd X.n) := by
  constructor
  · intro h
    exact ⟨fun a ha => (Atom.realize_relabel _ _ _).1
        (h _ (List.mem_append_left _ (List.mem_map_of_mem ha))),
      fun a ha => (Atom.realize_relabel _ _ _).1
        (h _ (List.mem_append_right _ (List.mem_map_of_mem ha)))⟩
  · rintro ⟨h₁, h₂⟩ a ha
    rcases List.mem_append.1 ha with ha | ha <;> obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    · exact (Atom.realize_relabel _ _ _).2 (h₁ b hb)
    · exact (Atom.realize_relabel _ _ _).2 (h₂ b hb)

/-- The first projection out of a concatenation. -/
def appendFst (X Y : HornCat.{u} L) : append X Y ⟶ X :=
  mor (fun i => Term.var (Fin.castAdd Y.n i)) fun _ _ x hx => ((holds_append X Y x).1 hx).1

/-- The second projection out of a concatenation. -/
def appendSnd (X Y : HornCat.{u} L) : append X Y ⟶ Y :=
  mor (fun i => Term.var (Fin.natAdd X.n i)) fun _ _ x hx => ((holds_append X Y x).1 hx).2

/-- A Horn formula in context with the equations between two tuples of terms added. -/
def addEqs (X : HornCat.{u} L) {m : ℕ} (σ τ : Fin m → L.Term (Fin X.n)) : HornCat.{u} L :=
  ⟨X.n, X.atoms ++ List.ofFn fun i => Atom.equal (σ i) (τ i)⟩

/-- Satisfaction of a Horn formula with added equations. -/
theorem holds_addEqs {N : Type*} [L.Structure N] (X : HornCat.{u} L) {m : ℕ}
    (σ τ : Fin m → L.Term (Fin X.n)) (x : Fin X.n → N) :
    (addEqs X σ τ).Holds x ↔ X.Holds x ∧ ∀ i, (σ i).realize x = (τ i).realize x := by
  constructor
  · intro h
    exact ⟨fun a ha => h a (List.mem_append_left _ ha),
      fun i => h _ (List.mem_append_right _ (List.mem_ofFn.2 ⟨i, rfl⟩))⟩
  · rintro ⟨h₁, h₂⟩ a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact h₁ a ha
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
      exact h₂ i

/-- The tuple of variables is a morphism out of a Horn formula with added equations. -/
theorem isMor_addEqsι (X : HornCat.{u} L) {m : ℕ} (σ τ : Fin m → L.Term (Fin X.n)) :
    IsMor (addEqs X σ τ) X fun i => Term.var i :=
  fun _ _ x hx => ((holds_addEqs X σ τ x).1 hx).1

/-- The inclusion of a Horn formula with added equations. -/
def addEqsι (X : HornCat.{u} L) {m : ℕ} (σ τ : Fin m → L.Term (Fin X.n)) : addEqs X σ τ ⟶ X :=
  mor (fun i => Term.var i) (isMor_addEqsι X σ τ)

/-- The category of elements of the fiber functor of a structure is cofiltered. -/
instance isCofiltered_fiber : IsCofiltered (fiber.{u} (L := L) M).Elements where
  nonempty := ⟨(fiber M).elementsMk (top 0) ⟨Fin.elim0, holds_top _⟩⟩
  cone_objs x y := by
    refine ⟨(fiber M).elementsMk (append x.obj y.obj)
      ⟨Fin.append x.val.1 y.val.1, (holds_append _ _ _).2 ⟨?_, ?_⟩⟩,
      Functor.Elements.homMk (appendFst _ _) ?_, Functor.Elements.homMk (appendSnd _ _) ?_,
      trivial⟩
    · simpa [Function.comp_def] using x.val.2
    · simpa [Function.comp_def] using y.val.2
    · exact Subtype.ext (funext fun i => Fin.append_left _ _ _)
    · exact Subtype.ext (funext fun i => Fin.append_right _ _ _)
  cone_maps {x y} f g := by
    obtain ⟨σ, hσ, hf⟩ := exists_eq_mor f.hom
    obtain ⟨τ, hτ, hg⟩ := exists_eq_mor g.hom
    have hfx := f.map_val
    have hgx := g.map_val
    rw [hf, fiber_map_mor] at hfx
    rw [hg, fiber_map_mor] at hgx
    have heq : ∀ i, (σ i).realize x.val.1 = (τ i).realize x.val.1 := fun i => by
      rw [← hgx] at hfx
      exact congrFun (congrArg Subtype.val hfx) i
    refine ⟨(fiber M).elementsMk (addEqs x.obj σ τ) ⟨x.val.1, (holds_addEqs _ _ _ _).2
      ⟨x.val.2, heq⟩⟩, Functor.Elements.homMk (addEqsι _ _ _) rfl, ?_⟩
    ext
    change addEqsι _ _ _ ≫ f.hom = addEqsι _ _ _ ≫ g.hom
    rw [hf, hg]
    exact (mor_eq_mor_iff (isMor_comp (isMor_addEqsι _ _ _) hσ)
      (isMor_comp (isMor_addEqsι _ _ _) hτ)).2 fun N _ z hz i => by
      rw [Term.realize_subst, Term.realize_subst]
      exact ((holds_addEqs _ _ _ _).1 hz).2 i

/-- A structure on a type is a point of the site `(HornCat L, ⊥)`, with fiber functor
`HornCat.fiber M`. -/
noncomputable def point :
    GrothendieckTopology.Point.{max u₁ u₂ u} (⊥ : GrothendieckTopology (HornCat.{u} L)) where
  fiber := fiber M
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective {X} R hR x := by
    obtain rfl : R = ⊤ := by simpa using hR
    exact ⟨X, 𝟙 X, by simp, x, by simp⟩

variable {M} {N : Type (max u₁ u₂ u)} [L.Structure N]

/-- A homomorphism of structures induces a morphism of fiber functors. -/
def fiberMap (h : M →[L] N) : fiber.{u} (L := L) M ⟶ fiber N where
  app X := TypeCat.ofHom fun x => ⟨h ∘ x.1, holds_hom h X x.2⟩
  naturality X Y f := by
    obtain ⟨σ, hσ, rfl⟩ := exists_eq_mor f
    ext x
    exact Subtype.ext (funext fun i => (HomClass.realize_term h).symm)

/-- A homomorphism of structures `M →[L] N` induces a morphism of points `point N ⟶ point M`. -/
def pointHom (h : M →[L] N) : point.{u} (L := L) N ⟶ point M :=
  ⟨fiberMap h⟩

/-- The morphism of points of the identity homomorphism. -/
@[simp]
theorem pointHom_id : pointHom (Hom.id L M) = 𝟙 (point.{u} (L := L) M) := by
  ext
  rfl

/-- The morphism of points of a composite homomorphism. -/
@[simp]
theorem pointHom_comp {P : Type (max u₁ u₂ u)} [L.Structure P] (h : M →[L] N) (k : N →[L] P) :
    pointHom (k.comp h) = pointHom k ≫ pointHom.{u} (L := L) h := by
  ext
  rfl

end HornCat

end LeanPool.ClassifyingTopoi.Syntactic
