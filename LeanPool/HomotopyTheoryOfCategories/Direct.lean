/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.AlgebraicTopology.Reedy.Basic
public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Order.Interval.Finset.Basic

/-!
# Direct and inverse categories

A category is *direct* (`IsDirect`) when the relation `DirectRel C` ("there is a non-identity
morphism `X ⟶ Y`") is well-founded, and *inverse* (`IsInverse`) when its opposite is direct.
We relate these notions to Mathlib's `HomotopicalAlgebra.ReedyStructure`: a *direct Reedy
structure* is a `ReedyStructure (identities C) ⊤ α` (Riehl–Verity, *The theory and practice of
Reedy categories*, TAC 2014). We prove:

* `IsDirect.eq_id_of_endo` and `IsDirect.skeletal`: a direct category has no non-identity
  endomorphisms and is skeletal;
* `nonempty_reedyStructure_nat_iff`: `C` has an `ℕ`-valued direct Reedy structure iff it is
  direct with every rank `IsDirect.rank` finite;
* `ReedyStructure.exists_directPart` and `ReedyStructure.exists_inversePart`: the degree-raising
  (resp. degree-lowering) wide subcategory of a Reedy category is direct (resp. inverse), with the
  same degree;
* `isDirect_iff_wellFoundedLT` and `exists_reedyStructure_card_Iio`: a partial order is direct iff
  `<` is well-founded, and has the degree `x ↦ #{y | y < x}` when its lower sets are finite.

The equivalence between direct categories and ordinal-valued direct Reedy structures (roadmap
7.2) and the direct Reedy structure of the semi-simplex category (roadmap 8.4) are already in the
pool, in `CategoryTheoryToolkit` (`HomotopicalAlgebra.ReedyStructure.ofWellFounded`,
`HomotopicalAlgebra.ReedyStructure.wellFounded` and `SemiSimplexCategory.reedyStructure`), and are
not repeated here.

Everything rests on two constructors, `reedyStructureOfDirect` and `reedyStructureOfInverse`,
for which the unique factorization is automatic. Products of Reedy structures and the further
examples of roadmap Layer 8 are not formalised.

This is Layers 7 and 8 of the roadmap *Homotopy theory of small categories*.
-/

@[expose] public section

universe w v u

namespace LeanPool.HomotopyTheoryOfCategories

open CategoryTheory HomotopicalAlgebra Opposite MorphismProperty

/-- A morphism is an identity, in the sense of `MorphismProperty.identities`, iff it is an
`eqToHom`. -/
lemma identities_iff {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) :
    identities C f ↔ ∃ h : X = Y, f = eqToHom h := by
  constructor
  · rintro ⟨⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨_⟩

/-- **Layer 7.1.** The relation on objects "there is a non-identity morphism `X ⟶ Y`". -/
def DirectRel (C : Type u) [Category.{v} C] (X Y : C) : Prop :=
  ∃ f : X ⟶ Y, ¬ MorphismProperty.identities C f

/-- **Layer 7.1.** A category is *direct* if there is no infinite descending chain of
non-identity morphisms `⋯ ⟶ X₂ ⟶ X₁ ⟶ X₀`, that is, `DirectRel C` is well-founded. -/
class IsDirect (C : Type u) [Category.{v} C] : Prop where
  /-- `DirectRel C` is well-founded. -/
  wellFounded : WellFounded (DirectRel C)

/-- **Layer 7.1.** A category is *inverse* if its opposite is direct. -/
class IsInverse (C : Type u) [Category.{v} C] : Prop where
  /-- The opposite category is direct. -/
  isDirect_op : IsDirect Cᵒᵖ

section Constructors

variable {C : Type u} [Category.{v} C]
  {α : Type w} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]

/-- **Layer 7.2.** A direct Reedy structure from a degree that strictly increases along every
non-identity morphism; the factorization of `f` is `𝟙 ≫ f`. -/
def reedyStructureOfDirect (deg : C → α)
    (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), ¬ identities C f → deg X < deg Y) :
    ReedyStructure (identities C) ⊤ α where
  deg := deg
  lt₁ f hf hf' := absurd hf hf'
  lt₂ f _ hf' := h f hf'
  nonempty_unique {X Y} f := ⟨
    { default := ⟨X, 𝟙 X, f, by simp, ⟨X⟩, trivial⟩
      uniq := by
        rintro ⟨Z, i, p, fac, hi, -⟩
        obtain ⟨⟩ := hi
        obtain rfl : p = f := by simpa using fac
        rfl }⟩

/-- **Layer 7.4.** An inverse Reedy structure from a degree that strictly decreases along every
non-identity morphism; the factorization of `f` is `f ≫ 𝟙`. -/
def reedyStructureOfInverse (deg : C → α)
    (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), ¬ identities C f → deg Y < deg X) :
    ReedyStructure ⊤ (identities C) α where
  deg := deg
  lt₁ f _ hf' := h f hf'
  lt₂ f hf hf' := absurd hf hf'
  nonempty_unique {X Y} f := ⟨
    { default := ⟨Y, f, 𝟙 Y, by simp, trivial, ⟨Y⟩⟩
      uniq := by
        rintro ⟨Z, i, p, fac, -, hp⟩
        obtain ⟨⟩ := hp
        obtain rfl : i = f := by simpa using fac
        rfl }⟩

/-- The degree of a direct Reedy structure strictly increases along non-identity morphisms. -/
lemma deg_lt_of_directRel (r : ReedyStructure (identities C) ⊤ α) {X Y : C}
    (h : DirectRel C X Y) : r.deg X < r.deg Y :=
  h.elim fun f hf ↦ r.lt₂ f trivial hf

end Constructors

namespace IsDirect

variable {C : Type u} [Category.{v} C] [IsDirect C]

/-- **Layer 7.2.** The canonical degree of an object of a direct category: its rank for
`DirectRel C`. -/
noncomputable def rank (X : C) : Ordinal.{u} :=
  haveI : WellFounded (DirectRel C) := IsDirect.wellFounded
  WellFounded.rank (DirectRel C) X

/-- The rank strictly increases along non-identity morphisms. -/
lemma rank_lt {X Y : C} (h : DirectRel C X Y) : rank X < rank Y :=
  haveI : WellFounded (DirectRel C) := IsDirect.wellFounded
  WellFounded.rank_lt_of_rel h

/-- The rank of `X` is the supremum of the successors of the ranks of the `Y` with a
non-identity morphism `Y ⟶ X`. -/
lemma rank_eq (X : C) : rank X = ⨆ Y : { Y // DirectRel C Y X }, Order.succ (rank Y.1) :=
  haveI : WellFounded (DirectRel C) := IsDirect.wellFounded
  WellFounded.rank_eq (DirectRel C) X

/-- **Layer 7.1.** In a direct category every endomorphism is the identity. -/
theorem eq_id_of_endo {X : C} (f : X ⟶ X) : f = 𝟙 X := by
  by_contra hf
  refine (rank_lt ⟨f, fun h ↦ hf ?_⟩).false
  obtain ⟨-, rfl⟩ := (identities_iff f).1 h
  rfl

/-- **Layer 7.1.** A direct category is skeletal. -/
theorem skeletal : Skeletal C := by
  rintro X Y ⟨e⟩
  by_contra hXY
  have hne : ∀ {A B : C} (f : A ⟶ B), A ≠ B → ¬ identities C f := fun f h hf => h (by
    obtain ⟨⟩ := hf
    rfl)
  exact (rank_lt ⟨e.hom, hne e.hom hXY⟩).asymm (rank_lt ⟨e.inv, hne e.inv (Ne.symm hXY)⟩)

end IsDirect

variable (C : Type u) [Category.{v} C]

/-- A direct Reedy structure with values in any well-ordered `α` makes `C` direct. -/
lemma isDirect_of_reedyStructure {α : Type w} [LinearOrder α] [OrderBot α] [SuccOrder α]
    [WellFoundedLT α]
    (r : HomotopicalAlgebra.ReedyStructure (MorphismProperty.identities C) ⊤ α) :
    IsDirect C :=
  ⟨Subrelation.wf (fun h ↦ deg_lt_of_directRel r h) (InvImage.wf r.deg wellFounded_lt)⟩

/-- The rank is bounded by the degree of any direct Reedy structure with values in `ℕ`. -/
lemma IsDirect.rank_le_deg [IsDirect C]
    (r : HomotopicalAlgebra.ReedyStructure (MorphismProperty.identities C) ⊤ ℕ) (X : C) :
    IsDirect.rank X ≤ r.deg X := by
  refine WellFounded.induction (C := fun X ↦ IsDirect.rank X ≤ (r.deg X : Ordinal))
    IsDirect.wellFounded X fun X ih ↦ ?_
  rw [IsDirect.rank_eq]
  refine Ordinal.iSup_le fun Y ↦ Order.succ_le_of_lt ((ih Y.1 Y.2).trans_lt ?_)
  exact_mod_cast deg_lt_of_directRel r Y.2

/-- **Layer 7.3.** A category has an `ℕ`-valued direct Reedy structure exactly when it is direct
with every rank finite. -/
theorem nonempty_reedyStructure_nat_iff :
    Nonempty (HomotopicalAlgebra.ReedyStructure (MorphismProperty.identities C) ⊤ ℕ) ↔
      ∃ _ : IsDirect C, ∀ X : C, IsDirect.rank X < Ordinal.omega0 := by
  constructor
  · rintro ⟨r⟩
    have := isDirect_of_reedyStructure C r
    exact ⟨this, fun X ↦ (IsDirect.rank_le_deg C r X).trans_lt (Ordinal.natCast_lt_omega0 _)⟩
  · rintro ⟨_, h⟩
    choose n hn using fun X ↦ Ordinal.lt_omega0.1 (h X)
    refine ⟨reedyStructureOfDirect n fun X Y f hf ↦ ?_⟩
    have := IsDirect.rank_lt ⟨f, hf⟩
    rw [hn X, hn Y] at this
    exact_mod_cast this

/-- A morphism of a wide subcategory whose underlying morphism is an identity is an identity. -/
lemma identities_of_identities_hom {P : MorphismProperty C} [P.IsMultiplicative]
    {X Y : WideSubcategory P} (f : X ⟶ Y) (hf : identities C f.hom) : identities _ f := by
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  obtain ⟨h, hf⟩ := (identities_iff _).1 hf
  dsimp at h
  subst h
  obtain rfl : f = 𝟙 _ := WideSubcategory.hom_ext P hf
  exact ⟨_⟩

namespace ReedyStructure

variable {C} {W₁ W₂ : MorphismProperty C} [W₁.IsMultiplicative] [W₂.IsMultiplicative]
  {α : Type w} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]

/-- **Layer 7.4.** The degree-raising part of a Reedy structure is direct, with the same degree.
-/
theorem exists_directPart (r : ReedyStructure W₁ W₂ α) :
    ∃ r' : ReedyStructure (MorphismProperty.identities (WideSubcategory W₂)) ⊤ α,
      ∀ X, r'.deg X = r.deg X.obj :=
  ⟨reedyStructureOfDirect (fun X ↦ r.deg X.obj) (fun _ _ f hf ↦
    r.lt₂ f.hom f.property fun h ↦ hf (identities_of_identities_hom C f h)), fun _ ↦ rfl⟩

/-- **Layer 7.4.** The degree-lowering part of a Reedy structure is inverse, with the same
degree. -/
theorem exists_inversePart (r : ReedyStructure W₁ W₂ α) :
    ∃ r' : ReedyStructure ⊤ (MorphismProperty.identities (WideSubcategory W₁)) α,
      ∀ X, r'.deg X = r.deg X.obj :=
  ⟨reedyStructureOfInverse (fun X ↦ r.deg X.obj) (fun _ _ f hf ↦
    r.lt₁ f.hom f.property fun h ↦ hf (identities_of_identities_hom C f h)), fun _ ↦ rfl⟩

end ReedyStructure

/-- In a partial order, there is a non-identity morphism `x ⟶ y` iff `x < y`. -/
lemma directRel_iff_lt {P : Type u} [PartialOrder P] (x y : P) : DirectRel P x y ↔ x < y := by
  constructor
  · rintro ⟨f, hf⟩
    refine lt_of_le_of_ne (leOfHom f) fun h ↦ hf ?_
    subst h
    obtain rfl : f = 𝟙 x := Subsingleton.elim _ _
    exact ⟨_⟩
  · intro h
    refine ⟨homOfLE h.le, fun hf ↦ h.ne ?_⟩
    exact ((identities_iff _).1 hf).1

/-- **Layer 8.1.** A partial order is direct iff `<` is well-founded. -/
theorem isDirect_iff_wellFoundedLT (P : Type u) [PartialOrder P] :
    IsDirect P ↔ WellFoundedLT P := by
  have h : DirectRel P = (· < ·) := by
    ext x y
    exact directRel_iff_lt x y
  exact ⟨fun hP ↦ (h ▸ hP.wellFounded : WellFounded (· < ·)),
    fun hP ↦ ⟨h ▸ (hP : WellFounded (· < ·))⟩⟩

/-- **Layer 8.1.** A partial order with finite lower sets has an `ℕ`-valued direct
Reedy structure with degree `x ↦ #{y | y < x}`. -/
theorem exists_reedyStructure_card_Iio (P : Type u) [PartialOrder P]
    [LocallyFiniteOrderBot P] :
    ∃ r : HomotopicalAlgebra.ReedyStructure (MorphismProperty.identities P) ⊤ ℕ,
      ∀ x, r.deg x = (Finset.Iio x).card := by
  refine ⟨reedyStructureOfDirect (fun x ↦ (Finset.Iio x).card) fun x y f hf ↦ ?_, fun _ ↦ rfl⟩
  have hxy : x < y := (directRel_iff_lt x y).1 ⟨f, hf⟩
  refine Finset.card_lt_card ⟨Finset.Iio_subset_Iio hxy.le, fun h ↦ ?_⟩
  exact lt_irrefl x (Finset.mem_Iio.1 (h (Finset.mem_Iio.2 hxy)))

end LeanPool.HomotopyTheoryOfCategories
