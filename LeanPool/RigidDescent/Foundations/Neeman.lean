/-
Copyright (c) 2026 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import LeanPool.RigidDescent.Foundations.CellularTower
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Neeman's theorem: localizing subcategories containing the generators

Let `T` be compactly generated, with chosen compact generators `G i`
(`CompactlyGenerated.gen`), and let `g` be the family of their shifts `G i⟦n⟧`
(`CompactlyGenerated.shiftedGen`).

* `CellularTower.isIso_hom`: for every `X`, the cellular tower of `Hom(-, X)` with respect to
  `g` has `u∞ : X∞ ⟶ X` an isomorphism. Its cone `C` receives no nonzero maps from any
  `G i⟦n⟧`, because `a ↦ a ≫ u∞` is bijective on maps from every `G i⟦n⟧`; so `C = 0`.
* `prop_of_localizing`: a property of objects that is closed under isomorphisms, triangulated
  and closed under coproducts, and holds for every generator, holds for every object. Indeed
  `X₀` is a coproduct of generators, each `Xₙ₊₁` is a cone of a map between objects with the
  property, and so is the telescope `X∞ ≅ X`.
-/

@[expose] public section

open CategoryTheory Limits Opposite Pretriangulated
open CategoryTheory.Pretriangulated.Opposite

universe v u

namespace RigidDescent

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasShift T ℤ]

namespace CompactlyGenerated

variable (T) [CompactlyGenerated T]

/-- The index type of the chosen compact generators. -/
def GenIndex : Type v := (exists_generators (T := T)).choose

/-- The chosen compact generators. -/
noncomputable def gen : GenIndex T → T := (exists_generators (T := T)).choose_spec.choose

/-- The shifted generators `G i⟦n⟧`. -/
noncomputable def shiftedGen (p : GenIndex T × ℤ) : T := (gen T p.1)⟦p.2⟧

variable {T}

lemma isCompactObj_gen (i : GenIndex T) : IsCompactObj (gen T i) :=
  (exists_generators (T := T)).choose_spec.choose_spec.1 i

/-- The generators detect zero objects. -/
lemma isZero_of_gen (X : T)
    (h : ∀ (i : GenIndex T) (n : ℤ) (f : (gen T i)⟦n⟧ ⟶ X), f = 0) : IsZero X :=
  (exists_generators (T := T)).choose_spec.choose_spec.2 X h

lemma isCompactObj_shiftedGen [∀ n : ℤ, (shiftFunctor T n).Additive] (p : GenIndex T × ℤ) :
    IsCompactObj (shiftedGen T p) :=
  (isCompactObj_gen p.1).shift p.2

end CompactlyGenerated

open CompactlyGenerated

/-- A property of objects is *closed under coproducts* if it holds for `∐ Y` whenever it
holds for every `Y j`, `j : J`, `J : Type v`. -/
def IsClosedUnderCoproducts [HasCoproducts.{v} T] (P : ObjectProperty T) : Prop :=
  ∀ (J : Type v) (Y : J → T), (∀ j, P (Y j)) → P (∐ Y)

omit [Preadditive T] [HasShift T ℤ] in
/-- Closure under coproducts indexed by `v`-small types. -/
lemma IsClosedUnderCoproducts.of_small [HasCoproducts.{v} T] {P : ObjectProperty T}
    [P.IsClosedUnderIsomorphisms] (hP : IsClosedUnderCoproducts P) {J : Type*} [Small.{v} J]
    (Y : J → T) [HasCoproduct Y] (h : ∀ j, P (Y j)) : P (∐ Y) :=
  P.prop_of_iso (Sigma.reindex (equivShrink.{v} J).symm Y) (hP _ _ fun _ => h _)

variable [HasZeroObject T] [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]
  [CompactlyGenerated T]

/-- For a cellular tower of `Hom(-, X)`, the element `u∞` as a map `X∞ ⟶ X`. -/
def CellularTower.hom {X : T} {κ : Type v} {g : κ → T}
    (ct : CellularTower (preadditiveYoneda.obj X) g) : ct.tel.obj ⟶ X :=
  ct.u

/-- For the cellular tower of `Hom(-, X)` with respect to the shifted generators,
`u∞ : X∞ ⟶ X` is an isomorphism. -/
theorem CellularTower.isIso_hom {X : T}
    (ct : CellularTower (preadditiveYoneda.obj X) (shiftedGen T)) : IsIso ct.hom := by
  have inj : ∀ (p : GenIndex T × ℤ) (a : shiftedGen T p ⟶ ct.tel.obj), a ≫ ct.hom = 0 →
      a = 0 := by
    intro p a ha
    apply (ct.bijective p).1
    change a ≫ ct.hom = 0 ≫ ct.hom
    rw [ha, Limits.zero_comp]
  have surj : ∀ (p : GenIndex T × ℤ) (b : shiftedGen T p ⟶ X), ∃ a, a ≫ ct.hom = b :=
    fun p b => (ct.bijective p).2 b
  obtain ⟨C, v, w, hT⟩ := distinguished_cocone_triangle ct.hom
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1 (isZero_of_gen C fun i n f => ?_)
  have hw : f ≫ w = 0 := by
    obtain ⟨y, hy⟩ := (shiftFunctor T (1 : ℤ)).map_surjective
      ((shiftNegShift _ (1 : ℤ)).hom ≫ f ≫ w)
    have hy0 : y ≫ ct.hom = 0 := by
      apply (shiftFunctor T (1 : ℤ)).map_injective
      rw [Functor.map_comp, hy, Functor.map_zero, Category.assoc, Category.assoc]
      have := comp_distTriang_mor_zero₃₁ _ hT
      dsimp at this
      rw [this, Limits.comp_zero, Limits.comp_zero]
    let e : shiftedGen T (i, n + -1) ≅ ((gen T i)⟦n⟧)⟦(-1 : ℤ)⟧ :=
      (shiftFunctorAdd' T n (-1) (n + -1) rfl).app _
    have hy' : y = 0 := by
      rw [← cancel_epi e.hom, Limits.comp_zero]
      exact inj _ _ (by rw [Category.assoc, hy0, Limits.comp_zero])
    rw [hy', Functor.map_zero] at hy
    apply (cancel_epi (shiftNegShift ((gen T i)⟦n⟧) (1 : ℤ)).hom).mp
    rw [Limits.comp_zero]
    exact hy.symm
  obtain ⟨b, rfl⟩ := Triangle.coyoneda_exact₃ _ hT f hw
  obtain ⟨a, rfl⟩ := surj (i, n) b
  have := comp_distTriang_mor_zero₁₂ _ hT
  dsimp at this
  exact (Category.assoc _ _ _).trans ((a ≫= this).trans Limits.comp_zero)

/-- Every object is isomorphic to the telescope of a cellular tower: there is a cellular tower
of `Hom(-, X)` with respect to the shifted generators. -/
lemma CellularTower.nonempty_yoneda (X : T) :
    Nonempty (CellularTower (preadditiveYoneda.obj X) (shiftedGen T)) :=
  CellularTower.nonempty (inferInstanceAs (preadditiveYoneda.obj X).IsHomological)
    (sendsCoproductsToProducts_preadditiveYoneda X) isCompactObj_shiftedGen

/-- **Neeman's theorem.** A property of objects that is closed under isomorphisms, triangulated
and closed under coproducts, and holds for every generator, holds for every object. -/
theorem prop_of_localizing (P : ObjectProperty T) [P.IsClosedUnderIsomorphisms]
    [P.IsTriangulated] (hP : IsClosedUnderCoproducts P) (hG : ∀ i, P (gen T i)) (X : T) :
    P X := by
  obtain ⟨ct⟩ := CellularTower.nonempty_yoneda X
  have hg : ∀ p, P (shiftedGen T p) := fun p => P.le_shift p.2 _ (hG p.1)
  have hX : ∀ n, P (ct.X n) := by
    intro n
    induction n with
    | zero =>
      obtain ⟨J, j, ⟨e⟩⟩ := ct.zero
      exact P.prop_of_iso e.symm (hP J _ fun i => hg (j i))
    | succ n ih =>
      obtain ⟨J, j, f, δ, hT⟩ := ct.succ n
      exact P.ext_of_isTriangulatedClosed₃ _ hT (hP J _ fun i => hg (j i)) ih
  have hX' : P (∐ ct.X) := hP.of_small _ hX
  have hinf : P ct.tel.obj := P.ext_of_isTriangulatedClosed₃ _ ct.tel.distinguished hX' hX'
  have := ct.isIso_hom
  exact P.prop_of_iso (asIso ct.hom) hinf

end RigidDescent
