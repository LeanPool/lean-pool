/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.CategoryTheory.ConnectedComponents
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import LeanPool.HomotopyTheoryOfCategories.FundamentalGroupoid
import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# Fibrations of groupoids and their exact sequence

A functor `p : E ⥤ B` of groupoids is a fibration (`IsGroupoidFibration`) when it is
star-surjective: every morphism out of `p x` lifts, in the sense of Mathlib's `Functor.IsHomLift`,
to a morphism out of `x` (Brown–Heath–Kamps 1983, §2). For `x : E` and the fibre
`F := p.Fiber (p.obj x)` (Mathlib's `Functor.Fiber`) we prove the exactness of
`1 → Aut_F(x) → Aut_E(x) → Aut_B(p x) → π₀ F → π₀ E → π₀ B`
(Brown–Heath–Kamps 1983, sequence (1.1), after Brown 1970):

* `IsGroupoidFibration.range_mapAut_fiberInclusion`: exactness at `Aut_E(x)`, for every functor
  of groupoids;
* `IsGroupoidFibration.mem_range_mapAut_iff`: exactness at `Aut_B(p x)`;
* `IsGroupoidFibration.mapConnectedComponents_eq_iff`: exactness at `π₀ F`, for every functor of
  groupoids;
* `IsGroupoidFibration.mapConnectedComponents_eq_mk_iff`: exactness at `π₀ E`.

The proofs compose lifts and use that a zigzag in a groupoid, or in the fibre of a functor of
groupoids, composes to a single morphism. The Mayer–Vietoris sequence (roadmap 1.5) is not
formalised.

This is Layer 1.4 of the roadmap *Homotopy theory of small categories*.
-/

@[expose] public section

universe v u

namespace LeanPool.HomotopyTheoryOfCategories

open CategoryTheory

/-- **Layer 1.4.** A fibration of groupoids: a star-surjective functor (Brown–Heath–Kamps 1983,
§2), every morphism out of `p x` lifting to a morphism out of `x`. -/
def IsGroupoidFibration {E B : Type u} [Groupoid.{v} E] [Groupoid.{v} B] (p : E ⥤ B) : Prop :=
  ∀ (x : E) (b : B) (g : p.obj x ⟶ b), ∃ (y : E) (φ : x ⟶ y), p.IsHomLift g φ

namespace IsGroupoidFibration

variable {E B : Type u} [Groupoid.{v} E] [Groupoid.{v} B] {p : E ⥤ B}

/-- A morphism `φ : a ⟶ b` lies over `f : p a ⟶ p b` iff `p.map φ = f`. -/
lemma isHomLift_iff {a b : E} (f : p.obj a ⟶ p.obj b) (φ : a ⟶ b) :
    p.IsHomLift f φ ↔ p.map φ = f :=
  ⟨fun _ ↦ (IsHomLift.eq_of_isHomLift p f φ).symm, fun h ↦ h ▸ inferInstance⟩

/-- In the fibre of a functor of groupoids, objects related by a zigzag are related by a
morphism. -/
lemma nonempty_hom_of_zigzag_fiber {S : B} {y z : p.Fiber S} (h : Zigzag y z) :
    Nonempty (y ⟶ z) := by
  induction h with
  | refl => exact ⟨𝟙 _⟩
  | tail _ hz ih =>
    obtain ⟨f⟩ := ih
    rcases hz with ⟨⟨g⟩⟩ | ⟨⟨g⟩⟩
    · exact ⟨f ≫ g⟩
    · have : p.IsHomLift (𝟙 S) g.1 := g.2
      exact ⟨f ≫ ⟨inv g.1, inferInstance⟩⟩

/-- **Layer 1.4.** Exactness at `Aut_E(x)` of the sequence of a fibration: the automorphisms of
`x` in the fibre `F` over `p x` are those sent to `𝟙` by `p`. This holds for every functor of
groupoids. -/
theorem range_mapAut_fiberInclusion (p : E ⥤ B) (x : E) :
    ((Functor.Fiber.fiberInclusion (p := p) (S := p.obj x)).mapAut ⟨x, rfl⟩).range =
      (p.mapAut x).ker := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    have : p.IsHomLift (𝟙 (p.obj x)) τ.asIso.hom.1 := τ.asIso.hom.2
    refine Aut.ext' ?_
    exact (isHomLift_iff (𝟙 (p.obj x)) τ.asIso.hom.1).1 this
  · intro hσ
    have h : p.map σ.asIso.hom = 𝟙 _ :=
      congrArg (fun e : Aut (p.obj x) ↦ e.asIso.hom) hσ
    have : p.IsHomLift (𝟙 (p.obj x)) σ.asIso.hom := (isHomLift_iff _ _).2 h
    let x' : p.Fiber (p.obj x) := Functor.Fiber.mk (a := x) rfl
    refine ⟨.of
      { hom := (⟨σ.asIso.hom, this⟩ : x' ⟶ x')
        inv := (⟨σ.asIso.inv, IsHomLift.lift_id_inv p (p.obj x) σ.asIso⟩ : x' ⟶ x')
        hom_inv_id := by ext; exact σ.asIso.hom_inv_id
        inv_hom_id := by ext; exact σ.asIso.inv_hom_id }, Aut.ext' rfl⟩

/-- **Layer 1.4.** Exactness at `Aut_B(p x)`: `g` lifts to an automorphism of `x` iff every lift
of `g` out of `x` ends in the component of `x` in the fibre over `p x`. -/
theorem mem_range_mapAut_iff (hp : IsGroupoidFibration p) (x : E) (g : Aut (p.obj x)) :
    g ∈ (p.mapAut x).range ↔ ∀ (y : p.Fiber (p.obj x)) (φ : x ⟶ y.1), p.IsHomLift g.asIso.hom φ →
      (Quotient.mk'' y : ConnectedComponents (p.Fiber (p.obj x))) = Quotient.mk'' ⟨x, rfl⟩ := by
  constructor
  · rintro ⟨σ, rfl⟩ y φ hφ
    have : p.IsHomLift (p.map σ.asIso.hom) φ := hφ
    have h : p.IsHomLift (p.map σ.asIso.inv ≫ p.map σ.asIso.hom) (σ.asIso.inv ≫ φ) :=
      inferInstance
    rw [← p.map_comp, Iso.inv_hom_id, p.map_id] at h
    let x' : p.Fiber (p.obj x) := Functor.Fiber.mk (a := x) rfl
    exact Quotient.sound (Zigzag.of_inv (⟨σ.asIso.inv ≫ φ, h⟩ : x' ⟶ y))
  · intro h
    obtain ⟨y, φ, hφ⟩ := hp x (p.obj x) g.asIso.hom
    let y' : p.Fiber (p.obj x) := ⟨y, IsHomLift.codomain_eq p g.asIso.hom φ⟩
    obtain ⟨m⟩ := nonempty_hom_of_zigzag_fiber (Quotient.exact' (h y' φ hφ)).symm
    have : p.IsHomLift (𝟙 (p.obj x)) m.1 := m.2
    have hσ : p.IsHomLift g.asIso.hom (φ ≫ inv m.1) := inferInstance
    refine ⟨.of (asIso (φ ≫ inv m.1)), Aut.ext' ?_⟩
    exact (isHomLift_iff _ _).1 hσ

/-- **Layer 1.4.** Exactness at `π₀ F`: two objects of the fibre over `p x` lie in one component
of `E` iff one lies in the component of an endpoint of a lift, out of the other, of an
automorphism of `p x` (the fibres of `π₀ F → π₀ E` are the orbits of `Aut_B(p x)`). This holds
for every functor of groupoids. -/
theorem mapConnectedComponents_eq_iff (p : E ⥤ B) (x : E)
    (y y' : p.Fiber (p.obj x)) :
    Functor.Fiber.fiberInclusion.mapConnectedComponents (Quotient.mk'' y) =
        Functor.Fiber.fiberInclusion.mapConnectedComponents (Quotient.mk'' y') ↔
      ∃ (g : p.obj x ⟶ p.obj x) (z : p.Fiber (p.obj x)) (φ : y.1 ⟶ z.1),
        p.IsHomLift g φ ∧
          (Quotient.mk'' z : ConnectedComponents (p.Fiber (p.obj x))) = Quotient.mk'' y' := by
  constructor
  · intro h
    obtain ⟨ψ⟩ : Nonempty (y.1 ⟶ y'.1) := Groupoid.nonempty_hom_of_zigzag (Quotient.exact' h)
    refine ⟨eqToHom y.2.symm ≫ p.map ψ ≫ eqToHom y'.2, y', ψ, ?_, rfl⟩
    exact IsHomLift.of_fac' p _ ψ y.2 y'.2 (by simp)
  · rintro ⟨g, z, φ, -, hz⟩
    have hz' : Zigzag z.1 y'.1 :=
      zigzag_obj_of_zigzag Functor.Fiber.fiberInclusion (Quotient.exact' hz)
    exact Quotient.sound ((Zigzag.of_hom φ).trans hz')

/-- **Layer 1.4.** Exactness at `π₀ E`: a component of `E` lies over the component of `p x` iff it
meets the fibre over `p x`. -/
theorem mapConnectedComponents_eq_mk_iff (hp : IsGroupoidFibration p) (x : E)
    (c : ConnectedComponents E) :
    p.mapConnectedComponents c = Quotient.mk'' (p.obj x) ↔
      c ∈ Set.range
        (Functor.Fiber.fiberInclusion (p := p) (S := p.obj x)).mapConnectedComponents := by
  induction c using Quotient.inductionOn with | h e => ?_
  constructor
  · intro h
    obtain ⟨g⟩ := Groupoid.nonempty_hom_of_zigzag (Quotient.exact' h)
    obtain ⟨y, φ, hφ⟩ := hp e (p.obj x) g
    refine ⟨Quotient.mk'' ⟨y, IsHomLift.codomain_eq p g φ⟩, ?_⟩
    exact Quotient.sound (Zigzag.of_inv φ)
  · rintro ⟨⟨y⟩, hy⟩
    rw [← hy]
    change Quotient.mk'' (p.obj y.1) = Quotient.mk'' (p.obj x)
    rw [y.2]

end IsGroupoidFibration

end LeanPool.HomotopyTheoryOfCategories
