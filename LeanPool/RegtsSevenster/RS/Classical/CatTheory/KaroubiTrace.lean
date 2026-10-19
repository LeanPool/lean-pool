/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.CatTheory.KaroubiLinear
public import LeanPool.RegtsSevenster.RS.Classical.Algebra.TraceCriterion
public import LeanPool.RegtsSevenster.RS.Common.NilpotentMap

/-!
# The trace criterion on a Karoubi corner

Nilpotence transports along the underlying-morphism map. Cyclicity
sandwiches arbitrary ambient tests into the corner, so a
nondegenerate trace that kills nilpotents proves semisimplicity
of every corner endomorphism algebra.
-/

@[expose] public section

namespace RS

open CategoryTheory CategoryTheory.Idempotents

/-- Nilpotent corner endomorphisms are nilpotent in the base category. -/
theorem karoubiEnd_isNilpotent {C : Type*} [Category C]
    [Preadditive C] {P : Karoubi C} {x : End P}
    (hx : IsNilpotent x) : IsNilpotent (show End P.X from .of x.asHom.f) :=
  isNilpotent_map_of_mul_zero (fun y : End P => (show End P.X from .of y.asHom.f))
    rfl (fun _ _ => rfl) hx

/-- A finite-dimensional ambient trace criterion restricts to a
Karoubi corner. -/
theorem karoubiEnd_isSemisimpleRing_of_trace {C : Type*} [Category C]
    [Preadditive C] [Linear ℂ C] (P : Karoubi C)
    [FiniteDimensional ℂ (End P.X)] (τ : End P.X →ₗ[ℂ] ℂ)
    (hnil : ∀ x : End P.X, IsNilpotent x → τ x = 0)
    (hcyc : ∀ a b : End P.X, τ (End.of (a.asHom ≫ b.asHom)) = τ (End.of (b.asHom ≫ a.asHom)))
    (hnd : ∀ a : End P.X, (∀ b : End P.X, τ (End.of (a.asHom ≫ b.asHom)) = 0) → a = 0) :
    IsSemisimpleRing (End P) := by
  let L : End P →ₗ[ℂ] End P.X :=
    End.linearEquiv.symm.toLinearMap ∘ₗ karoubiHomLinearMap P P ∘ₗ
      End.linearEquiv.toLinearMap
  have : FiniteDimensional ℂ (End P) :=
    FiniteDimensional.of_injective L
      (fun _ _ h => End.ext (Karoubi.Hom.ext (congrArg End.asHom h)))
  refine isSemisimpleRing_of_trace (τ.comp L)
    (fun x hx => hnil (.of x.asHom.f) (karoubiEnd_isNilpotent hx)) (fun a ha => ?_)
  apply End.ext
  apply Karoubi.hom_ext
  change a.asHom.f = 0
  suffices hz : (End.of a.asHom.f : End P.X) = 0 from congrArg End.asHom hz
  apply hnd
  intro b
  have hb : P.p ≫ (P.p ≫ b.asHom ≫ P.p) ≫ P.p = P.p ≫ b.asHom ≫ P.p := by
    simp only [Category.assoc]
    rw [show P.p ≫ P.p ≫ b.asHom ≫ P.p ≫ P.p =
      (P.p ≫ P.p) ≫ b.asHom ≫ (P.p ≫ P.p) from by
        simp only [Category.assoc]]
    rw [P.idem]
  have key := ha (End.of ⟨P.p ≫ b.asHom ≫ P.p, hb⟩)
  have hred : a.asHom.f ≫ (P.p ≫ b.asHom ≫ P.p) = (a.asHom.f ≫ b.asHom) ≫ P.p := by
    rw [show a.asHom.f ≫ (P.p ≫ b.asHom ≫ P.p) =
      (a.asHom.f ≫ P.p) ≫ b.asHom ≫ P.p from by simp only [Category.assoc]]
    rw [Karoubi.comp_p]
    simp only [Category.assoc]
  calc τ (End.of (a.asHom.f ≫ b.asHom)) =
        τ (End.of (P.p ≫ (a.asHom.f ≫ b.asHom))) := by
        rw [show P.p ≫ (a.asHom.f ≫ b.asHom) = (P.p ≫ a.asHom.f) ≫ b.asHom from by
          simp only [Category.assoc], Karoubi.p_comp]
    _ = τ (End.of ((a.asHom.f ≫ b.asHom) ≫ P.p)) := hcyc (.of P.p) (.of (a.asHom.f ≫ b.asHom))
    _ = τ (End.of (a.asHom.f ≫ (P.p ≫ b.asHom ≫ P.p))) := by rw [hred]
    _ = 0 := key

end RS
