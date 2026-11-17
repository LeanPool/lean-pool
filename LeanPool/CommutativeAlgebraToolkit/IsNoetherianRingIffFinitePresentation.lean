/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Shrink

/-!
# Noetherian rings and finitely presented modules

A ring is Noetherian if and only if every finitely generated module over it is finitely
presented. One direction is `Module.finitePresentation_of_finite`; for the other, a finitely
presented cyclic module `R ⧸ I` forces `I` to be finitely generated.

## Main statements

* `isNoetherianRing_iff_forall_finitePresentation`: `R` is Noetherian iff every finitely
  generated `R`-module (in any universe in which `R` is small) is finitely presented.
-/

public section

universe v in
variable (R : Type*) [Ring R] in
/-- A ring `R` is Noetherian if and only if every finitely generated `R`-module is finitely
presented. It suffices to consider modules in any universe in which `R` is small. -/
theorem isNoetherianRing_iff_forall_finitePresentation [Small.{v} R] :
    IsNoetherianRing R ↔ ∀ (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
      Module.FinitePresentation R M := by
  refine ⟨fun _ M _ _ _ ↦ Module.finitePresentation_of_finite R M, fun h ↦ ?_⟩
  refine (isNoetherianRing_iff_ideal_fg R).2 fun I ↦ ?_
  let e := Shrink.linearEquiv.{v} R (R ⧸ I)
  have := Module.Finite.equiv e.symm
  have := h (Shrink.{v} (R ⧸ I))
  have := Module.FinitePresentation.of_equiv e
  have hI := Module.FinitePresentation.fg_ker I.mkQ I.mkQ_surjective
  rw [Submodule.ker_mkQ] at hI
  exact hI
