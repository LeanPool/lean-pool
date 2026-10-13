/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.UnitCubeMultiscale.EllipticityLocality

/-!
# WellDefinedness

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-! # Well-definedness of origin-cube lower multiscale ellipticity -/

namespace Algsuperdiff.Section24.UnitCubeMultiscale.Lambda

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory

variable {d : ℕ}

/-- The unique-value proof used by the frozen origin-cube `lambda` anchor. -/
theorem existsUnique
    (s : ℝ) (q : Book.Ch02.MultiscaleExponent)
    (a : CoeffOn (cubeDomain (originCube d 0))) :
    ∃! value : ℝ, ∀ F : TriadicCoeffFamily d,
      CoeffOn.AEEq (F.coeffOn (originCube d 0)) a →
        value = Book.Ch02.lambdaSq (originCube d 0) s q F := by
  let F₀ := Classical.choose
    (Algsuperdiff.Section24.UnitCubeMultiscale.exists_compatibleTriadicCoeffFamily a)
  have hF₀ : CoeffOn.AEEq (F₀.coeffOn (originCube d 0)) a :=
    Classical.choose_spec
      (Algsuperdiff.Section24.UnitCubeMultiscale.exists_compatibleTriadicCoeffFamily a)
  refine ⟨Book.Ch02.lambdaSq (originCube d 0) s q F₀, ?_, ?_⟩
  · intro F hF
    exact Algsuperdiff.Section24.UnitCubeMultiscale.lambdaSq_eq_of_root_aeeq
      a F₀ F hF₀ hF s q
  · intro value hvalue
    exact hvalue F₀ hF₀

end Algsuperdiff.Section24.UnitCubeMultiscale.Lambda
