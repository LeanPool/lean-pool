/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ComplexSpacetime

/-!
# Explicit rank algebra at the canonical contour preimage

In the free shell coordinates (z0,z1,z3), the selected five Lorentz
directions and the radial p2 direction give this real six-dimensional
linear map. Its inverse is explicit, even when the time component A
vanishes. No submersion theorem is assumed here.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- Linear map for the reference contour tangent linear, of type `(Fin 6 → ℝ) →ₗ[ℝ] (Fin 3 → ℂ)
where toFun x`. -/
noncomputable def referenceContourTangentLinear (A B C D E : ℝ) :
    (Fin 6 → ℝ) →ₗ[ℝ] (Fin 3 → ℂ) where
  toFun x := ![((B * x 1 + D * x 5 : ℝ) : ℂ) + Complex.I * (C * x 0 : ℝ),
    ((A * x 0 - B * x 2 : ℝ) : ℂ) + Complex.I * (E * x 5 : ℝ),
    ((B * x 4 : ℝ) : ℂ) + Complex.I * (C * x 3 : ℝ)]
  map_add' x y := by
    ext i
    fin_cases i <;> simp [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul] <;> ring
  map_smul' a x := by
    ext i
    fin_cases i <;> simp [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.real_smul] <;> ring

/-- Reference contour tangent inverse. -/
noncomputable def referenceContourTangentInverse (A B C D E : ℝ)
    (z : Fin 3 → ℂ) : Fin 6 → ℝ :=
  ![(z 0).im / C, ((z 0).re - D * ((z 1).im / E)) / B,
    (A * ((z 0).im / C) - (z 1).re) / B,
    (z 2).im / C, (z 2).re / B, (z 1).im / E]

theorem referenceContourTangent_left_inverse (A B C D E : ℝ)
    (hB : B ≠ 0) (hC : C ≠ 0) (hE : E ≠ 0) :
    Function.LeftInverse (referenceContourTangentInverse A B C D E)
      (referenceContourTangentLinear A B C D E) := by
  intro x
  ext i
  fin_cases i <;>
    simp [referenceContourTangentInverse, referenceContourTangentLinear,
      Complex.mul_re, Complex.mul_im, hB, hC, hE]

theorem referenceContourTangent_right_inverse (A B C D E : ℝ)
    (hB : B ≠ 0) (hC : C ≠ 0) (hE : E ≠ 0) :
    Function.RightInverse (referenceContourTangentInverse A B C D E)
      (referenceContourTangentLinear A B C D E) := by
  intro z
  ext i
  fin_cases i <;> apply Complex.ext <;>
    simp [referenceContourTangentInverse, referenceContourTangentLinear,
      Complex.mul_re, Complex.mul_im] <;>
    field_simp <;> ring

/-- Reference contour tangent equivalence of type `(Fin 6 → ℝ) ≃L[ℝ] (Fin 3 → ℂ)`. -/
noncomputable def referenceContourTangentEquiv (A B C D E : ℝ)
    (hB : B ≠ 0) (hC : C ≠ 0) (hE : E ≠ 0) :
    (Fin 6 → ℝ) ≃L[ℝ] (Fin 3 → ℂ) :=
  ({ referenceContourTangentLinear A B C D E with
    invFun := referenceContourTangentInverse A B C D E
    left_inv := referenceContourTangent_left_inverse A B C D E hB hC hE
    right_inv := referenceContourTangent_right_inverse A B C D E hB hC hE } :
    (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℂ)).toContinuousLinearEquiv

/-- At the canonical contour preimage all three denominators stay nonzero,
including normalized mass zero and cos(theta)=0. -/
theorem canonicalContourTangent_bijective (ω B θ : ℝ)
    (hω : 0 < ω) (hB : 0 < B) (hθ : 0 < Real.sin θ) :
    Function.Bijective (referenceContourTangentLinear
      (ω * Real.cos θ) B (ω * Real.sin θ)
      (B / ω * Real.cos θ) (B / ω * Real.sin θ)) :=
  (referenceContourTangentEquiv (ω * Real.cos θ) B (ω * Real.sin θ)
    (B / ω * Real.cos θ) (B / ω * Real.sin θ)
    hB.ne' (mul_pos hω hθ).ne' (mul_pos (div_pos hB hω) hθ).ne').bijective

end VacuumBellSeparation
