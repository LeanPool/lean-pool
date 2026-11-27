/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Recovering a genuine derivative from coordinate curves

Differentiability is essential here. Once it is established, the actual
one-dimensional coordinate derivatives identify the full derivative;
no inference from merely existing partial derivatives is used.
-/

@[expose] public section

namespace VacuumBellSeparation

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasFDerivAt_zero_of_coordinate_curves {n : ℕ}
    {f : (Fin n → ℝ) → F} (hf : DifferentiableAt ℝ f 0)
    (L : (Fin n → ℝ) →L[ℝ] F)
    (h : ∀ i : Fin n, HasDerivAt (fun t : ℝ => f (Pi.single i t))
      (L (Pi.single i 1)) 0) : HasFDerivAt f L 0 := by
  have hcol (i : Fin n) : fderiv ℝ f 0 (Pi.single i 1) = L (Pi.single i 1) := by
    have hi : HasDerivAt (fun t : ℝ => (Pi.single i t : Fin n → ℝ))
        (Pi.single i (1 : ℝ) : Fin n → ℝ) 0 := by
      simpa using (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℝ) i).hasDerivAt
    have hd : HasFDerivAt f (fderiv ℝ f 0) (Pi.single i (0 : ℝ)) := by
      simpa using hf.hasFDerivAt
    exact (hd.comp_hasDerivAt 0 hi).unique (h i)
  have hL : fderiv ℝ f 0 = L := by
    ext x
    have hx : x = ∑ i : Fin n, x i • Pi.single i (1 : ℝ) := by
      ext j
      simp [Pi.single_apply]
    rw [hx, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul, map_smul, hcol]
  simpa only [hL] using hf.hasFDerivAt

end VacuumBellSeparation
