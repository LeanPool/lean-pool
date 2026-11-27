/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.BargmannBlockCoordinates

/-!
# Literal statement construction extracted from Gaussian/GaussianBargmannKernel

The moved declarations retain their original text. Later target proofs remain separate.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexConjugate MatrixOrder Matrix.Norms.L2Operator

/-- Reorder mode/quadrature pairs into all q coordinates followed by all p
coordinates, as in Appendix A. -/
def groupedPhysicalCovariance {m : ℕ}
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ :=
  V.submatrix (groupedToMode m) (groupedToMode m)


/-- Literal matrix M_ρ in equation (Bargmann), with real covariance first
put into the source's grouped quadrature order. -/
def bargmannGaussianMatrix {m : ℕ}
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ :=
  bargmannSwap - bargmannDᵀ *
    complexifyMatrix (groupedPhysicalCovariance V + (1 / 2 : ℝ) • 1)⁻¹ * bargmannD


end VacuumBellSeparation.Gaussian
