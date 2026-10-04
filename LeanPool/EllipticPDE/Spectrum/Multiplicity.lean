/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Spectrum.Variational
public import Mathlib.Analysis.InnerProductSpace.Spectrum


/-!
# Positivity and finite multiplicity of the Dirichlet eigenvalues

The spectral theorem `EllipticPdes.Sobolev.solOp_spectral` produces the eigenspaces and says
nothing about where the eigenvalues sit or how large the eigenspaces are. Both follow from what
is already at hand.

Positivity is the Rayleigh bound: `principalEigenvalue_le_of_weak_eigen` places every weak
eigenvalue above `λ₁`, and `principalEigenvalue_pos` places `λ₁` above the coercivity constant.
Finite multiplicity is the compactness of the solution operator, through Mathlib's
`ContinuousLinearMap.finite_dimensional_eigenspace`, which the Rellich embedding supplies.

## Main declarations

* `EllipticPdes.Sobolev.weak_eigenvalue_pos`: every weak Dirichlet eigenvalue is positive.
* `EllipticPdes.Sobolev.solOp_finiteDimensional_eigenspace`: each eigenspace at a nonzero
  eigenvalue of the solution operator is finite dimensional.
* `EllipticPdes.Sobolev.dirichlet_eigenvalue_pos_of_bounded` and
  `EllipticPdes.Sobolev.dirichlet_finiteDimensional_eigenspace_of_bounded`: the two at `-Δ` on a
  bounded domain, with boundedness the only hypothesis beyond the eigenpair.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §6.5.1, Theorem 1.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

open EllipticPdes.Analysis

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} {B : H01 Ω →L[ℝ] H01 Ω →L[ℝ] ℝ}

/-- **Every weak Dirichlet eigenvalue is positive.** A nonzero weak eigenfunction has eigenvalue
at least `λ₁`, and `λ₁` exceeds the coercivity constant. -/
theorem weak_eigenvalue_pos (hco : IsCoercive B) (hne : ∃ V : H01 Ω, embL2 Ω V ≠ 0)
    {lam : ℝ} {U : H01 Ω} (hU : U ≠ 0)
    (heig : ∀ V : H01 Ω, B U V = lam * ⟪embL2 Ω U, embL2 Ω V⟫) : 0 < lam :=
  lt_of_lt_of_le (principalEigenvalue_pos hco hne)
    (principalEigenvalue_le_of_weak_eigen hco hU heig)

/-- **Finite multiplicity of the eigenvalues.** The eigenspace of the solution operator at a
nonzero eigenvalue is finite dimensional, the operator being compact. -/
theorem solOp_finiteDimensional_eigenspace (hco : IsCoercive B)
    (hRellich : IsCompactOperator (embL2 Ω)) {μ : ℝ} (hμ : μ ≠ 0) :
    FiniteDimensional ℝ (Module.End.eigenspace (solOp B hco : Module.End ℝ (L2D Ω)) μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace (solOp_isCompact hco hRellich) μ hμ

/-- **Positivity at `-Δ` on a bounded domain**, with the Poincaré inequality supplying
coercivity. -/
theorem dirichlet_eigenvalue_pos_of_bounded {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hΩb : Bornology.IsBounded Ω) (hne : ∃ V : H01 Ω, embL2 Ω V ≠ 0)
    {lam : ℝ} {U : H01 Ω} (hU : U ≠ 0)
    (heig : ∀ V : H01 Ω, laplaceBilin Ω U V = lam * ⟪embL2 Ω U, embL2 Ω V⟫) : 0 < lam :=
  weak_eigenvalue_pos (EllipticPdes.Poincare.laplaceBilin_coercive_of_bounded hΩb) hne hU heig

/-- **Finite multiplicity at `-Δ` on a bounded measurable domain.** -/
theorem dirichlet_finiteDimensional_eigenspace_of_bounded {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) {μ : ℝ} (hμ : μ ≠ 0) :
    FiniteDimensional ℝ (Module.End.eigenspace
      (solOp (laplaceBilin Ω) (EllipticPdes.Poincare.laplaceBilin_coercive_of_bounded hΩb)
        : Module.End ℝ (L2D Ω)) μ) :=
  solOp_finiteDimensional_eigenspace _ (embL2_isCompact hΩm hΩb) hμ

end EllipticPdes.Sobolev
