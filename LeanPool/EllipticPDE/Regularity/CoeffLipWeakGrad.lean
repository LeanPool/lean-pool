/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.Local.Reduction
public import Mathlib.Analysis.Calculus.Rademacher


/-!
# Weak gradient of a `W^{1,infinity}` coefficient

`IsLipCoeff` is the hypothesis the interior estimate reads, and the cutoff reduction that
takes the estimate from `H_0^1(Omega)` to `H^1(Omega)` reads one thing more: a weak gradient
of each coefficient entry, essentially bounded, which `CoeffWeakGrad` bundles. A `C^1`
coefficient supplies it through its classical partials (`IsC1Coeff.coeffWeakGrad`) and a
`W^{k+1,infinity}` family through its first order (`IsWkInftyCoeff.coeffWeakGrad`). This file
supplies it from the Lipschitz estimate alone, which is what Guo, *Partial Differential
Equations I and II* (Course Lecture Notes), Theorem VIII.2.2 (p. 63) and Gilbarg-Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Theorem 8.8 (p. 179) ask of the
leading coefficients.

## The argument

Rademacher's theorem (`LipschitzWith.ae_differentiableAt`) gives a derivative almost
everywhere, and `fderiv` names it: the total `fderiv` of Mathlib is the derivative where one
exists and zero elsewhere, so `coeffDa A l i j` below is measurable (`measurable_fderiv`) and
bounded by the Lipschitz constant wherever the derivative exists
(`norm_fderiv_le_of_lipschitz`).

That it is the weak derivative is the difference quotient identity
`∫ a(x) (φ(x - h e_l) - φ(x))/h = ∫ ((a(x + h e_l) - a(x))/h) φ(x)`,
exact for every `h ≠ 0` by translation invariance of the volume, taken to the limit along
`h = 1/(n+1)`. On the left the quotient of `φ` converges uniformly to `-∂_l φ` and is
supported in one compact set for every `h ≤ 1`; on the right the quotient of `a` is bounded
by `A₁` and converges almost everywhere by Rademacher. Dominated convergence on each side
gives `∫ a ∂_l φ = -∫ (da) φ`.

## Main declarations

* `IsLipCoeff.lipschitzWith`: the estimate as a `LipschitzWith` statement.
* `coeffDa`: the chosen representative of `∂_l a_{ij}`.
* `measurable_coeffDa`, `IsLipCoeff.abs_da_le`: its measurability and its bound, the
  bound being pointwise rather than essential, since `fderiv` is zero off the differentiability
  set.

## What this file does not yet supply

`HasWeakPartial l (fun x => A.a x i j) (coeffDa A l i j)`, and with it
`IsLipCoeff.coeffWeakGrad`. The route is the one described above: the difference quotient
identity by `measurePreserving_translate` and `MeasurePreserving.integral_comp`, then
`tendsto_integral_of_dominated_convergence` on each side, the almost-everywhere convergence
of the quotient of `a` coming from `LipschitzWith.ae_differentiableAt` through
`hasDerivAt_iff_tendsto_slope`. Until it is proved, the cutoff reduction of
`interior_H2_estimate_W12` reads a `C¹` bundle and the `H^1` statements of the interior
theory ask `C¹` of the principal coefficients where Guo VIII.2.2 and Gilbarg-Trudinger 8.8
ask `W^{1,∞}`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology NNReal

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ} {A : EllipticCoeff d}

/-- The Lipschitz estimate of `IsLipCoeff` as a `LipschitzWith` statement, which is what
Rademacher's theorem and the bound on the derivative are stated for. -/
theorem IsLipCoeff.lipschitzWith (hA : IsLipCoeff A) (i j : Fin d) :
    LipschitzWith (Real.toNNReal hA.A1) (fun y => A.a y i j) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h := hA.lip i j x y
  rw [Real.dist_eq, Real.coe_toNNReal _ hA.A1_nonneg, ← dist_eq_norm] at *
  exact h

/-- The chosen representative of the weak partial `∂_l a_{ij}`: the total `fderiv` applied to
the `l`-th basis vector, which is the classical partial wherever the entry is differentiable
and zero on the null set where it is not. It is written for the coefficient rather than for a
bundle over it, no hypothesis being needed to name it. -/
def coeffDa (A : EllipticCoeff d) (l i j : Fin d) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x => fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single l (1 : ℝ))

/-- `coeffDa` is measurable, the total `fderiv` being measurable and evaluation at a vector
continuous. No regularity of the entry enters. -/
theorem measurable_coeffDa (A : EllipticCoeff d) (l i j : Fin d) :
    Measurable (coeffDa A l i j) :=
  ((ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single l (1 : ℝ))).continuous.measurable).comp
    (measurable_fderiv ℝ (fun y => A.a y i j))

/-- `coeffDa` is bounded by the Lipschitz constant everywhere: where the entry is differentiable
this is the converse mean value inequality, and elsewhere `fderiv` is zero. -/
theorem IsLipCoeff.abs_da_le (hA : IsLipCoeff A) (l i j : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : |coeffDa A l i j x| ≤ hA.A1 := by
  have hop : ‖fderiv ℝ (fun y => A.a y i j) x‖ ≤ (Real.toNNReal hA.A1 : ℝ) :=
    norm_fderiv_le_of_lipschitz ℝ (hA.lipschitzWith i j)
  have hle := (fderiv ℝ (fun y => A.a y i j) x).le_opNorm
    (EuclideanSpace.single l (1 : ℝ))
  rw [PiLp.norm_single, norm_one, mul_one] at hle
  have : ‖coeffDa A l i j x‖ ≤ (Real.toNNReal hA.A1 : ℝ) := le_trans hle hop
  rwa [Real.norm_eq_abs, Real.coe_toNNReal _ hA.A1_nonneg] at this

end EllipticPdes.Regularity
