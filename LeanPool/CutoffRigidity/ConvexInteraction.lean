/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Tactic

/-!
# Translation-invariant interactions

This file formalizes the directional differentiation step in the proof of
Theorem `thm_bg_convex_inter` (Section 3.5) of `cutcur-lean.tex`.
Differentiating the constant function `u ↦ W (x + u • v)` gives
`fderiv ℝ W x v = 0`, hence `⟪gradient W x, v⟫ = 0`.
It then computes the coordinate-sum gradient and Laplacian and proves the
pointwise differential equation `L h = -ρ h` for the stated potential.
This is an analytic ingredient, not a proof of the spectral-gap theorem.
-/

public section

namespace CutoffRigidity

/-- The derivative of a differentiable interaction vanishes in a direction
along which that interaction is invariant. The proof differentiates the
constant restriction to the affine line, as in Section 3.5 of the paper. -/
theorem fderiv_apply_eq_zero_of_translation_invariant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : E → ℝ} {x v : E} (hW : DifferentiableAt ℝ W x)
    (hinv : ∀ u : ℝ, W (x + u • v) = W x) :
    fderiv ℝ W x v = 0 := by
  have hline : HasDerivAt (fun u : ℝ => x + u • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hchain : HasDerivAt (fun u : ℝ => W (x + u • v))
      (fderiv ℝ W x v) 0 := by
    exact hW.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hconst : (fun u : ℝ => W (x + u • v)) = fun _ => W x := funext hinv
  rw [hconst] at hchain
  exact hchain.unique (hasDerivAt_const (0 : ℝ) (W x))

/-- The interaction gradient is orthogonal to any direction of translation
invariance. This is the `∇W · (1,…,1) = 0` step of Section 3.5. -/
theorem inner_gradient_eq_zero_of_translation_invariant
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {W : E → ℝ} {x v : E} (hW : DifferentiableAt ℝ W x)
    (hinv : ∀ u : ℝ, W (x + u • v) = W x) :
    inner ℝ (gradient W x) v = 0 := by
  rw [inner_gradient_left]
  exact fderiv_apply_eq_zero_of_translation_invariant hW hinv

/-- The component sum of the actual Euclidean gradient vanishes when the
interaction is invariant in direction `(1,…,1)`. This is the particular
direction used for the coordinate-sum eigenfunction in Section 3.5. -/
theorem sum_gradient_eq_zero_of_diagonal_translation_invariant
    {d : ℕ} {W : EuclideanSpace ℝ (Fin d) → ℝ}
    {x : EuclideanSpace ℝ (Fin d)} (hW : DifferentiableAt ℝ W x)
    (hinv : ∀ u : ℝ,
      W (x + u • WithLp.toLp 2 (fun _ : Fin d => (1 : ℝ))) = W x) :
    ∑ i : Fin d, gradient W x i = 0 := by
  have h := inner_gradient_eq_zero_of_translation_invariant hW hinv
  rw [PiLp.inner_apply] at h
  simpa only [Real.inner_apply, mul_one] using h

/-- The sum of Euclidean coordinates, used in Section 3.5. -/
@[expose] noncomputable def coordinateSum {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i : Fin d, x i

/-- The all-ones Euclidean vector. -/
@[expose] def diagonalDirection (d : ℕ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun _ : Fin d => (1 : ℝ))

theorem inner_diagonalDirection {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (diagonalDirection d) x = coordinateSum x := by
  rw [PiLp.inner_apply]
  simp only [diagonalDirection, Real.inner_apply, one_mul, coordinateSum]

/-- The coordinate sum is linear, so its derivative is the same linear functional
at every point. -/
theorem fderiv_coordinateSum {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ coordinateSum x = innerSL ℝ (diagonalDirection d) := by
  have heq : (coordinateSum : EuclideanSpace ℝ (Fin d) → ℝ) =
      innerSL ℝ (diagonalDirection d) := by
    funext y
    exact (inner_diagonalDirection y).symm
  rw [heq]
  exact (innerSL ℝ (diagonalDirection d)).fderiv

theorem gradient_coordinateSum {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    gradient coordinateSum x = diagonalDirection d := by
  apply ext_inner_right ℝ
  intro y
  rw [inner_gradient_left, fderiv_coordinateSum]
  rfl

/-- The Euclidean Laplacian as the trace of the second Fréchet derivative
in the standard orthonormal coordinate directions. -/
@[expose] noncomputable def euclideanLaplacian {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i : Fin d, fderiv ℝ
    (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)

/-- The pointwise differential expression from the Langevin generator.
No assertion about its self-adjoint `L²` realization is made by this definition. -/
@[expose] noncomputable def langevinDifferentialOperator {d : ℕ}
    (V f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  euclideanLaplacian f x - inner ℝ (gradient V x) (gradient f x)

theorem euclideanLaplacian_coordinateSum {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    euclideanLaplacian coordinateSum x = 0 := by
  simp only [euclideanLaplacian, fderiv_coordinateSum, fderiv_const_apply,
    zero_apply, Finset.sum_const_zero]

/-- The exact pointwise generator computation in Section 3.5: the sum of
coordinates solves `L h = -ρ h` when the interaction is translation invariant
in the diagonal direction. This does not assert `L²` domain membership or
identify the spectral gap. -/
theorem langevinDifferentialOperator_coordinateSum {d : ℕ} {ρ : ℝ}
    {W : EuclideanSpace ℝ (Fin d) → ℝ} {x : EuclideanSpace ℝ (Fin d)}
    (hW : DifferentiableAt ℝ W x)
    (hinv : ∀ u : ℝ, W (x + u • diagonalDirection d) = W x) :
    langevinDifferentialOperator (fun y => ρ / 2 * ‖y‖ ^ 2 + W y) coordinateSum x =
      -ρ * coordinateSum x := by
  have hnorm := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.differentiableAt
  have hquad := hnorm.const_mul (ρ / 2)
  have hdir := fderiv_apply_eq_zero_of_translation_invariant hW hinv
  rw [langevinDifferentialOperator, euclideanLaplacian_coordinateSum,
    gradient_coordinateSum, inner_gradient_left, fderiv_fun_add hquad hW,
    fderiv_const_mul hnorm, fderiv_norm_sq_apply]
  simp only [add_apply, smul_apply, smul_eq_mul,
    hdir, add_zero, zero_sub]
  rw [show innerSL ℝ x (diagonalDirection d) = coordinateSum x by
    change inner ℝ x (diagonalDirection d) = coordinateSum x
    rw [real_inner_comm, inner_diagonalDirection]]
  ring

end CutoffRigidity
