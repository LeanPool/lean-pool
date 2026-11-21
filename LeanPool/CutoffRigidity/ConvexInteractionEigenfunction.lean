/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.ClassicalEigenspace
public import LeanPool.CutoffRigidity.ConvexInteraction

/-!
# The genuine L² coordinate-sum eigenfunction for diagonal interactions

Section 3.5 differentiates translation invariance and exhibits the sum of
coordinates as an eigenfunction. Here its actual Gibbs L² membership and
nonzero classical eigenvector are proved, rather than assumed. Identifying
the full self-adjoint spectral gap additionally needs its spectral theory.
-/

public section

namespace CutoffRigidity

open MeasureTheory

variable {d : ℕ} {ρ : ℝ} {W : EuclideanSpace ℝ (Fin d) → ℝ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "V" => (fun y : E => ρ / 2 * ‖y‖ ^ 2 + W y)

/-- Squared norm of the diagonal direction used by the paper. -/
theorem norm_sq_diagonalDirection (d : ℕ) : ‖diagonalDirection d‖ ^ 2 = (d : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp [diagonalDirection]

/-- The coordinate sum belongs to actual Gibbs L²; its pointwise PDE and
normalization are not substitutes for an integrability proof. -/
theorem coordinateSum_memLp_gibbs (hW : Differentiable ℝ W) (hρ : 0 < ρ)
    (hinv : ∀ x : E, ∀ u : ℝ, W (x + u • diagonalDirection d) = W x)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    MemLp (coordinateSum : E → ℝ) 2 (gibbsMeasure volume V) := by
  have hV : Differentiable ℝ V :=
    fun x => (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (ρ / 2)).differentiableAt).add
      (hW x)
  have heigen : ∀ x : E,
      langevinDifferentialOperator V (fun y => inner ℝ (diagonalDirection d) y + 0) x =
        -ρ * (inner ℝ (diagonalDirection d) x + 0) := by
    simpa only [add_zero, inner_diagonalDirection] using
      (fun x => langevinDifferentialOperator_coordinateSum (hW x) (hinv x))
  simpa only [add_zero, inner_diagonalDirection] using
    affine_eigenfunction_memLp_all V hV (diagonalDirection d) 0 ρ hρ heigen hprob

/-- The written coordinate-sum eigenfunction has exactly the predicted
second moment, including its dependence on dimension. -/
theorem coordinateSum_second_moment_gibbs (hW : Differentiable ℝ W) (hρ : 0 < ρ)
    (hinv : ∀ x : E, ∀ u : ℝ, W (x + u • diagonalDirection d) = W x)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    (∫ x, coordinateSum x ^ 2 ∂gibbsMeasure volume V) = (d : ℝ) / ρ := by
  have hV : Differentiable ℝ V :=
    fun x => (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (ρ / 2)).differentiableAt).add
      (hW x)
  have heigen : ∀ x : E,
      langevinDifferentialOperator V (fun y => inner ℝ (diagonalDirection d) y + 0) x =
        -ρ * (inner ℝ (diagonalDirection d) x + 0) := by
    simpa only [add_zero, inner_diagonalDirection] using
      (fun x => langevinDifferentialOperator_coordinateSum (hW x) (hinv x))
  simpa only [add_zero, inner_diagonalDirection, norm_sq_diagonalDirection] using
    affine_eigenfunction_second_moment_all V hV (diagonalDirection d) 0 ρ hρ heigen hprob

/-- In positive dimension the displayed function supplies an actual nonzero
classical L² eigenvector. No arbitrary representative is evaluated. -/
theorem exists_nonzero_classical_eigenvector_of_diagonal_invariance
    (hd : 0 < d) (hW : ContDiff ℝ 2 W) (hρ : 0 < ρ)
    (hinv : ∀ x : E, ∀ u : ℝ, W (x + u • diagonalDirection d) = W x)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    ∃ u : classicalL2Eigenspace V ρ, u ≠ 0 := by
  have hm := coordinateSum_memLp_gibbs (hW.differentiable (by norm_num)) hρ hinv hprob
  have hsum : ContDiff ℝ 2 (coordinateSum : E → ℝ) := by
    have heq : (coordinateSum : E → ℝ) = innerSL ℝ (diagonalDirection d) :=
      funext (fun x => (inner_diagonalDirection x).symm)
    rw [heq]
    exact (innerSL ℝ (diagonalDirection d)).contDiff
  let u : classicalL2Eigenspace V ρ := ⟨hm.toLp coordinateSum, coordinateSum,
    hsum,
    (fun x => langevinDifferentialOperator_coordinateSum
      (hW.differentiable (by norm_num) x) (hinv x)), hm.coeFn_toLp.symm⟩
  refine ⟨u, ?_⟩
  intro hu
  have hae : (coordinateSum : E → ℝ) =ᵐ[gibbsMeasure volume V] 0 := by
    have hv : hm.toLp coordinateSum = 0 := congrArg Subtype.val hu
    exact hm.coeFn_toLp.symm.trans (by simpa only [hv] using
      (Lp.coeFn_zero ℝ 2 (gibbsMeasure volume V) :
        (0 : E →₂[gibbsMeasure volume V] ℝ) =ᵐ[gibbsMeasure volume V] (fun _ => 0)))
  have hzero : (∫ x, coordinateSum x ^ 2 ∂gibbsMeasure volume V) = 0 := by
    calc
      _ = ∫ _ : E, (0 : ℝ) ∂gibbsMeasure volume V :=
        integral_congr_ae (by
          filter_upwards [hae] with x hx
          change coordinateSum x = 0 at hx
          simp only [hx, zero_pow (by norm_num : (2 : ℕ) ≠ 0)])
      _ = 0 := integral_zero _ _
  rw [coordinateSum_second_moment_gibbs (hW.differentiable (by norm_num)) hρ hinv hprob] at hzero
  have : (0 : ℝ) < (d : ℝ) / ρ := div_pos (by exact_mod_cast hd) hρ
  linarith

/-- In the curved setting the actual classical eigenspace at the quadratic
rate is nonempty and finite dimensional. This supplies the positive rank
needed to choose an eigen-direction in the cutoff bounds. -/
theorem classicalL2Eigenspace_finrank_pos_of_diagonal_invariance
    (hd : 0 < d) (hW : ContDiff ℝ 2 W) (hρ : 0 < ρ)
    (hinv : ∀ x : E, ∀ u : ℝ, W (x + u • diagonalDirection d) = W x)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    0 < Module.finrank ℝ (classicalL2Eigenspace V ρ) := by
  have hV : ContDiff ℝ 2 V :=
    (contDiff_const.mul (contDiff_norm_sq ℝ)).add hW
  have := classicalL2Eigenspace_finiteDimensional hV ρ hρ hHess
  exact Module.finrank_pos_iff_exists_ne_zero.mpr
    (exists_nonzero_classical_eigenvector_of_diagonal_invariance hd hW hρ hinv hprob)

end CutoffRigidity
