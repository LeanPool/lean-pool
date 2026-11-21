/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module
public import LeanPool.CutoffRigidity.ConvexInteractionSpectralGap
public import LeanPool.CutoffRigidity.GibbsFirstEigenspace
public import LeanPool.CutoffRigidity.AffineEigenfunctionSplitting

/-! # The complete convex diagonal-interaction theorem

The source interaction assumptions construct the actual first-eigenclass,
exact spectral gap, full curvature-gap condition, and genuine orthogonal
Gaussian probability-product factorization. The normalized endpoint also
constructs the actual probability law from the finite positive partition
integral. No eigenclass, splitting, or projected-law premise is used.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The diagonal direction divided by its norm. In positive dimension this is a unit vector. -/
@[expose] noncomputable def unitDiagonalDirection (d : ℕ) : EuclideanSpace ℝ (Fin d) :=
  ‖diagonalDirection d‖⁻¹ • diagonalDirection d

theorem diagonalDirection_ne_zero (hd : 0 < d) : diagonalDirection d ≠ 0 := by
  intro hz
  have hh := norm_sq_diagonalDirection d
  rw [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hh
  have hp : (0 : ℝ) < d := by exact_mod_cast hd
  linarith

theorem norm_unitDiagonalDirection (hd : 0 < d) : ‖unitDiagonalDirection d‖ = 1 := by
  simp only [unitDiagonalDirection, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (norm_nonneg _)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (diagonalDirection_ne_zero hd))

/-- All three conclusions of the source convex-interaction theorem,
expressed with actual operator eigenspaces and a full probability product. -/
structure ConvexInteractionConclusions
    (ρ : ℝ) (W : E → ℝ)
    (hV : ContDiff ℝ 2 (fun x : E => ρ / 2 * ‖x‖ ^ 2 + W x))
    (hp : IsProbabilityMeasure (gibbsMeasure volume (fun x : E => ρ / 2 * ‖x‖ ^ 2 + W x))) : Prop
      where
  spectral_gap : gibbsSpectralGap hV hp = ρ
  coordinate_sum_first_eigenfunction :
    ∃ u : gibbsFirstEigenspace hV hp,
      (u : E →₂[gibbsMeasure volume (fun x => ρ / 2 * ‖x‖ ^ 2 + W x)] ℝ) =ᵐ[
        gibbsMeasure volume (fun x => ρ / 2 * ‖x‖ ^ 2 + W x)] coordinateSum ∧ u ≠ 0
  hessian_bound : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤
    fderiv ℝ (fderiv ℝ (fun x => ρ / 2 * ‖x‖ ^ 2 + W x)) x z z
  curvature_gap : ∀ x z : E, gibbsSpectralGap hV hp * ‖z‖ ^ 2 ≤
    fderiv ℝ (fderiv ℝ (fun x => ρ / 2 * ‖x‖ ^ 2 + W x)) x z z
  gaussian_factor :
    ∃ A : E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × (Submodule.span ℝ {unitDiagonalDirection d})ᗮ),
      A.symm (WithLp.toLp 2 (1, (0 : (Submodule.span ℝ {unitDiagonalDirection d})ᗮ))) =
        unitDiagonalDirection d ∧
      ∃ η : Measure (Submodule.span ℝ {unitDiagonalDirection d})ᗮ, IsProbabilityMeasure η ∧
        (gibbsMeasure volume (fun x : E => ρ / 2 * ‖x‖ ^ 2 + W x)).map (fun x => (A x).ofLp) =
          (gaussianReal 0 (ρ⁻¹).toNNReal).prod η

/-- Complete general normalized-measure version of the written theorem.
C² regularity of V is derived from C² W and the actual quadratic term. -/
theorem convexInteraction_theorem
    {ρ : ℝ} {W : E → ℝ} (hd : 0 < d) (hW : ContDiff ℝ 2 W)
    (hconv : ConvexOn ℝ Set.univ W) (hρ : 0 < ρ)
    (hinv : ∀ x : E, ∀ t : ℝ, W (x + t • diagonalDirection d) = W x)
    (hp : IsProbabilityMeasure (gibbsMeasure volume (fun x : E => ρ / 2 * ‖x‖ ^ 2 + W x))) :
    ∃ hV : ContDiff ℝ 2 (fun x : E => ρ / 2 * ‖x‖ ^ 2 + W x),
      ConvexInteractionConclusions ρ W hV hp := by
  let V := fun x : E => ρ / 2 * ‖x‖ ^ 2 + W x
  have hV : ContDiff ℝ 2 V := (contDiff_const.mul (contDiff_norm_sq ℝ)).add hW
  have hgap := convexInteraction_spectralGap_eq hd hW hconv hρ hinv hp hV
  have hHess := hessian_quadratic_add_convex_lower hW hconv ρ
  refine ⟨hV, ⟨hgap, ?_, hHess, ?_, ?_⟩⟩
  · let := hp
    have hm := coordinateSum_memLp_gibbs (hW.differentiable (by norm_num)) hρ hinv hp
    have hsum : ContDiff ℝ 2 (coordinateSum : E → ℝ) := by
      have heq : (coordinateSum : E → ℝ) = innerSL ℝ (diagonalDirection d) :=
        funext (fun x => (inner_diagonalDirection x).symm)
      rw [heq]
      exact (innerSL ℝ (diagonalDirection d)).contDiff
    have heigen (x : E) : langevinDifferentialOperator V coordinateSum x = -ρ * coordinateSum x :=
      langevinDifferentialOperator_coordinateSum (hW.differentiable (by norm_num) x) (hinv x)
    have hc : hm.toLp coordinateSum ∈ classicalL2Eigenspace V ρ :=
      ⟨coordinateSum, hsum, heigen, hm.coeFn_toLp.symm⟩
    have hOp := classicalL2Eigenspace_le_gibbsOperatorEigenspace hV hp ρ hρ.le hc
    have hFirst : hm.toLp coordinateSum ∈ gibbsFirstEigenspace hV hp := by
      change hm.toLp coordinateSum ∈ gibbsOperatorEigenspace hV hp (gibbsSpectralGap hV hp)
      rw [hgap]
      exact hOp
    have hnorm : ‖hm.toLp coordinateSum‖ ^ 2 = (d : ℝ) / ρ := by
      rw [norm_toLp_sq hm, coordinateSum_second_moment_gibbs (hW.differentiable
        (by norm_num)) hρ hinv hp]
    refine ⟨⟨hm.toLp coordinateSum, hFirst⟩, hm.coeFn_toLp, ?_⟩
    intro hz
    have hz' : hm.toLp coordinateSum = 0 := congrArg Subtype.val hz
    rw [hz', norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hnorm
    have hp0 : (0 : ℝ) < (d : ℝ) / ρ := div_pos (by exact_mod_cast hd) hρ
    linarith
  · simpa only [hgap] using hHess
  · have hEigen (x : E) :
        langevinDifferentialOperator V (fun y => inner ℝ (diagonalDirection d) y + 0) x =
          -ρ * (inner ℝ (diagonalDirection d) x + 0) := by
      simpa only [add_zero, inner_diagonalDirection] using
        langevinDifferentialOperator_coordinateSum (hW.differentiable (by norm_num) x) (hinv x)
    obtain ⟨A, hA, η, hη, hfactor⟩ := affine_eigenfunction_gibbs_factor V
      (hV.differentiable (by norm_num)) (diagonalDirection d) (diagonalDirection_ne_zero hd) 0 ρ hρ
      hEigen hp
    refine ⟨A, hA, η, hη, ?_⟩
    convert! hfactor using 1
    simp only [zero_div, zero_smul, add_zero, gibbsMeasure, unitDiagonalDirection, V]
    rfl

/-- Complete source theorem after explicit additive normalization. The
actual probability law, exact spectral gap, first coordinate-sum class,
curvature-gap condition and full Gaussian product factor all follow from
C² convex diagonally invariant W and ρ>0 alone. -/
theorem normalized_convexInteraction_theorem
    {ρ : ℝ} {W : E → ℝ} (hd : 0 < d) (hW : ContDiff ℝ 2 W)
    (hconv : ConvexOn ℝ Set.univ W) (hρ : 0 < ρ)
    (hinv : ∀ x : E, ∀ t : ℝ, W (x + t • diagonalDirection d) = W x) :
    let Z := ∫ x : E, Real.exp (-(ρ / 2 * ‖x‖ ^ 2 + W x))
    let Wn := fun x => W x + Real.log Z
    ∃ (hVn : ContDiff ℝ 2 (fun x : E => ρ / 2 * ‖x‖ ^ 2 + Wn x))
      (hp : IsProbabilityMeasure (gibbsMeasure volume (fun x : E => ρ / 2 * ‖x‖ ^ 2 + Wn x))),
      ConvexInteractionConclusions ρ Wn hVn hp := by
  intro Z Wn
  have hp : IsProbabilityMeasure (gibbsMeasure volume (fun x : E => ρ / 2 * ‖x‖ ^ 2 + Wn x)) := by
    simpa only [Wn, add_assoc] using (convexInteraction_normalized_probability_memLp_two hW hconv ρ
      hρ).1
  obtain ⟨hVn, hResult⟩ := convexInteraction_theorem hd (hW.add contDiff_const)
    (hconv.add_const (Real.log Z)) hρ (fun x t => by rw [hinv x t]) hp
  exact ⟨hVn, hp, hResult⟩

end CutoffRigidity
