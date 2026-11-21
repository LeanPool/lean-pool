/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.ConvexInteractionEigenfunction
public import LeanPool.CutoffRigidity.QuadraticLangevinPotential
public import LeanPool.CutoffRigidity.GibbsMoments
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Curvature from the source convex-interaction hypothesis

Convexity is restricted to affine lines. Monotonicity of their actual first
derivative gives nonnegativity of their second derivative, which the chain
rule identifies with the actual Hessian quadratic form. Adding the quadratic
confinement gives the source Bakry--Émery Hessian bound. This does not identify
a self-adjoint spectral gap.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory

private theorem hasDerivAt_translated_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x z : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => x + s • z) z t := by
  simpa only [one_smul] using ((hasDerivAt_id' t).smul_const z).const_add x

private theorem convexOn_translated_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : E → ℝ} (hconv : ConvexOn ℝ univ W) (x z : E) :
    ConvexOn ℝ univ (fun t : ℝ => W (x + t • z)) := by
  have h := hconv.comp_affineMap (AffineMap.lineMap x (x + z))
  simpa only [preimage_univ, Function.comp_def, AffineMap.lineMap_apply_module',
    add_sub_cancel_left, add_comm] using h

private theorem hasDerivAt_fderiv_eval_line_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : E → ℝ} (hW : ContDiff ℝ 2 W) (x z : E) :
    HasDerivAt (fun t : ℝ => fderiv ℝ W (x + t • z) z) (fderiv ℝ (fderiv ℝ W) x z z) 0 := by
  have hdW : Differentiable ℝ (fderiv ℝ W) :=
    (hW.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hcomp := (hdW (x + (0 : ℝ) • z)).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_translated_line x z 0)
  have hchain := hcomp.clm_apply (hasDerivAt_const 0 z)
  simpa only [Function.comp_apply, zero_smul, add_zero, map_zero] using! hchain

/-- A twice continuously differentiable convex function has nonnegative
actual Hessian quadratic form, proved by restricting to affine lines. -/
theorem hessian_nonneg_of_contDiff_convexOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : E → ℝ} (hW : ContDiff ℝ 2 W) (hconv : ConvexOn ℝ univ W) (x z : E) :
    0 ≤ fderiv ℝ (fderiv ℝ W) x z z := by
  let f : ℝ → ℝ := fun t => W (x + t • z)
  have hfd (t : ℝ) : HasDerivAt f (fderiv ℝ W (x + t • z) z) t :=
    (hW.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_translated_line x z t)
  have hconvf : ConvexOn ℝ univ f := convexOn_translated_line hconv x z
  have hm : Monotone (deriv f) :=
    fun s t hst => (hconvf.monotoneOn_deriv (fun t _ => (hfd t).differentiableAt))
      (mem_univ s) (mem_univ t) hst
  have hident : deriv f = fun t => fderiv ℝ W (x + t • z) z := funext (fun t => (hfd t).deriv)
  have hd : HasDerivAt (deriv f) (fderiv ℝ (fderiv ℝ W) x z z) 0 := by
    rw [hident]
    exact hasDerivAt_fderiv_eval_line_zero hW x z
  rw [← hd.deriv]
  exact hm.deriv_nonneg

/-- Adding the quadratic confinement to the actual convex interaction gives
the full Hessian lower bound asserted in Section 3.5. -/
theorem hessian_quadratic_add_convex_lower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {W : E → ℝ} (hW : ContDiff ℝ 2 W) (hconv : ConvexOn ℝ univ W)
    (ρ : ℝ) (x z : E) :
    ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun y => ρ / 2 * ‖y‖ ^ 2 + W y)) x z z := by
  let Q := quadraticLangevinPotential (E := E) ρ
  have hQ : ContDiff ℝ 2 Q := contDiff_quadraticLangevinPotential ρ
  have hderiv : fderiv ℝ (fun y => Q y + W y) =
      fun y => fderiv ℝ Q y + fderiv ℝ W y := by
    funext y
    exact fderiv_add (hQ.differentiable (by norm_num) y) (hW.differentiable (by norm_num) y)
  change ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun y => Q y + W y)) x z z
  rw [hderiv, fderiv_fun_add
    (((hQ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x)
    (((hW.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x)]
  simp only [add_apply]
  have hquad := hessian_quadraticLangevinPotential (E := E) ρ x z
  change fderiv ℝ (fderiv ℝ Q) x z z = _ at hquad
  rw [hquad]
  exact le_add_of_nonneg_right (hessian_nonneg_of_contDiff_convexOn hW hconv x z)

/-- Convexity and positive quadratic confinement imply an actual finite,
strictly positive partition integral; no partition bound is assumed. -/
theorem convexInteraction_partition_finite_positive {d : ℕ}
    {W : EuclideanSpace ℝ (Fin d) → ℝ} (hW : ContDiff ℝ 2 W)
    (hconv : ConvexOn ℝ univ W) (ρ : ℝ) (hρ : 0 < ρ) :
    Integrable (fun x => Real.exp (-(ρ / 2 * ‖x‖ ^ 2 + W x))) volume ∧
      0 < ∫ x, Real.exp (-(ρ / 2 * ‖x‖ ^ 2 + W x)) := by
  have hV : ContDiff ℝ 2 (fun x => ρ / 2 * ‖x‖ ^ 2 + W x) :=
    (contDiff_const.mul (contDiff_norm_sq ℝ)).add hW
  exact gibbs_partition_finite_positive hV ρ hρ (hessian_quadratic_add_convex_lower hW hconv ρ)

/-- The paper's additive normalization constructs a genuine probability
measure with actual finite second moment from convexity. -/
theorem convexInteraction_normalized_probability_memLp_two {d : ℕ}
    {W : EuclideanSpace ℝ (Fin d) → ℝ} (hW : ContDiff ℝ 2 W)
    (hconv : ConvexOn ℝ univ W) (ρ : ℝ) (hρ : 0 < ρ) :
    let V := fun x => ρ / 2 * ‖x‖ ^ 2 + W x
    let Z := ∫ x, Real.exp (-V x)
    IsProbabilityMeasure (gibbsMeasure volume (fun x => V x + Real.log Z)) ∧
      MemLp (fun x : EuclideanSpace ℝ (Fin d) => x) 2
        (gibbsMeasure volume (fun x => V x + Real.log Z)) := by
  have hV : ContDiff ℝ 2 (fun x => ρ / 2 * ‖x‖ ^ 2 + W x) :=
    (contDiff_const.mul (contDiff_norm_sq ℝ)).add hW
  exact normalized_gibbs_probability_memLp_two hV ρ hρ (hessian_quadratic_add_convex_lower hW hconv
    ρ)

/-- The normalized convex interaction has a C² potential and a Gibbs probability law. -/
theorem convexInteraction_normalization {d : ℕ} {W : EuclideanSpace ℝ (Fin d) → ℝ}
    (hW : ContDiff ℝ 2 W) (hconv : ConvexOn ℝ univ W) (ρ : ℝ) (hρ : 0 < ρ) :
    let Z := ∫ x, Real.exp (-(ρ / 2 * ‖x‖ ^ 2 + W x))
    let Vn := fun x => ρ / 2 * ‖x‖ ^ 2 + (W x + Real.log Z)
    ContDiff ℝ 2 Vn ∧ IsProbabilityMeasure (gibbsMeasure volume Vn) := by
  intro Z Vn
  refine ⟨(contDiff_const.mul (contDiff_norm_sq ℝ)).add (hW.add contDiff_const), ?_⟩
  simpa only [Vn, add_assoc] using
    (convexInteraction_normalized_probability_memLp_two hW hconv ρ hρ).1

/-- With the source normalization and diagonal invariance, convexity itself
supplies every curvature premise of the nonempty classical eigenspace result. -/
theorem classicalL2Eigenspace_finrank_pos_of_convex_diagonal_invariance
    {d : ℕ} (hd : 0 < d) {W : EuclideanSpace ℝ (Fin d) → ℝ}
    (hW : ContDiff ℝ 2 W) (hconv : ConvexOn ℝ univ W) {ρ : ℝ} (hρ : 0 < ρ)
    (hinv : ∀ x, ∀ u : ℝ, W (x + u • diagonalDirection d) = W x)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume (fun x => ρ / 2 * ‖x‖ ^ 2 + W x))) :
    0 < Module.finrank ℝ (classicalL2Eigenspace (fun x => ρ / 2 * ‖x‖ ^ 2 + W x) ρ) :=
  classicalL2Eigenspace_finrank_pos_of_diagonal_invariance hd hW hρ hinv hprob
    (hessian_quadratic_add_convex_lower hW hconv ρ)


/-- After the paper's explicit additive normalization, the convex invariant
interaction supplies a genuine nonzero classical L² eigenspace, with no
probability or partition-integral premise. -/
theorem normalized_convexInteraction_classicalL2Eigenspace_finrank_pos
    {d : ℕ} (hd : 0 < d) {W : EuclideanSpace ℝ (Fin d) → ℝ}
    (hW : ContDiff ℝ 2 W) (hconv : ConvexOn ℝ univ W) {ρ : ℝ} (hρ : 0 < ρ)
    (hinv : ∀ x, ∀ u : ℝ, W (x + u • diagonalDirection d) = W x) :
    let Z := ∫ x, Real.exp (-(ρ / 2 * ‖x‖ ^ 2 + W x))
    0 < Module.finrank ℝ (classicalL2Eigenspace
      (fun x => ρ / 2 * ‖x‖ ^ 2 + W x + Real.log Z) ρ) := by
  intro Z
  have hp := (convexInteraction_normalized_probability_memLp_two hW hconv ρ hρ).1
  have hW' : ContDiff ℝ 2 (fun x => W x + Real.log Z) := hW.add contDiff_const
  have hc' : ConvexOn ℝ univ (fun x => W x + Real.log Z) := hconv.add_const _
  have hi' : ∀ x, ∀ u : ℝ,
      (W (x + u • diagonalDirection d) + Real.log Z) = W x + Real.log Z := by
    intro x u
    rw [hinv x u]
  have hp' : IsProbabilityMeasure
      (gibbsMeasure volume (fun x => ρ / 2 * ‖x‖ ^ 2 + (W x + Real.log Z))) := by
    simpa only [add_assoc] using hp
  have h := classicalL2Eigenspace_finrank_pos_of_convex_diagonal_invariance hd hW' hc' hρ hi' hp'
  have hfun : (fun x : EuclideanSpace ℝ (Fin d) => ρ / 2 * ‖x‖ ^ 2 + (W x + Real.log Z)) =
      (fun x => ρ / 2 * ‖x‖ ^ 2 + W x + Real.log Z) := by
    funext x
    ring
  rw [hfun] at h
  exact h

end CutoffRigidity
