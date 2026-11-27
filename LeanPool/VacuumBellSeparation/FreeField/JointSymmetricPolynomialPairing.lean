/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointCenteredPolynomialMoments
public import LeanPool.VacuumBellSeparation.FreeField.JointWeightedPolynomialGrowth
public import LeanPool.VacuumBellSeparation.Polynomial.JointMidpointPolynomial

/-!
# The weighted symmetric polynomial reproduces the original kernel pairing

The inner products are complex, whereas the original source moments and
the restricted polynomial form are real. Every conjugation is explicit.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open Gaussian Gaussian.HilbertComplexification MvPolynomial MeasureTheory
open ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace ComplexConjugate

theorem jointCenteredScaledCoordinates_swap (a : EuclideanSpace ℝ (Fin 3)) (s : ℝ)
    (x : JointKernelSpace) :
    jointCenteredScaledCoordinates a s (WithLp.toLp 2 (x.snd, x.fst)) =
      jointCenteredScaledCoordinates a s x ∘ swapSpatialSix := by
  funext j
  fin_cases j <;> rfl

theorem integrable_jointCenteredPolynomial_test (a : EuclideanSpace ℝ (Fin 3)) (s : ℝ)
    (P : MvPolynomial (Fin 6) ℂ) (f g : SpatialTestFunction) :
    Integrable (fun x : JointKernelSpace => (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) *
      eval (jointCenteredScaledCoordinates a s x) P) := by
  have hz : Continuous (jointCenteredScaledCoordinates a s) := by
    apply continuous_pi
    intro j
    refine Fin.addCases (m := 3) (n := 3) (fun i => ?_) (fun i => ?_) j <;>
      simp only [jointCenteredScaledCoordinates, Fin.addCases_left, Fin.addCases_right] <;> fun_prop
  exact ((jointSpatialTestProduct f g).continuous.mul
    (P.continuous_eval.comp hz)).integrable_of_hasCompactSupport
    ((hasCompactSupport_jointSpatialTestProduct f g).mul_right)

theorem integral_jointCenteredPolynomial_transpose (a : EuclideanSpace ℝ (Fin 3)) (s : ℝ)
    (P : MvPolynomial (Fin 6) ℂ) (f g : SpatialTestFunction) :
    (∫ x : JointKernelSpace, (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) *
      eval (jointCenteredScaledCoordinates a s x) (rename swapSpatialSix P)) =
    (∫ x : JointKernelSpace, (g.1 x.fst : ℂ) * (f.1 x.snd : ℂ) *
      eval (jointCenteredScaledCoordinates a s x) P) := by
  simp only [eval_rename]
  simp_rw [← jointCenteredScaledCoordinates_swap]
  calc
    _ = ∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        (f.1 p.1 : ℂ) * (g.1 p.2 : ℂ) *
          eval (jointCenteredScaledCoordinates a s (WithLp.toLp 2 (p.2, p.1))) P := by
      simpa only [WithLp.fst, WithLp.snd] using
        (integral_jointKernel_ofLp (fun p => (f.1 p.1 : ℂ) * (g.1 p.2 : ℂ) *
          eval (jointCenteredScaledCoordinates a s (WithLp.toLp 2 (p.2, p.1))) P))
    _ = ∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        (f.1 p.2 : ℂ) * (g.1 p.1 : ℂ) *
          eval (jointCenteredScaledCoordinates a s (WithLp.toLp 2 p)) P :=
      integral_prod_swap (fun p => (f.1 p.2 : ℂ) * (g.1 p.1 : ℂ) *
        eval (jointCenteredScaledCoordinates a s (WithLp.toLp 2 p)) P)
    _ = ∫ x : JointKernelSpace, (f.1 x.snd : ℂ) * (g.1 x.fst : ℂ) *
        eval (jointCenteredScaledCoordinates a s x) P := by
      simpa only [WithLp.fst, WithLp.snd, WithLp.toLp_ofLp] using
        (integral_jointKernel_ofLp (fun p => (f.1 p.2 : ℂ) * (g.1 p.1 : ℂ) *
          eval (jointCenteredScaledCoordinates a s (WithLp.toLp 2 p)) P)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by ring

theorem re_integral_jointCenteredPolynomial_symmetrization
    (a : EuclideanSpace ℝ (Fin 3)) (s : ℝ)
    (P : MvPolynomial (Fin 6) ℂ) (f g : SpatialTestFunction) :
    (∫ x : JointKernelSpace, (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) *
      eval (jointCenteredScaledCoordinates a s x) (-(P + rename swapSpatialSix P))).re =
    -(∑ d ∈ P.support, (P.coeff d).re *
      (normalizedCenteredSourceMoment a s f (spatialSixLeftExponent d) *
          normalizedCenteredSourceMoment a s g (spatialSixRightExponent d) +
        normalizedCenteredSourceMoment a s f (spatialSixRightExponent d) *
          normalizedCenteredSourceMoment a s g (spatialSixLeftExponent d))) := by
  simp only [map_neg, map_add, mul_neg, mul_add]
  rw [integral_neg, integral_add (integrable_jointCenteredPolynomial_test a s P f g)
    (integrable_jointCenteredPolynomial_test a s (rename swapSpatialSix P) f g),
    integral_jointCenteredPolynomial_transpose, integral_jointCenteredPolynomial_test,
    integral_jointCenteredPolynomial_test]
  simp only [Complex.neg_re, Complex.add_re, Complex.re_sum, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]
  rw [← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  ring

theorem inner_jointSymmetricPolynomialOperator_of_real_pairings
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : (Fin 3 → ℕ) → E) (P : MvPolynomial (Fin 6) ℂ) (x y : E)
    (mx my : (Fin 3 → ℕ) → ℝ)
    (hx : ∀ α, inner ℂ x (v α) = (mx α : ℂ))
    (hy : ∀ α, inner ℂ y (v α) = (my α : ℂ)) :
    inner ℂ x (jointSymmetricPolynomialOperator v P y) =
      (-(∑ d ∈ P.support, (P.coeff d).re *
        (mx (spatialSixLeftExponent d) * my (spatialSixRightExponent d) +
          mx (spatialSixRightExponent d) * my (spatialSixLeftExponent d))) : ℝ) := by
  have hy' (α) : inner ℂ (v α) y = (my α : ℂ) := by
    rw [← inner_conj_symm (v α) y, hy, Complex.conj_ofReal]
  simp only [jointSymmetricPolynomialOperator, neg_apply, sum_apply, smul_apply,
    inner_neg_right, inner_sum, inner_smul_right_eq_smul, symmetricRankOne,
    add_apply, inner_add_right, rankOne_apply, hx, hy',
    Complex.real_smul, smul_eq_mul, Complex.ofReal_neg, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_add]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- The actual reserve sandwich agrees with the real polynomial kernel
whenever the supplied vectors are the proved normalized moment vectors. -/
theorem weighted_jointSymmetricPolynomial_pairing
    {μ b : ℝ} (hμ : 0 < μ) (U : Set (EuclideanSpace ℝ (Fin 3)))
    (a : EuclideanSpace ℝ (Fin 3)) (s : ℝ)
    (v : (Fin 3 → ℕ) → ComplexSourceHilbert hμ U)
    (P : MvPolynomial (Fin 6) ℂ)
    (π : SourceTestSpace hμ U → SpatialTestFunction)
    (hv : ∀ α (x : SourceTestSpace hμ U),
      inner ℂ (ofReal (x : SourceHilbert hμ U)) ((sourceReserve hμ U ^ b) (v α)) =
        (normalizedCenteredSourceMoment a s (π x) α : ℂ))
    (x y : SourceTestSpace hμ U) :
    inner ℂ (ofReal (x : SourceHilbert hμ U))
      ((sourceReserve hμ U ^ b * jointSymmetricPolynomialOperator v P * sourceReserve hμ U ^ b)
        (ofReal (y : SourceHilbert hμ U))) =
      ((∫ z : JointKernelSpace, ((π x).1 z.fst : ℂ) * ((π y).1 z.snd : ℂ) *
        eval (jointCenteredScaledCoordinates a s z) (-(P + rename swapSpatialSix P))).re : ℝ) := by
  rw [jointSymmetricPolynomialOperator_sandwich _ (CFC.rpow_nonneg (a := sourceReserve hμ U)
    (y := b)).isSelfAdjoint]
  rw [inner_jointSymmetricPolynomialOperator_of_real_pairings
    (fun α => (sourceReserve hμ U ^ b) (v α)) P _ _
    (fun α => normalizedCenteredSourceMoment a s (π x) α)
    (fun α => normalizedCenteredSourceMoment a s (π y) α)
    (fun α => hv α x) (fun α => hv α y)]
  rw [re_integral_jointCenteredPolynomial_symmetrization]

end VacuumBellSeparation
