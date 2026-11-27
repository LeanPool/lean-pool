/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialFormRank
public import LeanPool.VacuumBellSeparation.FreeField.JointRealCoordinates
public import LeanPool.VacuumBellSeparation.FreeField.JointSmoothKernelProduct
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Polynomial kernel integrals are the actual finite moment pairings

All integrals use the genuine six-dimensional Euclidean product volume.
Compact support proves convergence before the finite polynomial expansion
is integrated. Complex coefficients are restricted by taking real parts.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open MeasureTheory MvPolynomial Gaussian
open scoped InnerProductSpace

theorem jointPolynomial_monomial_coordinates (d : Fin 6 →₀ ℕ) (x : JointKernelSpace) :
    (∏ j : Fin 6, jointComplexCoordinates x j ^ d j) =
      spatialMonomial (spatialSixLeftExponent d) x.fst *
        spatialMonomial (spatialSixRightExponent d) x.snd := by
  rw [Fin.prod_univ_add (a := 3) (b := 3)]
  simp only [jointComplexCoordinates_left, jointComplexCoordinates_right,
    spatialMonomial, spatialSixLeftExponent, spatialSixRightExponent]

theorem integrable_jointPolynomial_test (P : MvPolynomial (Fin 6) ℂ)
    (f g : SpatialTestFunction) :
    Integrable (fun x : JointKernelSpace =>
      (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) * eval (jointComplexCoordinates x) P) := by
  have hc : Continuous (fun x : JointKernelSpace =>
      (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) * eval (jointComplexCoordinates x) P) :=
    (jointSpatialTestProduct f g).continuous.mul
      (P.continuous_eval.comp jointComplexCoordinates.continuous)
  exact hc.integrable_of_hasCompactSupport
    ((hasCompactSupport_jointSpatialTestProduct f g).mul_right)

theorem integral_jointPolynomial_test (P : MvPolynomial (Fin 6) ℂ)
    (f g : SpatialTestFunction) :
    (∫ x : JointKernelSpace,
      (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) * eval (jointComplexCoordinates x) P) =
      ∑ d ∈ P.support, P.coeff d * spatialTestMoment f (spatialSixLeftExponent d) *
        spatialTestMoment g (spatialSixRightExponent d) := by
  let T := fun (d : Fin 6 →₀ ℕ) (x : JointKernelSpace) =>
    P.coeff d * ((spatialMonomial (spatialSixLeftExponent d) x.fst * (f.1 x.fst : ℂ)) *
      (spatialMonomial (spatialSixRightExponent d) x.snd * (g.1 x.snd : ℂ)))
  have he (x : JointKernelSpace) :
      (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) * eval (jointComplexCoordinates x) P =
        ∑ d ∈ P.support, T d x := by
    rw [eval_eq']
    simp only [Finset.mul_sum, jointPolynomial_monomial_coordinates]
    apply Finset.sum_congr rfl
    intro d hd
    dsimp only [T]
    ring
  have hi (d : Fin 6 →₀ ℕ) : Integrable (T d) := by
    have hc : Continuous (T d) := by
      have hα := continuous_spatialMonomial (spatialSixLeftExponent d)
      have hβ := continuous_spatialMonomial (spatialSixRightExponent d)
      have hf := f.2.1.continuous
      have hg := g.2.1.continuous
      dsimp only [T]
      fun_prop
    apply hc.integrable_of_hasCompactSupport
    apply HasCompactSupport.of_support_subset_isCompact
      (hasCompactSupport_jointSpatialTestProduct f g).isCompact
    intro x hx
    apply subset_tsupport
    by_contra hn
    have hn' : (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) = 0 := by
      simpa only [Function.mem_support, not_not] using hn
    rcases mul_eq_zero.mp hn' with hf | hg
    · exact hx (by simp only [T, hf, mul_zero, zero_mul])
    · exact hx (by simp only [T, hg, mul_zero])
  simp_rw [he]
  rw [integral_finsetSum P.support (fun d _ => hi d)]
  apply Finset.sum_congr rfl
  intro d hd
  dsimp only [T]
  rw [integral_const_mul]
  change P.coeff d * (∫ x : JointKernelSpace,
    (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      (spatialMonomial (spatialSixLeftExponent d) p.1 * (f.1 p.1 : ℂ)) *
        (spatialMonomial (spatialSixRightExponent d) p.2 * (g.1 p.2 : ℂ)))
      (WithLp.ofLp x)) = _
  rw [integral_jointKernel_ofLp (G := ℂ)
    (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      (spatialMonomial (spatialSixLeftExponent d) p.1 * (f.1 p.1 : ℂ)) *
        (spatialMonomial (spatialSixRightExponent d) p.2 * (g.1 p.2 : ℂ)))]
  change P.coeff d * (∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
    (spatialMonomial (spatialSixLeftExponent d) p.1 * (f.1 p.1 : ℂ)) *
      (spatialMonomial (spatialSixRightExponent d) p.2 * (g.1 p.2 : ℂ))
        ∂(volume.prod volume)) = _
  rw [integral_prod_mul (μ := volume) (ν := volume)
    (fun x : EuclideanSpace ℝ (Fin 3) =>
      spatialMonomial (spatialSixLeftExponent d) x * (f.1 x : ℂ))
    (fun y : EuclideanSpace ℝ (Fin 3) =>
      spatialMonomial (spatialSixRightExponent d) y * (g.1 y : ℂ))]
  simp only [spatialTestMoment, mul_assoc]

theorem re_integral_jointPolynomial_test (P : MvPolynomial (Fin 6) ℂ)
    (f g : SpatialTestFunction) :
    (∫ x : JointKernelSpace,
      (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) * eval (jointComplexCoordinates x) P).re =
      ∑ d ∈ P.support, (P.coeff d).re * spatialRealTestMoment f (spatialSixLeftExponent d) *
        spatialRealTestMoment g (spatialSixRightExponent d) := by
  rw [integral_jointPolynomial_test]
  simp only [Complex.re_sum, spatialTestMoment_eq_ofReal, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

theorem jointPolynomial_field_pairing {μ : ℝ} (hμ : 0 < μ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (v : JointSourceMomentFamily hμ U)
    (P : MvPolynomial (Fin 6) ℂ) (x y : SourceTestSpace hμ U) :
    inner ℝ (x : SourceHilbert hμ U)
      (jointPolynomialMomentOperator (𝕜 := ℝ) v.field P (y : SourceHilbert hμ U)) =
        (∫ z : JointKernelSpace, (x.1.1.1 z.fst : ℂ) * (y.1.1.1 z.snd : ℂ) *
          eval (jointComplexCoordinates z) P).re := by
  rw [inner_jointPolynomialMomentOperator_real, re_integral_jointPolynomial_test]
  simp only [v.field_pairing]

theorem jointPolynomial_momentum_pairing {μ : ℝ} (hμ : 0 < μ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (v : JointSourceMomentFamily hμ U)
    (P : MvPolynomial (Fin 6) ℂ) (x y : SourceTestSpace hμ U) :
    inner ℝ (x : SourceHilbert hμ U)
      (jointPolynomialMomentOperator (𝕜 := ℝ) v.momentum P (y : SourceHilbert hμ U)) =
        (∫ z : JointKernelSpace, (x.1.2.1 z.fst : ℂ) * (y.1.2.1 z.snd : ℂ) *
          eval (jointComplexCoordinates z) P).re := by
  rw [inner_jointPolynomialMomentOperator_real, re_integral_jointPolynomial_test]
  simp only [v.momentum_pairing]

end VacuumBellSeparation
