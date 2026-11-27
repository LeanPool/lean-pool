/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointNormalizedMomentVectors
public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialKernelMoments

/-! # Literal centered and scaled polynomial test integrals -/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open Gaussian MeasureTheory MvPolynomial

/-- Normalized centered monomial given by `∏ j, (((x j - a j) / s : ℝ) : ℂ) ^ α j`. -/
def normalizedCenteredMonomial (a : EuclideanSpace ℝ (Fin 3)) (s : ℝ)
    (α : Fin 3 → ℕ) (x : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  ∏ j, (((x j - a j) / s : ℝ) : ℂ) ^ α j

theorem continuous_normalizedCenteredMonomial (a : EuclideanSpace ℝ (Fin 3))
    (s : ℝ) (α : Fin 3 → ℕ) : Continuous (normalizedCenteredMonomial a s α) := by
  unfold normalizedCenteredMonomial
  fun_prop

theorem centeredSpatialTestMoment_eq_integral (a : EuclideanSpace ℝ (Fin 3))
    (f : SpatialTestFunction) (α : Fin 3 → ℕ) :
    centeredSpatialTestMoment a f α = ∫ x, (∏ j, (x j - a j) ^ α j) * f.1 x := by
  unfold centeredSpatialTestMoment spatialRealTestMoment
  rw [← integral_add_right_eq_self
    (fun x : EuclideanSpace ℝ (Fin 3) => (∏ j, (x j - a j) ^ α j) * f.1 x) a]
  simp only [spatialTestTranslate, sub_neg_eq_add, PiLp.add_apply, add_sub_cancel_right]

theorem normalizedCenteredSourceMoment_eq_integral (a : EuclideanSpace ℝ (Fin 3))
    (s : ℝ) (f : SpatialTestFunction) (α : Fin 3 → ℕ) :
    (normalizedCenteredSourceMoment a s f α : ℂ) =
      ∫ x, normalizedCenteredMonomial a s α x * (f.1 x : ℂ) := by
  rw [normalizedCenteredSourceMoment, centeredSpatialTestMoment_eq_integral,
    ← integral_const_mul]
  rw [← integral_complex_ofReal (μ := volume)
    (f := fun x : EuclideanSpace ℝ (Fin 3) =>
      s⁻¹ ^ (∑ j, α j) * ((∏ j, (x j - a j) ^ α j) * f.1 x))]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  unfold normalizedCenteredMonomial
  push_cast
  rw [show (∏ j : Fin 3, (((x j : ℂ) - (a j : ℂ)) / (s : ℂ)) ^ α j) =
      (∏ j : Fin 3, ((x j : ℂ) - (a j : ℂ)) ^ α j) *
        ((s : ℂ)⁻¹) ^ (∑ j, α j) by
      simp only [div_eq_mul_inv, mul_pow, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum]]
  ring

/-- Joint centered scaled coordinates. -/
def jointCenteredScaledCoordinates (a : EuclideanSpace ℝ (Fin 3)) (s : ℝ)
    (x : JointKernelSpace) (j : Fin 6) : ℂ :=
  Fin.addCases (fun i : Fin 3 => (((x.fst i - a i) / s : ℝ) : ℂ))
    (fun i : Fin 3 => (((x.snd i - a i) / s : ℝ) : ℂ)) j

theorem jointCenteredScaled_monomial (a : EuclideanSpace ℝ (Fin 3)) (s : ℝ)
    (d : Fin 6 →₀ ℕ) (x : JointKernelSpace) :
    (∏ j : Fin 6, jointCenteredScaledCoordinates a s x j ^ d j) =
      normalizedCenteredMonomial a s (spatialSixLeftExponent d) x.fst *
        normalizedCenteredMonomial a s (spatialSixRightExponent d) x.snd := by
  rw [Fin.prod_univ_add (a := 3) (b := 3)]
  simp only [jointCenteredScaledCoordinates, Fin.addCases_left, Fin.addCases_right,
    normalizedCenteredMonomial, spatialSixLeftExponent, spatialSixRightExponent]

theorem integral_jointCenteredPolynomial_test (a : EuclideanSpace ℝ (Fin 3)) (s : ℝ)
    (P : MvPolynomial (Fin 6) ℂ) (f g : SpatialTestFunction) :
    (∫ x : JointKernelSpace, (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) *
      eval (jointCenteredScaledCoordinates a s x) P) =
      ∑ d ∈ P.support, P.coeff d *
        (normalizedCenteredSourceMoment a s f (spatialSixLeftExponent d) : ℂ) *
        (normalizedCenteredSourceMoment a s g (spatialSixRightExponent d) : ℂ) := by
  let T := fun (d : Fin 6 →₀ ℕ) (x : JointKernelSpace) =>
    P.coeff d * ((normalizedCenteredMonomial a s (spatialSixLeftExponent d) x.fst *
      (f.1 x.fst : ℂ)) *
      (normalizedCenteredMonomial a s (spatialSixRightExponent d) x.snd * (g.1 x.snd : ℂ)))
  have he (x : JointKernelSpace) :
      (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) * eval (jointCenteredScaledCoordinates a s x) P =
        ∑ d ∈ P.support, T d x := by
    rw [eval_eq']
    simp only [Finset.mul_sum, jointCenteredScaled_monomial]
    apply Finset.sum_congr rfl
    intro d hd
    dsimp only [T]
    ring
  have hi (d : Fin 6 →₀ ℕ) : Integrable (T d) := by
    have hc : Continuous (T d) := by
      have hα := continuous_normalizedCenteredMonomial a s (spatialSixLeftExponent d)
      have hβ := continuous_normalizedCenteredMonomial a s (spatialSixRightExponent d)
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
      (normalizedCenteredMonomial a s (spatialSixLeftExponent d) p.1 * (f.1 p.1 : ℂ)) *
        (normalizedCenteredMonomial a s (spatialSixRightExponent d) p.2 * (g.1 p.2 : ℂ)))
      (WithLp.ofLp x)) = _
  rw [integral_jointKernel_ofLp (G := ℂ)
    (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      (normalizedCenteredMonomial a s (spatialSixLeftExponent d) p.1 * (f.1 p.1 : ℂ)) *
        (normalizedCenteredMonomial a s (spatialSixRightExponent d) p.2 * (g.1 p.2 : ℂ)))]
  change P.coeff d * (∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
    (normalizedCenteredMonomial a s (spatialSixLeftExponent d) p.1 * (f.1 p.1 : ℂ)) *
      (normalizedCenteredMonomial a s (spatialSixRightExponent d) p.2 * (g.1 p.2 : ℂ))
        ∂(volume.prod volume)) = _
  rw [integral_prod_mul (μ := volume) (ν := volume)
    (fun x : EuclideanSpace ℝ (Fin 3) =>
      normalizedCenteredMonomial a s (spatialSixLeftExponent d) x * (f.1 x : ℂ))
    (fun y : EuclideanSpace ℝ (Fin 3) =>
      normalizedCenteredMonomial a s (spatialSixRightExponent d) y * (g.1 y : ℂ)),
    ← normalizedCenteredSourceMoment_eq_integral, ← normalizedCenteredSourceMoment_eq_integral]
  ring

theorem jointPhysicalMidpoint_eq_centeredScaled {s : ℝ} (hs : s ≠ 0)
    (x : JointKernelSpace) :
    jointPhysicalMidpoint s (jointComplexCoordinates x) =
      jointCenteredScaledCoordinates (spatialAxisDisplacement (s / 2) 0) s x := by
  have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  funext j
  refine Fin.addCases (m := 3) (n := 3) (fun i => ?_) (fun i => ?_) j
  · simp only [jointPhysicalMidpoint, jointComplexCoordinates_left,
      jointCenteredScaledCoordinates, Fin.addCases_left]
    fin_cases i <;> simp [jointPhysicalMidpointShift, spatialAxisDisplacement]
    field_simp [hs']
  · simp only [jointPhysicalMidpoint, jointComplexCoordinates_right,
      jointCenteredScaledCoordinates, Fin.addCases_right]
    fin_cases i <;> simp [jointPhysicalMidpointShift, spatialAxisDisplacement]
    field_simp [hs']

end VacuumBellSeparation
