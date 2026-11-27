/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.BargmannPointwise
public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeCoherentCoordinates
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# The actual finite-mode Bargmann isometry

Products of the proved one-mode Gaussian monomials are actual orthonormal
vectors in L² of complex product Lebesgue measure. The Hilbert-sum API
constructs an isometry from the full occupation space. All finite mode
counts are included, including the empty product and its one-dimensional
occupation space.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory
open scoped ComplexConjugate

theorem integrable_bargmannMonomial_norm_sq (n : ℕ) :
    Integrable (fun z : ℂ => ‖bargmannMonomial n z‖ ^ 2) :=
  (memLp_two_iff_integrable_sq_norm (memLp_bargmannMonomial n).aestronglyMeasurable).mp
    (memLp_bargmannMonomial n)

theorem integral_inner_bargmannMonomial (n k : ℕ) :
    (∫ z : ℂ, inner ℂ (bargmannMonomial n z) (bargmannMonomial k z)) =
      if n = k then 1 else 0 := by
  calc
    _ = inner ℂ (bargmannBasisVector n) (bargmannBasisVector k) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(memLp_bargmannMonomial n).coeFn_toLp,
        (memLp_bargmannMonomial k).coeFn_toLp] with z hn hk
      simp only [bargmannBasisVector, hn, hk]
    _ = _ := inner_bargmannBasisVector n k

/-- Multi Bargmann monomial given by `∏ j, bargmannMonomial (k j) (z j)`. -/
def multiBargmannMonomial {m : ℕ} (k : Fin m → ℕ) (z : Fin m → ℂ) : ℂ :=
  ∏ j, bargmannMonomial (k j) (z j)

theorem multiBargmannMonomial_norm_sq {m : ℕ} (k : Fin m → ℕ) (z : Fin m → ℂ) :
    ‖multiBargmannMonomial k z‖ ^ 2 = ∏ j, ‖bargmannMonomial (k j) (z j)‖ ^ 2 := by
  rw [multiBargmannMonomial, norm_prod, ← Finset.prod_pow]

theorem memLp_multiBargmannMonomial {m : ℕ} (k : Fin m → ℕ) :
    MemLp (multiBargmannMonomial k) 2 (volume : Measure (Fin m → ℂ)) := by
  have hc : Continuous (multiBargmannMonomial k) := by
    unfold multiBargmannMonomial bargmannMonomial
    fun_prop
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  simpa only [multiBargmannMonomial_norm_sq, MeasureTheory.volume_pi] using
    (Integrable.fintype_prod (fun j => integrable_bargmannMonomial_norm_sq (k j)))

theorem inner_multiBargmannMonomial {m : ℕ} (k l : Fin m → ℕ) (z : Fin m → ℂ) :
    inner ℂ (multiBargmannMonomial k z) (multiBargmannMonomial l z) =
      ∏ j, inner ℂ (bargmannMonomial (k j) (z j)) (bargmannMonomial (l j) (z j)) := by
  simp only [multiBargmannMonomial, RCLike.inner_apply', map_prod, Finset.prod_mul_distrib]

theorem integral_inner_multiBargmannMonomial {m : ℕ} (k l : Fin m → ℕ) :
    (∫ z : Fin m → ℂ, inner ℂ (multiBargmannMonomial k z) (multiBargmannMonomial l z)) =
      if k = l then 1 else 0 := by
  simp_rw [inner_multiBargmannMonomial]
  rw [MeasureTheory.volume_pi, integral_fintype_prod_eq_prod
    (fun j z => inner ℂ (bargmannMonomial (k j) z) (bargmannMonomial (l j) z))]
  simp_rw [integral_inner_bargmannMonomial]
  by_cases h : k = l
  · subst l
    simp
  · simp only [h, ite_false]
    obtain ⟨j, hj⟩ : ∃ j, k j ≠ l j := by
      by_contra hnone
      push Not at hnone
      exact h (funext hnone)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

/-- Multi Bargmann basis vector. -/
def multiBargmannBasisVector {m : ℕ} (k : Fin m → ℕ) : Lp ℂ 2 (volume : Measure (Fin m → ℂ)) :=
  (memLp_multiBargmannMonomial k).toLp (multiBargmannMonomial k)

theorem inner_multiBargmannBasisVector {m : ℕ} (k l : Fin m → ℕ) :
    inner ℂ (multiBargmannBasisVector k) (multiBargmannBasisVector l) =
      if k = l then 1 else 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ z : Fin m → ℂ, inner ℂ (multiBargmannMonomial k z) (multiBargmannMonomial l z) := by
      apply integral_congr_ae
      filter_upwards [(memLp_multiBargmannMonomial k).coeFn_toLp,
        (memLp_multiBargmannMonomial l).coeFn_toLp] with z hk hl
      simp only [multiBargmannBasisVector, hk, hl]
    _ = _ := integral_inner_multiBargmannMonomial k l

theorem orthonormal_multiBargmannBasisVector (m : ℕ) :
    Orthonormal ℂ (@multiBargmannBasisVector m) :=
  orthonormal_iff_ite.mpr inner_multiBargmannBasisVector

/-- Multi Bargmann L². -/
def multiBargmannL2 (m : ℕ) :
    MultiModeOscillatorSpace m →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (Fin m → ℂ)) :=
  (orthonormal_multiBargmannBasisVector m).orthogonalFamily.linearIsometry

theorem multiBargmannL2_apply_single {m : ℕ} (k : Fin m → ℕ) (c : ℂ) :
    multiBargmannL2 m (lp.single 2 k c) = c • multiBargmannBasisVector k := by
  rw [multiBargmannL2, OrthogonalFamily.linearIsometry_apply_single,
    LinearIsometry.toSpanSingleton_apply]

theorem hasSum_multiBargmannL2 {m : ℕ} (x : MultiModeOscillatorSpace m) :
    HasSum (fun k => x k • multiBargmannBasisVector k) (multiBargmannL2 m x) := by
  simpa only [multiBargmannL2, LinearIsometry.toSpanSingleton_apply] using
    (orthonormal_multiBargmannBasisVector m).orthogonalFamily.hasSum_linearIsometry x

end VacuumBellSeparation.Gaussian
