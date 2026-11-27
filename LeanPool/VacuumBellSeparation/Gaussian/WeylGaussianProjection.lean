/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.WeylAverageFubini

/-!
# A nonzero actual Gaussian projection for a symplectic relabeling

Evenness of the Gaussian and the actual Weyl adjoint identity prove
self-adjointness of the strong average. The proved compressed-Weyl
identity gives its square. After the literal π^m normalization it is a
nonzero orthogonal projection, and its normalized vacuum image is an
actual unit vector with the required Gaussian Weyl characteristic.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory ContinuousLinearMap
open scoped ComplexConjugate ComplexOrder

variable {m : ℕ}

theorem weylVacuumWeight_conj (z : Fin m → ℂ) : conj
  (weylVacuumWeight m z) = weylVacuumWeight m z := by
  simp only [weylVacuumWeight, ← Complex.exp_conj, Complex.conj_ofReal]

theorem weylVacuumWeight_neg (z : Fin m → ℂ) : weylVacuumWeight m (-z) = weylVacuumWeight m z := by
  simp only [weylVacuumWeight, WithLp.toLp_neg, norm_neg]

theorem relabeledWeylAverage_isSelfAdjoint
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m) :
    IsSelfAdjoint (relabeledWeylAverage T) := by
  apply isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  calc
    inner ℂ (relabeledWeylAverage T x) y =
        conj (inner ℂ y (relabeledWeylAverage T x)) := (inner_conj_symm _ _).symm
    _ = ∫ z : Fin m → ℂ, conj (weylVacuumWeight m z *
        inner ℂ y (multiOscillatorWeyl (T (WithLp.toLp 2 z)) x)) := by
      rw [inner_relabeledWeylAverage, integral_conj]
    _ = ∫ z : Fin m → ℂ, weylVacuumWeight m (-z) *
        inner ℂ x (multiOscillatorWeyl (T (WithLp.toLp 2 (-z))) y) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        dsimp only
        rw [map_mul, weylVacuumWeight_conj, inner_conj_symm,
          ← adjoint_inner_right, multiOscillatorWeyl_adjoint,
          weylVacuumWeight_neg, WithLp.toLp_neg, map_neg]
    _ = ∫ z : Fin m → ℂ, weylVacuumWeight m z *
        inner ℂ x (multiOscillatorWeyl (T (WithLp.toLp 2 z)) y) :=
      integral_neg_eq_self (fun z : Fin m → ℂ => weylVacuumWeight m z *
        inner ℂ x (multiOscillatorWeyl (T (WithLp.toLp 2 z)) y)) volume
    _ = inner ℂ x (relabeledWeylAverage T y) := (inner_relabeledWeylAverage T x y).symm

theorem relabeledWeylAverage_mul_self
    {T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m} (hT : PreservesWeylForm T) :
    relabeledWeylAverage T * relabeledWeylAverage T =
      (Real.pi : ℂ) ^ m • relabeledWeylAverage T := by
  simpa only [map_zero, multiOscillatorWeyl_zero, mul_one, phaseSpaceVacuumWeight,
    norm_zero, zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_div,
    Complex.ofReal_zero, Complex.exp_zero] using relabeledWeylAverage_sandwich hT 0

/-- Relabeled Gaussian projection given by `((Real.pi : ℂ) ^ m)⁻¹ • relabeledWeylAverage T`. -/
def relabeledGaussianProjection
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m) :
    MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m :=
  ((Real.pi : ℂ) ^ m)⁻¹ • relabeledWeylAverage T

theorem relabeledGaussianProjection_isSelfAdjoint
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m) :
    IsSelfAdjoint (relabeledGaussianProjection T) := by
  exact (show IsSelfAdjoint (((Real.pi : ℂ) ^ m)⁻¹) by simp [IsSelfAdjoint]).smul
    (relabeledWeylAverage_isSelfAdjoint T)

theorem relabeledGaussianProjection_mul_self
    {T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m} (hT : PreservesWeylForm T) :
    relabeledGaussianProjection T * relabeledGaussianProjection T = relabeledGaussianProjection
      T := by
  have hp : (Real.pi : ℂ) ^ m ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  simp only [relabeledGaussianProjection, smul_mul_assoc, mul_smul_comm,
    relabeledWeylAverage_mul_self hT, smul_smul]
  congr 1
  field_simp [hp]

theorem relabeledGaussianProjection_isStarProjection
    {T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m} (hT : PreservesWeylForm T) :
    IsStarProjection (relabeledGaussianProjection T) :=
  ⟨relabeledGaussianProjection_mul_self hT, relabeledGaussianProjection_isSelfAdjoint T⟩

theorem relabeledGaussianProjection_nonneg
    {T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m} (hT : PreservesWeylForm T) :
    0 ≤ relabeledGaussianProjection T := (relabeledGaussianProjection_isStarProjection hT).nonneg

theorem relabeledGaussianProjection_vacuum_ne_zero
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m) :
    relabeledGaussianProjection T (multiCoherentVector (0 : MultiModePhaseSpace m)) ≠ 0 := by
  rw [relabeledGaussianProjection, smul_apply]
  exact smul_ne_zero (inv_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    (relabeledWeylAverage_vacuum_ne_zero T)

theorem relabeledGaussianProjection_weyl_sandwich
    {T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m} (hT : PreservesWeylForm T)
    (a : MultiModePhaseSpace m) :
    relabeledGaussianProjection T * multiOscillatorWeyl (T a) * relabeledGaussianProjection T =
      phaseSpaceVacuumWeight a • relabeledGaussianProjection T := by
  have hp : (Real.pi : ℂ) ^ m ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  simp only [relabeledGaussianProjection, smul_mul_assoc, mul_smul_comm,
    relabeledWeylAverage_sandwich hT, smul_smul]
  congr 1
  field_simp [hp]

/-- Relabeled Gaussian vacuum. -/
def relabeledGaussianVacuum
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m) : MultiModeOscillatorSpace m :=
  (‖relabeledGaussianProjection T (multiCoherentVector (0 : MultiModePhaseSpace m))‖⁻¹ : ℝ) •
    relabeledGaussianProjection T (multiCoherentVector 0)

theorem norm_relabeledGaussianVacuum
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m) : ‖relabeledGaussianVacuum T‖ = 1 := by
  have hn := norm_ne_zero_iff.mpr (relabeledGaussianProjection_vacuum_ne_zero T)
  rw [relabeledGaussianVacuum, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hn]

theorem relabeledGaussianProjection_vacuum_fixed
    {T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m} (hT : PreservesWeylForm T) :
    relabeledGaussianProjection T (relabeledGaussianVacuum T) = relabeledGaussianVacuum T := by
  rw [relabeledGaussianVacuum, map_smul_of_tower, ← mul_apply_eq_comp,
    relabeledGaussianProjection_mul_self hT]

/-- Actual Gaussian vector characteristic for the relabeled Weyl family,
derived from the nonzero projection and its compressed-Weyl identity. -/
theorem relabeledGaussianVacuum_characteristic
    {T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m} (hT : PreservesWeylForm T)
    (a : MultiModePhaseSpace m) :
    inner ℂ (relabeledGaussianVacuum T)
      (multiOscillatorWeyl (T a) (relabeledGaussianVacuum T)) = phaseSpaceVacuumWeight a := by
  let P := relabeledGaussianProjection T
  let v := relabeledGaussianVacuum T
  have hPv : P v = v := relabeledGaussianProjection_vacuum_fixed hT
  have hP : P.adjoint = P := (isSelfAdjoint_iff'.mp (relabeledGaussianProjection_isSelfAdjoint T))
  have hinner : inner ℂ v v = 1 := by
    rw [inner_self_eq_norm_sq_to_K, norm_relabeledGaussianVacuum]
    norm_num
  calc
    _ = inner ℂ (P v) (multiOscillatorWeyl (T a) (P v)) := by rw [hPv]
    _ = inner ℂ v (P (multiOscillatorWeyl (T a) (P v))) := by
      rw [← adjoint_inner_right, hP]
    _ = inner ℂ v ((P * multiOscillatorWeyl (T a) * P) v) := by
      simp only [mul_apply_eq_comp]
    _ = inner ℂ v ((phaseSpaceVacuumWeight a • P) v) := by
      rw [show P * multiOscillatorWeyl (T a) * P = phaseSpaceVacuumWeight a • P from
        relabeledGaussianProjection_weyl_sandwich hT a]
    _ = phaseSpaceVacuumWeight a := by rw [smul_apply, inner_smul_right, hPv, hinner, mul_one]

end VacuumBellSeparation.Gaussian
