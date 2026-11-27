/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.ComplexShellChart
public import LeanPool.VacuumBellSeparation.Shell.ComplexLorentzFamilySmooth
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Genuine radial dispersion and contour derivatives

The positive radial base B keeps the mass-shell parametrization smooth
also at mass zero. These are literal positive-energy momenta.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- Radial shell momentum defined as `WithLp.toLp 2 ![0, B + r, 0]`. -/
noncomputable def radialShellMomentum (B r : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![0, B + r, 0]

/-- Radial shell energy given by `Real.sqrt (m ^ 2 + (B + r) ^ 2)`. -/
noncomputable def radialShellEnergy (m B r : ℝ) : ℝ :=
  Real.sqrt (m ^ 2 + (B + r) ^ 2)

theorem radialShellMomentum_dispersion (m B r : ℝ) :
    dispersion m (radialShellMomentum B r) = radialShellEnergy m B r := by
  simp [dispersion, radialShellEnergy, radialShellMomentum,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

theorem radialShellEnergy_pos {B : ℝ} (hB : 0 < B) (m : ℝ) :
    0 < radialShellEnergy m B 0 := by
  apply Real.sqrt_pos.mpr
  simpa using add_pos_of_nonneg_of_pos (sq_nonneg m) (sq_pos_of_pos hB)

theorem contDiffAt_radialShellEnergy {B : ℝ} (hB : 0 < B) (m : ℝ) :
    ContDiffAt ℝ ⊤ (radialShellEnergy m B) 0 := by
  have h : ContDiff ℝ ⊤ (fun r : ℝ => m ^ 2 + (B + r) ^ 2) := by fun_prop
  exact h.contDiffAt.sqrt (by
    simpa using (add_pos_of_nonneg_of_pos (sq_nonneg m) (sq_pos_of_pos hB)).ne')

theorem hasDerivAt_radialShellEnergy {B : ℝ} (hB : 0 < B) (m : ℝ) :
    HasDerivAt (radialShellEnergy m B) (B / radialShellEnergy m B 0) 0 := by
  have hq := (((hasDerivAt_id (0 : ℝ)).const_add B).pow 2).const_add (m ^ 2)
  have h := hq.sqrt (by
    simpa using (add_pos_of_nonneg_of_pos (sq_nonneg m) (sq_pos_of_pos hB)).ne')
  change HasDerivAt (fun r : ℝ => Real.sqrt (m ^ 2 + (B + r) ^ 2))
    (B / radialShellEnergy m B 0) 0
  convert h using 1 <;> simp [radialShellEnergy]; ring

/-- Radial shell contour. -/
noncomputable def radialShellContour (m B θ r : ℝ) : ComplexSpacetime :=
  (((radialShellEnergy m B r * Real.cos θ : ℝ) : ℂ),
    ![Complex.I * (radialShellEnergy m B r * Real.sin θ : ℝ), ((B + r : ℝ) : ℂ), 0])

theorem radialShellContour_eq_boost (m B θ r : ℝ) :
    radialShellContour m B θ r =
      complexShellBoost m ((θ : ℂ) * Complex.I) (radialShellMomentum B r) := by
  rw [complexShellBoost, radialShellMomentum_dispersion,
    Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  apply Prod.ext
  · simp [radialShellContour, radialShellMomentum, Complex.ofReal_mul]
  · ext i
    fin_cases i <;> simp [radialShellContour, radialShellMomentum, Complex.ofReal_mul]; ring

theorem contDiffAt_radialShellContour {B : ℝ} (hB : 0 < B) (m θ : ℝ) :
    ContDiffAt ℝ ⊤ (radialShellContour m B θ) 0 := by
  have h := contDiffAt_radialShellEnergy hB m
  apply ContDiffAt.prodMk
  · simpa only [Complex.real_smul, Complex.ofReal_mul] using
      h.smul_const (Real.cos θ : ℂ)
  · apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · change ContDiffAt ℝ ⊤
        (fun r => Complex.I * ((radialShellEnergy m B r * Real.sin θ : ℝ) : ℂ)) 0
      simpa only [Complex.real_smul, Complex.ofReal_mul, mul_assoc, mul_left_comm,
        mul_comm] using h.smul_const (Complex.I * (Real.sin θ : ℂ))
    · exact Complex.ofRealCLM.contDiff.contDiffAt.comp 0
        (contDiffAt_const.add contDiffAt_id)
    · exact contDiffAt_const

theorem hasDerivAt_radialShellContour {B : ℝ} (hB : 0 < B) (m θ : ℝ) :
    HasDerivAt (radialShellContour m B θ)
      (((B / radialShellEnergy m B 0 * Real.cos θ : ℝ) : ℂ),
        ![Complex.I * (B / radialShellEnergy m B 0 * Real.sin θ : ℝ), 1, 0]) 0 := by
  have h := hasDerivAt_radialShellEnergy hB m
  apply HasDerivAt.prodMk
  · simpa only [Complex.real_smul, Complex.ofReal_mul] using
      h.smul_const (Real.cos θ : ℂ)
  · apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · change HasDerivAt
        (fun r => Complex.I * ((radialShellEnergy m B r * Real.sin θ : ℝ) : ℂ))
        (Complex.I * ((B / radialShellEnergy m B 0 * Real.sin θ : ℝ) : ℂ)) 0
      simpa only [Complex.real_smul, Complex.ofReal_mul, mul_assoc, mul_left_comm,
        mul_comm] using h.smul_const (Complex.I * (Real.sin θ : ℂ))
    · simpa using ((hasDerivAt_id (0 : ℝ)).const_add B).ofReal_comp
    · exact hasDerivAt_const 0 0

end VacuumBellSeparation
