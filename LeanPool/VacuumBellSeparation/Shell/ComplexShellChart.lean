/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ComplexLorentzForm
public import Mathlib.Analysis.Complex.SqrtDeriv

/-!
# Literal complex-shell coordinates near the canonical regular preimage

The free coordinates are (z0,z1,z3); the second spatial coordinate is
the principal square root of z0^2-z1^2-z3^2-m^2. On its positive-real
radicand neighbourhood this gives an actual holomorphic shell chart.
No chart measure or pushforward-density conclusion is asserted here.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- Continuous linear map for the complex shell coordinates, of type `ComplexSpacetime →L[ℂ] (Fin 3
→ ℂ)`. -/
noncomputable def complexShellCoordinates : ComplexSpacetime →L[ℂ] (Fin 3 → ℂ) :=
  ContinuousLinearMap.pi fun i => Fin.cases
    (ContinuousLinearMap.fst ℂ ℂ (Fin 3 → ℂ))
    (fun j => (ContinuousLinearMap.proj (if j = 0 then 0 else 2)).comp
      (ContinuousLinearMap.snd ℂ ℂ (Fin 3 → ℂ))) i

theorem complexShellCoordinates_apply (z : ComplexSpacetime) :
    complexShellCoordinates z = ![z.1, z.2 0, z.2 2] := by
  ext i
  fin_cases i <;> rfl

/-- Complex shell radicand given by `w 0 ^ 2 - w 1 ^ 2 - w 2 ^ 2 - (m : ℂ) ^ 2`. -/
noncomputable def complexShellRadicand (m : ℝ) (w : Fin 3 → ℂ) : ℂ :=
  w 0 ^ 2 - w 1 ^ 2 - w 2 ^ 2 - (m : ℂ) ^ 2

/-- Complex shell chart. -/
noncomputable def complexShellChart (m : ℝ) (w : Fin 3 → ℂ) : ComplexSpacetime :=
  (w 0, ![w 1, Complex.sqrt (complexShellRadicand m w), w 2])

/-- Complex shell chart domain with membership specified by `{w | 0 < (complexShellRadicand m
w).re}`. -/
def complexShellChartDomain (m : ℝ) : Set (Fin 3 → ℂ) :=
  {w | 0 < (complexShellRadicand m w).re}

theorem continuous_complexShellRadicand (m : ℝ) : Continuous (complexShellRadicand m) := by
  unfold complexShellRadicand
  fun_prop

theorem isOpen_complexShellChartDomain (m : ℝ) : IsOpen (complexShellChartDomain m) :=
  isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_complexShellRadicand m))

theorem complexShellChart_mem_shell (m : ℝ) (w : Fin 3 → ℂ) :
    complexShellChart m w ∈ complexShell m := by
  have hs : Complex.sqrt (complexShellRadicand m w) ^ 2 = complexShellRadicand m w := by
    exact Complex.cpow_ofNat_inv_pow _ 2
  change (w 0) ^ 2 - spatialDot
    ![w 1, Complex.sqrt (complexShellRadicand m w), w 2]
    ![w 1, Complex.sqrt (complexShellRadicand m w), w 2] = (m : ℂ) ^ 2
  rw [spatialDot_eq]
  change (w 0) ^ 2 - (w 1 * w 1 +
    Complex.sqrt (complexShellRadicand m w) * Complex.sqrt (complexShellRadicand m w) +
    w 2 * w 2) = (m : ℂ) ^ 2
  rw [← pow_two (Complex.sqrt (complexShellRadicand m w)), hs]
  dsimp only [complexShellRadicand]
  ring

theorem complexShellCoordinates_chart (m : ℝ) (w : Fin 3 → ℂ) :
    complexShellCoordinates (complexShellChart m w) = w := by
  rw [complexShellCoordinates_apply]
  ext i
  fin_cases i <;> rfl

theorem complexShellRadicand_coordinates {m : ℝ} {z : ComplexSpacetime}
    (hz : z ∈ complexShell m) :
    complexShellRadicand m (complexShellCoordinates z) = (z.2 1) ^ 2 := by
  change z.1 ^ 2 - spatialDot z.2 z.2 = (m : ℂ) ^ 2 at hz
  rw [spatialDot_eq] at hz
  rw [complexShellRadicand, complexShellCoordinates_apply]
  change z.1 ^ 2 - (z.2 0) ^ 2 - (z.2 2) ^ 2 - (m : ℂ) ^ 2 = (z.2 1) ^ 2
  linear_combination hz

theorem complexShellChart_coordinates {m : ℝ} {z : ComplexSpacetime}
    (hz : z ∈ complexShell m) (hpos : 0 < (z.2 1).re) :
    complexShellChart m (complexShellCoordinates z) = z := by
  have hs : Complex.sqrt (complexShellRadicand m (complexShellCoordinates z)) = z.2 1 := by
    rw [complexShellRadicand_coordinates hz]
    exact Complex.sq_cpow_two_inv hpos
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i
    · rfl
    · exact hs
    · rfl

theorem complexShellChart_second_re_pos {m : ℝ} {w : Fin 3 → ℂ}
    (hw : w ∈ complexShellChartDomain m) : 0 < ((complexShellChart m w).2 1).re := by
  change 0 < (Complex.sqrt (complexShellRadicand m w)).re
  rw [Complex.sqrt, Complex.cpow_inv_two_re]
  apply Real.sqrt_pos.mpr
  have hn := norm_nonneg (complexShellRadicand m w)
  change 0 < (complexShellRadicand m w).re at hw
  positivity

theorem differentiableAt_complexShellChart {m : ℝ} {w : Fin 3 → ℂ}
    (hw : w ∈ complexShellChartDomain m) : DifferentiableAt ℂ (complexShellChart m) w := by
  have hr : DifferentiableAt ℂ (complexShellRadicand m) w := by
    unfold complexShellRadicand
    fun_prop
  have hs := (Complex.differentiableAt_sqrt (Complex.mem_slitPlane_iff.mpr (Or.inl hw))).comp w hr
  apply DifferentiableAt.prodMk
  · exact (ContinuousLinearMap.proj (0 : Fin 3) : (Fin 3 → ℂ) →L[ℂ] ℂ).differentiableAt
  · apply differentiableAt_pi.mpr
    intro i
    fin_cases i
    · exact (ContinuousLinearMap.proj (1 : Fin 3) : (Fin 3 → ℂ) →L[ℂ] ℂ).differentiableAt
    · exact hs
    · exact (ContinuousLinearMap.proj (2 : Fin 3) : (Fin 3 → ℂ) →L[ℂ] ℂ).differentiableAt

end VacuumBellSeparation
