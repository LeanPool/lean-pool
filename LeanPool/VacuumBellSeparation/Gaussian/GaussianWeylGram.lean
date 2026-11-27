/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.RealCoordinateWeyl
public import LeanPool.VacuumBellSeparation.Gaussian.DensityExpectationGram
public import LeanPool.VacuumBellSeparation.Gaussian.GaussianDifferenceQuotient

/-!
# Actual Gaussian finite differences of Weyl operators

At positive time s the displacement amplitude is sqrt(s). The actual
positive density Gram of W(sqrt(s)x)-I has the exact three-exponential
formula. Thus its divided limit can establish uncertainty without using
unbounded position/momentum operators or postulating a positive kernel.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexConjugate

variable {m : ℕ}

/-- Gaussian Weyl difference given by `realCoordinateWeyl (Real.sqrt s • x) - 1`. -/
def gaussianWeylDifference (s : ℝ) (x : Fin m × Fin 2 → ℝ) :
    MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m :=
  realCoordinateWeyl (Real.sqrt s • x) - 1

/-- Gaussian Weyl cross exponent. -/
def gaussianWeylCrossExponent
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (x y : Fin m × Fin 2 → ℝ) : ℂ :=
  ((-((y - x) ⬝ᵥ (V *ᵥ (y - x))) : ℝ) : ℂ) +
    Complex.I * ((x ⬝ᵥ (modeSymplecticForm *ᵥ y) : ℝ) : ℂ)

theorem gaussianWeylDifference_expectation
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hG : HasGaussianDisplacementCharacteristic A V)
    {s : ℝ} (hs : 0 ≤ s) (x y : Fin m × Fin 2 → ℝ) :
    densityExpectation (multiModeNumberBasis m) A
      (star (gaussianWeylDifference s x) * gaussianWeylDifference s y) =
      gaussianGramDifference (gaussianWeylCrossExponent V x y)
        ((-(x ⬝ᵥ (V *ᵥ x)) : ℝ) : ℂ) ((-(y ⬝ᵥ (V *ᵥ y)) : ℝ) : ℂ) s := by
  let φ := densityExpectationCLM (multiModeNumberBasis m) hA
  let t := Real.sqrt s
  have htt : t * t = s := Real.mul_self_sqrt hs
  have hφ (v : Fin m × Fin 2 → ℝ) :
      φ (realCoordinateWeyl v) = Complex.exp ((-(v ⬝ᵥ (V *ᵥ v)) : ℝ) : ℂ) :=
    gaussianDisplacement_realCoordinateWeyl hG v
  have hφ₁ : φ 1 = 1 := by
    change densityExpectation (multiModeNumberBasis m) A 1 = 1
    rw [densityExpectation_one _ hA, gaussianDisplacement_positiveTrace_eq_one hA hG,
      ENNReal.toReal_one, Complex.ofReal_one]
  have hplus : -(t • x) + t • y = t • (y - x) := by module
  have hphase : (-(t • x)) ⬝ᵥ (modeSymplecticForm *ᵥ (t • y)) =
      -s * (x ⬝ᵥ (modeSymplecticForm *ᵥ y)) := by
    rw [← neg_smul, real_bilinear_smul, neg_mul, htt]
  have hquad (v : Fin m × Fin 2 → ℝ) :
      (t • v) ⬝ᵥ (V *ᵥ (t • v)) = s * (v ⬝ᵥ (V *ᵥ v)) := by
    rw [real_bilinear_smul, htt]
  have hfirst : φ (realCoordinateWeyl (-(t • x)) * realCoordinateWeyl (t • y)) =
      Complex.exp ((s : ℂ) * gaussianWeylCrossExponent V x y) := by
    rw [realCoordinateWeyl_mul, map_smul, hφ, hplus, hquad, hphase,
      smul_eq_mul, ← Complex.exp_add]
    congr 1
    unfold gaussianWeylCrossExponent
    push_cast
    ring
  have hx : φ (realCoordinateWeyl (-(t • x))) =
      Complex.exp ((s : ℂ) * ((-(x ⬝ᵥ (V *ᵥ x)) : ℝ) : ℂ)) := by
    rw [hφ]
    simp only [Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg, hquad]
    congr 1
    push_cast
    ring
  have hy : φ (realCoordinateWeyl (t • y)) =
      Complex.exp ((s : ℂ) * ((-(y ⬝ᵥ (V *ᵥ y)) : ℝ) : ℂ)) := by
    rw [hφ, hquad]
    congr 1
    push_cast
    ring
  change φ (star (realCoordinateWeyl (t • x) - 1) * (realCoordinateWeyl (t • y) - 1)) = _
  rw [star_sub, star_one, realCoordinateWeyl_star, sub_mul, mul_sub, one_mul,
    mul_one, map_sub, map_sub, map_sub, hfirst, hx, hy, hφ₁]
  unfold gaussianGramDifference
  ring

end VacuumBellSeparation.Gaussian
