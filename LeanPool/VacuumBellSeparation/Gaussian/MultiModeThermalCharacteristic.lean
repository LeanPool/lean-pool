/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeThermalState
public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeWeylProduct
public import LeanPool.VacuumBellSeparation.Gaussian.QuadratureNormalization

/-!
# The actual finite-mode thermal characteristic function

The genuine Weyl operator's number-basis diagonal factors over all modes.
Absolute finite-tuple Fubini therefore evaluates the actual complex thermal
state as a product of the already proved one-mode expectations. This is a
statement about the constructed infinite-dimensional operators and states,
including pure factors and the zero-mode case.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

theorem multiThermalState_oscillatorWeyl_product {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (z : MultiModePhaseSpace m) :
    multiThermalState hq₀ hq₁ (multiOscillatorWeyl z) =
      ∏ j, thermalState (hq₀ j) (hq₁ j) (oscillatorWeyl (z j)) := by
  let f : Fin m → ℕ → ℂ := fun j n =>
    (thermalWeight (q j) n : ℂ) * inner ℂ (numberBasis n) (oscillatorWeyl (z j) (numberBasis n))
  have hs (j : Fin m) : HasSum (f j) (thermalState (hq₀ j) (hq₁ j) (oscillatorWeyl (z j))) :=
    (summable_diagonalExpectation_terms numberBasis
      (hasSum_thermalWeight (hq₀ j) (hq₁ j)).summable (oscillatorWeyl (z j))).hasSum
  have hp := hasSum_fin_complex_product m f _ (fun j => (hs j).summable.norm) hs
  apply (hasSum_multiThermalState hq₀ hq₁ (multiOscillatorWeyl z)).unique
  convert hp using 1
  funext k
  rw [multiOscillatorWeyl_number_diagonal, multiModeThermalWeight,
    Complex.ofReal_prod, ← Finset.prod_mul_distrib]

/-- The characteristic of the actual product thermal density in canonical
complex phase coordinates. The physical quadrature variance is `v(q)`. -/
theorem multiThermalState_oscillatorWeyl {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (z : MultiModePhaseSpace m) :
    multiThermalState hq₀ hq₁ (multiOscillatorWeyl z) =
      Complex.exp ((-∑ j, thermalQuadratureVariance (q j) * ‖z j‖ ^ 2 : ℝ) : ℂ) := by
  rw [multiThermalState_oscillatorWeyl_product hq₀ hq₁]
  simp_rw [thermalState_oscillatorWeyl]
  rw [← Complex.exp_sum, ← Complex.ofReal_sum]
  congr 2
  simp only [thermalQuadratureVariance, neg_mul, Finset.sum_neg_distrib]

/-- Multi quadrature label defined as `WithLp.toLp 2 (fun j => quadratureLabel (v j))`. -/
noncomputable def multiQuadratureLabel {m : ℕ} (v : Fin m → ℝ × ℝ) : MultiModePhaseSpace m :=
  WithLp.toLp 2 (fun j => quadratureLabel (v j))

/-- Multi quadrature Weyl obtained from `multiOscillatorWeyl`. -/
noncomputable def multiQuadratureWeyl {m : ℕ} (v : Fin m → ℝ × ℝ) :
    MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m :=
  multiOscillatorWeyl (multiQuadratureLabel v)

/-- Literal real-quadrature normalization of the actual finite-mode
characteristic, with vacuum variance `1/2` in every pure mode. -/
theorem multiThermalState_quadratureWeyl {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (v : Fin m → ℝ × ℝ) :
    multiThermalState hq₀ hq₁ (multiQuadratureWeyl v) =
      Complex.exp ((-(1 / 2) * ∑ j, thermalQuadratureVariance (q j) *
        ((v j).1 ^ 2 + (v j).2 ^ 2) : ℝ) : ℂ) := by
  rw [multiQuadratureWeyl, multiThermalState_oscillatorWeyl hq₀ hq₁]
  apply congrArg (fun r : ℝ => Complex.exp (r : ℂ))
  simp only [multiQuadratureLabel, PiLp.toLp_apply, quadratureLabel_norm_sq]
  rw [Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

end VacuumBellSeparation.Gaussian
