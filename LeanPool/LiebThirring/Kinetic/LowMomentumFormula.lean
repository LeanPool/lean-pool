/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.ContractionIntegral
public import LeanPool.LiebThirring.Kinetic.ContractionState
public import LeanPool.LiebThirring.Kinetic.CurryingDensity
public import LeanPool.LiebThirring.Kinetic.LowMomentumTest
public import LeanPool.LiebThirring.Fourier.ContractionFourier

/-!
# Pointwise low fields and one-particle contraction

The negative Fourier phase in the one-spin test becomes the positive
inverse phase under the adjoint contraction. The equality is in the Hilbert
fiber at every spatial point, without pointwise claims about state slices.
-/

public section

open MeasureTheory
open scoped FourierTransform ComplexConjugate

namespace LiebThirring

variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A one-spin negative-phase Fourier test contracts to the continuous low
field component. The representative premise characterizes the test, rather
than assuming a low-momentum estimate. -/
theorem lowFourierField_component_eq_of_fourier_ae
    (h : Lp (PiLp 2 (fun _ : ι => H)) 2 (volume : Measure Position))
    (E : ℝ) (hE : 0 ≤ E) (x : Position) (s : ι)
    (g : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure Position))
    (hg : ((𝓕 g : Lp (EuclideanSpace ℂ ι) 2 volume) : Position → EuclideanSpace ℂ ι) =ᵐ[volume]
      (lowMomentumRegion E).indicator (fun ξ =>
        EuclideanSpace.single s (Real.fourierChar (-inner ℝ ξ x) : ℂ))) :
    lowFourierField h E x s = tensorContraction (H := H) g h := by
  apply ext_inner_left ℂ
  intro v
  rw [← Fourier.tensorContraction_fourier, inner_tensorContraction]
  let P : PiLp 2 (fun _ : ι => H) →L[ℂ] ℂ :=
    (innerSL ℂ v).comp (PiLp.proj (𝕜 := ℂ) 2 (fun _ : ι => H) s)
  have hraw := integrable_lowFourierField h E hE x
  have hcomm := P.integral_comp_comm hraw
  have hlow : lowFourierField h E x = ∫ ξ : Position,
      Real.fourierChar (inner ℝ ξ x) •
        (lowMomentumRegion E).indicator
          (Lp.fourierTransformₗᵢ Position (PiLp 2 (fun _ : ι => H)) h : Position → PiLp 2 (fun _ :
            ι => H)) ξ := by
    rw [lowFourierField, Real.fourierInv_eq]
  change P (lowFourierField h E x) = _
  rw [hlow]
  rw [← hcomm]
  apply integral_congr_ae
  filter_upwards [hg] with ξ hξ
  rw [hξ]
  by_cases hmem : ξ ∈ lowMomentumRegion E
  · simp [P, Set.indicator_of_mem hmem, Circle.smul_def, EuclideanSpace.single,
      apply_ite, ite_mul]
    rfl
  · simp [P, Set.indicator_of_notMem hmem]

/-- The exact the low-momentum bound test contracts to the scaled density-field component. -/
theorem lowFourierField_density_component_eq {N q : ℕ} (i : Fin N)
    (ψ : State N q) (E : ℝ) (hE : 0 ≤ E) (x : Position) (s : Fin q) :
    lowFourierField (densityField i ψ) E x s =
      (Real.sqrt N : ℂ) • oneParticleContraction i (lowMomentumTest E x s hE) ψ := by
  calc
    _ = tensorContraction (H := RestState i q) (lowMomentumTest E x s hE)
        (densityField i ψ) :=
      lowFourierField_component_eq_of_fourier_ae _ E hE x s _
        (lowMomentumTest_fourier_ae E hE x s)
    _ = _ := by
      change tensorContraction (H := RestState i q) (lowMomentumTest E x s hE)
        ((Real.sqrt N : ℂ) • oneParticleCurrying i ψ) =
          (Real.sqrt N : ℂ) • tensorContraction (H := RestState i q)
            (lowMomentumTest E x s hE) (oneParticleCurrying i ψ)
      exact map_smul _ _ _

/-- Squared component norm in the exact normalization used by the Pauli bound. -/
theorem lowFourierField_density_component_norm_sq {N q : ℕ} (i : Fin N)
    (ψ : State N q) (E : ℝ) (hE : 0 ≤ E) (x : Position) (s : Fin q) :
    ‖lowFourierField (densityField i ψ) E x s‖ ^ 2 =
      (N : ℝ) * ‖oneParticleContraction i (lowMomentumTest E x s hE) ψ‖ ^ 2 := by
  rw [lowFourierField_density_component_eq, norm_smul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (Nat.cast_nonneg N)]

end LiebThirring
end
