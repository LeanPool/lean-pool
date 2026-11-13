/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle

/-! # Parseval's identity for finite families of distinct Fourier frequencies -/

open MeasureTheory Complex
open scoped BigOperators

namespace PhaseRetrieval

/-- Parseval's identity for a finite Fourier sum with injectively indexed frequencies. -/
public theorem integral_norm_sq_fourier_sum {ι : Type*} [Fintype ι]
    {period : ℝ} [Fact (0 < period)] (frequencies : ι ↪ ℤ) (coefficients : ι → ℂ) :
    (∫ t : AddCircle period,
      ‖∑ i : ι, coefficients i * fourier (frequencies i) t‖ ^ 2 ∂AddCircle.haarAddCircle) =
      ∑ i : ι, ‖coefficients i‖ ^ 2 := by
  let polynomial : C(AddCircle period, ℂ) :=
    ∑ i : ι, coefficients i • fourier (frequencies i)
  let vector := (ContinuousMap.toLp (α := AddCircle period) 2 AddCircle.haarAddCircle ℂ)
    polynomial
  have hvector : vector = ∑ i : ι, coefficients i • fourierLp 2 (frequencies i) := by
    simp only [vector, polynomial, fourierLp, map_sum, map_smul]
  have horth : Orthonormal ℂ (fun i : ι => fourierLp (T := period) 2 (frequencies i)) :=
    (orthonormal_fourier (T := period)).comp frequencies frequencies.injective
  have hinner : inner ℂ vector vector = (∑ i : ι, ‖coefficients i‖ ^ 2 : ℝ) := by
    rw [hvector, horth.inner_sum coefficients coefficients Finset.univ, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hae := ContinuousMap.coeFn_toLp
    (μ := AddCircle.haarAddCircle) (𝕜 := ℂ) (p := 2) polynomial
  have hint := L2.integrable_inner (𝕜 := ℂ) vector vector
  calc
    (∫ t : AddCircle period,
        ‖∑ i : ι, coefficients i * fourier (frequencies i) t‖ ^ 2 ∂AddCircle.haarAddCircle) =
        (inner ℂ vector vector).re := by
      rw [L2.inner_def]
      change _ = Complex.reCLM _
      rw [← ContinuousLinearMap.integral_comp_comm _ hint]
      apply integral_congr_ae
      filter_upwards [hae] with t ht
      have hre : Complex.reCLM (inner ℂ ((vector : AddCircle period → ℂ) t)
          ((vector : AddCircle period → ℂ) t)) =
          ‖(vector : AddCircle period → ℂ) t‖ ^ 2 :=
        @inner_self_eq_norm_sq ℂ ℂ _ _ _ _
      rw [hre, show (vector : AddCircle period → ℂ) t = polynomial t from ht]
      simp only [polynomial, ContinuousMap.coe_sum, Finset.sum_apply,
        ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
    _ = ∑ i : ι, ‖coefficients i‖ ^ 2 := by rw [hinner, Complex.ofReal_re]

end PhaseRetrieval
