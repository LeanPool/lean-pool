/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.FiniteRenyiStripBoundary

/-!
# Actual finite Schatten interpolation by the three-lines theorem

For an actual strictly positive dual test X of Hilbert--Schmidt norm one,
the constructed entire strip function has the correct boundary norms.
Applying the pinned Hadamard theorem gives the dual interpolation bound.
The dual-test normalization is explicit here; choosing the actual
normalized positive middle sandwich is a separate finite algebra step.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix Set
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator ComplexConjugate ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem norm_finiteRenyiStripFunction_one_edge_normalized {ρ σ X : Matrix ι ι ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (hX : X.PosDef) (τ : ℝ)
    {p q : ℝ} (hpq : p.HolderConjugate q) (hτq : 2 * τ * q = 2)
    (hXt : (X ^ (2 : ℝ)).trace.re = 1) {z : ℂ} (hz : z.re = 1) :
    ‖finiteRenyiStripFunction hσ hX ρ τ z‖ ≤
      ((finiteRenyiSandwich ρ σ τ ^ p).trace.re) ^ (1 / p) := by
  have h := ennreal_finiteRenyiStripFunction_one_edge hρ hσ hX τ hpq hz
  simp only [hτq, finitePositivePowerTrace, hXt, ENNReal.ofReal_one, ENNReal.one_rpow, mul_one] at h
  have hfin : finitePositivePowerTrace (finiteRenyiSandwich ρ σ τ) p ^ (1 / p) ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg hpq.one_div_nonneg (finitePositivePowerTrace_lt_top _ _).ne).ne
  have hreal := ENNReal.toReal_mono hfin h
  simpa only [ENNReal.toReal_ofReal (norm_nonneg _), ← ENNReal.toReal_rpow,
    finitePositivePowerTrace,
    ENNReal.toReal_ofReal (real_trace_positive_rpow_nonneg
      (finiteRenyiSandwich_posDef hρ hσ τ) p)] using hreal

theorem finiteRenyiStripFunction_at_interpolation {ρ σ X : Matrix ι ι ℂ}
    (hσ : σ.PosDef) (hX : X.PosDef) {τ θ : ℝ} (hτθ : 2 * τ * θ = 1) :
    finiteRenyiStripFunction hσ hX ρ τ (θ : ℂ) =
      (X * finiteRenyiSandwich ρ σ (1 / 2)).trace := by
  have hx : ((2 * τ : ℝ) : ℂ) * (θ : ℂ) = 1 := by exact_mod_cast hτθ
  have hs : ((-τ / 2 : ℝ) : ℂ) * (θ : ℂ) = ((-(1 / 2 : ℝ) / 2 : ℝ) : ℂ) := by
    have h : (-τ / 2) * θ = -(1 / 2 : ℝ) / 2 := by nlinarith [hτθ]
    exact_mod_cast h
  unfold finiteRenyiStripFunction finiteRenyiSandwich
  rw [hx, hs, positiveMatrixComplexPower_one, positiveMatrixComplexPower_real]
  congr 1
  noncomm_ring

theorem finiteRenyi_dual_interpolation {ρ σ X : Matrix ι ι ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (hX : X.PosDef)
    {p q τ θ : ℝ} (hpq : p.HolderConjugate q) (hτq : 2 * τ * q = 2)
    (hθ : θ ∈ Icc (0 : ℝ) 1) (hτθ : 2 * τ * θ = 1)
    (hXt : (X ^ (2 : ℝ)).trace.re = 1) :
    ‖(X * finiteRenyiSandwich ρ σ (1 / 2)).trace‖ ≤
      ρ.trace.re ^ (1 - θ) *
        ((finiteRenyiSandwich ρ σ τ ^ p).trace.re) ^ (θ / p) := by
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
    (finiteRenyiStripFunction hσ hX ρ τ)
    (z := (θ : ℂ)) (a := ρ.trace.re)
    (b := ((finiteRenyiSandwich ρ σ τ ^ p).trace.re) ^ (1 / p))
    (by simpa only [Complex.HadamardThreeLines.verticalClosedStrip, mem_preimage,
      Complex.ofReal_re] using hθ)
    (differentiable_finiteRenyiStripFunction hσ hX ρ τ).diffContOnCl
    (finiteRenyiStripFunction_bounded hσ hX ρ τ)
    (fun z hz => norm_finiteRenyiStripFunction_zero_edge hρ hσ hX τ (Set.mem_singleton_iff.mp hz))
    (fun z hz => norm_finiteRenyiStripFunction_one_edge_normalized hρ hσ hX τ hpq hτq hXt
      (Set.mem_singleton_iff.mp hz))
  rw [finiteRenyiStripFunction_at_interpolation hσ hX hτθ, Complex.ofReal_re] at h
  have hN := real_trace_positive_rpow_nonneg (finiteRenyiSandwich_posDef hρ hσ τ) p
  have he : (((finiteRenyiSandwich ρ σ τ ^ p).trace.re) ^ (1 / p)) ^ θ =
      ((finiteRenyiSandwich ρ σ τ ^ p).trace.re) ^ (θ / p) := by
    rw [← Real.rpow_mul hN]
    congr 1
    ring
  rwa [he] at h

end VacuumBellSeparation.Gaussian
