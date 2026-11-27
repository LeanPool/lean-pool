/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.CoherentCoordinates
public import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Totality of the actual coherent family

An ℓ² vector orthogonal to all exponential vectors has a scalar power
series identically zero. Analytic power-series uniqueness proves that all
its coordinates vanish. Thus coherent totality is derived, not assumed.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open Filter Topology
open scoped ComplexConjugate

/-- Coherent analysis series defined as `FormalMultilinearSeries.ofScalars ℂ (fun k => conj (x k) /
(Real.sqrt (k.factorial : ℝ) : ℂ))`. -/
noncomputable def coherentAnalysisSeries (x : OscillatorSpace) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun k => conj (x k) / (Real.sqrt (k.factorial : ℝ) : ℂ))

theorem hasSum_coherentAnalysis (x : OscillatorSpace) (z : ℂ) :
    HasSum (fun k => z ^ k • (coherentAnalysisSeries x).coeff k)
      (inner ℂ x (exponentialVector z)) := by
  have h := lp.hasSum_inner (𝕜 := ℂ) x (exponentialVector z)
  convert h using 1
  funext k
  simp only [coherentAnalysisSeries, FormalMultilinearSeries.coeff_ofScalars,
    smul_eq_mul, exponentialVector_apply, RCLike.inner_apply', coherentCoefficient]
  ring

theorem hasFPowerSeriesAt_coherentAnalysis (x : OscillatorSpace) :
    HasFPowerSeriesAt (fun z => inner ℂ x (exponentialVector z))
      (coherentAnalysisSeries x) 0 := by
  apply hasFPowerSeriesAt_iff.mpr
  exact Eventually.of_forall fun z => by simpa only [zero_add] using hasSum_coherentAnalysis x z

theorem eq_zero_of_inner_exponentialVector_eq_zero (x : OscillatorSpace)
    (hx : ∀ z, inner ℂ x (exponentialVector z) = 0) : x = 0 := by
  have hf : (fun z => inner ℂ x (exponentialVector z)) = (0 : ℂ → ℂ) := funext hx
  have hp : HasFPowerSeriesAt (0 : ℂ → ℂ) (coherentAnalysisSeries x) 0 := by
    rw [← hf]
    exact hasFPowerSeriesAt_coherentAnalysis x
  have hseries := hp.eq_zero
  apply lp.ext
  funext k
  have hk : (FormalMultilinearSeries.ofScalars ℂ
      (fun j => conj (x j) / (Real.sqrt (j.factorial : ℝ) : ℂ))) k = 0 :=
    congrFun hseries k
  have hc : conj (x k) / (Real.sqrt (k.factorial : ℝ) : ℂ) = 0 :=
    (FormalMultilinearSeries.ofScalars_eq_zero ℂ k).mp hk
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hden : (Real.sqrt (k.factorial : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hfac))
  have hz : conj (x k) = 0 := (div_eq_zero_iff).mp hc |>.resolve_right hden
  simpa using hz

theorem exponentialVector_dense_span :
    (Submodule.span ℂ (Set.range exponentialVector)).topologicalClosure = ⊤ := by
  let K := Submodule.span ℂ (Set.range exponentialVector)
  have horth : Kᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    apply eq_zero_of_inner_exponentialVector_eq_zero x
    intro z
    exact K.inner_left_of_mem_orthogonal (Submodule.subset_span ⟨z, rfl⟩) hx
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure, horth]

end VacuumBellSeparation.Gaussian
