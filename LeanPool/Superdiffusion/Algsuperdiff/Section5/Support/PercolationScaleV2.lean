/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section5.PercolationGFv2
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.OnePointChainStreamFull
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.ExitTimeHomogenizationJointEvent

/-!
# PercolationScaleV2

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The percolation scale from the successor estimate

The successor chains-of-good-cubes estimate is stated with injection constant `1`.
This module transports its crossing count to an arbitrary positive injection constant by the
accuracy rescaling of the joint event.  The resulting supplier has the successor logarithmic
floor and tail exponent.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Field
open Algsuperdiff.Section5.Provider
open Algsuperdiff.Section5.Trace
open DivergenceFormProcess.Form
open HCPolySupport MeasureTheory
open MarkovProcess
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ}

/-- The successor percolation estimate, transported from injection constant `1` to an
arbitrary positive injection constant.  Rescaling by `K = max 1 Cinj` weakens the anchor's
accuracy floor by the factor `K` and its exponential rate by the factor `K ^ 2`. -/
theorem exists_measurable_scale_ae_crossing_v2
    (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gamma0 c C Creg : ℝ, 0 < gamma0 ∧ 0 < c ∧ 0 < C ∧ 0 < Creg ∧
      ∀ Cinj : ℝ, 0 < Cinj →
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ ep : ℝ, ep ∈ Set.Icc ((C * max 1 Cinj) * Real.sqrt M.gamma *
          Real.rpow |Real.log M.gamma| (7 / 2)) (1 / 4) →
      ∀ m : ℤ, ∃ Y : Cutoff.CutoffSample d → ℕ,
        Measurable Y ∧
        (∀ N : ℕ, 1 ≤ N →
          (Cutoff.cutoffSampleLaw M).toMeasure {omega | N ≤ Y omega} ≤
            ENNReal.ofReal (Real.exp (-((c / (max 1 Cinj) ^ (2 : ℕ)) *
              ep ^ (2 : ℕ) * M.gamma⁻¹ *
              |Real.log M.gamma| ^ (-6 : ℤ) * (3 : ℝ) ^ N)))) ∧
        ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ n : ℤ,
          n ≤ m - (Y omega : ℤ) →
          ∀ (N : ℕ) (x : ℕ → Fin d → ℤ),
            Provider.Percolation.IsLatticePath x N →
            x 0 ∈ Provider.Percolation.cubeAt (m - n).toNat 0 →
            x N ∉ Provider.Percolation.cubeAt ((m - n).toNat + 1) 0 →
            (3 / 4 : ℝ) * (3 : ℝ) ^ (m - n).toNat ≤
              ((qSiteCount M Creg Cinj n ep
                (Algsuperdiff.Section5.Percolation.pathSites N x) omega : ℕ) : ℝ) := by
  obtain ⟨gamma0, c0, C0, Creg, hgamma0, hc0, hC0, hCreg, hmain⟩ :=
    Algsuperdiff.Frozen.Section5.percolation_GF_v2 d cstar hcstar 1 zero_lt_one
  refine ⟨gamma0, c0, C0, Creg, hgamma0, hc0, hC0, hCreg, ?_⟩
  intro Cinj hCinj
  let K : ℝ := max 1 Cinj
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left 1 Cinj)
  have hK1 : 1 ≤ K := le_max_left 1 Cinj
  intro M hcstarM hgamma ep hep m
  have hep0 : 0 ≤ ep := by
    have hlower : 0 ≤ (C0 * max 1 Cinj) * Real.sqrt M.gamma *
        Real.rpow |Real.log M.gamma| (7 / 2) :=
      mul_nonneg (mul_nonneg (mul_nonneg hC0.le (le_max_of_le_left zero_le_one))
        (Real.sqrt_nonneg _))
        (Real.rpow_nonneg (abs_nonneg _) _)
    exact hlower.trans hep.1
  have heprescaled : ep / K ∈ Set.Icc
      (C0 * Real.sqrt M.gamma * Real.rpow |Real.log M.gamma| (7 / 2)) (1 / 4) := by
    constructor
    · rw [le_div_iff₀ hK]
      calc
        C0 * Real.sqrt M.gamma * Real.rpow |Real.log M.gamma| (7 / 2) * K =
            (C0 * max 1 Cinj) * Real.sqrt M.gamma *
              Real.rpow |Real.log M.gamma| (7 / 2) := by
              dsimp only [K]
              ring
        _ ≤ ep := hep.1
    · have hdiv : ep / K ≤ ep := by
        rw [div_le_iff₀ hK]
        nlinarith only [hep0, hK1]
      exact hdiv.trans hep.2
  obtain ⟨Y, hYmeas, hYtail, hYcross⟩ :=
    hmain M hcstarM hgamma (ep / K) heprescaled m
  refine ⟨Y, hYmeas, ?_, ?_⟩
  · intro N hN
    refine (hYtail N hN).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    congr 2
    dsimp only [K]
    field_simp
  · filter_upwards [hYcross] with omega homega
    intro n hn N x hpath h0 hN
    refine (homega n hn N x hpath h0 hN).trans ?_
    exact_mod_cast qSiteCount_mono M Creg n
      (Algsuperdiff.Section5.Percolation.pathSites N x) omega
      (fun z => qEvent_rescaled_accuracy_subset M Creg hCinj n
        (rescaledLatticePoint n z) hep0)

end

end Algsuperdiff.Section5.Support
