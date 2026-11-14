/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Percolation.PathBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.PercolationScaleTail
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SiteTailCalibration

/-!
# PercolationAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The crossing bridge for the chains of good cubes

Section 5.2 asserts that, for every maximal scale `m`, there is an integer-valued
random variable `Y_m` with an exponential tail such that below the scale
`m - Y_m` every rescaled lattice path crossing the annulus between the cubes
`□_{m-n}` and `□_{m-n+1}` meets the good event `Q(z + □_n, ε)` at at least
three quarters of `3^{m-n}` of its sites.

One step of that argument is recorded here: the passage from a crossing that is
light for the good event `Q` to a crossing that is light for the site-indexed
family `shiftedSiteBadEventFive`, the family the abstract percolation path
estimate is applied to.  The complement of a bad site is contained in `Q`, so a
path visiting few sites of `Q` visits few complements of bad sites, and the
count the path estimate controls bounds `qSiteCount` from below.

## Main results

* `lightQPathEvent_subset` — a light crossing of the annulus is a light crossing
  for the site-indexed family.

## References

* ABK26, the chains of good cubes of Section 5.2.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support
open HCPolySupport MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

section Bridge

variable {d : ℕ}

/-- **A light crossing of the annulus is a light crossing for the site family.**
The complement of the union over scales of the bad events at a site is contained
in `Q` at that site, so the good-vertex count of the percolation estimate is at
most the count of sites at which `Q` occurs.  The two readings of a crossing —
as a function on an initial segment and as a list of adjacent sites — are
identified by `exists_crossing_iff`, which carries the set of visited sites
across unchanged. -/
theorem lightQPathEvent_subset (M : ABKModel d) {Creg Cinj C0 ep : ℝ} (m : ℤ) (k : ℕ)
    (hC0 : 0 ≤ C0) (hep : 0 ≤ ep) (hthr : C0 * (1 - shellDecayBase)⁻¹ ≤ Cinj⁻¹) :
    lightQPathEvent M Creg Cinj m ep k ⊆
      {omega : Cutoff.CutoffSample d | ∃ Gamma : List (Percolation.Site d),
        Percolation.IsPathFrom k Gamma ∧
          ∑ z ∈ Gamma.toFinset,
            (Percolation.badSet
              (shiftedSiteBadEventFive M Creg C0 ep (m - (k : ℤ))) z)ᶜ.indicator
              (fun _ => (1 : ℝ)) omega < (1 - (1 / 4 : ℝ)) * 3 ^ k} := by
  intro omega homega
  obtain ⟨Gamma, hGamma, hcount⟩ :=
    (Percolation.exists_crossing_iff k
      (fun S => ((qSiteCount M Creg Cinj (m - (k : ℤ)) ep S omega : ℕ) : ℝ) <
        (3 : ℝ) / 4 * (3 : ℝ) ^ k)).1 homega
  refine ⟨Gamma, hGamma, ?_⟩
  have hle : ∑ z ∈ Gamma.toFinset,
      (Percolation.badSet
        (shiftedSiteBadEventFive M Creg C0 ep (m - (k : ℤ))) z)ᶜ.indicator
        (fun _ => (1 : ℝ)) omega ≤
      ((qSiteCount M Creg Cinj (m - (k : ℤ)) ep Gamma.toFinset omega : ℕ) : ℝ) := by
    rw [qSiteCount_eq_sum_indicator]
    refine Finset.sum_le_sum fun z _ => ?_
    exact Set.indicator_le_indicator_of_subset
      (compl_badSet_subset_qEvent M (m - (k : ℤ)) z hC0 hep hthr)
      (fun _ => zero_le_one) omega
  have h34 : (1 - (1 / 4 : ℝ)) * 3 ^ k = (3 : ℝ) / 4 * (3 : ℝ) ^ k := by norm_num
  rw [h34]
  exact lt_of_le_of_lt hle hcount

end Bridge

end

end Algsuperdiff.Section5.Provider
