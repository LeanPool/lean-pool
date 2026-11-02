/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.PercolationScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Dirichlet
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.S5ErrorMomentBoundProvider

/-!
# S5ErrorMomentBound

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support
open HCPolySupport MeasureTheory
open scoped ENNReal

/-!
# Moments of the localized error — [ABK] Section 5.1 (`e.error.rv.Sfive.moment.bound`)

Source: `references/algsuperdiff.tex:12854-12860`.

For a disorder model of strength `gamma` small enough there is a constant `C`
such that, at every scale `n` and every centre `y`, the localized error
`localizedError M n y` of the cube `y + □_n` has, for every exponent
`p ∈ [1, C⁻¹ gamma⁻¹ |log gamma|⁻¹]`, the moment bound

`𝔼[E^p]^{1/p} ≤ C (√p + √|log gamma|) √gamma |log gamma|³`.

The localized error is the normalized `L^∞` distance between the rough-field
Dirichlet solution on the cube and the solution of the comparator problem with
coefficient `σ_n I`, taken as a supremum over the normalized forcing class.

## Reading of the statement

* **`p`-th-power form.** The bound is stated as
  `∫⁻ E^p ≤ (ENNReal.ofReal amplitude)^p` rather than through the `p`-th root of
  the integral: the two are equivalent, and the power form is the one an
  `ℝ≥0∞`-valued integral states without a division.
* **One constant.** A single `C` serves both the amplitude and the upper end of
  the range of `p`, exactly as printed. It may depend on the dimension `d` and
  on the value `cstar` of the model's ellipticity parameter `c⋆`, that is
  `C = C(d, c⋆)`; no constant of Section 5 enters.
* **Small-disorder premise.** The hypothesis `M.gamma ≤ gamma0` is the standing
  regime `gamma ≤ gamma0(d, c⋆)` in which the estimates of Sections 3 and 4 are
  stated (`references/algsuperdiff.tex:372`), made explicit here so that the
  type shows it.
* **Cubes.** Cubes are indexed by `ℤ` and centred at an arbitrary `y`, the form
  in which Section 5.1 uses the estimate; the display of Section 4 is the case
  of a cube centred at the origin, and the two are related by translation
  covariance of the model.

## Conventions

* The amplitude carries the factor `√p + √|log gamma|`, as in the paper. It is
  the factor the generator renormalization theorem of Section 4 supplies for the
  same error amplitude, and it is what the percolation estimate of Section 5.2
  consumes.
* The absolute value is required at the odd power: `log gamma < 0` over the
  whole admissible range, so an unsigned cube would make the amplitude negative
  and the bound vacuously false.

Proved; reduces to the standard axioms.
-/

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section4.s5_error_moment_bound
    (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ (p : ℝ) (n : ℤ) (y : Vec d), 1 ≤ p →
          p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
          (∫⁻ omega, localizedError M n y omega ^ p ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
            ENNReal.ofReal (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
              Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ p
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section4.Provider.s5_error_moment_bound_provider d cstar hcstar
