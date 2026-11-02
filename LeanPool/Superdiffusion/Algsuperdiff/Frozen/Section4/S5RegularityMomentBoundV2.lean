/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.PercolationScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Dirichlet
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.RegularityMoment.SuccessorMoment

/-!
# S5RegularityMomentBoundV2

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support
open HCPolySupport MeasureTheory
open scoped ENNReal

/-!
# Moments of the localized regularity — [ABK] Section 5.1 (`e.reg.rv.Sfive.moment.bound`)

Source: `references/algsuperdiff.tex:12861-12866`.

For a disorder model of strength `gamma` small enough there are constants `c`
and `C` such that, at every scale `n` and every centre `y`, the localized
regularity `localizedRegularity M n y` of the cube `y + □_n` satisfies

`𝔼[X^p]^{1/p} ≤ C` at the single exponent `p = c gamma⁻¹ |log gamma|⁻⁶`.

The localized regularity is the normalized `1/2`-Hölder seminorm of the
continuous representative of the rough-field Dirichlet solution on the cube,
taken as a supremum over the normalized forcing class.

## Where the exponent comes from

Almost surely the localized regularity is at most `C 3^{X/2} (1 + localizedError)`
for the minimal scale `X` of the local Hölder estimate, so a moment of the
localized regularity at exponent `p` costs a moment of the localized error at an
exponent at least `p`. Those moments are the content of
`Algsuperdiff.Frozen.Section4.s5_error_moment_bound`, which holds in the range
`p ≤ C⁻¹ gamma⁻¹ |log gamma|⁻¹` and whose amplitude at the top of that range
grows like `|log gamma|^{5/2}` rather than staying bounded. Each of the two
costs a power of `|log gamma|`, which is how the exponent above sits below
`gamma⁻¹` by the sixth power of `|log gamma|`. Sections 5.1 and 5.2 read this
bound only through a single-site estimate at the exponent class
`c ep² gamma⁻¹ |log gamma|⁻⁶`, which is exactly the class carried here.

## Reading of the statement

* **`p`-th-power form.** As for the error moments, the bound is stated as
  `∫⁻ X^p ≤ (ENNReal.ofReal C)^p` rather than through the `p`-th root of the
  integral; the two are equivalent and the power form is the one an
  `ℝ≥0∞`-valued integral states without a division.
* **Two constants, one exponent.** The source writes literally two constants,
  the exponent and the bound `C`; both may depend on the dimension `d` and on
  the value `cstar` of the model's ellipticity parameter `c⋆`, that is
  `c = c(d, c⋆)` and `C = C(d, c⋆)`. No constant of Section 5 enters, and the
  exponent is a single one rather than a range. The range form follows from it,
  the sample law being a probability measure.
* **The Hölder exponent is not a binder.** The exponent `1/2` of the seminorm is
  carried inside `localizedRegularity` itself; the local Hölder estimate is
  instantiated at `alpha = 1/2` on the same cube to produce this bound, and no
  exponent binder appears in the statement.
* **Small-disorder premise.** The hypothesis `M.gamma ≤ gamma0` is the standing
  regime `gamma ≤ gamma0(d, c⋆)` in which the estimates of Sections 3 and 4 are
  stated (`references/algsuperdiff.tex:372`), made explicit here so that the
  type shows it.
* **Cubes.** Cubes are indexed by `ℤ` and centred at an arbitrary `y`, the form
  in which Section 5.1 uses the estimate.

## Conventions

The conventions this bound inherits are those of the two estimates its proof
consumes: the local Hölder estimate, which is taken at zero boundary datum with
the seminorm on the full cube, and the moment bound for the localized error,
whose amplitude carries the factor `√p + √|log gamma|`.

Proved; reduces to the standard axioms.
-/

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section4.s5_regularity_moment_bound_v2
    (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gamma0 c C : ℝ, 0 < gamma0 ∧ 0 < c ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ (n : ℤ) (y : Vec d),
        (∫⁻ omega, localizedRegularity M n y omega ^
              (c * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ))
            ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
          ENNReal.ofReal C ^ (c * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ))
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section4.Provider.s5_regularity_moment_bound_v2_provider d cstar hcstar
