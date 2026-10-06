/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.PhysicalFrameTransport

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.ConstantAbsorptionIntoLength

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The `C₀` absorptions: absorbing the per-`g` constants into the length

bound carries the constant `Cscheduled` produced by
the flux scheduled rate at the witness, which is

```
Cscheduled = 2 · outputFactor · Cdual · Cbesov d · √Kflux · √hardyConstant
```

(`HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.UniformFluxScheduledRateExtraction`, with
`Cbesov d = fractionalDualToBesovConstant d` and
`D = Cbesov d ^ 2`).  The restated hole, on the other hand, needs a **single**
`C₀` with `∀ s₀ ρ Rad, 0 < C₀ s₀ ρ Rad`, fixed before `g` and before the domain.

The factors split into five classes:

* **(a)** law-free and admissible in `C₀ s₀ ρ Rad`: `2`, `Cdual` (dimension only,
  by the Cdual module's F1 absorptions), `Cbesov d`, and `√hardyConstant`, whose selector
  `exists_ruledHardySelection` fixes it from `(d, ρ, Rad, s)`
  alone — exactly `C₀`'s permitted dependence;
* **(b)** the rate factor `(ε · x · …) ^ κ`, already the hole's own;
* **(c)** `boundaryEnergy ^ (1/2)`, already the hole's own right-hand factor;
* **(d)** law-free but `g`-dependent: everything in `Kframe` beyond (a) — the
  orders `r`, `b = responseWindowOrder g`, the rate `kappaRate`, `Rad`, `cnorm`,
  the certificate amplitude `√h.delta`, the bracket `J`, and
  `frameFoldConstant`/`foldedResponseFillingConstant`;
* **(e)** the eccentricity: `√Kenergy` from the frozen-witness price at
  the eccentricity constant `Cwit`.

`outputFactor` is in **none** of them: it cancels against the
physical-frame transport.

This module supplies the absorption itself.  Classes (d) and (e) are a single
nonnegative real `Krest`; the lemma below moves it into the length as a factor
`perGLengthFactor Krest kappa`, which is exactly the per-`g` law-free length
factor the root-interface modules is adding.  The `0 ≤` versus `0 <` defect is
repaired in the same step by `C₀ + 1`.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open scoped ENNReal

noncomputable section

/-- The per-`g` length factor that absorbs a nonnegative constant at the rate
`kappa`: the `kappa`-th root of the constant, truncated at one. -/
@[expose]
def perGLengthFactor (Krest kappa : ℝ) : ℝ := (max 1 Krest) ^ kappa⁻¹

theorem one_le_perGLengthFactor (Krest : ℝ) {kappa : ℝ} (hkappa : 0 < kappa) :
    1 ≤ perGLengthFactor Krest kappa := by
  rw [perGLengthFactor]
  exact one_le_rpow_of_one_le (le_max_left _ _) (inv_nonneg.mpr hkappa.le)

theorem perGLengthFactor_nonneg (Krest : ℝ) {kappa : ℝ} (hkappa : 0 < kappa) :
    0 ≤ perGLengthFactor Krest kappa :=
  le_trans zero_le_one (one_le_perGLengthFactor Krest hkappa)

/-- The defining property: raised to the rate, the length factor is the
truncated constant it absorbs. -/
theorem perGLengthFactor_rpow (Krest : ℝ) {kappa : ℝ} (hkappa : 0 < kappa) :
    perGLengthFactor Krest kappa ^ kappa = max 1 Krest := by
  have hK0 : (0 : ℝ) ≤ max 1 Krest := le_trans zero_le_one (le_max_left _ _)
  rw [perGLengthFactor, ← Real.rpow_mul hK0, inv_mul_cancel₀ hkappa.ne',
    Real.rpow_one]

/-- **The absorption.**  A per-`g` constant multiplying the rate factor is moved
into the length, leaving the law-free constant alone in front. -/
theorem constant_absorbed_into_length {C0 Krest epsilon x fold kappa : ℝ}
    (hC0 : 0 ≤ C0) (hkappa : 0 < kappa) (heps : 0 ≤ epsilon) (hx : 0 ≤ x)
    (hfold : 0 ≤ fold) :
    (C0 * Krest) * (epsilon * (x * fold)) ^ kappa ≤
      C0 * (epsilon * (x * perGLengthFactor Krest kappa * fold)) ^ kappa := by
  have hLg : 0 ≤ perGLengthFactor Krest kappa :=
    perGLengthFactor_nonneg Krest hkappa
  have hbase : (0 : ℝ) ≤ epsilon * (x * fold) :=
    mul_nonneg heps (mul_nonneg hx hfold)
  have hrewrite : epsilon * (x * perGLengthFactor Krest kappa * fold) =
      epsilon * (x * fold) * perGLengthFactor Krest kappa := by ring
  have hsplit : (epsilon * (x * perGLengthFactor Krest kappa * fold)) ^ kappa =
      (epsilon * (x * fold)) ^ kappa * (max 1 Krest) := by
    rw [hrewrite, Real.mul_rpow hbase hLg, perGLengthFactor_rpow Krest hkappa]
  have hrate0 : (0 : ℝ) ≤ (epsilon * (x * fold)) ^ kappa :=
    Real.rpow_nonneg hbase _
  rw [hsplit]
  have hKle : Krest ≤ max 1 Krest := le_max_right _ _
  calc C0 * Krest * (epsilon * (x * fold)) ^ kappa
      = C0 * (Krest * (epsilon * (x * fold)) ^ kappa) := by ring
    _ ≤ C0 * (max 1 Krest * (epsilon * (x * fold)) ^ kappa) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hKle hrate0) hC0
    _ = C0 * ((epsilon * (x * fold)) ^ kappa * max 1 Krest) := by ring

end

end RowSupply
end HighContrast
end HCPolySupport
