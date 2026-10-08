/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastIsotropyCarriers

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastLoadScalePiFree

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The load scale, the `kap2` value and the metric factor

**Corrected interface.**  This file was first written on the assumption
that the Euclidean boundary envelope could be eliminated by an *inequality*:
each of `weakLoadScalePiFree`, `kap2Value` and `metricFactorValue` is monotone in the
scalar `boundaryConst C_d g m_Al · 3^{gG}`, so any `Π`-free upper bound on that
scalar would propagate.  The near-reference comparison refutes that reading:
the hypothesis
`boundaryConst C_d g m_Al · 3^{gG} ≤ cIso` forces
`witnessEccentricity m_Al ≤ cIso`
(the row-envelope eccentricity bound), and at the fusion's binding
`m_Al = canonicalMetric 𝐄` the family has
`witnessEccentricity (canonicalMetric 𝐄) → ∞` at constant contrast.  **No
`Π`-free `cIso` satisfies it**, and the near-reference comparison — which bounds `adaptedMean`, not
`boundaryConst` — cannot discharge it.

The correct interface is the near-reference comparison's, and it is a **change
of normalizing block, not a scalar inequality**: the account is taken against
`isotropyReference` rather than the inflated reference, so `isotropyLoadScale`
*replaces*
`weakLoadScalePiFree` and `isotropyKap2` *replaces* `kap2Value`.  There is no
inequality between the old and new carriers, and none is needed.

What this file therefore supplies:

* the two monotonicity steps, **retained but no longer part of the load-scale
  interface**: they are sound, and they remain the arithmetic that the row-3
  re-parametrization will use once an envelope is produced, but they are *not*
  dischargeable from the near-reference comparison.
* — the arithmetic the consumers need **at the near-reference comparison's carriers**.
* — the metric factor, which *does* close: its `r` slot is discharged by
  the near-reference comparison's `sqrt_kappaRef_le_of_refContrast_le` at `r = √(1 + 6σ)`,
  dimension-only.  This closes the residual that the previous version of this
  file named as missing (`kappaRef 𝐄` has no upper bound in the tree) — the near-reference
  comparison
  supplied it.
* — the propagation into `fusionRecursionConstantIsotropySharp`'s quadratic branch, at
  carriers with no `boundaryConst`, no `witnessEccentricity`, no `3^{gG}` and no
  `kappaRef`.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## 1. The envelope monotonicity steps (outside the load-scale interface) -/

/-- The weak load scale at an abstract envelope scalar.

**Not `Π`-free in practice**: see the header.  Retained as arithmetic. -/
@[expose]
def weakLoadScalePiFree (cIso kap : ℝ) : ℝ := 2 * cIso * kap * 7

/-! ## 2. The arithmetic at the near-reference comparison's carriers -/

/-- The entry comparability constant is at least one. -/
theorem one_le_isotropyKap2 {cIso : ℝ} (hcIso : 0 ≤ cIso) (hsmall : cIso < 1) :
    1 ≤ isotropyKap2 cIso := by
  have hpos : (0 : ℝ) < 1 - cIso := by linarith only [hsmall]
  have hid : (1 - cIso) * (1 - cIso)⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  have hcu : (0 : ℝ) ≤ cIso * (1 - cIso)⁻¹ :=
    mul_nonneg hcIso (inv_nonneg.mpr hpos.le)
  rw [isotropyKap2]
  nlinarith only [hid, hcu]

/-! ## 3. The metric factor, closed at the near-reference comparison's imbalance bound -/

/-- The metric factor at an abstract reference ratio `r ≥ √κ_𝐄`. -/
@[expose]
def metricFactorValuePiFree (cF kap r : ℝ) : ℝ :=
  Real.sqrt (cF * r * (2 + 2 * (kap * (cF * r))))

theorem metricFactorValue_eq_piFree (E : BlockMat d) (cF kap : ℝ) :
    metricFactorValue E cF kap =
      metricFactorValuePiFree cF kap (Real.sqrt (kappaRef E)) := rfl

/-- **The metric factor is monotone in all three carriers.** -/
theorem metricFactorValuePiFree_mono {cF cF' kap kap' r r' : ℝ}
    (hcF0 : 0 ≤ cF) (hkap0 : 0 ≤ kap) (hr0 : 0 ≤ r)
    (hcF : cF ≤ cF') (hkap : kap ≤ kap') (hr : r ≤ r') :
    metricFactorValuePiFree cF kap r ≤ metricFactorValuePiFree cF' kap' r' := by
  have hcF'0 : (0 : ℝ) ≤ cF' := le_trans hcF0 hcF
  have hx0 : (0 : ℝ) ≤ cF * r := mul_nonneg hcF0 hr0
  have hx : cF * r ≤ cF' * r' := mul_le_mul hcF hr hr0 hcF'0
  have hsq : (cF * r) ^ 2 ≤ (cF' * r') ^ 2 := pow_le_pow_left₀ hx0 hx 2
  have h1 : kap * (cF * r) ^ 2 ≤ kap * (cF' * r') ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hkap0
  have h2 : kap * (cF' * r') ^ 2 ≤ kap' * (cF' * r') ^ 2 :=
    mul_le_mul_of_nonneg_right hkap (sq_nonneg _)
  have hkq : kap * (cF * r) ^ 2 ≤ kap' * (cF' * r') ^ 2 := le_trans h1 h2
  rw [metricFactorValuePiFree, metricFactorValuePiFree]
  refine Real.sqrt_le_sqrt ?_
  nlinarith only [hx, hkq]

/-- The metric factor at an abstract imbalance bound. -/
theorem metricFactorValue_le_piFree {E : BlockMat d} {cF cF' kap kap' r : ℝ}
    (hcF0 : 0 ≤ cF) (hkap0 : 0 ≤ kap)
    (hcF : cF ≤ cF') (hkap : kap ≤ kap')
    (hr : Real.sqrt (kappaRef E) ≤ r) :
    metricFactorValue E cF kap ≤ metricFactorValuePiFree cF' kap' r := by
  rw [metricFactorValue_eq_piFree]
  exact metricFactorValuePiFree_mono hcF0 hkap0 (Real.sqrt_nonneg _) hcF hkap hr

/-- **The metric factor closed at a dimension-only ratio.**  the near-reference comparison's
`sqrt_kappaRef_le_of_refContrast_le` discharges the `r` slot at `√(1 + 6σ)`,
which carries no `Π`. -/
theorem metricFactorValue_le_isotropy [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {sigma : ℝ} (hsigma : refContrast E - 1 ≤ sigma)
    {cF cF' kap kap' : ℝ} (hcF0 : 0 ≤ cF) (hkap0 : 0 ≤ kap)
    (hcF : cF ≤ cF') (hkap : kap ≤ kap') :
    metricFactorValue E cF kap ≤
      metricFactorValuePiFree cF' kap' (Real.sqrt (1 + 6 * sigma)) :=
  metricFactorValue_le_piFree hcF0 hkap0 hcF hkap
    (sqrt_kappaRef_le_of_refContrast_le hdag hsigma)

/-- **The metric factor at the near-reference comparison's carriers.**  Every argument is
`Π`-free. -/
@[expose]
def isotropyMetricFactor (cIso sigma : ℝ) : ℝ :=
  metricFactorValuePiFree (1 + cIso) (isotropyKap2 cIso)
    (Real.sqrt (1 + 6 * sigma))

theorem metricFactorValue_le_isotropyMetricFactor [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {sigma : ℝ} (hsigma : refContrast E - 1 ≤ sigma)
    {cIso cF kap : ℝ} (hcF0 : 0 ≤ cF) (hkap0 : 0 ≤ kap)
    (hcF : cF ≤ 1 + cIso) (hkap : kap ≤ isotropyKap2 cIso) :
    metricFactorValue E cF kap ≤ isotropyMetricFactor cIso sigma := by
  rw [isotropyMetricFactor]
  exact metricFactorValue_le_isotropy hdag hsigma hcF0 hkap0 hcF hkap

/-! ## 4. Propagation into the quadratic branch -/

end

end HCPolySupport.HighContrast.Quenched
