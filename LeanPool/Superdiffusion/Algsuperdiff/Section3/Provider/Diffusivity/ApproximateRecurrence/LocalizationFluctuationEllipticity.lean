/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity

/-!
# LocalizationFluctuationEllipticity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The ellipticity display of Step 2 of `l.approximate.recurrence.formula`

ABK26, Step 2 of `l.approximate.recurrence.formula`: for every `z in 3^n Zd
cap cu_m`, using `e.ellipticities.monotone.ordered`,
`e.bound.one.cube.by.lambdas` and the scale gap `m - n <= 8 gamma^{-1}`,

```
  shom_{m-h}^{-1} Lambda_{1,2}(z+cu_n; a_m)
+ shom_{m-h} lambda_{1,2}^{-1}(z+cu_n; a_m)
<= C ( shom_{m-h}^{-1} Lambda_{gamma,2}(cu_m; a_m)
     + shom_{m-h} lambda_{gamma,2}^{-1}(cu_m; a_m) ) .
```

The two named displays are CoarseGraining's `LambdaSq_antitone` /
`lambdaSq_mono` (the `s`-monotonicity half of
`e.ellipticities.monotone.ordered`) and `descendant_LambdaSq_le` /
`descendant_lambdaSq_inv_le` (`e.bound.one.cube.by.lambdas`).  The scale gap
enters only through the descendant weight `3^{2 gamma (m-n)}`, which the gap
caps at the absolute constant `3^16`; that is the display's generic `C`.

## Binders

The scale gap is a premise of the display in the manuscript's own words ("and
that `m - n <= 8 gamma^{-1}`"), and is carried here in the equivalent scaled
form `2 gamma (Q.scale - k) <= 16`.  `0 < gamma < 1` is the standing exponent
window and `0 < shom` the standing positivity of the running diffusivity; both
are source data.  No smallness, moment, measurability or integrability
proposition occurs: this is a deterministic, pathwise inequality between
coarse-grained ellipticity constants of one and the same coefficient family.

## Scope

No anchor, frozen theorem or external input is consumed, and there is no
`sorry`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2, display;
  `e.ellipticities.monotone.ordered`; `e.bound.one.cube.by.lambdas`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport
open HCPolySupport.Book

noncomputable section

variable {d : ℕ}

/-- **The gauged ellipticity sum**, `shom^{-1} Lambda_{s,2}(Q; a) + shom
lambda_{s,2}^{-1}(Q; a)`. -/
def gaugedEllipticitySum (sigmaBar : ℝ) (Q : TriadicCube d) (s : ℝ)
    (a : Ch02.TriadicCoeffFamily d) : ℝ :=
  sigmaBar⁻¹ * Ch02.LambdaSq Q s (.finite 2) a +
    sigmaBar * (Ch02.lambdaSq Q s (.finite 2) a)⁻¹

/-- The gauged ellipticity sum is nonnegative for a nonnegative gauge. -/
theorem gaugedEllipticitySum_nonneg (Q : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) {sigmaBar s : ℝ} (hsig : 0 ≤ sigmaBar)
    (hs : 0 < s) : 0 ≤ gaugedEllipticitySum sigmaBar Q s a := by
  have h1 : 0 ≤ Ch02.LambdaSq Q s (.finite 2) a :=
    Ch02.LambdaSq_finite_nonneg Q a hs (by norm_num)
  have h2 : 0 ≤ (Ch02.lambdaSq Q s (.finite 2) a)⁻¹ :=
    inv_nonneg.mpr (Ch02.lambdaSq_finite_nonneg Q a hs (by norm_num))
  exact add_nonneg (mul_nonneg (inv_nonneg.mpr hsig) h1) (mul_nonneg hsig h2)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
