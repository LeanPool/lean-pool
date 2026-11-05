/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomFinitePTranslate
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomMollifyChain

/-!
# HomFinitePConversion

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5, Step 3c: the finite-`p` conversion

## THE CONVERSION

The `L^∞` endpoint is taken from the PRINTED finite-`p` proposition rather
than from its `p ↑ ∞` limit.  The mechanism is an
exponent shift, and the conversion is a four-step chain, every step proved:

```text
  (1)  3^{-ms}‖∇u-∇v‖_{B^{-s}_{p,p}(□_m)} ≤ A          (hCG', printed carrier)
  (2)  ⟹  |(∇u-∇v)_R| ≤ A·3^{(s+d/p)·depth R}          (HomFinitePGauge: one term
                                                        out of 3^{jd}, constant 1)
  (3)  ⟹  ‖(∇u-∇v)_{x+□_n}‖ ≤ 6dγ·A·3^{(s+d/p)(m-n)}   (HomFinitePTranslate:
                                                        the Whitney tiling, γ = liftGeomFactor)
  (4)  ⟹  3^{-m}|u-v| ≤ 16d·6dγ·A = 96 d² γ A a.e.     (the endpoint)
```

**The `3^{m(s+d/p)}` prefactor cancels exactly.**  Step (2) produces the gauge
constant `A·3^{m s'}` at the shifted order `s' = s + d/p`, and the endpoint
multiplies by `3^{-m s'}` (`linfty_constant_cancels`).  So the finite-`p` route
gives on the SAME display as the `(∞,∞)` route with `L` replaced by the
finite-`p` gauge level, at the dimension-only constant `96 d² γ`
(`≤ 288 d²` at the Step-3 pin, since `γ = liftGeomFactor s' ≤ 3`).

## THE RANGE GUARD, and where it is discharged

The chain requires `0 < s' ≤ 1/2`, i.e. `s + d/p ≤ 1/2`.  At the author's
`p = 4d` this is `d/p = 1/4`, hence exactly `s ≤ 1/4` — which is the Step-3
pin already in force: `s = |log γ|^{-1}` with the `homS_le_quarter` at
`4 ≤ |log γ|`.  The guard is an explicit hypothesis at every statement
(`hguard`), never silent.

## Carriers: no harvest, no deviation

`hCG'` is stated at the PRINTED grid-summed carrier (the negative Besov
seminorm definition's pure lattice `3^k ℤ^d ∩ □_m` = `CoarseGraining`'s
`descendantsAtDepth`).  The grid/translate carrier mismatch is
DISCHARGED here by `HomFinitePTranslate.uniformBoxGaugeBound_of_gridGauge`:
the reconstruction is proved.  The only extra
frame item it needs is that the field vanishes off `□_m`, which is the `H¹₀`
zero extension already present in the frame.

## Main results

* `linfty_constant_cancels` — the `3^{m(s+d/p)}` cancellation, displayed.

Steps (2)–(4) are carried at the print's own sup-over-depths gauge, in
`HomSpineSupFormRethread`.
-/

open MeasureTheory HCPolySupport HCPolySupport.Book.Ch03

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The cancellation and the guard, displayed -/

/-- **THE `3^{m(s+d/p)}` CANCELLATION.**

The extraction inflates the gauge constant by `3^{m s'}` and the endpoint
deflates it by `3^{-m s'}`; the two are inverse.  Nothing about `p` survives
into the `L^∞` display except through the exponent guard. -/
theorem linfty_constant_cancels (m : ℤ) (K A s' : ℝ) :
    K * (A * (3 : ℝ) ^ (s' * (m : ℝ))) * (3 : ℝ) ^ (-(m : ℝ) * s') = K * A := by
  have hone : (3 : ℝ) ^ (s' * (m : ℝ)) * (3 : ℝ) ^ (-(m : ℝ) * s') = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    have hzero : s' * (m : ℝ) + -(m : ℝ) * s' = 0 := by ring
    rw [hzero, Real.rpow_zero]
  calc K * (A * (3 : ℝ) ^ (s' * (m : ℝ))) * (3 : ℝ) ^ (-(m : ℝ) * s')
      = (K * A) * ((3 : ℝ) ^ (s' * (m : ℝ)) * (3 : ℝ) ^ (-(m : ℝ) * s')) := by ring
    _ = K * A := by rw [hone, mul_one]

end

end Algsuperdiff.Section4.Provider.Homogenization
