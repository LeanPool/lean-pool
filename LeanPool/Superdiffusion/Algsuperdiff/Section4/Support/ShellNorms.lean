/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.ShellDerivativeControl

/-!
# ShellNorms

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Section 4 volume-normalized shell Sobolev gauges

ABK26's Section 4 good events (`d.good.event.for.lambda`) and the annular
decomposition (`p.mathcalE.annular.decomp`) weigh the stream increments `j_k`
in the manuscript's *volume-normalized* Sobolev norms `‖∇j‖_{W^{1,∞}(□_m)}`
and `‖j‖_{W^{2,∞}(z+□_k)}`.

The manuscript defines, for `|U| < ∞`,

```
  ‖f‖_{W^{1,p}(U)} = ( ‖∇f‖_{L^p(U)}^p + |U|^{-p/d} ‖f‖_{L^p(U)}^p )^{1/p} ,
```

and the `k`-th order analogue adds one term per derivative order with the
matching power of `|U|^{-1/d}`.  At the endpoint `p = ∞` the `ℓ^p` combination
is the maximum and the normalized `L^∞` norm is the plain `L^∞` norm, so on
the triadic cube `□_m` (where `|□_m|^{-1/d} = 3^{-m}`) the two gauges used by
Section 4 are

```
  ‖∇j‖_{W^{1,∞}(□_m)}   = max ( ‖∇²j‖_{L^∞(□_m)} , 3^{-m} ‖∇j‖_{L^∞(□_m)} ) ,
  ‖j‖_{W^{2,∞}(z+□_k)}  = max ( ‖∇²j‖_{L^∞(z+□_k)} ,
                                 3^{-k}  ‖∇j‖_{L^∞(z+□_k)} ,
                                 3^{-2k} ‖j‖_{L^∞(z+□_k)} ) .
```

Both are realized on the proved shell carriers: the origin-cube `L^∞` gauges
are `Algsuperdiff.Section3.Cutoff.localCubeControl` (order `0`) and
`Algsuperdiff.Section3.Provider.Stream.localCubeDerivNorm` /
`localCubeSecondDerivNorm` (orders `1` and `2`), and the translated cube `z +
□_k` is realized by the frozen `ShellField.translate` action (`translate z j =
j (· + z)`), for which the exact supremum over `z + □_k` of a derivative of `j`
is the supremum over `□_k` of the same derivative of `translate z j`.  No new
supremum, no fallback branch and no chosen representative is introduced.

## Main definitions

* `shellW1InfGradNorm m j` — the tex `‖∇j‖_{W^{1,∞}(□_m)}`.
* `shellW2InfNormAt z k j` — the tex `‖j‖_{W^{2,∞}(z+□_k)}`.

## References

* ABK26, (the normalized Sobolev norms).
* ABK26, `d.good.event.for.lambda`, and `p.mathcalE.annular.decomp`.
-/

namespace Algsuperdiff.Section4.Support

open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Stream

variable {d : ℕ}

/-! ## The first-order gauge on the origin cube -/

/-- The manuscript's `‖∇j‖_{W^{1,∞}(□_m)}`: the `p = ∞` endpoint of the
volume-normalized `W^{1,p}` norm, applied to `f = ∇j` on the origin cube
`□_m`, where `|□_m|^{-1/d} = 3^{-m}`. -/
noncomputable def shellW1InfGradNorm (m : ℤ) (j : ShellField d) : ℝ :=
  max (localCubeSecondDerivNorm m j) ((3 : ℝ) ^ (-m) * localCubeDerivNorm m j)

theorem shellW1InfGradNorm_def (m : ℤ) (j : ShellField d) :
    shellW1InfGradNorm m j =
      max (localCubeSecondDerivNorm m j) ((3 : ℝ) ^ (-m) * localCubeDerivNorm m j) :=
  rfl

theorem shellW1InfGradNorm_nonneg (m : ℤ) (j : ShellField d) :
    0 ≤ shellW1InfGradNorm m j :=
  le_max_of_le_left (localCubeSecondDerivNorm_nonneg m j)

theorem measurable_shellW1InfGradNorm (m : ℤ) :
    Measurable (shellW1InfGradNorm (d := d) m) :=
  (measurable_localCubeSecondDerivNorm m).max
    (measurable_const.mul (measurable_localCubeDerivNorm m))

/-- The second-derivative leg is dominated by the gauge. -/
theorem localCubeSecondDerivNorm_le_shellW1InfGradNorm (m : ℤ) (j : ShellField d) :
    localCubeSecondDerivNorm m j ≤ shellW1InfGradNorm m j :=
  le_max_left _ _

/-- The normalized first-derivative leg is dominated by the gauge. -/
theorem three_zpow_mul_localCubeDerivNorm_le_shellW1InfGradNorm
    (m : ℤ) (j : ShellField d) :
    (3 : ℝ) ^ (-m) * localCubeDerivNorm m j ≤ shellW1InfGradNorm m j :=
  le_max_right _ _

/-! ## The second-order gauge on a translated cube -/

/-- The manuscript's `‖j‖_{W^{2,∞}(z+□_k)}`: the `p = ∞` endpoint of the
volume-normalized second-order Sobolev norm on the translated cube `z + □_k`,
where `|z+□_k|^{-1/d} = 3^{-k}`.

The translated cube is realized by the frozen translation action:
`ShellField.translate z j = j (· + z)` carries the supremum over `z + □_k` of
any derivative of `j` to the supremum over `□_k` of the same derivative of
`translate z j`, which is exactly what the proved origin-cube gauges compute. -/
noncomputable def shellW2InfNormAt (z : Vec d) (k : ℤ) (j : ShellField d) : ℝ :=
  max (shellW1InfGradNorm k (ShellField.translate z j))
    ((3 : ℝ) ^ (-2 * k) * localCubeControl k (ShellField.translate z j))

theorem measurable_shellW2InfNormAt (z : Vec d) (k : ℤ) :
    Measurable (shellW2InfNormAt (d := d) z k) :=
  ((measurable_shellW1InfGradNorm k).comp (ShellField.measurable_translate z)).max
    (measurable_const.mul
      ((measurable_localCubeControl k).comp (ShellField.measurable_translate z)))

/-- The normalized value leg is dominated by the gauge. -/
theorem three_zpow_mul_localCubeControl_le_shellW2InfNormAt
    (z : Vec d) (k : ℤ) (j : ShellField d) :
    (3 : ℝ) ^ (-2 * k) * localCubeControl k (ShellField.translate z j) ≤
      shellW2InfNormAt z k j :=
  le_max_right _ _

/-- The first-order gauge of the translate is dominated by the second-order
gauge, the exact `W^{1,∞} ≤ W^{2,∞}` embedding on one cube. -/
theorem shellW1InfGradNorm_translate_le_shellW2InfNormAt
    (z : Vec d) (k : ℤ) (j : ShellField d) :
    shellW1InfGradNorm k (ShellField.translate z j) ≤ shellW2InfNormAt z k j :=
  le_max_left _ _

end Algsuperdiff.Section4.Support
