/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenEndEmbedding
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourSeminormComparisons

/-!
# StepSevenEndAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 7d, part three: `e.energy.density.estimate`

## The target

ABK26, the last line of the proof of `t.regularity`:

> Since `m - m' ≤ |𝓑_z| + 3 ≤ C₁⁻¹(1-α)(m-n) + 3`, we obtain
> `e.energy.density.estimate` by the previous display and `e.gradient.with.shom`
> since `σ_{n'} ≤ 2 σ_m`.

and the target display `e.energy.density.estimate`:

```text
  ν^{1/2}‖∇u‖_{L²((x+□_n)∩□_m)}
    ≤ C 3^{(1-α)(m-n)} ( ν^{1/2}‖∇u‖_{L²(□_m)}
        + σ_m^{-1/2} 3^{m/2}[𝐠]_{W^{1/2,∞}(□_m)}
        + σ_m^{1/2} 3^{m/2}‖∇h‖_{W^{1/2,∞}(□_m)} 1_{x ∉ □_{m-1}} ) .
```

## The exponent bookkeeping — the two halves make exactly `(1-α)(m-n)`

`stepSevenGradientWithShom` carries `3^{(3/4)(1-α)(m-n)}`, and the Step-7d
endpoint (`StepSevenEndEmbedding`) contributes the transport factor, which
`StepSevenEndPoincare` absorbs into `3^{(1/4)(1-α)(m-n)}`.  Their product is
`3^{(1-α)(m-n)}` — the printed exponent, character for character.  This is the
arithmetic reason the printed `3/4` of `e.gradient.with.shom` is what it is:
the theorem's own exponent is `1`, and Step 7d spends the remaining quarter on
the coarse-graining transport.

## `σ_{n'} ≤ 2 σ_m` needs no adjacency

The final sentence presents `σ_{n'} ≤ 2σ_m` as an adjacency consequence.  In
this repository the growth cap is
`sigmaBar_le_rpow_mul_sigmaBar_of_inductionState`, derived from conjunct 1 of
the frozen Section-3 `inductionState` at the two scales alone — at the explicit
constant `4` rather than the printed `2`, which is immaterial inside `C` (the
collapse cost becomes `√4 = 2` instead of `√2`).  Both are delivered: the
composition takes `σ_{n'} ≤ Ccmp · σ_m` for an arbitrary `Ccmp`, and the
printed `Ccmp = 2` and the proved `Ccmp = 4` are both instances.

## The data-bracket collapse is owned here

This module owns the collapse: the data-leg merge is applied here, at the
same comparison `σ_{n'} ≤ Ccmp σ_m` that the assembly uses for the
oscillation leg, so the two consumptions of `e.shom.m.vs.shom.n` are one
hypothesis.

## The `[𝐠]_{H^s}` → `[𝐠]_{W^{1/2,∞}}` passage

The endpoint's data leg is `3^{sm}[𝐠]_{H^s(□_m)}` while the theorem's data leg
is `3^{m/2}[𝐠]_{W^{1/2,∞}(□_m)}`; the manuscript never displays the passage.
It is the proved atom `three_rpow_mul_normalizedGagliardoESeminormOn_cube_le`,
and it is consumed here in the real-valued layer, not re-derived: the
free `s` cancels out of the scale weight, which is why
`e.energy.density.estimate` can be `s`-free.

## The conditional inputs reaching this module

Nothing new is assumed here.  The assembly is a theorem about the two proved
displays; the live conditional inputs are the ones its two arguments carry —'s
`hcacc`/`hlambda`/`hosc`, `StepSevenEndPoincare`'s `hcg`/`hlambda`, and
`StepSevenEndEmbedding`'s `hembed`/`hbridge`.

The end chain is the single entry point: it takes each of the three
proved displays' conclusions in its hypothesis slots (`stepSevenGradientWithShom`,
the absorbed coarse-grained Poincaré display, and the
oscillation endpoint's three links) and produces `e.energy.density.estimate`.
The unification is syntactic — no massaging, one associativity `ring`.

## Strengthenings

`sqrt_shomNp_mul_endpoint_le` and the two composition theorems need no sign
condition on the endpoint constant or on the transported bracket: the
multiplicative step only uses `0 ≤ oscTrunc` and `0 ≤ √Ccmp·√σ_m`.  Those
binders were therefore dropped rather than carried unused.

## References

* ABK26, `e.energy.density.estimate`; the assembly.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

/-! ## 1. `σ_{n'} ≤ C σ_m` on the oscillation leg -/

/-- `√σ_m · √(σ_m⁻¹) = 1`. -/
theorem sqrt_mul_sqrt_inv_eq_one {S : ℝ} (hS : 0 < S) :
    Real.sqrt S * Real.sqrt S⁻¹ = 1 := by
  rw [← Real.sqrt_mul hS.le, mul_inv_cancel₀ (ne_of_gt hS), Real.sqrt_one]

/-- **The `σ` collapse on the oscillation leg**.

The Step-7c gradient display multiplies the endpoint by `√σ_{n'}`, while the
endpoint itself carries `√(σ_m⁻¹)`; the comparison `σ_{n'} ≤ Ccmp σ_m` makes the
two cancel at the cost `√Ccmp`:

```text
  √σ_{n'} · Cend · √(σ_m⁻¹) · X  ≤  √Ccmp · Cend · X .
```

`Ccmp = 2` is the printed constant; the derived growth cap gives `Ccmp = 4`.  No
sign condition on `Cend` or `X` is needed — a strengthening: the multiplicative
step only uses `0 ≤ oscTrunc` and `0 ≤ √Ccmp·√σ_m`. -/
theorem sqrt_shomNp_mul_endpoint_le {shomNp shomM Ccmp Cend X oscTrunc : ℝ}
    (hshomM : 0 < shomM) (hCcmp : 0 ≤ Ccmp)
    (hoscTrunc : 0 ≤ oscTrunc) (hcomp : shomNp ≤ Ccmp * shomM)
    (hend : oscTrunc ≤ Cend * (Real.sqrt shomM⁻¹ * X)) :
    Real.sqrt shomNp * oscTrunc ≤ Real.sqrt Ccmp * Cend * X := by
  have hSm : (0 : ℝ) ≤ Real.sqrt shomM := Real.sqrt_nonneg _
  have hCc : (0 : ℝ) ≤ Real.sqrt Ccmp := Real.sqrt_nonneg _
  have hstep : Real.sqrt shomNp ≤ Real.sqrt Ccmp * Real.sqrt shomM := by
    calc Real.sqrt shomNp ≤ Real.sqrt (Ccmp * shomM) := Real.sqrt_le_sqrt hcomp
      _ = Real.sqrt Ccmp * Real.sqrt shomM := Real.sqrt_mul hCcmp shomM
  have h1 : Real.sqrt shomNp * oscTrunc ≤
      (Real.sqrt Ccmp * Real.sqrt shomM) * (Cend * (Real.sqrt shomM⁻¹ * X)) :=
    mul_le_mul hstep hend hoscTrunc (mul_nonneg hCc hSm)
  have hcancel := sqrt_mul_sqrt_inv_eq_one hshomM
  have h2 : (Real.sqrt Ccmp * Real.sqrt shomM) * (Cend * (Real.sqrt shomM⁻¹ * X)) =
      Real.sqrt Ccmp * Cend * ((Real.sqrt shomM * Real.sqrt shomM⁻¹) * X) := by ring
  rw [hcancel, one_mul] at h2
  linarith only [h1, h2.ge, h2.le]

/-! ## 2. The assembly -/

/-- **`e.energy.density.estimate`, assembled** — the abstract-real core.

From's `e.gradient.with.shom` at the power = 3^{(3/4)(1-α)(m-n)}` and the
Step-7d endpoint = 3^{(1/4)(1-α)(m-n)}`, together with `σ_{n'} ≤ Ccmp σ_m`,
the theorem's own display follows at the power `R34 · = 3^{(1-α)(m-n)}`:

```text
  gradLoc ≤ Cg·(√Ccmp·Cend)·(R34·R14)·( gradM + √(σ_m⁻¹)·dataG )
            + Cg·R34·( √σ_{n'}·dataOsc + dataM ) ,
```

the second summand being the honest data bracket, which the merged form
collapses to the printed one. -/
theorem stepSevenEnergyDensityEstimate_compose {Cg Cend Ccmp R34 R14 shomNp shomM
    gradLoc oscTrunc dataOsc dataM gradM dataG : ℝ}
    (hCg : 0 ≤ Cg) (hCcmp : 0 ≤ Ccmp) (hshomM : 0 < shomM)
    (hR34 : 0 ≤ R34) (hoscTrunc : 0 ≤ oscTrunc)
    (hcomp : shomNp ≤ Ccmp * shomM)
    (hgrad : gradLoc ≤ Cg * Real.sqrt shomNp * R34 * oscTrunc +
      Cg * R34 * (Real.sqrt shomNp * dataOsc + dataM))
    (hend : oscTrunc ≤ Cend * R14 *
      (Real.sqrt shomM⁻¹ * (gradM + Real.sqrt shomM⁻¹ * dataG))) :
    gradLoc ≤ Cg * (Real.sqrt Ccmp * (Cend * R14)) * R34 *
        (gradM + Real.sqrt shomM⁻¹ * dataG) +
      Cg * R34 * (Real.sqrt shomNp * dataOsc + dataM) := by
  have hkey := sqrt_shomNp_mul_endpoint_le (Cend := Cend * R14) hshomM hCcmp
    hoscTrunc hcomp hend
  -- push the collapsed leg through `Cg · R34`
  have hmul : Cg * R34 * (Real.sqrt shomNp * oscTrunc) ≤
      Cg * R34 * (Real.sqrt Ccmp * (Cend * R14) *
        (gradM + Real.sqrt shomM⁻¹ * dataG)) :=
    mul_le_mul_of_nonneg_left hkey (mul_nonneg hCg hR34)
  have hexp1 : Cg * Real.sqrt shomNp * R34 * oscTrunc =
      Cg * R34 * (Real.sqrt shomNp * oscTrunc) := by ring
  have hexp2 : Cg * R34 * (Real.sqrt Ccmp * (Cend * R14) *
      (gradM + Real.sqrt shomM⁻¹ * dataG)) =
      Cg * (Real.sqrt Ccmp * (Cend * R14)) * R34 *
        (gradM + Real.sqrt shomM⁻¹ * dataG) := by ring
  linarith only [hgrad, hmul, hexp1.ge, hexp1.le, hexp2.ge, hexp2.le]

/-! ## 5. The data leg in the theorem's own seminorm -/

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end

end Algsuperdiff.Section4.Provider.Regularity
