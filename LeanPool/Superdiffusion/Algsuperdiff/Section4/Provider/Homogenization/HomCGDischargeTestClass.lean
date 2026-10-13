/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomCGDischargeInstantiation
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepFourPairing

/-!
# HomCGDischargeTestClass

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two printed levels, and the ONE residue between them and `WeakNegDualBoundOn`

## The two legs, at the printed levels

`HomCGDischargeAssembly` proves the printed display as a single inequality for
the pair `σ₀‖∇u-∇v‖ + ‖𝐚∇u-σ₀∇v‖`.  `smoothDual_legs_of_display` splits it into
the two levels the Step-4 consumer wants, which are the two levels exactly:

```text
  σ₀ · ‖∇u-∇v‖_{smooth dual}  ≤  3^{sm} · RHS,
       ‖𝐚∇u-σ₀∇v‖_{smooth dual} ≤  3^{sm} · RHS.
```

## The residue: the TEST CLASS, isolated as one `Prop`

`WeakNegDualBoundOn Q s W F` (the carrier, consumed at Step 4) quantifies over
**merely Hölder** test fields, measured in the volume-normalized Hölder gauge
`wsInftyGauge Q s Ksup KHol = 3^{-s·scale}·Ksup + KHol`.  `CoarseGraining`'s
dual quantifies over **globally smooth** test fields measured in
`cubeEuclideanWspFullENorm` at the conjugate exponent.  The domination of the
Hölder test gauge by the smooth-dual gauge is exactly the missing comparison,
and it is the ONLY missing thing: given it, every smooth-dual level converts to
a `WeakNegDualBoundOn` level at one uniform factor `Ktest`.

## MEASUREMENT: the conversion is FALSE at equal orders

That domination must fail when `s` is read on both sides.
The reason is an index obstruction, not a constant:

* the Hölder gauge is the `B^{s}_{∞,∞}(□_m)` norm (the manuscript declares
  `C^{0,s}` and `W^{s,∞}` interchangeable);
* `CoarseGraining`'s test gauge is the Gagliardo `W^{s,p′}` norm, i.e. `B^{s}_{p′,p′}`;
* on a bounded cube `B^{s}_{∞,∞} ⊂ B^{s}_{p′,∞}` but `B^{s}_{p′,∞} ⊄ B^{s}_{p′,p′}`:
  the Gagliardo double integral of a `C^{0,s}` field carries the integrand
  `|x-y|^{-s p′ - d}·|φ(x)-φ(y)|^{p′} ≤ K^{p′}|x-y|^{-d}`, which is
  **logarithmically divergent**, and the bound is saturated by Weierstrass-type
  fields.  So no finite `Ktest` exists at equal orders.

The honest route therefore LOSES ORDER: apply the display at `s′ < s`,
where `C^{0,s}(□_m) ⊂ W^{s′,p′}(□_m)` holds with constant
`C(d,(s-s′)p′)^{1/p′}·3^{m(s-s′)}`, and observe that the same `3^{m(s-s′)}`
appears in the `L^{p′}` half of the gauge, so it factors out of the whole
comparison:

```text
  ‖φ‖_{W^{s′,p′} full} ≤ C · 3^{m(s-s′)} · wsInftyGauge □_m s Ksup KHol.
```

Composed with the display at `s′` (whose smooth-dual level carries `3^{s′m}`)
this produces exactly the target level `3^{sm}`, i.e. the order loss is FREE at
the level, and is paid only inside the right-hand side, where the printed
`s^{-1}`, `s^{-9/2}` and `(s₂-s)^{-1}` are evaluated at `s′` instead of `s`.
Because the spine's bundle quantifies `s`, `s₂`, `C_cg`, `E₁`, `E₂`, `D_g` and
`S` **existentially**, that substitution is admissible for the spine; it is NOT
admissible inside a single instance of the transcribed finite-`p`
coarse-graining hypothesis, whose three clauses share one `s`.

## The two analytic inputs the order-loss route still needs

Neither was found by name or statement search in `CoarseGraining`, in this
repository, or in the Mathlib `MeasureTheory`/`SpecialFunctions` integrability
files:

1. `∫∫_{□×□} |x-y|^{β-d} dx dy < ∞` for `β > 0` with the explicit cube-scaling
   `≤ C(d,β)·|□|·L^{β}` — the Riesz-kernel integrability that turns a Hölder
   bound into a Gagliardo bound.  The nearest available statement is `CoarseGraining`'s
   `rieszKernel_integrableOn_ball`, which is the SINGLE exponent `β = 1`
   (`‖x-y‖^{1-d}`); the route needs `β = (s-s′)p′`, which is small — and
   `β = 1` would force `s′ = s - 1/p′ < 0` under the bundle's own guard
   `s + d/p ≤ 1/2`, so the available case cannot be reused;
2. a smooth-test approximation: a `C^{0,s}` field on `□_m` is the uniform limit
   on `□_m` of globally smooth fields with the same sup and Hölder bounds
   (McShane extension + mollification; the `mollifyBump` machinery
   and the Hölder preservation cover the mollification half).

The domination at equal orders is what those two inputs would produce.
-/

open HCPolySupport HCPolySupport.Book.Ch03 HCPolySupport.Book.Ch03.ABK26
open Algsuperdiff.Section4.Support
open MeasureTheory
open scoped BigOperators ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. Scale bookkeeping -/

/-- `3^{sm} · 3^{-sm} = 1`, in `ℝ≥0∞`. -/
theorem ofReal_three_rpow_scale_pair (s : ℝ) (m : ℤ) :
    ENNReal.ofReal (Real.rpow 3 (s * (m : ℝ))) *
      ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ))) = 1 := by
  have hnn : (0 : ℝ) ≤ Real.rpow 3 (s * (m : ℝ)) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hprod : Real.rpow 3 (s * (m : ℝ)) * Real.rpow 3 (-s * (m : ℝ)) = 1 := by
    change (3 : ℝ) ^ (s * (m : ℝ)) * (3 : ℝ) ^ (-s * (m : ℝ)) = 1
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    have hexp : s * (m : ℝ) + -s * (m : ℝ) = 0 := by ring
    rw [hexp, Real.rpow_zero]
  rw [← ENNReal.ofReal_mul hnn, hprod, ENNReal.ofReal_one]

/-! ## 2. The two printed levels -/

/-- **The printed display, split into the two Step-4 levels.**

From `3^{-sm}(σ₀‖∇u-∇v‖ + ‖𝐚∇u-σ₀∇v‖) ≤ R` one reads off both legs at level
`3^{sm}·R`, which is the pair of levels. -/
theorem smoothDual_legs_of_display {m : ℤ}
    {a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m))} {sigma0 : ℝ}
    {u v : H1Function (openCubeSet (originCube d m))} {s : FractionalOrder}
    {p : FiniteLpExponent} {R : ℝ≥0∞}
    (h : ENNReal.ofReal (Real.rpow 3 (-s.1 * (m : ℝ))) *
        centeredCubeFluxComparisonSmoothDualLHS m a sigma0 u v s p ≤ R) :
    ENNReal.ofReal sigma0 *
          cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p
            (centeredCubeGradientDifferenceL2Field m u v) ≤
        ENNReal.ofReal (Real.rpow 3 (s.1 * (m : ℝ))) * R ∧
      cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p
          (centeredCubeFluxDifferenceL2Field m a sigma0 u v) ≤
        ENNReal.ofReal (Real.rpow 3 (s.1 * (m : ℝ))) * R := by
  set Wp : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 3 (s.1 * (m : ℝ))) with hWp
  set Wm : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 3 (-s.1 * (m : ℝ))) with hWm
  set X : ℝ≥0∞ := centeredCubeFluxComparisonSmoothDualLHS m a sigma0 u v s p with hX
  have hpair : Wp * Wm = 1 := ofReal_three_rpow_scale_pair s.1 m
  have hfull : X ≤ Wp * R := by
    calc X = (Wp * Wm) * X := by rw [hpair, one_mul]
      _ = Wp * (Wm * X) := by ring
      _ ≤ Wp * R := by gcongr
  constructor
  · exact le_trans (by
      rw [hX, centeredCubeFluxComparisonSmoothDualLHS]
      exact le_add_right (le_refl _)) hfull
  · exact le_trans (by
      rw [hX, centeredCubeFluxComparisonSmoothDualLHS]
      exact le_add_left (le_refl _)) hfull

end

end Algsuperdiff.Section4.Provider.Homogenization
