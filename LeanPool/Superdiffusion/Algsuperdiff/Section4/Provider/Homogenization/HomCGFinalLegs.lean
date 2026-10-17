/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomCGFinalDuality

/-!
# HomCGFinalLegs

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two duality legs, produced from the display at the lower order

## What this file supplies

The last link of the order-loss route: the display, read at the LOWER order
`s′`, produces BOTH `WeakNegDualBoundOn` legs at the DATA order `s`.

Input: `3^{-s′m}(σ₀‖∇u-∇v‖ + ‖𝐚∇u-σ₀∇v‖)_{smooth dual at s′} ≤ R`, i.e.
`HomCGDischargeTestClass.smoothDual_legs_of_display` applied at `s′`.

Output, with `K = cgTestConst d □_m s s′ p′`:

```text
  WeakNegDualBoundOn □_m s (K · σ₀⁻¹ · 3^{s′m} R) (∇u - ∇v)   and
  WeakNegDualBoundOn □_m s (K ·        3^{s′m} R) (𝐚∇u - σ₀∇v).
```

Since `K = d·3^{m(s-s′)}·(1 + C(d,β)^{1/p′})`, the produced levels are

```text
  d(1+C)·3^{sm}·σ₀⁻¹·R      and      d(1+C)·3^{sm}·R,
```

which is EXACTLY the shape of the finite-`p` coarse-graining hypothesis's two
duality clauses, `3^{s·scale}σ⁻¹·RHS` and `3^{s·scale}·RHS`, with the dimensional factor
`d(1 + C(d,β)^{1/p′})` absorbed into the printed constant `C_cg` — which the
spine's bundle quantifies existentially.  The order loss has vanished from the
LEVEL; it survives only inside `R`, where the printed `s^{-1}`, `s^{-9/2}` and
`(s₂-s)^{-1}` are read at `s′`.
-/

open HCPolySupport HCPolySupport.Book.Ch03 HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The scale weight, moved to the real side -/

private theorem ofReal_three_rpow_mul_toReal {t : ℝ} {R : ℝ≥0∞} (hR : R ≠ ⊤) :
    ENNReal.ofReal (Real.rpow 3 t) * R =
      ENNReal.ofReal (Real.rpow 3 t * R.toReal) := by
  change ENNReal.ofReal ((3 : ℝ) ^ t) * R = ENNReal.ofReal ((3 : ℝ) ^ t * R.toReal)
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) t),
    ENNReal.ofReal_toReal hR]

private theorem three_rpow_mul_toReal_nonneg {t : ℝ} (R : ℝ≥0∞) :
    (0 : ℝ) ≤ Real.rpow 3 t * R.toReal :=
  mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) t) ENNReal.toReal_nonneg

/-! ## 2. The two legs -/

/-- **BOTH Step-4 duality legs, produced from the display at `s′ < s`.** -/
theorem weakNegDualBounds_of_smoothDualDisplay {m : ℤ}
    {a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m))} {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) {u v : H1Function (openCubeSet (originCube d m))}
    (s' s : FractionalOrder) (p : FiniteLpExponent)
    (hlo : 0 < (s.1 - s'.1) * p.conjugate.exponent.toReal)
    (hhi : (s.1 - s'.1) * p.conjugate.exponent.toReal < (d : ℝ))
    {R : ℝ≥0∞} (hRtop : R ≠ ⊤)
    (hdisp : ENNReal.ofReal (Real.rpow 3 (-s'.1 * (m : ℝ))) *
        centeredCubeFluxComparisonSmoothDualLHS m a sigma0 u v s' p ≤ R) :
    WeakNegDualBoundOn (originCube d m) s.1
        (cgTestConst d (originCube d m) s.1 s'.1 p.conjugate.exponent.toReal *
          (sigma0⁻¹ * (Real.rpow 3 (s'.1 * (m : ℝ)) * R.toReal)))
        (centeredCubeGradientDifferenceL2Field m u v).toField ∧
      WeakNegDualBoundOn (originCube d m) s.1
        (cgTestConst d (originCube d m) s.1 s'.1 p.conjugate.exponent.toReal *
          (Real.rpow 3 (s'.1 * (m : ℝ)) * R.toReal))
        (centeredCubeFluxDifferenceL2Field m a sigma0 u v).toField := by
  obtain ⟨hgradRaw, hfluxRaw⟩ := smoothDual_legs_of_display hdisp
  have hweight := ofReal_three_rpow_mul_toReal (t := s'.1 * (m : ℝ)) hRtop
  have hDnn : (0 : ℝ) ≤ Real.rpow 3 (s'.1 * (m : ℝ)) * R.toReal :=
    three_rpow_mul_toReal_nonneg R
  /- the flux l -/
  have hflux : cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s' p
      (centeredCubeFluxDifferenceL2Field m a sigma0 u v) ≤
      ENNReal.ofReal (Real.rpow 3 (s'.1 * (m : ℝ)) * R.toReal) := by
    rwa [hweight] at hfluxRaw
  /- the gradient leg: strip the printed `σ₀` weig -/
  have hs0ne : ENNReal.ofReal sigma0 ≠ 0 := (ENNReal.ofReal_pos.mpr hsigma0).ne'
  have hs0top : ENNReal.ofReal sigma0 ≠ ⊤ := ENNReal.ofReal_ne_top
  have hstrip := mul_le_mul' (le_refl (ENNReal.ofReal sigma0)⁻¹) hgradRaw
  rw [← mul_assoc, ENNReal.inv_mul_cancel hs0ne hs0top, one_mul, hweight,
    ← ENNReal.ofReal_inv_of_pos hsigma0,
    ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hsigma0))] at hstrip
  have hgradnn : (0 : ℝ) ≤ sigma0⁻¹ * (Real.rpow 3 (s'.1 * (m : ℝ)) * R.toReal) :=
    mul_nonneg (le_of_lt (inv_pos.mpr hsigma0)) hDnn
  exact ⟨weakNegDualBoundOn_of_smoothDualLevel s' s p hlo hhi hgradnn hstrip,
    weakNegDualBoundOn_of_smoothDualLevel s' s p hlo hhi hDnn hflux⟩

end

end Algsuperdiff.Section4.Provider.Homogenization
