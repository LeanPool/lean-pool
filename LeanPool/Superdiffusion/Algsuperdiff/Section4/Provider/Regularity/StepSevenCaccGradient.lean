/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenCaccVolume

/-!
# StepSevenCaccGradient

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 7c: `e.gradient.with.shom`

## The target

```text
  ν^{1/2}‖∇u‖_{L²((z+□_{n+1}) ∩ □_m)}
    ≤ C σ_{n'}^{1/2} 3^{(3/4)(1-α)(m-n)} 3^{-(m'-1)}
        ‖u - (u)_{(z+□_{m'-1})∩□_m}‖_{L²((z+□_{m'-1})∩□_m)}
      + C 3^{(3/4)(1-α)(m-n)} 3^{m/2} ( σ_m^{-1/2}[𝐠]_{W^{1/2,∞}(□_m)}
          + σ_m^{1/2}‖∇h‖_{W^{1/2,∞}(□_m)} 1_{z ∉ □_{m-1}} ) ,
```

`C = C(d, c_*)`, and `3/4 = 1/4` (volume) `+ 1/2` (Hölder).

## The scalar carriers

Following's `StepSixHolderExponent`, the step is proved on the S the display
names, so that the composition is a theorem about the two exponents and nothing
else:

* `gradLoc` — `ν^{1/2}‖∇u‖_{L²((z+□_{n+1})∩□_m)}`: for `𝐚_L = ν I + 𝐤` with
  `𝐤` antisymmetric this is the symmetric coefficient energy, so the reading is
  literally the manuscript's quantity.
* `gradCore` — the same energy on the Caccioppoli core `U_{n'-2}`.
* `volFac` — `3^{(d/2)(n'-n)}`, discharged here against the Step-3 budget and
  the `C₁` floor.
* `lamLo` — `Λ_{1/4,2}(z + □_{n'}; 𝐚_{L,n'})`, the Caccioppoli's ellipticity
  coefficient.
* `shomNp` — `σ_{n'}`.
* `oscLo` — `3^{-n'}‖u - (u)_{U_{n'}}‖_{L²(U_{n'})}`.
* `oscHi` — `3^{-(m'-1)}‖u - (u)_{U_{m'-1}}‖_{L²(U_{m'-1})}`.
* `dataOsc` — Step 6's OWN data leg, `3^{m/2}(σ_m^{-1}[𝐠]_{W^{1/2,∞}(□_m)} +
  ‖∇h‖_{W^{1/2,∞}(□_m)}1_{z∉□_{m-1}})`.
* `dataM` — the Caccioppoli's own data leg at scale `n'`, after
  `e.lambda.stability.applied`.

## The three conditional inputs, and nothing else

The display-named theorems carry exactly three conditional inputs:

* **`hcacc`** — `l.coarse.grained.Caccioppoli.RHS` applied at the good scale
  `n'`, in square-root (energy-norm) form.  See that module.
* **`hlambda`** — `e.lambda.stability.applied`, the upper leg at `k' = n'`:
  `Λ_{1/4,2}(z+□_{n'};𝐚_{L,n'})1_{G} ≤ C σ_{n'}`.
* **`hosc`** — `e.oscillation.Holder.bound` at scale `n'`, in exactly the
  shape `oscillationHolderBound_of_iterationResult` produces.

Everything else is discharged: the volume factor's budget arithmetic
(`StepSevenCaccVolume`), the exponent addition `1/4 + 1/2 = 3/4`, and the
`R₂ ≥ 1` monotonicity that lets the Caccioppoli's own data leg ride the same
power of three.

## References

* ABK26, `e.gradient.with.shom`.
* ABK26, `e.oscillation.Holder.bound`; `e.lambda.stability.applied`.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

noncomputable section

/-! ## 1. The composition core -/

/-- **The Step-7c composition, on abstract reals.**

From the four ingredients

```text
  gradLoc  ≤ volFac · gradCore                 (the volume half)
  volFac   ≤ Cvol · R₁                         (the budget, StepSevenCaccVolume)
  gradCore ≤ Ccacc·(√lamLo · oscLo) + Ccacc·dataM        (hcacc)
  lamLo    ≤ Clam · shomNp                                (hlambda)
  oscLo    ≤ Cosc·R₂·oscHi + Cosc·R₂·dataOsc              (hosc)
```

together with `1 ≤ R₂`, the display follows at the single output constant `Cvol
· Ccacc · (Cosc·√Clam + 1)` and the single power `R₁·R₂`.  Every step is a
product of nonnegative reals; no transcendental atom occurs. -/
theorem gradientWithShom_compose {Cvol Ccacc Cosc Clam R1 R2 gradLoc gradCore volFac
    oscLo oscHi dataOsc dataM lamLo shomNp : ℝ}
    (hCvol : 0 ≤ Cvol) (hCcacc : 0 ≤ Ccacc) (hCosc : 0 ≤ Cosc) (hClam : 0 ≤ Clam)
    (hR1 : 0 ≤ R1) (hR2one : 1 ≤ R2) (hgradCore : 0 ≤ gradCore)
    (hoscLo : 0 ≤ oscLo) (hoscHi : 0 ≤ oscHi) (hdataOsc : 0 ≤ dataOsc)
    (hdataM : 0 ≤ dataM)
    (hvol : gradLoc ≤ volFac * gradCore) (hvolB : volFac ≤ Cvol * R1)
    (hcacc : gradCore ≤ Ccacc * (Real.sqrt lamLo * oscLo) + Ccacc * dataM)
    (hlambda : lamLo ≤ Clam * shomNp)
    (hosc : oscLo ≤ Cosc * R2 * oscHi + Cosc * R2 * dataOsc) :
    gradLoc ≤
      (Cvol * Ccacc * (Cosc * Real.sqrt Clam + 1)) * Real.sqrt shomNp * (R1 * R2) * oscHi +
        (Cvol * Ccacc * (Cosc * Real.sqrt Clam + 1)) * (R1 * R2) *
          (Real.sqrt shomNp * dataOsc + dataM) := by
  have hR2 : (0 : ℝ) ≤ R2 := le_trans zero_le_one hR2one
  set S : ℝ := Real.sqrt shomNp with hSdef
  set L : ℝ := Real.sqrt Clam with hLdef
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  -- `√lamLo ≤ L · S`
  have hsqrt : Real.sqrt lamLo ≤ L * S := by
    calc Real.sqrt lamLo ≤ Real.sqrt (Clam * shomNp) := Real.sqrt_le_sqrt hlambda
      _ = L * S := Real.sqrt_mul hClam shomNp
  -- push `hosc` through the Caccioppoli
  have hA : Real.sqrt lamLo * oscLo ≤ L * S * (Cosc * R2 * oscHi) +
      L * S * (Cosc * R2 * dataOsc) := by
    have h1 : Real.sqrt lamLo * oscLo ≤ L * S * oscLo :=
      mul_le_mul_of_nonneg_right hsqrt hoscLo
    have h2 : L * S * oscLo ≤ L * S * (Cosc * R2 * oscHi + Cosc * R2 * dataOsc) :=
      mul_le_mul_of_nonneg_left hosc (mul_nonneg hL hS)
    have h3 : L * S * (Cosc * R2 * oscHi + Cosc * R2 * dataOsc) =
        L * S * (Cosc * R2 * oscHi) + L * S * (Cosc * R2 * dataOsc) := by ring
    linarith only [h1, h2, h3.ge, h3.le]
  have hB : gradCore ≤ Ccacc * (L * S * (Cosc * R2 * oscHi) +
      L * S * (Cosc * R2 * dataOsc)) + Ccacc * dataM := by
    have h := mul_le_mul_of_nonneg_left hA hCcacc
    linarith only [hcacc, h]
  -- push the volume factor through
  have hC : gradLoc ≤ (Cvol * R1) * gradCore := by
    have h := mul_le_mul_of_nonneg_right hvolB hgradCore
    linarith only [hvol, h]
  have hD : (Cvol * R1) * gradCore ≤ (Cvol * R1) *
      (Ccacc * (L * S * (Cosc * R2 * oscHi) + L * S * (Cosc * R2 * dataOsc)) +
        Ccacc * dataM) :=
    mul_le_mul_of_nonneg_left hB (mul_nonneg hCvol hR1)
  -- the four nonnegative slacks
  have p1 : 0 ≤ Cvol * Ccacc * S * R1 * R2 * oscHi := by
    have := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg hCvol hCcacc) hS) hR1) hR2) hoscHi
    exact this
  have p2 : 0 ≤ Cvol * Ccacc * S * R1 * R2 * dataOsc := by
    have := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg hCvol hCcacc) hS) hR1) hR2) hdataOsc
    exact this
  have p3 : 0 ≤ Cvol * Ccacc * Cosc * L * R1 * R2 * dataM := by
    have := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg hCvol hCcacc) hCosc) hL) hR1) hR2) hdataM
    exact this
  have p4 : 0 ≤ Cvol * Ccacc * R1 * dataM * (R2 - 1) := by
    have hR2m : (0 : ℝ) ≤ R2 - 1 := by linarith only [hR2one]
    have := mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg hCvol hCcacc) hR1) hdataM) hR2m
    exact this
  have hkey : (Cvol * R1) *
      (Ccacc * (L * S * (Cosc * R2 * oscHi) + L * S * (Cosc * R2 * dataOsc)) +
        Ccacc * dataM) +
      (Cvol * Ccacc * S * R1 * R2 * oscHi + Cvol * Ccacc * S * R1 * R2 * dataOsc +
        Cvol * Ccacc * Cosc * L * R1 * R2 * dataM +
        Cvol * Ccacc * R1 * dataM * (R2 - 1)) =
      (Cvol * Ccacc * (Cosc * L + 1)) * S * (R1 * R2) * oscHi +
        (Cvol * Ccacc * (Cosc * L + 1)) * (R1 * R2) * (S * dataOsc + dataM) := by
    ring
  linarith only [hC, hD, p1, p2, p3, p4, hkey.ge, hkey.le]

/-! ## 2. `e.gradient.with.shom` -/

/-- `1 ≤ 3^{c·(1-α)(m-n)}` for `c ≥ 0` in the Step-1/Step-3 regime. -/
theorem one_le_rpow_three_stepSixExponent {c alpha : ℝ} {n m : ℤ} (hc : 0 ≤ c)
    (halpha : alpha ≤ 1) (hnm : n ≤ m) :
    (1 : ℝ) ≤ Real.rpow (3 : ℝ) (c * stepSixExponent alpha n m) := by
  have hz : Real.rpow (3 : ℝ) (0 : ℝ) = 1 := Real.rpow_zero 3
  have hnn : (0 : ℝ) ≤ c * stepSixExponent alpha n m :=
    mul_nonneg hc (stepSixExponent_nonneg halpha hnm)
  have h : Real.rpow (3 : ℝ) (0 : ℝ) ≤
      Real.rpow (3 : ℝ) (c * stepSixExponent alpha n m) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hnn
  rwa [hz] at h

/-- `3^{c₁ t} · 3^{c₂ t} = 3^{(c₁+c₂) t}` at the Step-6 exponent argument. -/
theorem rpow_three_stepSixExponent_mul {c1 c2 alpha : ℝ} {n m : ℤ} :
    Real.rpow (3 : ℝ) (c1 * stepSixExponent alpha n m) *
        Real.rpow (3 : ℝ) (c2 * stepSixExponent alpha n m) =
      Real.rpow (3 : ℝ) ((c1 + c2) * stepSixExponent alpha n m) := by
  have h := Real.rpow_add (show (0 : ℝ) < 3 by norm_num)
    (c1 * stepSixExponent alpha n m) (c2 * stepSixExponent alpha n m)
  have hexp : c1 * stepSixExponent alpha n m + c2 * stepSixExponent alpha n m =
      (c1 + c2) * stepSixExponent alpha n m := by ring
  rw [hexp] at h
  exact h.symm

/-- **`e.gradient.with.shom`, as printed.**

The Caccioppoli at the lowest good scale `n'`, the Hölder bound at that same
scale, and the volume factor, composed.  The exponent is the printed `3/4 = 1/4
+ 1/2`.

The data bracket is the honest `σ_{n'}^{1/2}·dataOsc + dataM`; see the module
docstring for the (separately proved) collapse to the printed
`3^{m/2}(σ_m^{-1/2}[𝐠] + σ_m^{1/2}‖∇h‖1)`.

`hcacc`, `hlambda`, `hosc` are the only conditional inputs. -/
theorem stepSevenGradientWithShom (d : ℕ) {C1 alpha delta : ℝ} {B : ℕ} {n m n' : ℤ}
    {Ccacc Cosc Clam gradLoc gradCore oscLo oscHi dataOsc dataM lamLo shomNp : ℝ}
    (hC1 : 2 * (d : ℝ) + 2 ≤ C1) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hnm : n ≤ m) (hdelta : delta ≤ C1⁻¹ * (1 - alpha))
    (hgap : n' - n ≤ (B : ℤ) + 6)
    (hbudget : (B : ℝ) ≤ delta * (((m - n).toNat : ℝ) + 1))
    (hCcacc : 0 ≤ Ccacc) (hCosc : 0 ≤ Cosc) (hClam : 0 ≤ Clam)
    (hgradCore : 0 ≤ gradCore) (hoscLo : 0 ≤ oscLo) (hoscHi : 0 ≤ oscHi)
    (hdataOsc : 0 ≤ dataOsc) (hdataM : 0 ≤ dataM)
    (hvol : gradLoc ≤
      Real.rpow (3 : ℝ) (((d : ℝ) / 2) * ((n' : ℝ) - (n : ℝ))) * gradCore)
    (hcacc : gradCore ≤ Ccacc * (Real.sqrt lamLo * oscLo) + Ccacc * dataM)
    (hlambda : lamLo ≤ Clam * shomNp)
    (hosc : oscLo ≤
      Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * oscHi +
        Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * dataOsc) :
    gradLoc ≤
      (Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) * Ccacc *
          (Cosc * Real.sqrt Clam + 1)) * Real.sqrt shomNp *
          Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) * oscHi +
        (Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) * Ccacc *
          (Cosc * Real.sqrt Clam + 1)) *
          Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
          (Real.sqrt shomNp * dataOsc + dataM) := by
  have hvolB := three_rpow_stepSevenVolume_le d hC1 halpha0 halpha1 hnm hdelta hgap hbudget
  have hCvol : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hR1 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hR2one : (1 : ℝ) ≤ Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) :=
    one_le_rpow_three_stepSixExponent (by norm_num) halpha1 hnm
  have hprod : Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) *
      Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) =
      Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) := by
    rw [rpow_three_stepSixExponent_mul]
    norm_num
  have h := gradientWithShom_compose hCvol hCcacc hCosc hClam hR1 hR2one hgradCore
    hoscLo hoscHi hdataOsc hdataM hvol hvolB hcacc hlambda hosc
  rwa [hprod] at h

end

end Algsuperdiff.Section4.Provider.Regularity
