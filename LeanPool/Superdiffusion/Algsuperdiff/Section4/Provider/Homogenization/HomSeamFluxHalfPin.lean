/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxFreeCcg

/-!
# HomSeamFluxHalfPin

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The test-class constant at the print's own Schauder provenance `α = 1/2`

## Why this file exists

The printed test-class pin `cgTestConstBase d (homS M) (7 homS M/8)
p′` gauges the Step-4 dual pairing test at Hölder order `α = s = |log γ|⁻¹`.
The order gap of the conversion is then `α - s′ = s/8`, PROPORTIONAL to `s`, so
the radial kernel's geometric factor `(1 - 3^{-(α-s′)p′})⁻¹` degenerates like
`(s p′)⁻¹`, and the constant DIVERGES like `|log γ|^{1/p′}` (the machine-proved
lower-bound chain).  Since the pairing constant is linear in it, the
envelope condition `C_w ≤ C_w⁰` of `HomSchauderUniform.spineClauseConst_le_abs`
is unsatisfiable at that pin.

The print does NOT gauge the test at order `s`.  It derives the `W^{s,∞}` bound
of the Step-4 test from `C^{0,1/2}` Schauder data, whose
scale weight is the display's own `3^{m(1/2-s)}`; the DATA leg of this tree
already received that fixed-gap treatment (`cgOverlapDataConst`, taken at the
gap `1/2 - 49/100`, model-free by type), the TEST leg never did.

Re-pinning `α:= 1/2` keeps the dual order `s′ = 7s/8` where the pairing needs
it and evaluates the geometric factor at the FIXED gap `1/2 - 7s/8 ≥ 9/32`.
`cgTestConstBase_half_le` below is the resulting bound: `γ`-free, `s`-free,
`d`-and-`p′`-only.

## What this file supplies

* `recutKtestHalf` — the re-pinned test-class constant, and `recutKtestHalfBound`
  its model-free majorant (`cgTestConstBase_half_le` +
  `recutKtestHalf_le_bound`);
* `recutCwHalfFluxAt` — the free-`Ccg` pairing constant of `HomSeamFluxFreeCcg`
  with that constant in the `K_test` slot;
* `pairCwLegOf_le_of_bounds` — the generic leg envelope: at `sbase ≤ B` and
  `κ ≤ κ₀` the leg is bounded by an `sbase`-free and `κ`-free quantity;
* **THE ENVELOPE LEMMA** `recutCwHalfFluxAt_le_envelope`:
  `recutCwHalfFluxAt … ≤ C_w⁰` at every `M`, at
  the explicit `C_w⁰ = recutCwHalfEnvelope d hd1 Ccg Cgap Cen0` — a function of
  `d`, the printed exponent, `C_gap` and `C_en⁰` alone.  This is exactly the
  statement measured to be FALSE at the `α = s` pin;
* `spineClauseConst_le_abs_half` — the immediate consequence: the `K_abs` frame
  condition of the re-cut bundle closes BEFORE the model.

`Cen0` stays a free slot throughout: whether the energy-slot constant supplied
for it is itself model-uniform is a separate question, still open, and no
claim about it is made here.
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The conversion at the Schauder provenance `α = 1/2` -/

/-- The annulus ratio of the `(1/2, 7s/8, t)` conversion: the geometric ratio is
`3^{-(1/2 - 7s/8)t}`, whose order gap does NOT close with `s`. -/
theorem cgAnnulusRatio_half_eq (d : ℕ) (s t : ℝ) :
    Regularity.annulusRatio d (cgGagliardoBeta d (1 / 2) (7 * s / 8) t) =
      (3 : ℝ) ^ (-((1 / 2 - 7 * s / 8) * t)) := by
  have hd : ((3 : ℝ) ^ d) = (3 : ℝ) ^ ((d : ℕ) : ℝ) := (Real.rpow_natCast 3 d).symm
  rw [Regularity.annulusRatio, cgGagliardoBeta, hd, ← Real.rpow_sub (by norm_num)]
  congr 1
  ring

/-- **THE FIXED-GAP RADIAL CONSTANT.**  At `α = 1/2` the radial-kernel constant
of the `(7s/8, t)` conversion is bounded by the `s`-FREE quantity
`3^d 2^d (1 - 3^{-t/4})⁻¹`, for every base order `s ≤ 1/4`: the order gap is at
least `1/4`, so the geometric factor never degenerates.  Contrast the
`radialKernelConst_pinned_ge`, where the same constant at `α = s` grows like
`s⁻¹ = |log γ|`. -/
theorem cgRadialKernelConst_half_le (d : ℕ) {s t : ℝ} (hs : s ≤ 1 / 4) (ht : 0 < t) :
    Regularity.radialKernelConst d (cgGagliardoBeta d (1 / 2) (7 * s / 8) t) ≤
      (3 : ℝ) ^ d * 2 ^ d / (1 - (3 : ℝ) ^ (-(t / 4))) := by
  set beta := cgGagliardoBeta d (1 / 2) (7 * s / 8) t with hbeta
  have hgap0 : 0 < 1 / 2 - 7 * s / 8 := by linarith only [hs]
  have hnumeq : ((1 : ℝ) / 3) ^ (-beta) = (3 : ℝ) ^ beta := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_neg]
  have hble : beta ≤ (d : ℝ) := by
    rw [hbeta, cgGagliardoBeta]
    have hpos : 0 ≤ (1 / 2 - 7 * s / 8) * t := le_of_lt (mul_pos hgap0 ht)
    linarith only [hpos]
  have hnumle : (3 : ℝ) ^ beta ≤ (3 : ℝ) ^ d := by
    have h1 : (3 : ℝ) ^ beta ≤ (3 : ℝ) ^ ((d : ℕ) : ℝ) :=
      Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 3) |>.mpr hble
    rwa [Real.rpow_natCast] at h1
  have hratio : Regularity.annulusRatio d beta = (3 : ℝ) ^ (-((1 / 2 - 7 * s / 8) * t)) :=
    cgAnnulusRatio_half_eq d s t
  have hratle : Regularity.annulusRatio d beta ≤ (3 : ℝ) ^ (-(t / 4)) := by
    rw [hratio]
    refine Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 3) |>.mpr ?_
    have hquarter : 1 / 4 ≤ 1 / 2 - 7 * s / 8 := by linarith only [hs]
    have h4 : t / 4 ≤ (1 / 2 - 7 * s / 8) * t := by
      have hmul : (1 / 4 : ℝ) * t ≤ (1 / 2 - 7 * s / 8) * t :=
        mul_le_mul_of_nonneg_right hquarter ht.le
      linarith only [hmul]
    linarith only [h4]
  have hden1 : (3 : ℝ) ^ (-(t / 4)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [ht])
  have hdenpos : 0 < 1 - (3 : ℝ) ^ (-(t / 4)) := by linarith only [hden1]
  have hdenle : 1 - (3 : ℝ) ^ (-(t / 4)) ≤ 1 - Regularity.annulusRatio d beta := by
    linarith only [hratle]
  have hnum0 : (0 : ℝ) ≤ (3 : ℝ) ^ beta := (Real.rpow_pos_of_pos (by norm_num) _).le
  have h2d : (0 : ℝ) ≤ (2 : ℝ) ^ d := by positivity
  have hnn : (0 : ℝ) ≤ (3 : ℝ) ^ beta * 2 ^ d := mul_nonneg hnum0 h2d
  rw [Regularity.radialKernelConst, hnumeq]
  calc (3 : ℝ) ^ beta * 2 ^ d / (1 - Regularity.annulusRatio d beta)
      ≤ (3 : ℝ) ^ beta * 2 ^ d / (1 - (3 : ℝ) ^ (-(t / 4))) :=
        div_le_div_of_nonneg_left hnn hdenpos hdenle
    _ ≤ (3 : ℝ) ^ d * 2 ^ d / (1 - (3 : ℝ) ^ (-(t / 4))) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnumle h2d)
          (inv_nonneg.mpr hdenpos.le)

/-- **THE `γ`-UNIFORM TEST-CLASS CONSTANT.**  At the Schauder provenance
`α = 1/2`, for every base order `s ≤ 1/4` and every dual exponent `t > 0`,

```text
  cgTestConstBase d (1/2) (7s/8) t  ≤  d (1 + (3^d 2^d (1 - 3^{-t/4})⁻¹)^{1/t}),
```

with NO `s` — hence no `γ` — on the right. -/
theorem cgTestConstBase_half_le (d : ℕ) {s t : ℝ} (hs : s ≤ 1 / 4) (ht : 0 < t) :
    cgTestConstBase d (1 / 2) (7 * s / 8) t ≤
      (d : ℝ) * (1 + ((3 : ℝ) ^ d * 2 ^ d / (1 - (3 : ℝ) ^ (-(t / 4)))) ^ t⁻¹) := by
  have hgap0 : 0 < 1 / 2 - 7 * s / 8 := by linarith only [hs]
  have hblt : cgGagliardoBeta d (1 / 2) (7 * s / 8) t < (d : ℝ) :=
    cgGagliardoBeta_lt (mul_pos hgap0 ht)
  have hrad0 : (0 : ℝ) ≤
      Regularity.radialKernelConst d (cgGagliardoBeta d (1 / 2) (7 * s / 8) t) :=
    (Regularity.radialKernelConst_pos hblt).le
  have hmono : Regularity.radialKernelConst d
        (cgGagliardoBeta d (1 / 2) (7 * s / 8) t) ^ t⁻¹ ≤
      ((3 : ℝ) ^ d * 2 ^ d / (1 - (3 : ℝ) ^ (-(t / 4)))) ^ t⁻¹ :=
    Real.rpow_le_rpow hrad0 (cgRadialKernelConst_half_le d hs ht)
      (le_of_lt (inv_pos.mpr ht))
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  rw [cgTestConstBase]
  exact mul_le_mul_of_nonneg_left (by linarith only [hmono]) hd0

/-! ## 2. The re-pinned test constant and its model-free majorant -/

/-- **THE RE-PINNED TEST-CLASS CONSTANT.**  The printed test-class pin
with the Hölder gauge moved from `α = s` to the print's own Schauder provenance
`α = 1/2`; the dual order `s′ = 7s/8` is UNCHANGED. -/
def recutKtestHalf (d : ℕ) (hd1 : 1 ≤ d) (M : ABKModel d) : ℝ :=
  cgTestConstBase d (1 / 2) (7 * homS M / 8)
    (recutExponent d hd1).conjugate.exponent.toReal

/-- The model-free majorant of the re-pinned test-class constant: `d` and the
printed conjugate exponent only. -/
def recutKtestHalfBound (d : ℕ) (hd1 : 1 ≤ d) : ℝ :=
  (d : ℝ) * (1 + ((3 : ℝ) ^ d * 2 ^ d /
      (1 - (3 : ℝ) ^ (-((recutExponent d hd1).conjugate.exponent.toReal / 4)))) ^
    ((recutExponent d hd1).conjugate.exponent.toReal)⁻¹)

theorem recutKtestHalf_nonneg (d : ℕ) (hd1 : 1 ≤ d) (M : ABKModel d)
    (hlog : 4 ≤ |Real.log M.gamma|) : 0 ≤ recutKtestHalf d hd1 M := by
  have ht : 0 < (recutExponent d hd1).conjugate.exponent.toReal :=
    finiteLpExponent_toReal_pos (recutExponent d hd1).conjugate
  have hquarter : homS M ≤ 1 / 4 := homS_le_quarter hlog
  have hgap0 : 0 < 1 / 2 - 7 * homS M / 8 := by linarith only [hquarter]
  refine cgTestConstBase_nonneg d ?_
  exact mul_pos hgap0 ht

/-- **THE TEST CONSTANT IS `γ`-UNIFORM AT THE RE-PIN.**  This is the machine
fact the D2 re-cut rests on: the majorant names `d` and the printed exponent
only. -/
theorem recutKtestHalf_le_bound (d : ℕ) (hd1 : 1 ≤ d) (M : ABKModel d)
    (hlog : 4 ≤ |Real.log M.gamma|) :
    recutKtestHalf d hd1 M ≤ recutKtestHalfBound d hd1 := by
  have ht : 0 < (recutExponent d hd1).conjugate.exponent.toReal :=
    finiteLpExponent_toReal_pos (recutExponent d hd1).conjugate
  exact cgTestConstBase_half_le d (homS_le_quarter hlog) ht

theorem recutKtestHalfBound_nonneg (d : ℕ) (hd1 : 1 ≤ d) :
    0 ≤ recutKtestHalfBound d hd1 := by
  have ht : 0 < (recutExponent d hd1).conjugate.exponent.toReal :=
    finiteLpExponent_toReal_pos (recutExponent d hd1).conjugate
  have hden : (3 : ℝ) ^ (-((recutExponent d hd1).conjugate.exponent.toReal / 4)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [ht])
  have hnum : (0 : ℝ) ≤ (3 : ℝ) ^ d * 2 ^ d := by positivity
  have hpow : (0 : ℝ) ≤ ((3 : ℝ) ^ d * 2 ^ d /
      (1 - (3 : ℝ) ^ (-((recutExponent d hd1).conjugate.exponent.toReal / 4)))) ^
      ((recutExponent d hd1).conjugate.exponent.toReal)⁻¹ :=
    Real.rpow_nonneg (div_nonneg hnum (by linarith only [hden])) _
  rw [recutKtestHalfBound]
  exact mul_nonneg (Nat.cast_nonneg d) (by linarith only [hpow])

/-! ## 3. The generic leg envelope -/

/-- **THE LEG ENVELOPE.**  `pairCwLegOf` is bounded by a quantity free of the
base order `sbase` (only `sbase ≤ B` is used) and of the multiplier `κ` (only
`κ ≤ κ₀`).  Both degenerations live in the two factors bounded
here: the `(θ sbase)⁻¹ ⬝ sbase` cancellation is EXACT, and the window factor
`(s₂ - θ sbase)⁻¹` is monotone in `sbase`. -/
theorem pairCwLegOf_le_of_bounds (d : ℕ) {Ccg : ℝ} (p : FiniteLpExponent)
    (s2 : FractionalOrder) {Cgap Cen0 sbase kappa theta B kappa0 : ℝ}
    (hCcg0 : 0 ≤ Ccg) (hCgap : 0 < Cgap) (hCen0 : 0 ≤ Cen0) (hsbase : 0 < sbase)
    (hkappa : 0 ≤ kappa) (hkle : kappa ≤ kappa0) (htheta : 0 < theta)
    (hB : sbase ≤ B) (hBs2 : theta * B < s2.1)
    (hCdata0 : 0 ≤ cgOverlapDataConst d s2 p) (hs2gap : 5 < 10 * s2.1 * Real.log 3) :
    pairCwLegOf d Ccg p s2 Cgap Cen0 sbase kappa theta ≤
      kappa0 * Ccg * theta⁻¹ * Cen0 +
        kappa0 * Ccg * theta ^ (-(9 / 2) : ℝ) * (s2.1 - theta * B)⁻¹ *
          cgOverlapDataConst d s2 p * homGapConstAt s2.1 / Cgap := by
  have hsne : sbase ≠ 0 := ne_of_gt hsbase
  have htne : theta ≠ 0 := ne_of_gt htheta
  have hG0 : (0 : ℝ) ≤ homGapConstAt s2.1 := homGapConstAt_nonneg hs2gap
  have hthetapow : (0 : ℝ) ≤ theta ^ (-(9 / 2) : ℝ) := Real.rpow_nonneg htheta.le _
  have hthinv : (0 : ℝ) ≤ theta⁻¹ := inv_nonneg.mpr htheta.le
  /- the first summand: the `sbase` cancellation is exa -/
  have hfirsteq : kappa * Ccg * (theta * sbase)⁻¹ * Cen0 * sbase =
      kappa * Ccg * theta⁻¹ * Cen0 := by
    field_simp
  have hfirstle : kappa * Ccg * theta⁻¹ * Cen0 ≤ kappa0 * Ccg * theta⁻¹ * Cen0 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkle hCcg0) hthinv) hCen0
  /- the second summand: the window factor is monotone in the base ord -/
  have hwinB : (0 : ℝ) < s2.1 - theta * B := by linarith only [hBs2]
  have hthB : theta * sbase ≤ theta * B := mul_le_mul_of_nonneg_left hB htheta.le
  have hwins : (0 : ℝ) < s2.1 - theta * sbase := by linarith only [hwinB, hthB]
  have hinvle : (s2.1 - theta * sbase)⁻¹ ≤ (s2.1 - theta * B)⁻¹ :=
    inv_anti₀ hwinB (by linarith only [hthB])
  have hk3 : kappa * Ccg * theta ^ (-(9 / 2) : ℝ) ≤
      kappa0 * Ccg * theta ^ (-(9 / 2) : ℝ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkle hCcg0) hthetapow
  have hk30 : (0 : ℝ) ≤ kappa * Ccg * theta ^ (-(9 / 2) : ℝ) :=
    mul_nonneg (mul_nonneg hkappa hCcg0) hthetapow
  have hstep1 : kappa * Ccg * theta ^ (-(9 / 2) : ℝ) * (s2.1 - theta * sbase)⁻¹ ≤
      kappa0 * Ccg * theta ^ (-(9 / 2) : ℝ) * (s2.1 - theta * B)⁻¹ :=
    mul_le_mul hk3 hinvle (inv_nonneg.mpr hwins.le) (le_trans hk30 hk3)
  have hstep2 : kappa * Ccg * theta ^ (-(9 / 2) : ℝ) * (s2.1 - theta * sbase)⁻¹ *
      cgOverlapDataConst d s2 p ≤
      kappa0 * Ccg * theta ^ (-(9 / 2) : ℝ) * (s2.1 - theta * B)⁻¹ *
        cgOverlapDataConst d s2 p := mul_le_mul_of_nonneg_right hstep1 hCdata0
  have hstep3 : kappa * Ccg * theta ^ (-(9 / 2) : ℝ) * (s2.1 - theta * sbase)⁻¹ *
      cgOverlapDataConst d s2 p * homGapConstAt s2.1 ≤
      kappa0 * Ccg * theta ^ (-(9 / 2) : ℝ) * (s2.1 - theta * B)⁻¹ *
        cgOverlapDataConst d s2 p * homGapConstAt s2.1 :=
    mul_le_mul_of_nonneg_right hstep2 hG0
  have hsecond : kappa * Ccg * theta ^ (-(9 / 2) : ℝ) * (s2.1 - theta * sbase)⁻¹ *
        cgOverlapDataConst d s2 p * homGapConstAt s2.1 / Cgap ≤
      kappa0 * Ccg * theta ^ (-(9 / 2) : ℝ) * (s2.1 - theta * B)⁻¹ *
        cgOverlapDataConst d s2 p * homGapConstAt s2.1 / Cgap := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hstep3 (inv_nonneg.mpr hCgap.le)
  rw [pairCwLegOf, hfirsteq]
  linarith only [hfirstle, hsecond]

/-! ## 4. The re-pinned pairing constant and THE ENVELOPE -/

/-- The free-`Ccg` pairing constant of `HomSeamFluxFreeCcg` at the re-pinned
test constant. -/
def recutCwHalfFluxAt (d : ℕ) (hd1 : 1 ≤ d) (M : ABKModel d) (Ccg Cgap Cen0 : ℝ) : ℝ :=
  2 * pairCwOf d Ccg (recutExponent d hd1) recutOrderTop Cgap Cen0 (homS M)
    (recutKtestHalf d hd1 M)

/-- **THE MODEL-FREE PAIRING ENVELOPE**, at the numeral pin `p = 4d`,
`s₂ = 49/100`, `B = 1/4` (the gate `homS M ≤ 1/4`).  A function of `d`,
the printed exponent, `C_gap` and `C_en⁰` — no `M`, hence no `γ`. -/
def recutCwHalfEnvelope (d : ℕ) (hd1 : 1 ≤ d) (Ccg Cgap Cen0 : ℝ) : ℝ :=
  2 * ((1 * Ccg * (1 : ℝ)⁻¹ * Cen0 +
        1 * Ccg * (1 : ℝ) ^ (-(9 / 2) : ℝ) *
          ((recutOrderTop : FractionalOrder).1 - 1 * (1 / 4))⁻¹ *
          cgOverlapDataConst d recutOrderTop (recutExponent d hd1) *
          homGapConstAt (recutOrderTop : FractionalOrder).1 / Cgap) +
      (recutKtestHalfBound d hd1 * Ccg * (7 / 8 : ℝ)⁻¹ * Cen0 +
        recutKtestHalfBound d hd1 * Ccg * (7 / 8 : ℝ) ^ (-(9 / 2) : ℝ) *
          ((recutOrderTop : FractionalOrder).1 - 7 / 8 * (1 / 4))⁻¹ *
          cgOverlapDataConst d recutOrderTop (recutExponent d hd1) *
          homGapConstAt (recutOrderTop : FractionalOrder).1 / Cgap))

/-- **THE ENVELOPE LEMMA.**

The pairing constant of the re-cut lane, at the Schauder-provenance test pin, is
bounded by a quantity that does not mention the model.  This is the statement
measured to be UNSATISFIABLE at the `α = s` pin
(it grows like `|log γ|^{1-1/(4d)}`): the ONLY model-dependent factor of
`pairCwOf` was the test constant, and at `α = 1/2` it is bounded by
`recutKtestHalfBound`. -/
theorem recutCwHalfFluxAt_le_envelope (d : ℕ) (hd1 : 1 ≤ d) (M : ABKModel d)
    {Ccg Cgap Cen0 : ℝ} (hCcg0 : 0 ≤ Ccg) (hCgap : 0 < Cgap) (hCen0 : 0 ≤ Cen0)
    (hlog : 4 ≤ |Real.log M.gamma|) :
    recutCwHalfFluxAt d hd1 M Ccg Cgap Cen0 ≤ recutCwHalfEnvelope d hd1 Ccg Cgap Cen0 := by
  have hs : 0 < homS M := homS_pos_of_four _ hlog
  have hquarter : homS M ≤ 1 / 4 := homS_le_quarter hlog
  obtain ⟨hs2lt, hs2gt⟩ := recutOrderTop_window d hd1
  have hCdata0 : (0 : ℝ) ≤ cgOverlapDataConst d recutOrderTop (recutExponent d hd1) :=
    cgOverlapDataConst_nonneg d recutOrderTop (recutExponent d hd1)
      (holderHalf_window (p := recutExponent d hd1) hs2lt hs2gt).1
  have hgapexp := recutOrderTop_gapExponent
  have hKtest0 : (0 : ℝ) ≤ recutKtestHalf d hd1 M := recutKtestHalf_nonneg d hd1 M hlog
  have hKle : recutKtestHalf d hd1 M ≤ recutKtestHalfBound d hd1 :=
    recutKtestHalf_le_bound d hd1 M hlog
  have hleg1 := pairCwLegOf_le_of_bounds d (recutExponent d hd1) recutOrderTop
    (Ccg := Ccg) (Cgap := Cgap) (Cen0 := Cen0) (sbase := homS M) (kappa := 1)
    (theta := 1) (B := 1 / 4) (kappa0 := 1) hCcg0 hCgap hCen0 hs zero_le_one le_rfl
    one_pos hquarter (by rw [recutOrderTop_val]; norm_num) hCdata0 hgapexp
  have hleg2 := pairCwLegOf_le_of_bounds d (recutExponent d hd1) recutOrderTop
    (Ccg := Ccg) (Cgap := Cgap) (Cen0 := Cen0) (sbase := homS M)
    (kappa := recutKtestHalf d hd1 M) (theta := 7 / 8) (B := 1 / 4)
    (kappa0 := recutKtestHalfBound d hd1) hCcg0 hCgap hCen0 hs hKtest0 hKle
    (by norm_num) hquarter (by rw [recutOrderTop_val]; norm_num) hCdata0 hgapexp
  rw [recutCwHalfFluxAt, pairCwOf, recutCwHalfEnvelope]
  linarith only [hleg1, hleg2]

/-- The envelope is nonnegative on its own terms — no model is consulted. -/
theorem recutCwHalfEnvelope_nonneg (d : ℕ) (hd1 : 1 ≤ d) {Ccg Cgap Cen0 : ℝ}
    (hCcg0 : 0 ≤ Ccg) (hCgap : 0 < Cgap) (hCen0 : 0 ≤ Cen0) :
    0 ≤ recutCwHalfEnvelope d hd1 Ccg Cgap Cen0 := by
    have hKB0 : (0 : ℝ) ≤ recutKtestHalfBound d hd1 := recutKtestHalfBound_nonneg d hd1
    obtain ⟨hs2lt, hs2gt⟩ := recutOrderTop_window d hd1
    have hCdata0 : (0 : ℝ) ≤ cgOverlapDataConst d recutOrderTop (recutExponent d hd1) :=
      cgOverlapDataConst_nonneg d recutOrderTop (recutExponent d hd1)
        (holderHalf_window (p := recutExponent d hd1) hs2lt hs2gt).1
    have hG0 : (0 : ℝ) ≤ homGapConstAt (recutOrderTop : FractionalOrder).1 :=
      homGapConstAt_nonneg recutOrderTop_gapExponent
    have hw1 : (0 : ℝ) ≤ ((recutOrderTop : FractionalOrder).1 - 1 * (1 / 4))⁻¹ := by
      rw [recutOrderTop_val]; norm_num
    have hw2 : (0 : ℝ) ≤ ((recutOrderTop : FractionalOrder).1 - 7 / 8 * (1 / 4))⁻¹ := by
      rw [recutOrderTop_val]; norm_num
    have hp1 : (0 : ℝ) ≤ (1 : ℝ) ^ (-(9 / 2) : ℝ) := Real.rpow_nonneg zero_le_one _
    have hp2 : (0 : ℝ) ≤ (7 / 8 : ℝ) ^ (-(9 / 2) : ℝ) := Real.rpow_nonneg (by norm_num) _
    have hA : (0 : ℝ) ≤ 1 * Ccg * (1 : ℝ)⁻¹ * Cen0 :=
      mul_nonneg (mul_nonneg (by linarith only [hCcg0]) (by norm_num)) hCen0
    have hB : (0 : ℝ) ≤ 1 * Ccg * (1 : ℝ) ^ (-(9 / 2) : ℝ) *
        ((recutOrderTop : FractionalOrder).1 - 1 * (1 / 4))⁻¹ *
        cgOverlapDataConst d recutOrderTop (recutExponent d hd1) *
        homGapConstAt (recutOrderTop : FractionalOrder).1 / Cgap :=
      div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
        (by linarith only [hCcg0]) hp1) hw1) hCdata0) hG0) hCgap.le
    have hC : (0 : ℝ) ≤ recutKtestHalfBound d hd1 * Ccg * (7 / 8 : ℝ)⁻¹ * Cen0 :=
      mul_nonneg (mul_nonneg (mul_nonneg hKB0 hCcg0) (by norm_num)) hCen0
    have hD : (0 : ℝ) ≤ recutKtestHalfBound d hd1 * Ccg * (7 / 8 : ℝ) ^ (-(9 / 2) : ℝ) *
        ((recutOrderTop : FractionalOrder).1 - 7 / 8 * (1 / 4))⁻¹ *
        cgOverlapDataConst d recutOrderTop (recutExponent d hd1) *
        homGapConstAt (recutOrderTop : FractionalOrder).1 / Cgap :=
      div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
        (mul_nonneg hKB0 hCcg0) hp2) hw2) hCdata0) hG0) hCgap.le
    rw [recutCwHalfEnvelope]
    linarith only [hA, hB, hC, hD]

/-- **THE `K_abs` FRAME CONDITION, CLOSED BEFORE THE MODEL, AT THE RE-PIN.**

`HomSchauderUniform.spineClauseConst_le_abs` fed by the envelope: the absorbed
constant of the two clause displays is bounded by a quantity naming only `d`,
the printed exponent, `C_gap` and `C_en⁰`. -/
theorem spineClauseConst_le_abs_half (d : ℕ) (hd1 : 1 ≤ d) (M : ABKModel d)
    {Ccg Cgap Cen0 : ℝ} (hCcg0 : 0 ≤ Ccg) (hCgap : 0 < Cgap) (hCen0 : 0 ≤ Cen0)
    (hlog : 4 ≤ |Real.log M.gamma|) :
    spineClauseConst d (homS M) (recutExponent d hd1).exponent.toReal
        (recutCwHalfFluxAt d hd1 M Ccg Cgap Cen0) (stepFourSchauderConstU d) ≤
      (2 * stepFourSchauderConstU d + 288 * (d : ℝ) ^ (2 : ℕ)) *
        recutCwHalfEnvelope d hd1 Ccg Cgap Cen0 := by
  have hs : 0 < homS M := homS_pos_of_four _ hlog
  have hquarter : homS M ≤ 1 / 4 := homS_le_quarter hlog
  have hquot : (d : ℝ) / (recutExponent d hd1).exponent.toReal = 1 / 4 :=
    recutExponent_quotient d hd1
  have hguard : homS M + (d : ℝ) / (recutExponent d hd1).exponent.toReal ≤ 1 / 2 := by
    rw [hquot]; linarith only [hquarter]
  obtain ⟨hs2lt, hs2gt⟩ := recutOrderTop_window d hd1
  have hCdata0 : (0 : ℝ) ≤ cgOverlapDataConst d recutOrderTop (recutExponent d hd1) :=
    cgOverlapDataConst_nonneg d recutOrderTop (recutExponent d hd1)
      (holderHalf_window (p := recutExponent d hd1) hs2lt hs2gt).1
  have hgapexp := recutOrderTop_gapExponent
  have hss2 : homS M < (recutOrderTop : FractionalOrder).1 := by
    rw [recutOrderTop_val]; linarith only [hquarter]
  have h1 := pairCwLegOf_nonneg d (recutExponent d hd1) recutOrderTop (Ccg := Ccg)
    (Cgap := Cgap) (Cen0 := Cen0) (sbase := homS M) (kappa := 1) (theta := 1)
    hCcg0 hCgap hCen0 hs zero_le_one one_pos (by linarith only [hss2]) hCdata0 hgapexp
  have h2 := pairCwLegOf_nonneg d (recutExponent d hd1) recutOrderTop (Ccg := Ccg)
    (Cgap := Cgap) (Cen0 := Cen0) (sbase := homS M)
    (kappa := recutKtestHalf d hd1 M) (theta := 7 / 8) hCcg0 hCgap hCen0 hs
    (recutKtestHalf_nonneg d hd1 M hlog) (by norm_num)
    (by linarith only [hss2, hs]) hCdata0 hgapexp
  have hCw0 : (0 : ℝ) ≤ recutCwHalfFluxAt d hd1 M Ccg Cgap Cen0 := by
    rw [recutCwHalfFluxAt, pairCwOf]
    linarith only [h1, h2]
  exact spineClauseConst_le_abs d hCw0
    (recutCwHalfFluxAt_le_envelope d hd1 M hCcg0 hCgap hCen0 hlog) hguard

end

end Algsuperdiff.Section4.Provider.Homogenization
