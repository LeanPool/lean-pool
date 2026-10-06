/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Geometry.PositiveSqrtCongruence
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ResponseBlockObjects
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.SourceLoadBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.TerminalEnergyMeasurability
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# High-contrast homogenization: Entry.Response.Rows.SourceLoadHeadBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Source-Load Head Bound for the Cell-Pairing Row

The cutoff-mean rows average the cutoff fluctuation over a partition of the terminal cell against
a pathwise pairing; discrete Cauchy-Schwarz for weighted flat averages bounds this by the
geometric mean of the pairing's flat-averaged head and twice the flat-averaged scalar deficit,
and annealed Cauchy-Schwarz then moves the expectation inside each factor. The head factor is the
depth-zero summand of the source load `L_s`, whose series sums over triadic generations the
squared `(b^{1/2}, S_*^{-1/2})`-norm of the annealed mean; the expectation of its squared
two-term head is bounded, again by annealed Cauchy-Schwarz, by the square of the sum of the
square roots of the expectations of its summands. Since every summand of `L_s` is nonnegative,
the convergent series dominates each of them, and the expectation of a pathwise coarse-block
quadratic form equals the same form of the annealed block.  The head bound at the terminal scale
is what the cell half of `p.response.transfer` consumes.
-/

section
/-!
## Cauchy--Schwarz for the square roots of two integrable functions

For a measure `P` and integrable nonnegative functions `f` and `g`, the integral of the product of
the square roots is bounded by the product of the square roots of the integrals:

`∫ √f √g ≤ √(∫ f) · √(∫ g)`.

This is the annealed Cauchy--Schwarz inequality behind the cell part of the first error row of
`e.response.cutoff.estimate`: it compares the difference energy `f` with the cell energy `g` of
the sample.  The proof integrates the pointwise Young inequality
`√f √g ≤ (lam f + g / lam) / 2` against the measure; the optimal choice of `lam` reproduces the
geometric mean `√(∫ f) · √(∫ g)`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Cauchy--Schwarz for the square roots of two integrable functions: if `f` and `g` are integrable
and nonnegative, then `∫ √f √g ≤ √(∫ f) · √(∫ g)`.  The pointwise Young inequality
`2 √(f a) √(g a) ≤ lam f a + g a / lam` is integrated against `P`, and the parameter `lam` is then
chosen as `√(∫ g) / √(∫ f)`; when one of the integrals vanishes, the corresponding function vanishes
almost everywhere and so does the product.  This is the annealed Cauchy--Schwarz inequality behind
the cell part of the first error row of `e.response.cutoff.estimate`. -/
theorem integral_sqrt_mul_sqrt_le_sqrt_mul_sqrt {alpha : Type*} [MeasurableSpace alpha]
    (P : Measure alpha) {f g : alpha → ℝ}
    (hf : Integrable f P) (hg : Integrable g P)
    (hf0 : ∀ a, 0 ≤ f a) (hg0 : ∀ a, 0 ≤ g a)
    (hfg : Integrable (fun a => Real.sqrt (f a) * Real.sqrt (g a)) P) :
    (∫ a, Real.sqrt (f a) * Real.sqrt (g a) ∂P)
      ≤ Real.sqrt (∫ a, f a ∂P) * Real.sqrt (∫ a, g a ∂P) := by
  have hA0 : 0 ≤ ∫ a, f a ∂P := integral_nonneg fun a => hf0 a
  have hB0 : 0 ≤ ∫ a, g a ∂P := integral_nonneg fun a => hg0 a
  have hR0 : 0 ≤ Real.sqrt (∫ a, f a ∂P) * Real.sqrt (∫ a, g a ∂P) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rcases eq_or_lt_of_le hA0 with hA | hA
  · -- `∫ f = 0`, so `f` vanishes almost everywhere and the product has zero integral.
    have hfae : f =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun a => hf0 a) hf).mp hA.symm
    have hprodae : (fun a => Real.sqrt (f a) * Real.sqrt (g a)) =ᵐ[P] 0 :=
      hfae.mono fun a ha => by
        show Real.sqrt (f a) * Real.sqrt (g a) = 0
        simp only [ha, Pi.zero_apply, Real.sqrt_zero, zero_mul]
    have hI : (∫ a, Real.sqrt (f a) * Real.sqrt (g a) ∂P) = 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun a => mul_nonneg (Real.sqrt_nonneg (f a)) (Real.sqrt_nonneg (g a))) hfg).mpr hprodae
    exact hI.trans_le hR0
  · rcases eq_or_lt_of_le hB0 with hB | hB
    · -- `∫ g = 0`, symmetric.
      have hgae : g =ᵐ[P] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun a => hg0 a) hg).mp hB.symm
      have hprodae : (fun a => Real.sqrt (f a) * Real.sqrt (g a)) =ᵐ[P] 0 :=
        hgae.mono fun a ha => by
          show Real.sqrt (f a) * Real.sqrt (g a) = 0
          simp only [ha, Pi.zero_apply, Real.sqrt_zero, mul_zero]
      have hI : (∫ a, Real.sqrt (f a) * Real.sqrt (g a) ∂P) = 0 :=
        (integral_eq_zero_iff_of_nonneg
          (fun a => mul_nonneg (Real.sqrt_nonneg (f a)) (Real.sqrt_nonneg (g a))) hfg).mpr hprodae
      exact hI.trans_le hR0
    · -- Both integrals are positive: integrate the pointwise Young inequality.
      set lam : ℝ := Real.sqrt (∫ a, g a ∂P) / Real.sqrt (∫ a, f a ∂P) with hlamdef
      have hlam : 0 < lam := by
        rw [hlamdef]
        exact div_pos (Real.sqrt_pos.mpr hB) (Real.sqrt_pos.mpr hA)
      have hpt : ∀ a, Real.sqrt (f a) * Real.sqrt (g a)
          ≤ (lam * f a + g a / lam) / 2 := by
        intro a
        have hmul : 2 * lam * (Real.sqrt (f a) * Real.sqrt (g a))
            ≤ lam ^ 2 * f a + g a := by
          have h := sq_nonneg (lam * Real.sqrt (f a) - Real.sqrt (g a))
          nlinarith only [h, Real.sq_sqrt (hf0 a), Real.sq_sqrt (hg0 a)]
        have heq : (lam ^ 2 * f a + g a) / (2 * lam) = (lam * f a + g a / lam) / 2 := by
          field_simp
        rw [← heq]
        rw [le_div_iff₀ (by linarith only [hlam] : (0 : ℝ) < 2 * lam)]
        nlinarith only [hmul]
      have hRint : Integrable (fun a => (lam * f a + g a / lam) / 2) P :=
        ((hf.const_mul lam).add (hg.div_const lam)).div_const 2
      have hmono : (∫ a, Real.sqrt (f a) * Real.sqrt (g a) ∂P)
          ≤ ∫ a, (lam * f a + g a / lam) / 2 ∂P :=
        integral_mono_ae hfg hRint (Filter.Eventually.of_forall hpt)
      have hint : (∫ a, (lam * f a + g a / lam) / 2 ∂P)
          = (lam * (∫ a, f a ∂P) + (∫ a, g a ∂P) / lam) / 2 := by
        rw [integral_div, integral_add (hf.const_mul lam) (hg.div_const lam),
          integral_const_mul, integral_div]
      have hAne : Real.sqrt (∫ a, f a ∂P) ≠ 0 := (Real.sqrt_pos.mpr hA).ne'
      have hBne : Real.sqrt (∫ a, g a ∂P) ≠ 0 := (Real.sqrt_pos.mpr hB).ne'
      have hA' : (∫ a, f a ∂P) = Real.sqrt (∫ a, f a ∂P) * Real.sqrt (∫ a, f a ∂P) := by
        rw [← sq]
        exact (Real.sq_sqrt hA0).symm
      have hB' : (∫ a, g a ∂P) = Real.sqrt (∫ a, g a ∂P) * Real.sqrt (∫ a, g a ∂P) := by
        rw [← sq]
        exact (Real.sq_sqrt hB0).symm
      have hAd : (∫ a, f a ∂P) / Real.sqrt (∫ a, f a ∂P) = Real.sqrt (∫ a, f a ∂P) := by
        rw [div_eq_iff hAne]
        exact hA'
      have hBd : (∫ a, g a ∂P) / Real.sqrt (∫ a, g a ∂P) = Real.sqrt (∫ a, g a ∂P) := by
        rw [div_eq_iff hBne]
        exact hB'
      have hla : lam * (∫ a, f a ∂P)
          = Real.sqrt (∫ a, f a ∂P) * Real.sqrt (∫ a, g a ∂P) := by
        calc lam * (∫ a, f a ∂P)
            = (Real.sqrt (∫ a, g a ∂P) / Real.sqrt (∫ a, f a ∂P))
              * (∫ a, f a ∂P) := by rw [hlamdef]
          _ = Real.sqrt (∫ a, g a ∂P)
              * ((∫ a, f a ∂P) / Real.sqrt (∫ a, f a ∂P)) := by
              rw [div_mul_eq_mul_div, mul_div_assoc]
          _ = Real.sqrt (∫ a, g a ∂P) * Real.sqrt (∫ a, f a ∂P) := by rw [hAd]
          _ = Real.sqrt (∫ a, f a ∂P) * Real.sqrt (∫ a, g a ∂P) := by ring
      have hlb : (∫ a, g a ∂P) / lam
          = Real.sqrt (∫ a, f a ∂P) * Real.sqrt (∫ a, g a ∂P) := by
        calc (∫ a, g a ∂P) / lam
            = (∫ a, g a ∂P) / (Real.sqrt (∫ a, g a ∂P) / Real.sqrt (∫ a, f a ∂P)) := by
              rw [hlamdef]
          _ = (∫ a, g a ∂P) * Real.sqrt (∫ a, f a ∂P) / Real.sqrt (∫ a, g a ∂P) := by
              rw [div_div_eq_mul_div]
          _ = ((∫ a, g a ∂P) / Real.sqrt (∫ a, g a ∂P)) * Real.sqrt (∫ a, f a ∂P) := by
              rw [div_mul_eq_mul_div]
          _ = Real.sqrt (∫ a, g a ∂P) * Real.sqrt (∫ a, f a ∂P) := by rw [hBd]
          _ = Real.sqrt (∫ a, f a ∂P) * Real.sqrt (∫ a, g a ∂P) := by ring
      have hval : (lam * (∫ a, f a ∂P) + (∫ a, g a ∂P) / lam) / 2
          = Real.sqrt (∫ a, f a ∂P) * Real.sqrt (∫ a, g a ∂P) := by
        rw [hla, hlb]
        ring
      exact (hmono.trans_eq hint).trans_eq hval

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Weighted flat averages over the cells of a partition

The first error row of `e.response.cutoff.estimate` averages over the scale-`s` subcells of a
terminal cell.  The cutoff fluctuations about one are bounded by one in absolute value, so the
weighted flat average of the fluctuation times an integrand is controlled by the flat average of
the absolute integrand; the cross terms are then averaged by the discrete Cauchy--Schwarz
inequality for flat averages.  This file records those two finite-sum steps, together with the
additivity of the flat average.
-/

namespace HCPolySupport.HighContrast.Multiscale

noncomputable section

/-- **Weighted flat average against a bounded weight.**  If every weight `fl w` is bounded in
absolute value by one on the finite index set `Z`, then the flat average of `fl w * v w` is
bounded by the flat average of `|v w|`.  The weight bound enters pointwise through
`|fl w * v w| ≤ |v w|`, and the nonnegative factor `(Z.card : ℝ)⁻¹` passes through the resulting
sum inequality.  This is the weighted cell step of `e.response.cutoff.estimate`. -/
theorem abs_flat_average_weighted_le {iota : Type*} (Z : Finset iota) (fl v : iota → ℝ)
    (hfl : ∀ w ∈ Z, |fl w| ≤ 1) :
    |(Z.card : ℝ)⁻¹ * ∑ w ∈ Z, fl w * v w| ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, |v w| := by
  have hc : 0 ≤ (Z.card : ℝ)⁻¹ := by positivity
  have hS : |∑ w ∈ Z, fl w * v w| ≤ ∑ w ∈ Z, |v w| := by
    calc
      |∑ w ∈ Z, fl w * v w| ≤ ∑ w ∈ Z, |fl w * v w| :=
        Finset.abs_sum_le_sum_abs (fun w => fl w * v w) Z
      _ = ∑ w ∈ Z, |fl w| * |v w| :=
        Finset.sum_congr rfl fun w _ => abs_mul (fl w) (v w)
      _ ≤ ∑ w ∈ Z, 1 * |v w| :=
        Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_right (hfl w hw) (abs_nonneg (v w))
      _ = ∑ w ∈ Z, |v w| := by simp
  calc
    |(Z.card : ℝ)⁻¹ * ∑ w ∈ Z, fl w * v w|
        = (Z.card : ℝ)⁻¹ * |∑ w ∈ Z, fl w * v w| := by
          rw [abs_mul, abs_of_nonneg hc]
    _ ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, |v w| := mul_le_mul_of_nonneg_left hS hc

/-- **Discrete Cauchy--Schwarz for flat averages.**  If `x` and `y` are nonnegative on `Z`, the
flat average of `√(x w) * √(y w)` is bounded by the product of the square roots of the flat
averages of `x` and of `y`.  The Cauchy--Schwarz inequality for finite sums gives the unnormalized
bound, and multiplying by the nonnegative factor `(Z.card : ℝ)⁻¹` turns the product of the two
square roots into the product of the normalized square roots.  This controls the cross terms of
the optimizer replacement in `e.response.cutoff.estimate`. -/
theorem flat_average_sqrt_mul_sqrt_le {iota : Type*} (Z : Finset iota) (x y : iota → ℝ)
    (hx : ∀ w ∈ Z, 0 ≤ x w) (hy : ∀ w ∈ Z, 0 ≤ y w) :
    (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, Real.sqrt (x w) * Real.sqrt (y w)
      ≤ Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, x w)
        * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, y w) := by
  have hc : 0 ≤ (Z.card : ℝ)⁻¹ := by positivity
  have hsq : ∑ w ∈ Z, Real.sqrt (x w) * Real.sqrt (y w)
      ≤ Real.sqrt (∑ w ∈ Z, x w) * Real.sqrt (∑ w ∈ Z, y w) := by
    have h1 : ∑ w ∈ Z, Real.sqrt (x w) ^ 2 = ∑ w ∈ Z, x w :=
      Finset.sum_congr rfl fun w hw => Real.sq_sqrt (hx w hw)
    have h2 : ∑ w ∈ Z, Real.sqrt (y w) ^ 2 = ∑ w ∈ Z, y w :=
      Finset.sum_congr rfl fun w hw => Real.sq_sqrt (hy w hw)
    have h := Real.sum_mul_le_sqrt_mul_sqrt Z
      (fun w => Real.sqrt (x w)) (fun w => Real.sqrt (y w))
    simpa only [h1, h2] using h
  have hsqrt : Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, x w)
        * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, y w)
      = (Z.card : ℝ)⁻¹
        * (Real.sqrt (∑ w ∈ Z, x w) * Real.sqrt (∑ w ∈ Z, y w)) := by
    rw [Real.sqrt_mul hc, Real.sqrt_mul hc]
    conv_rhs => rw [← Real.mul_self_sqrt hc]
    ring
  calc
    (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, Real.sqrt (x w) * Real.sqrt (y w)
        ≤ (Z.card : ℝ)⁻¹
          * (Real.sqrt (∑ w ∈ Z, x w) * Real.sqrt (∑ w ∈ Z, y w)) :=
          mul_le_mul_of_nonneg_left hsq hc
    _ = Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, x w)
          * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, y w) := hsqrt.symm

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Cauchy--Schwarz with the expectation outside the cell average

The first error row of `e.response.cutoff.estimate` pairs the cutoff fluctuation cell averages
`c w`, which are bounded by one in absolute value, against the pathwise product `√(f w a) √(g w a)`
of the difference and cell energies.  The weighted flat average over the scale-`s` subcells is
controlled pathwise by the flat Cauchy--Schwarz product of the two energies, and the sample
expectation is then moved inside each factor by the annealed square-root Cauchy--Schwarz
inequality.  The result is the direct full-dual pairing estimate of `e.response.cutoff.estimate`:
the weights stay inside the cell average, while the expectation acts linearly on each energy.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Expectation outside the weighted cell average.**  Let `c` be the cutoff fluctuation cell
averages, bounded by one on the finite index set `Z`, and let `f` and `g` be nonnegative families of
sample functions.  Then the modulus of the sample expectation of the weighted flat average of
`c w * (√(f w a) * √(g w a))` is bounded by the product of the square roots of the sample
expectations of the flat averages of `f` and of `g`.

Pathwise, the bounded weights are peeled off by the flat weighted-average bound, and the remaining
flat average of `√(f w a) √(g w a)` is estimated by the discrete Cauchy--Schwarz inequality for
flat averages.  Integrating the resulting pointwise bound and applying the annealed square-root
Cauchy--Schwarz inequality moves the expectation inside each factor.  This is the weighted cell
step of `e.response.cutoff.estimate`. -/
theorem abs_integral_flat_weighted_prod_le {iota alpha : Type*} [MeasurableSpace alpha]
    (P : Measure alpha) (Z : Finset iota) (c : iota → ℝ) (hc : ∀ w ∈ Z, |c w| ≤ 1)
    (f g : iota → alpha → ℝ)
    (hf : ∀ w ∈ Z, ∀ a, 0 ≤ f w a) (hg : ∀ w ∈ Z, ∀ a, 0 ≤ g w a)
    (hFint : Integrable (fun a => (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, f w a) P)
    (hGint : Integrable (fun a => (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, g w a) P)
    (hMidint : Integrable (fun a =>
      Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, f w a)
        * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, g w a)) P)
    (hPint : Integrable (fun a => (Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
      c w * (Real.sqrt (f w a) * Real.sqrt (g w a))) P) :
    |∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w * (Real.sqrt (f w a) * Real.sqrt (g w a)) ∂P|
      ≤ Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, f w a ∂P)
        * Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, g w a ∂P) := by
  have hpt : ∀ a, |(Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
        c w * (Real.sqrt (f w a) * Real.sqrt (g w a))|
      ≤ Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, f w a)
        * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, g w a) := by
    intro a
    have h1 := abs_flat_average_weighted_le Z c
      (fun w => Real.sqrt (f w a) * Real.sqrt (g w a)) hc
    have h2 : (Z.card : ℝ)⁻¹
          * ∑ w ∈ Z, |Real.sqrt (f w a) * Real.sqrt (g w a)|
        = (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, Real.sqrt (f w a) * Real.sqrt (g w a) := by
      congr 1
      exact Finset.sum_congr rfl fun w _ =>
        abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have h3 := flat_average_sqrt_mul_sqrt_le Z (fun w => f w a) (fun w => g w a)
      (fun w hw => hf w hw a) (fun w hw => hg w hw a)
    exact h1.trans (h2.trans_le h3)
  have hF0 : ∀ a, 0 ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, f w a := by
    intro a
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun w hw => hf w hw a)
  have hG0 : ∀ a, 0 ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, g w a := by
    intro a
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun w hw => hg w hw a)
  have hmono : (∫ a, |(Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
        c w * (Real.sqrt (f w a) * Real.sqrt (g w a))| ∂P)
      ≤ ∫ a, Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, f w a)
          * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, g w a) ∂P :=
    integral_mono hPint.abs hMidint hpt
  calc
    |∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
        c w * (Real.sqrt (f w a) * Real.sqrt (g w a)) ∂P|
        ≤ ∫ a, |(Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
            c w * (Real.sqrt (f w a) * Real.sqrt (g w a))| ∂P :=
          abs_integral_le_integral_abs
    _ ≤ ∫ a, Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, f w a)
          * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, g w a) ∂P := hmono
    _ ≤ Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, f w a ∂P)
          * Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, g w a ∂P) :=
          integral_sqrt_mul_sqrt_le_sqrt_mul_sqrt P hFint hGint hF0 hG0 hMidint

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The cell pairing row of the cutoff-mean estimate, abstractly

The cell half of the two cutoff-mean rows of `e.response.cutoff.estimate` pairs the cutoff
fluctuation cell averages `c w`, bounded by one in absolute value, against a full-dual pairing
`pairing w a`.  Each subcell contributes a pairing controlled pathwise by the cell's own
source-load head `G w a` times the square root of twice its scalar deficit `D w a`.  Averaging the
bounded weight against that pathwise control and then applying the discrete and the annealed
Cauchy--Schwarz inequalities bounds the modulus of the sample expectation by the geometric mean of
the annealed head and the annealed flat deficit, the latter being exactly `2 tau`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The cell pairing row of the cutoff-mean estimate.**  Let `c` be the cutoff fluctuation cell
averages, bounded by one on the finite index set `Z`, and let `pairing` be a full-dual pairing whose
subcell values are controlled pathwise by the source-load head `G` and the scalar deficit `D`
through `|pairing w a| ≤ G w a * √(2 * D w a)`.  If the annealed flat average of `G ^ 2` is at most
`Lhead` and the annealed flat average of `2 * D` equals `2 * tau`, then the modulus of the sample
expectation of the weighted flat average of `c w * pairing w a` is at most `√Lhead * √(2 * tau)`.
This is the cell half of the two cutoff-mean rows of `e.response.cutoff.estimate`. -/
theorem abs_integral_flat_weighted_pairing_le {iota alpha : Type*} [MeasurableSpace alpha]
    (P : Measure alpha) (Z : Finset iota) (c : iota → ℝ) (hc : ∀ w ∈ Z, |c w| ≤ 1)
    (pairing G D : iota → alpha → ℝ) (Lhead tau : ℝ)
    (hG : ∀ w ∈ Z, ∀ a, 0 ≤ G w a) (hD : ∀ w ∈ Z, ∀ a, 0 ≤ D w a)
    (hbd : ∀ w ∈ Z, ∀ a, |pairing w a| ≤ G w a * Real.sqrt (2 * D w a))
    (hGsq : (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2 ∂P) ≤ Lhead)
    (hDval : (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a ∂P) = 2 * tau)
    (hFint : Integrable (fun a => (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2) P)
    (hDint : Integrable (fun a => (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a) P)
    (hMidint : Integrable (fun a =>
      Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2)
        * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a)) P)
    (hPint : Integrable (fun a => (Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
      c w * (Real.sqrt ((G w a) ^ 2) * Real.sqrt (2 * D w a))) P)
    (hPint' : Integrable (fun a => (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w * pairing w a) P) :
    |∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w * pairing w a ∂P|
      ≤ Real.sqrt Lhead * Real.sqrt (2 * tau) := by
  have hprod : |∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
        c w * (Real.sqrt ((G w a) ^ 2) * Real.sqrt (2 * D w a)) ∂P|
      ≤ Real.sqrt Lhead * Real.sqrt (2 * tau) := by
    have h0 := abs_integral_flat_weighted_prod_le P Z c hc
      (fun w a => (G w a) ^ 2) (fun w a => 2 * D w a)
      (fun w _ a => sq_nonneg (G w a))
      (fun w hw a => by linarith only [hD w hw a])
      hFint hDint hMidint hPint
    calc
      |∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
          c w * (Real.sqrt ((G w a) ^ 2) * Real.sqrt (2 * D w a)) ∂P|
          ≤ Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2 ∂P)
            * Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a ∂P) := h0
      _ = Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2 ∂P)
            * Real.sqrt (2 * tau) := by rw [hDval]
      _ ≤ Real.sqrt Lhead * Real.sqrt (2 * tau) :=
            mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hGsq) (Real.sqrt_nonneg _)
  have hpt : ∀ a, |(Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w * pairing w a|
      ≤ Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2)
        * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a) := by
    intro a
    have h1 := abs_flat_average_weighted_le Z c (fun w => pairing w a) hc
    have h2 : (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, |pairing w a|
        ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
            Real.sqrt ((G w a) ^ 2) * Real.sqrt (2 * D w a) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun w hw => by
          rw [Real.sqrt_sq (hG w hw a)]
          exact hbd w hw a)
        (by positivity)
    have h3 := flat_average_sqrt_mul_sqrt_le Z (fun w => (G w a) ^ 2)
      (fun w => 2 * D w a)
      (fun w _ => sq_nonneg (G w a))
      (fun w hw => by linarith only [hD w hw a])
    exact h1.trans (h2.trans h3)
  have hF0 : ∀ a, 0 ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2 := by
    intro a
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun w _ => sq_nonneg (G w a))
  have hD0 : ∀ a, 0 ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a := by
    intro a
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun w hw => by linarith only [hD w hw a])
  calc
    |∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w * pairing w a ∂P|
        ≤ ∫ a, |(Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w * pairing w a| ∂P :=
          abs_integral_le_integral_abs
    _ ≤ ∫ a, Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2)
          * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a) ∂P :=
          integral_mono hPint'.abs hMidint hpt
    _ ≤ Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2 ∂P)
          * Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a ∂P) :=
          integral_sqrt_mul_sqrt_le_sqrt_mul_sqrt P hFint hDint hF0 hD0 hMidint
    _ = Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2 ∂P)
          * Real.sqrt (2 * tau) := by rw [hDval]
    _ ≤ Real.sqrt Lhead * Real.sqrt (2 * tau) :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hGsq) (Real.sqrt_nonneg _)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The source load dominates its own scale-`m` term

The source load `L_s` of `e.response.cutoff.estimate` is the sum over generations of the
weighted flat averages of the squared `(b_{s-n,z}, S_{*,s-n,z})`-norms of the annealed mean.
Every one of its summands is nonnegative, so whenever the series converges it dominates each of
its terms -- in particular the terminal term `m = 0`, which is the flat average over the
terminal partition that the cutoff-mean rows pair against.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Every summand of the source load `L_s` of `e.response.cutoff.estimate` is nonnegative: the
geometric weight `3^{-3n/2}` is positive, the reciprocal cell count is nonnegative, and the
inner average is a sum of squares. -/
theorem respSourceLoad_summand_nonneg {d : ℕ} (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (s : ℤ) (b : CoeffSpace d → CoeffField d) (Y : BlockVec d) (n : ℕ) :
    0 ≤ (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
      ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).upperLeft
                Y.1)) +
            Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).lowerRight
                Y.2))) ^ 2) := by
  refine mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)) ?_
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun z _ => sq_nonneg _)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The head term of the source load

The source load `L_s` of `e.response.cutoff.estimate` is the weighted sum over the triadic
generations of the squared `(b^{1/2}, S_*^{-1/2})`-norm of the annealed mean.  At generation
`n = 0` the weight is `1`, the index box is the single scale-`s` cell itself, and the printed
summand `(|b^{1/2} P| + |S_*^{-1/2} Q|)^2` dominates the flat head energy
`|b^{1/2} P|^2 + |S_*^{-1/2} Q|^2`.  This module identifies that head term and bounds the flat
head energy by the source load whenever the defining series converges.  It is the only term of
`L_s` that the cutoff-mean row of the estimate consumes.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- At generation `n = 0` the triadic index box is the singleton box `{0}`: the only cell of the
partition at the terminal scale is the scale-`s` cell itself. -/
theorem triadicIndexBox_zero (d : ℕ) : triadicIndexBox d 0 = {0} := by
  rw [triadicIndexBox]
  have h : (((3 ^ 0 - 1) / 2 : ℕ) : ℤ) = 0 := by norm_num
  rw [h, neg_zero, Finset.Icc_self]
  exact Fintype.piFinset_singleton (0 : Fin d → ℤ)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The depth-zero head of the source load

The cell half of the cutoff-mean row of `p.response.transfer` pairs the mean defect against the
dual variable `Y` and produces the square of the two-term head
`(|b_s^{1/2}P| + |(S_{*,s})^{-1/2}Q|)` of the source load at the terminal generation's own
scale.  The source load `L_s` is the sum over the descendant generations of `3^{-3n/2}` times the
flat average of the same expression, so the head is the `n = 0` summand of that sum and is
therefore at most `L_s` as soon as the family is summable.  This module exposes that terminal
summand and bounds the head by the load.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The terminal (`n = 0`) summand of the source load `L_s` of `p.response.transfer`: at
generation `0` the weight `3^{-3n/2}` is `1`, the triadic index box is the singleton box `{0}`,
and the flat average collapses to the value at the scale-`s` cell itself, so the summand is
exactly the squared two-term head `(|b_s^{1/2}P| + |(S_{*,s})^{-1/2}Q|)²`. -/
theorem respSourceLoadSummand_zero {d : ℕ} [NeZero d] (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (s : ℤ) (b : CoeffSpace d → CoeffField d) (Y : BlockVec d) :
    respSourceLoadSummand P jStar F s b Y 0
      = (Real.sqrt (vecDot Y.1 (matVecMul
            (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) s 0) b).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
            (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) s 0) b).lowerRight Y.2))) ^ 2 := by
  unfold respSourceLoadSummand
  rw [triadicIndexBox_zero d]
  simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, one_mul, Finset.card_singleton,
    Nat.cast_one, inv_one, Finset.sum_singleton, sub_zero]

/-- The squared two-term head `(|b_s^{1/2}P| + |(S_{*,s})^{-1/2}Q|)²` at the terminal scale is
the `n = 0` summand of the source load `L_s` of `p.response.transfer`, so whenever the defining
series converges the head is at most the load itself. -/
theorem sq_head_le_respSourceLoad {d : ℕ} [NeZero d] (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (s : ℤ) (b : CoeffSpace d → CoeffField d) (Y : BlockVec d)
    (hsum : Summable (respSourceLoadSummand P jStar F s b Y)) :
    (Real.sqrt (vecDot Y.1 (matVecMul
          (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) s 0) b).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul
          (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) s 0) b).lowerRight Y.2))) ^ 2
      ≤ respSourceLoad P jStar F s b Y := by
  rw [respSourceLoad_eq_tsum_summand]
  rw [← respSourceLoadSummand_zero P jStar F s b Y]
  exact hsum.le_tsum 0 (fun n _ => respSourceLoad_summand_nonneg P jStar F s b Y n)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Expectation of a pathwise coarse-block quadratic form

The quadratic form of a coarse block `𝐀(V; b a)` in a fixed vector is a finite linear combination
of the entries of the block.  The Bochner integral therefore commutes with the quadratic form, and
the expectation of the pathwise form is the form of the annealed block `E[𝐀(V; b)]`.  These are the
identities at which the expectation lands on the diagonal blocks used by the source load of
`p.response.transfer`, so that the load is read from `E[𝐀(V; b)]` rather than from a pointwise
Cauchy--Schwarz bound.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The expectation of the upper-left pathwise quadratic form is the annealed quadratic form.**
For an integrable family of coarse blocks, the expectation of `Y · (𝐀(V; b a).upperLeft) Y` equals
`Y · (E[𝐀(V; b)].upperLeft) Y`, the quadratic form of the upper-left diagonal block of the
annealed block that defines the source load of `p.response.transfer`. -/
theorem integral_vecDot_coarseBlock_upperLeft {d : ℕ} (P : Measure (CoeffSpace d))
    (V : Set (Vec d)) (b : CoeffSpace d → CoeffField d) (Y : Vec d)
    (hint : ∀ i j, Integrable (fun a => (coarseBlockMatrix V (b a)).upperLeft i j) P) :
    (∫ a, vecDot Y (matVecMul (coarseBlockMatrix V (b a)).upperLeft Y) ∂P)
      = vecDot Y (matVecMul (annealedBlockOf P V b).upperLeft Y) := by
  have hrow : ∀ i : Fin d, Integrable (fun a => ∑ j : Fin d,
      Y i * ((coarseBlockMatrix V (b a)).upperLeft i j * Y j)) P :=
    fun i => integrable_finsetSum _ fun j _ =>
      ((hint i j).mul_const (Y j)).const_mul (Y i)
  unfold vecDot matVecMul annealedBlockOf
  simp only [Matrix.of_apply, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => hrow i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => ((hint i j).mul_const (Y j)).const_mul (Y i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_mul_const]

/-- **The expectation of the lower-right pathwise quadratic form is the annealed quadratic form.**
For an integrable family of coarse blocks, the expectation of `Y · (𝐀(V; b a).lowerRight) Y` equals
`Y · (E[𝐀(V; b)].lowerRight) Y`, the quadratic form of the lower-right diagonal block of the
annealed block that defines the source load of `p.response.transfer`. -/
theorem integral_vecDot_coarseBlock_lowerRight {d : ℕ} (P : Measure (CoeffSpace d))
    (V : Set (Vec d)) (b : CoeffSpace d → CoeffField d) (Y : Vec d)
    (hint : ∀ i j, Integrable (fun a => (coarseBlockMatrix V (b a)).lowerRight i j) P) :
    (∫ a, vecDot Y (matVecMul (coarseBlockMatrix V (b a)).lowerRight Y) ∂P)
      = vecDot Y (matVecMul (annealedBlockOf P V b).lowerRight Y) := by
  have hrow : ∀ i : Fin d, Integrable (fun a => ∑ j : Fin d,
      Y i * ((coarseBlockMatrix V (b a)).lowerRight i j * Y j)) P :=
    fun i => integrable_finsetSum _ fun j _ =>
      ((hint i j).mul_const (Y j)).const_mul (Y i)
  unfold vecDot matVecMul annealedBlockOf
  simp only [Matrix.of_apply, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => hrow i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => ((hint i j).mul_const (Y j)).const_mul (Y i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_mul_const]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The expectation of the squared two-term head

For a measure `P` and integrable nonnegative functions `f` and `g`, the expectation of the square
of the sum of the two square roots is bounded by the square of the sum of the square roots of the
expectations:

`∫ (√f + √g)^2 ≤ (√(∫ f) + √(∫ g))^2`.

Expanding the square, the two pure terms integrate to the annealed quantities `∫ f` and `∫ g`,
while the cross term is controlled in the sample by the annealed Cauchy--Schwarz inequality
`integral_sqrt_mul_sqrt_le_sqrt_mul_sqrt`; the pieces reassemble into the square of the sum of the
square roots of the annealed quantities.  This is how the pathwise head of the direct full-dual
pairing is dominated by the head of `respSourceLoad`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The expectation of the squared two-term head: if `f` and `g` are integrable and nonnegative
and the square `(√f + √g)^2` is integrable, then
`∫ (√f + √g)^2 ≤ (√(∫ f) + √(∫ g))^2`.  The square is expanded pointwise into
`f + g + 2 √f √g`, the two pure terms integrate to `∫ f` and `∫ g`, and the cross term is bounded
by the annealed Cauchy--Schwarz inequality `integral_sqrt_mul_sqrt_le_sqrt_mul_sqrt`; the result
recombines into the square of the sum of the square roots of the annealed quantities.  This is the
estimate behind the head of `respSourceLoad` in the first error row of `e.response.cutoff.estimate`.
-/
theorem integral_sq_sqrt_add_sqrt_le {alpha : Type*} [MeasurableSpace alpha]
    (P : Measure alpha) {f g : alpha → ℝ}
    (hf : Integrable f P) (hg : Integrable g P)
    (hf0 : ∀ a, 0 ≤ f a) (hg0 : ∀ a, 0 ≤ g a)
    (hfg : Integrable (fun a => Real.sqrt (f a) * Real.sqrt (g a)) P)
    (hsq : Integrable (fun a => (Real.sqrt (f a) + Real.sqrt (g a)) ^ 2) P) :
    (∫ a, (Real.sqrt (f a) + Real.sqrt (g a)) ^ 2 ∂P)
      ≤ (Real.sqrt (∫ a, f a ∂P) + Real.sqrt (∫ a, g a ∂P)) ^ 2 := by
  have hpt : ∀ a, (Real.sqrt (f a) + Real.sqrt (g a)) ^ 2
      = f a + g a + 2 * (Real.sqrt (f a) * Real.sqrt (g a)) := by
    intro a
    rw [add_sq, Real.sq_sqrt (hf0 a), Real.sq_sqrt (hg0 a)]
    ring
  have hsum : Integrable (fun a => f a + g a + 2 * (Real.sqrt (f a) * Real.sqrt (g a))) P :=
    hsq.congr (Filter.Eventually.of_forall fun a => hpt a)
  have hcross : Integrable (fun a => 2 * (Real.sqrt (f a) * Real.sqrt (g a))) P :=
    (hsum.sub (hf.add hg)).congr (Filter.Eventually.of_forall fun a => by
      show (f a + g a + 2 * (Real.sqrt (f a) * Real.sqrt (g a))) - (f a + g a)
        = 2 * (Real.sqrt (f a) * Real.sqrt (g a))
      ring)
  have hA0 : 0 ≤ ∫ a, f a ∂P := integral_nonneg fun a => hf0 a
  have hB0 : 0 ≤ ∫ a, g a ∂P := integral_nonneg fun a => hg0 a
  have hLHS : (∫ a, (Real.sqrt (f a) + Real.sqrt (g a)) ^ 2 ∂P)
      = (∫ a, f a ∂P) + (∫ a, g a ∂P)
        + 2 * (∫ a, Real.sqrt (f a) * Real.sqrt (g a) ∂P) := by
    calc (∫ a, (Real.sqrt (f a) + Real.sqrt (g a)) ^ 2 ∂P)
        = ∫ a, f a + g a + 2 * (Real.sqrt (f a) * Real.sqrt (g a)) ∂P :=
          integral_congr_ae (Filter.Eventually.of_forall fun a => hpt a)
      _ = (∫ a, f a + g a ∂P)
          + ∫ a, 2 * (Real.sqrt (f a) * Real.sqrt (g a)) ∂P :=
          integral_add (hf.add hg) hcross
      _ = (∫ a, f a ∂P) + (∫ a, g a ∂P)
          + 2 * (∫ a, Real.sqrt (f a) * Real.sqrt (g a) ∂P) := by
          rw [integral_add hf hg, integral_const_mul]
  have hCS : (∫ a, Real.sqrt (f a) * Real.sqrt (g a) ∂P)
      ≤ Real.sqrt (∫ a, f a ∂P) * Real.sqrt (∫ a, g a ∂P) :=
    integral_sqrt_mul_sqrt_le_sqrt_mul_sqrt P hf hg hf0 hg0 hfg
  have hRHS : (Real.sqrt (∫ a, f a ∂P) + Real.sqrt (∫ a, g a ∂P)) ^ 2
      = (∫ a, f a ∂P) + (∫ a, g a ∂P)
        + 2 * (Real.sqrt (∫ a, f a ∂P) * Real.sqrt (∫ a, g a ∂P)) := by
    rw [add_sq, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
    ring
  calc (∫ a, (Real.sqrt (f a) + Real.sqrt (g a)) ^ 2 ∂P)
      = (∫ a, f a ∂P) + (∫ a, g a ∂P)
        + 2 * (∫ a, Real.sqrt (f a) * Real.sqrt (g a) ∂P) := hLHS
    _ ≤ (∫ a, f a ∂P) + (∫ a, g a ∂P)
        + 2 * (Real.sqrt (∫ a, f a ∂P) * Real.sqrt (∫ a, g a ∂P)) := by linarith only [hCS]
    _ = (Real.sqrt (∫ a, f a ∂P) + Real.sqrt (∫ a, g a ∂P)) ^ 2 := hRHS.symm

end

end HCPolySupport.HighContrast.Multiscale
end
