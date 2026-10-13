/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffHomogenizationError
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.TwoTermOrlicz
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Tail.TailSqrt
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Disorder.CstarUpperBound

/-!
# AmplitudeBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The amplitude bridge: the diagonal fourth moment and the amplitude range

The printed sentence reads

`E[mathcal E_{1/4, infinity, 2}(cu_L, a_L; shom_L)^4]^{1/2} <=^2 gamma` for
every `L in (-infinity, m-1] cap Z`,

and the next sentence instantiates the preceding proposition at `delta_1 :=^2
gamma`.  Item `A.3` fixes the two constants of that instantiation: it sets `s =
1/4` and `delta_1 = 10^9 E^2 gamma`, and it needs `delta_1 <= 1/2` before the
proposition may be applied.

This module supplies both halves at the genuine cutoff sample law and in the
byte shape the proved Step-1 consumer takes them:

1. *The diagonal fourth moment.*  For every cutoff scale `L <= m - 1`,
   `lintegral (ofReal (E_{1/4}(cu_L; a_L, shom_L)^4)) <= ofReal (delta_1^2)`
   with `delta_1 = 10^9 E^2 gamma`.
2. *The amplitude range.*  `delta_1 in Ioc 0 (1/2)`.

## Where the numerals come from

* The `A.3` discounts `t = 1/8` and `u = 1/16` belong to its
  *observation-scale* transport, which enlarges the cube from `cu_L` to
  `cu_M`; the diagonal display proved here is at the cutoff cube itself,
  so no discount change occurs and the printed `1/4` is kept.
* The `10^9` is not consumed as a sharp constant below: the two-term amplitudes
  of the preceding-error clause produce `8 ((12 A)^4 + (208 B)^4)` with `A = 4
  E sqrt gamma` and `B = 16 exp(-E^{-3} gamma^{-1})`, which the regime fact
  `gamma <= E^{-10}` collapses to at most `1.6 * 10^16 * E^4 gamma^2`, against
  the target `10^18 E^4 gamma^2`; the slack factor is about `64` (the honest
  budget `1.5702e16` against `1e18`), and `10^9` is the first power of ten that
  closes (`10^8` fails).  Every intermediate numeral is displayed in the
  private lemmas below.
* `12 = 6 * 2` and `208 = 13 * 16` are the two Chapter 4 moment constants
  `gammaMomentConst sigma * 4^{1/sigma}` at `sigma = 2` and `sigma = 1/2`,
  bounded above by `6` and `13` respectively from the explicit value
  `gammaMomentConst sigma = 2 e max{1, (2 / (sigma e))^{1/sigma}}`.
* `8` is the elementary `(a + b)^4 <= 8 (a^4 + b^4)` used to split the two-term
  witness pair.

## References

* ABK26.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open Filter MeasureTheory Set
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.IndependentSums
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## Elementary real arithmetic -/

/-- `exp (-x) <= 2 / x ^ 2` for positive `x`.  Re-derivation of the private
`CombineBadEvent.exp_neg_le_two_div_sq`, which cannot be consumed. -/
private theorem exp_neg_le_two_div_sq {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ 2 / x ^ 2 := by
  have hquad : 1 + x + x ^ 2 / 2 ≤ Real.exp x := Real.quadratic_le_exp_of_nonneg hx.le
  have hsq : 0 < x ^ 2 := by positivity
  have hexp : 0 < Real.exp x := Real.exp_pos x
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ hexp, div_mul_eq_mul_div, le_div_iff₀ hsq]
  nlinarith

/-- The fourth-power form of the two-term rare amplitude under the
induction regime `gamma <= E^{-10}`.  This is the fourth-power analogue of the
private `CombineBadEvent.exp_neg_sq_le_of_regime`. -/
private theorem exp_neg_pow_four_le_of_regime {E gamma : ℝ} (hE : 1 ≤ E)
    (hgamma : 0 < gamma) (hregime : gamma ≤ (E⁻¹) ^ 10) :
    Real.exp (-(E⁻¹ ^ 3 * gamma⁻¹)) ^ 4 ≤ 16 * (E ^ 4 * gamma ^ 2) := by
  have hEpos : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have hx : 0 < E⁻¹ ^ 3 * gamma⁻¹ := by positivity
  have htail : Real.exp (-(E⁻¹ ^ 3 * gamma⁻¹)) ≤ 2 * (E ^ 6 * gamma ^ 2) := by
    refine (exp_neg_le_two_div_sq hx).trans_eq ?_
    field_simp
  have hpow : Real.exp (-(E⁻¹ ^ 3 * gamma⁻¹)) ^ 4 ≤ (2 * (E ^ 6 * gamma ^ 2)) ^ 4 :=
    pow_le_pow_left₀ (Real.exp_pos _).le htail 4
  have hE10 : (0 : ℝ) < E ^ 10 := by positivity
  have hgE : gamma * E ^ 10 ≤ 1 := by
    have hinv : gamma ≤ (E ^ 10)⁻¹ := by rwa [← inv_pow]
    calc gamma * E ^ 10 ≤ (E ^ 10)⁻¹ * E ^ 10 :=
          mul_le_mul_of_nonneg_right hinv hE10.le
      _ = 1 := inv_mul_cancel₀ hE10.ne'
  have hsix : (gamma * E ^ 10) ^ 6 ≤ 1 := pow_le_one₀ (by positivity) hgE
  have hnn : (0 : ℝ) ≤ E ^ 20 * gamma ^ 6 := by positivity
  have hE40 : (1 : ℝ) ≤ E ^ 40 := one_le_pow₀ hE
  have h20 : E ^ 20 * gamma ^ 6 ≤ 1 := by
    have hstep : E ^ 20 * gamma ^ 6 * 1 ≤ E ^ 20 * gamma ^ 6 * E ^ 40 :=
      mul_le_mul_of_nonneg_left hE40 hnn
    rw [mul_one, show E ^ 20 * gamma ^ 6 * E ^ 40 = (gamma * E ^ 10) ^ 6 by ring] at hstep
    exact hstep.trans hsix
  have hP : (0 : ℝ) ≤ E ^ 4 * gamma ^ 2 := by positivity
  refine hpow.trans ?_
  calc (2 * (E ^ 6 * gamma ^ 2)) ^ 4
      = 16 * ((E ^ 4 * gamma ^ 2) * (E ^ 20 * gamma ^ 6)) := by ring
    _ ≤ 16 * ((E ^ 4 * gamma ^ 2) * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h20 hP) (by norm_num)
    _ = 16 * (E ^ 4 * gamma ^ 2) := by rw [mul_one]

/-- The two-term split at the fourth power. -/
private theorem add_pow_four_le_eight_mul (a b : ℝ) :
    (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  have h1 : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
  have h2 : (0 : ℝ) ≤ (a + b) ^ 2 := sq_nonneg _
  calc (a + b) ^ 4 = ((a + b) ^ 2) ^ 2 := by ring
    _ ≤ (2 * (a ^ 2 + b ^ 2)) ^ 2 := by nlinarith [h1, h2]
    _ ≤ 8 * (a ^ 4 + b ^ 4) := by nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]

/-! ## The two Chapter 4 moment constants at `p = 4` -/

/-- `4 ^ (1/2) = 2`, the `sigma = 2` moment factor `p ^ sigma⁻¹` at `p = 4`. -/
private theorem rpow_four_inv_two : (4 : ℝ) ^ (2 : ℝ)⁻¹ = 2 := by
  rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 2,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    show ((2 : ℕ) : ℝ) * (2 : ℝ)⁻¹ = 1 by norm_num, Real.rpow_one]

/-- `4 ^ 2 = 16`, the `sigma = 1/2` moment factor `p ^ sigma⁻¹` at `p = 4`. -/
private theorem rpow_four_two : (4 : ℝ) ^ ((1 : ℝ) / 2)⁻¹ = 16 := by
  rw [show ((1 : ℝ) / 2)⁻¹ = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- `gammaMomentConst 2 = 2 e <= 6`: the `max` is attained at `1`, since
`2 / (2 e) = e^{-1} <= 1`. -/
private theorem gammaMomentConst_two_le : gammaMomentConst 2 ≤ 6 := by
  have hlt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hgt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hmax : max 1 ((2 / (2 * Real.exp 1)) ^ (2 : ℝ)⁻¹) = 1 := by
    refine max_eq_left (Real.rpow_le_one (by positivity) ?_ (by norm_num))
    rw [div_le_one (by positivity)]
    linarith
  unfold gammaMomentConst
  rw [hmax, mul_one]
  linarith

/-- `gammaMomentConst (1/2) = 32 / e <= 13`: here the `max` is attained at
`(4 / e) ^ 2`. -/
private theorem gammaMomentConst_half_le : gammaMomentConst (1 / 2) ≤ 13 := by
  have hlt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hgt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hval : (2 / ((1 : ℝ) / 2 * Real.exp 1)) ^ ((1 : ℝ) / 2)⁻¹ =
      (4 / Real.exp 1) ^ (2 : ℕ) := by
    rw [show (2 : ℝ) / ((1 : ℝ) / 2 * Real.exp 1) = 4 / Real.exp 1 by
        field_simp
        norm_num,
      show ((1 : ℝ) / 2)⁻¹ = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hsq : (4 / Real.exp 1) ^ (2 : ℕ) ≤ 2.3 := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    nlinarith
  have hmax : max 1 ((2 / ((1 : ℝ) / 2 * Real.exp 1)) ^ ((1 : ℝ) / 2)⁻¹) ≤ 2.3 := by
    rw [hval]
    exact max_le (by norm_num) hsq
  have hnn : (0 : ℝ) ≤ max 1 ((2 / ((1 : ℝ) / 2 * Real.exp 1)) ^ ((1 : ℝ) / 2)⁻¹) :=
    le_trans zero_le_one (le_max_left _ _)
  unfold gammaMomentConst
  nlinarith

/-! ## The two-term fourth moment -/

/-- **The fourth `lintegral` moment of a two-term weak-Orlicz bound.**  If a
nonnegative `X` satisfies `X <= O_{Gamma_2}(A) + O_{Gamma_{1/2}}(B)`, then

`lintegral (ofReal (X ^ 4)) <= ofReal (8 ((12 A) ^ 4 + (208 B) ^ 4))`.

The numerals are `12 = gammaMomentConst 2 * 4 ^ (1/2)` and
`208 = gammaMomentConst (1/2) * 4 ^ 2`, bounded above, together with the
elementary split constant `8`. -/
private theorem lintegral_ofReal_pow_four_le_of_twoTerm
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {X : Omega → ℝ} {A B : ℝ}
    (hXnonneg : ∀ omega, 0 ≤ X omega)
    (h : Probability.IsTwoTermBigOWith mu (gammaSigma 2) (gammaSigma (1 / 2)) X A B) :
    ∫⁻ omega, ENNReal.ofReal (X omega ^ 4) ∂mu ≤
      ENNReal.ofReal (8 * ((12 * A) ^ 4 + (208 * B) ^ 4)) := by
  obtain ⟨Y, Z, -, -, hA, hB, -, hYmeas, hZmeas, hdom, hYtail, hZtail⟩ := h
  set Y0 : Omega → ℝ := fun omega => max 0 (Y omega) with hY0def
  set Z0 : Omega → ℝ := fun omega => max 0 (Z omega) with hZ0def
  have hY0nonneg : ∀ omega, 0 ≤ Y0 omega := fun _ => le_max_left _ _
  have hZ0nonneg : ∀ omega, 0 ≤ Z0 omega := fun _ => le_max_left _ _
  have hY0meas : Measurable Y0 := measurable_const.max hYmeas
  have hZ0meas : Measurable Z0 := measurable_const.max hZmeas
  have hY0tail : IsBigOWith mu (gammaSigma 2) Y0 A := by
    simpa only [hY0def] using Tail.isBigOWith_max_zero hA hYtail
  have hZ0tail : IsBigOWith mu (gammaSigma (1 / 2)) Z0 B := by
    simpa only [hZ0def] using Tail.isBigOWith_max_zero hB hZtail
  -- the two Chapter 4 fourth moments, converted from `rpow` to a natural power
  have hY4 : ∫⁻ omega, ENNReal.ofReal (Y0 omega ^ (4 : ℕ)) ∂mu ≤
      ENNReal.ofReal ((gammaMomentConst 2 * (4 : ℝ) ^ (2 : ℝ)⁻¹ * A) ^ (4 : ℕ)) := by
    have hraw := lintegral_rpow_le_of_isBigOWith_gammaSigma (μ := mu) (Y := Y0)
      (K := A) (σ := 2) (p := 4) (by norm_num) hA (by norm_num) hY0nonneg
      hY0meas.aemeasurable hY0tail
    simpa only [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] using hraw
  have hZ4 : ∫⁻ omega, ENNReal.ofReal (Z0 omega ^ (4 : ℕ)) ∂mu ≤
      ENNReal.ofReal ((gammaMomentConst (1 / 2) * (4 : ℝ) ^ ((1 : ℝ) / 2)⁻¹ * B) ^ (4 : ℕ)) := by
    have hraw := lintegral_rpow_le_of_isBigOWith_gammaSigma (μ := mu) (Y := Z0)
      (K := B) (σ := (1 / 2 : ℝ)) (p := 4) (by norm_num) hB (by norm_num) hZ0nonneg
      hZ0meas.aemeasurable hZ0tail
    simpa only [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] using hraw
  -- the constants
  have hc1 : gammaMomentConst 2 * (4 : ℝ) ^ (2 : ℝ)⁻¹ ≤ 12 := by
    rw [rpow_four_inv_two]
    linarith [gammaMomentConst_two_le]
  have hc2 : gammaMomentConst (1 / 2) * (4 : ℝ) ^ ((1 : ℝ) / 2)⁻¹ ≤ 208 := by
    rw [rpow_four_two]
    linarith [gammaMomentConst_half_le]
  have hc1nn : (0 : ℝ) ≤ gammaMomentConst 2 * (4 : ℝ) ^ (2 : ℝ)⁻¹ :=
    mul_nonneg (gammaMomentConst_pos (by norm_num)).le (Real.rpow_nonneg (by norm_num) _)
  have hc2nn : (0 : ℝ) ≤ gammaMomentConst (1 / 2) * (4 : ℝ) ^ ((1 : ℝ) / 2)⁻¹ :=
    mul_nonneg (gammaMomentConst_pos (by norm_num)).le (Real.rpow_nonneg (by norm_num) _)
  have hY4' : ∫⁻ omega, ENNReal.ofReal (Y0 omega ^ (4 : ℕ)) ∂mu ≤
      ENNReal.ofReal ((12 * A) ^ (4 : ℕ)) :=
    hY4.trans (ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (mul_nonneg hc1nn hA.le)
        (mul_le_mul_of_nonneg_right hc1 hA.le) 4))
  have hZ4' : ∫⁻ omega, ENNReal.ofReal (Z0 omega ^ (4 : ℕ)) ∂mu ≤
      ENNReal.ofReal ((208 * B) ^ (4 : ℕ)) :=
    hZ4.trans (ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (mul_nonneg hc2nn hB.le)
        (mul_le_mul_of_nonneg_right hc2 hB.le) 4))
  -- the pointwise two-term split
  have hpt : ∀ omega, ENNReal.ofReal (X omega ^ 4) ≤
      8 * ENNReal.ofReal (Y0 omega ^ 4) + 8 * ENNReal.ofReal (Z0 omega ^ 4) := by
    intro omega
    have hdom0 : X omega ≤ Y0 omega + Z0 omega :=
      (hdom omega).trans (add_le_add (le_max_right _ _) (le_max_right _ _))
    have hreal : X omega ^ 4 ≤ 8 * Y0 omega ^ 4 + 8 * Z0 omega ^ 4 := by
      have hstep := pow_le_pow_left₀ (hXnonneg omega) hdom0 4
      have hsplit := add_pow_four_le_eight_mul (Y0 omega) (Z0 omega)
      linarith
    calc ENNReal.ofReal (X omega ^ 4)
        ≤ ENNReal.ofReal (8 * Y0 omega ^ 4 + 8 * Z0 omega ^ 4) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = 8 * ENNReal.ofReal (Y0 omega ^ 4) + 8 * ENNReal.ofReal (Z0 omega ^ 4) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
          norm_num
  have hYm4 : Measurable fun omega => ENNReal.ofReal (Y0 omega ^ 4) :=
    (hY0meas.pow_const 4).ennreal_ofReal
  have hZm4 : Measurable fun omega => ENNReal.ofReal (Z0 omega ^ 4) :=
    (hZ0meas.pow_const 4).ennreal_ofReal
  calc ∫⁻ omega, ENNReal.ofReal (X omega ^ 4) ∂mu
      ≤ ∫⁻ omega,
          (8 * ENNReal.ofReal (Y0 omega ^ 4) + 8 * ENNReal.ofReal (Z0 omega ^ 4)) ∂mu :=
        lintegral_mono hpt
    _ = 8 * (∫⁻ omega, ENNReal.ofReal (Y0 omega ^ 4) ∂mu) +
          8 * ∫⁻ omega, ENNReal.ofReal (Z0 omega ^ 4) ∂mu := by
        rw [lintegral_add_left (hYm4.const_mul 8), lintegral_const_mul 8 hYm4,
          lintegral_const_mul 8 hZm4]
    _ ≤ 8 * ENNReal.ofReal ((12 * A) ^ (4 : ℕ)) +
          8 * ENNReal.ofReal ((208 * B) ^ (4 : ℕ)) := by
        gcongr
    _ = ENNReal.ofReal (8 * ((12 * A) ^ 4 + (208 * B) ^ 4)) := by
        rw [show ((8 : ENNReal)) = ENNReal.ofReal 8 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-! ## The `E` floor available from the `c_star` upper bound -/

theorem ten_le_of_fifteen_mul_inv_cstar_le (M : ABKModel d) {E : ℝ}
    (hEfloor : 15 * (Disorder.cstar M)⁻¹ ≤ E) : (10 : ℝ) ≤ E := by
  have hc : 0 < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hle : Disorder.cstar M ≤ 3 / 2 := Provider.Disorder.cstar_le_three_halves M
  have h : (10 : ℝ) ≤ 15 * (Disorder.cstar M)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hc]
    linarith
  linarith

/-! ## The amplitude range -/

/-- **The amplitude range**, `A.3`'s `0 < delta_1 <= 1/2` for
`delta_1 = 10^9 E^2 gamma`.

The arithmetic is `10^9 E^2 gamma <= 10^9 Chom^{-1} epsilon <= epsilon <= 1/2`. -/
theorem amplitude_mem_Ioc_of_gate (M : ABKModel d) {E Chom epsilon : ℝ}
    (hE : 1 ≤ E) (hChom : (10 : ℝ) ^ 9 ≤ Chom)
    (hepsilon : epsilon ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hgate : M.gamma ≤ Chom⁻¹ * (E⁻¹) ^ 2 * epsilon) :
    10 ^ 9 * E ^ 2 * M.gamma ∈ Set.Ioc (0 : ℝ) (1 / 2) := by
  have hEpos : (0 : ℝ) < E := lt_of_lt_of_le zero_lt_one hE
  have hgammaPos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hChomPos : (0 : ℝ) < Chom := lt_of_lt_of_le (by norm_num) hChom
  refine ⟨by positivity, ?_⟩
  have hstep : 10 ^ 9 * E ^ 2 * M.gamma ≤
      10 ^ 9 * E ^ 2 * (Chom⁻¹ * (E⁻¹) ^ 2 * epsilon) :=
    mul_le_mul_of_nonneg_left hgate (by positivity)
  have hcollapse : 10 ^ 9 * E ^ 2 * (Chom⁻¹ * (E⁻¹) ^ 2 * epsilon) =
      10 ^ 9 * Chom⁻¹ * epsilon := by
    field_simp
  have hchominv : (10 : ℝ) ^ 9 * Chom⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hChomPos]
    exact hChom
  have hfinal : (10 : ℝ) ^ 9 * Chom⁻¹ * epsilon ≤ epsilon := by
    have := mul_le_mul_of_nonneg_right hchominv hepsilon.1.le
    linarith
  calc 10 ^ 9 * E ^ 2 * M.gamma
      ≤ 10 ^ 9 * E ^ 2 * (Chom⁻¹ * (E⁻¹) ^ 2 * epsilon) := hstep
    _ = 10 ^ 9 * Chom⁻¹ * epsilon := hcollapse
    _ ≤ epsilon := hfinal
    _ ≤ 1 / 2 := hepsilon.2

/-! ## The diagonal fourth moment -/

variable [NeZero d]

/-- **The diagonal fourth moment at `s = 1/4`.**  Under the preceding-error clause
of the frozen statement and its two regime facts, for every cutoff scale
`L <= m - 1`,

`E[mathcal E_{1/4, infinity, 2}(cu_L; a_L, shom_L)^4] <= (10^9 E^2 gamma)^2`,

in the `lintegral` shape the proved Step-1 consumers take.

The cube scale, the coefficient-cutoff scale and the comparator scale are all
`L`, so this is the *diagonal* display and the clause is used at its own
observation scale: no finite-cover transport and no discount halving occurs,
and the printed discount `1/4` is kept.  The window `1/4 in Icc (8 gamma) 1`
required by the clause is supplied from `E >= 10` and `gamma <= E^{-10}`. -/
theorem lintegral_cutoffHomogenizationErrorRepresentative_pow_four_le
    (M : ABKModel d) {m : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hEfloor : 15 * (Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hregime : M.gamma ≤ ((E : ℝ)⁻¹) ^ 10)
    (hLower : ∀ k : ℤ, k ≤ m - 1 →
      ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
        Probability.IsTwoTermBigOWith
          (Cutoff.cutoffSampleLaw M).toMeasure
          (gammaSigma 2) (gammaSigma (1 / 2))
          (Observable.cutoffHomogenizationError M k
            ⟨s,
              (mul_pos (by norm_num : (0 : ℝ) < 8)
                M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
          ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
          ((s⁻¹) ^ 2 *
            Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))))
    {L : ℤ} (hL : L ≤ m - 1) (hs : (0 : ℝ) < 1 / 4) :
    ∫⁻ omega, ENNReal.ofReal
        (Observable.cutoffHomogenizationErrorRepresentative M L L hs
          (Annealed.sigmaBar M L) omega ^ 4)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((10 ^ 9 * (E : ℝ) ^ 2 * M.gamma) ^ 2) := by
  have hE1 : (1 : ℝ) ≤ (E : ℝ) := E.property
  have hEpos : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le zero_lt_one hE1
  have hgammaPos : 0 < M.gamma := M.shellPrefix.gamma_pos
  -- the legal window of the preceding-error clause at `s = 1/4`
  have hEten : (10 : ℝ) ≤ (E : ℝ) := ten_le_of_fifteen_mul_inv_cstar_le M hEfloor
  have hgammaSmall : M.gamma ≤ 1 / 32 := by
    have hinv : ((E : ℝ)⁻¹) ^ 10 ≤ ((1 : ℝ) / 10) ^ 10 := by
      refine pow_le_pow_left₀ (inv_nonneg.mpr hEpos.le) ?_ 10
      rw [inv_le_comm₀ hEpos (by norm_num)]
      linarith
    have hnum : ((1 : ℝ) / 10) ^ 10 ≤ 1 / 32 := by norm_num
    linarith [hregime.trans (hinv.trans hnum)]
  have hwindow : (1 / 4 : ℝ) ∈ Set.Icc (8 * M.gamma) 1 := ⟨by linarith, by norm_num⟩
  -- the clause at the diagonal `k = L`, whose carrier is the representative
  have hclause := hLower L hL (1 / 4) hwindow
  have hcarrier : Observable.cutoffHomogenizationError M L
      ⟨1 / 4,
        (mul_pos (by norm_num : (0 : ℝ) < 8)
          M.shellPrefix.gamma_pos).trans_le hwindow.1⟩ =
      Observable.cutoffHomogenizationErrorRepresentative M L L hs
        (Annealed.sigmaBar M L) := rfl
  rw [hcarrier] at hclause
  have hXnonneg : ∀ omega,
      0 ≤ Observable.cutoffHomogenizationErrorRepresentative M L L hs
        (Annealed.sigmaBar M L) omega := fun omega =>
    Observable.cutoffHomogenizationErrorRepresentative_nonneg M L L hs
      (Annealed.sigmaBar M L) omega
  refine (lintegral_ofReal_pow_four_le_of_twoTerm hXnonneg hclause).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  -- the amplitude arithmetic
  set A : ℝ := (E : ℝ) * ((1 : ℝ) / 4)⁻¹ * Real.sqrt M.gamma with hAdef
  set B : ℝ := (((1 : ℝ) / 4)⁻¹) ^ 2 *
    Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) with hBdef
  have hP : (0 : ℝ) ≤ (E : ℝ) ^ 4 * M.gamma ^ 2 := by positivity
  have hA4 : A ^ 4 = 256 * ((E : ℝ) ^ 4 * M.gamma ^ 2) := by
    have hsqrt : Real.sqrt M.gamma ^ 2 = M.gamma := Real.sq_sqrt hgammaPos.le
    rw [hAdef, show ((E : ℝ) * ((1 : ℝ) / 4)⁻¹ * Real.sqrt M.gamma) ^ 4 =
      (E : ℝ) ^ 4 * ((((1 : ℝ) / 4)⁻¹) ^ 4) * (Real.sqrt M.gamma ^ 2) ^ 2 by ring, hsqrt]
    norm_num
    ring
  have hB4 : B ^ 4 ≤ 1048576 * ((E : ℝ) ^ 4 * M.gamma ^ 2) := by
    have hexp := exp_neg_pow_four_le_of_regime hE1 hgammaPos hregime
    have hexpand : B ^ 4 = 65536 * Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) ^ 4 := by
      rw [hBdef]; ring
    rw [hexpand]
    calc 65536 * Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) ^ 4
        ≤ 65536 * (16 * ((E : ℝ) ^ 4 * M.gamma ^ 2)) :=
          mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ = 1048576 * ((E : ℝ) ^ 4 * M.gamma ^ 2) := by ring
  calc 8 * ((12 * A) ^ 4 + (208 * B) ^ 4)
      = 8 * (20736 * A ^ 4 + 1871773696 * B ^ 4) := by ring
    _ ≤ 8 * (20736 * (256 * ((E : ℝ) ^ 4 * M.gamma ^ 2)) +
          1871773696 * (1048576 * ((E : ℝ) ^ 4 * M.gamma ^ 2))) := by
        have h1 : (20736 : ℝ) * A ^ 4 =
            20736 * (256 * ((E : ℝ) ^ 4 * M.gamma ^ 2)) := by rw [hA4]
        have h2 : (1871773696 : ℝ) * B ^ 4 ≤
            1871773696 * (1048576 * ((E : ℝ) ^ 4 * M.gamma ^ 2)) :=
          mul_le_mul_of_nonneg_left hB4 (by norm_num)
        linarith
    _ ≤ (10 ^ 9 * (E : ℝ) ^ 2 * M.gamma) ^ 2 := by nlinarith [hP]

/-- **The amplitude bridge**, item `(I-1)` of the corrected Section 3.5
account: the two data the Step-1 display must be instantiated with at
`delta_1 = 10^9 E^2 gamma`, delivered together and uniformly in the cutoff
scale.

The amplitude does not depend on `L`, so the fourth-moment half is uniform over
the whole admissible corridor `L <= m - 1` and, in particular, over every
corridor scale pair the finite recurrence of `A.4` reindexes. -/
theorem amplitude_mem_Ioc_and_lintegral_pow_four_le
    (M : ABKModel d) {m : ℤ} {E : {E : ℝ // 1 ≤ E}} {Chom epsilon : ℝ}
    (hChom : (10 : ℝ) ^ 9 ≤ Chom)
    (hEfloor : 15 * (Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hregime : M.gamma ≤ ((E : ℝ)⁻¹) ^ 10)
    (hLower : ∀ k : ℤ, k ≤ m - 1 →
      ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
        Probability.IsTwoTermBigOWith
          (Cutoff.cutoffSampleLaw M).toMeasure
          (gammaSigma 2) (gammaSigma (1 / 2))
          (Observable.cutoffHomogenizationError M k
            ⟨s,
              (mul_pos (by norm_num : (0 : ℝ) < 8)
                M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
          ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
          ((s⁻¹) ^ 2 *
            Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))))
    (hepsilon : epsilon ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hgate : M.gamma ≤ Chom⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon)
    (hs : (0 : ℝ) < 1 / 4) :
    10 ^ 9 * (E : ℝ) ^ 2 * M.gamma ∈ Set.Ioc (0 : ℝ) (1 / 2) ∧
      ∀ L : ℤ, L ≤ m - 1 →
        ∫⁻ omega, ENNReal.ofReal
            (Observable.cutoffHomogenizationErrorRepresentative M L L hs
              (Annealed.sigmaBar M L) omega ^ 4)
            ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
          ENNReal.ofReal ((10 ^ 9 * (E : ℝ) ^ 2 * M.gamma) ^ 2) :=
  ⟨amplitude_mem_Ioc_of_gate M E.property hChom hepsilon hgate,
    fun _ hL =>
      lintegral_cutoffHomogenizationErrorRepresentative_pow_four_le M hEfloor hregime
        hLower hL hs⟩

end

end Algsuperdiff.Section3.Provider.Homogenization
