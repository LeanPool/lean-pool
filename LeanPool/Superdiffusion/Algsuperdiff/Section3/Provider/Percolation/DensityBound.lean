/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.ScaleDecomposition
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.TsumTriangle
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# DensityBound

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Conclusion (1) of ABK26's general percolation lemma: the density bound

This module proves the density bound `e.density.bound`, conclusion (1) of
`l.percolation.bound.general` (ABK26), from hypotheses (ii) and (iii) of that
lemma, following Step 1 of its proof.

## The printed statement, and its correction

The printed conclusion reads: there is `c(d) > 0` such that **for every `t > 0`**,
if `a < d`,

`ℙ[ ⨍_{z ∈ □_m ∩ ℤ^d} (1_{B(z)} - ℙ[B(z)]) > t ] ≤ exp(-c t² a² (d-a)² T² 3^{am})`.

The range `∀ t > 0` outruns the proof: Step 1 delivers the weak-Orlicz estimate

`⨍_{z ∈ □_m ∩ ℤ^d} (1_{B(z)} - ℙ[B(z)]) ≤ 𝒪_{Γ₂}(A)`,
`A = C(a^{-1} + (d-a)^{-1}) T^{-1} 3^{-am/2}`,

which yields `ℙ[· > t] ≤ 2 exp(-t²/A²)`; absorbing the factor `2` into a
constant-free `exp(-c t²/A²)` needs `t ≳ A`, and for `t ≪ A` the argument gives
only the trivial bound `≤ 1` while the printed right-hand side is `< 1`. The
corrected statement is the weak-Orlicz estimate itself — equivalently, the
printed tail bound restricted to `t ≥ A`. Both forms are proved below:
`isBigOWith_gammaSigma_densityAverage` and
`measureReal_densityAverage_gt_le_exp`.

## The proof

`ScaleDecomposition.lean` supplies the exact first-occurrence scale
decomposition and the per-scale estimate; `ColoredConcentration.lean` supplies
the colouring corollary of the concentration inequality. What remains here is
arithmetic: the per-scale amplitude

`Ā_L = C (T^{-1}) min(2^{d/2} 3^{-dm/2} 3^{(d-a)L/2}, 3^{-aL/2})`

dominates the per-scale estimate — the first entry of the `min` is the genuine
concentration gain, available while `3^L` is below the diameter of `□_m`, the
second is the trivial triangle-inequality bound — and

`∑_{L ∈ ℕ} Ā_L ≤ C(d) (a^{-1} + (d-a)^{-1}) T^{-1} 3^{-am/2}`,

the two halves of the geometric sum producing the two poles `a^{-1}` (from
`L > m`, where `a > 0` is needed) and `(d-a)^{-1}` (from `L ≤ m`, where `a < d`
is needed). Hypothesis (i) of the source lemma, independence across disjoint
sets of scales, is *not* used by Step 1 and is therefore not assumed.

## Main results

* `Algsuperdiff.Section3.Provider.Percolation.isBigOWith_gammaSigma_densityAverage`
* `Algsuperdiff.Section3.Provider.Percolation.measureReal_densityAverage_gt_le_exp`

## References

* ABK26, `l.percolation.bound.general` (1) `e.density.bound`.
* ABK26, Step 1 of its proof.
-/

namespace Algsuperdiff.Section3.Provider.Percolation

open MeasureTheory ProbabilityTheory
open HCPolySupport.IndependentSums

noncomputable section

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### Elementary `rpow` arithmetic -/

private theorem three_pos_real : (0 : ℝ) < 3 := by norm_num

private theorem three_rpow_pow (x : ℝ) (n : ℕ) : ((3 : ℝ) ^ x) ^ n = (3 : ℝ) ^ (x * n) := by
  rw [← Real.rpow_natCast ((3 : ℝ) ^ x) n, ← Real.rpow_mul three_pos_real.le]

private theorem three_rpow_mul (x y : ℝ) : (3 : ℝ) ^ x * (3 : ℝ) ^ y = (3 : ℝ) ^ (x + y) :=
  (Real.rpow_add three_pos_real x y).symm

private theorem sqrt_pow_eq_rpow {c : ℝ} (hc : 0 ≤ c) (k : ℕ) :
    Real.sqrt (c ^ k) = c ^ ((k : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast c k, ← Real.rpow_mul hc]
  congr 1
  ring

private theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le three_pos_real]
  linarith only [Real.exp_one_lt_d9]

/-- `3 ^ x ≥ 1 + x` for `x ≥ 0`: the elementary bound that converts the two
geometric ratios of Step 1 into the poles `a^{-1}` and `(d-a)^{-1}`. -/
private theorem add_one_le_three_rpow {x : ℝ} (hx : 0 ≤ x) : x + 1 ≤ (3 : ℝ) ^ x := by
  rw [Real.rpow_def_of_pos three_pos_real]
  have h1 : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
  have h2 : Real.exp x ≤ Real.exp (Real.log 3 * x) :=
    Real.exp_le_exp.mpr (le_mul_of_one_le_left hx one_le_log_three)
  linarith only [h1, h2]

private theorem inv_mul_rpow_neg_two {T X : ℝ} (hT : 0 < T) (hX : 0 < X) :
    (T⁻¹ * X) ^ (-(2 : ℝ)) = T ^ 2 * X ^ (-(2 : ℝ)) := by
  rw [Real.mul_rpow (by positivity) hX.le, Real.inv_rpow hT.le, Real.rpow_neg hT.le,
    inv_inv, ← Real.rpow_natCast T 2]
  norm_num

private theorem three_rpow_pow_neg_two (a : ℝ) (L : ℕ) :
    (((3 : ℝ) ^ (-a / 2)) ^ L) ^ (-(2 : ℝ)) = (3 : ℝ) ^ (a * (L : ℝ)) := by
  rw [three_rpow_pow, ← Real.rpow_mul three_pos_real.le]
  congr 1
  ring

/-! ### The per-scale amplitude -/

/-- The per-scale amplitude of ABK26 Step 1. The first entry of the `min` is the
concentration gain from the colouring, the second the trivial triangle-inequality
bound; the `min` is what keeps the scale sum convergent in both regimes. -/
def perScaleAmplitude (d : ℕ) (a T : ℝ) (m L : ℕ) : ℝ :=
  2 * gammaTriangleConst 2 * HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
    (T⁻¹ * min ((2 : ℝ) ^ ((d : ℝ) / 2) * ((3 : ℝ) ^ (-(d : ℝ) / 2)) ^ m *
        ((3 : ℝ) ^ (((d : ℝ) - a) / 2)) ^ L)
      (((3 : ℝ) ^ (-a / 2)) ^ L))

private theorem colorConst_pos :
    0 < 2 * gammaTriangleConst 2 *
      HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 :=
  mul_pos (mul_pos two_pos gammaTriangleConst_pos)
    (gammaSigmaIndependentSumConst_pos (by norm_num))

theorem perScaleAmplitude_pos (d : ℕ) {a T : ℝ} (hT : 0 < T) (m L : ℕ) :
    0 < perScaleAmplitude d a T m L := by
  have hmin : 0 < min ((2 : ℝ) ^ ((d : ℝ) / 2) * ((3 : ℝ) ^ (-(d : ℝ) / 2)) ^ m *
      ((3 : ℝ) ^ (((d : ℝ) - a) / 2)) ^ L) (((3 : ℝ) ^ (-a / 2)) ^ L) := by
    refine lt_min ?_ ?_ <;> positivity
  exact mul_pos colorConst_pos (mul_pos (inv_pos.mpr hT) hmin)

theorem summable_perScaleAmplitude (d : ℕ) {a T : ℝ} (ha : 0 < a) (hT : 0 < T) (m : ℕ) :
    Summable (perScaleAmplitude d a T m) := by
  have hq0 : (0 : ℝ) < (3 : ℝ) ^ (-a / 2) := Real.rpow_pos_of_pos three_pos_real _
  have hq1 : (3 : ℝ) ^ (-a / 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [ha])
  have hmaj : Summable fun L : ℕ =>
      2 * gammaTriangleConst 2 *
        HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
        (T⁻¹ * ((3 : ℝ) ^ (-a / 2)) ^ L) :=
    Summable.mul_left _ (Summable.mul_left _
      (summable_geometric_of_lt_one hq0.le hq1))
  refine Summable.of_nonneg_of_le (fun L => (perScaleAmplitude_pos d hT m L).le)
    (fun L => ?_) hmaj
  rw [perScaleAmplitude]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (min_le_right _ _) (inv_pos.mpr hT).le)
    colorConst_pos.le

/-! ### The per-scale estimate at the amplitude `perScaleAmplitude` -/

private theorem colorScale_mul_le (d m L : ℕ) {a T : ℝ} (hT : 0 < T) :
    colorScale d m L * (2 * (T⁻¹ * ((3 : ℝ) ^ (-a / 2)) ^ L)) ≤
      perScaleAmplitude d a T m L := by
  have hN : ((cubeFinset (d := d) m).card : ℝ) = (3 : ℝ) ^ (d * m) := by
    rw [card_cubeFinset]
    push_cast
    ring
  have hNpos : (0 : ℝ) < ((cubeFinset (d := d) m).card : ℝ) := by
    rw [hN]; positivity
  have hqpos : (0 : ℝ) < ((3 : ℝ) ^ (-a / 2)) ^ L := by positivity
  set F : ℝ := Real.sqrt (min (((3 ^ L + 1) ^ d : ℕ) : ℝ)
    ((cubeFinset (d := d) m).card : ℝ)) *
      (Real.sqrt ((cubeFinset (d := d) m).card : ℝ) /
        ((cubeFinset (d := d) m).card : ℝ)) with hFdef
  have hF0 : 0 ≤ F := by
    rw [hFdef]; positivity
  -- the trivial bound `F ≤ 1`
  have hF1 : F ≤ 1 := by
    rw [hFdef]
    have h1 : Real.sqrt (min (((3 ^ L + 1) ^ d : ℕ) : ℝ)
        ((cubeFinset (d := d) m).card : ℝ)) ≤
        Real.sqrt ((cubeFinset (d := d) m).card : ℝ) :=
      Real.sqrt_le_sqrt (min_le_right _ _)
    have h2 : Real.sqrt ((cubeFinset (d := d) m).card : ℝ) *
        (Real.sqrt ((cubeFinset (d := d) m).card : ℝ) /
          ((cubeFinset (d := d) m).card : ℝ)) = 1 := by
      rw [← mul_div_assoc, Real.mul_self_sqrt hNpos.le, div_self hNpos.ne']
    calc F ≤ Real.sqrt ((cubeFinset (d := d) m).card : ℝ) *
          (Real.sqrt ((cubeFinset (d := d) m).card : ℝ) /
            ((cubeFinset (d := d) m).card : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 1 := h2
  -- the colouring bound
  have hcount : (((3 ^ L + 1) ^ d : ℕ) : ℝ) ≤ (2 : ℝ) ^ d * (3 : ℝ) ^ (d * L) := by
    have hnat : ((3 ^ L + 1) ^ d : ℕ) ≤ 2 ^ d * 3 ^ (d * L) := by
      have h1 : (3 : ℕ) ^ L + 1 ≤ 2 * 3 ^ L := by
        have := Nat.one_le_two_pow (n := 0)
        have h3 : 1 ≤ (3 : ℕ) ^ L := Nat.one_le_pow _ _ (by omega)
        omega
      calc ((3 ^ L + 1) ^ d : ℕ) ≤ (2 * 3 ^ L) ^ d := Nat.pow_le_pow_left h1 d
        _ = 2 ^ d * 3 ^ (d * L) := by rw [Nat.mul_pow, ← pow_mul, Nat.mul_comm L d]
    exact_mod_cast hnat
  have hF2 : F * ((3 : ℝ) ^ (-a / 2)) ^ L ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * ((3 : ℝ) ^ (-(d : ℝ) / 2)) ^ m *
        ((3 : ℝ) ^ (((d : ℝ) - a) / 2)) ^ L := by
    have hsq : Real.sqrt (min (((3 ^ L + 1) ^ d : ℕ) : ℝ)
        ((cubeFinset (d := d) m).card : ℝ)) ≤
        (2 : ℝ) ^ ((d : ℝ) / 2) * (3 : ℝ) ^ (((d * L : ℕ) : ℝ) / 2) := by
      calc Real.sqrt (min (((3 ^ L + 1) ^ d : ℕ) : ℝ)
            ((cubeFinset (d := d) m).card : ℝ))
          ≤ Real.sqrt ((2 : ℝ) ^ d * (3 : ℝ) ^ (d * L)) :=
            Real.sqrt_le_sqrt (le_trans (min_le_left _ _) hcount)
        _ = Real.sqrt ((2 : ℝ) ^ d) * Real.sqrt ((3 : ℝ) ^ (d * L)) :=
            Real.sqrt_mul (by positivity) _
        _ = (2 : ℝ) ^ ((d : ℝ) / 2) * (3 : ℝ) ^ (((d * L : ℕ) : ℝ) / 2) := by
            rw [sqrt_pow_eq_rpow (by norm_num : (0 : ℝ) ≤ 2) d,
              sqrt_pow_eq_rpow three_pos_real.le (d * L)]
    have hdiv : Real.sqrt ((cubeFinset (d := d) m).card : ℝ) /
        ((cubeFinset (d := d) m).card : ℝ) = (3 : ℝ) ^ (-(((d * m : ℕ)) : ℝ) / 2) := by
      rw [hN, sqrt_pow_eq_rpow three_pos_real.le (d * m),
        ← Real.rpow_natCast (3 : ℝ) (d * m), ← Real.rpow_sub three_pos_real]
      congr 1
      ring
    have hstep : F ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * (3 : ℝ) ^ (((d * L : ℕ) : ℝ) / 2) *
        (3 : ℝ) ^ (-(((d * m : ℕ)) : ℝ) / 2) := by
      rw [hFdef, hdiv]
      exact mul_le_mul_of_nonneg_right hsq (by positivity)
    refine le_trans (mul_le_mul_of_nonneg_right hstep hqpos.le) (le_of_eq ?_)
    rw [three_rpow_pow, three_rpow_pow, three_rpow_pow, mul_assoc, mul_assoc,
      three_rpow_mul, three_rpow_mul, mul_assoc, three_rpow_mul]
    congr 1
    push_cast
    ring_nf
  -- assemble
  have hmin : F * ((3 : ℝ) ^ (-a / 2)) ^ L ≤
      min ((2 : ℝ) ^ ((d : ℝ) / 2) * ((3 : ℝ) ^ (-(d : ℝ) / 2)) ^ m *
        ((3 : ℝ) ^ (((d : ℝ) - a) / 2)) ^ L) (((3 : ℝ) ^ (-a / 2)) ^ L) := by
    refine le_min hF2 ?_
    calc F * ((3 : ℝ) ^ (-a / 2)) ^ L ≤ 1 * ((3 : ℝ) ^ (-a / 2)) ^ L :=
          mul_le_mul_of_nonneg_right hF1 hqpos.le
      _ = ((3 : ℝ) ^ (-a / 2)) ^ L := one_mul _
  rw [colorScale, perScaleAmplitude, ← hFdef]
  have hTinv : (0 : ℝ) ≤ T⁻¹ := le_of_lt (inv_pos.mpr hT)
  calc gammaTriangleConst 2 *
        HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 * F *
        (2 * (T⁻¹ * ((3 : ℝ) ^ (-a / 2)) ^ L))
      = 2 * gammaTriangleConst 2 *
          HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
          (T⁻¹ * (F * ((3 : ℝ) ^ (-a / 2)) ^ L)) := by ring
    _ ≤ 2 * gammaTriangleConst 2 *
          HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
          (T⁻¹ * min ((2 : ℝ) ^ ((d : ℝ) / 2) * ((3 : ℝ) ^ (-(d : ℝ) / 2)) ^ m *
            ((3 : ℝ) ^ (((d : ℝ) - a) / 2)) ^ L) (((3 : ℝ) ^ (-a / 2)) ^ L)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmin hTinv) colorConst_pos.le

/-- The per-scale estimate of Step 1 at the amplitude `perScaleAmplitude`. -/
theorem isBigOWith_gammaSigma_abs_scaleAverage [IsProbabilityMeasure μ]
    {B : ℕ → (Fin d → ℤ) → Set Ω} {a T : ℝ} {m L : ℕ}
    (hB : ∀ (l : ℕ) (y : Fin d → ℤ), MeasurableSet (B l y))
    (hindep : ∀ (l : ℕ) (S S' : Set (Fin d → ℤ)),
      (∀ u ∈ S, ∀ v ∈ S', 3 ^ l < latDist u v) →
      Indep (siteSigma B S l) (siteSigma B S' l) μ)
    (htail : ∀ (l : ℕ) (y : Fin d → ℤ),
      μ.real (B l y) ≤ Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * (l : ℝ)))))
    (ha : 0 < a) (hT : 1 ≤ T) :
    IsBigOWith μ (gammaSigma 2) (fun ω => |scaleAverage B μ L m ω|)
      (perScaleAmplitude d a T m L) := by
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hqbase : (0 : ℝ) < (3 : ℝ) ^ (-a / 2) := Real.rpow_pos_of_pos three_pos_real _
  have hqbase1 : (3 : ℝ) ^ (-a / 2) ≤ 1 :=
    le_of_lt (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [ha]))
  have hq0 : (0 : ℝ) < ((3 : ℝ) ^ (-a / 2)) ^ L := by positivity
  have hq1 : ((3 : ℝ) ^ (-a / 2)) ^ L ≤ 1 := pow_le_one₀ hqbase.le hqbase1
  have hA0 : 0 < T⁻¹ * ((3 : ℝ) ^ (-a / 2)) ^ L := by positivity
  have hA1 : T⁻¹ * ((3 : ℝ) ^ (-a / 2)) ^ L ≤ 1 := by
    have hTinv : T⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hT0]
      exact hT
    have hmul : T⁻¹ * ((3 : ℝ) ^ (-a / 2)) ^ L ≤ 1 * 1 :=
      mul_le_mul hTinv hq1 hq0.le zero_le_one
    linarith only [hmul]
  have hpow : (T⁻¹ * ((3 : ℝ) ^ (-a / 2)) ^ L) ^ (-(2 : ℝ)) =
      T ^ 2 * (3 : ℝ) ^ (a * (L : ℝ)) := by
    rw [inv_mul_rpow_neg_two hT0 hq0, three_rpow_pow_neg_two]
  have hscale := isBigO_gammaSigma_scaleAverage (μ := μ) (m := m) (L := L) hB (hindep L)
    hA0 hA1 (fun z => by rw [hpow]; exact htail L z)
  exact hscale.mono_scale (colorScale_mul_le d m L hT0)

/-! ### The scale sum -/

/-- The dimensional constant in the corrected amplitude of `e.density.bound`. -/
def densityBoundConst (d : ℕ) : ℝ :=
  gammaTriangleConst 2 *
    (2 * gammaTriangleConst 2 *
      HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2) *
    (2 * (2 : ℝ) ^ ((d : ℝ) / 2) * ((d : ℝ) + 2))

theorem densityBoundConst_pos (d : ℕ) : 0 < densityBoundConst d := by
  rw [densityBoundConst]
  have h1 : (0 : ℝ) < gammaTriangleConst 2 := gammaTriangleConst_pos
  have h2 : (0 : ℝ) < 2 * (2 : ℝ) ^ ((d : ℝ) / 2) * ((d : ℝ) + 2) := by positivity
  exact mul_pos (mul_pos h1 colorConst_pos) h2

/-- **The scale sum of ABK26 Step 1.** The pole `a^{-1}` comes from the scales
`L > m`, the pole `(d-a)^{-1}` from the scales `L ≤ m`. -/
theorem tsum_perScaleAmplitude_le (d : ℕ) {a T : ℝ} (ha : 0 < a) (had : a < (d : ℝ))
    (hT : 0 < T) (m : ℕ) :
    ∑' L, perScaleAmplitude d a T m L ≤
      (2 * gammaTriangleConst 2 *
          HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2) *
        (2 * (2 : ℝ) ^ ((d : ℝ) / 2) * ((d : ℝ) + 2)) *
        (a⁻¹ + ((d : ℝ) - a)⁻¹) * T⁻¹ * ((3 : ℝ) ^ (-a / 2)) ^ m := by
  set c₂ : ℝ := (2 : ℝ) ^ ((d : ℝ) / 2) with hc₂def
  set s : ℝ := (3 : ℝ) ^ (-(d : ℝ) / 2) with hsdef
  set ρ : ℝ := (3 : ℝ) ^ (((d : ℝ) - a) / 2) with hρdef
  set q : ℝ := (3 : ℝ) ^ (-a / 2) with hqdef
  have hc₂1 : (1 : ℝ) ≤ c₂ := by
    rw [hc₂def]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hspos : 0 < s := by rw [hsdef]; positivity
  have hqpos : 0 < q := by rw [hqdef]; positivity
  have hq1 : q < 1 := by
    rw [hqdef]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [ha])
  have hρ1 : 1 + ((d : ℝ) - a) / 2 ≤ ρ := by
    rw [hρdef]
    have hrp := add_one_le_three_rpow (x := ((d : ℝ) - a) / 2) (by linarith only [had])
    linarith only [hrp]
  have hρpos : 1 < ρ := by linarith only [hρ1, had]
  have hsρ : s * ρ = q := by
    rw [hsdef, hρdef, hqdef, three_rpow_mul]
    congr 1
    ring
  have hc₂pos : 0 < c₂ := lt_of_lt_of_le zero_lt_one hc₂1
  -- the summand
  set f : ℕ → ℝ := fun L => min (c₂ * s ^ m * ρ ^ L) (q ^ L) with hfdef
  have hf0 : ∀ L, 0 ≤ f L := fun L => le_min
    (mul_nonneg (mul_nonneg hc₂pos.le (pow_nonneg hspos.le m))
      (pow_nonneg (by linarith only [hρpos] : (0 : ℝ) ≤ ρ) L))
    (pow_nonneg hqpos.le L)
  have hfq : ∀ L, f L ≤ q ^ L := fun L => min_le_right _ _
  have hfsum : Summable f :=
    Summable.of_nonneg_of_le hf0 hfq (summable_geometric_of_lt_one hqpos.le hq1)
  -- split at `m`
  have hsplit : ∑ L ∈ Finset.range (m + 1), f L + ∑' j, f (j + (m + 1)) = ∑' L, f L :=
    hfsum.sum_add_tsum_nat_add (m + 1)
  -- the low scales
  have hlow : ∑ L ∈ Finset.range (m + 1), f L ≤ c₂ * q ^ m * (ρ / (ρ - 1)) := by
    have hgeom : ∑ L ∈ Finset.range (m + 1), ρ ^ L = (ρ ^ (m + 1) - 1) / (ρ - 1) :=
      geom_sum_eq (by linarith only [hρpos]) (m + 1)
    have hstep : ∑ L ∈ Finset.range (m + 1), f L ≤
        c₂ * s ^ m * ∑ L ∈ Finset.range (m + 1), ρ ^ L := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun L _ => min_le_left _ _
    have hρm : c₂ * s ^ m * (ρ ^ (m + 1) / (ρ - 1)) = c₂ * q ^ m * (ρ / (ρ - 1)) := by
      rw [pow_succ, ← hsρ, mul_pow]
      field_simp
    refine le_trans hstep ?_
    rw [hgeom]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity)) (le_of_eq hρm)
    exact div_le_div_of_nonneg_right (by linarith only [hρpos]) (by linarith only [hρpos])
  -- the high scales
  have hhigh : ∑' j, f (j + (m + 1)) ≤ q ^ m * (q / (1 - q)) := by
    have hsum : ∑' j : ℕ, q ^ (j + (m + 1)) = q ^ (m + 1) * (1 - q)⁻¹ := by
      have : ∀ j : ℕ, q ^ (j + (m + 1)) = q ^ (m + 1) * q ^ j := by
        intro j; rw [pow_add]; ring
      rw [tsum_congr this, tsum_mul_left, tsum_geometric_of_lt_one hqpos.le hq1]
    have hsummable1 : Summable fun j : ℕ => f (j + (m + 1)) :=
      (summable_nat_add_iff (m + 1)).mpr hfsum
    have hsummable2 : Summable fun j : ℕ => q ^ (j + (m + 1)) :=
      (summable_nat_add_iff (m + 1)).mpr (summable_geometric_of_lt_one hqpos.le hq1)
    refine le_trans (Summable.tsum_le_tsum (fun j => hfq _) hsummable1 hsummable2)
      (le_of_eq ?_)
    rw [hsum, pow_succ]
    field_simp
  -- the two ratios
  have hratio1 : ρ / (ρ - 1) ≤ 1 + 2 / ((d : ℝ) - a) := by
    have hda : 0 < (d : ℝ) - a := by linarith only [had]
    have hρm1 : ((d : ℝ) - a) / 2 ≤ ρ - 1 := by linarith only [hρ1]
    have hpos : 0 < ρ - 1 := by linarith only [hρpos]
    have hdiv : ρ / (ρ - 1) = 1 + 1 / (ρ - 1) := by
      field_simp
      linarith only []
    have hle : 1 / (ρ - 1) ≤ 2 / ((d : ℝ) - a) := by
      rw [div_le_div_iff₀ hpos hda]
      linarith only [hρm1]
    linarith only [hdiv, hle]
  have hratio2 : q / (1 - q) ≤ 2 / a := by
    have hQ : (1 : ℝ) + a / 2 ≤ q⁻¹ := by
      have hqinv : q⁻¹ = (3 : ℝ) ^ (a / 2) := by
        rw [hqdef, ← Real.rpow_neg three_pos_real.le]
        congr 1
        ring
      rw [hqinv]
      have hrp := add_one_le_three_rpow (x := a / 2) (by linarith only [ha])
      linarith only [hrp]
    have h1q : 0 < 1 - q := by linarith only [hq1]
    have hkey : a / 2 * q ≤ 1 - q := by
      have := mul_le_mul_of_nonneg_right hQ hqpos.le
      rw [inv_mul_cancel₀ hqpos.ne'] at this
      linarith only [this]
    rw [div_le_div_iff₀ h1q (by linarith only [ha] : (0 : ℝ) < a)]
    linarith only [hkey]
  -- put the pieces together
  have hftotal : ∑' L, f L ≤ q ^ m * (c₂ * (1 + 2 / ((d : ℝ) - a)) + 2 / a) := by
    rw [← hsplit]
    have h1 : c₂ * q ^ m * (ρ / (ρ - 1)) ≤ q ^ m * (c₂ * (1 + 2 / ((d : ℝ) - a))) := by
      have := mul_le_mul_of_nonneg_left hratio1
        (by positivity : (0 : ℝ) ≤ c₂ * q ^ m)
      calc c₂ * q ^ m * (ρ / (ρ - 1)) ≤ c₂ * q ^ m * (1 + 2 / ((d : ℝ) - a)) := this
        _ = q ^ m * (c₂ * (1 + 2 / ((d : ℝ) - a))) := by ring
    have h2 : q ^ m * (q / (1 - q)) ≤ q ^ m * (2 / a) :=
      mul_le_mul_of_nonneg_left hratio2 (by positivity)
    have hadd := add_le_add (le_trans hlow h1) (le_trans hhigh h2)
    linarith only [hadd]
  have hconst : c₂ * (1 + 2 / ((d : ℝ) - a)) + 2 / a ≤
      2 * c₂ * ((d : ℝ) + 2) * (a⁻¹ + ((d : ℝ) - a)⁻¹) := by
    have hda : 0 < (d : ℝ) - a := by linarith only [had]
    have hd : (0 : ℝ) < d := by linarith only [ha, had]
    have hu : 0 < a⁻¹ := inv_pos.mpr ha
    have hv : 0 < ((d : ℝ) - a)⁻¹ := inv_pos.mpr hda
    have h1 : (1 : ℝ) ≤ (d : ℝ) * a⁻¹ := by
      rw [le_mul_inv_iff₀ ha]
      linarith only [had]
    have h2 : 2 / ((d : ℝ) - a) = 2 * ((d : ℝ) - a)⁻¹ := by
      rw [div_eq_mul_inv]
    have h3 : 2 / a = 2 * a⁻¹ := by rw [div_eq_mul_inv]
    rw [h2, h3]
    have e1 : c₂ * (1 + 2 * ((d : ℝ) - a)⁻¹) + 2 * a⁻¹ =
        c₂ + 2 * (c₂ * ((d : ℝ) - a)⁻¹) + 2 * a⁻¹ := by ring
    have e2 : 2 * c₂ * ((d : ℝ) + 2) * (a⁻¹ + ((d : ℝ) - a)⁻¹) =
        2 * (c₂ * ((d : ℝ) * a⁻¹)) + 4 * (c₂ * a⁻¹) +
          2 * (c₂ * ((d : ℝ) * ((d : ℝ) - a)⁻¹)) + 4 * (c₂ * ((d : ℝ) - a)⁻¹) := by ring
    rw [e1, e2]
    have h4 : c₂ ≤ c₂ * ((d : ℝ) * a⁻¹) := le_mul_of_one_le_right hc₂pos.le h1
    have h5 : (0 : ℝ) ≤ c₂ * ((d : ℝ) * ((d : ℝ) - a)⁻¹) :=
      mul_nonneg hc₂pos.le (mul_nonneg hd.le hv.le)
    have h6 : (2 : ℝ) * a⁻¹ ≤ 4 * (c₂ * a⁻¹) := by
      linarith only [mul_nonneg (by linarith only [hc₂1] : (0 : ℝ) ≤ 4 * c₂ - 2) hu.le]
    have h7 : (0 : ℝ) ≤ c₂ * ((d : ℝ) - a)⁻¹ := mul_nonneg hc₂pos.le hv.le
    have h8 : (0 : ℝ) ≤ c₂ * ((d : ℝ) * a⁻¹) := mul_nonneg hc₂pos.le (mul_nonneg hd.le hu.le)
    linarith only [h4, h5, h6, h7, h8]
  have hmain : ∑' L, f L ≤ 2 * c₂ * ((d : ℝ) + 2) * (a⁻¹ + ((d : ℝ) - a)⁻¹) * q ^ m := by
    refine le_trans hftotal ?_
    calc q ^ m * (c₂ * (1 + 2 / ((d : ℝ) - a)) + 2 / a)
        ≤ q ^ m * (2 * c₂ * ((d : ℝ) + 2) * (a⁻¹ + ((d : ℝ) - a)⁻¹)) :=
          mul_le_mul_of_nonneg_left hconst (by positivity)
      _ = 2 * c₂ * ((d : ℝ) + 2) * (a⁻¹ + ((d : ℝ) - a)⁻¹) * q ^ m := by ring
  -- transfer to `perScaleAmplitude`
  have hpS : ∀ L, perScaleAmplitude d a T m L =
      (2 * gammaTriangleConst 2 *
        HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2) * (T⁻¹ * f L) := by
    intro L
    rw [perScaleAmplitude, hfdef]
  rw [tsum_congr hpS, tsum_mul_left, tsum_mul_left]
  have hTinv : (0 : ℝ) ≤ T⁻¹ := le_of_lt (inv_pos.mpr hT)
  calc (2 * gammaTriangleConst 2 *
        HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2) * (T⁻¹ * ∑' L, f L)
      ≤ (2 * gammaTriangleConst 2 *
          HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2) *
          (T⁻¹ * (2 * c₂ * ((d : ℝ) + 2) * (a⁻¹ + ((d : ℝ) - a)⁻¹) * q ^ m)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmain hTinv)
          colorConst_pos.le
    _ = (2 * gammaTriangleConst 2 *
          HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2) *
          (2 * c₂ * ((d : ℝ) + 2)) * (a⁻¹ + ((d : ℝ) - a)⁻¹) * T⁻¹ * q ^ m := by ring

/-! ### The density bound -/

/-- The tail form on the corrected range is `measureReal_densityAverage_gt_le_exp`.

The hypotheses are exactly (ii) and (iii) of the source lemma together with its
parameter constraints `a ∈ (0,d)` and `T ≥ 1`; hypothesis (i) is not needed for
Step 1. Measurability of the bad events is the reading of the word "events". -/
theorem isBigOWith_gammaSigma_densityAverage [IsProbabilityMeasure μ]
    {B : ℕ → (Fin d → ℤ) → Set Ω} {a T : ℝ} {m : ℕ}
    (hB : ∀ (l : ℕ) (y : Fin d → ℤ), MeasurableSet (B l y))
    (hindep : ∀ (l : ℕ) (S S' : Set (Fin d → ℤ)),
      (∀ u ∈ S, ∀ v ∈ S', 3 ^ l < latDist u v) →
      Indep (siteSigma B S l) (siteSigma B S' l) μ)
    (htail : ∀ (l : ℕ) (y : Fin d → ℤ),
      μ.real (B l y) ≤ Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * (l : ℝ)))))
    (ha : 0 < a) (had : a < (d : ℝ)) (hT : 1 ≤ T) :
    IsBigOWith μ (gammaSigma 2) (densityAverage B μ m)
      (densityBoundConst d * (a⁻¹ + ((d : ℝ) - a)⁻¹) * T⁻¹ *
        ((3 : ℝ) ^ (-a / 2)) ^ m) := by
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hmeas : ∀ L : ℕ, Measurable fun ω => |scaleAverage B μ L m ω| := by
    intro L
    have h : Measurable (scaleAverage B μ L m) :=
      measurable_const.mul
        (Finset.measurable_sum _ fun z _ => measurable_centeredScale hB L z)
    exact Measurable.abs h
  have htri := Orlicz.isBigOWith_gammaSigma_tsum_of_tsum_le (μ := μ) (σ := 2)
    (X := fun L ω => |scaleAverage B μ L m ω|)
    (a := perScaleAmplitude d a T m)
    (B := (2 * gammaTriangleConst 2 *
        HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2) *
      (2 * (2 : ℝ) ^ ((d : ℝ) / 2) * ((d : ℝ) + 2)) *
      (a⁻¹ + ((d : ℝ) - a)⁻¹) * T⁻¹ * ((3 : ℝ) ^ (-a / 2)) ^ m)
    (by norm_num) (fun _ _ => abs_nonneg _) hmeas
    (fun L => perScaleAmplitude_pos d hT0 m L)
    (summable_perScaleAmplitude d ha hT0 m)
    (fun L => isBigOWith_gammaSigma_abs_scaleAverage hB hindep htail ha hT)
    (tsum_perScaleAmplitude_le d ha had hT0 m)
  refine (htri.of_le fun ω => densityAverage_le_tsum_abs_scaleAverage hB m ω).mono_scale ?_
  rw [densityBoundConst]
  exact le_of_eq (by ring)

/-- The constant `c(d) > 0` in the exponent of the printed tail bound. -/
def densityBoundExpConst (d : ℕ) : ℝ := (densityBoundConst d ^ 2 * (d : ℝ) ^ 2)⁻¹

theorem densityBoundExpConst_pos {d : ℕ} (hd : 0 < d) : 0 < densityBoundExpConst d := by
  rw [densityBoundExpConst]
  have h1 : (0 : ℝ) < densityBoundConst d ^ 2 := pow_pos (densityBoundConst_pos d) 2
  have h2 : (0 : ℝ) < (d : ℝ) ^ 2 := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    positivity
  exact inv_pos.mpr (mul_pos h1 h2)

/-- On that range it is an exact reformulation of
`isBigOWith_gammaSigma_densityAverage`. -/
theorem measureReal_densityAverage_gt_le_exp [IsProbabilityMeasure μ]
    {B : ℕ → (Fin d → ℤ) → Set Ω} {a T t : ℝ} {m : ℕ}
    (hB : ∀ (l : ℕ) (y : Fin d → ℤ), MeasurableSet (B l y))
    (hindep : ∀ (l : ℕ) (S S' : Set (Fin d → ℤ)),
      (∀ u ∈ S, ∀ v ∈ S', 3 ^ l < latDist u v) →
      Indep (siteSigma B S l) (siteSigma B S' l) μ)
    (htail : ∀ (l : ℕ) (y : Fin d → ℤ),
      μ.real (B l y) ≤ Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * (l : ℝ)))))
    (ha : 0 < a) (had : a < (d : ℝ)) (hT : 1 ≤ T)
    (ht : densityBoundConst d * (a⁻¹ + ((d : ℝ) - a)⁻¹) * T⁻¹ *
      ((3 : ℝ) ^ (-a / 2)) ^ m ≤ t) :
    μ.real {ω | t < densityAverage B μ m ω} ≤
      Real.exp (-(densityBoundExpConst d * t ^ 2 * a ^ 2 * ((d : ℝ) - a) ^ 2 * T ^ 2 *
        (3 : ℝ) ^ (a * (m : ℝ)))) := by
  have hbase := isBigOWith_gammaSigma_densityAverage (m := m) hB hindep htail ha had hT
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hda : (0 : ℝ) < (d : ℝ) - a := by linarith only [had]
  have hd : (0 : ℝ) < (d : ℝ) := by linarith only [ha, had]
  have hCpos : (0 : ℝ) < densityBoundConst d := densityBoundConst_pos d
  have hPpos : (0 : ℝ) < ((3 : ℝ) ^ (-a / 2)) ^ m := by
    have : (0 : ℝ) < (3 : ℝ) ^ (-a / 2) := Real.rpow_pos_of_pos three_pos_real _
    positivity
  have hGpos : (0 : ℝ) < (3 : ℝ) ^ (a * (m : ℝ)) := Real.rpow_pos_of_pos three_pos_real _
  have hSpos : (0 : ℝ) < a⁻¹ + ((d : ℝ) - a)⁻¹ :=
    add_pos (inv_pos.mpr ha) (inv_pos.mpr hda)
  set A : ℝ := densityBoundConst d * (a⁻¹ + ((d : ℝ) - a)⁻¹) * T⁻¹ *
    ((3 : ℝ) ^ (-a / 2)) ^ m with hAdef
  have hApos : 0 < A := by
    rw [hAdef]
    exact mul_pos (mul_pos (mul_pos hCpos hSpos) (inv_pos.mpr hT0)) hPpos
  have hs : 1 ≤ t / A := (one_le_div hApos).mpr ht
  have hev := hbase hs
  rw [show A * (t / A) = t by field_simp, gammaSigma_inv] at hev
  refine le_trans hev (Real.exp_le_exp.mpr ?_)
  have hrpow : (t / A) ^ (2 : ℝ) = (t / A) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (t / A) 2]
    norm_num
  rw [hrpow]
  have hP2 : (((3 : ℝ) ^ (-a / 2)) ^ m) ^ 2 = ((3 : ℝ) ^ (a * (m : ℝ)))⁻¹ := by
    rw [three_rpow_pow, ← Real.rpow_natCast ((3 : ℝ) ^ (-a / 2 * (m : ℝ))) 2,
      ← Real.rpow_mul three_pos_real.le, ← Real.rpow_neg three_pos_real.le]
    congr 1
    push_cast
    ring
  have hA2 : A ^ 2 = densityBoundConst d ^ 2 * (a⁻¹ + ((d : ℝ) - a)⁻¹) ^ 2 *
      (T ^ 2)⁻¹ * ((3 : ℝ) ^ (a * (m : ℝ)))⁻¹ := by
    rw [hAdef, ← hP2]
    ring
  have hfinal : (t / A) ^ (2 : ℕ) =
      densityBoundExpConst d * t ^ 2 * a ^ 2 * ((d : ℝ) - a) ^ 2 * T ^ 2 *
        (3 : ℝ) ^ (a * (m : ℝ)) := by
    rw [div_pow, hA2, densityBoundExpConst]
    field_simp
    ring
  rw [hfinal]

end

end Algsuperdiff.Section3.Provider.Percolation
