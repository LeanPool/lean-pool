/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineDepthBandGeometry

/-!
# HomSpineDepthBandArith

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The band sum of the single-depth Gagliardo reduction, in closed form

## What this file is for

Pure scalar arithmetic, over abstract reals, away from every measure: the exact
size of the triadic band sum the Gagliardo reduction of a depth-`j` slice
produces.  Banding the double integral at `|x-y| ∈ [3^{-(k+1)}·L, 3^{-k}·L)`
(`L` the side of the ambient cube, `k: ℕ` by `exists_triadic_band`), band `k`
carries

* the KERNEL factor `(3^{-(k+1)}L)^{-(a+d)}` (`a = s·p'` the order weight),
* the sup-BALL factor `(2·3^{-k}L)^d`, and
* the STRADDLING weight `bandStraddleWeight`: `1` at the far bands `k < j`
  (every pair straddles) and `2·D·3^{j-k}` at the near bands `k ≥ j`
  (`HomSpineDepthStraddleMeasure.volume_cubeBoundaryLayer_le` at thickness
  `3^{j-k}`).

`sum_bandTerm_le` sums the three over ALL bands and matches exactly
`HomSpineDepthGagliardoBand.gridDepthBandFactor a j = near + Σ_{i<j} 3^{-i·a}`,
at the explicit dimensional prefactor `2^{d+2}·D·3^d` and the cell-side weight
`(L/3^j)^{-a}`.  The two halves are the band facts used verbatim:
`sum_near_band_le` for `k ≥ j` and the truncated geometric sum for `k < j`.
The one-band kernel gain `3^a ≤ 2` is `HomLiftScaleArith.three_rpow_le_two`.
-/

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26
open scoped BigOperators ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

/-! ## 1. Elementary `rpow` facts on the admissible band -/

/-- The triadic weight as a real power. -/
theorem inv_three_pow_eq (k : ℕ) : (1 / 3 : ℝ) ^ k = (3 : ℝ) ^ (-(k : ℝ)) := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]

/-! ## 2. The band term -/

/-- The straddling weight of band `k` at depth `j`: at the far bands every pair
straddles the depth-`j` skeleton (weight `1`); at the near bands only the
boundary layer of thickness `3^{j-k}` does, and its measure is `2·d·3^{j-k}`
times the cell measure — read here at `D = d+1`. -/
def bandStraddleWeight (D : ℝ) (j k : ℕ) : ℝ :=
  if k < j then 1 else 2 * D * (1 / 3 : ℝ) ^ (k - j)

theorem bandStraddleWeight_nonneg {D : ℝ} (hD : 0 ≤ D) (j k : ℕ) :
    0 ≤ bandStraddleWeight D j k := by
  rw [bandStraddleWeight]
  split_ifs with h
  · norm_num
  · exact mul_nonneg (mul_nonneg (by norm_num) hD) (pow_nonneg (by norm_num) _)

/-- The kernel-times-ball factor of band `k`: `(3^{-(k+1)}L)^{-(a+d)}·(2·3^{-k}L)^d`. -/
def bandKernelVolume (a L : ℝ) (dd k : ℕ) : ℝ :=
  ((1 / 3 : ℝ) ^ (k + 1) * L) ^ (-(a + (dd : ℝ))) * (2 * ((1 / 3 : ℝ) ^ k * L)) ^ dd

/-- **The band factor in closed form.**  The `d` powers of the ball radius cancel
`d` of the `d+a` powers of the kernel, leaving one gain `3^a` per band and the
running weight `3^{a·k}·L^{-a}`. -/
theorem bandKernelVolume_eq {a L : ℝ} (hL : 0 < L) (dd k : ℕ) :
    bandKernelVolume a L dd k =
      2 ^ dd * (3 : ℝ) ^ (a + (dd : ℝ)) * ((3 : ℝ) ^ (a * (k : ℝ)) * L ^ (-a)) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hk1 : ((1 / 3 : ℝ) ^ (k + 1) : ℝ) = (3 : ℝ) ^ (-((k : ℝ) + 1)) := by
    rw [inv_three_pow_eq]
    push_cast
    ring_nf
  have hk : ((1 / 3 : ℝ) ^ k : ℝ) = (3 : ℝ) ^ (-(k : ℝ)) := inv_three_pow_eq k
  rw [bandKernelVolume, hk1, hk, Real.mul_rpow (Real.rpow_nonneg h3.le _) hL.le,
    ← Real.rpow_mul h3.le,
    show (2 : ℝ) * ((3 : ℝ) ^ (-(k : ℝ)) * L) = 2 * (3 : ℝ) ^ (-(k : ℝ)) * L by ring,
    mul_pow, mul_pow, ← Real.rpow_natCast ((3 : ℝ) ^ (-(k : ℝ))) dd, ← Real.rpow_mul h3.le,
    ← Real.rpow_natCast L dd]
  have e3 : (3 : ℝ) ^ ((-((k : ℝ) + 1)) * (-(a + (dd : ℝ)))) * (3 : ℝ) ^ (-(k : ℝ) * (dd : ℝ)) =
      (3 : ℝ) ^ (a + (dd : ℝ)) * (3 : ℝ) ^ (a * (k : ℝ)) := by
    rw [← Real.rpow_add h3, ← Real.rpow_add h3]
    congr 1
    ring
  have eL : L ^ ((dd : ℕ) : ℝ) * L ^ (-(a + (dd : ℝ))) = L ^ (-a) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  calc (3 : ℝ) ^ ((-((k : ℝ) + 1)) * (-(a + (dd : ℝ)))) * L ^ (-(a + (dd : ℝ))) *
        (2 ^ dd * (3 : ℝ) ^ (-(k : ℝ) * (dd : ℝ)) * L ^ ((dd : ℕ) : ℝ))
      = 2 ^ dd *
          ((3 : ℝ) ^ ((-((k : ℝ) + 1)) * (-(a + (dd : ℝ)))) * (3 : ℝ) ^ (-(k : ℝ) * (dd : ℝ))) *
          (L ^ ((dd : ℕ) : ℝ) * L ^ (-(a + (dd : ℝ)))) := by ring
    _ = 2 ^ dd * ((3 : ℝ) ^ (a + (dd : ℝ)) * (3 : ℝ) ^ (a * (k : ℝ))) * L ^ (-a) := by
        rw [e3, eL]
    _ = 2 ^ dd * (3 : ℝ) ^ (a + (dd : ℝ)) * ((3 : ℝ) ^ (a * (k : ℝ)) * L ^ (-a)) := by ring

theorem bandKernelVolume_nonneg {a L : ℝ} (hL : 0 ≤ L) (dd k : ℕ) :
    0 ≤ bandKernelVolume a L dd k := by
  refine mul_nonneg (Real.rpow_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hL) _) ?_
  exact pow_nonneg (mul_nonneg (by norm_num) (mul_nonneg (pow_nonneg (by norm_num) _) hL)) _

/-- The full band term: kernel × ball × straddling weight. -/
def bandTerm (a L D : ℝ) (dd j k : ℕ) : ℝ :=
  bandKernelVolume a L dd k * bandStraddleWeight D j k

/-! ## 3. The two halves of the band sum -/

/-- The FAR half `k < j`: the running weights `3^{a·k}` are the truncated
geometric sum of `HomSpineDepthGagliardoBand`, read backwards from the cell
scale. -/
theorem sum_far_three_rpow_le {a : ℝ} (ha0 : 0 < a) (j : ℕ) :
    (∑ k ∈ Finset.range j, (3 : ℝ) ^ (a * (k : ℝ))) ≤
      (3 : ℝ) ^ (a * (j : ℝ)) * ∑ i ∈ Finset.range j, (3 : ℝ) ^ (-a * (i : ℝ)) := by
  rw [← Finset.sum_range_reflect (fun k => (3 : ℝ) ^ (a * (k : ℝ))) j, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hij : i < j := Finset.mem_range.mp hi
  have hcast : ((j - 1 - i : ℕ) : ℝ) ≤ (j : ℝ) - (i : ℝ) := by
    have hn : (j - 1 - i : ℕ) + i ≤ j := by omega
    have hcastn := (Nat.cast_le (α := ℝ)).mpr hn
    push_cast at hcastn
    linarith only [hcastn]
  have hexp : a * ((j - 1 - i : ℕ) : ℝ) ≤ a * (j : ℝ) + -a * (i : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hcast ha0.le
    linarith only [hmul]
  calc (3 : ℝ) ^ (a * ((j - 1 - i : ℕ) : ℝ))
      ≤ (3 : ℝ) ^ (a * (j : ℝ) + -a * (i : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = (3 : ℝ) ^ (a * (j : ℝ)) * (3 : ℝ) ^ (-a * (i : ℝ)) :=
        Real.rpow_add (by norm_num) _ _

/-- The NEAR half `k ≥ j`: geometric at ratio `3^{-(1-a)} ≤ 3^{-1/2}`, so the
`sum_near_band_le` applies verbatim. -/
theorem sum_near_bandStraddleWeight_le {a : ℝ} (ha : a ≤ 1 / 2) {D : ℝ} (hD : 0 ≤ D)
    (j n : ℕ) :
    (∑ k ∈ Finset.Ico j n, (3 : ℝ) ^ (a * (k : ℝ)) * bandStraddleWeight D j k) ≤
      2 * D * (3 : ℝ) ^ (a * (j : ℝ)) * nearBandGeometricConstant := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hterm : ∀ i ∈ Finset.range (n - j),
      (3 : ℝ) ^ (a * ((j + i : ℕ) : ℝ)) * bandStraddleWeight D j (j + i) =
        2 * D * (3 : ℝ) ^ (a * (j : ℝ)) * (3 : ℝ) ^ (-(1 - a) * (i : ℝ)) := by
    intro i _
    have hnotlt : ¬ (j + i < j) := by omega
    have hsub : j + i - j = i := by omega
    rw [bandStraddleWeight, ite_eq_right hnotlt, hsub, inv_three_pow_eq]
    have hsplit : (3 : ℝ) ^ (a * ((j + i : ℕ) : ℝ)) =
        (3 : ℝ) ^ (a * (j : ℝ)) * (3 : ℝ) ^ (a * (i : ℝ)) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      push_cast
      ring
    have hmerge : (3 : ℝ) ^ (a * (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ)) =
        (3 : ℝ) ^ (-(1 - a) * (i : ℝ)) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      ring
    rw [hsplit, ← hmerge]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (sum_near_band_le ha (n - j)) ?_
  exact mul_nonneg (mul_nonneg (by norm_num) hD) (Real.rpow_nonneg (by norm_num) _)

/-! ## 4. The band sum -/

/-- The weighted running sum, both halves together. -/
theorem sum_three_rpow_mul_bandStraddleWeight_le {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2)
    {D : ℝ} (hD : 1 ≤ D) (j n : ℕ) :
    (∑ k ∈ Finset.range n, (3 : ℝ) ^ (a * (k : ℝ)) * bandStraddleWeight D j k) ≤
      2 * D * (3 : ℝ) ^ (a * (j : ℝ)) * gridDepthBandFactor a j := by
  have hD0 : (0 : ℝ) ≤ D := by linarith only [hD]
  have hjpow : (0 : ℝ) ≤ (3 : ℝ) ^ (a * (j : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hnear0 : 0 ≤ nearBandGeometricConstant := nearBandGeometricConstant_pos.le
  have hfarsum0 : (0 : ℝ) ≤ ∑ i ∈ Finset.range j, (3 : ℝ) ^ (-a * (i : ℝ)) :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (by norm_num) _
  /- the far half, with the weight identically `1` -/
  have hfar : (∑ k ∈ Finset.range j, (3 : ℝ) ^ (a * (k : ℝ)) * bandStraddleWeight D j k) ≤
      (3 : ℝ) ^ (a * (j : ℝ)) * ∑ i ∈ Finset.range j, (3 : ℝ) ^ (-a * (i : ℝ)) := by
    have hcongr : ∀ k ∈ Finset.range j,
        (3 : ℝ) ^ (a * (k : ℝ)) * bandStraddleWeight D j k = (3 : ℝ) ^ (a * (k : ℝ)) := by
      intro k hk
      rw [bandStraddleWeight, ite_eq_left (Finset.mem_range.mp hk), mul_one]
    rw [Finset.sum_congr rfl hcongr]
    exact sum_far_three_rpow_le ha0 j
  have htarget : (3 : ℝ) ^ (a * (j : ℝ)) *
        (∑ i ∈ Finset.range j, (3 : ℝ) ^ (-a * (i : ℝ))) +
      2 * D * (3 : ℝ) ^ (a * (j : ℝ)) * nearBandGeometricConstant ≤
        2 * D * (3 : ℝ) ^ (a * (j : ℝ)) * gridDepthBandFactor a j := by
    have hone : (3 : ℝ) ^ (a * (j : ℝ)) *
          (∑ i ∈ Finset.range j, (3 : ℝ) ^ (-a * (i : ℝ))) ≤
        2 * D * (3 : ℝ) ^ (a * (j : ℝ)) *
          (∑ i ∈ Finset.range j, (3 : ℝ) ^ (-a * (i : ℝ))) := by
      have hcoef : (1 : ℝ) * (3 : ℝ) ^ (a * (j : ℝ)) ≤ 2 * D * (3 : ℝ) ^ (a * (j : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith only [hD]) hjpow
      have := mul_le_mul_of_nonneg_right hcoef hfarsum0
      linarith only [this]
    rw [gridDepthBandFactor]
    have hexpand : 2 * D * (3 : ℝ) ^ (a * (j : ℝ)) *
        (nearBandGeometricConstant + ∑ i ∈ Finset.range j, (3 : ℝ) ^ (-a * (i : ℝ))) =
        2 * D * (3 : ℝ) ^ (a * (j : ℝ)) * nearBandGeometricConstant +
          2 * D * (3 : ℝ) ^ (a * (j : ℝ)) *
            (∑ i ∈ Finset.range j, (3 : ℝ) ^ (-a * (i : ℝ))) := by ring
    rw [hexpand]
    linarith only [hone]
  rcases le_total n j with hnj | hjn
  · have hsub : Finset.range n ⊆ Finset.range j := fun x hx =>
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hnj)
    have hmono : (∑ k ∈ Finset.range n, (3 : ℝ) ^ (a * (k : ℝ)) * bandStraddleWeight D j k) ≤
        ∑ k ∈ Finset.range j, (3 : ℝ) ^ (a * (k : ℝ)) * bandStraddleWeight D j k := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => ?_
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (bandStraddleWeight_nonneg hD0 j k)
    have hnearnn : (0 : ℝ) ≤ 2 * D * (3 : ℝ) ^ (a * (j : ℝ)) * nearBandGeometricConstant :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hD0) hjpow) hnear0
    linarith only [hmono, hfar, htarget, hnearnn]
  · have hsplit : (∑ k ∈ Finset.range j, (3 : ℝ) ^ (a * (k : ℝ)) * bandStraddleWeight D j k) +
        (∑ k ∈ Finset.Ico j n, (3 : ℝ) ^ (a * (k : ℝ)) * bandStraddleWeight D j k) =
        ∑ k ∈ Finset.range n, (3 : ℝ) ^ (a * (k : ℝ)) * bandStraddleWeight D j k := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
      exact Finset.sum_Ico_consecutive
        (fun k => (3 : ℝ) ^ (a * (k : ℝ)) * bandStraddleWeight D j k) (Nat.zero_le j) hjn
    have hnear := sum_near_bandStraddleWeight_le ha hD0 j n
    linarith only [hsplit, hfar, hnear, htarget]

/-- **THE BAND SUM, CLOSED.**  Every partial sum of the band terms is below the
depth-`j` band factor at the explicit dimensional prefactor `2^{d+2}·D·3^d` and
the cell-side weight `(L/3^j)^{-a}`.

This is the whole arithmetic of the single-depth Gagliardo reduction: the far
bands give `Σ_{i<j} 3^{-i·a}`, the near bands give `nearBandGeometricConstant`,
and the one-band kernel gain `3^a` is absorbed by `a ≤ 1/2`. -/
theorem sum_bandTerm_le {a L : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2) (hL : 0 < L)
    {D : ℝ} (hD : 1 ≤ D) (dd j n : ℕ) :
    (∑ k ∈ Finset.range n, bandTerm a L D dd j k) ≤
      2 ^ (dd + 2) * D * 3 ^ dd * (L / 3 ^ j) ^ (-a) * gridDepthBandFactor a j := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hD0 : (0 : ℝ) ≤ D := by linarith only [hD]
  have hcell : (L / 3 ^ j) ^ (-a) = (3 : ℝ) ^ (a * (j : ℝ)) * L ^ (-a) := by
    have h1 : ((3 : ℝ) ^ j : ℝ) = (3 : ℝ) ^ ((j : ℕ) : ℝ) := (Real.rpow_natCast 3 j).symm
    have h2 : ((3 : ℝ) ^ ((j : ℕ) : ℝ)) ^ (-a) = (3 : ℝ) ^ (-(a * (j : ℝ))) := by
      rw [← Real.rpow_mul h3.le]
      congr 1
      ring
    rw [Real.div_rpow hL.le (by positivity), h1, h2, div_eq_mul_inv, ← Real.rpow_neg h3.le,
      neg_neg]
    ring
  /- rewrite every band term in closed fo -/
  have hterm : ∀ k ∈ Finset.range n, bandTerm a L D dd j k =
      2 ^ dd * (3 : ℝ) ^ (a + (dd : ℝ)) * L ^ (-a) *
        ((3 : ℝ) ^ (a * (k : ℝ)) * bandStraddleWeight D j k) := by
    intro k _
    rw [bandTerm, bandKernelVolume_eq hL dd k]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hpre0 : (0 : ℝ) ≤ 2 ^ dd * (3 : ℝ) ^ (a + (dd : ℝ)) * L ^ (-a) :=
    mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg h3.le _))
      (Real.rpow_nonneg hL.le _)
  refine le_trans (mul_le_mul_of_nonneg_left
    (sum_three_rpow_mul_bandStraddleWeight_le ha0 ha hD j n) hpre0) ?_
  /- the prefactor: `3^{a+d} = 3^a·3^d ≤ 2·3^d` -/
  have hsplit : (3 : ℝ) ^ (a + (dd : ℝ)) = (3 : ℝ) ^ a * 3 ^ dd := by
    rw [Real.rpow_add h3, Real.rpow_natCast]
  have hgain : (3 : ℝ) ^ a ≤ 2 := three_rpow_le_two ha
  have hband0 : 0 ≤ gridDepthBandFactor a j := gridDepthBandFactor_nonneg a j
  have hjpow0 : (0 : ℝ) ≤ (3 : ℝ) ^ (a * (j : ℝ)) := Real.rpow_nonneg h3.le _
  have hL0 : (0 : ℝ) ≤ L ^ (-a) := Real.rpow_nonneg hL.le _
  have hrest0 : (0 : ℝ) ≤ 2 ^ dd * 3 ^ dd * L ^ (-a) *
      (2 * D * (3 : ℝ) ^ (a * (j : ℝ)) * gridDepthBandFactor a j) := by
    refine mul_nonneg (mul_nonneg (by positivity) hL0) ?_
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hD0) hjpow0) hband0
  have hlhs : 2 ^ dd * (3 : ℝ) ^ (a + (dd : ℝ)) * L ^ (-a) *
        (2 * D * (3 : ℝ) ^ (a * (j : ℝ)) * gridDepthBandFactor a j) =
      (3 : ℝ) ^ a * (2 ^ dd * 3 ^ dd * L ^ (-a) *
        (2 * D * (3 : ℝ) ^ (a * (j : ℝ)) * gridDepthBandFactor a j)) := by
    rw [hsplit]
    ring
  have hrhs : 2 ^ (dd + 2) * D * 3 ^ dd * (L / 3 ^ j) ^ (-a) * gridDepthBandFactor a j =
      2 * (2 ^ dd * 3 ^ dd * L ^ (-a) *
        (2 * D * (3 : ℝ) ^ (a * (j : ℝ)) * gridDepthBandFactor a j)) := by
    rw [hcell, pow_add]
    ring
  rw [hlhs, hrhs]
  exact mul_le_mul_of_nonneg_right hgain hrest0

end

end Algsuperdiff.Section4.Provider.Homogenization
