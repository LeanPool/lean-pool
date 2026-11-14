/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderAeSlopeDefect
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Covering.Differentiation

/-!
# CubeSchauderAeLimit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Cube Schauder: the Lebesgue-point limit of the a.e. identification

`CubeSchauderAeSlopeDefect.abs_slope_sub_le_cutoff_split` is the deterministic
inequality behind the almost-everywhere identification `Ψ = ∇w`.  This module
takes the limit and delivers the identification itself.

Fix a base point `x ∈ □_m` and a scale `j` small enough that the Euclidean ball
of radius `3^j/2` around `x` sits inside `□_m` — the open cube is open, so every
`j` below a threshold `j₀(x)` qualifies.  Feeding the canonical minimizer of the
window `W_j = (x+□_j) ∩ □_m` into the slope-defect inequality and dividing by
the cutoff mass gives the **one-scale defect bound**

```text
  |∇ℓ(u,W_j)_i − ∂_i u(x)|
      ≤ (8(d+1))^d · ( C_ibp(d)·K·√(3^j)
                       + ⨍_{B(x,3^j/2)} |∂_i u − ∂_i u(x)| ) ,
```

where the average is taken over the **sup-metric** ball, i.e. over the cube of
side `3^j` centred at `x`, and `∂_i u` is read through its zero extension off
`□_m`.  Both scale factors cancel exactly: `|W_j| ≤ (3^j)^d` and the cutoff mass
is at least `(3^j)^d/(8(d+1))^d`.

Letting `j = (m+1) − n` run to `−∞` kills the first term geometrically and the
second term at every **Lebesgue point** of the zero extension.  Since
`CubeSchauderPointwise.tendsto_windowSlope` sends `∇ℓ(u,W_j) → Ψ(x)`, the two
limits identify `Ψ(x)` with `∇u(x)` at almost every `x`, coordinate by
coordinate.

The Lebesgue points come from the Besicovitch Vitali family of the Lebesgue
measure on `Vec d = Fin d → ℝ`, whose closed balls *are* the sup-metric cubes;
the volume identity `|B(x,r)| = (2r)^d` is the product-measure formula.  No
doubling constant and no covering constant enter the statement: the sup-metric
ball is the window's own enclosing cube.

## Main results

* `exists_zpow_euclideanBall_subset` — the interior threshold `j₀(x)`.
* `gradIndicator` — the zero extension of `∂_i u` off `□_m`.
* `abs_windowSlope_sub_grad_le` — the one-scale defect bound.
* `ae_campanatoSlopeLimit_eq_grad` — **the residue `hae`**: at every `K ≥ 0`
  carrying the Campanato datum on all of `□_m`, the limit slope field agrees
  with the weak gradient almost everywhere.

## References

* ABK26.
-/

namespace Algsuperdiff.Section4.Provider.Schauder

open MeasureTheory Filter Topology
open HCPolySupport
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-! ## 1. The sup-metric ball -/

/-- The Euclidean ball sits inside the sup-metric ball of the same radius. -/
theorem euclideanBall_subset_ball (z : Vec d) {r : ℝ} (hr : 0 < r) :
    euclideanBall z r ⊆ Metric.ball z r := by
  intro y hy
  have hsq : euclideanSqDist y z < r ^ 2 := hy
  have hvn : vecNormSq (y - z) = euclideanSqDist y z := rfl
  have hnorm : ‖y - z‖ ≤ Real.sqrt (vecNormSq (y - z)) := norm_le_slopeMagnitude (y - z)
  have hlt : Real.sqrt (vecNormSq (y - z)) < r := by
    rw [hvn]
    exact (Real.sqrt_lt' hr).2 hsq
  rw [Metric.mem_ball, dist_eq_norm]
  exact lt_of_le_of_lt hnorm hlt

/-- **The interior threshold.**  Around a point of the open cube every
sufficiently small Euclidean ball stays inside the cube. -/
theorem exists_zpow_euclideanBall_subset {m : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) :
    ∃ j₀ : ℤ, ∀ j : ℤ, j ≤ j₀ →
      euclideanBall z ((3 : ℝ) ^ j / 2) ⊆ openCubeSet (originCube d m) := by
  obtain ⟨eps, heps, hball⟩ :=
    Metric.isOpen_iff.1 (HCPolySupport.isOpen_openCubeSet (originCube d m)) z hz
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one heps (by norm_num : (3 : ℝ)⁻¹ < 1)
  refine ⟨-(n : ℤ), fun j hj => ?_⟩
  have hjpos : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hmono : (3 : ℝ) ^ j ≤ (3 : ℝ) ^ (-(n : ℤ)) :=
    zpow_le_zpow_right₀ (by norm_num) hj
  have hid : (3 : ℝ) ^ (-(n : ℤ)) = ((3 : ℝ)⁻¹) ^ n := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  have hlt : (3 : ℝ) ^ j / 2 ≤ eps := by
    rw [hid] at hmono
    linarith only [hmono, hn, heps]
  refine subset_trans (euclideanBall_subset_ball z (by linarith only [hjpos])) ?_
  exact subset_trans (Metric.ball_subset_ball hlt) hball

/-- The truncated window sits inside the sup-metric closed ball of radius
`3^j/2`, i.e. inside the closed cube of side `3^j` about the base point. -/
theorem truncatedWindow_subset_closedBall (x : Vec d) (m j : ℤ) :
    truncatedWindow x m j ⊆ Metric.closedBall x ((3 : ℝ) ^ j / 2) := by
  intro y hy
  obtain ⟨p, hp, rfl⟩ := truncatedWindow_subset_translate x m j hy
  rw [Metric.mem_closedBall, dist_eq_norm, show x + p - x = p by abel]
  rw [mem_openCubeSet_originCube_iff] at hp
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have h := hp i
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith only [h.1], by linarith only [h.2]⟩

/-- The sup-metric closed ball has finite volume. -/
theorem volume_closedBall_ne_top (x : Vec d) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.closedBall x r) ≠ ⊤ := by
  rw [Real.volume_pi_closedBall x hr]
  exact ENNReal.ofReal_ne_top

/-- **The sup-metric ball's set integral in average form.**
`∫_{B(x,r)} f = (2r)^d · ⨍_{B(x,r)} f`. -/
theorem setIntegral_closedBall_eq_mul_setAverage (x : Vec d) {r : ℝ} (hr : 0 < r)
    (f : Vec d → ℝ) :
    ∫ y in Metric.closedBall x r, f y ∂volume
      = (2 * r) ^ d * ⨍ y in Metric.closedBall x r, f y ∂volume := by
  rw [setAverage_eq, smul_eq_mul, ← mul_assoc, measureReal_def,
    Real.volume_pi_closedBall x hr.le, Fintype.card_fin,
    ENNReal.toReal_ofReal (by positivity)]
  rw [mul_inv_cancel₀ (by positivity), one_mul]

/-! ## 2. The zero extension of the weak gradient -/

/-- The zero extension of the `i`-th coordinate of the weak gradient off `□_m`.
Extending is what makes the Lebesgue differentiation theorem — a statement about
globally integrable functions — available at every interior base point. -/
def gradIndicator (m : ℤ) (u : H1Function (openCubeSet (originCube d m))) (i : Fin d) :
    Vec d → ℝ :=
  Set.indicator (openCubeSet (originCube d m)) fun y => u.grad y i

theorem gradIndicator_of_mem {m : ℤ} {u : H1Function (openCubeSet (originCube d m))}
    {i : Fin d} {y : Vec d} (hy : y ∈ openCubeSet (originCube d m)) :
    gradIndicator m u i y = u.grad y i :=
  Set.indicator_of_mem hy _

theorem integrableOn_grad_apply {m : ℤ} (u : H1Function (openCubeSet (originCube d m)))
    (i : Fin d) :
    IntegrableOn (fun y => u.grad y i) (openCubeSet (originCube d m)) volume := by
  have hUdom : IsOpenBoundedConvexDomain (openCubeSet (originCube d m)) :=
    isOpenBoundedConvexDomain_openCubeSet _
  have : IsFiniteMeasure (volume.restrict (openCubeSet (originCube d m))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact hUdom.volume_lt_top
  have hgL2 : MemLp (fun y => u.grad y i) 2
      (volume.restrict (openCubeSet (originCube d m))) := by
    simpa only [volumeMeasureOn] using u.gradMemL2 i
  exact hgL2.integrable one_le_two

theorem integrable_gradIndicator {m : ℤ} (u : H1Function (openCubeSet (originCube d m)))
    (i : Fin d) : Integrable (gradIndicator m u i) volume :=
  (integrableOn_grad_apply u i).integrable_indicator (measurableSet_openCubeSet _)

/-- **The Lebesgue points of the extended gradient.**  At almost every point of
`Vec d` the sup-metric averages of `|∂_i u − ∂_i u(x)|` vanish, simultaneously in
every coordinate.  This is the Besicovitch Vitali family of the Lebesgue measure
on `Fin d → ℝ`, whose closed balls are the sup-metric cubes. -/
theorem ae_tendsto_setAverage_gradIndicator {m : ℤ}
    (u : H1Function (openCubeSet (originCube d m))) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ i : Fin d,
      Tendsto (fun r : ℝ => ⨍ y in Metric.closedBall x r,
          |gradIndicator m u i y - gradIndicator m u i x| ∂volume)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  rw [ae_all_iff]
  intro i
  have hf := integrable_gradIndicator u i
  filter_upwards [(Besicovitch.vitaliFamily (volume : Measure (Vec d))).ae_tendsto_average_norm_sub
    hf.locallyIntegrable] with x hx
  have h := hx.comp (Besicovitch.tendsto_filterAt (volume : Measure (Vec d)) x)
  refine h.congr fun r => ?_
  simp only [Function.comp_apply, Real.norm_eq_abs]

/-! ## 3. The one-scale defect bound -/

/-- The `d`-constant of the one-scale defect bound: the reciprocal of the cutoff
mass floor, normalized by the window volume. -/
def aeLimitConst (d : ℕ) : ℝ := (8 * ((d : ℝ) + 1)) ^ d

theorem aeLimitConst_pos (d : ℕ) : 0 < aeLimitConst d := by
  rw [aeLimitConst]
  positivity

/-- The final division of the one-scale bound: the window volume factor `P`
cancels and the reciprocal mass floor `Q` survives. -/
private theorem defect_divide {a P Q B : ℝ} (hP : 0 < P) (hQ : 0 < Q)
    (h : a * (P / Q) ≤ P * B) : a ≤ Q * B := by
  have hQ0 : Q ≠ 0 := ne_of_gt hQ
  have h' := mul_le_mul_of_nonneg_right h hQ.le
  have hid : a * (P / Q) * Q = a * P := by field_simp
  have hid2 : P * B * Q = Q * B * P := by ring
  have hkey : a * P ≤ Q * B * P := by linarith only [h', hid, hid2]
  exact le_of_mul_le_mul_right hkey hP

/-- The `1/d`-th power of a window volume bounded by `(3^j)^d` is at most
`3^j`. -/
theorem rpow_inv_le_zpow (hd : d ≠ 0) {j : ℤ} {V : ℝ} (hV : 0 ≤ V)
    (hle : V ≤ ((3 : ℝ) ^ j) ^ d) : V ^ ((d : ℝ)⁻¹) ≤ (3 : ℝ) ^ j := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) _
  have hexp : (0 : ℝ) ≤ (d : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg d)
  have hstep := Real.rpow_le_rpow hV hle hexp
  refine hstep.trans (le_of_eq ?_)
  rw [← Real.rpow_natCast ((3 : ℝ) ^ j) d, ← Real.rpow_mul h3.le,
    show (d : ℝ) * (d : ℝ)⁻¹ = 1 by field_simp [Nat.cast_ne_zero.2 hd], Real.rpow_one]

/-- **The one-scale defect bound.**

At an interior scale — one whose Euclidean ball of radius `3^j/2` still fits
inside `□_m` — the coordinate defect between the window slope and the pointwise
gradient value is controlled by the Campanato datum plus one sup-metric
oscillation average.  The window's own volume factor cancels against the cutoff
mass floor, leaving the pure `d`-constant `aeLimitConst d`. -/
theorem abs_windowSlope_sub_grad_le (hd : d ≠ 0) {m j : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hjm : j ≤ m + 1)
    (hsub : euclideanBall x ((3 : ℝ) ^ j / 2) ⊆ openCubeSet (originCube d m))
    (u : H1Function (openCubeSet (originCube d m))) {K : ℝ} (hK : 0 ≤ K)
    (hE : affineExcess (truncatedWindow x m j) u.toFun ≤ K * Real.sqrt ((3 : ℝ) ^ j))
    (i : Fin d) :
    |windowSlope m u.toFun x j i - u.grad x i|
      ≤ aeLimitConst d
        * (cutoffIbpConst d * K * Real.sqrt ((3 : ℝ) ^ j)
          + ⨍ y in Metric.closedBall x ((3 : ℝ) ^ j / 2),
              |gradIndicator m u i y - gradIndicator m u i x| ∂volume) := by
  have hjm' : j - 1 ≤ m := by omega
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hr : (0 : ℝ) < (3 : ℝ) ^ j / 2 := by linarith only [h3]
  have hUmeas : MeasurableSet (openCubeSet (originCube d m)) := measurableSet_openCubeSet _
  have hWU : truncatedWindow x m j ⊆ openCubeSet (originCube d m) :=
    truncatedWindow_subset_domain x m j
  have hWmeas : MeasurableSet (truncatedWindow x m j) := measurableSet_truncatedWindow x m j
  have hVpos : 0 < (volume (truncatedWindow x m j)).toReal :=
    volume_toReal_truncatedWindow_pos x hx hjm'
  have hVle : (volume (truncatedWindow x m j)).toReal ≤ ((3 : ℝ) ^ j) ^ d :=
    (volume_toReal_truncatedWindow_bounds x hx hjm').2
  -- the canonical minimizer of the window
  have huU : MemLp u.toFun 2 (volume.restrict (openCubeSet (originCube d m))) := by
    simpa only [volumeMeasureOn] using u.memL2
  have huW : MemLp u.toFun 2 (volume.restrict (truncatedWindow x m j)) :=
    huU.mono_measure (Measure.restrict_mono hWU le_rfl)
  have hmin := isAffineMinimizer_windowSlope hx hjm' huW
  -- the slope-defect inequality at the minimizer
  have hsplit := abs_slope_sub_le_cutoff_split hx hjm' hsub u
    (affineMinimizerPair (truncatedWindow x m j) u.toFun).1
    (windowSlope m u.toFun x j) (u.grad x) i
  -- the first right-hand term
  have hraw : affineDistOn (truncatedWindow x m j) u.toFun
      (affineMinimizerPair (truncatedWindow x m j) u.toFun).1 (windowSlope m u.toFun x j)
      = ((volume (truncatedWindow x m j)).toReal) ^ ((d : ℝ)⁻¹)
        * affineExcess (truncatedWindow x m j) u.toFun := by
    rw [hmin, affineExcessRaw_eq_rpow_mul_affineExcess hVpos]
  have hVd : ((volume (truncatedWindow x m j)).toReal) ^ ((d : ℝ)⁻¹) ≤ (3 : ℝ) ^ j :=
    rpow_inv_le_zpow hd hVpos.le hVle
  have hDle : affineDistOn (truncatedWindow x m j) u.toFun
      (affineMinimizerPair (truncatedWindow x m j) u.toFun).1 (windowSlope m u.toFun x j)
      ≤ (3 : ℝ) ^ j * (K * Real.sqrt ((3 : ℝ) ^ j)) := by
    rw [hraw]
    exact mul_le_mul hVd hE (affineExcess_nonneg _ _) h3.le
  have hprod : affineDistOn (truncatedWindow x m j) u.toFun
        (affineMinimizerPair (truncatedWindow x m j) u.toFun).1 (windowSlope m u.toFun x j)
        * (volume (truncatedWindow x m j)).toReal
      ≤ ((3 : ℝ) ^ j * (K * Real.sqrt ((3 : ℝ) ^ j))) * ((3 : ℝ) ^ j) ^ d :=
    mul_le_mul hDle hVle hVpos.le (by positivity)
  have hMnn : (0 : ℝ) ≤ cutoffIbpConst d * (3 : ℝ) ^ (-j) :=
    mul_nonneg (cutoffIbpConst_nonneg d) (zpow_pos (by norm_num) _).le
  have hterm1 : cutoffIbpConst d * (3 : ℝ) ^ (-j)
        * (affineDistOn (truncatedWindow x m j) u.toFun
            (affineMinimizerPair (truncatedWindow x m j) u.toFun).1
            (windowSlope m u.toFun x j)
          * (volume (truncatedWindow x m j)).toReal)
      ≤ (cutoffIbpConst d * K * Real.sqrt ((3 : ℝ) ^ j)) * ((3 : ℝ) ^ j) ^ d := by
    refine (mul_le_mul_of_nonneg_left hprod hMnn).trans (le_of_eq ?_)
    rw [zpow_neg]
    field_simp
  -- the second right-hand term
  have hfint : Integrable (gradIndicator m u i) volume := integrable_gradIndicator u i
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall x ((3 : ℝ) ^ j / 2))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 (volume_closedBall_ne_top x hr.le)
  have hballint : IntegrableOn
      (fun y => |gradIndicator m u i y - gradIndicator m u i x|)
      (Metric.closedBall x ((3 : ℝ) ^ j / 2)) volume :=
    ((hfint.integrableOn).sub (integrable_const _)).abs
  have hcongr : ∫ y in truncatedWindow x m j, |u.grad y i - u.grad x i| ∂volume
      = ∫ y in truncatedWindow x m j,
          |gradIndicator m u i y - gradIndicator m u i x| ∂volume := by
    refine setIntegral_congr_fun hWmeas fun y hy => ?_
    rw [gradIndicator_of_mem (hWU hy), gradIndicator_of_mem hx]
  have hmonoset : ∫ y in truncatedWindow x m j,
        |gradIndicator m u i y - gradIndicator m u i x| ∂volume
      ≤ ∫ y in Metric.closedBall x ((3 : ℝ) ^ j / 2),
        |gradIndicator m u i y - gradIndicator m u i x| ∂volume :=
    setIntegral_mono_set hballint (Eventually.of_forall fun y => abs_nonneg _)
      (LE.le.eventuallyLE (truncatedWindow_subset_closedBall x m j))
  have havg : ∫ y in Metric.closedBall x ((3 : ℝ) ^ j / 2),
        |gradIndicator m u i y - gradIndicator m u i x| ∂volume
      = ((3 : ℝ) ^ j) ^ d
        * ⨍ y in Metric.closedBall x ((3 : ℝ) ^ j / 2),
            |gradIndicator m u i y - gradIndicator m u i x| ∂volume := by
    rw [setIntegral_closedBall_eq_mul_setAverage x hr]
    congr 2
    ring
  -- the cutoff mass floor
  have hmass := integral_campanatoCutoff_ge (m := m) (j := j) (z := x) hsub
  have hmassid : ((3 : ℝ) ^ j / (8 * ((d : ℝ) + 1))) ^ d
      = ((3 : ℝ) ^ j) ^ d / aeLimitConst d := by
    rw [aeLimitConst, div_pow]
  -- assemble
  refine defect_divide (P := ((3 : ℝ) ^ j) ^ d) (by positivity) (aeLimitConst_pos d) ?_
  have hlow : |windowSlope m u.toFun x j i - u.grad x i|
        * (((3 : ℝ) ^ j) ^ d / aeLimitConst d)
      ≤ |windowSlope m u.toFun x j i - u.grad x i|
        * ∫ y in openCubeSet (originCube d m), campanatoCutoff x j y ∂volume := by
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [← hmassid]
    exact hmass
  have h2 : ∫ y in truncatedWindow x m j, |u.grad y i - u.grad x i| ∂volume
      ≤ ((3 : ℝ) ^ j) ^ d
        * ⨍ y in Metric.closedBall x ((3 : ℝ) ^ j / 2),
            |gradIndicator m u i y - gradIndicator m u i x| ∂volume := by
    rw [hcongr, ← havg]
    exact hmonoset
  have hexp : ((3 : ℝ) ^ j) ^ d
      * (cutoffIbpConst d * K * Real.sqrt ((3 : ℝ) ^ j)
        + ⨍ y in Metric.closedBall x ((3 : ℝ) ^ j / 2),
            |gradIndicator m u i y - gradIndicator m u i x| ∂volume)
      = cutoffIbpConst d * K * Real.sqrt ((3 : ℝ) ^ j) * ((3 : ℝ) ^ j) ^ d
        + ((3 : ℝ) ^ j) ^ d
          * ⨍ y in Metric.closedBall x ((3 : ℝ) ^ j / 2),
              |gradIndicator m u i y - gradIndicator m u i x| ∂volume := by ring
  linarith only [hlow, hsplit, hterm1, h2, hexp]

/-! ## 4. The limit -/

/-- The triadic scale sequence `3^{T−n}` tends to `0`. -/
theorem tendsto_zpow_sub_natCast_zero (T : ℤ) :
    Tendsto (fun n : ℕ => (3 : ℝ) ^ (T - (n : ℤ))) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (3 : ℝ) ^ T * (3 : ℝ)⁻¹ ^ n) atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
      (r := (3 : ℝ)⁻¹) (by norm_num) (by norm_num)
    simpa using hp.const_mul ((3 : ℝ) ^ T)
  refine h.congr fun n => ?_
  rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast, inv_pow]
  ring

/-- The triadic radius sequence tends to `0` from the right. -/
theorem tendsto_zpow_half_nhdsWithin_zero (T : ℤ) :
    Tendsto (fun n : ℕ => (3 : ℝ) ^ (T - (n : ℤ)) / 2) atTop (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
    (Eventually.of_forall fun n => ?_)
  · have h := (tendsto_zpow_sub_natCast_zero T).div_const 2
    simpa using h
  · have h := zpow_pos (by norm_num : (0 : ℝ) < 3) (T - (n : ℤ))
    exact Set.mem_Ioi.2 (by linarith only [h])

/-- **The a.e. identification `Ψ = ∇u`.**

Off the Campanato datum on **all** of `□_m` — the residue `hE` of
`CubeSchauderAssembly` — the limit slope field of the Campanato iteration agrees
with the weak gradient of `u` almost everywhere on the cube.  This is the second
named residue `hae` of `zeroDatumCubeSchauder_of_residues`, discharged. -/
theorem ae_campanatoSlopeLimit_eq_grad (hd : 0 < d) {m : ℤ}
    (u : H1Function (openCubeSet (originCube d m))) {K : ℝ} (hK : 0 ≤ K)
    (hE : ∀ z ∈ openCubeSet (originCube d m), ∀ j : ℤ, j ≤ m + 1 →
      affineExcess (truncatedWindow z m j) u.toFun ≤ K * Real.sqrt ((3 : ℝ) ^ j)) :
    ∀ᵐ y ∂(volume.restrict (openCubeSet (originCube d m))),
      campanatoSlopeLimit m (m + 1) u.toFun y = u.grad y := by
  have hdne : d ≠ 0 := by omega
  have hUmeas : MeasurableSet (openCubeSet (originCube d m)) := measurableSet_openCubeSet _
  have huU : MemLp u.toFun 2 (volume.restrict (openCubeSet (originCube d m))) := by
    simpa only [volumeMeasureOn] using u.memL2
  filter_upwards [ae_restrict_of_ae (ae_tendsto_setAverage_gradIndicator u),
    self_mem_ae_restrict hUmeas] with x hxleb hxU
  funext i
  obtain ⟨j0, hj0⟩ := exists_zpow_euclideanBall_subset hxU
  -- the slope sequence converges to the limit field
  have hslope := tendsto_windowSlope (u := u.toFun) hd hxU (le_refl (m + 1)) huU hK
    (hE x hxU)
  have hi : Tendsto (fun n : ℕ => windowSlope m u.toFun x (m + 1 - (n : ℤ)) i) atTop
      (𝓝 (campanatoSlopeLimit m (m + 1) u.toFun x i)) := tendsto_pi_nhds.mp hslope i
  have habs : Tendsto
      (fun n : ℕ => |windowSlope m u.toFun x (m + 1 - (n : ℤ)) i - u.grad x i|) atTop
      (𝓝 |campanatoSlopeLimit m (m + 1) u.toFun x i - u.grad x i|) :=
    (hi.sub_const _).abs
  -- the majorant converges to zero
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt ((3 : ℝ) ^ (m + 1 - (n : ℤ)))) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp (tendsto_zpow_sub_natCast_zero (m + 1))
    simpa using! h
  have havg : Tendsto (fun n : ℕ => ⨍ y in Metric.closedBall x ((3 : ℝ) ^ (m + 1 - (n : ℤ)) / 2),
      |gradIndicator m u i y - gradIndicator m u i x| ∂volume) atTop (𝓝 0) := by
    have h := (hxleb i).comp (tendsto_zpow_half_nhdsWithin_zero (m + 1))
    simpa [Function.comp_def] using h
  have hmaj : Tendsto (fun n : ℕ => aeLimitConst d
      * (cutoffIbpConst d * K * Real.sqrt ((3 : ℝ) ^ (m + 1 - (n : ℤ)))
        + ⨍ y in Metric.closedBall x ((3 : ℝ) ^ (m + 1 - (n : ℤ)) / 2),
            |gradIndicator m u i y - gradIndicator m u i x| ∂volume)) atTop (𝓝 0) := by
    have h := ((hsqrt.const_mul (cutoffIbpConst d * K)).add havg).const_mul (aeLimitConst d)
    simpa using h
  -- the eventual comparison
  have hev : (fun n : ℕ => |windowSlope m u.toFun x (m + 1 - (n : ℤ)) i - u.grad x i|)
      ≤ᶠ[atTop] fun n : ℕ => aeLimitConst d
        * (cutoffIbpConst d * K * Real.sqrt ((3 : ℝ) ^ (m + 1 - (n : ℤ)))
          + ⨍ y in Metric.closedBall x ((3 : ℝ) ^ (m + 1 - (n : ℤ)) / 2),
              |gradIndicator m u i y - gradIndicator m u i x| ∂volume) := by
    refine eventually_atTop.2 ⟨(m + 1 - j0).toNat, fun n hn => ?_⟩
    have hnj : m + 1 - (n : ℤ) ≤ j0 := by
      have hcast : (m + 1 - j0) ≤ (n : ℤ) := by
        have h := Int.toNat_le.1 hn
        omega
      omega
    exact abs_windowSlope_sub_grad_le hdne hxU (by omega) (hj0 _ hnj) u hK
      (hE x hxU _ (by omega)) i
  have hle : |campanatoSlopeLimit m (m + 1) u.toFun x i - u.grad x i| ≤ 0 :=
    le_of_tendsto_of_tendsto habs hmaj hev
  have hzero : campanatoSlopeLimit m (m + 1) u.toFun x i - u.grad x i = 0 :=
    abs_eq_zero.1 (le_antisymm hle (abs_nonneg _))
  linarith only [hzero]

end

end Algsuperdiff.Section4.Provider.Schauder
