/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.ScaleSelection
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Arithmetic geometry of the multiscale cells

This file develops the data-only part of Sections 3.2-3.3 from an already chosen
`ScaleFamily`.  The core scale is `ell n`, the reserved buffer radius is
`R n = sqrt (ell n)`, and the added axial amplitude is chosen so that the
selected Fourier mode receives one fixed spectral translation.

Only consequences of `ScaleFamily` are proved here.  In particular there is
no global velocity, cutoff, parametrix, or spectral-transfer assertion.  The
results below give the exact identities and geometric estimates those later
layers may use: geometric decay and summability, asymptotic separation of
core and buffer scales, summable-tail cell centres, pairwise buffer
separation, a packing criterion, and diffusivity-dependent matching wrappers.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter Set
open scoped Topology

namespace ScaleFamily

variable {p : LocalSeedParameters} {r : ScaleRatios p}

/-! ## Core and buffer scales -/

/-- Reserved transverse radius of the `n`th cell: `R_n = sqrt (ell_n)`. -/
def bufferRadius (f : ScaleFamily r) (n : ℕ) : ℝ :=
  Real.sqrt (f.ell n)

/-- The reserved radius `R_n = sqrt (ell_n)` is strictly positive. -/
theorem bufferRadius_pos (f : ScaleFamily r) (n : ℕ) :
    0 < f.bufferRadius n :=
  Real.sqrt_pos.2 (f.ell_pos n)

/-- Nonnegativity of the reserved radius `R_n`, the form needed for square-root manipulations. -/
theorem bufferRadius_nonneg (f : ScaleFamily r) (n : ℕ) :
    0 ≤ f.bufferRadius n :=
  (f.bufferRadius_pos n).le

/-- The square-root choice gives the exact relation `R_n^2 = ell_n`. -/
theorem bufferRadius_sq (f : ScaleFamily r) (n : ℕ) :
    f.bufferRadius n ^ 2 = f.ell n := by
  exact Real.sq_sqrt (f.ell_pos n).le

/-- Closed form of the reserved radius in terms of the rounded frequency:
`R_n = sqrt (k_* / K_n)`. -/
@[simp] theorem bufferRadius_formula (f : ScaleFamily r) (n : ℕ) :
    f.bufferRadius n =
      Real.sqrt ((p.kStar : ℝ) / f.fourierIndex n) := by
  rfl

/-- The base reserved radius is `R_0 = sqrt (k_* / K_0)`, so it is governed by the base index
`K_0` alone. -/
theorem bufferRadius_zero_formula (f : ScaleFamily r) :
    f.bufferRadius 0 = Real.sqrt ((p.kStar : ℝ) / f.K0) := by
  rfl

/-- Every reserved radius is at most the base radius `R_0`, so `R_0` bounds the whole family. -/
theorem bufferRadius_le_bufferRadius_zero (f : ScaleFamily r) (n : ℕ) :
    f.bufferRadius n ≤ f.bufferRadius 0 := by
  exact Real.sqrt_le_sqrt (f.ell_le_ell_zero n)

/-- The exact one-step contraction available from the lower adjacent
frequency ratio. -/
theorem ell_succ_le (f : ScaleFamily r) (n : ℕ) :
    f.ell (n + 1) ≤ r.q⁻¹ * f.ell n := by
  have hKn : 0 < (f.fourierIndex n : ℝ) :=
    Nat.cast_pos.2 (f.fourierIndex_pos n)
  have hKnext : 0 < (f.fourierIndex (n + 1) : ℝ) :=
    Nat.cast_pos.2 (f.fourierIndex_pos (n + 1))
  have hstep : r.q * (f.fourierIndex n : ℝ) ≤
      (f.fourierIndex (n + 1) : ℝ) :=
    (le_div_iff₀ hKn).mp (f.adjacent_ratio_lower n)
  unfold ell
  calc
    (p.kStar : ℝ) / (f.fourierIndex (n + 1) : ℝ) ≤
        (p.kStar : ℝ) / (r.q * (f.fourierIndex n : ℝ)) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _)
        (mul_pos r.q_pos hKn) hstep
    _ = r.q⁻¹ * ((p.kStar : ℝ) / (f.fourierIndex n : ℝ)) := by
      field_simp [ne_of_gt r.q_pos, ne_of_gt hKn, ne_of_gt hKnext]

/-- Contraction factor for the buffer radii. -/
def bufferContraction (_f : ScaleFamily r) : ℝ :=
  Real.sqrt r.q⁻¹

/-- The buffer contraction factor `sqrt (q⁻¹)` is strictly positive. -/
theorem bufferContraction_pos (f : ScaleFamily r) :
    0 < f.bufferContraction := by
  exact Real.sqrt_pos.2 (inv_pos.2 r.q_pos)

/-- Nonnegativity of the buffer contraction factor `sqrt (q⁻¹)`. -/
theorem bufferContraction_nonneg (f : ScaleFamily r) :
    0 ≤ f.bufferContraction :=
  f.bufferContraction_pos.le

/-- The buffer contraction factor is `< 1`, because the frequency ratio satisfies `q > 1`;
this is what makes the reserved radii geometrically decaying and summable. -/
theorem bufferContraction_lt_one (f : ScaleFamily r) :
    f.bufferContraction < 1 := by
  rw [bufferContraction, ← Real.sqrt_one]
  exact Real.sqrt_lt_sqrt (inv_nonneg.mpr r.q_pos.le)
    (inv_lt_one_of_one_lt₀ r.one_lt_q)

/-- One-step contraction of the reserved radii: `R_(n+1) ≤ sqrt (q⁻¹) * R_n`. -/
theorem bufferRadius_succ_le (f : ScaleFamily r) (n : ℕ) :
    f.bufferRadius (n + 1) ≤
      f.bufferContraction * f.bufferRadius n := by
  calc
    f.bufferRadius (n + 1) = Real.sqrt (f.ell (n + 1)) := rfl
    _ ≤ Real.sqrt (r.q⁻¹ * f.ell n) :=
      Real.sqrt_le_sqrt (f.ell_succ_le n)
    _ = Real.sqrt r.q⁻¹ * Real.sqrt (f.ell n) := by
      rw [Real.sqrt_mul (inv_nonneg.mpr r.q_pos.le)]
    _ = f.bufferContraction * f.bufferRadius n := rfl

/-- The reserved radii strictly decrease from one cell to the next. -/
theorem bufferRadius_succ_lt (f : ScaleFamily r) (n : ℕ) :
    f.bufferRadius (n + 1) < f.bufferRadius n := by
  apply (f.bufferRadius_succ_le n).trans_lt
  nlinarith [f.bufferContraction_lt_one,
    f.bufferContraction_nonneg, f.bufferRadius_pos n]

/-- The reserved radius `R` is strictly decreasing in the cell index. -/
theorem strictAnti_bufferRadius (f : ScaleFamily r) :
    StrictAnti f.bufferRadius :=
  strictAnti_nat_of_succ_lt f.bufferRadius_succ_lt

/-- Monotone (antitone) form of the decrease of the reserved radii, for use with index
comparisons. -/
theorem antitone_bufferRadius (f : ScaleFamily r) :
    Antitone f.bufferRadius :=
  f.strictAnti_bufferRadius.antitone

/-- Explicit geometric majorant for every buffer radius. -/
theorem bufferRadius_geometric_bound (f : ScaleFamily r) (n : ℕ) :
    f.bufferRadius n ≤
      f.bufferRadius 0 * f.bufferContraction ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        f.bufferRadius (n + 1) ≤
            f.bufferContraction * f.bufferRadius n :=
          f.bufferRadius_succ_le n
        _ ≤ f.bufferContraction *
            (f.bufferRadius 0 * f.bufferContraction ^ n) :=
          mul_le_mul_of_nonneg_left ih f.bufferContraction_nonneg
        _ = f.bufferRadius 0 * f.bufferContraction ^ (n + 1) := by
          rw [pow_succ]
          ring

/-- The buffer radii form a summable sequence. -/
theorem summable_bufferRadius (f : ScaleFamily r) :
    Summable f.bufferRadius := by
  apply summable_of_ratio_norm_eventually_le f.bufferContraction_lt_one
  filter_upwards [] with n
  simpa only [Real.norm_eq_abs,
    abs_of_pos (f.bufferRadius_pos (n + 1)),
    abs_of_pos (f.bufferRadius_pos n)] using f.bufferRadius_succ_le n

/-- The core scales themselves are summable as well. -/
theorem summable_ell (f : ScaleFamily r) : Summable f.ell := by
  apply summable_of_ratio_norm_eventually_le
    (inv_lt_one_of_one_lt₀ r.one_lt_q)
  filter_upwards [] with n
  simpa only [Real.norm_eq_abs, abs_of_pos (f.ell_pos (n + 1)),
    abs_of_pos (f.ell_pos n)] using f.ell_succ_le n

/-- The reserved radii tend to `0`, a consequence of their summability. -/
theorem tendsto_bufferRadius_zero (f : ScaleFamily r) :
    Tendsto f.bufferRadius atTop (𝓝 0) :=
  f.summable_bufferRadius.tendsto_atTop_zero

/-- The geometric-series upper bound for the total reserved radius. -/
theorem tsum_bufferRadius_le (f : ScaleFamily r) :
    (∑' n : ℕ, f.bufferRadius n) ≤
      f.bufferRadius 0 / (1 - f.bufferContraction) := by
  have hcNorm : ‖f.bufferContraction‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg f.bufferContraction_nonneg] using
      f.bufferContraction_lt_one
  have hpow : Summable (fun n : ℕ ↦ f.bufferContraction ^ n) :=
    summable_geometric_of_norm_lt_one hcNorm
  have hmajor : Summable
      (fun n : ℕ ↦ f.bufferRadius 0 * f.bufferContraction ^ n) :=
    hpow.mul_left _
  calc
    (∑' n : ℕ, f.bufferRadius n) ≤
        ∑' n : ℕ, f.bufferRadius 0 * f.bufferContraction ^ n :=
      f.summable_bufferRadius.tsum_le_tsum
        f.bufferRadius_geometric_bound hmajor
    _ = f.bufferRadius 0 *
        (∑' n : ℕ, f.bufferContraction ^ n) :=
      hpow.tsum_mul_left _
    _ = f.bufferRadius 0 * (1 - f.bufferContraction)⁻¹ := by
      rw [tsum_geometric_of_norm_lt_one hcNorm]
    _ = f.bufferRadius 0 / (1 - f.bufferContraction) := by
      rw [div_eq_mul_inv]

/-- The core-to-buffer ratio is exactly the buffer radius. -/
theorem ell_div_bufferRadius (f : ScaleFamily r) (n : ℕ) :
    f.ell n / f.bufferRadius n = f.bufferRadius n := by
  apply (div_eq_iff (ne_of_gt (f.bufferRadius_pos n))).2
  rw [← f.bufferRadius_sq n]
  ring

/-- Equivalently, the buffer-to-core ratio is the reciprocal buffer radius. -/
theorem bufferRadius_div_ell (f : ScaleFamily r) (n : ℕ) :
    f.bufferRadius n / f.ell n = (f.bufferRadius n)⁻¹ := by
  rw [← f.bufferRadius_sq n]
  field_simp [ne_of_gt (f.bufferRadius_pos n)]

/-- The reserved buffer becomes asymptotically much wider than the rescaled
local-flow core. -/
theorem tendsto_bufferRadius_div_ell_atTop (f : ScaleFamily r) :
    Tendsto (fun n ↦ f.bufferRadius n / f.ell n) atTop atTop := by
  have hwithin : Tendsto f.bufferRadius atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2
      ⟨f.tendsto_bufferRadius_zero,
        Eventually.of_forall fun n ↦ f.bufferRadius_pos n⟩
  apply hwithin.inv_tendsto_nhdsGT_zero.congr'
  exact Eventually.of_forall fun n ↦
    (f.bufferRadius_div_ell n).symm

/-! ## Added axial amplitudes -/

/-- Added axial speed in the `n`th cell.  Defining it through the already
proved wavenumber identity makes its scaling with `ell_n` transparent. -/
def axialAmplitude (f : ScaleFamily r) (tau : ℝ) (n : ℕ) : ℝ :=
  (tau / p.wavenumber) * f.ell n

/-- The formula of the paper, `a_n = tau / (2 pi K_n)`. -/
theorem axialAmplitude_formula (f : ScaleFamily r) (tau : ℝ) (n : ℕ) :
    f.axialAmplitude tau n =
      tau / (2 * Real.pi * (f.fourierIndex n : ℝ)) := by
  have hdenom : 2 * Real.pi * (f.fourierIndex n : ℝ) ≠ 0 := by
    exact ne_of_gt (mul_pos (mul_pos (by norm_num) Real.pi_pos)
      (Nat.cast_pos.2 (f.fourierIndex_pos n)))
  apply (eq_div_iff hdenom).2
  calc
    f.axialAmplitude tau n *
        (2 * Real.pi * (f.fourierIndex n : ℝ)) =
        (2 * Real.pi * (f.fourierIndex n : ℝ)) *
          f.axialAmplitude tau n := by ring
    _ = tau := by
      unfold axialAmplitude
      calc
        (2 * Real.pi * (f.fourierIndex n : ℝ)) *
            ((tau / p.wavenumber) * f.ell n) =
            (tau / p.wavenumber) *
              (2 * Real.pi * (f.fourierIndex n : ℝ) * f.ell n) := by
          ring
        _ = (tau / p.wavenumber) * p.wavenumber := by
          rw [f.axial_wavenumber_match n]
        _ = tau := div_mul_cancel₀ tau p.wavenumber_ne_zero

/-- The added axial speed produces the exact fixed spectral shift `tau`. -/
theorem axialAmplitude_match (f : ScaleFamily r) (tau : ℝ) (n : ℕ) :
    2 * Real.pi * (f.fourierIndex n : ℝ) *
      f.axialAmplitude tau n = tau := by
  rw [f.axialAmplitude_formula tau n]
  field_simp [ne_of_gt Real.pi_pos,
    ne_of_gt (Nat.cast_pos.2 (f.fourierIndex_pos n))]

/-- For a positive shift parameter `tau` every added axial amplitude `a_n` is positive; this is
the hypothesis under which the global velocity is nonzero. -/
theorem axialAmplitude_pos (f : ScaleFamily r) {tau : ℝ} (htau : 0 < tau)
    (n : ℕ) : 0 < f.axialAmplitude tau n := by
  exact mul_pos (div_pos htau p.wavenumber_pos) (f.ell_pos n)

/-- The added axial amplitudes `a_n = (tau / N) * ell_n` are summable, being a constant multiple
of the summable core scales. -/
theorem summable_axialAmplitude (f : ScaleFamily r) (tau : ℝ) :
    Summable (f.axialAmplitude tau) := by
  unfold axialAmplitude
  exact f.summable_ell.mul_left _

/-- Scale of the derivative created by cutting off the added axial velocity
across the buffer radius. -/
def axialGradientScale (f : ScaleFamily r) (tau : ℝ) (n : ℕ) : ℝ :=
  f.axialAmplitude tau n / f.bufferRadius n

/-- Closed form of the cutoff gradient scale: `a_n / R_n = (tau / N) * R_n`, the paper's
quantity `tau / (2 pi sqrt (k_* K_n))` (the display defining `eta_ax` after `eq:axial-offset`
reads `tau / (2 pi sqrt K_n)`: the Lean keeps `k_*` as a parameter, the
paper has `ell_n = 1 / K_n`, i.e. `k_* = 1`). -/
theorem axialGradientScale_formula (f : ScaleFamily r)
    (tau : ℝ) (n : ℕ) :
    f.axialGradientScale tau n =
      (tau / p.wavenumber) * f.bufferRadius n := by
  unfold axialGradientScale axialAmplitude
  calc
    ((tau / p.wavenumber) * f.ell n) / f.bufferRadius n =
        (tau / p.wavenumber) *
          (f.ell n / f.bufferRadius n) := by ring
    _ = (tau / p.wavenumber) * f.bufferRadius n := by
      rw [f.ell_div_bufferRadius n]

/-- For `0 ≤ tau` the cutoff gradient scale `a_n / R_n` is largest at `n = 0`, so the base cell
realises the paper's supremum `eta_ax` (the display after `eq:axial-offset`). -/
theorem axialGradientScale_le_zero (f : ScaleFamily r)
    {tau : ℝ} (htau : 0 ≤ tau) (n : ℕ) :
    f.axialGradientScale tau n ≤ f.axialGradientScale tau 0 := by
  rw [f.axialGradientScale_formula tau n,
    f.axialGradientScale_formula tau 0]
  exact mul_le_mul_of_nonneg_left (f.bufferRadius_le_bufferRadius_zero n)
    (div_nonneg htau p.wavenumber_pos.le)

/-- The cutoff gradient scales are summable, being a constant multiple of the reserved radii. -/
theorem summable_axialGradientScale (f : ScaleFamily r) (tau : ℝ) :
    Summable (f.axialGradientScale tau) := by
  rw [show f.axialGradientScale tau =
      fun n ↦ (tau / p.wavenumber) * f.bufferRadius n by
    funext n
    exact f.axialGradientScale_formula tau n]
  exact f.summable_bufferRadius.mul_left _

/-! ## Summable-tail placement and separation -/

/-- Tail of the reserved radii beginning with the `n`th cell. -/
def bufferTail (f : ScaleFamily r) (n : ℕ) : ℝ :=
  ∑' m : ℕ, f.bufferRadius (m + n)

/-- The tail sum of reserved radii from cell `n` onwards is nonnegative. -/
theorem bufferTail_nonneg (f : ScaleFamily r) (n : ℕ) :
    0 ≤ f.bufferTail n := by
  exact tsum_nonneg fun m ↦ f.bufferRadius_nonneg (m + n)

/-- The reserved-radius tails satisfy `T_n = R_n + T_(n+1)`, which is what makes the centres
`p_n = (4 T_n, 1/2)` separated by exactly `4 R_n`. -/
theorem bufferTail_recursion (f : ScaleFamily r) (n : ℕ) :
    f.bufferTail n = f.bufferRadius n + f.bufferTail (n + 1) := by
  have htail : Summable (fun m : ℕ ↦ f.bufferRadius (m + n)) :=
    (summable_nat_add_iff n).2 f.summable_bufferRadius
  unfold bufferTail
  calc
    (∑' m : ℕ, f.bufferRadius (m + n)) =
        f.bufferRadius (0 + n) +
          ∑' m : ℕ, f.bufferRadius ((m + 1) + n) :=
      htail.tsum_eq_zero_add
    _ = f.bufferRadius n +
        ∑' m : ℕ, f.bufferRadius (m + (n + 1)) := by
      simp only [zero_add]
      congr 1
      apply tsum_congr
      intro m
      congr 1
      omega

/-- First coordinate of the paper's centre
`p_n = (4 * sum_{m >= n} R_m, 1/2)`. -/
def cellCenterCoordinate (f : ScaleFamily r) (n : ℕ) : ℝ :=
  4 * f.bufferTail n

/-- Arithmetic centre in the fixed coordinate chart.  A later manifold layer
may map this pair into the transverse torus. -/
def cellCenter (f : ScaleFamily r) (n : ℕ) : ℝ × ℝ :=
  (f.cellCenterCoordinate n, 1 / 2)

/-- The first coordinate of the cell centre is the summable-tail coordinate `4 * T_n`. -/
@[simp] theorem cellCenter_fst (f : ScaleFamily r) (n : ℕ) :
    (f.cellCenter n).1 = f.cellCenterCoordinate n := rfl

/-- All cell centres lie on the horizontal line of height `1 / 2` in the chart. -/
@[simp] theorem cellCenter_snd (f : ScaleFamily r) (n : ℕ) :
    (f.cellCenter n).2 = 1 / 2 := rfl

/-- Adjacent centres are separated by exactly `4 R_n`. -/
theorem cellCenterCoordinate_recursion (f : ScaleFamily r) (n : ℕ) :
    f.cellCenterCoordinate n =
      4 * f.bufferRadius n + f.cellCenterCoordinate (n + 1) := by
  rw [cellCenterCoordinate, f.bufferTail_recursion n,
    cellCenterCoordinate]
  ring

/-- The centre coordinates strictly decrease, so the cells are laid out in index order along the
centre line. -/
theorem strictAnti_cellCenterCoordinate (f : ScaleFamily r) :
    StrictAnti f.cellCenterCoordinate := by
  apply strictAnti_nat_of_succ_lt
  intro n
  rw [f.cellCenterCoordinate_recursion n]
  nlinarith [f.bufferRadius_pos n]

/-- Monotone (antitone) form of the decrease of the centre coordinates. -/
theorem antitone_cellCenterCoordinate (f : ScaleFamily r) :
    Antitone f.cellCenterCoordinate :=
  f.strictAnti_cellCenterCoordinate.antitone

/-- The reserved-radius tails tend to `0`, so the cells accumulate at the chart origin. -/
theorem tendsto_bufferTail_zero (f : ScaleFamily r) :
    Tendsto f.bufferTail atTop (𝓝 0) := by
  change Tendsto (fun i ↦ ∑' k : ℕ, f.bufferRadius (k + i))
    atTop (𝓝 0)
  exact tendsto_sum_nat_add f.bufferRadius

/-- The cell centres converge to the origin of the centre line as the index grows. -/
theorem tendsto_cellCenterCoordinate_zero (f : ScaleFamily r) :
    Tendsto f.cellCenterCoordinate atTop (𝓝 0) := by
  change Tendsto (fun n ↦ 4 * f.bufferTail n) atTop (𝓝 0)
  simpa only [mul_zero] using
    tendsto_const_nhds.mul f.tendsto_bufferTail_zero

/-- Every two distinct buffer intervals on the centre line are strictly
separated.  This is the scalar inequality used to prove disjointness of the
corresponding Euclidean discs. -/
theorem bufferRadii_sum_lt_centerCoordinate_gap (f : ScaleFamily r)
    {n m : ℕ} (hnm : n < m) :
    f.bufferRadius n + f.bufferRadius m <
      |f.cellCenterCoordinate n - f.cellCenterCoordinate m| := by
  have hcentres : f.cellCenterCoordinate m < f.cellCenterCoordinate n :=
    f.strictAnti_cellCenterCoordinate hnm
  rw [abs_of_pos (sub_pos.mpr hcentres)]
  have hsucc_le_m : n + 1 ≤ m := hnm
  have htailOrder : f.cellCenterCoordinate m ≤
      f.cellCenterCoordinate (n + 1) :=
    f.antitone_cellCenterCoordinate hsucc_le_m
  have hgap : 4 * f.bufferRadius n ≤
      f.cellCenterCoordinate n - f.cellCenterCoordinate m := by
    rw [f.cellCenterCoordinate_recursion n]
    linarith
  have hradius : f.bufferRadius m ≤ f.bufferRadius n :=
    f.antitone_bufferRadius hnm.le
  calc
    f.bufferRadius n + f.bufferRadius m ≤ 2 * f.bufferRadius n := by
      linarith
    _ < 4 * f.bufferRadius n := by
      linarith [f.bufferRadius_pos n]
    _ ≤ f.cellCenterCoordinate n - f.cellCenterCoordinate m := hgap

/-- Quantity appearing on the left of the paper's chart-packing
condition. -/
def chartPackingQuantity (f : ScaleFamily r) : ℝ :=
  4 * (∑' n : ℕ, f.bufferRadius n) + f.bufferRadius 0

/-- A checkable geometric-series upper bound for chart packing. -/
theorem chartPackingQuantity_le (f : ScaleFamily r) :
    f.chartPackingQuantity ≤
      4 * (f.bufferRadius 0 / (1 - f.bufferContraction)) +
        f.bufferRadius 0 := by
  unfold chartPackingQuantity
  gcongr
  exact f.tsum_bufferRadius_le

/-- Once the geometric majorant is below `1/4`, the exact packing quantity
is below `1/4` as well.  This keeps the final large-`K0` choice as an explicit
downstream numerical obligation. -/
theorem chartPacking_of_geometric_bound (f : ScaleFamily r)
    (hbound :
      4 * (f.bufferRadius 0 / (1 - f.bufferContraction)) +
          f.bufferRadius 0 < 1 / 4) :
    f.chartPackingQuantity < 1 / 4 :=
  f.chartPackingQuantity_le.trans_lt hbound

/-- A support radius times every local core scale fits in one tenth of its
buffer whenever it does so under the worst-case radius `R_0`. -/
theorem supportScale_lt_tenth_buffer (f : ScaleFamily r)
    {supportRadius : ℝ} (hsupport : 0 ≤ supportRadius)
    (hsmall : 10 * supportRadius * f.bufferRadius 0 < 1) (n : ℕ) :
    supportRadius * f.ell n < f.bufferRadius n / 10 := by
  have hRn0 := f.bufferRadius_le_bufferRadius_zero n
  have hscaled : 10 * supportRadius * f.bufferRadius n < 1 := by
    calc
      10 * supportRadius * f.bufferRadius n ≤
          10 * supportRadius * f.bufferRadius 0 := by
        gcongr
      _ < 1 := hsmall
  have hRpos := f.bufferRadius_pos n
  have hscaled_mul := mul_lt_mul_of_pos_right hscaled hRpos
  rw [← f.bufferRadius_sq n]
  nlinarith [hscaled_mul]

/-! ## Diffusivity-dependent matching wrappers -/

/-- Physical diffusivity after rescaling to the `n`th local cell. -/
def rescaledDiffusivity (f : ScaleFamily r) (epsilon : ℝ) (n : ℕ) : ℝ :=
  epsilon / f.ell n ^ 2

/-- A selected cell together with exactly the admissibility fact used by the
local seed.  The family itself is fixed before `epsilon`; only `index` is
selected afterwards. -/
structure MatchingCell (f : ScaleFamily r) (epsilon : ℝ) where
  /-- Index of the scale-family cell selected for `epsilon`. -/
  index : ℕ
  admissible : f.rescaledDiffusivity epsilon index ∈ p.interval

namespace MatchingCell

variable {f : ScaleFamily r} {epsilon : ℝ}

/-- Rescaled diffusivity attached to a matching cell. -/
def delta (c : MatchingCell f epsilon) : ℝ :=
  f.rescaledDiffusivity epsilon c.index

/-- The rescaled diffusivity of a matching cell lies in the seed's admissible interval
`[deltaMinus, deltaPlus]`. -/
theorem delta_mem_interval (c : MatchingCell f epsilon) :
    c.delta ∈ p.interval :=
  c.admissible

/-- The rescaled diffusivity of a matching cell is positive, since `deltaMinus > 0`. -/
theorem delta_pos (c : MatchingCell f epsilon) : 0 < c.delta :=
  p.deltaMinus_pos.trans_le c.admissible.1

/-- Exact reconstruction of the physical diffusivity from a matching cell. -/
theorem epsilon_eq_delta_mul_ell_sq (c : MatchingCell f epsilon) :
    epsilon = c.delta * f.ell c.index ^ 2 := by
  unfold delta rescaledDiffusivity
  exact (div_mul_cancel₀ epsilon
    (ne_of_gt (sq_pos_of_pos (f.ell_pos c.index)))).symm

/-- The selected cell retains the exact local axial wavenumber, `2π K_n ell_n = N`.  The
paper sets `ell_n = 1 / K_n` in §3.2 and uses `K_n ell_n = 1` directly; with `k_*` kept as a
Lean parameter the identity reads `2π K_n ell_n = 2π k_* = N`. -/
theorem axial_wavenumber_match (c : MatchingCell f epsilon) :
    2 * Real.pi * (f.fourierIndex c.index : ℝ) * f.ell c.index =
      p.wavenumber :=
  f.axial_wavenumber_match c.index

/-- The selected cell's added axial speed gives the prescribed fixed shift. -/
theorem axialAmplitude_match (c : MatchingCell f epsilon) (tau : ℝ) :
    2 * Real.pi * (f.fourierIndex c.index : ℝ) *
      f.axialAmplitude tau c.index = tau :=
  f.axialAmplitude_match tau c.index

end MatchingCell

/-- Every physical diffusivity in the scale-family range has a matching
cell. -/
theorem exists_matchingCell (f : ScaleFamily r) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hupper : epsilon ≤ f.epsilon0) :
    Nonempty (MatchingCell f epsilon) := by
  obtain ⟨n, hn⟩ := f.exists_matching_scale hepsilon hupper
  exact ⟨⟨n, hn⟩⟩

end ScaleFamily

end

end FastDynamo
