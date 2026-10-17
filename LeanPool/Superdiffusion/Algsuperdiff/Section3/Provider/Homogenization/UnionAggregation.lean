/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.TwoLaneCoverTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.UnionDirectionNet
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.UnionSiteProducers
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.CommonEventAggregation

/-!
# UnionAggregation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Aggregation of the Section 3.5 grid displays over the cutoff family

ABK26 (proof of `p.homogenization.step`) fixes two integer separations `k1` and
`k2`, puts `k = k1 + k2` and `n = L + k1`, and then sums the per-cutoff grid
concentration display over the *infinite* family

`{L in Z : L <= m - k}`

to obtain `e.union.bound.fluct`.  This module performs that aggregation on the
genuine cutoff sample law and packages it in the shape the Section 3.5
statement uses for its supremum, namely one pair of measurable envelopes
dominating the whole indexed family on a single event of probability one.

Its abstract measure-theoretic part --- the A of the common-event two-term
carrier, which refers to nothing in Section 3.5 --- is
`Provider/Orlicz/CommonEventAggregation.lean`, and the finite direction net
that the Section 3.5 statement needs in order to pass from one direction to the
uncountable Euclidean unit sphere is
`Provider/Homogenization/UnionDirectionNet.lean`.

## What is aggregated

For each `j : N` the member of the family is the recentred grid average of
ABK26 at the cutoff `L_j = m - k1 - k2 - j` and the observation scale `n_j =
L_j + k1 = m - k2 - j`, written at relative depth `m - n_j = k2 + j`.  The
proved grid display `isTwoTermBigOWith_gridAverage_siteCenteredResponseJ` gives
each member a one-sided two-term `(Gamma_1, Gamma_{1/4})` bound whose two
amplitudes carry the factor `3 ^ (-d (k2 + j) / 2)`.  Both amplitudes are
therefore summable in `j` with a geometric ratio `3 ^ (-d/2) < 1`, and their
sums carry the single extra factor `(1 - 3 ^ (-d/2))^{-1}`, a constant
depending only on `d`.

## The measure-theoretic reading of the supremum

That is exactly the content of
`Algsuperdiff.Section3.Probability.IsCommonEventTwoTermBigOWith`, and the
aggregation below produces it through the abstract engine of
`Provider/Orlicz/CommonEventAggregation.lean`.  The two Orlicz terms stay
separate and one-sided throughout: the two lanes are never merged.

## The direction net

In the source the maximization is over one Euclidean unit vector, and convexity
reduces it to a finite net at a dimensional cost.  The reduction
against this repository's carrier is in the companion module
`Provider/Homogenization/UnionDirectionNet.lean`: on one probability-one
event, simultaneously for every cutoff scale and every unit direction, the
Section 3.5 response is at most `2 ^ d` times the sum of its values at the `d`
coordinate directions, hence at most `2 ^ d * d` times one of them.  The two
deliberate deviations from that reduction --- the coordinate net in place of the
sign vertices, and the cost
`2 ^ d` (or `2 ^ d * d`) in place of `d` --- are recorded in that module's
docstring, together with the two places inside the printed budget
`k = k1 + k2 <= C(d) |log epsilon|` where the extra factor is absorbed: the
fluctuation lanes by enlarging `k2` (see `exists_gridDecay_mul_le` below), and
the deterministic mean by running the finite-corridor iteration at
`epsilon / (2 ^ d * d)`.  Enlarging `k2` alone does not suffice: the direction
net multiplies the mean term as well.

## References

* ABK26, Proposition `p.homogenization.step`.
* ABK26, Appendix, the weak-Orlicz notation and the `Gamma_sigma` triangle
  inequality.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Percolation

noncomputable section

/-! ## The geometry of the cutoff family

The grid gain `3 ^ (-d k / 2)` of the concentration display is geometric in
the relative depth `k`, which is what makes the infinite cutoff family
summable.
-/

section Geometry

variable {d : ℕ}

/-- The grid gain is multiplicative in the relative depth. -/
theorem gridDecay_add (d k j : ℕ) :
    gridDecay d (k + j) = gridDecay d k * gridDecay d j := by
  unfold gridDecay
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  push_cast
  ring

/-- The grid gain is the geometric sequence of ratio `3 ^ (-d/2)`. -/
theorem gridDecay_eq_pow (d j : ℕ) : gridDecay d j = gridDecay d 1 ^ j := by
  induction j with
  | zero => norm_num [gridDecay]
  | succ n ih => rw [gridDecay_add d n 1, ih, pow_succ]

/-- The grid gain never exceeds one. -/
theorem gridDecay_le_one (d k : ℕ) : gridDecay d k ≤ 1 := by
  have hexp : -((d * k : ℕ) : ℝ) / 2 ≤ 0 := by
    have hnn : (0 : ℝ) ≤ ((d * k : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hexp

/-- In every genuine dimension the geometric ratio is strictly below one. -/
theorem gridDecay_lt_one (hd : 0 < d) : gridDecay d 1 < 1 := by
  have hexp : -((d * 1 : ℕ) : ℝ) / 2 < 0 := by
    have : (0 : ℝ) < ((d * 1 : ℕ) : ℝ) := by
      have : 0 < d * 1 := by omega
      exact_mod_cast this
    linarith
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexp

/-- The shifted grid gains are summable. -/
theorem summable_const_mul_gridDecay_add (hd : 0 < d) (k : ℕ) (c : ℝ) :
    Summable fun j : ℕ => c * gridDecay d (k + j) := by
  have hgeom : Summable fun j : ℕ => gridDecay d 1 ^ j :=
    summable_geometric_of_lt_one (gridDecay_pos d 1).le (gridDecay_lt_one hd)
  have heq : (fun j : ℕ => c * gridDecay d (k + j)) =
      fun j : ℕ => (c * gridDecay d k) * gridDecay d 1 ^ j := by
    funext j
    rw [gridDecay_add, gridDecay_eq_pow d j, mul_assoc]
  rw [heq]
  exact hgeom.mul_left _

/-- The exact geometric sum of the shifted grid gains.  This is the single
extra dimensional factor `(1 - 3 ^ (-d/2))^{-1}` paid by the infinite cutoff
family. -/
theorem tsum_const_mul_gridDecay_add (hd : 0 < d) (k : ℕ) (c : ℝ) :
    ∑' j : ℕ, c * gridDecay d (k + j) =
      c * gridDecay d k * (1 - gridDecay d 1)⁻¹ := by
  have heq : (fun j : ℕ => c * gridDecay d (k + j)) =
      fun j : ℕ => (c * gridDecay d k) * gridDecay d 1 ^ j := by
    funext j
    rw [gridDecay_add, gridDecay_eq_pow d j, mul_assoc]
  rw [heq, tsum_mul_left,
    tsum_geometric_of_lt_one (gridDecay_pos d 1).le (gridDecay_lt_one hd)]

/-- **The separation selection of ABK26.**  For every positive target
`epsilon` there is an integer separation `k` making the grid gain absorb any
prescribed positive constant, and the separation may be chosen of the
printed logarithmic size `k <= 1 + |2 log(c / epsilon) / (d log 3)|`.

The manuscript writes this as `k2 = ceil(log_3(10 epsilon^{-1}))` and then
records `k = k1 + k2 <= C |log epsilon|` in the last sentence of the proof. -/
theorem exists_gridDecay_mul_le (hd : 0 < d) {c epsilon : ℝ} (hc : 0 < c)
    (hepsilon : 0 < epsilon) :
    ∃ k : ℕ, c * gridDecay d k ≤ epsilon ∧
      (k : ℝ) ≤ 1 + |2 * Real.log (c / epsilon) / ((d : ℝ) * Real.log 3)| := by
  classical
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hden : 0 < (d : ℝ) * Real.log 3 := mul_pos hdpos hlog3
  set t : ℝ := 2 * Real.log (c / epsilon) / ((d : ℝ) * Real.log 3) with ht
  refine ⟨⌈t⌉₊, ?_, ?_⟩
  · have hkt : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
    have hprod : 2 * Real.log (c / epsilon) ≤ (⌈t⌉₊ : ℝ) * ((d : ℝ) * Real.log 3) := by
      rw [ht] at hkt
      exact (div_le_iff₀ hden).mp hkt
    have hcast : ((d * ⌈t⌉₊ : ℕ) : ℝ) = (d : ℝ) * (⌈t⌉₊ : ℝ) := by push_cast; ring
    have hkey : Real.log (c / epsilon) ≤ ((d * ⌈t⌉₊ : ℕ) : ℝ) / 2 * Real.log 3 := by
      rw [hcast]
      nlinarith
    have hexp := Real.exp_le_exp.2 hkey
    rw [Real.exp_log (div_pos hc hepsilon)] at hexp
    have hpow : Real.exp (((d * ⌈t⌉₊ : ℕ) : ℝ) / 2 * Real.log 3) =
        (3 : ℝ) ^ (((d * ⌈t⌉₊ : ℕ) : ℝ) / 2) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
      ring_nf
    rw [hpow] at hexp
    have hP : (0 : ℝ) < (3 : ℝ) ^ (((d * ⌈t⌉₊ : ℕ) : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hgd : gridDecay d ⌈t⌉₊ =
        ((3 : ℝ) ^ (((d * ⌈t⌉₊ : ℕ) : ℝ) / 2))⁻¹ := by
      unfold gridDecay
      rw [neg_div, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
    have hcle : c ≤ (3 : ℝ) ^ (((d * ⌈t⌉₊ : ℕ) : ℝ) / 2) * epsilon :=
      (div_le_iff₀ hepsilon).mp hexp
    rw [hgd]
    calc c * ((3 : ℝ) ^ (((d * ⌈t⌉₊ : ℕ) : ℝ) / 2))⁻¹
        ≤ ((3 : ℝ) ^ (((d * ⌈t⌉₊ : ℕ) : ℝ) / 2) * epsilon) *
            ((3 : ℝ) ^ (((d * ⌈t⌉₊ : ℕ) : ℝ) / 2))⁻¹ :=
          mul_le_mul_of_nonneg_right hcle (inv_pos.2 hP).le
      _ = epsilon := by field_simp
  · rcases le_or_gt 0 t with hpos | hneg
    · have hceil := Nat.ceil_lt_add_one hpos
      rw [abs_of_nonneg hpos]
      linarith
    · have hzero : ⌈t⌉₊ = 0 := Nat.ceil_eq_zero.2 hneg.le
      rw [hzero]
      have : (0 : ℝ) ≤ |t| := abs_nonneg t
      push_cast
      linarith

end Geometry

/-! ## The cutoff family of ABK26 -/

section Family

variable {d : ℕ}

/-- The cutoff scale `L_j = m - k1 - k2 - j` of the `j`-th member of the
family summed at ABK26: the printed range is `L <= m - k` with `k = k1 +
k2`. -/
def unionCutoffScale (m : ℤ) (k1 k2 j : ℕ) : ℤ := m - k1 - k2 - j

/-- The observation scale `n_j = L_j + k1` chosen in ABK26, at which the grid `3
^ n Z^d cap square_m` is taken. -/
def unionObservationScale (m : ℤ) (k2 j : ℕ) : ℤ := m - k2 - j

/-- The `j`-th member of the family aggregated at ABK26: the absolute
recentred grid average over `3 ^ (n_j) Z^d cap square_m`, written at the
relative depth `m - n_j = k2 + j`. -/
def unionGridAverage (M : ABKModel d) (m : ℤ) (k1 k2 j : ℕ) (e : Vec d) :
    CutoffSample d → ℝ :=
  fun omega => |((cubeFinset (d := d) (k2 + j)).card : ℝ)⁻¹ *
    ∑ u ∈ cubeFinset (d := d) (k2 + j),
      siteCenteredResponseJ M (unionCutoffScale m k1 k2 j)
        (unionObservationScale m k2 j) u e omega|

end Family

/-! ## The aggregated display -/

section Aggregation

/-- **The Section 3.5 cutoff-union display on one common event.**

Fix a unit direction `e`, as ABK26 does throughout, and two integer separations
`k1` and `k2` with `1 <= k1 + k2`.  From the preceding-error clause of the
Section 3.5 statement, the recentred grid averages of ABK26, taken at the
cutoffs `L_j = m - k1 - k2 - j` and the observation scales `n_j = L_j + k1`,
admit one pair of measurable envelopes dominating *every* member of the
infinite family on a single event of probability one, with a `Gamma_1`
amplitude proportional to `E^2 gamma` and a `Gamma_{1/4}` amplitude
proportional to `exp(-2 E^{-3} gamma^{-1})`, both carrying the separation gain
`3 ^ (-d k2 / 2)`.  The proportionality constant depends only on `d`.

The `Gamma_{1/4}` amplitude carries the exponent `2` where print `exp(-E^{-3}
gamma^{-1})`.  The frozen Section 3.5 conclusion asks for exactly this
amplitude.

The gain `3 ^ (-d k2 / 2)` is where the factor `epsilon` of the printed
right-hand side comes from: it is made as small as desired by enlarging `k2`,
which is the printed choice `k2 = ceil(log_3(10 epsilon^{-1}))`.

The two-lane transport, the per-site producers, the grid concentration engine
and the countable envelope selection are all consumed, not re-derived.  This
is a Provider endpoint and carries no source-node status by itself. -/
theorem exists_unionGridAverageCommonEnvelope (d : ℕ) :
    ∃ Cunion : ℝ, 0 < Cunion ∧
      ∀ (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E}),
        (∀ k : ℤ, k ≤ m - 1 →
          ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
            Probability.IsTwoTermBigOWith
              (cutoffSampleLaw M).toMeasure
              (gammaSigma 2) (gammaSigma (1 / 2))
              (Observable.cutoffHomogenizationError M k
                ⟨s,
                  (mul_pos (by norm_num : (0 : ℝ) < 8)
                    M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
              ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
              ((s⁻¹) ^ 2 *
                Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))) →
        (1 / 16 : ℝ) ∈ Set.Icc (8 * M.gamma) 1 →
        ∀ k1 k2 : ℕ, 1 ≤ k1 + k2 →
        ∀ e : Vec d, Ch02.vecNorm e = 1 →
          Probability.IsCommonEventTwoTermBigOWith
            (cutoffSampleLaw M).toMeasure (gammaSigma 1) (gammaSigma (1 / 4))
            (fun j : ℕ => unionGridAverage M m k1 k2 j e)
            (Cunion * ((E : ℝ) ^ 2 * M.gamma) * gridDecay d k2)
            (Cunion *
              Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) * gridDecay d k2) := by
  classical
  obtain ⟨Ctwo, -, htrans⟩ := exists_twoLaneObservationScaleTransport d
  have hinvnn : (0 : ℝ) ≤ (1 - gridDecay d 1)⁻¹ :=
    inv_nonneg.2 (by linarith [gridDecay_le_one d 1])
  have hty : (0 : ℝ) ≤ gammaTriangleConst 1 * gridConcentrationConst d 1 *
      Orlicz.mixedLinearConst 2 * siteLaneConst 1 * (Ctwo ^ 2 * 256) *
      (1 - gridDecay d 1)⁻¹ := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      gammaTriangleConst_pos.le
      (gridConcentrationConst_pos (by norm_num : (0 : ℝ) < 1)).le)
      (Orlicz.mixedLinearConst_pos 2).le) (siteLaneConst_pos one_pos).le)
      (by positivity)) hinvnn
  have hra : (0 : ℝ) ≤ gammaTriangleConst (1 / 4) *
      gridConcentrationConst d (1 / 4) * Orlicz.mixedQuarticConst 2 *
      siteLaneConst (1 / 4) * (Ctwo ^ 2 * 65536) * (1 - gridDecay d 1)⁻¹ := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      gammaTriangleConst_pos.le
      (gridConcentrationConst_pos (by norm_num : (0 : ℝ) < 1 / 4)).le)
      (Orlicz.mixedQuarticConst_pos 2).le)
      (siteLaneConst_pos (by norm_num : (0 : ℝ) < 1 / 4)).le)
      (by positivity)) hinvnn
  refine ⟨1 +
      (gammaTriangleConst 1 * gridConcentrationConst d 1 *
        Orlicz.mixedLinearConst 2 * siteLaneConst 1 * (Ctwo ^ 2 * 256) *
        (1 - gridDecay d 1)⁻¹) +
      (gammaTriangleConst (1 / 4) * gridConcentrationConst d (1 / 4) *
        Orlicz.mixedQuarticConst 2 * siteLaneConst (1 / 4) *
        (Ctwo ^ 2 * 65536) * (1 - gridDecay d 1)⁻¹), by linarith, ?_⟩
  intro M m E hLower hWindow k1 k2 hsep e he
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hgammann : (0 : ℝ) ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hA2 : (Ctwo * ((E : ℝ) * (1 / 16 : ℝ)⁻¹ * Real.sqrt M.gamma)) ^ 2 =
      Ctwo ^ 2 * 256 * ((E : ℝ) ^ 2 * M.gamma) := by
    have hg : Real.sqrt M.gamma ^ 2 = M.gamma := Real.sq_sqrt hgammann
    have hexpand : (Ctwo * ((E : ℝ) * (1 / 16 : ℝ)⁻¹ * Real.sqrt M.gamma)) ^ 2 =
        Ctwo ^ 2 * 256 * ((E : ℝ) ^ 2 * Real.sqrt M.gamma ^ 2) := by
      norm_num
      ring
    rw [hexpand, hg]
  have hB2 : (Ctwo * (((1 / 16 : ℝ))⁻¹ ^ 2 *
        Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))) ^ 2 =
      Ctwo ^ 2 * 65536 *
        Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) := by
    have hexp : Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) ^ 2 =
        Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) := by
      rw [sq, ← Real.exp_add]
      ring_nf
    have hexpand : (Ctwo * (((1 / 16 : ℝ))⁻¹ ^ 2 *
          Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))) ^ 2 =
        Ctwo ^ 2 * 65536 *
          Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) ^ 2 := by
      norm_num
      ring
    rw [hexpand, hexp]
  have hdisplay : ∀ j : ℕ,
      Probability.IsTwoTermBigOWith (cutoffSampleLaw M).toMeasure
        (gammaSigma 1) (gammaSigma (1 / 4))
        (unionGridAverage M m k1 k2 j e)
        (gridConcentrationConst d 1 *
          (Orlicz.mixedLinearConst 2 *
            (siteLaneConst 1 *
              (Ctwo * ((E : ℝ) * (1 / 16 : ℝ)⁻¹ * Real.sqrt M.gamma)) ^ 2)) *
          gridDecay d (k2 + j))
        (gridConcentrationConst d (1 / 4) *
          (Orlicz.mixedQuarticConst 2 *
            (siteLaneConst (1 / 4) *
              (Ctwo * (((1 / 16 : ℝ))⁻¹ ^ 2 *
                Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))) ^ 2)) *
          gridDecay d (k2 + j)) := by
    intro j
    have hL : unionCutoffScale m k1 k2 j ≤ m - 1 := by
      simp only [unionCutoffScale]
      omega
    have hLn : unionCutoffScale m k1 k2 j ≤ unionObservationScale m k2 j := by
      simp only [unionCutoffScale, unionObservationScale]
      omega
    exact isTwoTermBigOWith_gridAverage_siteCenteredResponseJ M hLn (k2 + j)
      (by norm_num : (0 : ℝ) < 1 / 8) he
      (htrans M m E hLower hWindow (unionCutoffScale m k1 k2 j)
        (unionObservationScale m k2 j) hL hLn)
  have hagg := isCommonEventTwoTermBigOWith_of_summable_isTwoTermBigOWith
    (mu := (cutoffSampleLaw M).toMeasure)
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1 / 4)
    (summable_const_mul_gridDecay_add hd k2 _)
    (summable_const_mul_gridDecay_add hd k2 _) hdisplay
  refine isCommonEventTwoTermBigOWith_mono_scale hagg ?_ ?_
  · rw [tsum_const_mul_gridDecay_add hd k2, hA2]
    have hrewrite : gammaTriangleConst 1 *
        (gridConcentrationConst d 1 *
            (Orlicz.mixedLinearConst 2 *
              (siteLaneConst 1 * (Ctwo ^ 2 * 256 * ((E : ℝ) ^ 2 * M.gamma)))) *
          gridDecay d k2 * (1 - gridDecay d 1)⁻¹) =
        (gammaTriangleConst 1 * gridConcentrationConst d 1 *
            Orlicz.mixedLinearConst 2 * siteLaneConst 1 * (Ctwo ^ 2 * 256) *
            (1 - gridDecay d 1)⁻¹) *
          ((E : ℝ) ^ 2 * M.gamma) * gridDecay d k2 := by
      ring
    rw [hrewrite]
    refine mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith)
        (mul_nonneg (sq_nonneg _) hgammann)) (gridDecay_pos d k2).le
  · rw [tsum_const_mul_gridDecay_add hd k2, hB2]
    have hrewrite : gammaTriangleConst (1 / 4) *
        (gridConcentrationConst d (1 / 4) *
            (Orlicz.mixedQuarticConst 2 *
              (siteLaneConst (1 / 4) *
                (Ctwo ^ 2 * 65536 *
                  Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))))) *
          gridDecay d k2 * (1 - gridDecay d 1)⁻¹) =
        (gammaTriangleConst (1 / 4) * gridConcentrationConst d (1 / 4) *
            Orlicz.mixedQuarticConst 2 * siteLaneConst (1 / 4) *
            (Ctwo ^ 2 * 65536) * (1 - gridDecay d 1)⁻¹) *
          Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) * gridDecay d k2 := by
      ring
    rw [hrewrite]
    refine mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)
      (gridDecay_pos d k2).le

end Aggregation

end

end Algsuperdiff.Section3.Provider.Homogenization
