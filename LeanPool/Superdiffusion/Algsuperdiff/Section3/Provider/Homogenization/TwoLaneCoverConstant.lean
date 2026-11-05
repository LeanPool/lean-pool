/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Probability.GaussianMaximum
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.TwoLaneCoverDepth
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.TsumTriangle
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.ConcentrationAEMeasurable

/-!
# TwoLaneCoverConstant

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The dimension-only cover constant of one exponent

This module carries the scale bookkeeping of the lane-separated
observation-scale transport of
`Provider/Homogenization/TwoLaneCoverTransport.lean`; it is separated to keep
each Lean file focused and below the repository line limit.  Nothing here
depends on the lane: the Orlicz exponent `sigma` is an arbitrary positive real
parameter and the cell family is arbitrary.

Two things are recorded.  First, the layer scales of the deterministic cover of
`Provider/Homogenization/TwoLaneCoverDepth.lean` at a general exponent
`sigma`: `laneDepthScale` is the layer weight of the coarse expansion times the
finite-maximum cost `(3 max(1, log N))^{1/sigma}` of that layer's parent
generation times the triangle constant `gammaTriangleConst sigma`, and
`laneFineDepthScale` is its fine-tail analogue.  Both are strictly positive --
which is what the countable triangle inequality demands of its scales -- and
both are summable, because the geometric layer weight beats the polynomial cost
`(1 + ell)^{1/sigma}`.  The resulting dimension-only constant is
`laneCoverConst d sigma`, which is at least `1` by construction.  Second, the
measurability in the sample of the three cover functionals, which the
probabilistic aggregation needs and which is discharged internally, never as a
binder.

The declarations below are local Provider results.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization.TwoLaneCoverInternal

open Filter MeasureTheory Set
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open scoped BigOperators

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The dimension-only cover constant of one exponent -/

/-- The layer scale of the cover at the exponent `sigma`: the geometric weight
of the layer, the finite-maximum cost of that layer's parent generation, and
the triangle constant. -/
def laneDepthScale (d : ℕ) (σ : ℝ) (ell : ℕ) : ℝ :=
  Ch02.geometricWeight (1 / 8) 2 ell *
    (3 * ((1 + (d : ℝ) * Real.log 3) * (1 + (ell : ℝ)))) ^ σ⁻¹ *
    gammaTriangleConst σ

/-- The fine-tail scale of the cover at the exponent `sigma`. -/
def laneFineDepthScale (d : ℕ) (σ : ℝ) (r : ℕ) : ℝ :=
  laneFineFactor r *
    (3 * ((1 + (d : ℝ) * Real.log 3) * (1 + (r : ℝ)))) ^ σ⁻¹

theorem laneDepthScale_pos (d : ℕ) (σ : ℝ) (ell : ℕ) :
    0 < laneDepthScale d σ ell := by
  unfold laneDepthScale
  have hweight : 0 < Ch02.geometricWeight (1 / 8) 2 ell := by
    rw [Ch02.geometricWeight_eq_old]
    exact HCPolySupport.geometricWeight_pos ell (by norm_num)
  have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hbase : 0 < 3 * ((1 + (d : ℝ) * Real.log 3) * (1 + (ell : ℝ))) := by
    positivity
  exact mul_pos (mul_pos hweight (Real.rpow_pos_of_pos hbase _))
    gammaTriangleConst_pos

private theorem laneFineFactor_pos (r : ℕ) : 0 < laneFineFactor r := by
  unfold laneFineFactor
  have hdiscount : 0 < Ch02.geometricDiscount (1 / 8 : ℝ) 2 := by
    rw [Ch02.geometricDiscount_eq_old]
    exact HCPolySupport.geometricDiscount_pos (by norm_num)
  have hgap : 0 < 1 - (3 : ℝ) ^ (-(((1 / 8 : ℝ) - (1 / 16 : ℝ)) * 2)) := by
    have := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3)
      (by norm_num : -(((1 / 8 : ℝ) - (1 / 16 : ℝ)) * 2) < 0)
    linarith
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (mul_pos hdiscount (inv_pos.mpr hgap))

theorem laneFineDepthScale_pos (d : ℕ) (σ : ℝ) (r : ℕ) :
    0 < laneFineDepthScale d σ r := by
  unfold laneFineDepthScale
  have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hbase : 0 < 3 * ((1 + (d : ℝ) * Real.log 3) * (1 + (r : ℝ))) := by
    positivity
  exact mul_pos (laneFineFactor_pos r) (Real.rpow_pos_of_pos hbase _)

private theorem summable_one_add_pow_mul_geometric {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) (N : ℕ) :
    Summable (fun ell : ℕ => (1 + (ell : ℝ)) ^ N * r ^ ell) := by
  have hnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr0]
    exact hr1
  have hF : Summable (fun n : ℕ => (n : ℝ) ^ N * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one N hnorm
  have hG : Summable (fun ell : ℕ => ((ell + 1 : ℕ) : ℝ) ^ N * r ^ (ell + 1)) :=
    hF.comp_injective (add_left_injective 1)
  refine ((hG.mul_left r⁻¹).congr fun ell => ?_)
  have hr' : r ≠ 0 := ne_of_gt hr0
  push_cast
  rw [pow_succ]
  field_simp
  ring

theorem summable_laneDepthScale (d : ℕ) (σ : ℝ) :
    Summable (laneDepthScale d σ) := by
  set N : ℕ := ⌈σ⁻¹⌉₊ with hN
  set c : ℝ := 1 + (d : ℝ) * Real.log 3 with hc
  set q : ℝ := (3 : ℝ) ^ (-(1 / 4 : ℝ)) with hq
  have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hc1 : 1 ≤ c := by
    rw [hc]
    have : 0 ≤ (d : ℝ) * Real.log 3 := mul_nonneg (Nat.cast_nonneg _) hlog
    linarith
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hbase : Summable (fun ell : ℕ => (1 + (ell : ℝ)) ^ N * q ^ ell) :=
    summable_one_add_pow_mul_geometric hq0 hq1 N
  have hmaj : Summable (fun ell : ℕ =>
      (Ch02.geometricDiscount (1 / 8 : ℝ) 2 * gammaTriangleConst σ *
        (3 * c) ^ N) * ((1 + (ell : ℝ)) ^ N * q ^ ell)) := hbase.mul_left _
  refine Summable.of_nonneg_of_le (fun ell => (laneDepthScale_pos d σ ell).le)
    (fun ell => ?_) hmaj
  have hweight : Ch02.geometricWeight (1 / 8 : ℝ) 2 ell =
      Ch02.geometricDiscount (1 / 8 : ℝ) 2 * q ^ ell := by
    rw [Ch02.geometricWeight, hq]
    congr 1
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ell,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hbase1 : (1 : ℝ) ≤ 3 * (c * (1 + (ell : ℝ))) := by
    have hell : (0 : ℝ) ≤ (ell : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hpow : (3 * (c * (1 + (ell : ℝ)))) ^ σ⁻¹ ≤
      (3 * c) ^ N * (1 + (ell : ℝ)) ^ N := by
    have hle : (3 * (c * (1 + (ell : ℝ)))) ^ σ⁻¹ ≤
        (3 * (c * (1 + (ell : ℝ)))) ^ (N : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbase1 (by
        rw [hN]
        exact Nat.le_ceil _)
    have hnat : (3 * (c * (1 + (ell : ℝ)))) ^ (N : ℝ) =
        (3 * c) ^ N * (1 + (ell : ℝ)) ^ N := by
      rw [Real.rpow_natCast, show 3 * (c * (1 + (ell : ℝ)))
        = (3 * c) * (1 + (ell : ℝ)) by ring, mul_pow]
    rw [hnat] at hle
    exact hle
  have hdisc : 0 ≤ Ch02.geometricDiscount (1 / 8 : ℝ) 2 := by
    rw [Ch02.geometricDiscount_eq_old]
    exact (HCPolySupport.geometricDiscount_pos (by norm_num)).le
  have hq0' : (0 : ℝ) ≤ q ^ ell := (pow_pos hq0 ell).le
  unfold laneDepthScale
  rw [hweight, show 3 * ((1 + (d : ℝ) * Real.log 3) * (1 + (ell : ℝ)))
    = 3 * (c * (1 + (ell : ℝ))) by rw [hc]]
  have hmul := mul_le_mul_of_nonneg_left hpow
    (mul_nonneg hdisc hq0')
  calc Ch02.geometricDiscount (1 / 8 : ℝ) 2 * q ^ ell *
        (3 * (c * (1 + (ell : ℝ)))) ^ σ⁻¹ * gammaTriangleConst σ
      = (Ch02.geometricDiscount (1 / 8 : ℝ) 2 * q ^ ell *
          (3 * (c * (1 + (ell : ℝ)))) ^ σ⁻¹) * gammaTriangleConst σ := by ring
    _ ≤ (Ch02.geometricDiscount (1 / 8 : ℝ) 2 * q ^ ell *
          ((3 * c) ^ N * (1 + (ell : ℝ)) ^ N)) * gammaTriangleConst σ :=
        mul_le_mul_of_nonneg_right (by
          simpa only [mul_assoc] using hmul) gammaTriangleConst_pos.le
    _ = (Ch02.geometricDiscount (1 / 8 : ℝ) 2 * gammaTriangleConst σ *
          (3 * c) ^ N) * ((1 + (ell : ℝ)) ^ N * q ^ ell) := by ring

private theorem laneFineDepthScale_eq (d : ℕ) (σ : ℝ) (r : ℕ) :
    laneFineDepthScale d σ r =
      ((1 - (3 : ℝ) ^ (-(((1 / 8 : ℝ) - (1 / 16 : ℝ)) * 2)))⁻¹ *
        (gammaTriangleConst σ)⁻¹) * laneDepthScale d σ r := by
  have hexp : (-(2 * (1 / 8 : ℝ) * (r : ℝ))) = -(1 / 8 : ℝ) * 2 * (r : ℝ) := by
    ring
  have htri : gammaTriangleConst σ ≠ 0 := gammaTriangleConst_pos.ne'
  have hdisc : Ch02.geometricDiscount (1 / 8 : ℝ) 2 ≠ 0 := by
    rw [Ch02.geometricDiscount_eq_old]
    exact (HCPolySupport.geometricDiscount_pos (by norm_num)).ne'
  unfold laneFineDepthScale laneDepthScale laneFineFactor
  rw [Ch02.geometricWeight, hexp]
  field_simp

theorem summable_laneFineDepthScale (d : ℕ) (σ : ℝ) :
    Summable (laneFineDepthScale d σ) := by
  have heq : laneFineDepthScale d σ = fun r =>
      ((1 - (3 : ℝ) ^ (-(((1 / 8 : ℝ) - (1 / 16 : ℝ)) * 2)))⁻¹ *
        (gammaTriangleConst σ)⁻¹) * laneDepthScale d σ r := by
    funext r
    exact laneFineDepthScale_eq d σ r
  rw [heq]
  exact (summable_laneDepthScale d σ).mul_left _

/-- The dimension-only cover constant of the exponent `sigma`. -/
def laneCoverConst (d : ℕ) (σ : ℝ) : ℝ :=
  1 + 2 * (3 * max 1 (Real.log 2)) ^ σ⁻¹ *
    (gammaTriangleConst σ * (∑' r : ℕ, laneDepthScale d σ r) +
      ∑' r : ℕ, laneFineDepthScale d σ r)

theorem one_le_laneCoverConst (d : ℕ) (σ : ℝ) :
    1 ≤ laneCoverConst d σ := by
  unfold laneCoverConst
  have hdepth : 0 ≤ ∑' r : ℕ, laneDepthScale d σ r :=
    tsum_nonneg fun r => (laneDepthScale_pos d σ r).le
  have hfine : 0 ≤ ∑' r : ℕ, laneFineDepthScale d σ r :=
    tsum_nonneg fun r => (laneFineDepthScale_pos d σ r).le
  have hsum : 0 ≤ gammaTriangleConst σ * (∑' r : ℕ, laneDepthScale d σ r) +
      ∑' r : ℕ, laneFineDepthScale d σ r :=
    add_nonneg (mul_nonneg gammaTriangleConst_pos.le hdepth) hfine
  have hfac : 0 ≤ 2 * (3 * max 1 (Real.log 2)) ^ σ⁻¹ := by
    have : (0 : ℝ) ≤ 3 * max 1 (Real.log 2) :=
      mul_nonneg (by norm_num) (zero_le_one.trans (le_max_left _ _))
    positivity
  nlinarith

/-! ## Measurability of the cover functionals -/

omit [NeZero d] in
private theorem descendantsAverage_measurable
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : HCPolySupport.TriadicCube d) (j : ℕ)
    (X : HCPolySupport.TriadicCube d → Omega → ℝ)
    (hX : ∀ R, Measurable (X R)) :
    Measurable (fun omega => descendantsAverage Q j (fun R => X R omega)) := by
  unfold descendantsAverage
  exact measurable_const.mul (Finset.measurable_sum _ fun R _ => hX R)

omit [NeZero d] in
theorem laneParentAverage_measurable (L m : ℤ)
    {g : HCPolySupport.TriadicCube d → Cutoff.CutoffSample d → ℝ}
    (hgm : ∀ R, Measurable (g R)) (ell : ℕ) :
    Measurable (laneParentAverage L m g ell) := by
  have hk : m - (ell : ℤ) ≤ (originCube d m).scale :=
    sub_le_self m (by exact_mod_cast Nat.zero_le ell)
  have hD : (descendantsAtScale (originCube d m) (m - (ell : ℤ))).Nonempty :=
    descendantsAtScale_nonempty _ hk
  have hsup : Measurable (fun omega =>
      (descendantsAtScale (originCube d m) (m - (ell : ℤ))).sup' hD
        (fun P => descendantsAverage P (Int.toNat (m - (ell : ℤ) - L))
          (fun R => g R omega))) :=
    Probability.measurable_finset_sup' hD fun P _ =>
      descendantsAverage_measurable P _ _ hgm
  have heq : (fun omega =>
      (descendantsAtScale (originCube d m) (m - (ell : ℤ))).sup' hD
        (fun P => descendantsAverage P (Int.toNat (m - (ell : ℤ) - L))
          (fun R => g R omega))) = laneParentAverage L m g ell := by
    funext omega
    exact (Ch04.RestrictionLawCarrier.finsetSupReal_eq_sup' _ hD _).symm
  rwa [← heq]

omit [NeZero d] in
private theorem laneCellSup_measurable (L m : ℤ) (hLm : L ≤ m)
    {g : HCPolySupport.TriadicCube d → Cutoff.CutoffSample d → ℝ}
    (hgm : ∀ R, Measurable (g R)) :
    Measurable (laneCellSup L m g) := by
  have hD : (descendantsAtScale (originCube d m) L).Nonempty :=
    descendantsAtScale_nonempty _ hLm
  have hsup : Measurable (fun omega =>
      (descendantsAtScale (originCube d m) L).sup' hD
        (fun R => g R omega)) :=
    Probability.measurable_finset_sup' hD fun R _ => hgm R
  have heq : (fun omega =>
      (descendantsAtScale (originCube d m) L).sup' hD
        (fun R => g R omega)) = laneCellSup L m g := by
    funext omega
    exact (Ch04.RestrictionLawCarrier.finsetSupReal_eq_sup' _ hD _).symm
  rwa [← heq]

omit [NeZero d] in
theorem laneTotal_measurable (L m : ℤ) (hLm : L ≤ m)
    {g : HCPolySupport.TriadicCube d → Cutoff.CutoffSample d → ℝ}
    (hgm : ∀ R, Measurable (g R)) :
    Measurable (laneTotal L m g) := by
  unfold laneTotal laneCoarse
  refine Measurable.add (Finset.measurable_sum _ fun ell _ => ?_)
    (measurable_const.mul (laneCellSup_measurable L m hLm hgm))
  exact measurable_const.mul (laneParentAverage_measurable L m hgm ell)

end

end Algsuperdiff.Section3.Provider.Homogenization.TwoLaneCoverInternal
