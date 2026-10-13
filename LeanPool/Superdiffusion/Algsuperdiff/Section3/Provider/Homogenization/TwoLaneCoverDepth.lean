/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffHomogenizationError
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.ObservationScaleFiniteCoverDepth

/-!
# TwoLaneCoverDepth

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The deterministic lane-separated cover of the observation cube

This module is the deterministic half of the lane-separated observation-scale
transport of `Provider/Homogenization/TwoLaneCoverTransport.lean`; it is
separated to keep each Lean file focused and below the repository line limit.
It contains no probability: every statement here is a pointwise inequality at
a fixed sample point, and the two cell families it is run against are
arbitrary.

Fix a coefficient cutoff scale `L`, an observation cube `square_m` and two cell
families `g, h` on the cubes.  The squared raw homogenization error of
`square_m`, read at the discount `1/8`, expands into weighted depth layers.
The first `m - L` layers are *coarse*: each is dominated by the maximum, over
that layer's parents, of the average of the cell family over their scale-`L`
descendants (`laneParentAverage`).  The remaining layers are *fine*: they sit
below the cutoff scale and are dominated, with a geometrically summable factor
(`laneFineFactor`), by the maximum of the cell family over all scale-`L` cells
of the observation cube (`laneCellSup`).  Every step is monotone in the cell
family and the two maxima are subadditive, so a cover of the squared raw cell
errors by `g + h` splits the whole deterministic bound into one cover
functional per lane (`laneTotal`).  That is the content of the endpoint of this
module, `cutoffHomogenizationErrorRaw_sq_le_laneTotal_add`.

No comparator change occurs anywhere: the coefficient cutoff is `a_L` and the
normalizer is `sigmabar_L` at the cell scale, at every intermediate scale and
at the observation cube.  The discounts `t = 1/8` at the observation cube and
`u = 1/16` at the cells are the ones fixed by the corrected Step 4 of
`p.combine.under.S`; see the References of
`Provider/Homogenization/TwoLaneCoverTransport.lean`.

The declarations below are local Provider results.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization.TwoLaneCoverInternal

open Filter MeasureTheory Set
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Homogenization.ObservationScaleFiniteCoverInternal
open scoped BigOperators

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## Two elementary facts about the finite averages and suprema of the cover -/

omit [NeZero d] in
private theorem le_finsetSupReal_of_mem {α : Type*} (s : Finset α) (f : α → ℝ)
    {x : α} (hx : x ∈ s) : f x ≤ Ch02.finsetSupReal s f := by
  unfold Ch02.finsetSupReal
  exact le_csSup ((s.finite_toSet.image f).bddAbove) ⟨x, Finset.mem_coe.2 hx, rfl⟩

omit [NeZero d] in
private theorem descendantsAverage_add (Q : HCPolySupport.TriadicCube d) (j : ℕ)
    (F G : HCPolySupport.TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => F R + G R) =
      descendantsAverage Q j F + descendantsAverage Q j G := by
  unfold descendantsAverage
  simp only [Finset.sum_add_distrib]
  ring

/-! ## The cover functional of one lane -/

/-- The layer-`ell` parent maximum of the descendant averages of one cell
family. -/
def laneParentAverage (L m : ℤ)
    (g : HCPolySupport.TriadicCube d → Cutoff.CutoffSample d → ℝ) (ell : ℕ)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  Ch02.finsetSupReal (descendantsAtScale (originCube d m) (m - (ell : ℤ)))
    (fun P => descendantsAverage P (Int.toNat (m - (ell : ℤ) - L))
      (fun R => g R omega))

/-- The coarse part of the cover functional: the first `m - L` layers. -/
def laneCoarse (L m : ℤ)
    (g : HCPolySupport.TriadicCube d → Cutoff.CutoffSample d → ℝ)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  ∑ ell ∈ Finset.range (Int.toNat (m - L)),
    Ch02.geometricWeight (1 / 8) 2 ell * laneParentAverage L m g ell omega

/-- The maximum of one cell family over all scale-`L` cells of the observation
cube. -/
def laneCellSup (L m : ℤ)
    (g : HCPolySupport.TriadicCube d → Cutoff.CutoffSample d → ℝ)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  Ch02.finsetSupReal (descendantsAtScale (originCube d m) L)
    (fun R => g R omega)

/-- The geometric factor paid by the fine tail below the cutoff scale. -/
def laneFineFactor (r : ℕ) : ℝ :=
  Real.rpow 3 (-(2 * (1 / 8 : ℝ) * (r : ℝ))) *
    (Ch02.geometricDiscount (1 / 8 : ℝ) 2 *
      (1 - (3 : ℝ) ^ (-(((1 / 8 : ℝ) - (1 / 16 : ℝ)) * 2)))⁻¹)

/-- The full cover functional of one cell family. -/
def laneTotal (L m : ℤ)
    (g : HCPolySupport.TriadicCube d → Cutoff.CutoffSample d → ℝ)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  laneCoarse L m g omega +
    laneFineFactor (Int.toNat (m - L)) * laneCellSup L m g omega

theorem laneFineFactor_nonneg (r : ℕ) : 0 ≤ laneFineFactor r := by
  unfold laneFineFactor
  have hdiscount : 0 ≤ Ch02.geometricDiscount (1 / 8 : ℝ) 2 := by
    rw [Ch02.geometricDiscount_eq_old]
    exact (HCPolySupport.geometricDiscount_pos (by norm_num)).le
  have hgap : 0 ≤ (1 - (3 : ℝ) ^
      (-(((1 / 8 : ℝ) - (1 / 16 : ℝ)) * 2)))⁻¹ := by
    apply inv_nonneg.mpr
    have hlt := Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : (1 : ℝ) < 3)
      (by norm_num : -(((1 / 8 : ℝ) - (1 / 16 : ℝ)) * 2) < 0)
    linarith
  exact mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
    (mul_nonneg hdiscount hgap)

theorem geometricWeight_eighth_two_nonneg (ell : ℕ) :
    0 ≤ Ch02.geometricWeight (1 / 8 : ℝ) 2 ell := by
  rw [Ch02.geometricWeight_eq_old]
  exact HCPolySupport.geometricWeight_nonneg ell (by norm_num)

omit [NeZero d] in
theorem laneParentAverage_nonneg (L m : ℤ)
    {g : HCPolySupport.TriadicCube d → Cutoff.CutoffSample d → ℝ}
    (hg : ∀ R omega, 0 ≤ g R omega) (ell : ℕ)
    (omega : Cutoff.CutoffSample d) :
    0 ≤ laneParentAverage L m g ell omega := by
  unfold laneParentAverage
  refine Ch02.finsetSupReal_nonneg _ _ fun P _ => ?_
  exact descendantsAverage_nonneg P _ _ fun R _ => hg R omega

omit [NeZero d] in
private theorem laneCellSup_nonneg (L m : ℤ)
    {g : HCPolySupport.TriadicCube d → Cutoff.CutoffSample d → ℝ}
    (hg : ∀ R omega, 0 ≤ g R omega) (omega : Cutoff.CutoffSample d) :
    0 ≤ laneCellSup L m g omega := by
  unfold laneCellSup
  exact Ch02.finsetSupReal_nonneg _ _ fun R _ => hg R omega

omit [NeZero d] in
theorem laneTotal_nonneg (L m : ℤ)
    {g : HCPolySupport.TriadicCube d → Cutoff.CutoffSample d → ℝ}
    (hg : ∀ R omega, 0 ≤ g R omega) (omega : Cutoff.CutoffSample d) :
    0 ≤ laneTotal L m g omega := by
  unfold laneTotal laneCoarse
  refine add_nonneg (Finset.sum_nonneg fun ell _ => ?_) ?_
  · exact mul_nonneg (geometricWeight_eighth_two_nonneg ell)
      (laneParentAverage_nonneg L m hg ell omega)
  · exact mul_nonneg (laneFineFactor_nonneg _) (laneCellSup_nonneg L m hg omega)

/-! ## The deterministic cover, split over the two lanes -/

/-- The squared raw cutoff error of a scale-`L` cell, read at the cell
window `1/16`. -/
def laneCellErrorRawSq (M : ABKModel d) (L : ℤ)
    (R : HCPolySupport.TriadicCube d) (omega : Cutoff.CutoffSample d) : ℝ :=
  (Ch02.HomogenizationErrorOnCube R (1 / 16) .infinity (.finite 2)
    (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
    (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L))) ^ 2

/-- The layer-`ell` term of the weighted-depth expansion of the squared raw
error of the observation cube. -/
def laneErrorLayerRaw (M : ABKModel d) (L m : ℤ) (ell : ℕ)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  Ch02.geometricWeight (1 / 8) 2 ell *
    Ch02.maxDescendantNormalizedBlockResponseAtScale (originCube d m)
      (m - (ell : ℤ)) (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
      (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L))

private theorem normalizedBlockResponseMax_le_laneCellErrorRawSq
    (M : ABKModel d) (L : ℤ) (R : HCPolySupport.TriadicCube d)
    (omega : Cutoff.CutoffSample d) :
    Ch02.normalizedBlockResponseMax R
        (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
        (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L)) ≤
      laneCellErrorRawSq M L R omega := by
  let a := Cutoff.coefficientCutoffTriadicCoeffFamily M L omega
  let a0 : HCPolySupport.Mat d :=
    Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L)
  have hhead :=
    Ch02.normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale_of_le
      R le_rfl a a0
  have htail := maxDescendantNormalizedBlockResponseAtDepth_le_error_sq
    R (by norm_num : (0 : ℝ) < 1 / 16) a a0 0
  have hpow : Real.rpow (3 : ℝ) (0 : ℝ) = 1 := Real.rpow_zero _
  simp only [Nat.cast_zero, sub_zero, mul_zero, hpow, one_mul] at htail
  exact hhead.trans (by simpa only [laneCellErrorRawSq, a, a0] using htail)

private theorem laneErrorLayerRaw_coarse_le
    (M : ABKModel d) (L m : ℤ) (hLm : L ≤ m)
    (g h : HCPolySupport.TriadicCube d → Cutoff.CutoffSample d → ℝ)
    (ell : ℕ) (hell : ell < Int.toNat (m - L))
    (omega : Cutoff.CutoffSample d)
    (hcell : ∀ R : HCPolySupport.TriadicCube d, R.scale = L →
      laneCellErrorRawSq M L R omega ≤ g R omega + h R omega) :
    laneErrorLayerRaw M L m ell omega ≤
      Ch02.geometricWeight (1 / 8) 2 ell *
        (laneParentAverage L m g ell omega +
          laneParentAverage L m h ell omega) := by
  classical
  let a := Cutoff.coefficientCutoffTriadicCoeffFamily M L omega
  let a0 : HCPolySupport.Mat d :=
    Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L)
  have hr : ((Int.toNat (m - L) : ℕ) : ℤ) = m - L :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hLm)
  have hellZ : (ell : ℤ) < m - L := by
    rw [← hr]
    exact_mod_cast hell
  have hLell : L ≤ m - (ell : ℤ) := by omega
  have hscale : m - (ell : ℤ) ≤ m :=
    sub_le_self m (by exact_mod_cast Nat.zero_le ell)
  have hmax :
      Ch02.maxDescendantNormalizedBlockResponseAtScale (originCube d m)
          (m - (ell : ℤ)) a a0 ≤
        laneParentAverage L m g ell omega +
          laneParentAverage L m h ell omega := by
    unfold Ch02.maxDescendantNormalizedBlockResponseAtScale
    refine Ch02.finsetSupReal_le _
      (descendantsAtScale_nonempty (originCube d m) hscale) ?_
    intro P hP
    have hPscale : P.scale = m - (ell : ℤ) :=
      descendant_scale_eq_of_mem_descendantsAtScale hP
    have hj : ((Int.toNat (m - (ell : ℤ) - L) : ℕ) : ℤ) = P.scale - L := by
      rw [hPscale]
      exact Int.toNat_of_nonneg (sub_nonneg.mpr hLell)
    have hPavg := normalizedBlockResponseMax_le_descendantsAverage P
      (Int.toNat (m - (ell : ℤ) - L)) a a0
    have hdesc : descendantsAverage P (Int.toNat (m - (ell : ℤ) - L))
        (fun R => Ch02.normalizedBlockResponseMax R a a0) ≤
        descendantsAverage P (Int.toNat (m - (ell : ℤ) - L))
          (fun R => g R omega + h R omega) := by
      refine descendantsAverage_le_descendantsAverage P _ ?_
      intro R hR
      have hRscale : R.scale = L := by
        rw [scale_eq_sub_of_mem_descendantsAtDepth hR, hj]
        ring
      exact (normalizedBlockResponseMax_le_laneCellErrorRawSq M L R omega).trans
        (hcell R hRscale)
    have hsplit : descendantsAverage P (Int.toNat (m - (ell : ℤ) - L))
        (fun R => g R omega + h R omega) =
        descendantsAverage P (Int.toNat (m - (ell : ℤ) - L))
            (fun R => g R omega) +
          descendantsAverage P (Int.toNat (m - (ell : ℤ) - L))
            (fun R => h R omega) :=
      descendantsAverage_add P _ _ _
    have hsupg : descendantsAverage P (Int.toNat (m - (ell : ℤ) - L))
        (fun R => g R omega) ≤ laneParentAverage L m g ell omega := by
      unfold laneParentAverage
      exact le_finsetSupReal_of_mem _
        (fun P => descendantsAverage P (Int.toNat (m - (ell : ℤ) - L))
          (fun R => g R omega)) hP
    have hsuph : descendantsAverage P (Int.toNat (m - (ell : ℤ) - L))
        (fun R => h R omega) ≤ laneParentAverage L m h ell omega := by
      unfold laneParentAverage
      exact le_finsetSupReal_of_mem _
        (fun P => descendantsAverage P (Int.toNat (m - (ell : ℤ) - L))
          (fun R => h R omega)) hP
    calc Ch02.normalizedBlockResponseMax P a a0
        ≤ descendantsAverage P (Int.toNat (m - (ell : ℤ) - L))
            (fun R => g R omega + h R omega) := hPavg.trans hdesc
      _ = descendantsAverage P (Int.toNat (m - (ell : ℤ) - L))
              (fun R => g R omega) +
            descendantsAverage P (Int.toNat (m - (ell : ℤ) - L))
              (fun R => h R omega) := hsplit
      _ ≤ laneParentAverage L m g ell omega +
            laneParentAverage L m h ell omega := add_le_add hsupg hsuph
  unfold laneErrorLayerRaw
  exact mul_le_mul_of_nonneg_left hmax (geometricWeight_eighth_two_nonneg ell)

private theorem laneErrorLayerRaw_fine_le
    (M : ABKModel d) (L m : ℤ) (hLm : L ≤ m)
    (g h : HCPolySupport.TriadicCube d → Cutoff.CutoffSample d → ℝ)
    (n : ℕ) (omega : Cutoff.CutoffSample d)
    (hcell : ∀ R : HCPolySupport.TriadicCube d, R.scale = L →
      laneCellErrorRawSq M L R omega ≤ g R omega + h R omega) :
    laneErrorLayerRaw M L m (Int.toNat (m - L) + n) omega ≤
      Ch02.geometricWeight (1 / 8) 2 (Int.toNat (m - L) + n) *
        Real.rpow 3 (2 * (1 / 16 : ℝ) * (n : ℝ)) *
          (laneCellSup L m g omega + laneCellSup L m h omega) := by
  classical
  let a := Cutoff.coefficientCutoffTriadicCoeffFamily M L omega
  let a0 : HCPolySupport.Mat d :=
    Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L)
  let r : ℕ := Int.toNat (m - L)
  have hr : (r : ℤ) = m - L := by
    dsimp [r]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hLm)
  have hscale : m - ((r + n : ℕ) : ℤ) = L - (n : ℤ) := by
    rw [show ((r + n : ℕ) : ℤ) = (r : ℤ) + (n : ℤ) by norm_num, hr]
    ring
  have hpoint : ∀ R ∈ descendantsAtScale (originCube d m) L,
      Ch02.maxDescendantNormalizedBlockResponseAtScale R (L - (n : ℤ)) a a0 ≤
        Real.rpow 3 (2 * (1 / 16 : ℝ) * (n : ℝ)) *
          (laneCellSup L m g omega + laneCellSup L m h omega) := by
    intro R hR
    have hRscale : R.scale = L := descendant_scale_eq_of_mem_descendantsAtScale hR
    have hraw := maxDescendantNormalizedBlockResponseAtDepth_le_error_sq
      R (by norm_num : (0 : ℝ) < 1 / 16) a a0 n
    have hraw' : Ch02.maxDescendantNormalizedBlockResponseAtScale R
        (L - (n : ℤ)) a a0 ≤
        Real.rpow 3 (2 * (1 / 16 : ℝ) * (n : ℝ)) *
          laneCellErrorRawSq M L R omega := by
      simpa only [hRscale, laneCellErrorRawSq, a, a0] using hraw
    refine hraw'.trans (mul_le_mul_of_nonneg_left ?_
      (Real.rpow_nonneg (by norm_num) _))
    have hgR : g R omega ≤ laneCellSup L m g omega := by
      unfold laneCellSup
      exact le_finsetSupReal_of_mem _ (fun R => g R omega) hR
    have hhR : h R omega ≤ laneCellSup L m h omega := by
      unfold laneCellSup
      exact le_finsetSupReal_of_mem _ (fun R => h R omega) hR
    exact (hcell R hRscale).trans (add_le_add hgR hhR)
  have hroot : Ch02.maxDescendantNormalizedBlockResponseAtScale (originCube d m)
      (m - ((r + n : ℕ) : ℤ)) a a0 ≤
      Real.rpow 3 (2 * (1 / 16 : ℝ) * (n : ℝ)) *
        (laneCellSup L m g omega + laneCellSup L m h omega) := by
    rw [hscale]
    unfold Ch02.maxDescendantNormalizedBlockResponseAtScale
    refine Ch02.finsetSupReal_le _
      (descendantsAtScale_nonempty (originCube d m)
        ((sub_le_self L (by exact_mod_cast Nat.zero_le n)).trans hLm)) ?_
    intro S hS
    obtain ⟨R, hR, hSR⟩ := exists_mem_descendantsAtScale_split
      (Q := originCube d m) (k := L) (l := L - (n : ℤ)) hLm
      (sub_le_self L (by exact_mod_cast Nat.zero_le n)) hS
    have hSRle :=
      Ch02.normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale
        a a0 hSR
    exact hSRle.trans (hpoint R hR)
  have hweight : 0 ≤ Ch02.geometricWeight (1 / 8) 2 (r + n) :=
    geometricWeight_eighth_two_nonneg (r + n)
  have hmul := mul_le_mul_of_nonneg_left hroot hweight
  simpa only [laneErrorLayerRaw, r, a, a0, mul_assoc] using hmul

/-! ## The geometric series of the fine tail -/

omit [NeZero d] in
private theorem collapseSummand {s t q : ℝ} (n : ℕ) :
    Ch02.geometricWeight t q n *
        ((3 : ℝ) ^ (2 * s * (n : ℝ))) ^ (q / 2) =
      Ch02.geometricDiscount t q *
        ((3 : ℝ) ^ (-((t - s) * q))) ^ n := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  unfold Ch02.geometricWeight
  simp only [Real.rpow_eq_pow]
  rw [mul_assoc, ← Real.rpow_mul h3.le,
    ← Real.rpow_natCast ((3 : ℝ) ^ (-((t - s) * q))) n,
    ← Real.rpow_mul h3.le, ← Real.rpow_add h3]
  congr 2
  ring

omit [NeZero d] in
private theorem summable_geometricWeight_rpow {s t q : ℝ}
    (hst : s < t) (hq : 0 < q) :
    Summable (fun n : ℕ => Ch02.geometricWeight t q n *
      ((3 : ℝ) ^ (2 * s * (n : ℝ))) ^ (q / 2)) := by
  refine (Summable.congr ?_
    (fun n => (collapseSummand (s := s) (t := t) (q := q) n).symm))
  exact (summable_geometric_of_lt_one
    (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (neg_neg_iff_pos.mpr (mul_pos (by linarith) hq)))).mul_left _

omit [NeZero d] in
private theorem tsum_geometricWeight_rpow {s t q : ℝ}
    (hst : s < t) (hq : 0 < q) :
    (∑' n : ℕ, Ch02.geometricWeight t q n *
        ((3 : ℝ) ^ (2 * s * (n : ℝ))) ^ (q / 2)) =
      Ch02.geometricDiscount t q *
        (1 - (3 : ℝ) ^ (-((t - s) * q)))⁻¹ := by
  have hrPos : 0 < (3 : ℝ) ^ (-((t - s) * q)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrLt : (3 : ℝ) ^ (-((t - s) * q)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (neg_neg_iff_pos.mpr (mul_pos (by linarith) hq))
  rw [tsum_congr (fun n => collapseSummand (s := s) (t := t) (q := q) n),
    tsum_mul_left, tsum_geometric_of_lt_one hrPos.le hrLt]

private theorem laneFineTailRaw_le
    (M : ABKModel d) (L m : ℤ) (hLm : L ≤ m)
    (g h : HCPolySupport.TriadicCube d → Cutoff.CutoffSample d → ℝ)
    (omega : Cutoff.CutoffSample d)
    (hcell : ∀ R : HCPolySupport.TriadicCube d, R.scale = L →
      laneCellErrorRawSq M L R omega ≤ g R omega + h R omega) :
    (∑' n : ℕ, laneErrorLayerRaw M L m (Int.toNat (m - L) + n) omega) ≤
      laneFineFactor (Int.toNat (m - L)) *
        (laneCellSup L m g omega + laneCellSup L m h omega) := by
  let Q := originCube d m
  let a := Cutoff.coefficientCutoffTriadicCoeffFamily M L omega
  let a0 : HCPolySupport.Mat d :=
    Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L)
  let r : ℕ := Int.toNat (m - L)
  let B : ℝ := laneCellSup L m g omega + laneCellSup L m h omega
  let f : ℕ → ℝ := fun n => laneErrorLayerRaw M L m (r + n) omega
  have hfull :=
    Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
      Q a a0 (by norm_num : (0 : ℝ) < 1 / 8)
  have hf : Summable f := by
    have htail := hfull.comp_injective (add_left_injective r)
    simpa only [f, laneErrorLayerRaw, Q, a, a0, r, originCube,
      Function.comp_apply, Nat.add_comm] using! htail
  have hpoint : ∀ n, f n ≤ Ch02.geometricWeight (1 / 8) 2 (r + n) *
      Real.rpow 3 (2 * (1 / 16 : ℝ) * (n : ℝ)) * B := by
    intro n
    simpa only [f, B, r] using
      laneErrorLayerRaw_fine_le M L m hLm g h n omega hcell
  let A : ℝ := Real.rpow 3 ((1 / 8 : ℝ) * 2 * (r : ℝ))
  have hA : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
  have hweightShift (n : ℕ) :
      Ch02.geometricWeight (1 / 8) 2 (r + n) =
        A⁻¹ * Ch02.geometricWeight (1 / 8) 2 n := by
    calc
      Ch02.geometricWeight (1 / 8) 2 (r + n) =
          Ch02.geometricWeight (1 / 8) 2 (n + r) := by rw [Nat.add_comm]
      _ = (A⁻¹ * A) * Ch02.geometricWeight (1 / 8) 2 (n + r) := by
        rw [inv_mul_cancel₀ hA.ne', one_mul]
      _ = A⁻¹ * (A * Ch02.geometricWeight (1 / 8) 2 (n + r)) := by ring
      _ = A⁻¹ * Ch02.geometricWeight (1 / 8) 2 n := by
        congr 1
        simpa only [A, Ch02.geometricWeight_eq_old] using
          (HCPolySupport.geometricWeight_shift (s := (1 / 8 : ℝ)) (q := 2)
            r n).symm
  have hbase : Summable (fun n : ℕ => Ch02.geometricWeight (1 / 8) 2 n *
      Real.rpow 3 (2 * (1 / 16 : ℝ) * (n : ℝ))) := by
    simpa only [show (2 / 2 : ℝ) = 1 by norm_num, Real.rpow_one] using!
      (summable_geometricWeight_rpow (s := (1 / 16 : ℝ)) (t := (1 / 8 : ℝ))
        (q := 2) (by norm_num) (by norm_num))
  have hmajor : Summable (fun n : ℕ => Ch02.geometricWeight (1 / 8) 2 (r + n) *
      Real.rpow 3 (2 * (1 / 16 : ℝ) * (n : ℝ)) * B) := by
    refine ((hbase.mul_left (A⁻¹ * B)).congr fun n => ?_)
    rw [hweightShift]
    ring
  have hsum := Summable.tsum_le_tsum hpoint hf hmajor
  have hclosed : (∑' n : ℕ, Ch02.geometricWeight (1 / 8) 2 n *
      Real.rpow 3 (2 * (1 / 16 : ℝ) * (n : ℝ))) =
      Ch02.geometricDiscount (1 / 8 : ℝ) 2 *
        (1 - (3 : ℝ) ^ (-(((1 / 8 : ℝ) - (1 / 16 : ℝ)) * 2)))⁻¹ := by
    simpa only [show (2 / 2 : ℝ) = 1 by norm_num, Real.rpow_one] using!
      (tsum_geometricWeight_rpow (s := (1 / 16 : ℝ)) (t := (1 / 8 : ℝ))
        (q := 2) (by norm_num) (by norm_num))
  have hmajorEq :
      (∑' n : ℕ, Ch02.geometricWeight (1 / 8) 2 (r + n) *
        Real.rpow 3 (2 * (1 / 16 : ℝ) * (n : ℝ)) * B) =
      A⁻¹ * (Ch02.geometricDiscount (1 / 8 : ℝ) 2 *
        (1 - (3 : ℝ) ^ (-(((1 / 8 : ℝ) - (1 / 16 : ℝ)) * 2)))⁻¹) * B := by
    calc
      (∑' n : ℕ, Ch02.geometricWeight (1 / 8) 2 (r + n) *
          Real.rpow 3 (2 * (1 / 16 : ℝ) * (n : ℝ)) * B) =
          (A⁻¹ * B) * ∑' n : ℕ, Ch02.geometricWeight (1 / 8) 2 n *
            Real.rpow 3 (2 * (1 / 16 : ℝ) * (n : ℝ)) := by
        rw [← tsum_mul_left]
        refine tsum_congr fun n => ?_
        rw [hweightShift]
        ring
      _ = A⁻¹ * (Ch02.geometricDiscount (1 / 8 : ℝ) 2 *
          (1 - (3 : ℝ) ^ (-(((1 / 8 : ℝ) - (1 / 16 : ℝ)) * 2)))⁻¹) * B := by
        rw [hclosed]
        ring
  have hAinv : A⁻¹ = Real.rpow 3 (-(2 * (1 / 8 : ℝ) * (r : ℝ))) := by
    have hneg : Real.rpow 3 (-(2 * (1 / 8 : ℝ) * (r : ℝ))) =
        (Real.rpow 3 ((1 / 8 : ℝ) * 2 * (r : ℝ)))⁻¹ := by
      rw [show (-(2 * (1 / 8 : ℝ) * (r : ℝ))) = -((1 / 8 : ℝ) * 2 * (r : ℝ)) by
        ring]
      exact Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3) _
    dsimp only [A]
    rw [hneg]
  rw [hmajorEq] at hsum
  calc (∑' n : ℕ, laneErrorLayerRaw M L m (Int.toNat (m - L) + n) omega)
      = ∑' n : ℕ, f n := by rfl
    _ ≤ A⁻¹ * (Ch02.geometricDiscount (1 / 8 : ℝ) 2 *
        (1 - (3 : ℝ) ^ (-(((1 / 8 : ℝ) - (1 / 16 : ℝ)) * 2)))⁻¹) * B := hsum
    _ = laneFineFactor (Int.toNat (m - L)) *
        (laneCellSup L m g omega + laneCellSup L m h omega) := by
      rw [hAinv]
      rfl

theorem cutoffHomogenizationErrorRaw_sq_le_laneTotal_add
    (M : ABKModel d) (L m : ℤ) (hLm : L ≤ m)
    (g h : HCPolySupport.TriadicCube d → Cutoff.CutoffSample d → ℝ)
    (omega : Cutoff.CutoffSample d)
    (hcell : ∀ R : HCPolySupport.TriadicCube d, R.scale = L →
      laneCellErrorRawSq M L R omega ≤ g R omega + h R omega) :
    (Observable.cutoffHomogenizationErrorRaw M L m (1 / 8)
      (Annealed.sigmaBar M L) omega) ^ 2 ≤
      laneTotal L m g omega + laneTotal L m h omega := by
  let r : ℕ := Int.toNat (m - L)
  let f : ℕ → ℝ := fun ell => laneErrorLayerRaw M L m ell omega
  let Q := originCube d m
  let a := Cutoff.coefficientCutoffTriadicCoeffFamily M L omega
  let a0 : HCPolySupport.Mat d :=
    Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L)
  have hsum : Summable f := by
    simpa only [f, laneErrorLayerRaw, Q, a, a0, originCube] using
      Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
        Q a a0 (by norm_num : (0 : ℝ) < 1 / 8)
  have hsq :
      (Observable.cutoffHomogenizationErrorRaw M L m (1 / 8)
        (Annealed.sigmaBar M L) omega) ^ 2 = ∑' ell : ℕ, f ell := by
    rw [Observable.cutoffHomogenizationErrorRaw_characterization]
    simpa only [f, laneErrorLayerRaw, Q, a, a0, originCube] using
      Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q
        (by norm_num : (0 : ℝ) < 1 / 8) a a0
  have hsplit :
      (Observable.cutoffHomogenizationErrorRaw M L m (1 / 8)
        (Annealed.sigmaBar M L) omega) ^ 2 =
        (∑ ell ∈ Finset.range r, f ell) +
          ∑' n : ℕ, laneErrorLayerRaw M L m (r + n) omega := by
    rw [hsq]
    symm
    simpa only [r, f, Nat.add_comm] using hsum.sum_add_tsum_nat_add r
  have hprefix : (∑ ell ∈ Finset.range r, f ell) ≤
      laneCoarse L m g omega + laneCoarse L m h omega := by
    have hstep : ∀ ell ∈ Finset.range r, f ell ≤
        Ch02.geometricWeight (1 / 8) 2 ell * laneParentAverage L m g ell omega +
          Ch02.geometricWeight (1 / 8) 2 ell *
            laneParentAverage L m h ell omega := by
      intro ell hell
      have := laneErrorLayerRaw_coarse_le M L m hLm g h ell
        (by simpa only [r] using Finset.mem_range.mp hell) omega hcell
      simpa only [f, mul_add] using this
    calc (∑ ell ∈ Finset.range r, f ell)
        ≤ ∑ ell ∈ Finset.range r,
            (Ch02.geometricWeight (1 / 8) 2 ell *
                laneParentAverage L m g ell omega +
              Ch02.geometricWeight (1 / 8) 2 ell *
                laneParentAverage L m h ell omega) :=
          Finset.sum_le_sum hstep
      _ = laneCoarse L m g omega + laneCoarse L m h omega := by
          unfold laneCoarse
          simp only [r, Finset.sum_add_distrib]
  have hfine := laneFineTailRaw_le M L m hLm g h omega hcell
  have hfinesplit : laneFineFactor r *
      (laneCellSup L m g omega + laneCellSup L m h omega) =
      laneFineFactor r * laneCellSup L m g omega +
        laneFineFactor r * laneCellSup L m h omega := by ring
  rw [hsplit]
  unfold laneTotal
  have hfine' : (∑' n : ℕ, laneErrorLayerRaw M L m (r + n) omega) ≤
      laneFineFactor r * laneCellSup L m g omega +
        laneFineFactor r * laneCellSup L m h omega := by
    simpa only [r, hfinesplit] using hfine
  linarith [hprefix, hfine']

end

end Algsuperdiff.Section3.Provider.Homogenization.TwoLaneCoverInternal
