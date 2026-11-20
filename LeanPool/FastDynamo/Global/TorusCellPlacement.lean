/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.CellGeometry

/-!
# Large-index placement of the transverse cells

This module discharges the large-`K0` choices in Section 3.3 that concern
the transverse geometry.  The centres and discs are represented in the fixed
Euclidean coordinate square of the paper (see `placementChart`).  The torus API uses the
quotient presentation of `UnitAddTorus` and exposes no local chart embedding,
so the result below is the exact Euclidean-chart placement certificate that
the quotient/chart bridge transports to the transverse torus.

No global velocity, cutoff, or infinite sum is defined here.

That bridge is `Global/TorusChartWeakTransfer.lean`, and the global velocity it feeds is
built in `Global/TorusFullVelocityConcrete.lean`; see `FastDynamo/MainTheorem.lean`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter Metric Set

namespace ScaleFamily

variable {p : LocalSeedParameters} {r : ScaleRatios p}

/-! ## The base-index funnel -/

/--
**The base-index funnel, one target.**  For every nonnegative support radius, every positive
target for the initial buffer radius `R_0 = sqrt (ell_0)` and every prescribed lower bound `M`
on `K_0`, there is a scale family with `K_0 ≥ M` satisfying the chart packing
`eq:chart-packing`, the core containment `eq:local-support-in-buffer`,
and `R_0 < target`.

This realises the final choice of `K_0` in the paragraph collecting the parameter choices at
the end of §7.2: every analytic threshold on `K_0` is monotone, because
`R_0 = sqrt (k_*/K_0)` decreases in `K_0` and `d(K_0) = sup_n ell_n/R_n = R_0`.  The paper
writes `R_0 = 1/sqrt K_0`: the Lean keeps `k_*` as a parameter, the paper takes `k_* = 1`.
For `eq:local-support-in-buffer` the paper (§3.3) gives the explicit sufficient threshold
`K_0 > (10 R_v)^2`; the Lean proves existence of a large `K_0` instead, through
`R_0 < 1/(10 (supportRadius + 1))`.
-/
theorem exists_ge_chartPacking_supportFit_bufferRadius_zero_lt
    (supportRadius target : ℝ) (hsupportRadius : 0 ≤ supportRadius) (htarget : 0 < target)
    (M : ℕ) :
    ∃ f : ScaleFamily r,
      M ≤ f.K0 ∧
      f.chartPackingQuantity < 1 / 4 ∧
      (∀ n, supportRadius * f.ell n < f.bufferRadius n / 10) ∧
      f.bufferRadius 0 < target := by
  classical
  set c : ℝ := Real.sqrt r.q⁻¹ with hcdef
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hc1 : c < 1 := by
    simpa [hcdef] using
      Real.sqrt_lt_sqrt (inv_nonneg.mpr r.q_pos.le) (inv_lt_one_of_one_lt₀ r.one_lt_q)
  set B : ℝ := 4 / (1 - c) + 1 with hBdef
  have hBpos : 0 < B := by
    rw [hBdef]
    have : 0 < 1 - c := by linarith
    positivity
  set t : ℝ := min (min ((1 / 4) / B) (1 / (10 * (supportRadius + 1)))) target with htdef
  have htpos : 0 < t := by
    rw [htdef]
    refine lt_min (lt_min ?_ ?_) htarget
    · positivity
    · positivity
  obtain ⟨K, hK⟩ := exists_nat_gt ((p.kStar : ℝ) / t ^ 2)
  obtain ⟨f, hfKM⟩ := ScaleFamily.exists_ge r (max K M)
  have hKf : K ≤ f.K0 := (Nat.le_max_left K M).trans hfKM
  have hMf : M ≤ f.K0 := (Nat.le_max_right K M).trans hfKM
  have hfKpos : 0 < (f.K0 : ℝ) := Nat.cast_pos.mpr f.K0_pos
  have hKfReal : (K : ℝ) ≤ (f.K0 : ℝ) := by exact_mod_cast hKf
  have hratio : (p.kStar : ℝ) / f.K0 < t ^ 2 := by
    rw [div_lt_iff₀ hfKpos]
    calc
      (p.kStar : ℝ) < (K : ℝ) * t ^ 2 := (div_lt_iff₀ (by positivity)).mp hK
      _ = t ^ 2 * (K : ℝ) := by ring
      _ ≤ t ^ 2 * (f.K0 : ℝ) := mul_le_mul_of_nonneg_left hKfReal (sq_nonneg _)
  have hR0 : f.bufferRadius 0 < t := by
    rw [f.bufferRadius_zero_formula]
    exact (Real.sqrt_lt' htpos).2 hratio
  have hgeom :
      4 * (f.bufferRadius 0 / (1 - f.bufferContraction)) + f.bufferRadius 0 < 1 / 4 := by
    have hcf : f.bufferContraction = c := rfl
    rw [hcf]
    calc
      4 * (f.bufferRadius 0 / (1 - c)) + f.bufferRadius 0 = f.bufferRadius 0 * B := by
        rw [hBdef]; ring
      _ < t * B := mul_lt_mul_of_pos_right hR0 hBpos
      _ ≤ ((1 / 4) / B) * B := by
        gcongr
        exact (min_le_left _ _).trans (min_le_left _ _)
      _ = 1 / 4 := by field_simp
  have hsmall : 10 * supportRadius * f.bufferRadius 0 < 1 := by
    calc
      10 * supportRadius * f.bufferRadius 0 ≤ 10 * supportRadius * t :=
        mul_le_mul_of_nonneg_left hR0.le (by positivity)
      _ ≤ 10 * supportRadius * (1 / (10 * (supportRadius + 1))) := by
        gcongr
        exact (min_le_left _ _).trans (min_le_right _ _)
      _ < 1 := by
        rw [show 10 * supportRadius * (1 / (10 * (supportRadius + 1))) =
            supportRadius / (supportRadius + 1) by field_simp]
        exact (div_lt_one₀ (by linarith : 0 < supportRadius + 1)).2 (by linarith)
  exact ⟨f, hMf, f.chartPacking_of_geometric_bound hgeom,
    fun n ↦ f.supportScale_lt_tenth_buffer hsupportRadius hsmall n,
    hR0.trans_le ((min_le_right _ _).trans_eq rfl)⟩

/-- For every nonnegative local support radius, a sufficiently large initial
Fourier index simultaneously satisfies the paper's chart-packing bound
and the local-core support fit in every buffer.  It is the funnel above with no lower bound on
`K_0` and no target for `R_0`. -/
theorem exists_largeK0_chartPacking_and_supportFit
    (supportRadius : ℝ) (hsupportRadius : 0 ≤ supportRadius) :
    ∃ f : ScaleFamily r,
      f.chartPackingQuantity < 1 / 4 ∧
      ∀ n, supportRadius * f.ell n < f.bufferRadius n / 10 := by
  obtain ⟨f, -, hpack, hfit, -⟩ :=
    exists_ge_chartPacking_supportFit_bufferRadius_zero_lt (r := r) supportRadius 1
      hsupportRadius one_pos 0
  exact ⟨f, hpack, hfit⟩

/-! ## Euclidean chart certificate -/

/-- The open coordinate square used for all transverse buffer discs.  The paper (§3.3) uses
`(-1/4, 1/4) × (1/4, 3/4)`; since every buffer disc lies at positive first coordinate, the Lean
works with its right half `(0, 1/4) × (1/4, 3/4)`. -/
def placementChart : Set (ℝ × ℝ) :=
  Set.Ioo (0 : ℝ) (1 / 4) ×ˢ Set.Ioo (1 / 4) (3 / 4)

/-- The `n`th transverse buffer disc, expressed in the Euclidean chart
coordinates. -/
def bufferDisk (f : ScaleFamily r) (n : ℕ) : Set (ℝ × ℝ) :=
  ball (f.cellCenter n) (f.bufferRadius n)

/-- The Euclidean disc containing the rescaled local velocity and its first
derivatives when their whole-plane support radius is `supportRadius`. -/
def localCoreDisk (f : ScaleFamily r) (supportRadius : ℝ) (n : ℕ) :
    Set (ℝ × ℝ) :=
  ball (f.cellCenter n) (supportRadius * f.ell n)

/-- The centres stay strictly to the right of the chart's accumulation edge. -/
theorem cellCenterCoordinate_pos (f : ScaleFamily r) (n : ℕ) :
    0 < f.cellCenterCoordinate n := by
  unfold cellCenterCoordinate
  rw [f.bufferTail_recursion n]
  nlinarith [f.bufferRadius_pos n, f.bufferTail_nonneg (n + 1)]

/-- Under the chart-packing bound `4 Σ_n R_n + R_0 < 1/4` (`eq:chart-packing`) the
largest buffer radius already satisfies `R_0 < 1/4`. -/
theorem bufferRadius_zero_lt_quarter
    (f : ScaleFamily r) (hpack : f.chartPackingQuantity < 1 / 4) :
    f.bufferRadius 0 < 1 / 4 := by
  have hsum : 0 ≤ ∑' n : ℕ, f.bufferRadius n :=
    tsum_nonneg fun n ↦ f.bufferRadius_nonneg n
  unfold chartPackingQuantity at hpack
  linarith

/-- Chart packing puts every buffer disc inside the fixed Euclidean chart. -/
theorem bufferDisk_subset_placementChart (f : ScaleFamily r)
    (hpack : f.chartPackingQuantity < 1 / 4) (n : ℕ) :
    f.bufferDisk n ⊆ placementChart := by
  intro z hz
  have hdist : dist z (f.cellCenter n) < f.bufferRadius n := hz
  have hfst_dist : dist z.1 (f.cellCenter n).1 < f.bufferRadius n := by
    calc
      dist z.1 (f.cellCenter n).1 ≤ dist z (f.cellCenter n) := by
        rw [Prod.dist_eq]
        exact le_max_left _ _
      _ < f.bufferRadius n := hdist
  have hsnd_dist : dist z.2 (f.cellCenter n).2 < f.bufferRadius n := by
    calc
      dist z.2 (f.cellCenter n).2 ≤ dist z (f.cellCenter n) := by
        rw [Prod.dist_eq]
        exact le_max_right _ _
      _ < f.bufferRadius n := hdist
  have hfst_abs : |z.1 - f.cellCenterCoordinate n| < f.bufferRadius n := by
    simpa [Real.dist_eq, f.cellCenter_fst] using hfst_dist
  have hsnd_abs : |z.2 - (1 / 2 : ℝ)| < f.bufferRadius n := by
    simpa [Real.dist_eq, f.cellCenter_snd] using hsnd_dist
  have hleft : f.bufferRadius n < f.cellCenterCoordinate n := by
    rw [f.cellCenterCoordinate_recursion n]
    nlinarith [f.bufferRadius_pos n, (f.cellCenterCoordinate_pos (n + 1)).le]
  have hright : f.cellCenterCoordinate n + f.bufferRadius n < 1 / 4 := by
    have hcenter : f.cellCenterCoordinate n ≤ f.cellCenterCoordinate 0 :=
      f.antitone_cellCenterCoordinate (Nat.zero_le n)
    have hradius : f.bufferRadius n ≤ f.bufferRadius 0 :=
      f.bufferRadius_le_bufferRadius_zero n
    have htotal : f.cellCenterCoordinate 0 + f.bufferRadius 0 =
        f.chartPackingQuantity := by
      simp [cellCenterCoordinate, bufferTail, chartPackingQuantity]
    calc
      f.cellCenterCoordinate n + f.bufferRadius n ≤
          f.cellCenterCoordinate 0 + f.bufferRadius 0 :=
        add_le_add hcenter hradius
      _ = f.chartPackingQuantity := htotal
      _ < 1 / 4 := hpack
  have hRquarter : f.bufferRadius n < 1 / 4 :=
    (f.bufferRadius_le_bufferRadius_zero n).trans_lt
      (f.bufferRadius_zero_lt_quarter hpack)
  rw [placementChart, Set.mem_prod]
  constructor
  · rw [Set.mem_Ioo]
    have hbounds := abs_lt.mp hfst_abs
    constructor <;> linarith
  · rw [Set.mem_Ioo]
    have hbounds := abs_lt.mp hsnd_abs
    constructor <;> linarith

/-- Distinct buffer discs are disjoint. -/
theorem disjoint_bufferDisk (f : ScaleFamily r) {n m : ℕ} (hnm : n < m) :
    Disjoint (f.bufferDisk n) (f.bufferDisk m) := by
  rw [Set.disjoint_left]
  intro z hzn hzm
  have hzn' : dist z (f.cellCenter n) < f.bufferRadius n := hzn
  have hzm' : dist z (f.cellCenter m) < f.bufferRadius m := hzm
  have htriangle : dist (f.cellCenter n) (f.cellCenter m) <
      f.bufferRadius n + f.bufferRadius m := by
    calc
      dist (f.cellCenter n) (f.cellCenter m) ≤
          dist (f.cellCenter n) z + dist z (f.cellCenter m) :=
        dist_triangle _ _ _
      _ = dist z (f.cellCenter n) + dist z (f.cellCenter m) := by
        rw [dist_comm (f.cellCenter n) z]
      _ < f.bufferRadius n + f.bufferRadius m := add_lt_add hzn' hzm'
  have hcenterdist : dist (f.cellCenter n) (f.cellCenter m) =
      |f.cellCenterCoordinate n - f.cellCenterCoordinate m| := by
    rw [Prod.dist_eq]
    simp [cellCenter, Real.dist_eq]
  rw [hcenterdist] at htriangle
  linarith [f.bufferRadii_sum_lt_centerCoordinate_gap hnm]

/-- The local-flow core fits strictly inside its corresponding buffer disc. -/
theorem localCoreDisk_subset_bufferDisk (f : ScaleFamily r)
    {supportRadius : ℝ}
    (hfit : ∀ n, supportRadius * f.ell n < f.bufferRadius n / 10)
    (n : ℕ) :
    f.localCoreDisk supportRadius n ⊆ f.bufferDisk n := by
  intro z hz
  have hdist : dist z (f.cellCenter n) < supportRadius * f.ell n := hz
  have hsmall : supportRadius * f.ell n < f.bufferRadius n := by
    have := hfit n
    nlinarith [f.bufferRadius_pos n]
  exact hdist.trans hsmall

/-- A complete placement certificate for the support radius supplied by a
helical local profile.  It contains no arbitrary packing hypothesis. -/
structure TorusCellPlacement (supportRadius : ℝ) where
  /-- The scale family whose cells are placed in the fixed torus chart. -/
  scaleFamily : ScaleFamily r
  chartPacking : scaleFamily.chartPackingQuantity < 1 / 4
  supportFit : ∀ n,
    supportRadius * scaleFamily.ell n < scaleFamily.bufferRadius n / 10

namespace TorusCellPlacement

variable {supportRadius : ℝ}

/-- A sufficiently large initial Fourier index always yields the required
placement certificate. -/
theorem nonempty (hsupportRadius : 0 ≤ supportRadius) :
    Nonempty (TorusCellPlacement (r := r) supportRadius) := by
  obtain ⟨f, hpack, hfit⟩ :=
    ScaleFamily.exists_largeK0_chartPacking_and_supportFit
      (r := r) supportRadius hsupportRadius
  exact ⟨⟨f, hpack, hfit⟩⟩

/-- A placement made for a larger support radius is also a placement, on the
same scale family, for every smaller support radius.  This is what lets the parameter chain
place the cells once, at the joint radius `R_v = max (1 + h) L_*` (a choice of the paper's
radius `R_v ≥ L_*` of §3.3),
and read the certificate back at the profile radius `1 + h` that the velocity layer is
parameterised by. -/
def restrictSupportRadius {smallRadius largeRadius : ℝ}
    (P : TorusCellPlacement (r := r) largeRadius)
    (hsmall : smallRadius ≤ largeRadius) :
    TorusCellPlacement (r := r) smallRadius where
  scaleFamily := P.scaleFamily
  chartPacking := P.chartPacking
  supportFit := fun n ↦ by
    refine lt_of_le_of_lt ?_ (P.supportFit n)
    exact mul_le_mul_of_nonneg_right hsmall (P.scaleFamily.ell_pos n).le

/-- Weakening a placement to a smaller support radius keeps the very same scale family, so no new
geometry is introduced by the restriction.
-/
@[simp] theorem restrictSupportRadius_scaleFamily
    {smallRadius largeRadius : ℝ}
    (P : TorusCellPlacement (r := r) largeRadius)
    (hsmall : smallRadius ≤ largeRadius) :
    (P.restrictSupportRadius hsmall).scaleFamily = P.scaleFamily :=
  rfl

/-- Every placed buffer disc lies inside the fixed Euclidean coordinate square `placementChart`,
by the placement's chart-packing field (`eq:chart-packing`). -/
theorem bufferDisk_subset_chart (P : TorusCellPlacement (r := r) supportRadius)
    (n : ℕ) : P.scaleFamily.bufferDisk n ⊆ placementChart :=
  P.scaleFamily.bufferDisk_subset_placementChart P.chartPacking n

/-- Distinct placed buffer discs are pairwise disjoint, the centres being separated by more than
the sum of the radii. -/
theorem disjoint_bufferDisk (P : TorusCellPlacement (r := r) supportRadius)
    {n m : ℕ} (hnm : n < m) :
    Disjoint (P.scaleFamily.bufferDisk n) (P.scaleFamily.bufferDisk m) :=
  P.scaleFamily.disjoint_bufferDisk hnm

/-- The local core disc of a placed cell, of radius `supportRadius * ell n`, lies inside that
cell's buffer disc, by the placement's support-fit field
(`eq:local-support-in-buffer`). -/
theorem localCoreDisk_subset_bufferDisk
    (P : TorusCellPlacement (r := r) supportRadius)
    (n : ℕ) :
    P.scaleFamily.localCoreDisk supportRadius n ⊆
      P.scaleFamily.bufferDisk n :=
  P.scaleFamily.localCoreDisk_subset_bufferDisk P.supportFit n

/-- The matching-cell selection remains compatible with the fixed placement:
the selected local core is inside its chart-contained, pairwise-disjoint
buffer disc. -/
theorem exists_matchingCell_with_placedCore
    (P : TorusCellPlacement (r := r) supportRadius)
    {epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hupper : epsilon ≤ P.scaleFamily.epsilon0) :
    ∃ c : MatchingCell P.scaleFamily epsilon,
      P.scaleFamily.localCoreDisk supportRadius c.index ⊆
        P.scaleFamily.bufferDisk c.index ∧
      P.scaleFamily.bufferDisk c.index ⊆ placementChart := by
  obtain ⟨c⟩ := P.scaleFamily.exists_matchingCell hepsilon hupper
  exact ⟨c, P.localCoreDisk_subset_bufferDisk c.index,
    P.bufferDisk_subset_chart c.index⟩

end TorusCellPlacement

end ScaleFamily

end

end FastDynamo
