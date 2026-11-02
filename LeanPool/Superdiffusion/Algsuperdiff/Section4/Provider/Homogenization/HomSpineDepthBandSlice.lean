/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineDepthBandArith

/-!
# HomSpineDepthBandSlice

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The straddling band, its slices and its mass

## What this file is for

The two measure-theoretic ingredients of the single-depth Gagliardo reduction,
one per variable.

* `straddleBand Q j k v` — the set of pairs `(x,y)` inside `Q` on which the
  depth-`j` slice JUMPS and whose sup distance sits in the triadic band
  `[3^{-(k+1)}·L, 3^{-k}·L)`, `L = cubeScaleFactor Q`.  It is measurable and
  symmetric.
* `measure_straddleBandSlice_le` — the `y`-slice: a sup ball of radius
  `3^{-k}·L`, so of volume at most `(2·3^{-k}L)^d`, and EMPTY unless `x` lies in
  `straddleLayerSet Q j k` (all of `Q` at the far bands `k < j`; the depth-`j`
  skeleton layer of thickness `3^{j-k}` at the near bands, by the separation of
  `HomSpineDepthBandGeometry`).
* `lintegral_indicator_straddleLayerSet_le` — the `x`-mass carried by that
  layer: at most `bandStraddleWeight (d+1) j k` times the total mass of the
  slice, since the slice is constant on cells and the layer measure is
  `2·d·3^{j-k}` per cell (`HomSpineDepthStraddleMeasure`).

Together these are exactly the two factors `bandKernelVolume`/`bandStraddleWeight`
that `HomSpineDepthBandArith.sum_bandTerm_le` sums.
-/

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped BigOperators ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The straddling band -/

/-- The pairs of `Q` on which the depth-`j` slice jumps, at triadic band `k`. -/
def straddleBand (Q : TriadicCube d) (j k : ℕ) (v : TriadicCube d → Vec d) :
    Set (Vec d × Vec d) :=
  {z : Vec d × Vec d | z.1 ∈ cubeSet Q ∧ z.2 ∈ cubeSet Q ∧
    gridDualDepthTest Q j v z.2 ≠ gridDualDepthTest Q j v z.1 ∧
    (1 / 3 : ℝ) ^ (k + 1) * cubeScaleFactor Q ≤ dist z.1 z.2 ∧
    dist z.1 z.2 < (1 / 3 : ℝ) ^ k * cubeScaleFactor Q}

theorem measurableSet_straddleBand (Q : TriadicCube d) (j k : ℕ)
    (v : TriadicCube d → Vec d) : MeasurableSet (straddleBand Q j k v) := by
  have hg : Measurable (gridDualDepthTest Q j v) := measurable_gridDualDepthTest Q j v
  have h1 : MeasurableSet {z : Vec d × Vec d | z.1 ∈ cubeSet Q} :=
    measurable_fst (measurableSet_cubeSet Q)
  have h2 : MeasurableSet {z : Vec d × Vec d | z.2 ∈ cubeSet Q} :=
    measurable_snd (measurableSet_cubeSet Q)
  have hdiff : Measurable (fun z : Vec d × Vec d =>
      gridDualDepthTest Q j v z.2 - gridDualDepthTest Q j v z.1) :=
    (hg.comp measurable_snd).sub (hg.comp measurable_fst)
  have h3 : MeasurableSet {z : Vec d × Vec d |
      gridDualDepthTest Q j v z.2 ≠ gridDualDepthTest Q j v z.1} := by
    have hpre : {z : Vec d × Vec d |
        gridDualDepthTest Q j v z.2 ≠ gridDualDepthTest Q j v z.1} =
        (fun z : Vec d × Vec d =>
          gridDualDepthTest Q j v z.2 - gridDualDepthTest Q j v z.1) ⁻¹' {(0 : Vec d)}ᶜ := by
      ext z
      simp [sub_eq_zero]
    rw [hpre]
    exact hdiff (MeasurableSet.compl (measurableSet_singleton _))
  have hdist : Measurable (fun z : Vec d × Vec d => dist z.1 z.2) := continuous_dist.measurable
  have h4 : MeasurableSet {z : Vec d × Vec d |
      (1 / 3 : ℝ) ^ (k + 1) * cubeScaleFactor Q ≤ dist z.1 z.2} :=
    hdist measurableSet_Ici
  have h5 : MeasurableSet {z : Vec d × Vec d |
      dist z.1 z.2 < (1 / 3 : ℝ) ^ k * cubeScaleFactor Q} :=
    hdist measurableSet_Iio
  have hEq : straddleBand Q j k v =
      ({z : Vec d × Vec d | z.1 ∈ cubeSet Q} ∩ {z : Vec d × Vec d | z.2 ∈ cubeSet Q} ∩
          {z : Vec d × Vec d |
            gridDualDepthTest Q j v z.2 ≠ gridDualDepthTest Q j v z.1}) ∩
        ({z : Vec d × Vec d |
            (1 / 3 : ℝ) ^ (k + 1) * cubeScaleFactor Q ≤ dist z.1 z.2} ∩
          {z : Vec d × Vec d | dist z.1 z.2 < (1 / 3 : ℝ) ^ k * cubeScaleFactor Q}) := by
    ext z
    simp only [straddleBand, Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  rw [hEq]
  exact ((h1.inter h2).inter h3).inter (h4.inter h5)

/-- The band is symmetric in its two variables. -/
theorem mem_straddleBand_swap {Q : TriadicCube d} {j k : ℕ} {v : TriadicCube d → Vec d}
    {x y : Vec d} (h : (x, y) ∈ straddleBand Q j k v) : (y, x) ∈ straddleBand Q j k v := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h2, h1, Ne.symm h3, by rwa [dist_comm], by rwa [dist_comm]⟩

/-- The `x`-set the band can meet: everything at the far bands, and the
depth-`j` skeleton layer of thickness `3^{j-k}` at the near bands. -/
def straddleLayerSet (Q : TriadicCube d) (j k : ℕ) : Set (Vec d) :=
  if k < j then cubeSet Q
  else ⋃ R ∈ descendantsAtDepth Q j, cubeBoundaryLayer R ((1 / 3 : ℝ) ^ (k - j))

/-! ## 2. The `y`-slice -/

/-- The `y`-slice of the band, in the shape the inner integral consumes. -/
theorem measure_straddleBandSlice_le (Q : TriadicCube d) (j k : ℕ)
    (v : TriadicCube d → Vec d) (x : Vec d) :
    volume {y : Vec d | (x, y) ∈ straddleBand Q j k v} ≤
      ENNReal.ofReal ((2 * ((1 / 3 : ℝ) ^ k * cubeScaleFactor Q)) ^ d) *
        (straddleLayerSet Q j k).indicator (fun _ => (1 : ℝ≥0∞)) x := by
  classical
  have hLpos : (0 : ℝ) < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  have hrad : (0 : ℝ) ≤ (1 / 3 : ℝ) ^ k * cubeScaleFactor Q :=
    mul_nonneg (pow_nonneg (by norm_num) _) hLpos.le
  by_cases hx : x ∈ straddleLayerSet Q j k
  · rw [Set.indicator_of_mem hx, mul_one]
    refine le_trans (measure_mono ?_) (volume_setOf_dist_lt_le x hrad)
    intro y hy
    exact hy.2.2.2.2
  · /- off the layer set the slice is emp -/
    have hempty : {y : Vec d | (x, y) ∈ straddleBand Q j k v} = ∅ := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hy
      obtain ⟨hx1, -, hne, -, hlt⟩ := hy
      refine hx ?_
      rw [straddleLayerSet]
      by_cases hkj : k < j
      · rw [ite_eq_left hkj]
        exact hx1
      · rw [ite_eq_right hkj]
        have hkj' : j ≤ k := by omega
        have hsplit : ((1 / 3 : ℝ) ^ k * cubeScaleFactor Q) =
            (1 / 3 : ℝ) ^ (k - j) * (cubeScaleFactor Q / (3 : ℝ) ^ j) := by
          have hkk : (1 / 3 : ℝ) ^ k = (1 / 3 : ℝ) ^ (k - j) * (1 / 3 : ℝ) ^ j := by
            rw [← pow_add]
            congr 1
            omega
          have hj : (1 / 3 : ℝ) ^ j = ((3 : ℝ) ^ j)⁻¹ := by
            rw [one_div, inv_pow]
          rw [hkk, hj, div_eq_mul_inv]
          ring
        rw [hsplit] at hlt
        exact mem_biUnion_cubeBoundaryLayer_of_gridDualDepthTest_ne Q j v
          (pow_nonneg (by norm_num) _) hx1 hne hlt
    rw [hempty, measure_empty]
    exact zero_le

/-! ## 3. The `x`-mass of the layer -/

/-- The straddling measure at ANY thickness `t ≤ 1`, at the constant `D = d+1`
the band arithmetic runs on: below `1/2` this is
`HomSpineDepthStraddleMeasure.volume_cubeBoundaryLayer_le`, above it the layer is
the whole cell and `2·D·t ≥ 1`. -/
theorem volume_cubeBoundaryLayer_le_succ (R : TriadicCube d) {t : ℝ} (ht0 : 0 ≤ t) :
    volume (cubeBoundaryLayer R t) ≤
      ENNReal.ofReal (2 * ((d : ℝ) + 1) * t * cubeVolume R) := by
  have hV : (0 : ℝ) ≤ cubeVolume R := (cubeVolume_pos R).le
  rcases le_or_gt t (1 / 2) with hhalf | hhalf
  · refine le_trans (volume_cubeBoundaryLayer_le R ht0 hhalf) (ENNReal.ofReal_le_ofReal ?_)
    have hd : 2 * (d : ℝ) * t ≤ 2 * ((d : ℝ) + 1) * t := by
      have ht' : (0 : ℝ) ≤ t := ht0
      have : 2 * (d : ℝ) ≤ 2 * ((d : ℝ) + 1) := by linarith only []
      exact mul_le_mul_of_nonneg_right this ht'
    exact mul_le_mul_of_nonneg_right hd hV
  · have hsub : volume (cubeBoundaryLayer R t) ≤ volume (cubeSet R) :=
      measure_mono (cubeBoundaryLayer_subset_cubeSet R t)
    have hval : volume (cubeSet R) = ENNReal.ofReal (cubeVolume R) := by
      rw [← cubeMeasure_apply_univ, cubeMeasure_apply_univ_eq]
    refine le_trans hsub (le_of_eq_of_le hval (ENNReal.ofReal_le_ofReal ?_))
    have hcoef : (1 : ℝ) ≤ 2 * ((d : ℝ) + 1) * t := by
      have hd1 : (1 : ℝ) ≤ (d : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
        linarith only [this]
      have hstep : 2 * (1 : ℝ) * (1 / 2 : ℝ) ≤ 2 * ((d : ℝ) + 1) * t := by
        have h1 : 2 * (1 : ℝ) ≤ 2 * ((d : ℝ) + 1) := by linarith only [hd1]
        have h2 : (0 : ℝ) ≤ 2 * (1 : ℝ) := by norm_num
        calc 2 * (1 : ℝ) * (1 / 2 : ℝ) ≤ 2 * ((d : ℝ) + 1) * (1 / 2 : ℝ) :=
              mul_le_mul_of_nonneg_right h1 (by norm_num)
          _ ≤ 2 * ((d : ℝ) + 1) * t :=
              mul_le_mul_of_nonneg_left hhalf.le (by linarith only [hd1])
      linarith only [hstep]
    calc cubeVolume R = 1 * cubeVolume R := (one_mul _).symm
      _ ≤ 2 * ((d : ℝ) + 1) * t * cubeVolume R := mul_le_mul_of_nonneg_right hcoef hV

/-- The total mass of a depth slice, cell by cell. -/
theorem lintegral_enorm_gridDualDepthTest_eq (Q : TriadicCube d) (j : ℕ)
    (v : TriadicCube d → Vec d) {r : ℝ} (hr : 0 < r) :
    (∫⁻ x, ‖euclideanNorm (gridDualDepthTest Q j v x)‖ₑ ^ r ∂(cubeMeasure Q)) =
      ∑ R ∈ descendantsAtDepth Q j,
        ‖euclideanNorm (v R)‖ₑ ^ r * ENNReal.ofReal (cubeVolume R) := by
  classical
  rw [show (fun x => ‖euclideanNorm (gridDualDepthTest Q j v x)‖ₑ ^ r) =
      (fun x => ∑ R ∈ descendantsAtDepth Q j,
        (cubeSet R).indicator (fun _ => ‖euclideanNorm (v R)‖ₑ ^ r) x) from
    funext fun x => enorm_euclideanNorm_gridDualDepthTest_rpow Q j v hr x]
  rw [lintegral_finsetSum _
    (fun R _ => (measurable_const.indicator (measurableSet_cubeSet R)))]
  refine Finset.sum_congr rfl fun R hR => ?_
  rw [lintegral_indicator_const (measurableSet_cubeSet R), cubeMeasure,
    Measure.restrict_apply (measurableSet_cubeSet R),
    Set.inter_eq_self_of_subset_left (cubeSet_subset_of_mem_descendantsAtDepth hR),
    ← cubeMeasure_apply_univ, cubeMeasure_apply_univ_eq]

/-- **THE LAYER MASS.**  The mass the depth slice carries on the band-`k`
straddling layer is at most `bandStraddleWeight (d+1) j k` times its total mass:
`1` at the far bands, `2·(d+1)·3^{j-k}` at the near ones. -/
theorem lintegral_indicator_straddleLayerSet_le (Q : TriadicCube d) (j k : ℕ)
    (v : TriadicCube d → Vec d) {r : ℝ} (hr : 0 < r) :
    (∫⁻ x, (straddleLayerSet Q j k).indicator
        (fun x => ‖euclideanNorm (gridDualDepthTest Q j v x)‖ₑ ^ r) x ∂(cubeMeasure Q)) ≤
      ENNReal.ofReal (bandStraddleWeight ((d : ℝ) + 1) j k) *
        ∫⁻ x, ‖euclideanNorm (gridDualDepthTest Q j v x)‖ₑ ^ r ∂(cubeMeasure Q) := by
  classical
  by_cases hkj : k < j
  · have hone : bandStraddleWeight ((d : ℝ) + 1) j k = 1 := by
      rw [bandStraddleWeight, ite_eq_left hkj]
    rw [straddleLayerSet, ite_eq_left hkj, hone, ENNReal.ofReal_one, one_mul]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ cubeSet Q
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  · /- near bands: the layer of thickness `t = 3^{j-k}` -/
    set t : ℝ := (1 / 3 : ℝ) ^ (k - j)
    have ht0 : (0 : ℝ) ≤ t := pow_nonneg (by norm_num) _
    have ht1 : t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hw : bandStraddleWeight ((d : ℝ) + 1) j k = 2 * ((d : ℝ) + 1) * t := by
      rw [bandStraddleWeight, ite_eq_right hkj]
    rw [straddleLayerSet, ite_eq_right hkj, hw,
      lintegral_enorm_gridDualDepthTest_eq Q j v hr, Finset.mul_sum]
    /- dominate the layer union cell by ce -/
    have hpt : ∀ x : Vec d,
        (⋃ R ∈ descendantsAtDepth Q j, cubeBoundaryLayer R t).indicator
            (fun x => ‖euclideanNorm (gridDualDepthTest Q j v x)‖ₑ ^ r) x ≤
          ∑ R ∈ descendantsAtDepth Q j,
            (cubeBoundaryLayer R t).indicator (fun _ => ‖euclideanNorm (v R)‖ₑ ^ r) x := by
      intro x
      by_cases hx : x ∈ ⋃ R ∈ descendantsAtDepth Q j, cubeBoundaryLayer R t
      · obtain ⟨R, hR'⟩ := Set.mem_iUnion.mp hx
        obtain ⟨hR, hxR⟩ := Set.mem_iUnion.mp hR'
        rw [Set.indicator_of_mem hx,
          gridDualDepthTest_apply_of_mem v hR (cubeBoundaryLayer_subset_cubeSet R t hxR)]
        have hsingle : (cubeBoundaryLayer R t).indicator
              (fun _ => ‖euclideanNorm (v R)‖ₑ ^ r) x ≤
            ∑ S ∈ descendantsAtDepth Q j,
              (cubeBoundaryLayer S t).indicator (fun _ => ‖euclideanNorm (v S)‖ₑ ^ r) x :=
          Finset.single_le_sum (f := fun S => (cubeBoundaryLayer S t).indicator
            (fun _ => ‖euclideanNorm (v S)‖ₑ ^ r) x) (fun S _ => zero_le) hR
        rwa [Set.indicator_of_mem hxR] at hsingle
      · rw [Set.indicator_of_notMem hx]
        exact zero_le
    refine le_trans (lintegral_mono hpt) ?_
    rw [lintegral_finsetSum _
      (fun R _ => (measurable_const.indicator (measurableSet_cubeBoundaryLayer R t)))]
    refine Finset.sum_le_sum fun R hR => ?_
    rw [lintegral_indicator_const (measurableSet_cubeBoundaryLayer R t)]
    have hmeas : (cubeMeasure Q) (cubeBoundaryLayer R t) ≤
        ENNReal.ofReal (2 * ((d : ℝ) + 1) * t * cubeVolume R) := by
      rw [cubeMeasure, Measure.restrict_apply (measurableSet_cubeBoundaryLayer R t)]
      exact le_trans (measure_mono Set.inter_subset_left)
        (volume_cubeBoundaryLayer_le_succ R ht0)
    refine le_trans (mul_le_mul' le_rfl hmeas) (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by
      exact mul_nonneg (mul_nonneg (by norm_num) (by
        have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
        linarith only [this])) ht0)]
    ring

end

end Algsuperdiff.Section4.Provider.Homogenization
