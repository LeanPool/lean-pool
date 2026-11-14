/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineDepthBandSlice

/-!
# HomSpineDepthBandIntegral

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The band integral: one Fubini, one symmetry, one mass bound

## What this file is for

The double integral of the depth-`j` slice's mass over ONE triadic band.  With
`N x = ‖g_j(x)‖ₑ^{p'}` and `Ω_k = straddleBand Q j k v`,

```text
  ∫∫_{Ω_k} (N x + N y)  ≤  2·(2·3^{-k}L)^d · bandStraddleWeight (d+1) j k · ∫ N.
```

The `x`-half is `HomSpineDepthBandSlice`'s two bounds composed: the `y`-slice is
a sup ball and is empty off the straddling layer, and the layer carries at most
`bandStraddleWeight` of the mass.  The `y`-half is the SAME quantity: `Ω_k` is
symmetric and `cubeMeasure Q` is `σ`-finite, so one Tonelli swap
(`lintegral_lintegral_swap`) identifies the two halves exactly — no second
estimate is made.
-/

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped BigOperators ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. Measurability of the two band densities -/

theorem measurable_enorm_gridDualDepthTest (Q : TriadicCube d) (j : ℕ)
    (v : TriadicCube d → Vec d) (r : ℝ) :
    Measurable (fun x : Vec d => ‖euclideanNorm (gridDualDepthTest Q j v x)‖ₑ ^ r) := by
  have hg : Measurable (gridDualDepthTest Q j v) := measurable_gridDualDepthTest Q j v
  have hn : Measurable (fun x : Vec d => euclideanNorm (gridDualDepthTest Q j v x)) := by
    have hh : Measurable (fun x : Vec d => HilbertVec.ofVec (gridDualDepthTest Q j v x)) :=
      (HilbertVec.ofVecL d).continuous.measurable.comp hg
    simpa only [euclideanNorm_eq_norm_ofVec] using hh.norm
  exact hn.enorm.pow_const r

/-! ## 2. The `x`-half -/

/-- **THE BAND INTEGRAL, `x`-HALF.**  The `y`-slice contributes the sup-ball
volume and confines `x` to the straddling layer; the layer carries at most
`bandStraddleWeight` of the slice's mass. -/
theorem lintegral_lintegral_straddleBand_fst_le (Q : TriadicCube d) (j k : ℕ)
    (v : TriadicCube d → Vec d) {r : ℝ} (hr : 0 < r) :
    (∫⁻ x, ∫⁻ y, (straddleBand Q j k v).indicator
        (fun z : Vec d × Vec d => ‖euclideanNorm (gridDualDepthTest Q j v z.1)‖ₑ ^ r) (x, y)
        ∂(cubeMeasure Q) ∂(cubeMeasure Q)) ≤
      ENNReal.ofReal ((2 * ((1 / 3 : ℝ) ^ k * cubeScaleFactor Q)) ^ d) *
        ENNReal.ofReal (bandStraddleWeight ((d : ℝ) + 1) j k) *
        ∫⁻ x, ‖euclideanNorm (gridDualDepthTest Q j v x)‖ₑ ^ r ∂(cubeMeasure Q) := by
  classical
  set μ : Measure (Vec d) := cubeMeasure Q with hμ
  set N : Vec d → ℝ≥0∞ :=
    fun x => ‖euclideanNorm (gridDualDepthTest Q j v x)‖ₑ ^ r with hN
  set B : ℝ≥0∞ := ENNReal.ofReal ((2 * ((1 / 3 : ℝ) ^ k * cubeScaleFactor Q)) ^ d) with hB
  /- the inner integral, exact -/
  have hinner : ∀ x : Vec d,
      (∫⁻ y, (straddleBand Q j k v).indicator
          (fun z : Vec d × Vec d => N z.1) (x, y) ∂μ) =
        N x * μ {y : Vec d | (x, y) ∈ straddleBand Q j k v} := by
    intro x
    have hslice : MeasurableSet {y : Vec d | (x, y) ∈ straddleBand Q j k v} :=
      (measurable_prodMk_left) (measurableSet_straddleBand Q j k v)
    have hfun : (fun y : Vec d => (straddleBand Q j k v).indicator
          (fun z : Vec d × Vec d => N z.1) (x, y)) =
        fun y : Vec d =>
          {y : Vec d | (x, y) ∈ straddleBand Q j k v}.indicator (fun _ => N x) y := by
      funext y
      by_cases hxy : (x, y) ∈ straddleBand Q j k v
      · have hy : y ∈ {y : Vec d | (x, y) ∈ straddleBand Q j k v} := hxy
        rw [Set.indicator_of_mem hxy, Set.indicator_of_mem hy]
      · have hy : y ∉ {y : Vec d | (x, y) ∈ straddleBand Q j k v} := hxy
        rw [Set.indicator_of_notMem hxy, Set.indicator_of_notMem hy]
    rw [hfun, lintegral_indicator_const hslice, mul_comm]
  /- the slice bou -/
  have hslicebd : ∀ x : Vec d, N x * μ {y : Vec d | (x, y) ∈ straddleBand Q j k v} ≤
      B * (straddleLayerSet Q j k).indicator N x := by
    intro x
    have hres : μ {y : Vec d | (x, y) ∈ straddleBand Q j k v} ≤
        volume {y : Vec d | (x, y) ∈ straddleBand Q j k v} := by
      rw [hμ, cubeMeasure]
      exact Measure.restrict_le_self _
    have hstep : N x * μ {y : Vec d | (x, y) ∈ straddleBand Q j k v} ≤
        N x * (B * (straddleLayerSet Q j k).indicator (fun _ => (1 : ℝ≥0∞)) x) :=
      mul_le_mul' le_rfl (le_trans hres (measure_straddleBandSlice_le Q j k v x))
    refine le_trans hstep (le_of_eq ?_)
    by_cases hx : x ∈ straddleLayerSet Q j k
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_one, mul_comm]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero, mul_zero]
  calc (∫⁻ x, ∫⁻ y, (straddleBand Q j k v).indicator
          (fun z : Vec d × Vec d => N z.1) (x, y) ∂μ ∂μ)
      = ∫⁻ x, N x * μ {y : Vec d | (x, y) ∈ straddleBand Q j k v} ∂μ :=
        lintegral_congr hinner
    _ ≤ ∫⁻ x, B * (straddleLayerSet Q j k).indicator N x ∂μ := lintegral_mono hslicebd
    _ = B * ∫⁻ x, (straddleLayerSet Q j k).indicator N x ∂μ := lintegral_const_mul' _ _ (by
        rw [hB]; exact ENNReal.ofReal_ne_top)
    _ ≤ B * (ENNReal.ofReal (bandStraddleWeight ((d : ℝ) + 1) j k) * ∫⁻ x, N x ∂μ) :=
        mul_le_mul' le_rfl (lintegral_indicator_straddleLayerSet_le Q j k v hr)
    _ = B * ENNReal.ofReal (bandStraddleWeight ((d : ℝ) + 1) j k) * ∫⁻ x, N x ∂μ :=
        (mul_assoc _ _ _).symm

/-! ## 3. The `y`-half, by symmetry -/

/-- **THE SYMMETRY.**  One Tonelli swap identifies the `y`-half with the
`x`-half: the band is symmetric and both slots carry the same finite measure. -/
theorem lintegral_lintegral_straddleBand_snd_eq (Q : TriadicCube d) (j k : ℕ)
    (v : TriadicCube d → Vec d) (r : ℝ) :
    (∫⁻ x, ∫⁻ y, (straddleBand Q j k v).indicator
        (fun z : Vec d × Vec d => ‖euclideanNorm (gridDualDepthTest Q j v z.2)‖ₑ ^ r) (x, y)
        ∂(cubeMeasure Q) ∂(cubeMeasure Q)) =
      ∫⁻ x, ∫⁻ y, (straddleBand Q j k v).indicator
        (fun z : Vec d × Vec d => ‖euclideanNorm (gridDualDepthTest Q j v z.1)‖ₑ ^ r) (x, y)
        ∂(cubeMeasure Q) ∂(cubeMeasure Q) := by
  classical
  have : IsFiniteMeasure (cubeMeasure Q) :=
    ⟨lt_top_iff_ne_top.2 (cubeMeasure_apply_univ_ne_top Q)⟩
  have : SFinite (cubeMeasure Q) := by
    unfold cubeMeasure
    infer_instance
  have hmeas : AEMeasurable
      (Function.uncurry fun x y : Vec d => (straddleBand Q j k v).indicator
        (fun z : Vec d × Vec d => ‖euclideanNorm (gridDualDepthTest Q j v z.2)‖ₑ ^ r) (x, y))
      ((cubeMeasure Q).prod (cubeMeasure Q)) := by
    refine Measurable.aemeasurable ?_
    exact ((measurable_enorm_gridDualDepthTest Q j v r).comp measurable_snd).indicator
      (measurableSet_straddleBand Q j k v)
  rw [lintegral_lintegral_swap hmeas]
  refine lintegral_congr fun y => lintegral_congr fun x => ?_
  by_cases hxy : (x, y) ∈ straddleBand Q j k v
  · rw [Set.indicator_of_mem hxy, Set.indicator_of_mem (mem_straddleBand_swap hxy)]
  · have hyx : (y, x) ∉ straddleBand Q j k v := fun h => hxy (mem_straddleBand_swap h)
    rw [Set.indicator_of_notMem hxy, Set.indicator_of_notMem hyx]

/-! ## 4. The band integral -/

/-- **THE BAND INTEGRAL.**  Both halves together, at the explicit band factor:
the sup-ball volume of the slice times the straddling weight of the layer, twice
(once per variable). -/
theorem lintegral_lintegral_straddleBand_pair_le (Q : TriadicCube d) (j k : ℕ)
    (v : TriadicCube d → Vec d) {r : ℝ} (hr : 0 < r) :
    (∫⁻ x, ∫⁻ y, ((straddleBand Q j k v).indicator
          (fun z : Vec d × Vec d => ‖euclideanNorm (gridDualDepthTest Q j v z.1)‖ₑ ^ r) (x, y) +
        (straddleBand Q j k v).indicator
          (fun z : Vec d × Vec d => ‖euclideanNorm (gridDualDepthTest Q j v z.2)‖ₑ ^ r) (x, y))
        ∂(cubeMeasure Q) ∂(cubeMeasure Q)) ≤
      2 * (ENNReal.ofReal ((2 * ((1 / 3 : ℝ) ^ k * cubeScaleFactor Q)) ^ d) *
          ENNReal.ofReal (bandStraddleWeight ((d : ℝ) + 1) j k) *
          ∫⁻ x, ‖euclideanNorm (gridDualDepthTest Q j v x)‖ₑ ^ r ∂(cubeMeasure Q)) := by
  classical
  have : IsFiniteMeasure (cubeMeasure Q) :=
    ⟨lt_top_iff_ne_top.2 (cubeMeasure_apply_univ_ne_top Q)⟩
  have : SFinite (cubeMeasure Q) := by
    unfold cubeMeasure
    infer_instance
  have hmeas1 : Measurable (fun z : Vec d × Vec d => (straddleBand Q j k v).indicator
      (fun z : Vec d × Vec d => ‖euclideanNorm (gridDualDepthTest Q j v z.1)‖ₑ ^ r) z) :=
    ((measurable_enorm_gridDualDepthTest Q j v r).comp measurable_fst).indicator
      (measurableSet_straddleBand Q j k v)
  have hmeas2 : Measurable (fun z : Vec d × Vec d => (straddleBand Q j k v).indicator
      (fun z : Vec d × Vec d => ‖euclideanNorm (gridDualDepthTest Q j v z.2)‖ₑ ^ r) z) :=
    ((measurable_enorm_gridDualDepthTest Q j v r).comp measurable_snd).indicator
      (measurableSet_straddleBand Q j k v)
  have hsplit : ∀ x : Vec d,
      (∫⁻ y, ((straddleBand Q j k v).indicator
            (fun z : Vec d × Vec d => ‖euclideanNorm (gridDualDepthTest Q j v z.1)‖ₑ ^ r)
              (x, y) +
          (straddleBand Q j k v).indicator
            (fun z : Vec d × Vec d => ‖euclideanNorm (gridDualDepthTest Q j v z.2)‖ₑ ^ r)
              (x, y)) ∂(cubeMeasure Q)) =
        (∫⁻ y, (straddleBand Q j k v).indicator
            (fun z : Vec d × Vec d => ‖euclideanNorm (gridDualDepthTest Q j v z.1)‖ₑ ^ r)
              (x, y) ∂(cubeMeasure Q)) +
          ∫⁻ y, (straddleBand Q j k v).indicator
            (fun z : Vec d × Vec d => ‖euclideanNorm (gridDualDepthTest Q j v z.2)‖ₑ ^ r)
              (x, y) ∂(cubeMeasure Q) := by
    intro x
    exact lintegral_add_left (hmeas1.comp measurable_prodMk_left) _
  have houter : Measurable fun x : Vec d => ∫⁻ y, (straddleBand Q j k v).indicator
      (fun z : Vec d × Vec d => ‖euclideanNorm (gridDualDepthTest Q j v z.1)‖ₑ ^ r) (x, y)
      ∂(cubeMeasure Q) := hmeas1.lintegral_prod_right'
  rw [lintegral_congr hsplit, lintegral_add_left houter,
    lintegral_lintegral_straddleBand_snd_eq Q j k v r, two_mul]
  exact add_le_add (lintegral_lintegral_straddleBand_fst_le Q j k v hr)
    (lintegral_lintegral_straddleBand_fst_le Q j k v hr)

end

end Algsuperdiff.Section4.Provider.Homogenization
