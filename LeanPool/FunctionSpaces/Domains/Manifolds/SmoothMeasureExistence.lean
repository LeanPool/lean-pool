/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Manifolds.BesovAtlas
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Geometry.Manifold.Instances.Sphere

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Smooth measures exist

Let `M` be a smooth manifold modelled on `E` with corners `I` and `A` a Besov atlas with charts
`κ_k` and partition of unity `(ψ_k)`. The **chart measure** of `A`
(`Manifold.BesovAtlas.chartMeasure`) transports the Lebesgue measure with weight `ψ_k ∘ κ_k⁻¹`
from the target of `κ_k` to `M` and sums over `k`:

`μ_A = ∑_k (κ_k⁻¹)_* (ψ_k ∘ κ_k⁻¹ · vol|_{κ_k(e_k.source)})`.

In every chart `e` of the atlas of `M` (`e ∈ atlas H M`) with extended chart `κ`, the change of
variables `Φ_k = κ_k ∘ κ⁻¹` (Mathlib's `lintegral_image_eq_lintegral_abs_det_fderiv_mul`) gives
`κ_* (μ_A|_{e.source}) = ρ_e · vol|_{κ(e.source)}` with the density
`ρ_e(y) = ∑_k |det DΦ_k(y)| ψ_k(κ⁻¹ y)` (`Manifold.BesovAtlas.chartDensity`,
`Manifold.BesovAtlas.map_extend_chartMeasure`), where `DΦ_k` is the derivative within the source of
`Φ_k`, a relatively open subset of `range I`. The density is continuous, because each term vanishes
near the points where `κ⁻¹ y` leaves the source of `κ_k`, and positive, because some `ψ_k(κ⁻¹ y)`
is positive and `DΦ_k(y)` is invertible. So `μ_A` is a finite smooth measure, that is, a measure
with a continuous positive density in every chart
(`Manifold.BesovAtlas.isSmoothMeasure_chartMeasure`,
`Manifold.BesovAtlas.isFiniteMeasure_chartMeasure`) for every model, with or without boundary,
and every compact Hausdorff manifold carries one (`Manifold.exists_isSmoothMeasure`); for example
the sphere `S^n ⊆ ℝ^(n+1)`, a compact manifold without boundary
(`Manifold.exists_isSmoothMeasure_sphere`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal Manifold ContDiff

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M] [BorelSpace M]

namespace BesovAtlas

variable (A : BesovAtlas I M)

/-! ### The chart measure -/

/-- The **chart measure** of a Besov atlas: `μ_A = ∑_k (κ_k⁻¹)_* (ψ_k ∘ κ_k⁻¹ · vol|_{T_k})`,
`T_k` the target of the extended chart `κ_k`. -/
noncomputable def chartMeasure : Measure M :=
  ∑ k, Measure.map (A.ext k).symm ((volume.restrict (A.ext k).target).withDensity
    fun y => ENNReal.ofReal (A.psi k ((A.ext k).symm y)))

/-- **The chart measure of a measurable set**: `μ_A(S) = ∑_k ∫_{S_k} ψ_k(κ_k⁻¹ y) dy`, where
`S_k` is the set of `y ∈ T_k` with `κ_k⁻¹ y ∈ S`. -/
theorem chartMeasure_apply {S : Set M} (hS : MeasurableSet S) :
    A.chartMeasure S = ∑ k, ∫⁻ y in (A.ext k).target ∩ (A.ext k).symm ⁻¹' S,
      ENNReal.ofReal (A.psi k ((A.ext k).symm y)) := by
  rw [chartMeasure, FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hT := measurableSet_extend_target I (A.chart k)
  have hκ : AEMeasurable (A.ext k).symm ((volume.restrict (A.ext k).target).withDensity
      fun y => ENNReal.ofReal (A.psi k ((A.ext k).symm y))) :=
    (((A.chart k).continuousOn_extend_symm (I := I)).aemeasurable hT).mono_ac
      (withDensity_absolutelyContinuous _ _)
  rw [Measure.map_apply_of_aemeasurable hκ hS, withDensity_apply' _ _,
    Measure.restrict_restrict' hT, inter_comm]

/-- **The chart measure is finite**: the `k`-th term has total mass at most the volume of the
compact set `κ_k(tsupport ψ_k)`, since `0 ≤ ψ_k ≤ 1` and `M` is compact. -/
instance isFiniteMeasure_chartMeasure [CompactSpace M] : IsFiniteMeasure A.chartMeasure := by
  refine ⟨?_⟩
  rw [A.chartMeasure_apply MeasurableSet.univ]
  refine ENNReal.sum_lt_top.2 fun k _ => ?_
  have hT := measurableSet_extend_target I (A.chart k)
  have hK : IsCompact (A.ext k '' tsupport (A.psi k)) :=
    (isClosed_tsupport _).isCompact.image_of_continuousOn ((A.chart k).continuousOn_extend.mono
      (by rw [OpenPartialHomeomorph.extend_source]; exact A.tsupport_psi_subset k))
  rw [preimage_univ, inter_univ]
  calc ∫⁻ y in (A.ext k).target, ENNReal.ofReal (A.psi k ((A.ext k).symm y))
      ≤ ∫⁻ y in (A.ext k).target, (A.ext k '' tsupport (A.psi k)).indicator 1 y := by
        refine setLIntegral_mono' hT fun y hy => ?_
        by_cases h0 : A.psi k ((A.ext k).symm y) = 0
        · rw [h0, ENNReal.ofReal_zero]
          exact zero_le
        · have hyK : y ∈ A.ext k '' tsupport (A.psi k) :=
            ⟨_, subset_tsupport _ h0, (A.ext k).right_inv hy⟩
          rw [indicator_of_mem hyK, Pi.one_apply, ← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (A.psi_le_one k _)
    _ ≤ ∫⁻ y, (A.ext k '' tsupport (A.psi k)).indicator 1 y := setLIntegral_le_lintegral _ _
    _ = volume (A.ext k '' tsupport (A.psi k)) := lintegral_indicator_one hK.measurableSet
    _ < ⊤ := hK.measure_lt_top

/-! ### The density in a chart -/

/-- The `k`-th **term of the density** in the chart `e`: `|det DΦ_k(y)| ψ_k(κ⁻¹ y)`, with the
change of charts `Φ_k = κ_k ∘ κ⁻¹` and its derivative within its source. -/
noncomputable def densityTerm (e : OpenPartialHomeomorph M H) (k : Fin A.n) (y : E) : ℝ :=
  |(fderivWithin ℝ (I.extendCoordChange e (A.chart k))
      (I.extendCoordChange e (A.chart k)).source y).det| * A.psi k ((e.extend I).symm y)

/-- The **density of the chart measure** in the chart `e`:
`ρ_e(y) = ∑_k |det DΦ_k(y)| ψ_k(κ⁻¹ y)`. -/
noncomputable def chartDensity (e : OpenPartialHomeomorph M H) (y : E) : ℝ :=
  ∑ k, A.densityTerm e k y

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M]
  [BorelSpace M] in
/-- The terms of the density are nonnegative. -/
theorem densityTerm_nonneg (e : OpenPartialHomeomorph M H) (k : Fin A.n) (y : E) :
    0 ≤ A.densityTerm e k y :=
  mul_nonneg (abs_nonneg _) (A.nonneg_psi k _)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M]
  [BorelSpace M] in
/-- The `k`-th term of the density vanishes where `κ⁻¹ y` lies outside the source of `κ_k`, since
`tsupport ψ_k` lies in that source. -/
theorem densityTerm_eq_zero (e : OpenPartialHomeomorph M H) (k : Fin A.n) {y : E}
    (hy : (e.extend I).symm y ∉ (A.chart k).source) : A.densityTerm e k y = 0 := by
  rw [densityTerm, image_eq_zero_of_notMem_tsupport fun h => hy (A.tsupport_psi_subset k h),
    mul_zero]

variable [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M]
  [BorelSpace M] in
/-- The `k`-th term of the density is continuous on the source of the change of charts `Φ_k`:
`Φ_k` is smooth there, so its derivative within the source is continuous
(Mathlib's `ContDiffOn.continuousOn_fderivWithin`). -/
theorem continuousOn_densityTerm_source {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M)
    (k : Fin A.n) :
    ContinuousOn (A.densityTerm e k) (I.extendCoordChange e (A.chart k)).source := by
  have hd := (I.contDiffOn_extendCoordChange (n := ∞) (IsManifold.subset_maximalAtlas he)
    (IsManifold.subset_maximalAtlas (A.chart_mem k))).continuousOn_fderivWithin
      I.uniqueDiffOn_extendCoordChange_source (by simp)
  refine (continuous_abs.comp_continuousOn
    (ContinuousLinearMap.continuous_det.comp_continuousOn hd)).mul ?_
  exact ((A.contMDiff_psi k).continuous.comp_continuousOn
    (e.continuousOn_extend_symm (I := I))).mono fun w hw => ((mem_coordChange_source _ _).1 hw).1

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M]
  [BorelSpace M] in
/-- **The terms of the density are continuous on the target** of the chart `e`: on the
relatively open source of `Φ_k` by `Manifold.BesovAtlas.continuousOn_densityTerm_source`; near a
point `y` with `κ⁻¹ y` outside the source of `κ_k`, `κ⁻¹ w` stays outside the closed
`tsupport ψ_k`, so the term vanishes near `y`. -/
theorem continuousOn_densityTerm {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M)
    (k : Fin A.n) : ContinuousOn (A.densityTerm e k) (e.extend I).target := by
  intro z hz
  have hsymm : ContinuousWithinAt (e.extend I).symm (e.extend I).target z :=
    e.continuousOn_extend_symm (I := I) z hz
  by_cases hzs : (e.extend I).symm z ∈ (A.chart k).source
  · have hnhds : (I.extendCoordChange e (A.chart k)).source ∈ 𝓝[(e.extend I).target] z := by
      filter_upwards [hsymm.preimage_mem_nhdsWithin ((A.chart k).open_source.mem_nhds hzs),
        self_mem_nhdsWithin] with w hw hwt
      exact (mem_coordChange_source _ _).2 ⟨hwt, hw⟩
    exact (A.continuousOn_densityTerm_source he k z
      ((mem_coordChange_source _ _).2 ⟨hz, hzs⟩)).mono_of_mem_nhdsWithin hnhds
  · have hnot : (e.extend I).symm z ∉ tsupport (A.psi k) := fun h =>
      hzs (A.tsupport_psi_subset k h)
    have hev : A.densityTerm e k =ᶠ[𝓝[(e.extend I).target] z] fun _ => 0 := by
      filter_upwards [hsymm.preimage_mem_nhdsWithin
        ((isClosed_tsupport _).isOpen_compl.mem_nhds hnot)] with w hw
      rw [densityTerm, image_eq_zero_of_notMem_tsupport hw, mul_zero]
    exact continuousWithinAt_const.congr_of_eventuallyEq hev (hev.eq_of_nhdsWithin hz)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M]
  [BorelSpace M] in
/-- **The density is positive on the target** of the chart `e`: some `ψ_k(κ⁻¹ y)` is positive,
since the `ψ_k` sum to `1`; then `κ⁻¹ y` lies in the source of `κ_k` and the derivative of the
change of charts `Φ_k` at `y` is invertible (Mathlib's
`ModelWithCorners.isInvertible_fderivWithin_extendCoordChange`), so its determinant is
nonzero. -/
theorem chartDensity_pos {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M) {y : E}
    (hy : y ∈ (e.extend I).target) : 0 < A.chartDensity e y := by
  obtain ⟨k, -, hk⟩ : ∃ k ∈ Finset.univ, (0 : ℝ) < A.psi k ((e.extend I).symm y) :=
    Finset.exists_lt_of_sum_lt (by rw [Finset.sum_const_zero, A.sum_psi]; exact one_pos)
  have hys : (e.extend I).symm y ∈ (A.chart k).source :=
    A.tsupport_psi_subset k (subset_tsupport _ hk.ne')
  obtain ⟨L, hL⟩ := I.isInvertible_fderivWithin_extendCoordChange (n := ∞) (by simp)
    (IsManifold.subset_maximalAtlas he) (IsManifold.subset_maximalAtlas (A.chart_mem k))
    ((mem_coordChange_source _ _).2 ⟨hy, hys⟩)
  refine Finset.sum_pos' (fun j _ => A.densityTerm_nonneg e j y) ⟨k, Finset.mem_univ _, ?_⟩
  refine mul_pos (abs_pos.2 ?_) hk
  rw [← hL]
  exact (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero

omit [MeasurableSpace M] [BorelSpace M] in
/-- **The change of variables for one term**: for every chart `e` of the atlas of `M`
(`e ∈ atlas H M`) and a measurable
`B ⊆ E`, `∫_{B ∩ κ(e.source)} |det DΦ_k| ψ_k ∘ κ⁻¹ = ∫_{S_k} ψ_k ∘ κ_k⁻¹`, where `S_k` is the
set of `y ∈ T_k` with `κ_k⁻¹ y ∈ e.source` and `κ(κ_k⁻¹ y) ∈ B`. The integrand on the left
vanishes off the source of `Φ_k` (`Manifold.BesovAtlas.densityTerm_eq_zero`), and `Φ_k` maps
`B ∩ source Φ_k` onto `S_k` (`Manifold.image_coordChange_inter`); Mathlib's
`lintegral_image_eq_lintegral_abs_det_fderiv_mul` with the derivatives within the source. -/
theorem setLIntegral_densityTerm {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M)
    (k : Fin A.n) {B : Set E} (hB : MeasurableSet B) :
    ∫⁻ z in B ∩ (e.extend I).target, ENNReal.ofReal (A.densityTerm e k z) =
      ∫⁻ y in (A.ext k).target ∩ (A.ext k).symm ⁻¹' (e.source ∩ e.extend I ⁻¹' B),
        ENNReal.ofReal (A.psi k ((A.ext k).symm y)) := by
  set Φ := I.extendCoordChange e (A.chart k)
  have hΦm : MeasurableSet Φ.source := measurableSet_coordChange_source e (A.chart k)
  have hT := measurableSet_extend_target I e
  have hsub : Φ.source ⊆ (e.extend I).target := fun z hz => ((mem_coordChange_source _ _).1 hz).1
  have hd := (I.contDiffOn_extendCoordChange (n := ∞) (IsManifold.subset_maximalAtlas he)
    (IsManifold.subset_maximalAtlas (A.chart_mem k))).differentiableOn (by simp)
  have hset : Φ.source ∩ (B ∩ (e.extend I).target) = B ∩ Φ.source := by
    ext z
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, hsub h.2⟩⟩
  rw [← image_coordChange_inter, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (hB.inter hΦm) (fun z hz => (hd z hz.2).hasFDerivWithinAt.mono inter_subset_right)
    (Φ.injOn.mono inter_subset_right)]
  calc ∫⁻ z in B ∩ (e.extend I).target, ENNReal.ofReal (A.densityTerm e k z)
      = ∫⁻ z in B ∩ (e.extend I).target,
          Φ.source.indicator (fun z => ENNReal.ofReal (A.densityTerm e k z)) z := by
        refine setLIntegral_congr_fun (hB.inter hT) fun z hz => ?_
        by_cases hzΦ : z ∈ Φ.source
        · rw [indicator_of_mem hzΦ]
        · rw [indicator_of_notMem hzΦ, A.densityTerm_eq_zero e k
            fun h => hzΦ ((mem_coordChange_source _ _).2 ⟨hz.2, h⟩), ENNReal.ofReal_zero]
    _ = ∫⁻ z in B ∩ Φ.source, ENNReal.ofReal (A.densityTerm e k z) := by
        rw [lintegral_indicator hΦm, Measure.restrict_restrict hΦm, hset]
    _ = _ := by
        refine setLIntegral_congr_fun (hB.inter hΦm) fun z hz => ?_
        obtain ⟨-, hzs⟩ := (mem_coordChange_source _ _).1 hz.2
        have hzs' : (e.extend I).symm z ∈ (A.ext k).source := by
          rwa [OpenPartialHomeomorph.extend_source]
        rw [densityTerm, ENNReal.ofReal_mul (abs_nonneg _), coordChange_apply,
          (A.ext k).left_inv hzs']

/-- **The chart measure in a chart**: for every chart `e` of the atlas of `M` (`e ∈ atlas H M`),
with extended chart `κ`,
`κ_* (μ_A|_{e.source}) = ρ_e · vol|_{κ(e.source)}` with the density `ρ_e` of
`Manifold.BesovAtlas.chartDensity`. Both sides are compared on a measurable `B`: the left side is
`μ_A(e.source ∩ κ⁻¹(B))` (`Manifold.BesovAtlas.chartMeasure_apply`), the right side the sum over
`k` of the integrals of the terms (`Manifold.BesovAtlas.setLIntegral_densityTerm`). -/
theorem map_extend_chartMeasure {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M) :
    Measure.map (e.extend I) (A.chartMeasure.restrict e.source) =
      (volume.restrict (e.extend I).target).withDensity
        fun y => ENNReal.ofReal (A.chartDensity e y) := by
  have hsrc : MeasurableSet e.source := e.open_source.measurableSet
  have hT := measurableSet_extend_target I e
  have hκ := aemeasurable_extend_restrict I e A.chartMeasure
  ext B hB
  have hS := measurableSet_source_inter_extend_preimage I e hB
  have hsum : ∀ y, ENNReal.ofReal (A.chartDensity e y) =
      ∑ k, ENNReal.ofReal (A.densityTerm e k y) := fun y =>
    ENNReal.ofReal_sum_of_nonneg fun k _ => A.densityTerm_nonneg e k y
  rw [Measure.map_apply_of_aemeasurable hκ hB, Measure.restrict_apply' hsrc, inter_comm,
    A.chartMeasure_apply hS, withDensity_apply _ hB, Measure.restrict_restrict hB]
  simp_rw [hsum]
  rw [lintegral_finsetSum' (f := fun k z => ENNReal.ofReal (A.densityTerm e k z)) _
    fun k _ => ENNReal.measurable_ofReal.comp_aemeasurable
    (((A.continuousOn_densityTerm he k).aemeasurable hT).mono_set inter_subset_right)]
  exact Finset.sum_congr rfl fun k _ => (A.setLIntegral_densityTerm he k hB).symm

/-- **The chart measure is smooth**: in every chart `e` of the atlas of `M` (`e ∈ atlas H M`) its
image has the density
`ρ_e = ∑_k |det DΦ_k| ψ_k ∘ κ⁻¹` (`Manifold.BesovAtlas.map_extend_chartMeasure`), continuous
(`Manifold.BesovAtlas.continuousOn_densityTerm`) and positive
(`Manifold.BesovAtlas.chartDensity_pos`) on the target. This holds for every model `I`, with or
without boundary. -/
instance isSmoothMeasure_chartMeasure : IsSmoothMeasure I A.chartMeasure where
  exists_density e he := ⟨fun y => ENNReal.ofReal (A.chartDensity e y),
    ENNReal.continuous_ofReal.comp_continuousOn
      (continuousOn_finsetSum _ fun k _ => A.continuousOn_densityTerm he k),
    fun _ hy => ⟨ENNReal.ofReal_pos.2 (A.chartDensity_pos he hy), ENNReal.ofReal_lt_top⟩,
    A.map_extend_chartMeasure he⟩

end BesovAtlas

/-! ### Existence -/

/-- **Smooth measures exist**: every compact Hausdorff smooth manifold, with or without boundary,
carries a finite smooth measure (a continuous positive density in every chart), the chart
measure of a Besov atlas
(`Manifold.BesovAtlas.nonempty`, `Manifold.BesovAtlas.isSmoothMeasure_chartMeasure`,
`Manifold.BesovAtlas.isFiniteMeasure_chartMeasure`). -/
theorem exists_isSmoothMeasure [CompactSpace M] [T2Space M] [IsManifold I ∞ M] :
    ∃ μ : Measure M, IsSmoothMeasure I μ ∧ IsFiniteMeasure μ := by
  obtain ⟨A⟩ := BesovAtlas.nonempty I M
  exact ⟨A.chartMeasure, inferInstance, inferInstance⟩

/-- **The sphere carries a smooth measure**: the unit sphere `S^n ⊆ ℝ^(n+1)`, with Mathlib's
stereographic charts modelled on `ℝ^n`, is a compact manifold without boundary, and it carries a
finite smooth measure, the chart measure of a Besov atlas (`Manifold.exists_isSmoothMeasure`). -/
theorem exists_isSmoothMeasure_sphere (n : ℕ) :
    ∃ μ : Measure (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1),
      IsSmoothMeasure (𝓡 n) μ ∧ IsFiniteMeasure μ :=
  exists_isSmoothMeasure

end Manifold
