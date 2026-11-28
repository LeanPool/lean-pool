/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Smooth measures on manifolds

A measure `μ` on a manifold `M` modelled on `E` with corners `I` is **smooth**
(`Manifold.IsSmoothMeasure`) if in every chart `e` of the atlas the image of `μ` on the source of
`e` under the extended chart `κ = e.extend I` has a continuous density `ρ_e` with `0 < ρ_e < ∞`
with respect to the Lebesgue measure on the target `κ(e.source) ⊆ range I`:

`κ_* (μ|_{e.source}) = ρ_e · vol|_{κ(e.source)}`.

So a smooth measure in this project is a measure with a continuous positive density in every
chart; the results use the continuity of the densities and the bounds `0 < ρ_e < ∞`, and no
differentiability.

The extended chart is almost everywhere measurable on its source
(`Manifold.aemeasurable_extend_restrict`), and the parts inside the source of preimages of
measurable sets are measurable (`Manifold.measurableSet_source_inter_extend_preimage`).

The Lebesgue measure of a smooth bounded domain is a smooth measure on its closure
(`Rd.SmoothDomain.isSmoothMeasure_volumeOn`).

**Integrals in a chart** (`Manifold.IsSmoothMeasure.lintegral_source_eq`):
`∫_{e.source} F dμ = ∫_{κ(e.source)} ρ_e(y) F(κ⁻¹ y) dy`. For functions that vanish outside a
compact subset `K` of the source, the density is bounded above and below on `κ(K)`, so the
integrals over `M` and over the chart are comparable
(`Manifold.IsSmoothMeasure.exists_lintegral_chart_le`): the `L_p` norms on `M` and in the chart
are equivalent for such functions (`Manifold.IsSmoothMeasure.exists_eLpNorm_chart_le`).

**Null sets in charts**: on a closed subset `K` of the source, the extended chart (set to `0` off
the source, `Manifold.measurable_piecewise_extend`) is quasi-measure-preserving from `μ|_K` to the
Lebesgue measure (`Manifold.IsSmoothMeasure.quasiMeasurePreserving_piecewise_extend`), so a
property of almost every point of `E` holds at `κ x` for `μ`-almost every `x ∈ K`
(`Manifold.IsSmoothMeasure.ae_comp_extend`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [MeasurableSpace M] [BorelSpace M]

/-- A **smooth measure** on `M`, here a measure with a continuous positive density in every chart:
in every chart `e` of the atlas, the image of `μ` on the source of `e` under the extended chart is
a measure with a continuous density `ρ_e` with `0 < ρ_e < ∞` on the target, with respect to the
Lebesgue measure on the target. -/
class IsSmoothMeasure (μ : Measure M) : Prop where
  exists_density : ∀ e ∈ atlas H M, ∃ ρ : E → ℝ≥0∞, ContinuousOn ρ (e.extend I).target ∧
    (∀ y ∈ (e.extend I).target, 0 < ρ y ∧ ρ y < ∞) ∧
    Measure.map (e.extend I) (μ.restrict e.source) =
      (volume.restrict (e.extend I).target).withDensity ρ

omit [FiniteDimensional ℝ E] [ChartedSpace H M] [MeasurableSpace M] [BorelSpace M] in
/-- The target of an extended chart is measurable: it is the intersection of an open set with the
closed range of `I`. -/
theorem measurableSet_extend_target (e : OpenPartialHomeomorph M H) :
    MeasurableSet (e.extend I).target := by
  rw [e.extend_target]
  exact (I.continuous_symm.isOpen_preimage _ e.open_target).measurableSet.inter
    I.isClosed_range.measurableSet

omit [FiniteDimensional ℝ E] [ChartedSpace H M] in
/-- **The extended chart, set to `0` off the source, is measurable**: `κ = e.extend I` is
continuous on the open source (Mathlib's `ContinuousOn.measurable_piecewise`). -/
theorem measurable_piecewise_extend (e : OpenPartialHomeomorph M H)
    [∀ x, Decidable (x ∈ e.source)] :
    Measurable (e.source.piecewise (e.extend I) fun _ => (0 : E)) := by
  refine ContinuousOn.measurable_piecewise ?_ continuousOn_const e.open_source.measurableSet
  have h := e.continuousOn_extend (I := I)
  rwa [e.extend_source] at h

omit [FiniteDimensional ℝ E] [ChartedSpace H M] in
/-- **The extended chart is almost everywhere measurable on its source**: for every measure `μ` on
`M`, `κ = e.extend I` is almost everywhere measurable for `μ` restricted to the open source, on
which `κ` is continuous. -/
theorem aemeasurable_extend_restrict (e : OpenPartialHomeomorph M H) (μ : Measure M) :
    AEMeasurable (e.extend I) (μ.restrict e.source) := by
  have h := (e.continuousOn_extend (I := I)).aemeasurable (μ := μ)
    (by rw [e.extend_source]; exact e.open_source.measurableSet)
  rwa [e.extend_source] at h

omit [FiniteDimensional ℝ E] [ChartedSpace H M] in
/-- **Preimages under the extended chart within its source are measurable**: for a measurable
`B ⊆ E`, the set `e.source ∩ κ⁻¹(B)`, `κ = e.extend I`, is measurable. It is the part inside the
source of the preimage of `B` under the measurable map `Manifold.measurable_piecewise_extend`
(Mathlib's `Set.piecewise_preimage`). -/
theorem measurableSet_source_inter_extend_preimage (e : OpenPartialHomeomorph M H) {B : Set E}
    (hB : MeasurableSet B) : MeasurableSet (e.source ∩ e.extend I ⁻¹' B) := by
  classical
  have h := (measurable_piecewise_extend I e hB).inter e.open_source.measurableSet
  rwa [piecewise_preimage, ite_inter_self, inter_comm] at h

namespace IsSmoothMeasure

variable {I} {μ : Measure M} [IsSmoothMeasure I μ]

omit [ChartedSpace H M] [IsSmoothMeasure I μ] in
/-- **Integrals in a chart**: for a chart `e` of the atlas with density `ρ` and a measurable
`F ≥ 0`, `∫_{e.source} F dμ = ∫_{κ(e.source)} ρ(y) F(κ⁻¹ y) dy`. -/
theorem lintegral_source_eq {e : OpenPartialHomeomorph M H} {ρ : E → ℝ≥0∞}
    (hρc : ContinuousOn ρ (e.extend I).target)
    (hmap : Measure.map (e.extend I) (μ.restrict e.source) =
      (volume.restrict (e.extend I).target).withDensity ρ)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x in e.source, F x ∂μ =
      ∫⁻ y in (e.extend I).target, ρ y * F ((e.extend I).symm y) := by
  have hT := measurableSet_extend_target I e
  have hsrc : MeasurableSet e.source := e.open_source.measurableSet
  have hκ := aemeasurable_extend_restrict I e μ
  have hFs : AEMeasurable (fun y => F ((e.extend I).symm y))
      (volume.restrict (e.extend I).target) :=
    hF.comp_aemeasurable ((e.continuousOn_extend_symm (I := I)).aemeasurable hT)
  have hFs' : AEMeasurable (fun y => F ((e.extend I).symm y))
      (Measure.map (e.extend I) (μ.restrict e.source)) := by
    rw [hmap]
    exact hFs.mono_ac (withDensity_absolutelyContinuous _ _)
  calc ∫⁻ x in e.source, F x ∂μ
      = ∫⁻ x in e.source, F ((e.extend I).symm (e.extend I x)) ∂μ :=
        setLIntegral_congr_fun hsrc fun x hx => by rw [e.extend_left_inv hx]
    _ = ∫⁻ y, F ((e.extend I).symm y) ∂(Measure.map (e.extend I) (μ.restrict e.source)) :=
        (lintegral_map' hFs' hκ).symm
    _ = ∫⁻ y, F ((e.extend I).symm y) ∂((volume.restrict (e.extend I).target).withDensity ρ) := by
        rw [hmap]
    _ = ∫⁻ y in (e.extend I).target, ρ y * F ((e.extend I).symm y) :=
        lintegral_withDensity_eq_lintegral_mul₀ (hρc.aemeasurable hT) hFs

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The density is bounded above and below on compact sets**: on a compact `K'` inside the
target, `c ≤ ρ ≤ C` with `0 < c` and `C < ∞`, since `ρ` is continuous with values in `(0, ∞)`. -/
theorem exists_density_bounds {T : Set E} {ρ : E → ℝ≥0∞} (hρc : ContinuousOn ρ T)
    (hρ : ∀ y ∈ T, 0 < ρ y ∧ ρ y < ∞) {K' : Set E} (hK' : IsCompact K') (hK'T : K' ⊆ T) :
    ∃ c C : ℝ≥0∞, c ≠ 0 ∧ C ≠ ∞ ∧ ∀ y ∈ K', c ≤ ρ y ∧ ρ y ≤ C := by
  rcases K'.eq_empty_or_nonempty with h | hne
  · exact ⟨1, 1, one_ne_zero, ENNReal.one_ne_top, by simp [h]⟩
  obtain ⟨y₀, hy₀, hmin⟩ := hK'.exists_isMinOn hne (hρc.mono hK'T)
  obtain ⟨y₁, hy₁, hmax⟩ := hK'.exists_isMaxOn hne (hρc.mono hK'T)
  exact ⟨ρ y₀, ρ y₁, (hρ y₀ (hK'T hy₀)).1.ne', (hρ y₁ (hK'T hy₁)).2.ne,
    fun y hy => ⟨hmin hy, hmax hy⟩⟩

variable (μ) in
/-- **Integrals on `M` and in a chart are comparable** for functions that vanish outside a compact
subset `K` of the source of a chart `e` of the atlas: there are `c > 0` and `C < ∞` with
`∫_{κ(e.source)} F ∘ κ⁻¹ ≤ c⁻¹ ∫_M F dμ` and `∫_M F dμ ≤ C ∫_{κ(e.source)} F ∘ κ⁻¹`. -/
theorem exists_lintegral_chart_le {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M)
    {K : Set M} (hK : IsCompact K) (hKs : K ⊆ e.source) :
    ∃ c C : ℝ≥0∞, c ≠ 0 ∧ C ≠ ∞ ∧ ∀ F : M → ℝ≥0∞, Measurable F → (∀ x ∉ K, F x = 0) →
      (∫⁻ y in (e.extend I).target, F ((e.extend I).symm y) ≤ c⁻¹ * ∫⁻ x, F x ∂μ) ∧
      ∫⁻ x, F x ∂μ ≤ C * ∫⁻ y in (e.extend I).target, F ((e.extend I).symm y) := by
  obtain ⟨ρ, hρc, hρ, hmap⟩ := IsSmoothMeasure.exists_density (I := I) (μ := μ) e he
  set T := (e.extend I).target
  have hK' : IsCompact (e.extend I '' K) :=
    hK.image_of_continuousOn ((e.continuousOn_extend (I := I)).mono (by rwa [e.extend_source]))
  have hK'T : e.extend I '' K ⊆ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact (e.extend I).map_source (by rw [e.extend_source]; exact hKs hx)
  obtain ⟨c, C, hc, hC, hbd⟩ := exists_density_bounds hρc hρ hK' hK'T
  refine ⟨c, C, hc, hC, fun F hF hFK => ⟨?_, ?_⟩⟩
  · -- where `F ∘ κ⁻¹ ≠ 0`, the density is at least `c`
    have hsupp : ∀ y ∈ T, F ((e.extend I).symm y) ≠ 0 → c ≤ ρ y := fun y hy hne => by
      have hx : (e.extend I).symm y ∈ K := by
        by_contra h
        exact hne (hFK _ h)
      have hyK : y ∈ e.extend I '' K := ⟨_, hx, (e.extend I).right_inv hy⟩
      exact (hbd y hyK).1
    calc ∫⁻ y in T, F ((e.extend I).symm y)
        ≤ ∫⁻ y in T, c⁻¹ * (ρ y * F ((e.extend I).symm y)) := by
          refine setLIntegral_mono' (measurableSet_extend_target I e) fun y hy => ?_
          by_cases hne : F ((e.extend I).symm y) = 0
          · rw [hne]
            exact zero_le
          · rw [← mul_assoc]
            calc F ((e.extend I).symm y) = 1 * F ((e.extend I).symm y) := (one_mul _).symm
              _ ≤ c⁻¹ * ρ y * F ((e.extend I).symm y) := by
                  gcongr
                  calc (1 : ℝ≥0∞) = c⁻¹ * c := (ENNReal.inv_mul_cancel hc (ne_top_of_le_ne_top
                        (hρ y hy).2.ne (hsupp y hy hne))).symm
                    _ ≤ c⁻¹ * ρ y := mul_le_mul' le_rfl (hsupp y hy hne)
      _ = c⁻¹ * ∫⁻ y in T, ρ y * F ((e.extend I).symm y) := lintegral_const_mul' _ _
          (ENNReal.inv_ne_top.2 hc)
      _ = c⁻¹ * ∫⁻ x in e.source, F x ∂μ := by rw [lintegral_source_eq hρc hmap hF]
      _ ≤ c⁻¹ * ∫⁻ x, F x ∂μ := mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
  · -- `F` lives in the source, where the density is at most `C`
    have hsupp : Function.support F ⊆ e.source := fun x hx => hKs (by
      by_contra h
      exact hx (hFK x h))
    calc ∫⁻ x, F x ∂μ = ∫⁻ x in e.source, F x ∂μ := (setLIntegral_eq_of_support_subset hsupp).symm
      _ = ∫⁻ y in T, ρ y * F ((e.extend I).symm y) := lintegral_source_eq hρc hmap hF
      _ ≤ ∫⁻ y in T, C * F ((e.extend I).symm y) := by
          refine setLIntegral_mono' (measurableSet_extend_target I e) fun y hy => ?_
          by_cases hne : F ((e.extend I).symm y) = 0
          · rw [hne, mul_zero, mul_zero]
          · have hx : (e.extend I).symm y ∈ K := by
              by_contra h
              exact hne (hFK _ h)
            exact mul_le_mul' (hbd y ⟨_, hx, (e.extend I).right_inv hy⟩).2 le_rfl
      _ = C * ∫⁻ y in T, F ((e.extend I).symm y) := lintegral_const_mul' _ _ hC

variable (μ) in
/-- **`L_p` norms on `M` and in a chart are comparable** for strongly measurable functions that
vanish outside a compact subset `K` of the source of a chart `e` of the atlas: for `0 < p < ∞`
there are `c, C < ∞` with `‖1_{κ(e.source)} (G ∘ κ⁻¹)‖_p ≤ c ‖G‖_{L_p(μ)}` and
`‖G‖_{L_p(μ)} ≤ C ‖1_{κ(e.source)} (G ∘ κ⁻¹)‖_p`
(`Manifold.IsSmoothMeasure.exists_lintegral_chart_le` for `‖G‖^p`, with Mathlib's
`MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict` for the indicator). -/
theorem exists_eLpNorm_chart_le {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M)
    {K : Set M} (hK : IsCompact K) (hKs : K ⊆ e.source) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    {F : Type*} [NormedAddCommGroup F] :
    ∃ c C : ℝ≥0∞, c ≠ ∞ ∧ C ≠ ∞ ∧ ∀ G : M → F, StronglyMeasurable G → (∀ x ∉ K, G x = 0) →
      eLpNorm ((e.extend I).target.indicator fun y => G ((e.extend I).symm y)) p volume ≤
          c * eLpNorm G p μ ∧
        eLpNorm G p μ ≤
          C * eLpNorm ((e.extend I).target.indicator fun y => G ((e.extend I).symm y)) p
            volume := by
  obtain ⟨c, C, hc, hC, hcmp⟩ := exists_lintegral_chart_le (I := I) μ he hK hKs
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  refine ⟨c⁻¹ ^ (1 / p.toReal), C ^ (1 / p.toReal),
    ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.inv_ne_top.2 hc),
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hC, fun G hG hGK => ?_⟩
  have hT := measurableSet_extend_target I e
  have hκ : AEMeasurable (e.extend I).symm (volume.restrict (e.extend I).target) :=
    (e.continuousOn_extend_symm (I := I)).aemeasurable hT
  have hFK : ∀ x ∉ K, ‖G x‖ₑ ^ p.toReal = 0 := fun x hx => by
    rw [hGK x hx, eNorm_zero, ENNReal.zero_rpow_of_pos hr]
  obtain ⟨h1, h2⟩ := hcmp _ (hG.eNorm.pow_const _) hFK
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hT.nullMeasurableSet,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp (f := fun y => G ((e.extend I).symm y))
      (hG.aestronglyMeasurable.comp_aemeasurable hκ),
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hG.aestronglyMeasurable,
    ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / p.toReal),
    ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / p.toReal)]
  exact ⟨ENNReal.rpow_le_rpow h1 (by positivity), ENNReal.rpow_le_rpow h2 (by positivity)⟩

omit [ChartedSpace H M] [MeasurableSpace M] [BorelSpace M] in
/-- **A chart integral of the indicator of a pulled-back set**: for `K ⊆ e.source` and a set `N`
of `E`, the integral over the target of `1_S ∘ κ⁻¹`, `S = K ∩ κ⁻¹(N)`, is at most `|N|`, where
`κ = e.extend I` is set to `0` off the source. -/
theorem setLIntegral_indicator_preimage_le {e : OpenPartialHomeomorph M H} {K : Set M}
    (hKs : K ⊆ e.source) [∀ x, Decidable (x ∈ e.source)] (N : Set E) :
    ∫⁻ y in (e.extend I).target,
        (K ∩ (e.source.piecewise (e.extend I) fun _ => (0 : E)) ⁻¹' N).indicator 1
          ((e.extend I).symm y) ≤ volume N := by
  set S := K ∩ (e.source.piecewise (e.extend I) fun _ => (0 : E)) ⁻¹' N
  calc ∫⁻ y in (e.extend I).target, S.indicator 1 ((e.extend I).symm y)
      ≤ ∫⁻ y in (e.extend I).target, (toMeasurable volume N).indicator 1 y := by
        refine setLIntegral_mono' (measurableSet_extend_target I e) fun y hy => ?_
        by_cases hyS : (e.extend I).symm y ∈ S
        · have hyN : y ∈ N := by
            have h := hyS.2
            rwa [mem_preimage, piecewise_eq_of_mem _ _ _ (hKs hyS.1),
              (e.extend I).right_inv hy] at h
          rw [indicator_of_mem hyS, indicator_of_mem (subset_toMeasurable _ _ hyN)]
          exact le_rfl
        · rw [indicator_of_notMem hyS]
          exact zero_le
    _ ≤ ∫⁻ y, (toMeasurable volume N).indicator 1 y := setLIntegral_le_lintegral _ _
    _ = volume N := by
        rw [lintegral_indicator_one (measurableSet_toMeasurable _ _), measure_toMeasurable]

variable (μ) in
/-- **Charts pull null sets back to null sets**: for a chart `e` of the atlas and a closed
`K ⊆ e.source`, the extended chart `κ = e.extend I`, set to `0` off the source, is
quasi-measure-preserving from `μ|_K` to the Lebesgue measure. For a null set `N`,
`μ(K ∩ κ⁻¹(N)) ≤ C ∫_{κ(e.source)} 1_{K ∩ κ⁻¹(N)} ∘ κ⁻¹ ≤ C |N| = 0`
(`Manifold.IsSmoothMeasure.exists_lintegral_chart_le`). -/
theorem quasiMeasurePreserving_piecewise_extend [CompactSpace M] {e : OpenPartialHomeomorph M H}
    (he : e ∈ atlas H M) {K : Set M} (hK : IsClosed K) (hKs : K ⊆ e.source)
    [∀ x, Decidable (x ∈ e.source)] :
    QuasiMeasurePreserving (e.source.piecewise (e.extend I) fun _ => (0 : E))
      (μ.restrict K) volume := by
  have hκ := measurable_piecewise_extend I e
  refine ⟨hκ.aemeasurable, Measure.AbsolutelyContinuous.mk fun N hN hN0 => ?_⟩
  obtain ⟨c, C, -, -, hcmp⟩ := exists_lintegral_chart_le (I := I) μ he hK.isCompact hKs
  have hS : MeasurableSet (K ∩ (e.source.piecewise (e.extend I) fun _ => (0 : E)) ⁻¹' N) :=
    hK.measurableSet.inter (hκ hN)
  have h := (hcmp _ (measurable_one.indicator hS)
    fun x hx => indicator_of_notMem (fun h : x ∈ K ∩ _ => hx h.1) _).2
  rw [lintegral_indicator_one hS] at h
  rw [Measure.map_apply hκ hN, Measure.restrict_apply (hκ hN), inter_comm]
  exact le_antisymm (h.trans ((mul_le_mul' le_rfl (setLIntegral_indicator_preimage_le hKs N)).trans
    (by rw [hN0, mul_zero]))) zero_le

/-- **Null sets in a chart are null on `M`**: for a chart `e` of the atlas, a closed set
`K ⊆ e.source` and a property `P` of almost every point of `E`, `P (κ x)` holds for `μ`-almost every
`x ∈ K`, `κ = e.extend I` (`Manifold.IsSmoothMeasure.quasiMeasurePreserving_piecewise_extend` and
Mathlib's `MeasureTheory.QuasiMeasurePreserving.ae`). -/
theorem ae_comp_extend [CompactSpace M] {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M)
    {K : Set M} (hK : IsClosed K) (hKs : K ⊆ e.source) {P : E → Prop}
    (hP : ∀ᵐ y ∂volume, P y) : ∀ᵐ x ∂μ, x ∈ K → P (e.extend I x) := by
  classical
  have h := (quasiMeasurePreserving_piecewise_extend (I := I) μ he hK hKs).ae hP
  filter_upwards [(ae_restrict_iff' hK.measurableSet).1 h] with x hx hxK
  simpa only [piecewise_eq_of_mem _ _ _ (hKs hxK)] using hx hxK

end IsSmoothMeasure

end Manifold
