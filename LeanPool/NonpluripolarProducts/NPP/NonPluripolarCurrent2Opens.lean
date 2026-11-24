/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.NPP.NonPluripolarCurrent2Measure

/-!
# Measures of manifold currents over open sets and the source well-definedness condition

Source: `chapter_npp.tex`, `def:npp:L69` (`eq:welldefinepluri`: "for each connected open subset
`U ⊆ X`, any smooth positive `(1,1)`-form `ω` on `U`, and each compact subset `K ⊆ U`,
`sup_k ∫_{K ∩ O_k} (⋀ⱼ dd^c (φⱼ ∨ (-k)))|_U ∧ ω^{dim U - p} < ∞`"); conventions: positive forms
are not necessarily strictly positive.

`M` is a complex manifold (mathlib holomorphic atlas, as in `SGPT.NPP.BedfordTaylorManifold`);
currents on `M` are compatible chart families (`SGPT.NPP.PositiveCurrent`).

* `SemipositiveFormOn U` — a smooth semipositive `(1,1)`-form on an open `U ⊆ M`, given by its
  coordinate expressions on the coordinate domains `e(e.source ∩ U)` (`chartDomain e U`) of all
  atlas charts, related by the tensor transformation law along the coordinate changes.
* `chartWedgeMeasure T θ e` — the local measure `T ∧ θ^q` of the coordinate expressions, on
  `chartDomain e U`, pushed to `M`; `chartWedgeMeasure_restrict_source` — **these local measures
  agree on overlaps** (biholomorphic invariance,
    `NonPluripolarCurrent.wedgePowerMeasure_pullback`).
* `wedgeMeasureOn T θ hK` — **the measure `(T|_U ∧ θ^q)|_K`** on a compact `K ⊆ M` (`M`
  Hausdorff, Borel), glued from a finite chart cover of `K` (`FiniteMeasureGluing`);
  `wedgeMeasureOn_restrict_source` — its restriction to every chart domain is the local measure,
  which characterizes it (`eq_wedgeMeasureOn`).
* `truncatedCurrent`, `strictLocusM` — the products `⋀ⱼ dd^c (φⱼ ∨ (-k))` as positive currents on
  `M`, and the Borel sets `O_k`.
* `IsNonPluripolarWellDefinedOnOpens` — **`eq:welldefinepluri` with the source's quantifiers**
  (all connected open `U ⊆ M`, all smooth semipositive `(1,1)`-forms on `U`, all compact
  `K ⊆ U`); `isNonPluripolarWellDefinedOnOpens_iff` — **it is equivalent to the chart condition
  `IsNonPluripolarWellDefined`** (one direction by finite covers of `K` by coordinate balls, the
  other with the forms `SemipositiveFormOn.ofChart` transported from one chart);
  `nonPluripolarProductOfOpens` — the product under the source condition, with the defining
  identities in every chart.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal Manifold

namespace SGPT.NPP

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorLocality
open SGPT.Foundations.Analysis.Pending.LocalCurrentPullback
open SGPT.NPP.NonPluripolarCurrent

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-! ### Coordinate domains and forms on open subsets -/

section Forms

/-- The coordinate domain `e(e.source ∩ U)` of an open `U ⊆ M` in the chart `e`. -/
def chartDomain (e : ComplexChart n M) (U : Opens M) : Opens (ComplexModel n) :=
  ⟨e.val.target ∩ e.val.symm ⁻¹' U, e.val.isOpen_inter_preimage_symm U.isOpen⟩

theorem chartDomain_le (e : ComplexChart n M) (U : Opens M) : chartDomain e U ≤ chartTarget e :=
  fun _ hz => hz.1

theorem mem_chartDomain {e : ComplexChart n M} {U : Opens M} {z : ComplexModel n} :
    z ∈ chartDomain e U ↔ z ∈ e.val.target ∧ e.val.symm z ∈ U := Iff.rfl

variable (n) in
/-- **A smooth semipositive `(1,1)`-form on an open subset `U` of `M`** (the source's "smooth
positive `(1,1)`-form", positive meaning semipositive): in every atlas chart `e`, a smooth family
of semipositive `(1,1)`-forms on the coordinate domain `e(e.source ∩ U)`, the expressions being
related on overlaps by the tensor transformation law along the coordinate change. -/
structure SemipositiveFormOn (U : Opens M) where
  /-- The coordinate expression in the chart `e` (meaningful on `chartDomain e U`). -/
  coeff : ComplexChart n M → ComplexModel n → RealForm n 2
  smooth : ∀ e, ContDiffOn ℝ ∞ (coeff e) (chartDomain e U)
  semipositive : ∀ e, ∀ z ∈ chartDomain e U, IsSemipositiveOneOne (coeff e z)
  compatible : ∀ e f, ∀ z ∈ chartDomain e U, z ∈ (chartTransition e f).source →
    coeff e z =
      (coeff f (chartTransition e f z)).compContinuousLinearMap (chartTransitionDerivative e f z)

end Forms

/-! ### Measurable inverse charts -/

section Inverse

open Classical in
/-- A measurable map equal to the inverse chart `e⁻¹` on the coordinate domain. -/
def chartInv (e : ComplexChart n M) : ComplexModel n → M :=
  e.val.target.piecewise e.val.symm fun _ => e.val.symm 0

theorem chartInv_of_mem {e : ComplexChart n M} {z : ComplexModel n} (hz : z ∈ e.val.target) :
    chartInv e z = e.val.symm z := by
  classical
  exact Set.piecewise_eq_of_mem _ _ _ hz

variable [MeasurableSpace M] [BorelSpace M]

theorem measurable_chartInv (e : ComplexChart n M) : Measurable (chartInv e) := by
  classical
  exact e.val.continuousOn_symm.measurable_piecewise continuousOn_const
    e.val.open_target.measurableSet

end Inverse

/-! ### The local measures `T ∧ ω^q` and their compatibility -/

section ChartMeasure

variable [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] [MeasurableSpace M] [BorelSpace M] {q : ℕ}

/-- The local measure `T ∧ ω^q` in the chart `e`, on the coordinate domain of `U`, as a measure
on `M`: the push-forward along `e⁻¹` of `(T_e ∧ ω_e^q)|_{e(e.source ∩ U)}`. -/
def chartWedgeMeasure (T : PositiveCurrent n M q) {U : Opens M} (θ : SemipositiveFormOn n U)
    (e : ComplexChart n M) : Measure M :=
  ((wedgePowerMeasure (T.inChart e) (θ.coeff e)).restrict (chartDomain e U)).map (chartInv e)

theorem chartWedgeMeasure_apply (T : PositiveCurrent n M q) {U : Opens M}
    (θ : SemipositiveFormOn n U) (e : ComplexChart n M) {s : Set M} (hs : MeasurableSet s) :
    chartWedgeMeasure T θ e s =
      wedgePowerMeasure (T.inChart e) (θ.coeff e) (chartInv e ⁻¹' s ∩ chartDomain e U) := by
  rw [chartWedgeMeasure, Measure.map_apply (measurable_chartInv e) hs,
    Measure.restrict_apply (measurable_chartInv e hs)]

/-- The local measure is carried by `e.source ∩ U`. -/
theorem chartWedgeMeasure_compl (T : PositiveCurrent n M q) {U : Opens M}
    (θ : SemipositiveFormOn n U) (e : ComplexChart n M) :
    chartWedgeMeasure T θ e ((e.val.source ∩ U : Set M)ᶜ) = 0 := by
  have hm : MeasurableSet ((e.val.source ∩ U : Set M)ᶜ) :=
    (e.val.open_source.inter U.isOpen).measurableSet.compl
  rw [chartWedgeMeasure_apply T θ e hm]
  refine measure_mono_null (fun z hz => ?_) measure_empty
  obtain ⟨hz1, hz2⟩ := hz
  rw [mem_preimage, chartInv_of_mem hz2.1] at hz1
  exact absurd ⟨e.val.map_target hz2.1, hz2.2⟩ hz1

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] [MeasurableSpace M] [BorelSpace M] in
/-- The part of the overlap of `e` and `f` lying over `U`, in `f`-coordinates. -/
def overlapDomain (e f : ComplexChart n M) (U : Opens M) : Opens (ComplexModel n) :=
  overlapTarget e f ⊓ chartDomain f U

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] [MeasurableSpace M] [BorelSpace M] in
theorem mem_overlapDomain {e f : ComplexChart n M} {U : Opens M} {y : ComplexModel n} :
    y ∈ overlapDomain e f U ↔ y ∈ chartDomain f U ∧ f.val.symm y ∈ e.val.source := by
  change y ∈ (chartTransition e f).target ∧ y ∈ chartDomain f U ↔ _
  simp only [chartTransition, OpenPartialHomeomorph.trans_target,
    OpenPartialHomeomorph.symm_target,
    mem_inter_iff, mem_preimage]
  exact ⟨fun ⟨⟨_, h1⟩, h2⟩ => ⟨h2, h1⟩, fun ⟨h2, h1⟩ => ⟨⟨h2.1, h1⟩, h2⟩⟩

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] [MeasurableSpace M] [BorelSpace M] in
theorem overlapDomain_le (e f : ComplexChart n M) (U : Opens M) :
    overlapDomain e f U ≤ overlapTarget e f := inf_le_left

omit [MeasurableSpace M] [BorelSpace M] in
theorem mem_preOpen_overlapDomain {e f : ComplexChart n M} {U : Opens M} {z : ComplexModel n} :
    z ∈ LocalCurrentPullbackDdc.preOpen (chartTransition_isBiholomorphicPair e f)
        (overlapDomain e f U) ↔ z ∈ chartDomain e U ∧ e.val.symm z ∈ f.val.source := by
  rw [LocalCurrentPullbackDdc.mem_preOpen]
  change z ∈ (chartTransition e f).source ∧ chartTransition e f z ∈ overlapDomain e f U ↔ _
  simp only [chartTransition, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source,
    mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨⟨hz, hzf⟩, hy⟩
    have hy' := (mem_overlapDomain.mp hy).1
    refine ⟨⟨hz, ?_⟩, hzf⟩
    have := hy'.2
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply] at this
    rw [mem_preimage, f.val.left_inv hzf] at this
    exact this
  · rintro ⟨⟨hz, hzU⟩, hzf⟩
    refine ⟨⟨hz, hzf⟩, ?_⟩
    have hmem : (e.val.symm.trans f.val) z ∈ (chartTransition e f).target :=
      (chartTransition e f).map_source (show z ∈ (chartTransition e f).source from
        by simp only [chartTransition, OpenPartialHomeomorph.trans_source,
          OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage]; exact ⟨hz, hzf⟩)
    refine ⟨hmem, f.val.map_source hzf, ?_⟩
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
    rw [mem_preimage, f.val.left_inv hzf]
    exact hzU

variable (T : PositiveCurrent n M q) {U : Opens M} (θ : SemipositiveFormOn n U)

omit [MeasurableSpace M] [BorelSpace M] in
/-- **Local compatibility of the measures `T ∧ θ^q` on an overlap**:
`(T_e ∧ θ_e^q)|_{A'} = σ_*((T_f ∧ θ_f^q)|_{B'})`, where `B'` is the part of the overlap over `U`
in `f`-coordinates, `A' = σ(B')` and `σ = e ∘ f⁻¹`. -/
theorem wedgePowerMeasure_overlap (e f : ComplexChart n M) :
    (wedgePowerMeasure (T.inChart e) (θ.coeff e)).restrict
        (LocalCurrentPullbackDdc.preOpen (chartTransition_isBiholomorphicPair e f)
          (overlapDomain e f U)) =
      ((wedgePowerMeasure (T.inChart f) (θ.coeff f)).restrict (overlapDomain e f U)).map
        (onOpen (overlapDomain e f U) (chartTransition e f).symm) := by
  set h := chartTransition_isBiholomorphicPair e f
  set B' := overlapDomain e f U
  have hB'B : B' ≤ overlapTarget e f := overlapDomain_le e f U
  set h' := LocalCurrentPullbackDdc.isBiholomorphicPair_preOpen h hB'B
  have hA'e : LocalCurrentPullbackDdc.preOpen h B' ≤ chartTarget e :=
    (LocalCurrentPullbackDdc.preOpen_le h B').trans (overlapSource_le e f)
  have hB'f : B' ≤ chartTarget f := hB'B.trans (overlapTarget_le e f)
  have hcur : restrict hA'e (T.inChart e) =
      pullback h' (isPositive_restrict (T.isPositive f) hB'f) := by
    have h1 := congrArg (restrict (LocalCurrentPullbackDdc.preOpen_le h B')) (T.compatible e f)
    rw [NonPluripolarCurrent.restrict_restrict] at h1
    rw [h1, ← LocalCurrentPullbackDdc.pullback_restrict h
      (isPositive_restrict (T.isPositive f) (overlapTarget_le e f)) hB'B]
    exact pullback_congr_current h' _ _
      (NonPluripolarCurrent.restrict_restrict hB'B (overlapTarget_le e f) _)
  have hA'D : ∀ z ∈ LocalCurrentPullbackDdc.preOpen h B', z ∈ chartDomain e U := fun z hz =>
    (mem_preOpen_overlapDomain.mp hz).1
  rw [← wedgePowerMeasure_restrict (T.isPositive e) hA'e, hcur,
    wedgePowerMeasure_pullback h' _ ((θ.smooth e).mono hA'D)
      (fun z hz => θ.semipositive e z (hA'D z hz)) (α := θ.coeff f) (fun z hz => ?_),
    wedgePowerMeasure_restrict (T.isPositive f) hB'f,
    Measure.restrict_restrict_of_subset subset_rfl]
  have hzA : z ∈ overlapSource e f := LocalCurrentPullbackDdc.preOpen_le h B' hz
  rw [θ.compatible e f z (hA'D z hz) hzA, chartTransitionDerivative, fderiv_real_eq h hzA]

/-- The local measure restricted to another chart domain, in coordinates. -/
theorem chartWedgeMeasure_restrict (e g : ComplexChart n M) :
    (chartWedgeMeasure T θ e).restrict g.val.source =
      ((wedgePowerMeasure (T.inChart e) (θ.coeff e)).restrict
        ((chartDomain e U : Set (ComplexModel n)) ∩ {z | e.val.symm z ∈ g.val.source})).map
          (chartInv e) := by
  rw [chartWedgeMeasure, Measure.restrict_map (measurable_chartInv e)
    g.val.open_source.measurableSet,
    Measure.restrict_restrict (measurable_chartInv e g.val.open_source.measurableSet)]
  congr 2
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    rw [chartInv_of_mem h2.1] at h1
    exact ⟨h2, h1⟩
  · rintro ⟨h2, h1⟩
    rw [← chartInv_of_mem h2.1] at h1
    exact ⟨h1, h2⟩

/-- **The local measures `T ∧ θ^q` agree on overlaps** (as measures on `M`). -/
theorem chartWedgeMeasure_restrict_source (e f : ComplexChart n M) :
    (chartWedgeMeasure T θ e).restrict f.val.source =
      (chartWedgeMeasure T θ f).restrict e.val.source := by
  set h := chartTransition_isBiholomorphicPair e f
  set B' := overlapDomain e f U
  have hB'B : B' ≤ overlapTarget e f := overlapDomain_le e f U
  set h' := LocalCurrentPullbackDdc.isBiholomorphicPair_preOpen h hB'B
  have hsetA : (chartDomain e U : Set (ComplexModel n)) ∩ {z | e.val.symm z ∈ f.val.source} =
      (LocalCurrentPullbackDdc.preOpen h B' : Set (ComplexModel n)) := by
    ext z
    rw [SetLike.mem_coe, mem_preOpen_overlapDomain]
    rfl
  have hsetB : (chartDomain f U : Set (ComplexModel n)) ∩ {y | f.val.symm y ∈ e.val.source} =
      (B' : Set (ComplexModel n)) := by
    ext y
    rw [SetLike.mem_coe, mem_overlapDomain]
    rfl
  rw [chartWedgeMeasure_restrict, chartWedgeMeasure_restrict, hsetA, hsetB,
    wedgePowerMeasure_overlap T θ e f, Measure.map_map (measurable_chartInv e)
      (measurable_onOpen_inv h')]
  refine Measure.map_congr ?_
  filter_upwards [ae_restrict_mem B'.isOpen.measurableSet] with y hy
  have hyf := mem_overlapDomain.mp hy
  have hσy := h'.mapsTo_inv hy
  rw [Function.comp_apply, onOpen_of_mem hy, chartInv_of_mem (overlapSource_le e f
      (LocalCurrentPullbackDdc.preOpen_le h B' hσy)), chartInv_of_mem hyf.1.1]
  change e.val.symm ((f.val.symm.trans e.val) y) = f.val.symm y
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, e.val.left_inv hyf.2]

end ChartMeasure

/-! ### The measure `(T|_U ∧ θ^q)|_K` on a compact set -/

section Compact

variable [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] [MeasurableSpace M] [BorelSpace M] [T2Space M]
  {q : ℕ}

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] [MeasurableSpace M] [BorelSpace M] [T2Space M] in
theorem exists_finite_chart_cover {K : Set M} (hK : IsCompact K) :
    ∃ (m : ℕ) (c : Fin m → ComplexChart n M), K ⊆ ⋃ i, (c i).val.source := by
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun x : M => (complexChartAt (n := n) x).val.source)
    (fun x => (complexChartAt (n := n) x).val.open_source)
    (fun x _ => mem_iUnion.mpr ⟨x, mem_complexChartAt_source x⟩)
  refine ⟨t.card, fun i => complexChartAt (t.equivFin.symm i).1, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (ht hx)
  refine mem_iUnion.mpr ⟨t.equivFin ⟨y, hy⟩, ?_⟩
  simpa using hxy

/-- The number of charts of the chosen finite chart cover of a compact set. -/
def coverSize {K : Set M} (hK : IsCompact K) : ℕ :=
  Classical.choose (exists_finite_chart_cover (n := n) hK)

/-- The chosen finite chart cover of a compact set. -/
def coverChart {K : Set M} (hK : IsCompact K) : Fin (coverSize (n := n) hK) → ComplexChart n M :=
  Classical.choose (Classical.choose_spec (exists_finite_chart_cover (n := n) hK))

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] [MeasurableSpace M] [BorelSpace M] [T2Space M] in
theorem subset_iUnion_coverChart {K : Set M} (hK : IsCompact K) :
    K ⊆ ⋃ i, (coverChart (n := n) hK i).val.source :=
  Classical.choose_spec (Classical.choose_spec (exists_finite_chart_cover (n := n) hK))

variable (T : PositiveCurrent n M q) {U : Opens M} (θ : SemipositiveFormOn n U)

/-- **The measure `(T|_U ∧ θ^q)|_K`** of a positive current `T` of bidimension `(q,q)` on `M`,
a smooth semipositive `(1,1)`-form `θ` on an open `U ⊆ M` and a compact `K ⊆ M`: the local
measures `T_e ∧ θ_e^q` of a finite chart cover of `K`, glued (`FiniteMeasureGluing.glue`) and
restricted to `K`.  It is characterized by its restrictions to all chart domains
(`wedgeMeasureOn_restrict_source`, `eq_wedgeMeasureOn`), so it does not depend on the cover. -/
def wedgeMeasureOn {K : Set M} (hK : IsCompact K) : Measure M :=
  (FiniteMeasureGluing.glue (fun i => (coverChart (n := n) hK i).val.source)
    (fun i => chartWedgeMeasure T θ (coverChart hK i))).restrict K

omit [T2Space M] in
theorem ae_mem_source_chartWedgeMeasure (e : ComplexChart n M) :
    ∀ᵐ x ∂chartWedgeMeasure T θ e, x ∈ e.val.source :=
  (measure_eq_zero_iff_ae_notMem.mp (chartWedgeMeasure_compl T θ e)).mono fun x hx => by
    simp only [mem_compl_iff, not_not] at hx
    exact hx.1

/-- **On every chart domain, `(T|_U ∧ θ^q)|_K` is the local measure**:
`(T|_U ∧ θ^q)|_K` restricted to `e.source` is `(T_e ∧ θ_e^q)|_{K ∩ e.source}`. -/
theorem wedgeMeasureOn_restrict_source {K : Set M} (hK : IsCompact K) (e : ComplexChart n M) :
    (wedgeMeasureOn T θ hK).restrict e.val.source =
      (chartWedgeMeasure T θ e).restrict (K ∩ e.val.source) := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hsrc : MeasurableSet e.val.source := e.val.open_source.measurableSet
  have hμe : (chartWedgeMeasure T θ e).restrict e.val.source = chartWedgeMeasure T θ e :=
    Measure.restrict_eq_self_of_ae_mem (ae_mem_source_chartWedgeMeasure T θ e)
  rw [wedgeMeasureOn, Measure.restrict_restrict hsrc, inter_comm]
  refine FiniteMeasureGluing.glue_restrict _ _
    (fun i => (coverChart hK i).val.open_source.measurableSet) (hKm.inter hsrc)
    (inter_subset_left.trans (subset_iUnion_coverChart hK)) _ fun i => ?_
  set c := coverChart (n := n) hK i
  have hci : MeasurableSet (c.val.source ∩ K) := c.val.open_source.measurableSet.inter hKm
  have hset : c.val.source ∩ (K ∩ e.val.source) = (c.val.source ∩ K) ∩ e.val.source :=
    (inter_assoc _ _ _).symm
  have hset' : (c.val.source ∩ K) ∩ c.val.source = c.val.source ∩ K := by
    rw [inter_assoc, inter_comm K, ← inter_assoc, inter_self]
  rw [hset, ← Measure.restrict_restrict hci, chartWedgeMeasure_restrict_source T θ c e,
    Measure.restrict_restrict hci, hset']
  conv_lhs => rw [← hμe]
  rw [Measure.restrict_restrict hci]

/-- `(T|_U ∧ θ^q)|_K` is carried by `K`. -/
theorem wedgeMeasureOn_compl {K : Set M} (hK : IsCompact K) :
    wedgeMeasureOn T θ hK Kᶜ = 0 := by
  rw [wedgeMeasureOn, Measure.restrict_apply hK.isClosed.measurableSet.compl, compl_inter_self,
    measure_empty]

/-- **Uniqueness**: a measure carried by `K` whose restriction to every chart domain is the local
measure is `(T|_U ∧ θ^q)|_K`. -/
theorem eq_wedgeMeasureOn {K : Set M} (hK : IsCompact K) {ν : Measure M} (hνK : ν Kᶜ = 0)
    (hν : ∀ e : ComplexChart n M,
      ν.restrict e.val.source = (chartWedgeMeasure T θ e).restrict (K ∩ e.val.source)) :
    ν = wedgeMeasureOn T θ hK := by
  have hcov := subset_iUnion_coverChart (n := n) hK
  have hae : ∀ {μ : Measure M}, μ Kᶜ = 0 →
      ∀ᵐ x ∂μ, x ∈ ⋃ i, (coverChart (n := n) hK i).val.source := fun {μ} h =>
    (measure_eq_zero_iff_ae_notMem.mp h).mono fun x hx => hcov (by simpa using hx)
  rw [← Measure.restrict_eq_self_of_ae_mem (hae hνK),
    ← Measure.restrict_eq_self_of_ae_mem (hae (wedgeMeasureOn_compl T θ hK))]
  refine Measure.restrict_iUnion_congr.mpr fun i => ?_
  rw [hν, wedgeMeasureOn_restrict_source]

/-- For `A ⊆ e.source`: `(T|_U ∧ θ^q)|_K (A) ≤ (T_e ∧ θ_e^q)(A)`. -/
theorem wedgeMeasureOn_le_chart {K : Set M} (hK : IsCompact K) (e : ComplexChart n M)
    {A : Set M} (hA : A ⊆ e.val.source) : wedgeMeasureOn T θ hK A ≤ chartWedgeMeasure T θ e A := by
  have h := congrArg (fun μ : Measure M => μ A) (wedgeMeasureOn_restrict_source T θ hK e)
  rw [Measure.restrict_apply' e.val.open_source.measurableSet, inter_eq_left.mpr hA] at h
  rw [h]
  exact Measure.restrict_apply_le _ _

end Compact

/-! ### The truncated products on the manifold and the strict loci -/

section Truncation

variable [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] {p q : ℕ} (hqp : q + p = n)

/-- **The Bedford–Taylor products of the truncations** `⋀ⱼ dd^c (φⱼ ∨ (-k))` of psh functions on
`M`, as positive currents on `M` (in every chart, the local truncated products). -/
def truncatedCurrent (φ : Fin p → M → EReal) (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i))
    (k : ℕ) : PositiveCurrent n M q where
  inChart e := truncatedBT hqp (chartTarget e) (fun i z => φ i (e.val.symm z)) k
  isPositive e := (isPositive_truncatedBT hqp (chartPlurisubharmonicOn hφ e) k).1
  compatible e f := by
    have hh := chartTransition_isBiholomorphicPair e f
    have hφf := chartPlurisubharmonicOn hφ f
    have hφB : ∀ i, PlurisubharmonicOn (fun z => φ i (f.val.symm z)) (overlapTarget e f) :=
      fun i => (hφf i).mono (overlapTarget_le e f)
    have hcongr : ∀ i, ∀ x ∈ overlapSource e f,
        φ i (e.val.symm x) = φ i (f.val.symm (chartTransition e f x)) := by
      intro i x hx
      have hx' : x ∈ (chartTransition e f).source := hx
      have hxf : e.val.symm x ∈ f.val.source := by
        simp only [chartTransition, OpenPartialHomeomorph.trans_source,
          OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage] at hx'
        exact hx'.2
      simp only [chartTransition, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
        f.val.left_inv hxf]
    rw [← truncatedBT_restrict hqp (chartPlurisubharmonicOn hφ e) (overlapSource_le e f),
      pullback_congr_current hh _ (isPositive_truncatedBT hqp hφB k).1
        (truncatedBT_restrict hqp hφf (overlapTarget_le e f) k).symm,
      pullback_truncatedBT hqp hh hφB k]
    exact congrFun (truncatedBT_congr hqp (U := overlapSource e f) hcongr) k

/-- The strict locus `O_k = {φ₁ > -k, …, φ_p > -k}` on `M`. -/
def strictLocusM (φ : Fin p → M → EReal) (k : ℕ) : Set M :=
  {x | ∀ i, ((-(k : ℝ) : ℝ) : EReal) < φ i x}

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] in
/-- Psh functions on a manifold are upper semicontinuous. -/
theorem upperSemicontinuous_of_manifoldPSH {u : M → EReal}
    (hu : SGPT.PSH.ManifoldPSH (n := n) u) : UpperSemicontinuous u := by
  intro x y hy
  obtain ⟨e, hxe, V, hV, -, -, hxV, hpu⟩ := hu x
  have hy' : chartFunction u e (e.val x) < y := by
    simpa [chartFunction, e.val.left_inv hxe] using hy
  have h0 : ∀ᶠ z in 𝓝 (e.val x), chartFunction u e z < y := by
    have := hpu.disc.upperSemicontinuousOn (e.val x) hxV y hy'
    rwa [nhdsWithin_eq_nhds.mpr (hV.mem_nhds hxV)] at this
  have h1 := (e.val.continuousAt hxe).eventually h0
  filter_upwards [h1, e.val.open_source.mem_nhds hxe] with x' hx' hx's
  simpa [chartFunction, e.val.left_inv hx's] using hx'

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] in
theorem measurableSet_strictLocusM [MeasurableSpace M] [BorelSpace M] {φ : Fin p → M → EReal}
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i)) (k : ℕ) :
    MeasurableSet (strictLocusM φ k) := by
  have e : strictLocusM φ k = ⋂ i, {x | ((-(k : ℝ) : ℝ) : EReal) < φ i x} := by
    ext x
    simp [strictLocusM]
  rw [e]
  exact MeasurableSet.iInter fun i =>
    measurableSet_lt measurable_const (upperSemicontinuous_of_manifoldPSH (hφ i)).measurable

end Truncation

/-! ### The source well-definedness condition on the manifold -/

section WellDefined

variable [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] [MeasurableSpace M] [BorelSpace M] [T2Space M]
  {p q : ℕ} (hqp : q + p = n)

/-- **The source well-definedness condition `eq:welldefinepluri`** (`def:npp:L69`) on the
manifold `M`, with the source's quantifiers: for every connected open `U ⊆ M`, every smooth
semipositive `(1,1)`-form `θ` on `U` and every compact `K ⊆ U`,
`sup_k ∫_{K ∩ O_k} (⋀ⱼ dd^c (φⱼ ∨ (-k)))|_U ∧ θ^{n-p} < ∞`, the integral being taken for the
measure `((⋀ⱼ dd^c (φⱼ ∨ (-k)))|_U ∧ θ^{n-p})|_K` (`wedgeMeasureOn`). -/
def IsNonPluripolarWellDefinedOnOpens (φ : Fin p → M → EReal)
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i)) : Prop :=
  ∀ U : Opens M, IsConnected (U : Set M) → ∀ θ : SemipositiveFormOn n U,
    ∀ (K : Set M) (hK : IsCompact K), K ⊆ U →
      ⨆ k, wedgeMeasureOn (truncatedCurrent hqp φ hφ k) θ hK (strictLocusM φ k) < ⊤

variable {φ : Fin p → M → EReal} (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i))

omit [T2Space M] in
/-- The measure of a chart piece `W ∩ O_k` is bounded by the local quantity of
`eq:welldefinepluri` in coordinates. -/
theorem chartWedgeMeasure_truncated_le {U : Opens M} (θ : SemipositiveFormOn n U)
    (e : ComplexChart n M) (z₀ : ComplexModel n) (r : ℝ) (k : ℕ) :
    chartWedgeMeasure (truncatedCurrent hqp φ hφ k) θ e
        ((e.val.source ∩ e.val ⁻¹' Metric.ball z₀ (r / 2)) ∩ strictLocusM φ k) ≤
      wedgePowerMeasure ((truncatedCurrent hqp φ hφ k).inChart e) (θ.coeff e)
        (Metric.closedBall z₀ (r / 2) ∩
          BedfordTaylorTopDegree.strictLocus (chartTarget e) (fun i z => φ i (e.val.symm z)) k)
            := by
  have hWm : MeasurableSet ((e.val.source ∩ e.val ⁻¹' Metric.ball z₀ (r / 2)) ∩ strictLocusM φ k)
    :=
    ((e.val.continuousOn.isOpen_inter_preimage e.val.open_source
      Metric.isOpen_ball).measurableSet).inter (measurableSet_strictLocusM hφ k)
  rw [chartWedgeMeasure_apply _ θ e hWm]
  refine measure_mono fun w hw => ?_
  obtain ⟨⟨⟨-, hw1⟩, hw2⟩, hwD⟩ := hw
  have hwt : w ∈ e.val.target := hwD.1
  rw [chartInv_of_mem hwt] at hw1 hw2
  rw [mem_preimage, e.val.right_inv hwt] at hw1
  exact ⟨Metric.ball_subset_closedBall hw1, hwt, fun i => hw2 i⟩

/-- **The chart condition implies the source condition**: if `eq:welldefinepluri` holds in
coordinates in every chart (`IsNonPluripolarWellDefined`), it holds for all connected open
`U ⊆ M`, forms on `U` and compact `K ⊆ U`. -/
theorem isNonPluripolarWellDefinedOnOpens_of_chart (hW : IsNonPluripolarWellDefined hqp φ) :
    IsNonPluripolarWellDefinedOnOpens hqp φ hφ := by
  intro U _ θ K hK hKU
  have hloc : ∀ x ∈ K, ∃ r > (0 : ℝ),
      Metric.ball ((complexChartAt (n := n) x).val x) r ⊆
        (chartDomain (complexChartAt (n := n) x) U : Set (ComplexModel n)) := by
    intro x hx
    have hmem : (complexChartAt (n := n) x).val x ∈ chartDomain (complexChartAt x) U :=
      ⟨(complexChartAt x).val.map_source (mem_complexChartAt_source x), by
        rw [mem_preimage, (complexChartAt x).val.left_inv (mem_complexChartAt_source x)]
        exact hKU hx⟩
    exact Metric.isOpen_iff.mp (chartDomain _ U).isOpen _ hmem
  choose! r hr hball using hloc
  set W : M → Set M := fun x => (complexChartAt (n := n) x).val.source ∩
    (complexChartAt (n := n) x).val ⁻¹' Metric.ball ((complexChartAt (n := n) x).val x) (r x / 2)
  have hWn : ∀ x ∈ K, W x ∈ 𝓝 x := fun x hx =>
    ((complexChartAt (n := n) x).val.continuousOn.isOpen_inter_preimage
      (complexChartAt (n := n) x).val.open_source Metric.isOpen_ball).mem_nhds
      ⟨mem_complexChartAt_source x, Metric.mem_ball_self (half_pos (hr x hx))⟩
  obtain ⟨t, htK, hKt⟩ := hK.elim_nhds_subcover W hWn
  -- the local bounds
  have hbound : ∀ x ∈ t, ⨆ k, wedgePowerMeasure
      ((truncatedCurrent hqp φ hφ k).inChart (complexChartAt (n := n) x))
      (θ.coeff (complexChartAt x))
      (Metric.closedBall ((complexChartAt (n := n) x).val x) (r x / 2) ∩
        BedfordTaylorTopDegree.strictLocus (chartTarget (complexChartAt (n := n) x))
          (fun i z => φ i ((complexChartAt (n := n) x).val.symm z)) k) < ⊤ := by
    intro x hx
    have hxK := htK x hx
    set e := complexChartAt (n := n) x
    have hVe : (⟨Metric.ball (e.val x) (r x), Metric.isOpen_ball⟩ : Opens (ComplexModel n)) ≤
        chartTarget e := fun z hz => (chartDomain_le _ U) (hball x hxK hz)
    have h := hW e ⟨Metric.ball _ (r x), Metric.isOpen_ball⟩ hVe
      ((convex_ball _ _).isConnected (Metric.nonempty_ball.mpr (hr x hxK)))
      (θ.coeff _) ((θ.smooth _).mono (hball x hxK))
      (fun z hz => θ.semipositive _ z (hball x hxK hz)) _ (isCompact_closedBall _ _)
      (Metric.closedBall_subset_ball (half_lt_self (hr x hxK)))
    refine lt_of_le_of_lt (le_of_eq (iSup_congr fun k => ?_)) h
    rw [wedgePowerMeasure_restrict (T := truncatedBT hqp (chartTarget e)
        (fun i z => φ i (e.val.symm z)) k) ((truncatedCurrent hqp φ hφ k).isPositive e) hVe,
      Measure.restrict_apply (Metric.isClosed_closedBall.measurableSet.inter
        (BedfordTaylorTopDegree.measurableSet_strictLocus (chartPlurisubharmonicOn hφ e) k))]
    congr 1
    refine (inter_eq_left.mpr ?_).symm
    exact inter_subset_left.trans (Metric.closedBall_subset_ball (half_lt_self (hr x hxK)))
  refine lt_of_le_of_lt (iSup_le fun k => ?_) (ENNReal.sum_lt_top.mpr hbound)
  set μ := wedgeMeasureOn (truncatedCurrent hqp φ hφ k) θ hK
  have hμK : μ.restrict K = μ := Measure.restrict_eq_self_of_ae_mem
    ((measure_eq_zero_iff_ae_notMem.mp (wedgeMeasureOn_compl _ θ hK)).mono fun x hx => by
      simpa using hx)
  calc μ (strictLocusM φ k) = μ (strictLocusM φ k ∩ K) := by
        conv_lhs => rw [← hμK]
        rw [Measure.restrict_apply' hK.isClosed.measurableSet]
    _ ≤ μ (⋃ x ∈ t, W x ∩ strictLocusM φ k) := by
        refine measure_mono fun y hy => ?_
        obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (hKt hy.2)
        exact mem_iUnion₂.mpr ⟨x, hx, hyx, hy.1⟩
    _ ≤ ∑ x ∈ t, μ (W x ∩ strictLocusM φ k) := measure_biUnion_finset_le _ _
    _ ≤ _ := Finset.sum_le_sum fun x hx => by
        refine (wedgeMeasureOn_le_chart _ θ hK (complexChartAt x)
          (inter_subset_left.trans inter_subset_left)).trans ?_
        exact (chartWedgeMeasure_truncated_le hqp hφ θ _ _ (r x) k).trans
          (le_iSup (fun k => wedgePowerMeasure
            ((truncatedCurrent hqp φ hφ k).inChart (complexChartAt (n := n) x))
            (θ.coeff (complexChartAt x))
            (Metric.closedBall ((complexChartAt (n := n) x).val x) (r x / 2) ∩
              BedfordTaylorTopDegree.strictLocus (chartTarget (complexChartAt (n := n) x))
                (fun i z => φ i ((complexChartAt (n := n) x).val.symm z)) k)) k)

end WellDefined

/-! ### Forms given in one chart -/

section OfChart

variable [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M]

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] in
theorem mem_overlapSource_of_mem_chartDomain {e f : ComplexChart n M} {U : Opens M}
    (hUf : (U : Set M) ⊆ f.val.source) {z : ComplexModel n} (hz : z ∈ chartDomain e U) :
    z ∈ overlapSource e f := by
  change z ∈ (chartTransition e f).source
  simp only [chartTransition, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage]
  exact ⟨hz.1, hUf hz.2⟩

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] in
theorem chartTransition_mem_chartDomain {e f : ComplexChart n M} {U : Opens M}
    (hUf : (U : Set M) ⊆ f.val.source) {z : ComplexModel n} (hz : z ∈ chartDomain e U) :
    chartTransition e f z ∈ chartDomain f U := by
  have hzf : e.val.symm z ∈ f.val.source := hUf hz.2
  refine ⟨?_, ?_⟩
  · simpa [chartTransition] using f.val.map_source hzf
  · simp only [chartTransition, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      mem_preimage, f.val.left_inv hzf]
    exact hz.2

theorem contDiffOn_chartTransitionDerivative (e f : ComplexChart n M) :
    ContDiffOn ℝ ∞ (chartTransitionDerivative e f) (overlapSource e f) :=
  ((contDiffOn_chartTransition e f).restrict_scalars ℝ).fderiv_of_isOpen
    (overlapSource e f).isOpen (by simp)

theorem chartTransitionDerivative_eq (e f : ComplexChart n M) {z : ComplexModel n}
    (hz : z ∈ overlapSource e f) :
    chartTransitionDerivative e f z =
      (fderiv ℂ (chartTransition e f) z).restrictScalars ℝ :=
  fderiv_real_eq (chartTransition_isBiholomorphicPair e f) hz

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] in
/-- The derivative of `f ∘ f⁻¹` is the identity on the coordinate domain. -/
theorem chartTransitionDerivative_self (f : ComplexChart n M) {z : ComplexModel n}
    (hz : z ∈ f.val.target) :
    chartTransitionDerivative f f z = ContinuousLinearMap.id ℝ (ComplexModel n) := by
  have hev : (chartTransition f f : ComplexModel n → ComplexModel n) =ᶠ[𝓝 z] id :=
    Filter.eventually_of_mem (f.val.open_target.mem_nhds hz) fun w hw => by
      simp only [chartTransition, OpenPartialHomeomorph.coe_trans, Function.comp_apply, id,
        f.val.right_inv hw]
  rw [chartTransitionDerivative, hev.fderiv_eq, fderiv_id]

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] in
theorem chartTransition_self_apply (f : ComplexChart n M) {z : ComplexModel n}
    (hz : z ∈ f.val.target) : chartTransition f f z = z := by
  simp only [chartTransition, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    f.val.right_inv hz]

/-- The chain rule for coordinate changes: `D(f ∘ e⁻¹) = D(f ∘ g⁻¹) ∘ D(g ∘ e⁻¹)`. -/
theorem chartTransitionDerivative_comp (e g f : ComplexChart n M) {z : ComplexModel n}
    (hzg : z ∈ overlapSource e g) (hzf : z ∈ overlapSource e f) :
    chartTransitionDerivative e f z =
      (chartTransitionDerivative g f (chartTransition e g z)).comp
        (chartTransitionDerivative e g z) := by
  have hzg' : z ∈ (chartTransition e g).source := hzg
  have hzf' : z ∈ (chartTransition e f).source := hzf
  simp only [chartTransition, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage] at hzg' hzf'
  have hev : (chartTransition e f : ComplexModel n → ComplexModel n) =ᶠ[𝓝 z]
      (chartTransition g f) ∘ (chartTransition e g) :=
    Filter.eventually_of_mem (((overlapSource e g).isOpen.inter (overlapSource e
      f).isOpen).mem_nhds
      ⟨hzg, hzf⟩) fun w hw => by
      have hw1 : w ∈ (chartTransition e g).source := hw.1
      simp only [chartTransition, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage] at hw1
      simp only [chartTransition, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
        g.val.left_inv hw1.2]
  have hgz : chartTransition e g z ∈ overlapSource g f := by
    change chartTransition e g z ∈ (chartTransition g f).source
    simp only [chartTransition, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage,
      OpenPartialHomeomorph.coe_trans, Function.comp_apply, g.val.left_inv hzg'.2]
    exact ⟨g.val.map_source hzg'.2, hzf'.2⟩
  have hd1 : DifferentiableAt ℝ (chartTransition e g) z :=
    (((contDiffOn_chartTransition e g).restrict_scalars ℝ).contDiffAt
      ((overlapSource e g).isOpen.mem_nhds hzg)).differentiableAt (by simp)
  have hd2 : DifferentiableAt ℝ (chartTransition g f) (chartTransition e g z) :=
    (((contDiffOn_chartTransition g f).restrict_scalars ℝ).contDiffAt
      ((overlapSource g f).isOpen.mem_nhds hgz)).differentiableAt (by simp)
  rw [chartTransitionDerivative, hev.fderiv_eq, fderiv_comp z hd2 hd1]
  rfl

/-- **A form on `U ⊆ f.source` given by its expression `β` in the chart `f`**: in another chart
`e` its expression is the pull-back `(f ∘ e⁻¹)^* β`. -/
def SemipositiveFormOn.ofChart (f : ComplexChart n M) {U : Opens M}
    (hUf : (U : Set M) ⊆ f.val.source) (β : ComplexModel n → RealForm n 2)
    (hβ : ContDiffOn ℝ ∞ β (chartDomain f U))
    (hβp : ∀ z ∈ chartDomain f U, IsSemipositiveOneOne (β z)) : SemipositiveFormOn n U where
  coeff e z := (β (chartTransition e f z)).compContinuousLinearMap (chartTransitionDerivative e f
    z)
  smooth e := by
    have hsub : (chartDomain e U : Set (ComplexModel n)) ⊆ overlapSource e f := fun z hz =>
      mem_overlapSource_of_mem_chartDomain hUf hz
    have hτ : ContDiffOn ℝ ∞ (chartTransition e f) (overlapSource e f) :=
      (contDiffOn_chartTransition e f).restrict_scalars ℝ
    have hβτ : ContDiffOn ℝ ∞ (fun z => β (chartTransition e f z)) (chartDomain e U) :=
      hβ.comp (hτ.mono hsub) fun z hz => chartTransition_mem_chartDomain hUf hz
    exact SmoothRealForm.contDiffOn_compContinuousLinearMap hβτ
      ((contDiffOn_chartTransitionDerivative e f).mono hsub)
  semipositive e z hz := by
    rw [chartTransitionDerivative_eq e f (mem_overlapSource_of_mem_chartDomain hUf hz)]
    exact (hβp _ (chartTransition_mem_chartDomain hUf hz)).comp _
      fun v => (fderiv ℂ (chartTransition e f) z).map_smul Complex.I v
  compatible e g z hz hzg := by
    have hzf := mem_overlapSource_of_mem_chartDomain (e := e) hUf hz
    have hzg' : z ∈ overlapSource e g := hzg
    have hτ : chartTransition g f (chartTransition e g z) = chartTransition e f z := by
      have h1 : z ∈ (chartTransition e g).source := hzg
      simp only [chartTransition, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage] at h1
      simp only [chartTransition, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
        g.val.left_inv h1.2]
    rw [hτ, chartTransitionDerivative_comp e g f hzg' hzf]
    rfl

theorem SemipositiveFormOn.ofChart_coeff_self (f : ComplexChart n M) {U : Opens M}
    (hUf : (U : Set M) ⊆ f.val.source) (β : ComplexModel n → RealForm n 2)
    (hβ : ContDiffOn ℝ ∞ β (chartDomain f U))
    (hβp : ∀ z ∈ chartDomain f U, IsSemipositiveOneOne (β z)) {z : ComplexModel n}
    (hz : z ∈ f.val.target) : (SemipositiveFormOn.ofChart f hUf β hβ hβp).coeff f z = β z := by
  change (β (chartTransition f f z)).compContinuousLinearMap (chartTransitionDerivative f f z) = _
  rw [chartTransition_self_apply f hz, chartTransitionDerivative_self f hz]
  rfl

end OfChart

/-! ### The source condition is equivalent to the chart condition -/

section Equivalence

variable [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] [MeasurableSpace M] [BorelSpace M] [T2Space M]
  {p q : ℕ} (hqp : q + p = n)

/-- `T ∧ α^q (S) = σ_T(S)` when `α` is the Euclidean Kähler form on `S`. -/
theorem wedgePowerMeasure_eq_traceMeasure_of_eqOn {U : Opens (ComplexModel n)}
    {T : LocalProductCurrent n U q} (hT : IsPositive T) {α : ComplexModel n → RealForm n 2}
    {S : Set (ComplexModel n)} (hS : MeasurableSet S) (hα : ∀ x ∈ S, α x = kahlerForm n) :
    wedgePowerMeasure T α S = hT.traceMeasure S := by
  rw [wedgePowerMeasure, dite_eq_left hT, withDensity_apply _ hS, ← setLIntegral_one]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae (densityForm_kahlerPower_ae hT)]
    with x hx h1
  rw [hα x hx, powerSpan_kahlerForm, h1, ENNReal.ofReal_one]

variable {φ : Fin p → M → EReal} (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i))

/-- **The source condition implies the chart condition on balls**: on a ball `V` of a coordinate
domain, the local mass condition holds (the form is the Euclidean Kähler form of the chart,
transported to the open set `f⁻¹(V)`). -/
theorem isWellDefinedOn_ball_of_opens (hG : IsNonPluripolarWellDefinedOnOpens hqp φ hφ)
    (f : ComplexChart n M) {z₀ : ComplexModel n} {r : ℝ} (hr : 0 < r)
    (hV : Metric.ball z₀ r ⊆ f.val.target) :
    NonPluripolarCurrent.IsWellDefinedOn hqp ⟨Metric.ball z₀ r, Metric.isOpen_ball⟩
      fun i z => φ i (f.val.symm z) := by
  set V : Opens (ComplexModel n) := ⟨Metric.ball z₀ r, Metric.isOpen_ball⟩
  have hVt : V ≤ chartTarget f := hV
  have hφf := chartPlurisubharmonicOn hφ f
  have hφV : ∀ i, PlurisubharmonicOn (fun z => φ i (f.val.symm z)) V :=
    fun i => (hφf i).mono hVt
  rw [isWellDefinedOn_iff hqp hφV, (isTruncationFamily hqp hφV).hasLocallyFiniteMass_iff]
  intro K' hK' hK'V
  -- the open set `f⁻¹(V)`, the form and the compact set on the manifold
  set U : Opens M := ⟨f.val.source ∩ f.val ⁻¹' V,
    f.val.continuousOn.isOpen_inter_preimage f.val.open_source V.isOpen⟩
  have hUf : (U : Set M) ⊆ f.val.source := inter_subset_left
  have hUconn : IsConnected (U : Set M) := by
    have h := ((convex_ball z₀ r).isConnected (Metric.nonempty_ball.mpr hr)).image f.val.symm
      (f.val.continuousOn_symm.mono hV)
    have e : f.val.symm '' Metric.ball z₀ r = (U : Set M) := by
      rw [← inter_eq_right.mpr hV, f.val.symm_image_target_inter_eq]
      ext x
      change x ∈ f.val.source ∩ f.val ⁻¹' (f.val.target ∩ Metric.ball z₀ r) ↔
        x ∈ f.val.source ∩ f.val ⁻¹' Metric.ball z₀ r
      simp only [mem_inter_iff, mem_preimage]
      exact ⟨fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, f.val.map_source h1, h2⟩⟩
    rwa [e] at h
  set θ := SemipositiveFormOn.ofChart f hUf (fun _ => kahlerForm n) contDiffOn_const
    (fun _ _ => isSemipositiveOneOne_kahlerForm)
  set K := f.val.symm '' K'
  have hK : IsCompact K := hK'.image_of_continuousOn
    (f.val.continuousOn_symm.mono (hK'V.trans hV))
  have hKU : K ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    have hzt := hV (hK'V hz)
    exact ⟨f.val.map_target hzt, by rw [mem_preimage, f.val.right_inv hzt]; exact hK'V hz⟩
  have hKf : K ⊆ f.val.source := hKU.trans hUf
  have h := hG U hUconn θ K hK hKU
  refine lt_of_le_of_lt (iSup_mono fun k => ?_) h
  set T := truncatedCurrent hqp φ hφ k
  have hOk := measurableSet_strictLocusM hφ k (M := M)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hOK : MeasurableSet (strictLocusM φ k ∩ K) := hOk.inter hKm
  -- the value of the glued measure on the chart piece
  have e1 : wedgeMeasureOn T θ hK (strictLocusM φ k ∩ f.val.source) =
      chartWedgeMeasure T θ f (strictLocusM φ k ∩ K) := by
    have h2 := congrArg (fun μ : Measure M => μ (strictLocusM φ k))
      (wedgeMeasureOn_restrict_source T θ hK f)
    rw [Measure.restrict_apply' f.val.open_source.measurableSet,
      Measure.restrict_apply hOk] at h2
    rw [h2, inter_eq_left.mpr hKf]
  have hO' := BedfordTaylorTopDegree.measurableSet_strictLocus hφf k
  have hK'm : MeasurableSet K' := hK'.isClosed.measurableSet
  calc ((isTruncationFamily hqp hφV).isPositive k).traceMeasure
          (K' ∩ BedfordTaylorTopDegree.strictLocus V (fun i z => φ i (f.val.symm z)) k)
        ≤ (T.isPositive f).traceMeasure
          (K' ∩ BedfordTaylorTopDegree.strictLocus (chartTarget f)
            (fun i z => φ i (f.val.symm z)) k) := by
          have hB : truncatedBT hqp V (fun i z => φ i (f.val.symm z)) k =
              restrict hVt (T.inChart f) := truncatedBT_restrict hqp hφf hVt k
          rw [traceMeasure_congr _ (isPositive_restrict (T.isPositive f) hVt) hB,
            traceMeasure_restrict, Measure.restrict_apply (hK'm.inter
              (BedfordTaylorTopDegree.measurableSet_strictLocus hφV k)),
            NonPluripolarCurrent.strictLocus_restrict hVt k]
          refine measure_mono fun z hz => ?_
          exact ⟨hz.1.1, hz.1.2.1⟩
      _ = wedgePowerMeasure (T.inChart f) (θ.coeff f)
          (K' ∩ BedfordTaylorTopDegree.strictLocus (chartTarget f)
            (fun i z => φ i (f.val.symm z)) k) :=
          (wedgePowerMeasure_eq_traceMeasure_of_eqOn (T.isPositive f) (hK'm.inter hO')
            fun z hz => SemipositiveFormOn.ofChart_coeff_self f hUf _ _ _ (hV (hK'V hz.1))).symm
      _ ≤ chartWedgeMeasure T θ f (strictLocusM φ k ∩ K) := by
          rw [chartWedgeMeasure_apply T θ f hOK]
          refine measure_mono fun z hz => ?_
          have hzt := hV (hK'V hz.1)
          refine ⟨?_, hzt, ?_⟩
          · rw [mem_preimage, chartInv_of_mem hzt]
            exact ⟨fun i => hz.2.2 i, z, hz.1, rfl⟩
          · refine ⟨f.val.map_target hzt, ?_⟩
            rw [mem_preimage, f.val.right_inv hzt]
            exact hK'V hz.1
      _ = wedgeMeasureOn T θ hK (strictLocusM φ k ∩ f.val.source) := e1.symm
      _ ≤ wedgeMeasureOn T θ hK (strictLocusM φ k) := measure_mono inter_subset_left

/-- **`def:npp:L69`: the source well-definedness condition `eq:welldefinepluri`, with its
quantification over all connected open subsets of the manifold, is equivalent to the chart
condition `IsNonPluripolarWellDefined`.** -/
theorem isNonPluripolarWellDefinedOnOpens_iff :
    IsNonPluripolarWellDefinedOnOpens hqp φ hφ ↔ IsNonPluripolarWellDefined hqp φ := by
  refine ⟨fun hG f => ?_, isNonPluripolarWellDefinedOnOpens_of_chart hqp hφ⟩
  have hball : ∀ z : chartTarget f, ∃ r > (0 : ℝ), Metric.ball (z : ComplexModel n) r ⊆
      f.val.target := fun z => Metric.isOpen_iff.mp f.val.open_target z z.2
  choose r hr hball using hball
  refine isWellDefinedOn_of_cover hqp (chartPlurisubharmonicOn hφ f)
    (fun z : chartTarget f => ⟨Metric.ball (z : ComplexModel n) (r z), Metric.isOpen_ball⟩)
    (fun z => hball z)
    (fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, Metric.mem_ball_self (hr ⟨z, hz⟩)⟩)
    fun z => isWellDefinedOn_ball_of_opens hqp hφ hG f (hr z) (hball z)

/-- **The non-pluripolar product under the source condition** (`def:npp:L69`): when
`eq:welldefinepluri` holds (for all connected open `U ⊆ M`, forms on `U` and compact `K ⊆ U`),
the positive current of bidimension `(q,q)` on `M` whose coordinate expressions are the local
products (`SGPT.NPP.nonPluripolarProduct`). -/
def nonPluripolarProductOfOpens (hW : IsNonPluripolarWellDefinedOnOpens hqp φ hφ) :
    PositiveCurrent n M q :=
  nonPluripolarProduct hqp φ hφ ((isNonPluripolarWellDefinedOnOpens_iff hqp hφ).mp hW)

/-- **The defining identity `eq:npp`** in every chart:
`1_{O_k} ⟨⋀ dd^c φⱼ⟩ = 1_{O_k} ⋀ⱼ dd^c (φⱼ ∨ (-k))`, the right-hand side being the
coordinate expression of the truncated product `truncatedCurrent`. -/
theorem nonPluripolarProductOfOpens_strictLocus (hW : IsNonPluripolarWellDefinedOnOpens hqp φ hφ)
    (e : ComplexChart n M) (k : ℕ) :
    mulBorel ((nonPluripolarProductOfOpens hqp hφ hW).inChart e)
        ((BedfordTaylorTopDegree.strictLocus (chartTarget e)
          (fun i z => φ i (e.val.symm z)) k).indicator fun _ => (1 : ℝ)) =
      mulBorel ((truncatedCurrent hqp φ hφ k).inChart e)
        ((BedfordTaylorTopDegree.strictLocus (chartTarget e)
          (fun i z => φ i (e.val.symm z)) k).indicator fun _ => (1 : ℝ)) :=
  nonPluripolarProduct_inChart_strictLocus hqp hφ _ e k

/-- **Extension by zero** in every chart: the product vanishes off `⋃ₖ O_k`. -/
theorem nonPluripolarProductOfOpens_compl (hW : IsNonPluripolarWellDefinedOnOpens hqp φ hφ)
    (e : ComplexChart n M) :
    mulBorel ((nonPluripolarProductOfOpens hqp hφ hW).inChart e)
        ((⋃ k, BedfordTaylorTopDegree.strictLocus (chartTarget e)
          (fun i z => φ i (e.val.symm z)) k)ᶜ.indicator fun _ => (1 : ℝ)) = 0 :=
  nonPluripolarProduct_inChart_compl hqp hφ _ e

end Equivalence

end SGPT.NPP
