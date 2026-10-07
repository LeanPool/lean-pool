/-
Copyright (c) 2026 FormalizingGMT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalizingGMT contributors
-/
module


public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.MeasureTheory.Integral.Regular
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import LeanPool.FormalizingGMT.RadonMeasures.Basic

/-!
# Weak convergence of Radon measures

This file defines the three conditions for weak convergence of Radon measures appearing in
Evans--Gariepy, Revised Edition, Theorem 1.40, and proves their equivalence for Radon measures
on Euclidean space.

Radon measures are modelled here by Borel measures (`MeasurableSpace X` together with
`BorelSpace X`) that are regular in Mathlib's sense, i.e. satisfy
`MeasureTheory.Measure.Regular`: they are finite on compact sets, outer regular by open sets and
inner regular by compact sets on open sets.
-/

@[expose] public section

open scoped CompactlySupported ENNReal NNReal
open Filter Function Set Topology

noncomputable section

namespace MeasureTheory

/-- A sequence of Radon measures `μ` converges weakly to a Radon measure `ν` if integrals against
every real-valued compactly supported continuous function converge.

This is called weak convergence by Evans--Gariepy and is also commonly called vague
convergence. -/
def Measure.WeaklyConverges
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : ℕ → Measure X) (ν : Measure X) : Prop :=
  ∀ f : C_c(X, ℝ),
    Tendsto (fun k ↦ ∫ x, f x ∂μ k) atTop (𝓝 (∫ x, f x ∂ν))

/-- Evans--Gariepy, Revised Edition, Theorem 1.40(ii): the compact-set upper bound and
open-set lower bound characterizing weak convergence.

Both clauses together constitute condition (ii); neither clause separately is equivalent to weak
convergence. -/
def Measure.WeaklyConvergesByCompactOpenBounds
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : ℕ → Measure X) (ν : Measure X) : Prop :=
  (∀ K : Set X, IsCompact K →
      atTop.limsup (fun k ↦ μ k K) ≤ ν K) ∧
    ∀ U : Set X, IsOpen U →
      ν U ≤ atTop.liminf (fun k ↦ μ k U)

/-- Evans--Gariepy, Revised Edition, Theorem 1.40(iii): convergence on every bounded Borel
continuity set of the limit measure.

Under `BorelSpace X`, `MeasurableSet B` says that `B` is Borel. For Euclidean space,
`Bornology.IsBounded B` is the usual metric boundedness condition. -/
def Measure.WeaklyConvergesOnBoundedContinuitySets
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [Bornology X]
    (μ : ℕ → Measure X) (ν : Measure X) : Prop :=
  ∀ B : Set X, Bornology.IsBounded B → MeasurableSet B →
    ν (frontier B) = 0 →
      Tendsto (fun k ↦ μ k B) atTop (𝓝 (ν B))

/-! ## Equivalence on Euclidean space -/

private theorem finiteMeasure_tendsto_of_open_liminf_of_mass_tendsto
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [Nonempty X] (μs : ℕ → FiniteMeasure X) (μ : FiniteMeasure X)
    (hopen : ∀ G : Set X, IsOpen G →
      (μ : Measure X) G ≤ atTop.liminf (fun k ↦ (μs k : Measure X) G))
    (hmass : Tendsto (fun k ↦ (μs k).mass) atTop (𝓝 μ.mass)) :
    Tendsto μs atTop (𝓝 μ) := by
  by_cases hμzero : μ = 0
  · subst μ
    apply FiniteMeasure.tendsto_zero_of_tendsto_zero_mass
    simpa using hmass
  have hmass_ne : μ.mass ≠ 0 := μ.mass_nonzero_iff.mpr hμzero
  have heventually_nonzero : ∀ᶠ k in atTop, μs k ≠ 0 := by
    simp_rw [← FiniteMeasure.mass_nonzero_iff]
    exact hmass (isOpen_compl_singleton.mem_nhds hmass_ne)
  have hmass_ennreal :
      Tendsto (fun k ↦ ((μs k).mass : ℝ≥0∞)) atTop (𝓝 (μ.mass : ℝ≥0∞)) :=
    ENNReal.continuous_coe.continuousAt.tendsto.comp hmass
  have hmass_inv :
      Tendsto (fun k ↦ ((μs k).mass : ℝ≥0∞)⁻¹) atTop
        (𝓝 ((μ.mass : ℝ≥0∞)⁻¹)) :=
    tendsto_inv_iff.mpr hmass_ennreal
  apply (FiniteMeasure.tendsto_normalize_iff_tendsto hμzero).mp
  refine ⟨tendsto_of_forall_isOpen_le_liminf' (μ := μ.normalize)
    (μs := fun k ↦ (μs k).normalize) ?_, hmass⟩
  intro G hG
  have hnormalized_eventually :
      ∀ᶠ k in atTop,
        ((μs k).normalize : Measure X) G =
          ((μs k).mass : ℝ≥0∞)⁻¹ * (μs k : Measure X) G := by
    filter_upwards [heventually_nonzero] with k hk
    rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero (μ := μs k) hk]
    simp only [Measure.coe_smul, Pi.smul_apply, Measure.nnreal_smul_coe_apply,
      ENNReal.coe_inv ((μs k).mass_nonzero_iff.mpr hk)]
  calc
    (μ.normalize : Measure X) G =
        (μ.mass : ℝ≥0∞)⁻¹ * (μ : Measure X) G := by
      rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero (μ := μ) hμzero]
      simp only [Measure.coe_smul, Pi.smul_apply, Measure.nnreal_smul_coe_apply,
        ENNReal.coe_inv hmass_ne]
    _ ≤ atTop.liminf (fun k ↦ ((μs k).mass : ℝ≥0∞)⁻¹) *
        atTop.liminf (fun k ↦ (μs k : Measure X) G) := by
      rw [hmass_inv.liminf_eq]
      exact mul_le_mul_right (hopen G hG) _
    _ ≤ atTop.liminf (fun k ↦
        ((μs k).mass : ℝ≥0∞)⁻¹ * (μs k : Measure X) G) :=
      ENNReal.le_liminf_mul
    _ = atTop.liminf (fun k ↦ ((μs k).normalize : Measure X) G) :=
      (liminf_congr hnormalized_eventually).symm

private theorem weaklyConverges_imp_compactOpenBounds
    {n : ℕ} (μ : ℕ → Measure (EuclideanSpace ℝ (Fin n)))
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hμ : ∀ k, (μ k).Regular) (hν : ν.Regular)
    (h : Measure.WeaklyConverges μ ν) :
    Measure.WeaklyConvergesByCompactOpenBounds μ ν := by
  let _ : ν.Regular := hν
  constructor
  · intro K hK
    rw [hK.measure_eq_biInf_integral_hasCompactSupport ν]
    simp only [le_iInf_iff]
    intro f hf_cont hf_compact hf_one hf_nonneg
    let fc : C_c(EuclideanSpace ℝ (Fin n), ℝ) :=
      ⟨⟨f, hf_cont⟩, hf_compact⟩
    have htendsto :
        Tendsto (fun k ↦ ENNReal.ofReal (∫ x, f x ∂μ k)) atTop
          (𝓝 (ENNReal.ofReal (∫ x, f x ∂ν))) := by
      apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      have hfc : (fun x => fc x) = f := rfl
      simpa only [hfc] using h fc
    calc
      atTop.limsup (fun k ↦ μ k K) ≤
          atTop.limsup (fun k ↦ ENNReal.ofReal (∫ x, f x ∂μ k)) := by
        apply limsup_le_limsup _ (by isBoundedDefault) (by isBoundedDefault)
        filter_upwards [] with k
        let _ : (μ k).Regular := hμ k
        exact (hf_cont.integrable_of_hasCompactSupport hf_compact).measure_le_integral
          (.of_forall hf_nonneg) fun x hx ↦ (hf_one hx).ge
      _ = ENNReal.ofReal (∫ x, f x ∂ν) := htendsto.limsup_eq
  · intro U hU
    rw [hU.measure_eq_iSup_isCompact ν]
    simp only [iSup_le_iff]
    intro K hKU hK
    obtain ⟨f, hf_one, hf_compact, hf_support, hf_range⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
    let fc : C_c(EuclideanSpace ℝ (Fin n), ℝ) := ⟨f, hf_compact⟩
    have hf_zero : Set.EqOn f 0 Uᶜ := by
      intro x hx
      by_contra hfx
      exact hx (hf_support (subset_tsupport f hfx))
    have htendsto :
        Tendsto (fun k ↦ ENNReal.ofReal (∫ x, f x ∂μ k)) atTop
          (𝓝 (ENNReal.ofReal (∫ x, f x ∂ν))) := by
      apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      have hfc : (fun x => fc x) = f := rfl
      simpa only [hfc] using h fc
    calc
      ν K ≤ ENNReal.ofReal (∫ x, f x ∂ν) := by
        exact f.continuous.integrable_of_hasCompactSupport hf_compact |>.measure_le_integral
          (.of_forall fun x ↦ (hf_range x).1) fun x hx ↦ (hf_one hx).ge
      _ = atTop.liminf (fun k ↦ ENNReal.ofReal (∫ x, f x ∂μ k)) :=
        htendsto.liminf_eq.symm
      _ ≤ atTop.liminf (fun k ↦ μ k U) := by
        apply liminf_le_liminf _ (by isBoundedDefault) (by isBoundedDefault)
        filter_upwards [] with k
        exact integral_le_measure (fun x _ ↦ (hf_range x).2)
          (fun x hx ↦ (hf_zero hx).le)

private theorem compactOpenBounds_imp_boundedContinuitySets
    {n : ℕ} (μ : ℕ → Measure (EuclideanSpace ℝ (Fin n)))
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (h : Measure.WeaklyConvergesByCompactOpenBounds μ ν) :
    Measure.WeaklyConvergesOnBoundedContinuitySets μ ν := by
  intro B hB_bounded hB_meas hB_frontier
  apply tendsto_measure_of_le_liminf_measure_of_limsup_measure_le
      (μ := ν) (μs := μ) interior_subset subset_closure
  · simpa only [frontier] using hB_frontier
  · exact h.2 (interior B) isOpen_interior
  · exact h.1 (closure B) hB_bounded.isCompact_closure

private lemma exists_bounded_open_null_frontier_between
    {n : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin n))) (hν : ν.Regular)
    {K U : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ B : Set (EuclideanSpace ℝ (Fin n)),
      K ⊆ B ∧ B ⊆ U ∧ IsOpen B ∧ Bornology.IsBounded B ∧ ν (frontier B) = 0 := by
  let _ : ν.Regular := hν
  let _ : SFinite ν := inferInstance
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨r, hr, hnull⟩ := exists_null_frontier_thickening ν K hδ
  refine ⟨Metric.thickening r K, Metric.self_subset_thickening hr.1 K,
    (Metric.thickening_subset_cthickening_of_le hr.2.le K).trans hδU,
    Metric.isOpen_thickening, hK.isBounded.thickening, hnull⟩

private theorem boundedContinuitySets_imp_compactOpenBounds
    {n : ℕ} (μ : ℕ → Measure (EuclideanSpace ℝ (Fin n)))
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (hν : ν.Regular)
    (h : Measure.WeaklyConvergesOnBoundedContinuitySets μ ν) :
    Measure.WeaklyConvergesByCompactOpenBounds μ ν := by
  let _ : ν.Regular := hν
  constructor
  · intro K hK
    rw [K.measure_eq_iInf_isOpen ν]
    simp only [le_iInf_iff]
    intro U hKU hU
    obtain ⟨B, hKB, hBU, hB_open, hB_bounded, hB_frontier⟩ :=
      exists_bounded_open_null_frontier_between ν hν hK hU hKU
    have htendsto := h B hB_bounded hB_open.measurableSet hB_frontier
    calc
      atTop.limsup (fun k ↦ μ k K) ≤ atTop.limsup (fun k ↦ μ k B) := by
        apply limsup_le_limsup _ (by isBoundedDefault) (by isBoundedDefault)
        exact .of_forall fun k ↦ measure_mono hKB
      _ = ν B := htendsto.limsup_eq
      _ ≤ ν U := measure_mono hBU
  · intro U hU
    rw [hU.measure_eq_iSup_isCompact ν]
    simp only [iSup_le_iff]
    intro K hKU hK
    obtain ⟨B, hKB, hBU, hB_open, hB_bounded, hB_frontier⟩ :=
      exists_bounded_open_null_frontier_between ν hν hK hU hKU
    have htendsto := h B hB_bounded hB_open.measurableSet hB_frontier
    calc
      ν K ≤ ν B := measure_mono hKB
      _ = atTop.liminf (fun k ↦ μ k B) := htendsto.liminf_eq.symm
      _ ≤ atTop.liminf (fun k ↦ μ k U) := by
        apply liminf_le_liminf _ (by isBoundedDefault) (by isBoundedDefault)
        exact .of_forall fun k ↦ measure_mono hBU

private theorem compactOpenBounds_imp_weaklyConverges
    {n : ℕ} (μ : ℕ → Measure (EuclideanSpace ℝ (Fin n)))
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hμ : ∀ k, (μ k).Regular) (hν : ν.Regular)
    (h : Measure.WeaklyConvergesByCompactOpenBounds μ ν) :
    Measure.WeaklyConverges μ ν := by
  let _ : ν.Regular := hν
  intro f
  obtain ⟨O, hfO, -, hO_open, hO_bounded, hO_frontier⟩ :=
    exists_bounded_open_null_frontier_between ν hν f.hasCompactSupport isOpen_univ
      (subset_univ _)
  have hO_meas : MeasurableSet O := hO_open.measurableSet
  have hμO_lt_top (k : ℕ) : μ k O < ∞ := by
    let _ : (μ k).Regular := hμ k
    exact hO_bounded.measure_lt_top
  have hνO_lt_top : ν O < ∞ := hO_bounded.measure_lt_top
  let μO : ℕ → FiniteMeasure (EuclideanSpace ℝ (Fin n)) := fun k ↦
    ⟨(μ k).restrict O, isFiniteMeasure_restrict.mpr (hμO_lt_top k).ne⟩
  let νO : FiniteMeasure (EuclideanSpace ℝ (Fin n)) :=
    ⟨ν.restrict O, isFiniteMeasure_restrict.mpr hνO_lt_top.ne⟩
  have hopen : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G →
      (νO : Measure (EuclideanSpace ℝ (Fin n))) G ≤
        atTop.liminf
          (fun k ↦ (μO k : Measure (EuclideanSpace ℝ (Fin n))) G) := by
    intro G hG
    have hGO_open : IsOpen (G ∩ O) := hG.inter hO_open
    change ν.restrict O G ≤ atTop.liminf (fun k ↦ (μ k).restrict O G)
    simp_rw [Measure.restrict_apply hG.measurableSet]
    exact h.2 (G ∩ O) hGO_open
  have hO_tendsto : Tendsto (fun k ↦ μ k O) atTop (𝓝 (ν O)) :=
    compactOpenBounds_imp_boundedContinuitySets μ ν h O hO_bounded hO_meas hO_frontier
  have hmass : Tendsto (fun k ↦ (μO k).mass) atTop (𝓝 νO.mass) := by
    have hO_mass : Tendsto (fun k ↦ ((μO k).mass : ℝ≥0∞)) atTop
        (𝓝 (νO.mass : ℝ≥0∞)) := by
      simp_rw [FiniteMeasure.ennreal_mass]
      simpa only [μO, νO, FiniteMeasure.toMeasure_mk,
        Measure.restrict_apply_univ] using hO_tendsto
    exact ENNReal.tendsto_coe.mp hO_mass
  have hfinite : Tendsto μO atTop (𝓝 νO) :=
    finiteMeasure_tendsto_of_open_liminf_of_mass_tendsto μO νO hopen hmass
  have hintegral :=
    FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hfinite
      f.toBoundedContinuousFunction
  have hf_zero : ∀ x, x ∉ O → f x = 0 :=
    fun x hx ↦ image_eq_zero_of_notMem_tsupport fun hxf ↦ hx (hfO hxf)
  have hrestrict (m : Measure (EuclideanSpace ℝ (Fin n))) :
      ∫ x, f.toBoundedContinuousFunction x ∂m.restrict O =
        ∫ x, f.toBoundedContinuousFunction x ∂m :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hf_zero
  have hintegral' :
      Tendsto (fun k ↦ ∫ x, f.toBoundedContinuousFunction x ∂μ k) atTop
        (𝓝 (∫ x, f.toBoundedContinuousFunction x ∂ν)) := by
    simpa only [μO, νO, FiniteMeasure.toMeasure_mk, hrestrict] using hintegral
  have hcoe : (fun x => f.toBoundedContinuousFunction x) = f := rfl
  simpa only [hcoe] using hintegral'

/-- Evans--Gariepy, Revised Edition, Theorem 1.40, equivalence of conditions (i) and (ii)
for Radon measures on Euclidean space. -/
theorem Measure.weaklyConverges_iff_compactOpenBounds
    {n : ℕ} (μ : ℕ → Measure (EuclideanSpace ℝ (Fin n)))
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hμ : ∀ k, (μ k).Regular) (hν : ν.Regular) :
    Measure.WeaklyConverges μ ν ↔
      Measure.WeaklyConvergesByCompactOpenBounds μ ν :=
  ⟨weaklyConverges_imp_compactOpenBounds μ ν hμ hν,
    compactOpenBounds_imp_weaklyConverges μ ν hμ hν⟩

/-- Evans--Gariepy, Revised Edition, Theorem 1.40, equivalence of conditions (ii) and (iii)
for Radon measures on Euclidean space. -/
theorem Measure.weaklyConvergesByCompactOpenBounds_iff_boundedContinuitySets
    {n : ℕ} (μ : ℕ → Measure (EuclideanSpace ℝ (Fin n)))
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (hν : ν.Regular) :
    Measure.WeaklyConvergesByCompactOpenBounds μ ν ↔
      Measure.WeaklyConvergesOnBoundedContinuitySets μ ν :=
  ⟨compactOpenBounds_imp_boundedContinuitySets μ ν,
    boundedContinuitySets_imp_compactOpenBounds μ ν hν⟩

/-- Evans--Gariepy, Revised Edition, Theorem 1.40, equivalence of conditions (i) and (iii)
for Radon measures on Euclidean space. -/
theorem Measure.weaklyConverges_iff_boundedContinuitySets
    {n : ℕ} (μ : ℕ → Measure (EuclideanSpace ℝ (Fin n)))
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hμ : ∀ k, (μ k).Regular) (hν : ν.Regular) :
    Measure.WeaklyConverges μ ν ↔
      Measure.WeaklyConvergesOnBoundedContinuitySets μ ν := by
  constructor
  · exact compactOpenBounds_imp_boundedContinuitySets μ ν ∘
      weaklyConverges_imp_compactOpenBounds μ ν hμ hν
  · exact compactOpenBounds_imp_weaklyConverges μ ν hμ hν ∘
      boundedContinuitySets_imp_compactOpenBounds μ ν hν

end MeasureTheory
