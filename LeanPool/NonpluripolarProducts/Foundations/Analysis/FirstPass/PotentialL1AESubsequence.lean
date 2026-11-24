/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PotentialL1ConvergenceInMeasure

/-!
# Almost-everywhere subsequences from canonical L¹ convergence

Convergence of the canonical extended-real `L¹` difference first gives
convergence in measure of the `toReal` representatives.  The standard
subsequence theorem then supplies almost-everywhere convergence.  The lemmas
below package this passage for a single family, for two families with one
common subsequence, and in holomorphic charts.

When the limiting function and the sequence members are finite almost
everywhere, the final lemmas lift convergence of the real representatives back
to convergence in `EReal`.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

/-- Convergence of the real representatives lifts to `EReal` provided the
limit is finite and the approximating values are eventually finite. -/
theorem tendsto_eReal_of_tendsto_toReal
    {ι : Type*} {l : Filter ι} {u : ι → EReal} {v : EReal}
    (hreal : Tendsto (fun i => (u i).toReal) l (𝓝 v.toReal))
    (hv_top : v ≠ ⊤) (hv_bot : v ≠ ⊥)
    (hu : ∀ᶠ i in l, u i ≠ ⊤ ∧ u i ≠ ⊥) :
    Tendsto u l (𝓝 v) := by
  rw [← EReal.coe_toReal hv_top hv_bot]
  exact (EReal.tendsto_coe.mpr hreal).congr'
    (hu.mono fun i hi => EReal.coe_toReal hi.1 hi.2)

/-- An almost-everywhere real convergence statement lifts pointwise to
`EReal` if every member of the countable family and the limit are finite
almost everywhere. -/
theorem ae_tendsto_eReal_of_ae_tendsto_toReal
    {X ι : Type*} [MeasurableSpace X] [Countable ι]
    {μ : Measure X} {l : Filter ι} {u : ι → X → EReal} {v : X → EReal}
    (hreal : ∀ᵐ x ∂μ,
      Tendsto (fun i => (u i x).toReal) l (𝓝 (v x).toReal))
    (hu : ∀ i, ∀ᵐ x ∂μ, u i x ≠ ⊤ ∧ u i x ≠ ⊥)
    (hv : ∀ᵐ x ∂μ, v x ≠ ⊤ ∧ v x ≠ ⊥) :
    ∀ᵐ x ∂μ, Tendsto (fun i => u i x) l (𝓝 (v x)) := by
  have hu_all : ∀ᵐ x ∂μ, ∀ i, u i x ≠ ⊤ ∧ u i x ≠ ⊥ := ae_all_iff.mpr hu
  filter_upwards [hreal, hu_all, hv] with x hreal_x hu_x hv_x
  exact tendsto_eReal_of_tendsto_toReal hreal_x hv_x.1 hv_x.2
    (Eventually.of_forall hu_x)

/-- Canonical extended-real `L¹` convergence along `atTop` has a strictly
increasing subsequence whose real representatives converge almost everywhere. -/
theorem exists_strictMono_tendsto_ae_toReal_of_lintegral_canonicalERealAbsDiff
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u : ℕ → X → EReal} {v : X → EReal}
    (hu : ∀ i, AEMeasurable (u i) μ) (hv : AEMeasurable v μ)
    (hL1 : Tendsto
      (fun i => ∫⁻ x, canonicalERealAbsDiff (u i x) (v x) ∂μ)
      atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂μ,
      Tendsto (fun k => (u (ns k) x).toReal) atTop (𝓝 (v x).toReal) :=
  (tendstoInMeasure_toReal_of_lintegral_canonicalERealAbsDiff_tendsto_zero
    hu hv hL1).exists_seq_tendsto_ae

/-- Filter-indexed version of the almost-everywhere subsequence extraction. -/
theorem exists_seq_tendsto_ae_toReal_of_lintegral_canonicalERealAbsDiff
    {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    {u : ι → X → EReal} {v : X → EReal} {l : Filter ι}
    [NeBot l] [IsCountablyGenerated l]
    (hu : ∀ i, AEMeasurable (u i) μ) (hv : AEMeasurable v μ)
    (hL1 : Tendsto
      (fun i => ∫⁻ x, canonicalERealAbsDiff (u i x) (v x) ∂μ)
      l (𝓝 0)) :
    ∃ ns : ℕ → ι, Tendsto ns atTop l ∧ ∀ᵐ x ∂μ,
      Tendsto (fun k => (u (ns k) x).toReal) atTop (𝓝 (v x).toReal) :=
  (tendstoInMeasure_toReal_of_lintegral_canonicalERealAbsDiff_tendsto_zero
    hu hv hL1).exists_seq_tendsto_ae'

/-- Two sequences converging in measure admit one common subsequence along
which both sequences converge almost everywhere. -/
theorem exists_common_strictMono_tendsto_ae_of_tendstoInMeasure
    {X E F : Type*} [MeasurableSpace X]
    [PseudoMetricSpace E] [PseudoMetricSpace F] {μ : Measure X}
    {u : ℕ → X → E} {uLim : X → E}
    {v : ℕ → X → F} {vLim : X → F}
    (hu : TendstoInMeasure μ u atTop uLim)
    (hv : TendstoInMeasure μ v atTop vLim) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂μ,
      Tendsto (fun k => u (ns k) x) atTop (𝓝 (uLim x)) ∧
      Tendsto (fun k => v (ns k) x) atTop (𝓝 (vLim x)) := by
  obtain ⟨ns₁, hns₁, hu₁⟩ := hu.exists_seq_tendsto_ae
  obtain ⟨ns₂, hns₂, hv₂⟩ :=
    (hv.comp hns₁.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ns₁ ∘ ns₂, hns₁.comp hns₂, ?_⟩
  filter_upwards [hu₁, hv₂] with x hu_x hv_x
  exact ⟨by simpa [Function.comp_def] using hu_x.comp hns₂.tendsto_atTop,
    by simpa [Function.comp_def] using hv_x⟩

/-- Two canonical extended-real `L¹` limits admit a common subsequence with
almost-everywhere convergence of both `toReal` representatives. -/
theorem exists_common_strictMono_tendsto_ae_toReal_of_lintegral_canonicalERealAbsDiff
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u₀ u₁ : ℕ → X → EReal} {v₀ v₁ : X → EReal}
    (hu₀ : ∀ i, AEMeasurable (u₀ i) μ) (hv₀ : AEMeasurable v₀ μ)
    (hu₁ : ∀ i, AEMeasurable (u₁ i) μ) (hv₁ : AEMeasurable v₁ μ)
    (hL1₀ : Tendsto
      (fun i => ∫⁻ x, canonicalERealAbsDiff (u₀ i x) (v₀ x) ∂μ)
      atTop (𝓝 0))
    (hL1₁ : Tendsto
      (fun i => ∫⁻ x, canonicalERealAbsDiff (u₁ i x) (v₁ x) ∂μ)
      atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂μ,
      Tendsto (fun k => (u₀ (ns k) x).toReal) atTop (𝓝 (v₀ x).toReal) ∧
      Tendsto (fun k => (u₁ (ns k) x).toReal) atTop (𝓝 (v₁ x).toReal) := by
  exact exists_common_strictMono_tendsto_ae_of_tendstoInMeasure
    (u := fun i x => (u₀ i x).toReal) (uLim := fun x => (v₀ x).toReal)
    (v := fun i x => (u₁ i x).toReal) (vLim := fun x => (v₁ x).toReal)
    (tendstoInMeasure_toReal_of_lintegral_canonicalERealAbsDiff_tendsto_zero
      hu₀ hv₀ hL1₀)
    (tendstoInMeasure_toReal_of_lintegral_canonicalERealAbsDiff_tendsto_zero
      hu₁ hv₁ hL1₁)

/-- Under almost-everywhere finiteness, canonical extended-real `L¹`
convergence has a subsequence converging almost everywhere in `EReal` itself. -/
theorem exists_strictMono_tendsto_ae_eReal_of_lintegral_canonicalERealAbsDiff
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u : ℕ → X → EReal} {v : X → EReal}
    (hu_meas : ∀ i, AEMeasurable (u i) μ) (hv_meas : AEMeasurable v μ)
    (hu_finite : ∀ i, ∀ᵐ x ∂μ, u i x ≠ ⊤ ∧ u i x ≠ ⊥)
    (hv_finite : ∀ᵐ x ∂μ, v x ≠ ⊤ ∧ v x ≠ ⊥)
    (hL1 : Tendsto
      (fun i => ∫⁻ x, canonicalERealAbsDiff (u i x) (v x) ∂μ)
      atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂μ,
      Tendsto (fun k => u (ns k) x) atTop (𝓝 (v x)) := by
  obtain ⟨ns, hns, hreal⟩ :=
    exists_strictMono_tendsto_ae_toReal_of_lintegral_canonicalERealAbsDiff
      hu_meas hv_meas hL1
  refine ⟨ns, hns, ?_⟩
  exact ae_tendsto_eReal_of_ae_tendsto_toReal hreal
    (fun k => hu_finite (ns k)) hv_finite

/-- Under almost-everywhere finiteness, two canonical extended-real `L¹`
limits admit one common subsequence converging almost everywhere in `EReal` for
both families. -/
theorem exists_common_strictMono_tendsto_ae_eReal_of_lintegral_canonicalERealAbsDiff
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u₀ u₁ : ℕ → X → EReal} {v₀ v₁ : X → EReal}
    (hu₀_meas : ∀ i, AEMeasurable (u₀ i) μ)
    (hv₀_meas : AEMeasurable v₀ μ)
    (hu₁_meas : ∀ i, AEMeasurable (u₁ i) μ)
    (hv₁_meas : AEMeasurable v₁ μ)
    (hu₀_finite : ∀ i, ∀ᵐ x ∂μ, u₀ i x ≠ ⊤ ∧ u₀ i x ≠ ⊥)
    (hv₀_finite : ∀ᵐ x ∂μ, v₀ x ≠ ⊤ ∧ v₀ x ≠ ⊥)
    (hu₁_finite : ∀ i, ∀ᵐ x ∂μ, u₁ i x ≠ ⊤ ∧ u₁ i x ≠ ⊥)
    (hv₁_finite : ∀ᵐ x ∂μ, v₁ x ≠ ⊤ ∧ v₁ x ≠ ⊥)
    (hL1₀ : Tendsto
      (fun i => ∫⁻ x, canonicalERealAbsDiff (u₀ i x) (v₀ x) ∂μ)
      atTop (𝓝 0))
    (hL1₁ : Tendsto
      (fun i => ∫⁻ x, canonicalERealAbsDiff (u₁ i x) (v₁ x) ∂μ)
      atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂μ,
      Tendsto (fun k => u₀ (ns k) x) atTop (𝓝 (v₀ x)) ∧
      Tendsto (fun k => u₁ (ns k) x) atTop (𝓝 (v₁ x)) := by
  obtain ⟨ns, hns, hreal⟩ :=
    exists_common_strictMono_tendsto_ae_toReal_of_lintegral_canonicalERealAbsDiff
      hu₀_meas hv₀_meas hu₁_meas hv₁_meas hL1₀ hL1₁
  have hreal₀ : ∀ᵐ x ∂μ,
      Tendsto (fun k => (u₀ (ns k) x).toReal) atTop (𝓝 (v₀ x).toReal) :=
    hreal.mono fun _ hx => hx.1
  have hreal₁ : ∀ᵐ x ∂μ,
      Tendsto (fun k => (u₁ (ns k) x).toReal) atTop (𝓝 (v₁ x).toReal) :=
    hreal.mono fun _ hx => hx.2
  have heReal₀ := ae_tendsto_eReal_of_ae_tendsto_toReal hreal₀
    (fun k => hu₀_finite (ns k)) hv₀_finite
  have heReal₁ := ae_tendsto_eReal_of_ae_tendsto_toReal hreal₁
    (fun k => hu₁_finite (ns k)) hv₁_finite
  refine ⟨ns, hns, ?_⟩
  filter_upwards [heReal₀, heReal₁] with x h₀ h₁
  exact ⟨h₀, h₁⟩

/-- Chartwise canonical `L¹` convergence has a strictly increasing subsequence
whose real chart representatives converge almost everywhere on the restricted
chart set. -/
theorem chartL1EDistance_exists_strictMono_tendsto_ae_toReal
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M]
    {u : ℕ → M → EReal} {v : M → EReal}
    (e : ComplexChart n M) (K : Set (ComplexModel n))
    (hu : ∀ i, AEMeasurable (fun z => chartFunction (u i) e z)
      (volume.restrict K))
    (hv : AEMeasurable (fun z => chartFunction v e z)
      (volume.restrict K))
    (hL1 : Tendsto (fun i => chartL1EDistance (u i) v e K)
      atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ z ∂volume.restrict K,
      Tendsto (fun k => (chartFunction (u (ns k)) e z).toReal)
        atTop (𝓝 (chartFunction v e z).toReal) :=
  (chartL1EDistance_tendstoInMeasure_toReal e K hu hv hL1).exists_seq_tendsto_ae

/-- Two chartwise canonical `L¹` limits on one chart set admit one common
subsequence with almost-everywhere convergence of both real representatives. -/
theorem chartL1EDistance_exists_common_strictMono_tendsto_ae_toReal
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M]
    {u₀ u₁ : ℕ → M → EReal} {v₀ v₁ : M → EReal}
    (e : ComplexChart n M) (K : Set (ComplexModel n))
    (hu₀ : ∀ i, AEMeasurable (fun z => chartFunction (u₀ i) e z)
      (volume.restrict K))
    (hv₀ : AEMeasurable (fun z => chartFunction v₀ e z)
      (volume.restrict K))
    (hu₁ : ∀ i, AEMeasurable (fun z => chartFunction (u₁ i) e z)
      (volume.restrict K))
    (hv₁ : AEMeasurable (fun z => chartFunction v₁ e z)
      (volume.restrict K))
    (hL1₀ : Tendsto (fun i => chartL1EDistance (u₀ i) v₀ e K)
      atTop (𝓝 0))
    (hL1₁ : Tendsto (fun i => chartL1EDistance (u₁ i) v₁ e K)
      atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ z ∂volume.restrict K,
      Tendsto (fun k => (chartFunction (u₀ (ns k)) e z).toReal)
        atTop (𝓝 (chartFunction v₀ e z).toReal) ∧
      Tendsto (fun k => (chartFunction (u₁ (ns k)) e z).toReal)
        atTop (𝓝 (chartFunction v₁ e z).toReal) := by
  exact exists_common_strictMono_tendsto_ae_of_tendstoInMeasure
    (u := fun i z => (chartFunction (u₀ i) e z).toReal)
    (uLim := fun z => (chartFunction v₀ e z).toReal)
    (v := fun i z => (chartFunction (u₁ i) e z).toReal)
    (vLim := fun z => (chartFunction v₁ e z).toReal)
    (chartL1EDistance_tendstoInMeasure_toReal e K hu₀ hv₀ hL1₀)
    (chartL1EDistance_tendstoInMeasure_toReal e K hu₁ hv₁ hL1₁)

/-- If the two chart families and their limits are finite almost everywhere,
the common chartwise `L¹` subsequence converges almost everywhere in `EReal`. -/
theorem chartL1EDistance_exists_common_strictMono_tendsto_ae_eReal
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M]
    {u₀ u₁ : ℕ → M → EReal} {v₀ v₁ : M → EReal}
    (e : ComplexChart n M) (K : Set (ComplexModel n))
    (hu₀_meas : ∀ i, AEMeasurable (fun z => chartFunction (u₀ i) e z)
      (volume.restrict K))
    (hv₀_meas : AEMeasurable (fun z => chartFunction v₀ e z)
      (volume.restrict K))
    (hu₁_meas : ∀ i, AEMeasurable (fun z => chartFunction (u₁ i) e z)
      (volume.restrict K))
    (hv₁_meas : AEMeasurable (fun z => chartFunction v₁ e z)
      (volume.restrict K))
    (hu₀_finite : ∀ i, ∀ᵐ z ∂volume.restrict K,
      chartFunction (u₀ i) e z ≠ ⊤ ∧ chartFunction (u₀ i) e z ≠ ⊥)
    (hv₀_finite : ∀ᵐ z ∂volume.restrict K,
      chartFunction v₀ e z ≠ ⊤ ∧ chartFunction v₀ e z ≠ ⊥)
    (hu₁_finite : ∀ i, ∀ᵐ z ∂volume.restrict K,
      chartFunction (u₁ i) e z ≠ ⊤ ∧ chartFunction (u₁ i) e z ≠ ⊥)
    (hv₁_finite : ∀ᵐ z ∂volume.restrict K,
      chartFunction v₁ e z ≠ ⊤ ∧ chartFunction v₁ e z ≠ ⊥)
    (hL1₀ : Tendsto (fun i => chartL1EDistance (u₀ i) v₀ e K)
      atTop (𝓝 0))
    (hL1₁ : Tendsto (fun i => chartL1EDistance (u₁ i) v₁ e K)
      atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ z ∂volume.restrict K,
      Tendsto (fun k => chartFunction (u₀ (ns k)) e z)
        atTop (𝓝 (chartFunction v₀ e z)) ∧
      Tendsto (fun k => chartFunction (u₁ (ns k)) e z)
        atTop (𝓝 (chartFunction v₁ e z)) := by
  apply
    exists_common_strictMono_tendsto_ae_eReal_of_lintegral_canonicalERealAbsDiff
      (u₀ := fun i z => chartFunction (u₀ i) e z)
      (v₀ := fun z => chartFunction v₀ e z)
      (u₁ := fun i z => chartFunction (u₁ i) e z)
      (v₁ := fun z => chartFunction v₁ e z)
      hu₀_meas hv₀_meas hu₁_meas hv₁_meas
      hu₀_finite hv₀_finite hu₁_finite hv₁_finite
  · simpa only [chartL1EDistance] using hL1₀
  · simpa only [chartL1EDistance] using hL1₁

end

end SGPT.Foundations.Analysis.FirstPass
