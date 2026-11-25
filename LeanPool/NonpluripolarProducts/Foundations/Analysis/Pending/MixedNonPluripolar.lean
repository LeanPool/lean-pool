/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.MixedNonPluripolar
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MixedMongeAmpere
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.NonPluripolarLimit
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.MeasureLocality

/-!
# Actual mixed truncation measures and their increasing limit

Bounded mixed max locality (Pending.BedfordTaylorMaxLocality) and noncharging
of arbitrary locally pluripolar sets (Pending.BedfordTaylorNonCharging, from the
weighted CLN estimate) are proved. Ordinary-open locality follows from
restriction, dependence on the potentials only on the open set, and uniqueness.
All measures below are constructed from canonical mixed BT existence;
compatibility, the increasing limit, restrictions and uniqueness are derived.
Uniform compact mass is an exact additional criterion, not automatic.
No exterior-wedge identification, coordinate invariance, or global current
construction is asserted. Normalization: `ddC = i ∂∂bar / (2π)`.
Sources: BEGZ `equ:nonpp`, `equ:welldef`, `pro:basic`; revised `sec:npp`;
Demailly CADG III.3.11 for bounded mixed noncharging.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.MixedNonPluripolar

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
open FirstPass.MixedNonPluripolar FirstPass.IncreasingMeasures
open MixedMongeAmpere

variable {n : ℕ}

/-- Bounded mixed plurifine locality on a common strict superlevel.
Both full BT relations include PSH, local boundedness, testing and support.
The set is not asserted to be ordinary open. -/
theorem localMixedBedfordTaylorMeasure_max_const_locality
    {Ω : Opens (ComplexModel n)} {v w : Fin n → ComplexModel n → ℝ}
    {μ ν : Measure (ComplexModel n)}
    (hμ : IsLocalMixedBedfordTaylorMeasure Ω v μ)
    (hν : IsLocalMixedBedfordTaylorMeasure Ω w ν) (c : ℝ)
    (hmax : ∀ i, EqOn (w i) (fun z => max (v i z) c) Ω) :
    ν.restrict {z | z ∈ Ω ∧ ∀ i, c < v i z} =
      μ.restrict {z | z ∈ Ω ∧ ∀ i, c < v i z} :=
  BedfordTaylor.IsLocalMixedBedfordTaylorMeasure.restrict_max_const hμ hν c hmax

/-- Restricting a mixed BT measure to a smaller open set gives the mixed BT
measure there. -/
theorem localMixedBedfordTaylorMeasure_restrict {Ω U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {μ : Measure (ComplexModel n)}
    (hμ : IsLocalMixedBedfordTaylorMeasure Ω u μ) (hU : U ≤ Ω) :
    IsLocalMixedBedfordTaylorMeasure U u (μ.restrict (U : Set (ComplexModel n))) := by
  refine ⟨fun i => (hμ.1 i).mono hU, ?_,
    MeasureLocality.finiteOnCompacts_restrict hμ.2.2.1 hU, fun V hV ↦ ?_⟩
  · rw [Measure.restrict_apply U.isOpen.measurableSet.compl]
    simp
  · have hVΩ : RelativelyCompactIn V Ω := ⟨hV.1, hV.2.trans hU⟩
    obtain ⟨hex, hconv⟩ := hμ.2.2.2 V hVΩ
    refine ⟨hex, fun f hf φ hφ hφc hφV ↦ ?_⟩
    rw [MeasureLocality.integral_restrict_eq_of_tsupport_subset
      (hφV.trans (subset_closure.trans hV.2))]
    exact hconv f hf φ hφ hφc hφV

/-- The mixed BT relation on an open set only depends on the potentials there. -/
theorem IsLocalMixedBedfordTaylorMeasure.congr {U : Opens (ComplexModel n)}
    {v w : Fin n → ComplexModel n → ℝ} {μ : Measure (ComplexModel n)}
    (hμ : IsLocalMixedBedfordTaylorMeasure U v μ) (hvw : ∀ i, EqOn (v i) (w i) U) :
    IsLocalMixedBedfordTaylorMeasure U w μ := by
  have happ {V : Opens (ComplexModel n)} (hVU : V ≤ U) {f : ℕ → Fin n → ComplexModel n → ℝ}
      (hf : IsDecreasingMixedApproximation V v f) : IsDecreasingMixedApproximation V w f :=
    ⟨hf.1, hf.2.1, fun i z hz ↦ (hvw i (hVU hz)) ▸ hf.2.2 i z hz⟩
  have happ' {V : Opens (ComplexModel n)} (hVU : V ≤ U) {f : ℕ → Fin n → ComplexModel n → ℝ}
      (hf : IsDecreasingMixedApproximation V w f) : IsDecreasingMixedApproximation V v f :=
    ⟨hf.1, hf.2.1, fun i z hz ↦ (hvw i (hVU hz)).symm ▸ hf.2.2 i z hz⟩
  refine ⟨fun i ↦ ⟨fun x hx ↦ ?_, fun z hz ↦ ?_⟩, hμ.2.1, hμ.2.2.1, fun V hV ↦ ?_⟩
  · refine ((hμ.1 i).1 x hx).congr ?_
    filter_upwards [U.isOpen.mem_nhds hx] with y hy
    rw [hvw i hy]
  · obtain ⟨V, hzV, hVU, C, hC⟩ := (hμ.1 i).2 z hz
    exact ⟨V, hzV, hVU, C, fun y hy ↦ (hvw i (hVU hy)) ▸ hC y hy⟩
  · have hVU : V ≤ U := subset_closure.trans hV.2
    obtain ⟨⟨f, hf⟩, hconv⟩ := hμ.2.2.2 V hV
    exact ⟨⟨f, happ hVU hf⟩, fun g hg ↦ hconv g (happ' hVU hg)⟩

/-- Ordinary-open locality, including equality of distinct representatives
on the smaller domain; no relation outside U is required. -/
theorem localMixedBedfordTaylorMeasure_open_locality
    {Ω U : Opens (ComplexModel n)} {v w : Fin n → ComplexModel n → ℝ}
    {μ ν : Measure (ComplexModel n)} (hU : U ≤ Ω)
    (hμ : IsLocalMixedBedfordTaylorMeasure Ω v μ)
    (hν : IsLocalMixedBedfordTaylorMeasure U w ν)
    (hvw : ∀ i, EqOn (v i) (w i) U) :
    μ.restrict (U : Set (ComplexModel n)) = ν :=
  localMixedBedfordTaylorMeasure_unique
    (IsLocalMixedBedfordTaylorMeasure.congr (localMixedBedfordTaylorMeasure_restrict hμ hU) hvw) hν

/-- The mixed weighted CLN estimate implies noncharging; this is never a
consequence of Haar-nullity alone. -/
theorem localMixedBedfordTaylorMeasure_doesNotChargePluripolarOn
    {Ω : Opens (ComplexModel n)} {v : Fin n → ComplexModel n → ℝ}
    {μ : Measure (ComplexModel n)} (hμ : IsLocalMixedBedfordTaylorMeasure Ω v μ) :
    DoesNotChargePluripolarOn μ (Ω : Set (ComplexModel n)) :=
  BedfordTaylor.IsLocalMixedBedfordTaylorMeasure.doesNotChargePluripolarOn hμ

theorem canonicalMixedBedfordTaylorMeasure_open_locality
    {Ω U : Opens (ComplexModel n)} {v w : Fin n → ComplexModel n → ℝ}
    (hU : U ≤ Ω) (hv : IsLocallyBoundedMixedPshOn Ω v)
    (hw : IsLocallyBoundedMixedPshOn U w) (hvw : ∀ i, EqOn (v i) (w i) U) :
    (canonicalMixedBedfordTaylorMeasure Ω v hv).restrict (U : Set (ComplexModel n)) =
      canonicalMixedBedfordTaylorMeasure U w hw :=
  localMixedBedfordTaylorMeasure_open_locality hU
    (canonicalMixedBedfordTaylorMeasure_spec Ω v hv)
    (canonicalMixedBedfordTaylorMeasure_spec U w hw) hvw

theorem canonicalMixedBedfordTaylorMeasure_restrict
    {Ω U : Opens (ComplexModel n)} {v : Fin n → ComplexModel n → ℝ}
    (hU : U ≤ Ω) (hv : IsLocallyBoundedMixedPshOn Ω v)
    (hvU : IsLocallyBoundedMixedPshOn U v) :
    (canonicalMixedBedfordTaylorMeasure Ω v hv).restrict (U : Set (ComplexModel n)) =
      canonicalMixedBedfordTaylorMeasure U v hvU :=
  canonicalMixedBedfordTaylorMeasure_open_locality hU hv hvU (fun _ _ _ => rfl)

/-- Canonical bounded mixed BT of the real truncations, restricted to the
actual common strict locus. The constructor consumes Pending BT existence. -/
def mixedTruncationMeasure (Ω : Opens (ComplexModel n))
    (u : Fin n → ComplexModel n → EReal) (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (k : ℕ) : Measure (ComplexModel n) :=
  (canonicalMixedBedfordTaylorMeasure Ω (mixedTruncationReal u k)
    (mixedTruncationReal_isLocallyBounded hu k)).restrict (commonStrictLocus Ω u k)

variable {Ω : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → EReal}

theorem mixedTruncationMeasure_proof_independent
    (hu hv : ∀ i, PlurisubharmonicOn (u i) Ω) (k : ℕ) :
    mixedTruncationMeasure Ω u hu k = mixedTruncationMeasure Ω u hv k := rfl

theorem mixedBedfordTaylor_truncation_restrict (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    {k l : ℕ} (hkl : k ≤ l) :
    (canonicalMixedBedfordTaylorMeasure Ω (mixedTruncationReal u l)
      (mixedTruncationReal_isLocallyBounded hu l)).restrict (commonStrictLocus Ω u k) =
    (canonicalMixedBedfordTaylorMeasure Ω (mixedTruncationReal u k)
      (mixedTruncationReal_isLocallyBounded hu k)).restrict (commonStrictLocus Ω u k) := by
  have h := localMixedBedfordTaylorMeasure_max_const_locality
    (canonicalMixedBedfordTaylorMeasure_spec Ω _ (mixedTruncationReal_isLocallyBounded hu l))
    (canonicalMixedBedfordTaylorMeasure_spec Ω _ (mixedTruncationReal_isLocallyBounded hu k))
    (-(k : ℝ)) (mixedTruncationReal_nested hu hkl)
  rw [← commonStrictLocus_eq_real_superlevel hu hkl] at h
  exact h.symm

theorem mixedTruncationMeasure_restrict (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    {k l : ℕ} (hkl : k ≤ l) :
    (mixedTruncationMeasure Ω u hu l).restrict (commonStrictLocus Ω u k) =
      mixedTruncationMeasure Ω u hu k := by
  unfold mixedTruncationMeasure
  rw [Measure.restrict_restrict_of_subset (commonStrictLocus_mono Ω u hkl)]
  exact mixedBedfordTaylor_truncation_restrict hu hkl

theorem mixedTruncationMeasure_mono (hu : ∀ i, PlurisubharmonicOn (u i) Ω) :
    Monotone (mixedTruncationMeasure Ω u hu) := by
  intro k l hkl
  rw [← mixedTruncationMeasure_restrict hu hkl]
  exact Measure.restrict_le_self

theorem mixedTruncationMeasure_finiteOnCompacts (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (k : ℕ) {K : Set (ComplexModel n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    mixedTruncationMeasure Ω u hu k K < ⊤ := by
  unfold mixedTruncationMeasure
  rw [Measure.restrict_apply hK.measurableSet]
  exact (measure_mono inter_subset_left).trans_lt
    (canonicalMixedBedfordTaylorMeasure_finiteOnCompacts
      (mixedTruncationReal_isLocallyBounded hu k) hK hKΩ)

theorem mixedTruncationMeasure_poleSet (hu : ∀ i, PlurisubharmonicOn (u i) Ω) (k : ℕ) :
    mixedTruncationMeasure Ω u hu k (componentPoleSet u) = 0 := by
  unfold mixedTruncationMeasure
  rw [Measure.restrict_apply' (measurableSet_commonStrictLocus hu k)]
  have he : componentPoleSet u ∩ commonStrictLocus Ω u k = ∅ := by
    exact eq_empty_iff_forall_notMem.mpr
      (fun _ hz => pole_not_mem_commonStrictLocus k hz.1 hz.2)
  rw [he, measure_empty]

theorem mixedTruncationMeasure_compl (hu : ∀ i, PlurisubharmonicOn (u i) Ω) (k : ℕ) :
    mixedTruncationMeasure Ω u hu k (Ω : Set (ComplexModel n))ᶜ = 0 := by
  unfold mixedTruncationMeasure
  rw [Measure.restrict_apply Ω.isOpen.measurableSet.compl]
  have he : (Ω : Set (ComplexModel n))ᶜ ∩ commonStrictLocus Ω u k = ∅ :=
    eq_empty_iff_forall_notMem.mpr (fun _ hz => hz.1 hz.2.1)
  rw [he, measure_empty]

/-- The actual mixed increasing limit, possibly infinite on interior compact
sets. In dimension zero this retains the empty tuple, hence has no pole erasure. -/
def mixedTruncationLimitMeasure (Ω : Opens (ComplexModel n))
    (u : Fin n → ComplexModel n → EReal) (hu : ∀ i, PlurisubharmonicOn (u i) Ω) :
    Measure (ComplexModel n) :=
  increasingLimit (mixedTruncationMeasure Ω u hu) (mixedTruncationMeasure_mono hu)

theorem mixedTruncationLimitMeasure_proof_independent
    (hu hv : ∀ i, PlurisubharmonicOn (u i) Ω) :
    mixedTruncationLimitMeasure Ω u hu = mixedTruncationLimitMeasure Ω u hv := rfl

theorem mixedTruncationLimitMeasure_apply (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (s : Set (ComplexModel n)) :
    mixedTruncationLimitMeasure Ω u hu s = ⨆ k, mixedTruncationMeasure Ω u hu k s :=
  increasingLimit_apply _ _ s

theorem mixedTruncationMeasure_le_limit (hu : ∀ i, PlurisubharmonicOn (u i) Ω) (k : ℕ) :
    mixedTruncationMeasure Ω u hu k ≤ mixedTruncationLimitMeasure Ω u hu :=
  le_increasingLimit _ _ k

theorem mixedTruncationLimitMeasure_le_iff (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (ν : Measure (ComplexModel n)) :
    mixedTruncationLimitMeasure Ω u hu ≤ ν ↔ ∀ k, mixedTruncationMeasure Ω u hu k ≤ ν :=
  increasingLimit_le_iff _ _ ν

theorem tendsto_mixedTruncationMeasure (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (s : Set (ComplexModel n)) :
    Tendsto (fun k => mixedTruncationMeasure Ω u hu k s) atTop
      (𝓝 (mixedTruncationLimitMeasure Ω u hu s)) :=
  tendsto_increasingLimit _ _ s

theorem mixedTruncationLimitMeasure_zero_iff (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (s : Set (ComplexModel n)) :
    mixedTruncationLimitMeasure Ω u hu s = 0 ↔ ∀ k, mixedTruncationMeasure Ω u hu k s = 0 :=
  increasingLimit_zero_iff _ _ s

theorem mixedTruncationLimitMeasure_poleSet (hu : ∀ i, PlurisubharmonicOn (u i) Ω) :
    mixedTruncationLimitMeasure Ω u hu (componentPoleSet u) = 0 :=
  (mixedTruncationLimitMeasure_zero_iff hu _).mpr (mixedTruncationMeasure_poleSet hu)

theorem mixedTruncationLimitMeasure_compl (hu : ∀ i, PlurisubharmonicOn (u i) Ω) :
    mixedTruncationLimitMeasure Ω u hu (Ω : Set (ComplexModel n))ᶜ = 0 :=
  (mixedTruncationLimitMeasure_zero_iff hu _).mpr (mixedTruncationMeasure_compl hu)

theorem mixedTruncationLimitMeasure_restrict_commonStrictLocus
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω) (k : ℕ) :
    (mixedTruncationLimitMeasure Ω u hu).restrict (commonStrictLocus Ω u k) =
      mixedTruncationMeasure Ω u hu k :=
  increasingLimit_restrict_of_stabilizes _ (mixedTruncationMeasure_mono hu) _ k
    (fun _ hkl => mixedTruncationMeasure_restrict hu hkl)

/-- Uniqueness requires no local finiteness and no nontriviality of components.
The union of their pole sets need not itself be locally pluripolar. -/
theorem mixedTruncationLimitMeasure_unique (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    {ν : Measure (ComplexModel n)} (hνΩ : ν (Ω : Set (ComplexModel n))ᶜ = 0)
    (hνpole : ν (componentPoleSet u) = 0)
    (hν : ∀ k, ν.restrict (commonStrictLocus Ω u k) = mixedTruncationMeasure Ω u hu k) :
    ν = mixedTruncationLimitMeasure Ω u hu := by
  have hae (ξ : Measure (ComplexModel n))
      (hξΩ : ξ (Ω : Set (ComplexModel n))ᶜ = 0) (hξpole : ξ (componentPoleSet u) = 0) :
      ∀ᵐ z ∂ξ, z ∈ ⋃ k, commonStrictLocus Ω u k := by
    apply ae_iff.mpr
    change ξ (⋃ k, commonStrictLocus Ω u k)ᶜ = 0
    rw [compl_iUnion_commonStrictLocus]
    exact measure_union_null hξΩ hξpole
  have h := Measure.restrict_iUnion_congr.mpr (fun k =>
    (hν k).trans (mixedTruncationLimitMeasure_restrict_commonStrictLocus hu k).symm)
  rw [Measure.restrict_eq_self_of_ae_mem (hae ν hνΩ hνpole),
    Measure.restrict_eq_self_of_ae_mem (hae _ (mixedTruncationLimitMeasure_compl hu)
      (mixedTruncationLimitMeasure_poleSet hu))] at h
  exact h

/-- Exact BEGZ compact-mass condition in top degree; it is additional data. -/
def HasUniformCompactMixedTruncationMass (Ω : Opens (ComplexModel n))
    (u : Fin n → ComplexModel n → EReal) (hu : ∀ i, PlurisubharmonicOn (u i) Ω) : Prop :=
  ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ Ω →
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k, mixedTruncationMeasure Ω u hu k K ≤ C

theorem mixedTruncationLimitMeasure_lt_top_iff (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (s : Set (ComplexModel n)) :
    mixedTruncationLimitMeasure Ω u hu s < ⊤ ↔
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k, mixedTruncationMeasure Ω u hu k s ≤ C :=
  increasingLimit_lt_top_iff _ _ s

theorem mixedTruncationLimitMeasure_finiteOnCompacts_iff
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω) :
    (∀ K : Set (ComplexModel n), IsCompact K → K ⊆ Ω →
      mixedTruncationLimitMeasure Ω u hu K < ⊤) ↔
      HasUniformCompactMixedTruncationMass Ω u hu := by
  constructor
  · intro h K hK hKΩ
    exact (mixedTruncationLimitMeasure_lt_top_iff hu K).mp (h K hK hKΩ)
  · intro h K hK hKΩ
    exact (mixedTruncationLimitMeasure_lt_top_iff hu K).mpr (h K hK hKΩ)

/-- Locality for potentially different tuples that agree on U. -/
theorem mixedTruncationMeasure_open_locality {U : Opens (ComplexModel n)}
    {v : Fin n → ComplexModel n → EReal} (hU : U ≤ Ω)
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω) (hv : ∀ i, PlurisubharmonicOn (v i) U)
    (huv : ∀ i, EqOn (u i) (v i) U) (k : ℕ) :
    (mixedTruncationMeasure Ω u hu k).restrict (U : Set (ComplexModel n)) =
      mixedTruncationMeasure U v hv k := by
  unfold mixedTruncationMeasure
  rw [Measure.restrict_restrict U.isOpen.measurableSet]
  rw [← canonicalMixedBedfordTaylorMeasure_open_locality hU
    (mixedTruncationReal_isLocallyBounded hu k) (mixedTruncationReal_isLocallyBounded hv k)
    (fun i z hz => congrArg (fun a : EReal => (max a ((-(k : ℝ) : ℝ) : EReal)).toReal)
      (huv i hz))]
  rw [Measure.restrict_restrict_of_subset (commonStrictLocus_subset k)]
  congr 1
  ext z
  constructor
  · intro hz
    exact ⟨hz.1, fun i => (huv i hz.1) ▸ hz.2.2 i⟩
  · intro hz
    exact ⟨hz.1, hU hz.1, fun i => (huv i hz.1).symm ▸ hz.2 i⟩

theorem mixedTruncationLimitMeasure_open_locality {U : Opens (ComplexModel n)}
    {v : Fin n → ComplexModel n → EReal} (hU : U ≤ Ω)
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω) (hv : ∀ i, PlurisubharmonicOn (v i) U)
    (huv : ∀ i, EqOn (u i) (v i) U) :
    (mixedTruncationLimitMeasure Ω u hu).restrict (U : Set (ComplexModel n)) =
      mixedTruncationLimitMeasure U v hv := by
  change (increasingLimit _ _).restrict (U : Set (ComplexModel n)) = _
  rw [increasingLimit_restrict]
  apply Measure.ext
  intro s _
  calc
    increasingLimit _ _ s = ⨆ k, (mixedTruncationMeasure Ω u hu k).restrict
        (U : Set (ComplexModel n)) s := increasingLimit_apply _ _ s
    _ = ⨆ k, mixedTruncationMeasure U v hv k s := by
      simp_rw [mixedTruncationMeasure_open_locality hU hu hv huv]
    _ = mixedTruncationLimitMeasure U v hv s := (mixedTruncationLimitMeasure_apply hv s).symm

theorem mixedTruncationLimitMeasure_restrict_open {U : Opens (ComplexModel n)}
    (hU : U ≤ Ω) (hu : ∀ i, PlurisubharmonicOn (u i) Ω) :
    (mixedTruncationLimitMeasure Ω u hu).restrict (U : Set (ComplexModel n)) =
      mixedTruncationLimitMeasure U u (fun i => (hu i).mono hU) :=
  mixedTruncationLimitMeasure_open_locality hU hu _ (fun _ _ _ => rfl)

theorem mixedTruncationMeasure_diagonal (hn : 0 < n)
    {v : ComplexModel n → EReal} (hv : PlurisubharmonicOn v Ω) (k : ℕ) :
    mixedTruncationMeasure Ω (fun _ => v) (fun _ => hv) k =
      MongeAmpere.truncationMeasure Ω v hv k := by
  unfold mixedTruncationMeasure
  change (canonicalMixedBedfordTaylorMeasure Ω (fun _ => truncationReal v k)
    (fun _ => truncationReal_isLocallyBoundedPshOn hv k)).restrict _ = _
  rw [canonicalMixedBedfordTaylorMeasure_diagonal, commonStrictLocus_diagonal hn]
  rfl

theorem mixedTruncationLimitMeasure_diagonal (hn : 0 < n)
    {v : ComplexModel n → EReal} (hv : PlurisubharmonicOn v Ω) :
    mixedTruncationLimitMeasure Ω (fun _ => v) (fun _ => hv) =
      MongeAmpere.truncationLimitMeasure Ω v hv := by
  apply Measure.ext
  intro s _
  rw [mixedTruncationLimitMeasure_apply, MongeAmpere.truncationLimitMeasure_apply]
  simp_rw [mixedTruncationMeasure_diagonal hn hv]

/-- For an empty tuple all steps equal the same canonical empty bounded BT.
The real empty tuple v is arbitrary: any two such tuples are equal. -/
theorem mixedTruncationMeasure_zero_dim (Ω : Opens (ComplexModel 0))
    (u : Fin 0 → ComplexModel 0 → EReal) (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (v : Fin 0 → ComplexModel 0 → ℝ) (hv : IsLocallyBoundedMixedPshOn Ω v) (k : ℕ) :
    mixedTruncationMeasure Ω u hu k = canonicalMixedBedfordTaylorMeasure Ω v hv := by
  have he : mixedTruncationReal u k = v := funext (fun i => Fin.elim0 i)
  unfold mixedTruncationMeasure
  simp only [commonStrictLocus_zero]
  subst v
  exact Measure.restrict_eq_self_of_ae_mem
    (ae_iff.mpr (canonicalMixedBedfordTaylorMeasure_compl Ω _ _))

theorem mixedTruncationLimitMeasure_zero_dim (Ω : Opens (ComplexModel 0))
    (u : Fin 0 → ComplexModel 0 → EReal) (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (v : Fin 0 → ComplexModel 0 → ℝ) (hv : IsLocallyBoundedMixedPshOn Ω v) :
    mixedTruncationLimitMeasure Ω u hu = canonicalMixedBedfordTaylorMeasure Ω v hv := by
  apply Measure.ext
  intro s _
  rw [mixedTruncationLimitMeasure_apply]
  simp_rw [mixedTruncationMeasure_zero_dim Ω u hu v hv]
  simp

/-- Real locally bounded tuples recover their original bounded mixed BT. -/
theorem mixedTruncationLimitMeasure_eq_canonical {v : Fin n → ComplexModel n → ℝ}
    (hv : IsLocallyBoundedMixedPshOn Ω v) :
    mixedTruncationLimitMeasure Ω (fun i z => (v i z : EReal)) (fun i => (hv i).1) =
      canonicalMixedBedfordTaylorMeasure Ω v hv := by
  symm
  refine mixedTruncationLimitMeasure_unique (fun i => (hv i).1)
    (canonicalMixedBedfordTaylorMeasure_compl Ω v hv) ?_ ?_
  · simp [componentPoleSet]
  · intro k
    have hmax : ∀ i, EqOn (mixedTruncationReal (fun i z => (v i z : EReal)) k i)
        (fun z => max (v i z) (-(k : ℝ))) Ω := by
      intro i z _
      exact truncationReal_coe (v i) k z
    have hset : commonStrictLocus Ω (fun i z => (v i z : EReal)) k =
        {z | z ∈ Ω ∧ ∀ i, -(k : ℝ) < v i z} := by
      ext z
      simp only [commonStrictLocus, mem_ofPred_eq, EReal.coe_lt_coe_iff]
    unfold mixedTruncationMeasure
    rw [hset]
    exact (localMixedBedfordTaylorMeasure_max_const_locality
      (canonicalMixedBedfordTaylorMeasure_spec Ω v hv)
      (canonicalMixedBedfordTaylorMeasure_spec Ω _
        (mixedTruncationReal_isLocallyBounded (fun i => (hv i).1) k)) (-(k : ℝ)) hmax).symm

theorem mixedTruncationMeasure_doesNotChargePluripolarOn
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω) (k : ℕ) :
    DoesNotChargePluripolarOn (mixedTruncationMeasure Ω u hu k) (Ω : Set (ComplexModel n)) := by
  intro s hs
  unfold mixedTruncationMeasure
  apply le_antisymm
  · exact (Measure.le_iff'.mp Measure.restrict_le_self _).trans_eq
      (localMixedBedfordTaylorMeasure_doesNotChargePluripolarOn
        (canonicalMixedBedfordTaylorMeasure_spec Ω _
          (mixedTruncationReal_isLocallyBounded hu k)) s hs)
  · exact bot_le

theorem mixedTruncationLimitMeasure_doesNotChargePluripolarOn
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω) :
    DoesNotChargePluripolarOn (mixedTruncationLimitMeasure Ω u hu) (Ω : Set (ComplexModel n)) := by
  intro s hs
  exact (mixedTruncationLimitMeasure_zero_iff hu _).mpr
    (fun k => mixedTruncationMeasure_doesNotChargePluripolarOn hu k s hs)

/-- **Congruence of the truncation limit.** Only the values on `Ω` matter. -/
theorem mixedTruncationLimitMeasure_congr {v : Fin n → ComplexModel n → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω) (hv : ∀ i, PlurisubharmonicOn (v i) Ω)
    (huv : ∀ i, EqOn (u i) (v i) Ω) :
    mixedTruncationLimitMeasure Ω u hu = mixedTruncationLimitMeasure Ω v hv := by
  have h := mixedTruncationLimitMeasure_open_locality (Ω := Ω) (U := Ω) le_rfl hu hv huv
  rwa [Measure.restrict_eq_self_of_ae_mem
    (ae_iff.mpr (mixedTruncationLimitMeasure_compl hu))] at h

/-- An extended-real tuple that agrees on `Ω` with a real locally bounded tuple
has the bounded mixed Bedford–Taylor measure as its truncation limit. The
tuple itself need not be a coercion: the corrected potentials of a patch are
sums of a chart function and a smooth potential. -/
theorem mixedTruncationLimitMeasure_eq_canonical_of_eqOn {v : Fin n → ComplexModel n → ℝ}
    (hv : IsLocallyBoundedMixedPshOn Ω v) (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (huv : ∀ i, EqOn (u i) (fun z => (v i z : EReal)) Ω) :
    mixedTruncationLimitMeasure Ω u hu = canonicalMixedBedfordTaylorMeasure Ω v hv := by
  rw [mixedTruncationLimitMeasure_congr hu (fun i => (hv i).1) huv,
    mixedTruncationLimitMeasure_eq_canonical hv]

/-- **The bounded case of the BEGZ uniform compact-mass condition.** A tuple
that is real and locally bounded on `Ω` satisfies it unconditionally: its
truncation limit is the bounded mixed Bedford–Taylor measure, which is finite
on every compact subset of `Ω`. No Kähler background and no global hypothesis
is used. -/
theorem hasUniformCompactMixedTruncationMass_of_eqOn {v : Fin n → ComplexModel n → ℝ}
    (hv : IsLocallyBoundedMixedPshOn Ω v) (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (huv : ∀ i, EqOn (u i) (fun z => (v i z : EReal)) Ω) :
    HasUniformCompactMixedTruncationMass Ω u hu := by
  rw [← mixedTruncationLimitMeasure_finiteOnCompacts_iff]
  intro K hK hKΩ
  rw [mixedTruncationLimitMeasure_eq_canonical_of_eqOn hv hu huv]
  exact canonicalMixedBedfordTaylorMeasure_finiteOnCompacts hv hK hKΩ

end SGPT.Foundations.Analysis.Pending.MixedNonPluripolar
