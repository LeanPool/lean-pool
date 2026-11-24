/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.IncreasingMeasures
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PluripolarSets
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BTTruncations
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorNonCharging

/-!
# The actual scalar truncation-limit measure

This is an actual increasing limit of the selected Bedford--Taylor measures,
not an unspecified product supplied as a parameter. The limit construction
inherits bounded BT existence and max-locality from Pending.BTTruncations.
Bounded BT noncharging is proved from the weighted CLN estimate (Demailly
III.3.11) in Pending.BedfordTaylorNonCharging; noncharging of the steps and of
the limit is composed from it.
The truncation characterization and uniform compact-mass criterion introduce
no further holes. Automatic local finiteness is not asserted.

The usual scalar non-pluripolar product is intended in positive complex
dimension. The same formulas define a pole-erasing measure when n = 0, but
that convention is not identified with the usual empty wedge product.

Sources: BEGZ §1.2, equ:nonpp and equ:welldef; revised sec:npp;
Demailly CADG III.3.11 (weighted Chern--Levine--Nirenberg estimate).
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.MongeAmpere

open FirstPass FirstPass.MongeAmpere FirstPass.IncreasingMeasures

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u : ComplexModel n → EReal}

/-- The scalar truncation prescription as an actual measure. It may have
infinite mass on an interior compact set. In dimension zero this retains the
pole-erasing prescription, rather than the conventional empty wedge. -/
def truncationLimitMeasure (Ω : Opens (ComplexModel n)) (u : ComplexModel n → EReal)
    (hu : PlurisubharmonicOn u Ω) : Measure (ComplexModel n) :=
  increasingLimit (truncationMeasure Ω u hu) (truncationMeasure_mono hu)

theorem truncationLimitMeasure_apply (hu : PlurisubharmonicOn u Ω)
    (s : Set (ComplexModel n)) :
    truncationLimitMeasure Ω u hu s = ⨆ k, truncationMeasure Ω u hu k s :=
  increasingLimit_apply _ _ s

theorem truncationMeasure_le_limit (hu : PlurisubharmonicOn u Ω) (k : ℕ) :
    truncationMeasure Ω u hu k ≤ truncationLimitMeasure Ω u hu :=
  le_increasingLimit _ _ k

theorem truncationLimitMeasure_le_iff (hu : PlurisubharmonicOn u Ω)
    (ν : Measure (ComplexModel n)) :
    truncationLimitMeasure Ω u hu ≤ ν ↔ ∀ k, truncationMeasure Ω u hu k ≤ ν :=
  increasingLimit_le_iff _ _ ν

theorem tendsto_truncationMeasure (hu : PlurisubharmonicOn u Ω)
    (s : Set (ComplexModel n)) :
    Tendsto (fun k => truncationMeasure Ω u hu k s) atTop
      (𝓝 (truncationLimitMeasure Ω u hu s)) :=
  tendsto_increasingLimit _ _ s

theorem truncationLimitMeasure_zero_iff (hu : PlurisubharmonicOn u Ω)
    (s : Set (ComplexModel n)) :
    truncationLimitMeasure Ω u hu s = 0 ↔ ∀ k, truncationMeasure Ω u hu k s = 0 :=
  increasingLimit_zero_iff _ _ s

theorem truncationLimitMeasure_poleSet (hu : PlurisubharmonicOn u Ω) :
    truncationLimitMeasure Ω u hu {z | u z = ⊥} = 0 :=
  (truncationLimitMeasure_zero_iff hu _).mpr (truncationMeasure_poleSet hu)

theorem truncationLimitMeasure_compl (hu : PlurisubharmonicOn u Ω) :
    truncationLimitMeasure Ω u hu (Ω : Set (ComplexModel n))ᶜ = 0 := by
  apply (truncationLimitMeasure_zero_iff hu _).mpr
  intro k
  unfold truncationMeasure
  rw [Measure.restrict_apply Ω.isOpen.measurableSet.compl]
  have hempty : (Ω : Set (ComplexModel n))ᶜ ∩ strictTruncationLocus Ω u k = ∅ := by
    ext z
    simp only [mem_inter_iff, mem_compl_iff, strictTruncationLocus, mem_ofPred_eq,
      mem_empty_iff_false, iff_false, not_and]
    exact fun hz hz' _ => hz hz'
  rw [hempty, measure_empty]

/-- The limit agrees exactly with the kth BT step on its strict locus. -/
theorem truncationLimitMeasure_restrict_strictLocus (hu : PlurisubharmonicOn u Ω)
    (k : ℕ) :
    (truncationLimitMeasure Ω u hu).restrict (strictTruncationLocus Ω u k) =
      truncationMeasure Ω u hu k :=
  increasingLimit_restrict_of_stabilizes _ (truncationMeasure_mono hu) _ k
    (fun _ hkl => truncationMeasure_restrict hu hkl)

/-- Off-pole truncation restrictions and zero mass on the omitted set
determine the measure, even when it is not locally finite. -/
theorem truncationLimitMeasure_unique (hu : PlurisubharmonicOn u Ω)
    {ν : Measure (ComplexModel n)}
    (hνΩ : ν (Ω : Set (ComplexModel n))ᶜ = 0)
    (hνpole : ν {z | u z = ⊥} = 0)
    (hν : ∀ k, ν.restrict (strictTruncationLocus Ω u k) = truncationMeasure Ω u hu k) :
    ν = truncationLimitMeasure Ω u hu := by
  have hae (ξ : Measure (ComplexModel n))
      (hξΩ : ξ (Ω : Set (ComplexModel n))ᶜ = 0)
      (hξpole : ξ {z | u z = ⊥} = 0) :
      ∀ᵐ z ∂ξ, z ∈ ⋃ k, strictTruncationLocus Ω u k := by
    apply ae_iff.mpr
    rw [iUnion_strictTruncationLocus]
    have heq : {z | z ∉ {z | z ∈ Ω ∧ u z ≠ ⊥}} =
        (Ω : Set (ComplexModel n))ᶜ ∪ {z | u z = ⊥} := by
      ext z
      simp only [mem_ofPred_eq, mem_union, mem_compl_iff]
      tauto
    rw [heq]
    exact measure_union_null hξΩ hξpole
  have h := Measure.restrict_iUnion_congr.mpr (fun k =>
    (hν k).trans (truncationLimitMeasure_restrict_strictLocus hu k).symm)
  rw [Measure.restrict_eq_self_of_ae_mem (hae ν hνΩ hνpole),
    Measure.restrict_eq_self_of_ae_mem (hae _ (truncationLimitMeasure_compl hu)
      (truncationLimitMeasure_poleSet hu))] at h
  exact h

/-- The BEGZ local mass condition in top degree, on actual truncation measures.
The bound can depend on the interior compact set, but not on the level. -/
def HasUniformCompactTruncationMass (Ω : Opens (ComplexModel n))
    (u : ComplexModel n → EReal) (hu : PlurisubharmonicOn u Ω) : Prop :=
  ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ Ω →
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k, truncationMeasure Ω u hu k K ≤ C

theorem truncationLimitMeasure_lt_top_iff (hu : PlurisubharmonicOn u Ω)
    (s : Set (ComplexModel n)) :
    truncationLimitMeasure Ω u hu s < ⊤ ↔
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k, truncationMeasure Ω u hu k s ≤ C :=
  increasingLimit_lt_top_iff _ _ s

theorem truncationLimitMeasure_finiteOnCompacts_iff (hu : PlurisubharmonicOn u Ω) :
    (∀ K : Set (ComplexModel n), IsCompact K → K ⊆ Ω →
      truncationLimitMeasure Ω u hu K < ⊤) ↔ HasUniformCompactTruncationMass Ω u hu := by
  constructor
  · intro h K hK hKΩ
    exact (truncationLimitMeasure_lt_top_iff hu K).mp (h K hK hKΩ)
  · intro h K hK hKΩ
    exact (truncationLimitMeasure_lt_top_iff hu K).mpr (h K hK hKΩ)

/-- Ordinary-open locality of the actual finite steps. -/
theorem truncationMeasure_restrict_open {U : Opens (ComplexModel n)} (hU : U ≤ Ω)
    (hu : PlurisubharmonicOn u Ω) (huU : PlurisubharmonicOn u U) (k : ℕ) :
    (truncationMeasure Ω u hu k).restrict (U : Set (ComplexModel n)) =
      truncationMeasure U u huU k := by
  unfold truncationMeasure
  rw [Measure.restrict_restrict U.isOpen.measurableSet]
  rw [← canonicalBedfordTaylorMeasure_restrict hU
    (truncationReal_isLocallyBoundedPshOn hu k)
    (truncationReal_isLocallyBoundedPshOn huU k)]
  have hsub : strictTruncationLocus U u k ⊆ (U : Set (ComplexModel n)) :=
    fun _ hz => hz.1
  rw [Measure.restrict_restrict_of_subset hsub]
  congr 1
  ext z
  simp only [strictTruncationLocus, mem_inter_iff, mem_ofPred_eq]
  exact ⟨fun hz => ⟨hz.1, hz.2.2⟩, fun hz => ⟨hz.1, hU hz.1, hz.2⟩⟩

theorem truncationLimitMeasure_restrict_open {U : Opens (ComplexModel n)} (hU : U ≤ Ω)
    (hu : PlurisubharmonicOn u Ω) (huU : PlurisubharmonicOn u U) :
    (truncationLimitMeasure Ω u hu).restrict (U : Set (ComplexModel n)) =
      truncationLimitMeasure U u huU := by
  change (increasingLimit _ _).restrict (U : Set (ComplexModel n)) = _
  rw [increasingLimit_restrict]
  apply Measure.ext
  intro s _
  calc
    increasingLimit _ _ s = ⨆ k, (truncationMeasure Ω u hu k).restrict
        (U : Set (ComplexModel n)) s := increasingLimit_apply _ _ s
    _ = ⨆ k, truncationMeasure U u huU k s := by
      simp_rw [truncationMeasure_restrict_open hU hu huU]
    _ = truncationLimitMeasure U u huU s := (truncationLimitMeasure_apply huU s).symm

/-- On a real locally bounded PSH potential, the truncation prescription
recovers the original bounded BT measure. No pluripolar noncharging is used. -/
theorem truncationLimitMeasure_eq_canonical {v : ComplexModel n → ℝ}
    (hv : IsLocallyBoundedPshOn Ω v) :
    truncationLimitMeasure Ω (fun z => (v z : EReal)) hv.1 =
      canonicalBedfordTaylorMeasure Ω v hv := by
  symm
  refine truncationLimitMeasure_unique hv.1 (canonicalBedfordTaylorMeasure_compl Ω v hv)
    ?_ ?_
  · simp
  · intro k
    have hmax : EqOn (truncationReal (fun z => (v z : EReal)) k)
        (fun z => max (v z) (-(k : ℝ))) Ω := by
      intro z _
      change (max (v z : EReal) ((-(k : ℝ) : ℝ) : EReal)).toReal =
        max (v z) (-(k : ℝ))
      rcases le_total (v z) (-(k : ℝ)) with hz | hz
      · rw [max_eq_right (EReal.coe_le_coe_iff.mpr hz), max_eq_right hz,
          EReal.toReal_coe]
      · rw [max_eq_left (EReal.coe_le_coe_iff.mpr hz), max_eq_left hz,
          EReal.toReal_coe]
    have hset : strictTruncationLocus Ω (fun z => (v z : EReal)) k =
        {z | z ∈ Ω ∧ -(k : ℝ) < v z} := by
      ext z
      simp only [strictTruncationLocus, mem_ofPred_eq, EReal.coe_lt_coe_iff]
    unfold truncationMeasure
    rw [hset]
    exact (localBedfordTaylorMeasure_max_const_locality
      (canonicalBedfordTaylorMeasure_spec Ω v hv)
      (canonicalBedfordTaylorMeasure_spec Ω _
        (truncationReal_isLocallyBoundedPshOn hv.1 k)) (-(k : ℝ)) hmax).symm

/-- Bounded BT measures do not charge arbitrary locally pluripolar sets.
This follows from the weighted CLN estimate, not Haar nullity. There is no arbitrary background
    current in this assertion. -/
theorem localBedfordTaylorMeasure_doesNotChargePluripolarOn
    {v : ComplexModel n → ℝ} {μ : Measure (ComplexModel n)}
    (hμ : IsLocalBedfordTaylorMeasure Ω v μ) :
    DoesNotChargePluripolarOn μ (Ω : Set (ComplexModel n)) :=
  BedfordTaylor.IsLocalBedfordTaylorMeasure.doesNotChargePluripolarOn hμ

theorem truncationMeasure_doesNotChargePluripolarOn (hu : PlurisubharmonicOn u Ω)
    (k : ℕ) :
    DoesNotChargePluripolarOn (truncationMeasure Ω u hu k) (Ω : Set (ComplexModel n)) := by
  intro s hs
  unfold truncationMeasure
  apply le_antisymm
  · exact (Measure.le_iff'.mp Measure.restrict_le_self _).trans_eq
      (localBedfordTaylorMeasure_doesNotChargePluripolarOn
        (canonicalBedfordTaylorMeasure_spec Ω _
          (truncationReal_isLocallyBoundedPshOn hu k)) s hs)
  · exact bot_le

/-- Noncharging passes to the actual limit without a uniform mass bound. -/
theorem truncationLimitMeasure_doesNotChargePluripolarOn (hu : PlurisubharmonicOn u Ω) :
    DoesNotChargePluripolarOn (truncationLimitMeasure Ω u hu) (Ω : Set (ComplexModel n)) := by
  intro s hs
  exact (truncationLimitMeasure_zero_iff hu _).mpr
    (fun k => truncationMeasure_doesNotChargePluripolarOn hu k s hs)

end SGPT.Foundations.Analysis.Pending.MongeAmpere
