/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorHolomorphic
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.NonPluripolarGauge

/-!
# Holomorphic covariance of the mixed non-pluripolar truncation limit

For a biholomorphism `τ : A → B` with inverse `σ`, the mixed truncation limit of
`v ∘ τ` on `A` is the push-forward under `σ` of the truncation limit of `v` on
`B`. The truncations commute with composition, their bounded products are
covariant, the strict loci correspond, and the pole set is not charged.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.MixedNonPluripolar

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
open FirstPass.MixedNonPluripolar MixedMongeAmpere BedfordTaylor

variable {n : ℕ}

/-- **Holomorphic covariance of the mixed truncation limit.** -/
theorem mixedTruncationLimitMeasure_comp_biholomorphic {A B : Opens (ComplexModel n)}
    {τ σ : ComplexModel n → ComplexModel n} (h : IsBiholomorphicPair A B τ σ)
    {v : Fin n → ComplexModel n → EReal} (hv : ∀ i, PlurisubharmonicOn (v i) B)
    (hvτ : ∀ i, PlurisubharmonicOn (fun x ↦ v i (τ x)) A) :
    mixedTruncationLimitMeasure A (fun i x ↦ v i (τ x)) hvτ =
      ((mixedTruncationLimitMeasure B v hv).restrict B).map σ := by
  classical
  set μ := mixedTruncationLimitMeasure B v hv
  have hσm (ρ : Measure (ComplexModel n)) : AEMeasurable σ (ρ.restrict B) :=
    h.holo_inv.continuousOn.aemeasurable B.isOpen.measurableSet
  have hmap (ρ : Measure (ComplexModel n)) (E : Set (ComplexModel n)) (hE : MeasurableSet E) :
      (ρ.restrict B).map σ E = ρ (σ ⁻¹' E ∩ B) := by
    rw [Measure.map_apply_of_aemeasurable (hσm ρ) hE,
      Measure.restrict_apply' B.isOpen.measurableSet]
  have hpre (k : ℕ) : σ ⁻¹' commonStrictLocus A (fun i x ↦ v i (τ x)) k ∩ B =
      commonStrictLocus B v k := by
    ext w
    constructor
    · rintro ⟨⟨-, hw⟩, hwB⟩
      exact ⟨hwB, fun i ↦ by simpa [h.right_inv w hwB] using hw i⟩
    · rintro ⟨hwB, hw⟩
      exact ⟨⟨h.mapsTo_inv hwB, fun i ↦ by simpa [h.right_inv w hwB] using hw i⟩, hwB⟩
  symm
  refine mixedTruncationLimitMeasure_unique hvτ ?_ ?_ fun k ↦ ?_
  · rw [hmap μ _ A.isOpen.measurableSet.compl]
    have : σ ⁻¹' (A : Set (ComplexModel n))ᶜ ∩ B = ∅ :=
      eq_empty_of_forall_notMem fun w hw ↦ hw.1 (h.mapsTo_inv hw.2)
    rw [this, measure_empty]
  · set M := (⋃ k, commonStrictLocus A (fun i x ↦ v i (τ x)) k)ᶜ
    have hM : MeasurableSet M :=
      (MeasurableSet.iUnion fun k ↦ measurableSet_commonStrictLocus hvτ k).compl
    have hPM : componentPoleSet (fun i x ↦ v i (τ x)) ⊆ M := by
      intro z hz
      simp only [M, compl_iUnion_commonStrictLocus]
      exact Or.inr hz
    refine measure_mono_null hPM ?_
    rw [hmap μ M hM]
    refine measure_mono_null (fun w hw ↦ ?_) (mixedTruncationLimitMeasure_poleSet hv)
    obtain ⟨hwM, hwB⟩ := hw
    change σ w ∉ ⋃ k, commonStrictLocus A (fun i x ↦ v i (τ x)) k at hwM
    rw [iUnion_commonStrictLocus] at hwM
    simp only [mem_ofPred_eq, not_and, not_forall, not_not] at hwM
    obtain ⟨i, hi⟩ := hwM (h.mapsTo_inv hwB)
    exact ⟨i, by simpa [h.right_inv w hwB] using hi⟩
  -- the bounded products of the truncations
  set a := mixedTruncationReal v k
  have hcanonB := canonicalMixedBedfordTaylorMeasure_spec B a
    (mixedTruncationReal_isLocallyBounded hv k)
  have hcanonA := canonicalMixedBedfordTaylorMeasure_spec A (mixedTruncationReal (fun i x ↦ v i (τ
    x)) k)
    (mixedTruncationReal_isLocallyBounded hvτ k)
  have hcov := (IsLocalMixedBedfordTaylorMeasure.isBTLimit hcanonB).comp_biholomorphic h
  have hAeq := (IsLocalMixedBedfordTaylorMeasure.isBTLimit hcanonA).unique hcov
  change ((μ.restrict B).map σ).restrict (commonStrictLocus A _ k) =
    (canonicalMixedBedfordTaylorMeasure A _ _).restrict (commonStrictLocus A _ k)
  rw [hAeq]
  have hLm := measurableSet_commonStrictLocus hvτ k
  rw [Measure.restrict_map_of_aemeasurable (hσm _) hLm,
    Measure.restrict_map_of_aemeasurable (hσm _) hLm,
    Measure.restrict_restrict' B.isOpen.measurableSet,
    Measure.restrict_restrict' B.isOpen.measurableSet, hpre,
    mixedTruncationLimitMeasure_restrict_commonStrictLocus hv k]
  rfl

end SGPT.Foundations.Analysis.Pending.MixedNonPluripolar
