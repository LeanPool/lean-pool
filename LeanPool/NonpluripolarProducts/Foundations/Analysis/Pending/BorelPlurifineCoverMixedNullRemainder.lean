/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BorelPlurifineOpenCountableNormalizedSuperlevelCover
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MixedMongeAmpere

/-!
# A countable plurifine cover with a universally mixed-null remainder

The original Borel fine-open set chooses a single normalized cover before
the original locally bounded mixed tuple is specified. Compact exhaustion
and capacity domination prove that every such tuple gives its remainder
zero measure on the original domain.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.BorelPlurifineCoverMixedNullRemainder

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor

variable {n : ℕ}

private theorem canonicalMixed_eq_zero_of_all_subdomain_capacity
    {Ω : Opens (ComplexModel n)} {E : Set (ComplexModel n)}
    (hEΩ : E ⊆ (Ω : Set (ComplexModel n)))
    (hcap : ∀ D : Opens (ComplexModel n), D ≤ Ω →
      relCapacity D (E ∩ (D : Set (ComplexModel n))) = 0)
    {u : Fin n → ComplexModel n → ℝ} (hu : IsLocallyBoundedMixedPshOn Ω u) :
    MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure Ω u hu E = 0 := by
  classical
  let μ := MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure Ω u hu
  have hμ : IsBTLimit Ω u μ :=
    IsLocalMixedBedfordTaylorMeasure.isBTLimit
      (MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure_spec Ω u hu)
  obtain ⟨U, -, hUrc, hUabs⟩ := exists_exhaustion Ω
  have hUΩ (m : ℕ) : U m ≤ Ω := subset_closure.trans (hUrc m).2
  have hnull (m : ℕ) : μ (E ∩ (U m : Set (ComplexModel n))) = 0 := by
    choose C hC using fun i : Fin n ↦
      BedfordTaylor.IsLocallyBoundedPshOn.exists_abs_le (hu i) (hUrc m).1 (hUrc m).2
    let M : ℝ := 1 + ∑ i : Fin n, |C i|
    have hsum : 0 ≤ ∑ i : Fin n, |C i| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    have hM : 0 < M := by dsimp only [M]; linarith
    have hbound (i : Fin n) (z : ComplexModel n) (hz : z ∈ U m) : |u i z| ≤ M := by
      have hi : |C i| ≤ ∑ j : Fin n, |C j| :=
        Finset.single_le_sum (f := fun j : Fin n ↦ |C j|)
          (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ i)
      calc
        |u i z| ≤ C i := hC i z (subset_closure hz)
        _ ≤ |C i| := le_abs_self _
        _ ≤ ∑ j : Fin n, |C j| := hi
        _ ≤ M := by dsimp only [M]; linarith
    have hle := hμ.le_relCapacity_of_abs_le hu (hUΩ m) hM hbound
      (E := E ∩ (U m : Set (ComplexModel n))) inter_subset_right
    rw [hcap (U m) (hUΩ m), mul_zero] at hle
    exact le_antisymm hle bot_le
  have hcover : E ⊆ ⋃ m, E ∩ (U m : Set (ComplexModel n)) := by
    intro x hx
    obtain ⟨m, hm⟩ := hUabs {x} isCompact_singleton
      (singleton_subset_iff.mpr (hEΩ hx))
    exact mem_iUnion.mpr ⟨m, hx, hm (mem_singleton x)⟩
  have hzero : μ (⋃ m, E ∩ (U m : Set (ComplexModel n))) = 0 :=
    measure_iUnion_null hnull
  exact le_antisymm ((measure_mono hcover).trans_eq hzero) bot_le

/-- The original set chooses a single cover whose remainder is null for
every original locally bounded mixed PSH tuple. -/
theorem exists_countable_normalized_cover_mixed_null
    {Ω : Opens (ComplexModel n)} {F : Set (ComplexModel n)}
    (hFΩ : F ⊆ (Ω : Set (ComplexModel n))) (hFBorel : MeasurableSet F)
    (hFine : IsOpen[PlurifinePshTopology.topology Ω] (Subtype.val ⁻¹' F)) :
    ∃ (B : ℕ → Opens (ComplexModel n)) (g : ℕ → ℕ → ComplexModel n → ℝ),
      (∀ j, B j ≤ Ω) ∧
      (∀ j k, PlurisubharmonicOn (fun x ↦ (g j k x : EReal)) Ω) ∧
      (∀ j, ∀ x ∈ Ω, Monotone (fun k ↦ g j k x)) ∧
      (∀ j k x, x ∈ B j → -1 ≤ g j k x ∧ g j k x ≤ 1) ∧
      (∀ j k, {x | x ∈ B j ∧ 0 < g j k x} ⊆ F ∧
        MeasurableSet {x | x ∈ B j ∧ 0 < g j k x} ∧
        IsOpen[PlurifinePshTopology.topology Ω]
          (Subtype.val ⁻¹' {x | x ∈ B j ∧ 0 < g j k x})) ∧
      MeasurableSet (F \ ⋃ j, ⋃ k, {x | x ∈ B j ∧ 0 < g j k x}) ∧
      (∀ (D : Opens (ComplexModel n)), D ≤ Ω →
        relCapacity D ((F \ ⋃ j, ⋃ k, {x | x ∈ B j ∧ 0 < g j k x}) ∩
          (D : Set (ComplexModel n))) = 0) ∧
      ∀ (u : Fin n → ComplexModel n → ℝ) (hu : IsLocallyBoundedMixedPshOn Ω u),
        MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure Ω u hu
          (F \ ⋃ j, ⋃ k, {x | x ∈ B j ∧ 0 < g j k x}) = 0 := by
  obtain ⟨B, g, hBΩ, hg, hmono, hbounds, hG, hE, hcap⟩ :=
    BorelPlurifineOpenCountableNormalizedSuperlevelCover.exists_countable_normalized_cover
      hFΩ hFBorel hFine
  refine ⟨B, g, hBΩ, hg, hmono, hbounds, hG, hE, hcap, ?_⟩
  intro u hu
  exact canonicalMixed_eq_zero_of_all_subdomain_capacity (sdiff_subset.trans hFΩ) hcap hu

end SGPT.Foundations.Analysis.Pending.BorelPlurifineCoverMixedNullRemainder
