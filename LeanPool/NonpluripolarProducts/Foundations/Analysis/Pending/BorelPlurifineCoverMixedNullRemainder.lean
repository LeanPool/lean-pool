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

A compact exhaustion and capacity domination turn capacity-zero remainders
into null sets for locally bounded mixed Bedford–Taylor measures.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.BorelPlurifineCoverMixedNullRemainder

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor

variable {n : ℕ}

/-- Capacity zero on every subdomain forces a mixed Bedford–Taylor measure to vanish. -/
theorem canonicalMixed_eq_zero_of_all_subdomain_capacity
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

end SGPT.Foundations.Analysis.Pending.BorelPlurifineCoverMixedNullRemainder
