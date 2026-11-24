/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BorelPlurifineCoverMixedNullRemainder
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BoundedBasicPlurifineLocality

/-!
# Canonical mixed locality on the original Borel plurifine set

The original set internally chooses a countable normalized superlevel cover.
Local restriction equalities and the universally mixed-null remainder give
the equality of both original canonical mixed measures on that same set.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.BorelPlurifineCanonicalMixedLocality

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor

variable {n : ℕ}

/-- Locality on the original Borel fine-open set for both original mixed tuples. -/
theorem canonicalMixed_restrict_eq_on_borel_plurifine_open
    {Ω : Opens (ComplexModel n)} {F : Set (ComplexModel n)}
    {a b : Fin n → ComplexModel n → ℝ}
    (ha : IsLocallyBoundedMixedPshOn Ω a) (hb : IsLocallyBoundedMixedPshOn Ω b)
    (hFΩ : F ⊆ (Ω : Set (ComplexModel n))) (hFBorel : MeasurableSet F)
    (hFine : IsOpen[PlurifinePshTopology.topology Ω] (Subtype.val ⁻¹' F))
    (heq : ∀ i, EqOn (a i) (b i) F) :
    (MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure Ω a ha).restrict F =
    (MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure Ω b hb).restrict F := by
  classical
  obtain ⟨B, g, hBΩ, hg, -, hbounds, hG, -, -, hnull⟩ :=
    BorelPlurifineCoverMixedNullRemainder.exists_countable_normalized_cover_mixed_null
      hFΩ hFBorel hFine
  let G (j k : ℕ) := {x | x ∈ B j ∧ 0 < g j k x}
  let P := ⋃ j, ⋃ k, G j k
  let E := F \ P
  let μa := MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure Ω a ha
  let μb := MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure Ω b hb
  have hlocal (j k : ℕ) : μa.restrict (G j k) = μb.restrict (G j k) := by
    exact BoundedBasicPlurifineLocality.canonicalMixed_restrict_eq_on_normalized_psh_superlevel
      (hBΩ j) ha hb ((hg j k).mono (hBΩ j)) (hbounds j k)
      (fun i ↦ (heq i).mono (hG j k).1)
  have hP : μa.restrict P = μb.restrict P :=
    Measure.restrict_iUnion_congr.mpr fun j ↦
      Measure.restrict_iUnion_congr.mpr fun k ↦ hlocal j k
  have hEa : μa.restrict E = 0 := Measure.restrict_eq_zero.mpr (hnull a ha)
  have hEb : μb.restrict E = 0 := Measure.restrict_eq_zero.mpr (hnull b hb)
  have hPF : P ⊆ F := iUnion_subset fun j ↦ iUnion_subset fun k ↦ (hG j k).1
  have hFE : F = P ∪ E := by
    ext x
    constructor
    · intro hx
      by_cases hp : x ∈ P
      · exact Or.inl hp
      · exact Or.inr ⟨hx, hp⟩
    · rintro (hp | he)
      · exact hPF hp
      · exact he.1
  change μa.restrict F = μb.restrict F
  rw [hFE]
  exact Measure.restrict_union_congr.mpr ⟨hP, hEa.trans hEb.symm⟩

end SGPT.Foundations.Analysis.Pending.BorelPlurifineCanonicalMixedLocality
