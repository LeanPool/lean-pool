/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.NegligibleSetNotCharged
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorExistence

/-!
# Relative capacity zero for a genuine increasing PSH gap

Compact exhaustion and positive reciprocal gaps extend the local weighted
increasing theorem to the actual full gap. Every normalized diagonal
competitor is treated internally, including on smaller ordinary domains.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.IncreasingPshGapCapacityZero

open FirstPass FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.NegligibleSetNotCharged

variable {n : ℕ}

/-- Every original canonical diagonal measure gives zero mass to the full
positive gap of a genuine increasing approximation on an arbitrary open domain. -/
theorem canonical_measure_gap_eq_zero {D : Opens (ComplexModel n)}
    {w V : ComplexModel n → ℝ} (hw : IsLocallyBoundedPshOn D w)
    (hV : IsLocallyBoundedPshOn D V) {v : ℕ → ComplexModel n → ℝ}
    (hv : IsIncApprox D V v) :
    Pending.MongeAmpere.canonicalBedfordTaylorMeasure D w hw
      {z | z ∈ D ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ k, v k z + δ ≤ V z} = 0 := by
  classical
  let μ := Pending.MongeAmpere.canonicalBedfordTaylorMeasure D w hw
  have hμ : IsBTLimit D (fun _ ↦ w) μ := isBTLimit_canonicalBedfordTaylorMeasure hw
  obtain ⟨U, _hUmono, hUrc, hUabs⟩ := exists_exhaustion D
  have hzero : ∀ j m : ℕ, μ
      (closure (U j : Set (ComplexModel n)) ∩
        {z | ∀ k, v k z + 1 / ((m : ℝ) + 1) ≤ V z}) = 0 :=
    fun j m ↦ measure_inter_gap_eq_zero hw hμ hV hv
      (hUrc j).1 (hUrc j).2 (by positivity)
  refine measure_mono_null ?_ (measure_iUnion_null fun j ↦ measure_iUnion_null (hzero j))
  rintro z ⟨hz, δ, hδ, hgap⟩
  obtain ⟨j, hj⟩ := hUabs {z} isCompact_singleton (singleton_subset_iff.mpr hz)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  refine mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨m, ?_, ?_⟩⟩
  · exact subset_closure (hj (by simp))
  · intro k
    linarith [hgap k]

/-- Literal relative capacity vanishes for the actual increasing gap on every
ordinary smaller domain, with no comparison of different ambient capacities. -/
theorem relCapacity_gap_eq_zero_of_le {D O : Opens (ComplexModel n)} (hOD : O ≤ D)
    {V : ComplexModel n → ℝ} (hV : IsLocallyBoundedPshOn D V)
    {v : ℕ → ComplexModel n → ℝ} (hv : IsIncApprox D V v) :
    relCapacity O {z | z ∈ O ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ k, v k z + δ ≤ V z} = 0 := by
  refine le_antisymm (relCapacity_le_of_forall fun w hw _hb ↦ ?_) bot_le
  exact le_of_eq (canonical_measure_gap_eq_zero hw
    (IsLocallyBoundedPshOn.mono_opens hV hOD) (hv.mono_opens hOD))

end SGPT.Foundations.Analysis.Pending.IncreasingPshGapCapacityZero
