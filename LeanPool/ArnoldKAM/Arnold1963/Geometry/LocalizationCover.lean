/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.HamiltonianLocalization
public import Mathlib.MeasureTheory.Measure.Regular

/-!
Finite local coverage from the original nondegenerate Hamiltonian data. Loss is measured
relative to the original action volume; the covering patches may overlap.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace KamProject.Arnold1963

/-- The unperturbed Hamiltonian and explicit compact-domain hypotheses for the global theorem. -/
structure GlobalHamiltonianData (n : ℕ) (H₀ : ComplexSpace n → ℂ)
    (ambient : Set (ComplexSpace n)) : Type where
  dimension_pos : 0 < n
  compact : IsCompact ambient
  domain_conj : ConjInvariant ambient
  analytic : AnalyticOnNhd ℂ H₀ ambient
  conj : ∀ p ∈ ambient, H₀ (conjVec p) = star (H₀ p)
  /-- The nonempty open real action set whose closure is the ambient domain's real slice. -/
  realOpen : Set (RealSpace n)
  isOpen_realOpen : IsOpen realOpen
  nonempty_realOpen : realOpen.Nonempty
  closure_realOpen : closure realOpen = realSlice ambient
  boundary_null : volume (frontier realOpen) = 0
  complex_interior : ∀ p ∈ realOpen, complexify p ∈ interior ambient
  nondegenerate : ∀ p ∈ realOpen, hessianDet H₀ (complexify p) ≠ 0

namespace GlobalHamiltonianData
variable {n : ℕ} {H₀ : ComplexSpace n → ℂ} {ambient : Set (ComplexSpace n)}
  (h : GlobalHamiltonianData n H₀ ambient)
include h

theorem realOpen_subset : h.realOpen ⊆ realSlice ambient :=
  h.closure_realOpen ▸ subset_closure

theorem volume_finite : volume (realSlice ambient) ≠ ⊤ :=
  (isCompact_realSlice h.compact).measure_ne_top

theorem volume_pos : 0 < volume (realSlice ambient) :=
  (h.isOpen_realOpen.measure_pos volume h.nonempty_realOpen).trans_le
    (measure_mono h.realOpen_subset)

theorem real_boundary_null : volume (realSlice ambient \ h.realOpen) = 0 := by
  simpa only [frontier, h.isOpen_realOpen.interior_eq, h.closure_realOpen] using h.boundary_null

theorem exists_cover (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset (HamiltonianPatch n H₀ ambient),
      volume (realSlice ambient \ ⋃ c ∈ s, realSlice c.domain) <
        ENNReal.ofReal ε * volume (realSlice ambient) := by
  have hεV : ENNReal.ofReal ε * volume (realSlice ambient) ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr hε).ne' h.volume_pos.ne'
  obtain ⟨K, hKU, hK, hVK⟩ := h.isOpen_realOpen.measurableSet.exists_isCompact_sdiff_lt
    (ne_top_of_le_ne_top h.volume_finite (measure_mono h.realOpen_subset)) hεV
  obtain ⟨s, hs⟩ := HamiltonianPatch.exists_finite_cover hK
    (fun p hp => h.complex_interior p (hKU hp)) h.analytic h.conj
    (fun p hp => h.nondegenerate p (hKU hp))
  refine ⟨s, lt_of_le_of_lt ?_ hVK⟩
  calc
    volume (realSlice ambient \ ⋃ c ∈ s, realSlice c.domain) ≤
        volume ((realSlice ambient \ h.realOpen) ∪ (h.realOpen \ K)) := measure_mono (by
      intro p hp
      by_cases hpU : p ∈ h.realOpen
      · refine Or.inr ⟨hpU, ?_⟩
        intro hpK
        obtain ⟨c, hc, hpc⟩ := mem_iUnion₂.mp (hs hpK)
        exact hp.2 (mem_iUnion₂.mpr ⟨c, hc,
          (show complexify p ∈ c.domain from interior_subset hpc)⟩)
      · exact Or.inl ⟨hp.1, hpU⟩)
    _ ≤ volume (realSlice ambient \ h.realOpen) + volume (h.realOpen \ K) := measure_union_le _ _
    _ = volume (h.realOpen \ K) := by rw [h.real_boundary_null, zero_add]

end GlobalHamiltonianData
end KamProject.Arnold1963
