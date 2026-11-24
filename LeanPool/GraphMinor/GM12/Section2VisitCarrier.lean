/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM12.Section2CirclePeriod
import LeanPool.GraphMinor.GM12.Section2IntervalCoverage
import LeanPool.GraphMinor.GM11.Regions

/-!
# The set used by the trace deformation

For Case 1 of XII (2.1), page 244, the deformation stays in the
visited regions together with the original drawing vertices. The
parameter subdivision covers the original curve by those pieces.
Its union meets the drawing only at those original vertices, and
any region met by this union is one of the listed regions. These
are precisely the controls needed by the selected-inside comparison.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- Choose the union of visited regions and original vertex images,
retaining its coverage and its drawing-atom controls. -/
theorem exists_region_visit_carrier
    {S : Type*} [TopologicalSpace S] {Γ : Drawing S} {φ : C(Circle, S)}
    {n : ℕ} (t : Fin (n + 1) → ℝ) (hperiod : t (Fin.last n) = t 0 + 1)
    (hΓ : ∀ i, periodicCurve φ (t i) ∈ Γ.V)
    (r : Fin n → Set S) (hr : ∀ i, r i ∈ Γ.R)
    (hfr : ∀ i s, s ∈ Ioo (t i.castSucc) (t i.succ) → periodicCurve φ s ∈ r i) :
    ∃ Z : Set S, range φ ⊆ Z ∧ (∀ i, r i ⊆ Z) ∧
      Z ∩ Γ.U ⊆ range φ ∩ Γ.V ∧
      ∀ R ∈ Γ.R, (Z ∩ R).Nonempty → ∃ i, R = r i := by
  let Z := (range φ ∩ Γ.V) ∪ ⋃ i, r i
  have hφZ : range φ ⊆ Z := by
    rintro x ⟨z, rfl⟩
    obtain ⟨s, hs, hsz⟩ := (circle_parameter_bijOn (t 0)).surjOn (mem_univ z)
    have heq : periodicCurve φ s = φ z := congrArg φ hsz
    rw [← heq]
    have hs' : s ∈ Icc (t 0) (t (Fin.last n)) := ⟨hs.1, hperiod.symm ▸ hs.2.le⟩
    rcases mem_range_or_mem_successive_open_interval t hs' with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact Or.inl ⟨mem_range_self _, hi ▸ hΓ i⟩
    · exact Or.inr (mem_iUnion.mpr ⟨i, hfr i s hi⟩)
  refine ⟨Z, hφZ, fun i x hx => Or.inr (mem_iUnion.mpr ⟨i, hx⟩), ?_, ?_⟩
  · rintro x ⟨(hx | hx), hxΓ⟩
    · exact hx
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact (region_subset (hr i) hi hxΓ).elim
  · intro R hR hmeet
    obtain ⟨x, hxZ, hxR⟩ := hmeet
    rcases hxZ with hx | hx
    · exact (region_subset hR hxR (Γ.V_subset_U hx.2)).elim
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      exact ⟨i, region_eq_of_mem hR (hr i) hxR hxi⟩

end GraphMinor.GM12
