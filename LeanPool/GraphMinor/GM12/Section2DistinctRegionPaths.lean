/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2CyclicEmbedding
public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM11.Regions

/-!
# Distinct region visits give a simple cyclic curve

In Case 1 of XII (2.1), page 244, the original vertex visits are
distinct and the successive region visits are distinct. A two-spoke
path has its endpoints at those vertices and its other points in
its region. Two half-open paths can therefore meet only when their
region labels agree, or when both parameters are their common
initial vertex. Injectivity within each path completes the argument.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM07

/-- Paths with distinct initial drawing vertices and distinct region
interiors have disjoint half-open images, provided each half-open path is
injective. This is the simplicity test in XII (2.1), Case 1. -/
theorem halfopen_separation_of_distinct_regions
    {S : Type*} [TopologicalSpace S] {Γ : Drawing S} {ι : Type*}
    {v : ι → S} (hv : ∀ i, v i ∈ Γ.V) (hvi : Function.Injective v)
    {r : ι → Set S} (hr : ∀ i, r i ∈ Γ.R) (hri : Function.Injective r)
    (γ : ι → C(unitInterval, S)) (hγi : ∀ i, InjOn (γ i) (Ico (0 : unitInterval) 1))
    (hγ0 : ∀ i, γ i 0 = v i)
    (hγr : ∀ i t, 0 < t.val → t.val < 1 → γ i t ∈ r i) :
    ∀ (i j : ι) (s t : unitInterval), s.val < 1 → t.val < 1 →
      γ i s = γ j t → i = j ∧ s = t := by
  intro i j s t hs ht heq
  have hij : i = j := by
    by_cases hs0 : s = 0
    · by_cases ht0 : t = 0
      · rw [hs0, ht0, hγ0 i, hγ0 j] at heq
        exact hvi heq
      · rw [hs0, hγ0 i] at heq
        have htpos : 0 < t.val := unitInterval.pos_iff_ne_zero.mpr ht0
        exact (region_subset (hr j) (hγr j t htpos ht)
          (heq ▸ Γ.V_subset_U (hv i))).elim
    · have hspos : 0 < s.val := unitInterval.pos_iff_ne_zero.mpr hs0
      by_cases ht0 : t = 0
      · rw [ht0, hγ0 j] at heq
        exact (region_subset (hr i) (hγr i s hspos hs)
          (heq.symm ▸ Γ.V_subset_U (hv j))).elim
      · have htpos : 0 < t.val := unitInterval.pos_iff_ne_zero.mpr ht0
        exact hri (region_eq_of_mem (hr i) (hr j) (hγr i s hspos hs)
          (heq.symm ▸ hγr j t htpos ht))
  subst j
  exact ⟨rfl, hγi i ⟨s.property.1, hs⟩ ⟨t.property.1, ht⟩ heq⟩

/-- Cyclic paths in distinct regions assemble to an embedded circle
when their drawing vertices are distinct and each half-open path is injective. -/
theorem concatLoop_isEmbedding_of_distinct_regions
    {S : Type*} [TopologicalSpace S] [T2Space S] {Γ : Drawing S}
    {n : ℕ} (hn : 0 < n)
    {v : Fin n → S} (hv : ∀ i, v i ∈ Γ.V) (hvi : Function.Injective v)
    {r : Fin n → Set S} (hr : ∀ i, r i ∈ Γ.R) (hri : Function.Injective r)
    (γ : Fin n → C(unitInterval, S)) (hγi : ∀ i, InjOn (γ i) (Ico (0 : unitInterval) 1))
    (hγ0 : ∀ i, γ i 0 = v i)
    (hγr : ∀ i t, 0 < t.val → t.val < 1 → γ i t ∈ r i)
    (hmatch : ∀ i : Fin n, γ i 1 = γ (finNext hn i) 0) :
    IsEmbedding (concatLoop hn γ hmatch) := by
  have hinj := concatLoop_injective_of_halfopen_pieces hn γ hmatch
    (halfopen_separation_of_distinct_regions hv hvi hr hri γ hγi hγ0 hγr)
  exact (concatLoop hn γ hmatch).continuous.isClosedEmbedding hinj |>.isEmbedding

end GraphMinor.GM12
