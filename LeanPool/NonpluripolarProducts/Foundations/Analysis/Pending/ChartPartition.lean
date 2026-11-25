/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GlobalPotentials
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HolomorphicMaps
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.SmoothTestCutoff

/-!
# Chart-supported smooth functions and partitions of unity on a complex manifold

A smooth function on a chart target whose support is a compact subset of that
target extends by zero to a function on the manifold that is smooth read in
*every* atlas chart: on the overlap it is the composition with the holomorphic
chart transition, and away from the (compact, hence closed) transported support
it vanishes identically.

Compactness of the manifold then produces a finite family of such functions
summing to one and subordinate to any given open cover. This is the missing
global ingredient for integration-by-parts arguments on `M`, which are otherwise
only available on chart targets.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.ChartPartition

open FirstPass FirstPass.HolomorphicMaps

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A function on a chart target, extended by zero to the whole manifold. -/
def chartExtend (e : ComplexChart n M) (β : ComplexModel n → ℝ) : M → ℝ :=
  (e.val.source).indicator fun x ↦ β (e.val x)

omit [IsComplexManifold n M] in
theorem chartExtend_of_mem {e : ComplexChart n M} {β : ComplexModel n → ℝ} {x : M}
    (hx : x ∈ e.val.source) : chartExtend e β x = β (e.val x) :=
  indicator_of_mem hx _

omit [IsComplexManifold n M] in
theorem chartExtend_of_notMem {e : ComplexChart n M} {β : ComplexModel n → ℝ} {x : M}
    (hx : x ∉ e.val.source) : chartExtend e β x = 0 :=
  indicator_of_notMem hx _

omit [IsComplexManifold n M] in
theorem chartExtend_nonneg {e : ComplexChart n M} {β : ComplexModel n → ℝ}
    (hβ : ∀ z, 0 ≤ β z) (x : M) : 0 ≤ chartExtend e β x := by
  by_cases hx : x ∈ e.val.source
  · rw [chartExtend_of_mem hx]; exact hβ _
  · rw [chartExtend_of_notMem hx]

omit [IsComplexManifold n M] in
theorem chartExtend_le_one {e : ComplexChart n M} {β : ComplexModel n → ℝ}
    (hβ : ∀ z, β z ≤ 1) (x : M) : chartExtend e β x ≤ 1 := by
  by_cases hx : x ∈ e.val.source
  · rw [chartExtend_of_mem hx]; exact hβ _
  · rw [chartExtend_of_notMem hx]; norm_num

omit [IsComplexManifold n M] in
/-- The transported support: the image of `tsupport β` under the inverse chart. -/
theorem chartExtend_eq_zero_of_notMem_image {e : ComplexChart n M} {β : ComplexModel n → ℝ}
    {x : M} (hx : x ∉ e.val.symm '' tsupport β) : chartExtend e β x = 0 := by
  by_cases hxs : x ∈ e.val.source
  · rw [chartExtend_of_mem hxs]
    by_contra hne
    exact hx ⟨e.val x, subset_tsupport _ hne, e.val.left_inv hxs⟩
  · exact chartExtend_of_notMem hxs

omit [IsComplexManifold n M] in
theorem support_chartExtend_subset (e : ComplexChart n M) {β : ComplexModel n → ℝ} :
    tsupport (chartExtend e β) ⊆ closure (e.val.symm '' tsupport β) :=
  closure_mono fun x hx ↦ by
    by_contra hmem
    exact hx (chartExtend_eq_zero_of_notMem_image hmem)

/-- **Chart-supported smoothness.** A smooth function with compact support inside
a chart target extends by zero to a function that is smooth in every chart. -/
theorem chartSmooth_chartExtend (e : ComplexChart n M) {β : ComplexModel n → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hβc : IsCompact (tsupport β)) (hβt : tsupport β ⊆ e.val.target) :
    ChartSmooth (n := n) (chartExtend e β) := by
  intro f
  set K : Set M := e.val.symm '' tsupport β with hK_def
  have hKc : IsCompact K := hβc.image_of_continuousOn (e.val.symm.continuousOn.mono hβt)
  have hKs : K ⊆ e.val.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.val.map_target (hβt hz)
  have hKcl : IsClosed K := hKc.isClosed
  refine contDiffOn_of_locally_contDiffOn fun z hz ↦ ?_
  by_cases hzK : f.val.symm z ∈ K
  · refine ⟨(f.val.target ∩ f.val.symm ⁻¹' e.val.source), ?_, ⟨hz, hKs hzK⟩, ?_⟩
    · simpa using f.val.symm.isOpen_inter_preimage e.val.open_source
    · have hsub : (f.val.target ∩ (f.val.target ∩ f.val.symm ⁻¹' e.val.source)) ⊆
          (chartTransition f e).source := by
        rintro y ⟨-, hy⟩
        exact hy
      refine ContDiffOn.congr (f := fun y ↦ β (chartTransition f e y)) ?_ ?_
      · intro y hy
        exact ((hβ.contDiffAt.comp y
          (chartTransition_contDiffAt_real f e (hsub hy))).contDiffWithinAt)
      · intro y hy
        have hys : f.val.symm y ∈ e.val.source := hy.2.2
        rw [chartExtend_of_mem hys]
        rfl
  · refine ⟨(f.val.target ∩ f.val.symm ⁻¹' Kᶜ), ?_, ⟨hz, hzK⟩, ?_⟩
    · simpa using f.val.symm.isOpen_inter_preimage hKcl.isOpen_compl
    · refine ContDiffOn.congr (f := fun _ ↦ (0 : ℝ)) contDiffOn_const ?_
      intro y hy
      exact chartExtend_eq_zero_of_notMem_image hy.2.2

/-- **Chart-smooth bumps.** Every point of an open set carries a chart-smooth
function with values in `[0,1]`, equal to one near the point and with compact
support inside the open set. -/
theorem exists_chartSmooth_bump (x : M) (S : Opens M) (hxS : x ∈ S) :
    ∃ h : M → ℝ, ChartSmooth (n := n) h ∧ (∀ y, 0 ≤ h y) ∧ (∀ y, h y ≤ 1) ∧
      tsupport h ⊆ (S : Set M) ∧ IsCompact (tsupport h) ∧ ∀ᶠ y in 𝓝 x, h y = 1 := by
  classical
  set e : ComplexChart n M := complexChartAt (n := n) x with he_def
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  set T : Opens (ComplexModel n) :=
    ⟨e.val.target ∩ e.val.symm ⁻¹' (S : Set M), by
      simpa using e.val.symm.isOpen_inter_preimage S.isOpen⟩ with hT_def
  have hzT : e.val x ∈ T := by
    refine ⟨e.val.map_source hx, ?_⟩
    change e.val.symm (e.val x) ∈ (S : Set M)
    rw [e.val.left_inv hx]
    exact hxS
  obtain ⟨β, hβ1, hβrange⟩ := exists_testFunction_eq_one_nhds_compact
    (K := ({e.val x} : Set (ComplexModel n))) isCompact_singleton
    (singleton_subset_iff.2 hzT)
  have hβt : tsupport (β : ComplexModel n → ℝ) ⊆ (T : Set (ComplexModel n)) := β.tsupport_subset
  have hβtar : tsupport (β : ComplexModel n → ℝ) ⊆ e.val.target :=
    hβt.trans fun _ hw ↦ hw.1
  have hβc : IsCompact (tsupport (β : ComplexModel n → ℝ)) := β.hasCompactSupport
  refine ⟨chartExtend e β, chartSmooth_chartExtend e β.contDiff hβc hβtar,
    chartExtend_nonneg (fun z ↦ (hβrange z).1),
    chartExtend_le_one (fun z ↦ (hβrange z).2), ?_, ?_, ?_⟩
  · have hKS : e.val.symm '' tsupport (β : ComplexModel n → ℝ) ⊆ (S : Set M) := by
      rintro _ ⟨w, hw, rfl⟩
      exact (hβt hw).2
    have hKc : IsCompact (e.val.symm '' tsupport (β : ComplexModel n → ℝ)) :=
      hβc.image_of_continuousOn (e.val.symm.continuousOn.mono hβtar)
    exact (support_chartExtend_subset e).trans (by rw [hKc.isClosed.closure_eq]; exact hKS)
  · have hKc : IsCompact (e.val.symm '' tsupport (β : ComplexModel n → ℝ)) :=
      hβc.image_of_continuousOn (e.val.symm.continuousOn.mono hβtar)
    refine hKc.of_isClosed_subset (isClosed_tsupport _) ?_
    exact (support_chartExtend_subset e).trans (by rw [hKc.isClosed.closure_eq])
  · have hcont : ContinuousAt e.val x :=
      e.val.continuousOn.continuousAt (e.val.open_source.mem_nhds hx)
    rw [nhdsSet_singleton] at hβ1
    filter_upwards [hcont.eventually hβ1, e.val.open_source.mem_nhds hx] with y hy hys
    rw [chartExtend_of_mem hys]
    exact hy

/-- **Chart-smooth partition of unity.** On a compact complex manifold every open
cover admits a finite subordinate family of nonnegative chart-smooth functions
summing to one. -/
theorem exists_chartSmooth_partitionOfUnity [CompactSpace M] {ι : Type*} (S : ι → Opens M)
    (hcover : ∀ x : M, ∃ i, x ∈ S i) :
    ∃ (m : ℕ) (χ : Fin m → M → ℝ) (idx : Fin m → ι),
      (∀ a, ChartSmooth (n := n) (χ a)) ∧ (∀ a y, 0 ≤ χ a y) ∧
        (∀ a, tsupport (χ a) ⊆ (S (idx a) : Set M)) ∧
        (∀ a, IsCompact (tsupport (χ a))) ∧ ∀ y, ∑ a, χ a y = 1 := by
  classical
  -- a bump at every point, subordinate to some member of the cover
  choose i hi using hcover
  choose h hsm hnonneg hle hsupp hcpt hone using fun x : M ↦
    exists_chartSmooth_bump (n := n) x (S (i x)) (hi x)
  set N : M → Set M := fun x ↦ interior {z | h x z = 1} with hN_def
  have hNopen (x : M) : IsOpen (N x) := isOpen_interior
  have hxN (x : M) : x ∈ N x := mem_interior_iff_mem_nhds.2 (hone x)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover N hNopen
    (fun x _ ↦ mem_iUnion.2 ⟨x, hxN x⟩)
  -- the finite family and its sum
  set m := s.card with hm_def
  set pt : Fin m → M := fun a ↦ (s.equivFin.symm a).val with hpt_def
  set D : M → ℝ := fun y ↦ ∑ a : Fin m, h (pt a) y with hD_def
  have hD1 (y : M) : 1 ≤ D y := by
    obtain ⟨x, hx⟩ := mem_iUnion.mp (hs (mem_univ y))
    obtain ⟨hxs, hy⟩ := mem_iUnion.mp hx
    have hy' : y ∈ {z : M | h x z = 1} := interior_subset hy
    have hy1 : h x y = 1 := hy'
    have hmem : (s.equivFin ⟨x, hxs⟩) ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ _
    have hxpt : pt (s.equivFin ⟨x, hxs⟩) = x := by
      simp [hpt_def]
    calc (1 : ℝ) = h (pt (s.equivFin ⟨x, hxs⟩)) y := by rw [hxpt, hy1]
      _ ≤ D y := Finset.single_le_sum (f := fun a ↦ h (pt a) y)
          (fun a _ ↦ hnonneg (pt a) y) hmem
  have hDpos (y : M) : 0 < D y := lt_of_lt_of_le zero_lt_one (hD1 y)
  have hDsmooth : ChartSmooth (n := n) D := by
    intro e
    exact ContDiffOn.sum fun a _ ↦ hsm (pt a) e
  have hsubsupp (a : Fin m) :
      tsupport ((fun a y ↦ h (pt a) y / D y) a) ⊆ tsupport (h (pt a)) := by
    refine (closure_mono ?_).trans (subset_of_eq (isClosed_tsupport (h (pt a))).closure_eq)
    intro y hy
    refine subset_tsupport _ fun hzero ↦ hy ?_
    change h (pt a) y / D y = 0
    rw [hzero, zero_div]
  refine ⟨m, fun a y ↦ h (pt a) y / D y, fun a ↦ i (pt a), fun a ↦ ?_, fun a y ↦ ?_,
    fun a ↦ ?_, fun a ↦ ?_, fun y ↦ ?_⟩
  · intro e
    exact (hsm (pt a) e).div (hDsmooth e) fun z _ ↦ (hDpos _).ne'
  · exact div_nonneg (hnonneg (pt a) y) (hDpos y).le
  · exact (hsubsupp a).trans (hsupp (pt a))
  · exact (hcpt (pt a)).of_isClosed_subset (isClosed_tsupport _) (hsubsupp a)
  · rw [← Finset.sum_div]
    exact div_self (hDpos y).ne'

end SGPT.Foundations.Analysis.Pending.ChartPartition

end
