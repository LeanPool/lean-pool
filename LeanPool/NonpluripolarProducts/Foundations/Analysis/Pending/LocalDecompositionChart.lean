/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.AnalyticLocalStatement
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.RegularAtDimChart
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.RegularPointDimension

/-!
# The local statement transported from a chart

Local decomposition data (LS) for the chart image `Â = e.target ∩ e⁻¹ A` of `A` at `e p`, in
the model space `ℂⁿ` with its identity chart, pull back along the preferred chart `e` at
`p` to local decomposition data for `A` at `p` (`LocalDecomposition.ofChart`).  Pieces are
pulled back, equations are unchanged, and regularity is transported by
`RegularAtDimChart.regularAtDim_chart_iff`.

This reduces blueprint `lag:local-statement` to the model space.
-/

@[expose] public section

open Set

namespace SGPT.Foundations.Analysis.Pending.AnalyticLocalStatement.LocalDecomposition

open FirstPass RegularAtDimChart RegularPointDimension

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Regular points of a subset of the model space are unchanged by intersecting with an open
set containing them. -/
theorem regularAtDim_inter_open_iff {B U : Set (ComplexModel n)} (hU : IsOpen U)
    {z : ComplexModel n} (hz : z ∈ U) {k : ℕ} :
    RegularAtDim (n := n) (M := ComplexModel n) (B ∩ U) z k ↔
      RegularAtDim (n := n) (M := ComplexModel n) B z k := by
  have h : B ∩ U ∩ U = B ∩ U := by rw [inter_assoc, inter_self]
  exact ⟨regularAtDim_of_inter_eq hU hz h, regularAtDim_of_inter_eq hU hz h.symm⟩

/-- **Pulling back local decomposition data along the chart at `p`.** -/
def ofChart {A : Set M} {p : M}
    (D : LocalDecomposition (n := n) (M := ComplexModel n)
      ((complexChartAt (n := n) p).val.target ∩ (complexChartAt (n := n) p).val.symm ⁻¹' A)
      ((complexChartAt (n := n) p).val p)) :
    LocalDecomposition (n := n) A p where
  nbhd := (complexChartAt (n := n) p).val.source ∩ (complexChartAt (n := n) p).val ⁻¹' D.nbhd
  isOpen_nbhd := (complexChartAt (n := n) p).val.isOpen_inter_preimage D.isOpen_nbhd
  mem_nbhd := ⟨mem_complexChartAt_source p, D.mem_nbhd⟩
  nbhd_subset_source := inter_subset_left
  count := D.count
  piece i := (complexChartAt (n := n) p).val.source ∩
    (complexChartAt (n := n) p).val ⁻¹' D.piece i
  dim := D.dim
  eqnCount := D.eqnCount
  eqn := D.eqn
  eqn_holomorphic i j := by
    refine (D.eqn_holomorphic i j).mono ?_
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨_, hy.2, rfl⟩
  piece_subset i := fun y hy => ⟨hy.1, D.piece_subset i hy.2⟩
  mem_piece_iff i y hy := by
    have h := D.mem_piece_iff i ((complexChartAt (n := n) p).val y) hy.2
    exact ⟨fun h' => h.mp h'.2, fun h' => ⟨hy.1, h.mpr h'⟩⟩
  inter_nbhd_eq := by
    ext y
    simp only [mem_inter_iff, mem_iUnion, mem_preimage]
    constructor
    · rintro ⟨hyA, hys, hyW⟩
      let chart := complexChartAt (n := n) p
      have hyA' : chart.val y ∈ chart.val.symm ⁻¹' A := by
        simpa only [mem_preimage, chart.val.left_inv hys] using hyA
      have hyHat : chart.val y ∈ (chart.val.target ∩ chart.val.symm ⁻¹' A) ∩ D.nbhd :=
        ⟨⟨chart.val.map_source hys, hyA'⟩, hyW⟩
      rw [D.inter_nbhd_eq] at hyHat
      obtain ⟨i, hi⟩ := mem_iUnion.mp hyHat
      exact ⟨i, hys, hi⟩
    · rintro ⟨i, hys, hi⟩
      have hyHat : (complexChartAt (n := n) p).val y ∈ ⋃ i, D.piece i := mem_iUnion.mpr ⟨i, hi⟩
      rw [← D.inter_nbhd_eq] at hyHat
      have hA := hyHat.1.2
      simp only [mem_preimage, (complexChartAt (n := n) p).val.left_inv hys] at hA
      exact ⟨hA, hys, hyHat.2⟩
  eq_dim_of_regularAtDim i {y k} hy := by
    have hys : y ∈ (complexChartAt (n := n) p).val.source := hy.2.1.1
    have h1 := (regularAtDim_chart_iff (complexChartAt (n := n) p) (D.piece i) hys).mp hy
    rw [regularAtDim_inter_open_iff (complexChartAt (n := n) p).val.open_target ((complexChartAt
      (n := n) p).val.map_source hys)] at h1
    exact D.eq_dim_of_regularAtDim i h1
  subset_closure_regularLocus i := by
    intro y hy
    rw [mem_closure_iff]
    intro O hO hyO
    have hO' : IsOpen ((complexChartAt (n := n) p).val '' (O ∩ (complexChartAt (n := n)
      p).val.source)) :=
      (complexChartAt (n := n) p).val.isOpen_image_of_subset_source (hO.inter (complexChartAt (n
        := n) p).val.open_source) inter_subset_right
    obtain ⟨w, ⟨y', hy'O, rfl⟩, hw⟩ := mem_closure_iff.mp (D.subset_closure_regularLocus i hy.2)
      _ hO' ⟨y, ⟨hyO, hy.1⟩, rfl⟩
    refine ⟨y', hy'O.1, ?_⟩
    rw [mem_regularLocus, regularAtDim_chart_iff (complexChartAt (n := n) p) (D.piece i) hy'O.2,
      regularAtDim_inter_open_iff (complexChartAt (n := n) p).val.open_target ((complexChartAt (n
        := n) p).val.map_source hy'O.2)]
    exact hw
  exists_mem_not_mem i l hil O hO hne := by
    obtain ⟨y, hyO, hyi⟩ := hne
    have hO' : IsOpen ((complexChartAt (n := n) p).val '' (O ∩ (complexChartAt (n := n)
      p).val.source)) :=
      (complexChartAt (n := n) p).val.isOpen_image_of_subset_source (hO.inter (complexChartAt (n
        := n) p).val.open_source) inter_subset_right
    obtain ⟨w, ⟨⟨y', hy'O, rfl⟩, hwi⟩, hwl⟩ :=
      D.exists_mem_not_mem i l hil _ hO' ⟨(complexChartAt (n := n) p).val y, ⟨y, ⟨hyO, hyi.1⟩,
        rfl⟩, hyi.2⟩
    exact ⟨y', ⟨hy'O.1, hy'O.2, hwi⟩, fun h => hwl h.2⟩

end

end SGPT.Foundations.Analysis.Pending.AnalyticLocalStatement.LocalDecomposition
