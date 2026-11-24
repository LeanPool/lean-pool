/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.IrreducibleGermConnected
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalStatementAssembly
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PureDimension

/-!
# The local statement with connected regular parts

Blueprint `lag:local-statement-connected` (Demailly, *Complex analytic and differential
geometry*, II.4.24, II.5.3).

`ConnectedParts D` strengthens local decomposition data `D` of `A` at `p`: every piece
contains `p`, and each piece `Aᵢ` has an open neighbourhood `Δᵢ` of `p` and a connected set
`Gᵢ ⊆ Aᵢ ∩ Δᵢ`, dense in `Aᵢ ∩ Δᵢ`, meeting no other piece, of regular points of `A` of
dimension `dᵢ`.  `exists_connectedParts` runs the assembly of (LS) with
`IrreducibleGermConnected.exists_connected_nhds` applied to each irreducible piece and the
other pieces.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.LocalStatementConnected

open FirstPass AnalyticLocalStatement AnalyticGermDecomposition

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Connected dense regular parts of the pieces of local decomposition data. -/
structure ConnectedParts {A : Set M} {p : M} (D : LocalDecomposition (n := n) A p) where
  mem_piece : ∀ i, p ∈ D.piece i
  /-- The neighbourhood `Δᵢ`. -/
  core : Fin D.count → Set M
  isOpen_core : ∀ i, IsOpen (core i)
  mem_core : ∀ i, p ∈ core i
  /-- The connected regular part `Gᵢ`. -/
  good : Fin D.count → Set M
  good_subset : ∀ i, good i ⊆ D.piece i ∩ core i
  isPreconnected_good : ∀ i, IsPreconnected (good i)
  subset_closure_good : ∀ i, D.piece i ∩ core i ⊆ closure (good i)
  not_mem_piece : ∀ i l, i ≠ l → ∀ y ∈ good i, y ∉ D.piece l
  regularAtDim_of_mem_good : ∀ i, ∀ y ∈ good i, RegularAtDim (n := n) A y (D.dim i)

namespace ConnectedParts

/-- Connected parts along an equality of sets. -/
def congrSet {A A' : Set M} {p : M} (h : A = A') {D : LocalDecomposition (n := n) A p}
    (C : ConnectedParts D) : ConnectedParts (D.congrSet h) := by
  subst h
  exact C

/-- Connected parts of translated local decomposition data. -/
def translate {S : Set (ComplexModel n)}
    {D : LocalDecomposition (n := n) (M := ComplexModel n) S 0} (C : ConnectedParts D)
    (q : ComplexModel n) : ConnectedParts (D.translate q) where
  mem_piece i := by
    change q - q ∈ D.piece i
    simpa using C.mem_piece i
  core i := {z | z - q ∈ C.core i}
  isOpen_core i := (C.isOpen_core i).preimage (continuous_id.sub continuous_const)
  mem_core i := by
    change q - q ∈ C.core i
    simpa using C.mem_core i
  good i := {z | z - q ∈ C.good i}
  good_subset i z hz := C.good_subset i hz
  isPreconnected_good i := (Homeomorph.subRight q).isPreconnected_preimage.mpr
    (C.isPreconnected_good i)
  subset_closure_good i := by
    intro z hz
    have h : z - q ∈ closure (C.good i) := C.subset_closure_good i hz
    have hc : (Homeomorph.subRight q) ⁻¹' closure (C.good i) =
        closure ((Homeomorph.subRight q) ⁻¹' C.good i) :=
      (Homeomorph.subRight q).preimage_closure _
    have h2 : z ∈ closure ((Homeomorph.subRight q) ⁻¹' C.good i) := by
      rw [← hc]
      exact h
    exact h2
  not_mem_piece i l hil y hy := C.not_mem_piece i l hil _ hy
  regularAtDim_of_mem_good i y hy :=
    (regularAtDim_translate_iff q y).mpr (C.regularAtDim_of_mem_good i _ hy)

/-- Regular points of the chart image of `A` are regular points of `A`. -/
theorem regularAtDim_of_chart {A : Set M} {p y : M}
    (hys : y ∈ (complexChartAt (n := n) p).val.source) {k : ℕ}
    (h : RegularAtDim (n := n) (M := ComplexModel n)
      ((complexChartAt (n := n) p).val.target ∩ (complexChartAt (n := n) p).val.symm ⁻¹' A)
      ((complexChartAt (n := n) p).val y) k) :
    RegularAtDim (n := n) A y k := by
  have h1 := (LocalDecomposition.regularAtDim_inter_open_iff
    (complexChartAt (n := n) p).val.open_target
    ((complexChartAt (n := n) p).val.map_source hys)).mpr h
  have h2 := (RegularAtDimChart.regularAtDim_chart_iff (complexChartAt (n := n) p) _ hys).mpr h1
  refine RegularPointDimension.regularAtDim_of_inter_eq
    (complexChartAt (n := n) p).val.open_source hys ?_ h2
  ext z
  constructor
  · rintro ⟨⟨hzs, -, hzA⟩, -⟩
    have hzA' : (complexChartAt (n := n) p).val.symm ((complexChartAt (n := n) p).val z) ∈ A :=
      hzA
    rw [(complexChartAt (n := n) p).val.left_inv hzs] at hzA'
    exact ⟨hzA', hzs⟩
  · rintro ⟨hzA, hzs⟩
    refine ⟨⟨hzs, (complexChartAt (n := n) p).val.map_source hzs, ?_⟩, hzs⟩
    change (complexChartAt (n := n) p).val.symm ((complexChartAt (n := n) p).val z) ∈ A
    rw [(complexChartAt (n := n) p).val.left_inv hzs]
    exact hzA

/-- Connected parts pulled back along the chart at `p`. -/
noncomputable def ofChart {A : Set M} {p : M}
    {D : LocalDecomposition (n := n) (M := ComplexModel n)
      ((complexChartAt (n := n) p).val.target ∩ (complexChartAt (n := n) p).val.symm ⁻¹' A)
      ((complexChartAt (n := n) p).val p)} (C : ConnectedParts D) :
    ConnectedParts (LocalDecomposition.ofChart D) where
  mem_piece i := ⟨mem_complexChartAt_source p, C.mem_piece i⟩
  core i := (complexChartAt (n := n) p).val.source ∩ (complexChartAt (n := n) p).val ⁻¹' C.core i
  isOpen_core i := (complexChartAt (n := n) p).val.isOpen_inter_preimage (C.isOpen_core i)
  mem_core i := ⟨mem_complexChartAt_source p, C.mem_core i⟩
  good i := (complexChartAt (n := n) p).val.source ∩ (complexChartAt (n := n) p).val ⁻¹' C.good i
  good_subset i y hy := ⟨⟨hy.1, (C.good_subset i hy.2).1⟩, hy.1, (C.good_subset i hy.2).2⟩
  isPreconnected_good i := by
    have hsub : C.good i ⊆ (complexChartAt (n := n) p).val.target := fun w hw =>
      (D.piece_subset_inter i (C.good_subset i hw).1).1.1
    rw [← (complexChartAt (n := n) p).val.symm_image_eq_source_inter_preimage hsub]
    exact (C.isPreconnected_good i).image _
      ((complexChartAt (n := n) p).val.continuousOn_symm.mono hsub)
  subset_closure_good i := by
    rintro y ⟨⟨hys, hyi⟩, -, hyc⟩
    have hsub : C.good i ⊆ (complexChartAt (n := n) p).val.target := fun w hw =>
      (D.piece_subset_inter i (C.good_subset i hw).1).1.1
    have h1 : (complexChartAt (n := n) p).val y ∈ closure (C.good i) :=
      C.subset_closure_good i ⟨hyi, hyc⟩
    have h2 := ((complexChartAt (n := n) p).val.continuousAt_symm
      ((complexChartAt (n := n) p).val.map_source hys)).continuousWithinAt.mem_closure_image h1
    rw [(complexChartAt (n := n) p).val.left_inv hys,
      (complexChartAt (n := n) p).val.symm_image_eq_source_inter_preimage hsub] at h2
    exact h2
  not_mem_piece i l hil y hy hyl := C.not_mem_piece i l hil _ hy.2 hyl.2
  regularAtDim_of_mem_good i y hy := regularAtDim_of_chart hy.1
    (C.regularAtDim_of_mem_good i _ hy.2)

end ConnectedParts

open AnalyticGermDecomposition IrreducibleGermLocal RegularPointDimension in
/-- **(LS) with connected regular parts at the origin of the model space.** -/
theorem exists_connectedParts_zero {S : Set (ComplexModel n)} (hS : IsAnalyticGerm S) :
    ∃ D : LocalDecomposition (n := n) (M := ComplexModel n) S 0, Nonempty (ConnectedParts D) := by
  classical
  obtain ⟨D₀, B', hpiece, hirr', hB'0, hpw', hdim⟩ := exists_localDecomposition_germs hS
  let Ω := D₀.nbhd
  have hΩo : IsOpen Ω := D₀.isOpen_nbhd
  have hΩ0 : (0 : ComplexModel n) ∈ Ω := D₀.mem_nbhd
  have hempty : IsAnalyticGerm (∅ : Set (ComplexModel n)) :=
    ⟨1, fun _ _ => 1, fun _ => Eventually.of_forall fun _ => differentiableAt_const _,
      Eventually.of_forall fun z => ⟨fun h => h.elim, fun h => by simpa using h 0⟩⟩
  have hconn : ∀ i, ∃ (d' : ℕ) (Δ G : Set (ComplexModel n)), IsOpen Δ ∧
      (0 : ComplexModel n) ∈ Δ ∧ B' i ∩ Δ ⊆ Ω ∧ G ⊆ B' i ∩ Δ ∧ IsPreconnected G ∧
      B' i ∩ Δ ⊆ closure G ∧ (∀ y ∈ G, ∀ l, l ≠ i → y ∉ B' l) ∧
      ∀ y ∈ G, RegularAtDim (n := n) (M := ComplexModel n) (B' i ∩ Δ) y d' := by
    intro i
    obtain ⟨d', Δ, G, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      IrreducibleGermConnected.exists_connected_nhds (hirr' i)
        (fun l => if l = i then ∅ else B' l)
        (fun l => by
          split_ifs
          exacts [hempty, (hirr' l).1])
        (fun l => by
          split_ifs with hl
          · intro h
            exact (hirr' i).2.1 (h.antisymm (Eventually.of_forall fun _ h => h.elim))
          · exact hpw' i l (Ne.symm hl))
        (hΩo.mem_nhds hΩ0)
    refine ⟨d', Δ, G, h1, h2, h3, h4, h5, h6, fun y hy l hl => ?_, h8⟩
    have h := h7 y hy l
    simpa [hl] using h
  choose dd Δ G hΔo hΔ0 hΔN hGsub hGconn hGdense hGnot hGreg using hconn
  refine ⟨D₀, ⟨{
    mem_piece := fun i => (hpiece i).symm ▸ ⟨hB'0 i, hΩ0⟩
    core := Δ
    isOpen_core := hΔo
    mem_core := hΔ0
    good := G
    good_subset := fun i y hy => by
      rw [hpiece i]
      exact ⟨⟨(hGsub i hy).1, hΔN i (hGsub i hy)⟩, (hGsub i hy).2⟩
    isPreconnected_good := hGconn
    subset_closure_good := fun i y hy => by
      rw [hpiece i] at hy
      exact hGdense i ⟨hy.1.1, hy.2⟩
    not_mem_piece := fun i l hil y hy hyl => by
      rw [hpiece l] at hyl
      exact hGnot i y hy l (Ne.symm hil) hyl.1
    regularAtDim_of_mem_good := ?_ }⟩⟩
  intro i y hy
  have hyB := hGsub i hy
  have hyΩ : y ∈ Ω := hΔN i hyB
  have hW1 : IsOpen (Ω ∩ Δ i) := hΩo.inter (hΔo i)
  have hR1 : RegularAtDim (n := n) (M := ComplexModel n) (B' i ∩ (Ω ∩ Δ i)) y (dd i) := by
    refine regularAtDim_of_inter_eq hW1 ⟨hyΩ, hyB.2⟩ ?_ (hGreg i y hy)
    ext z
    simp only [mem_inter_iff]
    tauto
  have hdd : dd i = D₀.dim i := hdim i (Ω ∩ Δ i) hW1 inter_subset_left hR1
  let W : Set (ComplexModel n) :=
    Ω ∩ Δ i ∩ ⋂ l, (if l = i then univ else Ω \ D₀.piece l)
  have hWo : IsOpen W := hW1.inter (isOpen_iInter_of_finite fun l => by
    split_ifs
    exacts [isOpen_univ, D₀.isOpen_nbhd_diff_piece l])
  have hyW : y ∈ W := ⟨⟨hyΩ, hyB.2⟩, mem_iInter.2 fun l => by
    split_ifs with hl
    · exact mem_univ _
    · exact ⟨hyΩ, fun h => hGnot i y hy l hl ((hpiece l) ▸ h).1⟩⟩
  have hset : (B' i ∩ Δ i) ∩ W = S ∩ W := by
    ext z
    constructor
    · rintro ⟨⟨hzB, -⟩, hzW⟩
      have hz : z ∈ S ∩ D₀.nbhd := by
        rw [D₀.inter_nbhd_eq]
        exact mem_iUnion.2 ⟨i, (hpiece i).symm ▸ ⟨hzB, hzW.1.1⟩⟩
      exact ⟨hz.1, hzW⟩
    · rintro ⟨hzS, hzW⟩
      have hz : z ∈ ⋃ l, D₀.piece l := by
        rw [← D₀.inter_nbhd_eq]
        exact ⟨hzS, hzW.1.1⟩
      obtain ⟨l, hl⟩ := mem_iUnion.1 hz
      by_cases hli : l = i
      · rw [hli, hpiece i] at hl
        exact ⟨⟨hl.1, hzW.1.2⟩, hzW⟩
      · have h := mem_iInter.1 hzW.2 l
        rw [ite_eq_right hli] at h
        exact absurd hl h.2
  have hR2 := regularAtDim_of_inter_eq hWo hyW hset (hGreg i y hy)
  rw [hdd] at hR2
  exact hR2

/-- **(LS) with connected regular parts.** -/
theorem exists_connectedParts {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A) {p : M} :
    ∃ D : LocalDecomposition (n := n) A p, Nonempty (ConnectedParts D) := by
  obtain ⟨P⟩ := hA p
  let e := (complexChartAt (n := n) p).val
  let q := e p
  let S : Set (ComplexModel n) := {w | w + q ∈ e.target ∩ e.symm ⁻¹' A}
  have hS : IsAnalyticGerm S := isAnalyticGerm_chart_translate P
  obtain ⟨D₀, ⟨C₀⟩⟩ := exists_connectedParts_zero hS
  have hset : {z | z - q ∈ S} = e.target ∩ e.symm ⁻¹' A := by
    ext z
    simp [S]
  exact ⟨_, ⟨ConnectedParts.ofChart ((C₀.translate q).congrSet hset)⟩⟩

end SGPT.Foundations.Analysis.Pending.LocalStatementConnected
