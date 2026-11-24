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
  obtain ⟨r, B, hBirr, -, hSB, hpw⟩ := exists_irreducible_decomposition_euclidean hS
  choose s g hg hBg using fun i => (hBirr i).1
  let B' : Fin r → Set (ComplexModel n) := fun i => {z | ∀ j, g i j z = 0}
  have hBB' : ∀ i, B i =ᶠ[𝓝 0] B' i := fun i => eventuallyEqSet_iff.2 (hBg i)
  have hirr' : ∀ i, IsIrreducibleGerm (B' i) := fun i =>
    isIrreducibleGerm_congr (hBirr i) (hBB' i)
  have hpw' : ∀ i l, i ≠ l → ¬ B' i ≤ᶠ[𝓝 0] B' l := by
    intro i l hil h
    apply hpw hil
    filter_upwards [eventuallyEqSet_iff.mp (hBB' i), eventuallyEqSet_iff.mp (hBB' l), h]
      with z hi hl hz hzi
    exact hl.mpr (hz (hi.mp hzi))
  choose d Ω₁ hΩ₁o hΩ₁0 hΩ₁ using fun i => exists_pure_nhds (hirr' i)
  have hthin : ∀ i l, ∃ Ω : Set (ComplexModel n), IsOpen Ω ∧ (0 : ComplexModel n) ∈ Ω ∧
      (i ≠ l → ∀ O : Set (ComplexModel n), IsOpen O → (O ∩ (B' i ∩ Ω)).Nonempty →
        ∃ y ∈ O ∩ (B' i ∩ Ω), y ∉ B' l) := by
    intro i l
    by_cases hil : i = l
    · exact ⟨univ, isOpen_univ, mem_univ _, fun h => absurd hil h⟩
    · obtain ⟨Ω, hΩo, hΩ0, hΩ⟩ := exists_thin_nhds (hirr' i) (hirr' l).1 (hpw' i l hil)
      exact ⟨Ω, hΩo, hΩ0, fun _ => hΩ⟩
  choose Ω₂ hΩ₂o hΩ₂0 hΩ₂ using hthin
  have hev : ∀ᶠ z in 𝓝 (0 : ComplexModel n), (z ∈ S ↔ ∃ i, ∀ j, g i j z = 0) ∧
      ∀ i j, DifferentiableAt ℂ (g i j) z := by
    have h1 := eventuallyEqSet_iff.1 hSB
    have h2 : ∀ᶠ z in 𝓝 (0 : ComplexModel n), ∀ i, (z ∈ B i ↔ z ∈ B' i) :=
      eventually_all.2 fun i => eventuallyEqSet_iff.1 (hBB' i)
    have h3 : ∀ᶠ z in 𝓝 (0 : ComplexModel n), ∀ i j, DifferentiableAt ℂ (g i j) z :=
      eventually_all.2 fun i => eventually_all.2 fun j => hg i j
    filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
    refine ⟨?_, hz3⟩
    rw [hz1, mem_iUnion]
    exact exists_congr fun i => hz2 i
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  let Ω : Set (ComplexModel n) :=
    Metric.ball 0 ε ∩ (⋂ i, Ω₁ i) ∩ ⋂ i, ⋂ l, Ω₂ i l
  have hΩo : IsOpen Ω := (Metric.isOpen_ball.inter (isOpen_iInter_of_finite hΩ₁o)).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun l => hΩ₂o i l)
  have hΩ0 : (0 : ComplexModel n) ∈ Ω :=
    ⟨⟨Metric.mem_ball_self hε, mem_iInter.2 hΩ₁0⟩,
      mem_iInter.2 fun i => mem_iInter.2 fun l => hΩ₂0 i l⟩
  have hΩ1 : ∀ i, Ω ⊆ Ω₁ i := fun i z hz => mem_iInter.1 hz.1.2 i
  have hΩ2 : ∀ i l, Ω ⊆ Ω₂ i l := fun i l z hz => mem_iInter.1 (mem_iInter.1 hz.2 i) l
  let D₀ : LocalDecomposition (n := n) (M := ComplexModel n) S 0 := {
    nbhd := Ω
    isOpen_nbhd := hΩo
    mem_nbhd := hΩ0
    nbhd_subset_source := fun _ _ => mem_univ _
    count := r
    piece := fun i => B' i ∩ Ω
    dim := d
    eqnCount := s
    eqn := g
    eqn_holomorphic := by
      rintro i j _ ⟨z, hz, rfl⟩
      exact ((hball z hz.1.1).2 i j).differentiableWithinAt
    piece_subset := fun i => inter_subset_right
    mem_piece_iff := fun i y hy => ⟨fun h => h.1, fun h => ⟨h, hy⟩⟩
    inter_nbhd_eq := by
      ext z
      simp only [mem_inter_iff, mem_iUnion]
      constructor
      · rintro ⟨hzS, hzΩ⟩
        obtain ⟨i, hi⟩ := (hball z hzΩ.1.1).1.mp hzS
        exact ⟨i, hi, hzΩ⟩
      · rintro ⟨i, hi, hzΩ⟩
        exact ⟨(hball z hzΩ.1.1).1.mpr ⟨i, hi⟩, hzΩ⟩
    eq_dim_of_regularAtDim := fun i {y k} hy => (hΩ₁ i Ω hΩo (hΩ1 i)).1 hy
    subset_closure_regularLocus := fun i => (hΩ₁ i Ω hΩo (hΩ1 i)).2
    exists_mem_not_mem := by
      intro i l hil O hO hne
      obtain ⟨y₀, hy₀O, hy₀i, hy₀Ω⟩ := hne
      obtain ⟨y, ⟨⟨hyO, hyΩ⟩, hyi, -⟩, hyl⟩ := hΩ₂ i l hil (O ∩ Ω) (hO.inter hΩo)
        ⟨y₀, ⟨hy₀O, hy₀Ω⟩, hy₀i, hΩ2 i l hy₀Ω⟩
      exact ⟨y, ⟨hyO, hyi, hyΩ⟩, fun h => hyl h.1⟩ }
  -- every irreducible piece passes through `0`
  have hB'0 : ∀ i, (0 : ComplexModel n) ∈ B' i := by
    intro i
    by_contra h0
    obtain ⟨j, hj⟩ : ∃ j, g i j 0 ≠ 0 := by
      by_contra h
      push Not at h
      exact h0 h
    apply (hirr' i).2.1
    have hc : ContinuousAt (g i j) 0 := (hg i j).self_of_nhds.continuousAt
    refine eventuallyEqSet_iff.2 ?_
    filter_upwards [hc.eventually_ne hj] with z hz
    exact ⟨fun h => hz (h j), fun h => h.elim⟩
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
    mem_piece := fun i => ⟨hB'0 i, hΩ0⟩
    core := Δ
    isOpen_core := hΔo
    mem_core := hΔ0
    good := G
    good_subset := fun i y hy => ⟨⟨(hGsub i hy).1, hΔN i (hGsub i hy)⟩, (hGsub i hy).2⟩
    isPreconnected_good := hGconn
    subset_closure_good := fun i y hy => hGdense i ⟨hy.1.1, hy.2⟩
    not_mem_piece := fun i l hil y hy hyl => hGnot i y hy l (Ne.symm hil) hyl.1
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
  have hdd : dd i = d i := (hΩ₁ i (Ω ∩ Δ i) hW1 (fun z hz => hΩ1 i hz.1)).1 hR1
  let W : Set (ComplexModel n) :=
    Ω ∩ Δ i ∩ ⋂ l, (if l = i then univ else Ω \ D₀.piece l)
  have hWo : IsOpen W := hW1.inter (isOpen_iInter_of_finite fun l => by
    split_ifs
    exacts [isOpen_univ, D₀.isOpen_nbhd_diff_piece l])
  have hyW : y ∈ W := ⟨⟨hyΩ, hyB.2⟩, mem_iInter.2 fun l => by
    split_ifs with hl
    · exact mem_univ _
    · exact ⟨hyΩ, fun h => hGnot i y hy l hl h.1⟩⟩
  have hset : (B' i ∩ Δ i) ∩ W = S ∩ W := by
    ext z
    constructor
    · rintro ⟨⟨hzB, -⟩, hzW⟩
      have hz : z ∈ S ∩ D₀.nbhd := by
        rw [D₀.inter_nbhd_eq]
        exact mem_iUnion.2 ⟨i, hzB, hzW.1.1⟩
      exact ⟨hz.1, hzW⟩
    · rintro ⟨hzS, hzW⟩
      have hz : z ∈ ⋃ l, D₀.piece l := by
        rw [← D₀.inter_nbhd_eq]
        exact ⟨hzS, hzW.1.1⟩
      obtain ⟨l, hl⟩ := mem_iUnion.1 hz
      by_cases hli : l = i
      · rw [hli] at hl
        exact ⟨⟨hl.1, hzW.1.2⟩, hzW⟩
      · have h := mem_iInter.1 hzW.2 l
        rw [ite_eq_right hli] at h
        exact absurd hl h.2
  have hR2 := regularAtDim_of_inter_eq hWo hyW hset (hGreg i y hy)
  rw [hdd] at hR2
  exact hR2

/-- **(LS) with connected regular parts.** -/
theorem exists_connectedParts {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A) {p : M}
    (_hp : p ∈ A) : ∃ D : LocalDecomposition (n := n) A p, Nonempty (ConnectedParts D) := by
  obtain ⟨P⟩ := hA p
  let e := (complexChartAt (n := n) p).val
  let q := e p
  let S : Set (ComplexModel n) := {w | w + q ∈ e.target ∩ e.symm ⁻¹' A}
  have hN : ∀ᶠ w in 𝓝 (0 : ComplexModel n), w + q ∈ P.coordinateNeighborhood := by
    have ht : Tendsto (fun w : ComplexModel n => w + q) (𝓝 0) (𝓝 q) := by
      exact (continuous_add_const q).tendsto' 0 q (zero_add q)
    exact ht (P.isOpen_coordinateNeighborhood.mem_nhds P.center_mem_coordinateNeighborhood)
  have hS : IsAnalyticGerm S := by
    refine ⟨P.generatorCount, fun j w => P.generator j (w + q), fun j => ?_, ?_⟩
    · filter_upwards [hN] with w hw
      exact ((P.generator_holomorphic j).differentiableAt
        (P.isOpen_coordinateNeighborhood.mem_nhds hw)).comp w (differentiableAt_id.add_const q)
    · filter_upwards [hN] with w hw
      have ht : w + q ∈ e.target := P.coordinateNeighborhood_subset_target hw
      have hy : e.symm (w + q) ∈ e.source := e.map_target ht
      have hz := P.zeroLocus hy (by rwa [e.right_inv ht])
      rw [e.right_inv ht] at hz
      change (w + q ∈ e.target ∧ e.symm (w + q) ∈ A) ↔ _
      exact ⟨fun h => hz.mp h.2, fun h => ⟨ht, hz.mpr h⟩⟩
  obtain ⟨D₀, ⟨C₀⟩⟩ := exists_connectedParts_zero hS
  have hset : {z | z - q ∈ S} = e.target ∩ e.symm ⁻¹' A := by
    ext z
    simp [S]
  exact ⟨_, ⟨ConnectedParts.ofChart ((C₀.translate q).congrSet hset)⟩⟩

end SGPT.Foundations.Analysis.Pending.LocalStatementConnected
