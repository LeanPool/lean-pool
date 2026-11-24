/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PureDimension

/-!
# Closures of differences of analytic sets

Blueprint `ana:closure-difference-analytic`, `ana:component-maximal` (Demailly, *Complex
analytic and differential geometry*, II.5.3).

* `isComplexAnalyticSubset_closure_diff`: for analytic `X`, `Y`, the set
  `closure (X \ Y)` is analytic.  Near `p ∈ X`, in a chart, `X` is a finite union of
  irreducible germs `Xᵢ`; those contained in `Y` near `p` contribute nothing, and for the
  others `Xᵢ ∩ Y` is thin in `Xᵢ` (`IrreducibleGermLocal.exists_thin_nhds`), so near `p`
  the closure is the union of the `Xᵢ ⊄ Y`.
* `eq_of_subset_of_inter_open_subset`: an analytic `V` inside an irreducible `Z` which
  contains a nonempty relatively open piece of `Z` is all of `Z`, since
  `Z = V ∪ closure (Z \ V)`.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ClosureDifferenceAnalytic

open FirstPass AnalyticGermDecomposition IrreducibleGermLocal AnalyticLocalStatement

variable {n : ℕ}

/-- **The model-space picture.**  Near `0`, an analytic germ `S` is a finite union of exact
zero sets `Sᵢ`; for the indices with `Q i` the set `Sᵢ ∩ T` is thin in `Sᵢ`, and for the
others `Sᵢ ⊆ T`.  The neighbourhood can be chosen inside any given neighbourhood of `0`. -/
theorem exists_nhds_decomposition_rel {S T : Set (ComplexModel n)} (hS : IsAnalyticGerm S)
    (hT : IsAnalyticGerm T) {N : Set (ComplexModel n)} (hN : N ∈ 𝓝 0) :
    ∃ U : Set (ComplexModel n), IsOpen U ∧ (0 : ComplexModel n) ∈ U ∧ U ⊆ N ∧
      ∃ (r : ℕ) (s : Fin r → ℕ) (g : (i : Fin r) → Fin (s i) → ComplexModel n → ℂ)
        (Q : Fin r → Prop),
        (∀ i j, DifferentiableOn ℂ (g i j) U) ∧
        (∀ z ∈ U, z ∈ S ↔ ∃ i, ∀ j, g i j z = 0) ∧
        (∀ i, ¬ Q i → ∀ z ∈ U, (∀ j, g i j z = 0) → z ∈ T) ∧
        (∀ i, Q i → ∀ O : Set (ComplexModel n), IsOpen O →
          (∃ z ∈ O ∩ U, ∀ j, g i j z = 0) → ∃ z ∈ O ∩ U, (∀ j, g i j z = 0) ∧ z ∉ T) := by
  classical
  obtain ⟨r, B, hBirr, -, hSB, -⟩ := exists_irreducible_decomposition_euclidean hS
  choose s g hg hBg using fun i => (hBirr i).1
  let B' : Fin r → Set (ComplexModel n) := fun i => {z | ∀ j, g i j z = 0}
  have hBB' : ∀ i, B i =ᶠ[𝓝 0] B' i := fun i => eventuallyEqSet_iff.2 (hBg i)
  have hirr' : ∀ i, IsIrreducibleGerm (B' i) := fun i =>
    isIrreducibleGerm_congr (hBirr i) (hBB' i)
  let Q : Fin r → Prop := fun i => ¬ B' i ≤ᶠ[𝓝 0] T
  have hloc : ∀ i, ∃ Ω : Set (ComplexModel n), IsOpen Ω ∧ (0 : ComplexModel n) ∈ Ω ∧
      (¬ Q i → ∀ z ∈ Ω, z ∈ B' i → z ∈ T) ∧
      (Q i → ∀ O : Set (ComplexModel n), IsOpen O → (O ∩ (B' i ∩ Ω)).Nonempty →
        ∃ y ∈ O ∩ (B' i ∩ Ω), y ∉ T) := by
    intro i
    by_cases hQ : Q i
    · obtain ⟨Ω, hΩo, hΩ0, hΩ⟩ := exists_thin_nhds (hirr' i) hT hQ
      exact ⟨Ω, hΩo, hΩ0, fun h => absurd hQ h, fun _ => hΩ⟩
    · have hle : B' i ≤ᶠ[𝓝 0] T := not_not.mp hQ
      obtain ⟨Ω, hΩsub, hΩo, hΩ0⟩ := mem_nhds_iff.mp hle
      exact ⟨Ω, hΩo, hΩ0, fun _ z hz hzB => hΩsub hz hzB, fun h => absurd h hQ⟩
  choose Ω hΩo hΩ0 hΩ1 hΩ2 using hloc
  have hev : ∀ᶠ z in 𝓝 (0 : ComplexModel n), ((z ∈ S ↔ ∃ i, ∀ j, g i j z = 0) ∧
      ∀ i j, DifferentiableAt ℂ (g i j) z) ∧ z ∈ N := by
    have h1 := eventuallyEqSet_iff.1 hSB
    have h2 : ∀ᶠ z in 𝓝 (0 : ComplexModel n), ∀ i, (z ∈ B i ↔ z ∈ B' i) :=
      eventually_all.2 fun i => eventuallyEqSet_iff.1 (hBB' i)
    have h3 : ∀ᶠ z in 𝓝 (0 : ComplexModel n), ∀ i j, DifferentiableAt ℂ (g i j) z :=
      eventually_all.2 fun i => eventually_all.2 fun j => hg i j
    filter_upwards [h1, h2, h3, hN] with z hz1 hz2 hz3 hz4
    refine ⟨⟨?_, hz3⟩, hz4⟩
    rw [hz1, mem_iUnion]
    exact exists_congr fun i => hz2 i
  obtain ⟨V, hVsub, hVo, hV0⟩ := mem_nhds_iff.mp hev
  let U : Set (ComplexModel n) := V ∩ ⋂ i, Ω i
  have hUo : IsOpen U := hVo.inter (isOpen_iInter_of_finite hΩo)
  have hUΩ : ∀ i, U ⊆ Ω i := fun i z hz => mem_iInter.1 hz.2 i
  refine ⟨U, hUo, ⟨hV0, mem_iInter.2 hΩ0⟩, fun z hz => (hVsub hz.1).2, r, s, g, Q,
    ?_, ?_, ?_, ?_⟩
  · intro i j z hz
    exact ((hVsub hz.1).1.2 i j).differentiableWithinAt
  · intro z hz
    exact (hVsub hz.1).1.1
  · intro i hQ z hz hzB
    exact hΩ1 i hQ z (hUΩ i hz) hzB
  · rintro i hQ O hO ⟨z, hzOU, hzB⟩
    obtain ⟨y, ⟨⟨hyO, hyU⟩, hyB, -⟩, hyT⟩ :=
      hΩ2 i hQ (O ∩ U) (hO.inter hUo) ⟨z, hzOU, hzB, hUΩ i hzOU.2⟩
    exact ⟨y, ⟨hyO, hyU⟩, hyB, hyT⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A presentation at `x` of a set which, on an open neighbourhood `W` of `x` in the chart
source, is a finite union of common zero sets of functions holomorphic on the chart image of
`W`. -/
theorem nonempty_presentation_of_eq_on_nhds {S : Set M} {x : M} {W : Set M} (hW : IsOpen W)
    (hxW : x ∈ W) (hWs : W ⊆ (complexChartAt (n := n) x).val.source) {r : ℕ}
    (s : Fin r → ℕ) (f : (i : Fin r) → Fin (s i) → ComplexModel n → ℂ)
    (hf : ∀ i j, DifferentiableOn ℂ (f i j) ((complexChartAt (n := n) x).val '' W))
    (Q : Fin r → Prop)
    (hS : ∀ y ∈ W, y ∈ S ↔ ∃ i, Q i ∧ ∀ j, f i j ((complexChartAt (n := n) x).val y) = 0) :
    Nonempty (ComplexAnalyticPresentationAt (n := n) S x) := by
  classical
  set e := (complexChartAt (n := n) x).val with he
  let ι := (i : {i // Q i}) → Fin (s i.1)
  let eqv := Fintype.equivFin ι
  let g : Fin (Fintype.card ι) → ComplexModel n → ℂ := fun c z =>
    ∏ i : {i // Q i}, f i.1 (eqv.symm c i) z
  have hopen : IsOpen (e '' W) := e.isOpen_image_of_subset_source hW hWs
  refine ⟨{ generatorCount := Fintype.card ι
            generator := g
            coordinateNeighborhood := e '' W
            isOpen_coordinateNeighborhood := hopen
            center_mem_coordinateNeighborhood := mem_image_of_mem e hxW
            coordinateNeighborhood_subset_target := ?_
            generator_holomorphic := ?_
            zeroLocus := ?_ }⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact e.map_source (hWs hy)
  · intro c
    exact PureDimension.differentiableOn_finset_prod _ _ _ fun (i : {i // Q i}) _ => hf i.1 _
  · intro y hy hyN
    obtain ⟨y', hy'W, hy'y⟩ := hyN
    have hyW : y ∈ W := by
      rwa [← e.injOn (hWs hy'W) hy hy'y]
    rw [hS y hyW]
    constructor
    · rintro ⟨i, hQi, hi⟩ c
      exact Finset.prod_eq_zero (Finset.mem_univ ⟨i, hQi⟩) (hi _)
    · intro h
      by_contra hcon
      push Not at hcon
      have hch : ∀ i : {i // Q i}, ∃ j, f i.1 j (e y) ≠ 0 := fun i => hcon i.1 i.2
      choose c hc using hch
      have := h (eqv c)
      simp only [g, Equiv.symm_apply_apply] at this
      exact (Finset.prod_ne_zero_iff.mpr fun i _ => hc i) this

/-- **Closures of differences of analytic sets are analytic.** -/
theorem isComplexAnalyticSubset_closure_diff {X Y : Set M}
    (hX : IsComplexAnalyticSubset (n := n) X) (hY : IsComplexAnalyticSubset (n := n) Y) :
    IsComplexAnalyticSubset (n := n) (closure (X \ Y)) := by
  intro x
  by_cases hx : x ∈ X
  swap
  · exact PureDimension.nonempty_presentation_of_not_mem hX.isClosed
      (closure_minimal sdiff_subset hX.isClosed) hx
  obtain ⟨PX⟩ := hX x
  obtain ⟨PY⟩ := hY x
  set e := (complexChartAt (n := n) x).val with he
  set q := e x with hq
  have hNt : {w : ComplexModel n | w + q ∈ e.target} ∈ 𝓝 (0 : ComplexModel n) := by
    have ht : Tendsto (fun w : ComplexModel n => w + q) (𝓝 0) (𝓝 q) :=
      (continuous_add_const q).tendsto' 0 q (zero_add q)
    exact ht (e.open_target.mem_nhds (e.map_source (mem_complexChartAt_source x)))
  obtain ⟨U, hUo, hU0, hUN, r, s, g, Q, hg, hgS, hgT, hthin⟩ :=
    exists_nhds_decomposition_rel (AnalyticLocalStatement.isAnalyticGerm_chart_translate PX)
      (AnalyticLocalStatement.isAnalyticGerm_chart_translate PY) hNt
  let W : Set M := e.source ∩ e ⁻¹' ((fun v => v - q) ⁻¹' U)
  have hWo : IsOpen W := e.isOpen_inter_preimage (hUo.preimage (continuous_sub_right q))
  have hxW : x ∈ W := ⟨mem_complexChartAt_source x, by simpa [q] using hU0⟩
  -- membership in `X`, `Y` read in the translated chart
  have hmem : ∀ (A : Set M) (y : M), y ∈ e.source →
      (e y - q ∈ {w : ComplexModel n | w + q ∈ e.target ∩ e.symm ⁻¹' A} ↔ y ∈ A) := by
    intro A y hy
    simp only [mem_ofPred_eq, sub_add_cancel, mem_inter_iff, mem_preimage, e.left_inv hy,
      e.map_source hy, true_and]
  have hcont : ∀ i j, ∀ y ∈ W, ContinuousAt (fun z => g i j (e z - q)) y := by
    intro i j y hy
    have h1 : ContinuousAt (g i j) (e y - q) :=
      (hg i j).continuousOn.continuousAt (hUo.mem_nhds hy.2)
    have h2 : ContinuousAt (fun z => e z - q) y :=
      (e.continuousAt hy.1).sub continuousAt_const
    exact h1.comp (f := fun z => e z - q) h2
  have key : ∀ y ∈ W, y ∈ closure (X \ Y) ↔ ∃ i, Q i ∧ ∀ j, g i j (e y - q) = 0 := by
    intro y hyW
    constructor
    · intro hycl
      by_contra hcon
      push Not at hcon
      have hev : ∀ᶠ z in 𝓝 y, ∀ i, Q i → ∃ j, g i j (e z - q) ≠ 0 := by
        refine eventually_all.2 fun i => ?_
        by_cases hQ : Q i
        · obtain ⟨j, hj⟩ := hcon i hQ
          filter_upwards [(hcont i j y hyW).eventually_ne hj] with z hz
          exact fun _ => ⟨j, hz⟩
        · exact Eventually.of_forall fun _ h => absurd h hQ
      obtain ⟨z, ⟨hz, hzW⟩, hzX, hzY⟩ :=
        mem_closure_iff_nhds.mp hycl _ (hev.and (hWo.mem_nhds hyW))
      obtain ⟨i, hi⟩ := (hgS _ hzW.2).mp ((hmem X z hzW.1).mpr hzX)
      by_cases hQ : Q i
      · obtain ⟨j, hj⟩ := hz i hQ
        exact hj (hi j)
      · exact hzY ((hmem Y z hzW.1).mp (hgT i hQ _ hzW.2 hi))
    · rintro ⟨i, hQ, hi⟩
      rw [mem_closure_iff]
      intro O hO hyO
      let O₀ : Set (ComplexModel n) :=
        (fun w => w + q) ⁻¹' (e.target ∩ e.symm ⁻¹' O)
      have hO₀ : IsOpen O₀ :=
        (e.isOpen_inter_preimage_symm hO).preimage (continuous_add_const q)
      obtain ⟨w, ⟨hwO, hwU⟩, hwg, hwT⟩ := hthin i hQ O₀ hO₀
        ⟨e y - q, ⟨by simpa [O₀, e.left_inv hyW.1, e.map_source hyW.1] using hyO, hyW.2⟩, hi⟩
      have hwt : w + q ∈ e.target := hwO.1
      have hzs : e.symm (w + q) ∈ e.source := e.map_target hwt
      have hez : e (e.symm (w + q)) - q = w := by rw [e.right_inv hwt, add_sub_cancel_right]
      refine ⟨e.symm (w + q), hwO.2, ?_, ?_⟩
      · rw [← hmem X _ hzs, hez]
        exact (hgS w hwU).mpr ⟨i, hwg⟩
      · rw [← hmem Y _ hzs, hez]
        exact hwT
  refine nonempty_presentation_of_eq_on_nhds hWo hxW inter_subset_left s
    (fun i j v => g i j (v - q)) ?_ Q key
  intro i j
  rintro _ ⟨y, hy, rfl⟩
  exact (((hg i j).differentiableAt (hUo.mem_nhds hy.2)).comp (e y)
    (differentiableAt_id.sub_const q)).differentiableWithinAt

/-- **Maximality from an open piece.** -/
theorem eq_of_subset_of_inter_open_subset {V Z : Set M}
    (hV : IsComplexAnalyticSubset (n := n) V)
    (hZ : IsComplexAnalyticallyIrreducible (n := n) Z) (hVZ : V ⊆ Z) {O : Set M}
    (hO : IsOpen O) (hne : (Z ∩ O).Nonempty) (hsub : Z ∩ O ⊆ V) : V = Z := by
  have hC := isComplexAnalyticSubset_closure_diff hZ.analytic hV
  have hCZ : closure (Z \ V) ⊆ Z := closure_minimal sdiff_subset hZ.analytic.isClosed
  have hZVC : Z = V ∪ closure (Z \ V) := by
    refine Subset.antisymm (fun z hz => ?_) (union_subset hVZ hCZ)
    by_cases hzV : z ∈ V
    · exact Or.inl hzV
    · exact Or.inr (subset_closure ⟨hz, hzV⟩)
  rcases hZ.eq_left_or_eq_right hV hC hVZ hCZ hZVC with h | h
  · exact h.symm
  · exfalso
    obtain ⟨y, hyZ, hyO⟩ := hne
    obtain ⟨z, hzO, hzZ, hzV⟩ := mem_closure_iff.mp (h.subset hyZ) O hO hyO
    exact hzV (hsub ⟨hzZ, hzO⟩)

end SGPT.Foundations.Analysis.Pending.ClosureDifferenceAnalytic
