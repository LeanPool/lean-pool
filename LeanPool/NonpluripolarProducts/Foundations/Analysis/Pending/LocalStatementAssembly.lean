/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalDecompositionChart
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.IrreducibleGermLocal

/-!
# Assembling the local statement (LS)

Blueprint `lag:local-statement`.  Local decomposition data exist at every point of an analytic
subset of a complex manifold (`AnalyticLocalStatement.exists_localDecomposition`):

1. at `0 ∈ ℂⁿ`, decompose the analytic germ into irredundant irreducible germs
   (`AnalyticGermDecomposition.exists_irreducible_decomposition_euclidean`), replace each by
   the exact zero set of its equations, and choose a ball on which the equations are
   holomorphic, the decomposition holds, every piece is pure-dimensional
   (`IrreducibleGermLocal.exists_pure_nhds`) and pairwise intersections are thin
   (`IrreducibleGermLocal.exists_thin_nhds`) — `exists_localDecomposition_zero`;
2. translate to the chart image `e p` (`LocalDecomposition.translate`);
3. pull back along the chart (`LocalDecomposition.ofChart`).
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.AnalyticLocalStatement

open FirstPass AnalyticGermDecomposition IrreducibleGermLocal RegularAtDimChart

noncomputable section

variable {n : ℕ}

/-- Translation by `-q` as a partial homeomorphism of the model space. -/
def translation (q : ComplexModel n) :
    OpenPartialHomeomorph (ComplexModel n) (ComplexModel n) :=
  (Homeomorph.addRight q).toOpenPartialHomeomorph

theorem translation_apply (q z : ComplexModel n) : translation q z = z + q := rfl

theorem translation_symm_apply (q z : ComplexModel n) : (translation q).symm z = z - q := by
  rw [sub_eq_add_neg]; rfl

theorem translation_source (q : ComplexModel n) : (translation q).source = univ := rfl

theorem translation_target (q : ComplexModel n) : (translation q).target = univ := rfl

theorem differentiableOn_translation (q : ComplexModel n) :
    DifferentiableOn ℂ (translation q) (translation q).source :=
  (differentiable_id.add_const q).differentiableOn

theorem differentiableOn_translation_symm (q : ComplexModel n) :
    DifferentiableOn ℂ (translation q).symm (translation q).target := by
  have : ((translation q).symm : ComplexModel n → ComplexModel n) = fun z => z - q := by
    funext z; exact translation_symm_apply q z
  rw [this]
  exact (differentiable_id.sub_const q).differentiableOn

/-- Regularity in the model space is invariant under translation. -/
theorem regularAtDim_translate_iff {S : Set (ComplexModel n)} (q y : ComplexModel n) {k : ℕ} :
    RegularAtDim (n := n) (M := ComplexModel n) {z | z - q ∈ S} y k ↔
      RegularAtDim (n := n) (M := ComplexModel n) S (y - q) k := by
  constructor
  · rintro ⟨hk, hyS, Φ, -, hΦ0, hflat⟩
    have hc : y - q ∈ (translation q).source := mem_univ _
    have hTc : translation q (y - q) = y := by rw [translation_apply, sub_add_cancel]
    refine ⟨hk, hyS, precomp (translation q) (differentiableOn_translation q)
      (differentiableOn_translation_symm q) hc hTc Φ, subset_univ _, ?_, ?_⟩
    · change Φ.toFun (translation q (y - q)) = 0
      rw [hTc]
      exact hΦ0
    · intro w _ hw
      change w ∈ (translation q).source ∩ translation q ⁻¹' Φ.source at hw
      change w ∈ S ↔ Φ.toFun (translation q w) ∈ complexCoordinatePlane n k
      have h := hflat (y := w + q) (mem_univ _) hw.2
      rw [mem_ofPred_eq, add_sub_cancel_right] at h
      exact h
  · rintro ⟨hk, hyS, Ψ, -, hΨ0, hflat⟩
    have hc : y ∈ (translation (-q)).source := mem_univ _
    have hTc : translation (-q) y = y - q := by rw [translation_apply, sub_eq_add_neg]
    refine ⟨hk, hyS, precomp (translation (-q)) (differentiableOn_translation (-q))
      (differentiableOn_translation_symm (-q)) hc hTc Ψ, subset_univ _, ?_, ?_⟩
    · change Ψ.toFun (translation (-q) y) = 0
      rw [hTc]
      exact hΨ0
    · intro w _ hw
      change w ∈ (translation (-q)).source ∩ translation (-q) ⁻¹' Ψ.source at hw
      change w - q ∈ S ↔ Ψ.toFun (translation (-q) w) ∈ complexCoordinatePlane n k
      have hw2 : w - q ∈ Ψ.source := by
        have := hw.2
        rwa [mem_preimage, translation_apply, ← sub_eq_add_neg] at this
      have h := hflat (y := w - q) (mem_univ _) hw2
      rw [translation_apply, ← sub_eq_add_neg]
      exact h

namespace LocalDecomposition

/-- Transport of local decomposition data along an equality of sets. -/
def congrSet {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    {A A' : Set M} {p : M} (h : A = A')
    (D : LocalDecomposition (n := n) A p) : LocalDecomposition (n := n) A' p :=
  h ▸ D

/-- **Translation of local decomposition data in the model space.** -/
def translate {S : Set (ComplexModel n)} (D : LocalDecomposition (n := n) (M := ComplexModel n)
    S 0)
    (q : ComplexModel n) :
    LocalDecomposition (n := n) (M := ComplexModel n) {z | z - q ∈ S} q where
  nbhd := {z | z - q ∈ D.nbhd}
  isOpen_nbhd := D.isOpen_nbhd.preimage (continuous_id.sub continuous_const)
  mem_nbhd := by simpa using D.mem_nbhd
  nbhd_subset_source := fun _ _ => mem_univ _
  count := D.count
  piece i := {z | z - q ∈ D.piece i}
  dim := D.dim
  eqnCount := D.eqnCount
  eqn i j := fun z => D.eqn i j (z - q)
  eqn_holomorphic i j := by
    refine (D.eqn_holomorphic i j).comp (differentiable_id.sub_const q).differentiableOn ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z - q, hz, rfl⟩
  piece_subset i := fun z hz => D.piece_subset i hz
  mem_piece_iff i y hy := D.mem_piece_iff i (y - q) hy
  inter_nbhd_eq := by
    ext z
    have h := congrArg (fun T : Set (ComplexModel n) => z - q ∈ T) D.inter_nbhd_eq
    simpa using h
  eq_dim_of_regularAtDim i {y k} hy :=
    D.eq_dim_of_regularAtDim i ((regularAtDim_translate_iff q y).mp hy)
  subset_closure_regularLocus i := by
    intro y hy
    have h := D.subset_closure_regularLocus i hy
    have hset : regularLocus (n := n) (M := ComplexModel n) {z | z - q ∈ D.piece i} (D.dim i) =
        (fun z => z - q) ⁻¹' regularLocus (n := n) (M := ComplexModel n) (D.piece i) (D.dim i)
          := by
      ext z
      exact regularAtDim_translate_iff q z
    rw [hset]
    have hhomeo := (Homeomorph.subRight q).preimage_closure
      (regularLocus (n := n) (M := ComplexModel n) (D.piece i) (D.dim i))
    have e1 : ((Homeomorph.subRight q : ComplexModel n ≃ₜ ComplexModel n) :
        ComplexModel n → ComplexModel n) = fun z => z - q := rfl
    rw [e1] at hhomeo
    rw [← hhomeo]
    exact h
  exists_mem_not_mem i l hil O hO hne := by
    obtain ⟨y, hyO, hyi⟩ := hne
    have hO' : IsOpen ((fun w => w + q) ⁻¹' O) := hO.preimage (continuous_id.add continuous_const)
    obtain ⟨w, ⟨hwO, hwi⟩, hwl⟩ := D.exists_mem_not_mem i l hil _ hO'
      ⟨y - q, by simpa using hyO, hyi⟩
    exact ⟨w + q, ⟨hwO, by simpa using hwi⟩, by simpa using hwl⟩

end LocalDecomposition

theorem isIrreducibleGerm_congr {A B : Set (ComplexModel n)} (hA : IsIrreducibleGerm A)
    (hAB : A =ᶠ[𝓝 0] B) : IsIrreducibleGerm B := by
  obtain ⟨hAn, hne, hirr⟩ := hA
  refine ⟨hAn.congr hAB, fun h => hne (hAB.trans h), fun C D hC hD hBCD => ?_⟩
  rcases hirr C D hC hD (hAB.trans hBCD) with h | h
  · exact Or.inl (hAB.symm.trans h)
  · exact Or.inr (hAB.symm.trans h)

/-- **(LS) at the origin of the model space.** -/
theorem exists_localDecomposition_zero {S : Set (ComplexModel n)} (hS : IsAnalyticGerm S) :
    Nonempty (LocalDecomposition (n := n) (M := ComplexModel n) S 0) := by
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
  exact ⟨{
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
      exact ⟨y, ⟨hyO, hyi, hyΩ⟩, fun h => hyl h.1⟩ }⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **The local statement (LS).**  Every point of an analytic subset of a complex manifold has
local decomposition data.  Blueprint `lag:local-statement`; the remaining inputs are
`IrreducibleGermLocal.exists_pure_nhds` and `IrreducibleGermLocal.exists_thin_nhds`. -/
theorem exists_localDecomposition {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    {p : M} (_hp : p ∈ A) : Nonempty (LocalDecomposition (n := n) A p) := by
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
  obtain ⟨D₀⟩ := exists_localDecomposition_zero hS
  have hset : {z | z - q ∈ S} = e.target ∩ e.symm ⁻¹' A := by
    ext z
    simp [S]
  exact ⟨LocalDecomposition.ofChart ((D₀.translate q).congrSet hset)⟩

end

end SGPT.Foundations.Analysis.Pending.AnalyticLocalStatement
