/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalStatementAssembly
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.RegularLocusDense
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.AnalyticSubsetTopology
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.RegularPointDimension

/-!
# Dimension strata and pure dimensionality of irreducible analytic sets

Blueprint `ana:dimension-strata`, `ana:pure-dimension` (Demailly, *Complex analytic and
differential geometry*, II.5.3).

For an analytic subset `A` of a complex manifold and a predicate `P` on dimensions, let
`S_P = ⋃_{P j} R_j`, where `R_j` is the set of regular points of `A` of dimension `j`.

* `closure_inter_nbhd_eq`: given local decomposition data (LS) at `p`
  (`AnalyticLocalStatement.LocalDecomposition`), `closure S_P ∩ W = ⋃_{P dᵢ} Aᵢ` on the
  neighbourhood `W`.  If `x ∈ R_j`, `P j`, lies in `W`, then near a point of `A` close to `x`
  the set `A` coincides with a single piece `Aᵢ` (a finite union of relatively closed sets
  has a member with interior), and regularity there forces `j = dᵢ`.  Conversely a
  `dᵢ`-regular point of `Aᵢ` off the other pieces is a `dᵢ`-regular point of `A`, and such
  points are dense in `Aᵢ`.
* `isComplexAnalyticSubset_closure_regularStratum`: `closure S_P` is analytic (a finite
  union of zero sets near points of `A`, empty near other points).
* `eq_dim_of_regularAtDim`: an irreducible analytic subvariety is pure-dimensional.  With
  `m = dim V`, `V = closure S_{= m} ∪ closure S_{≠ m}` by density of the regular locus;
  irreducibility and `R_m ≠ ∅` force `V = closure S_{= m}`, and a regular point of dimension
  `k` has a neighbourhood containing only `k`-dimensional regular points.

The only open input is the local statement `AnalyticLocalStatement.exists_localDecomposition`.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.PureDimension

open FirstPass AnalyticLocalStatement RegularPointDimension

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The regular points of `A` whose dimension satisfies `P`. -/
def regularStratum (A : Set M) (P : ℕ → Prop) : Set M :=
  ⋃ j, ⋃ (_ : P j), regularLocus (n := n) A j

omit [IsComplexManifold n M] in
theorem mem_regularStratum {A : Set M} {P : ℕ → Prop} {x : M} :
    x ∈ regularStratum (n := n) A P ↔ ∃ j, P j ∧ RegularAtDim (n := n) A x j := by
  simp [regularStratum]

omit [IsComplexManifold n M] in
theorem regularStratum_subset (A : Set M) (P : ℕ → Prop) :
    regularStratum (n := n) A P ⊆ A := by
  intro x hx
  obtain ⟨j, -, hj⟩ := mem_regularStratum.mp hx
  exact hj.2.1

end

end SGPT.Foundations.Analysis.Pending.PureDimension

namespace SGPT.Foundations.Analysis.Pending.AnalyticLocalStatement.LocalDecomposition

open FirstPass PureDimension RegularPointDimension

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

variable {A : Set M} {p : M} (D : LocalDecomposition (n := n) A p)

omit [IsComplexManifold n M] in
theorem piece_subset_inter (i : Fin D.count) : D.piece i ⊆ A ∩ D.nbhd := by
  intro y hy
  have : y ∈ ⋃ i, D.piece i := mem_iUnion.mpr ⟨i, hy⟩
  rwa [← D.inter_nbhd_eq] at this

omit [IsComplexManifold n M] in
/-- Each piece is relatively closed in the neighbourhood. -/
theorem isOpen_nbhd_diff_piece (i : Fin D.count) : IsOpen (D.nbhd \ D.piece i) := by
  set e := (complexChartAt (n := n) p).val with he
  have hopen : IsOpen (e '' D.nbhd) := e.isOpen_image_of_subset_source D.isOpen_nbhd
    D.nbhd_subset_source
  refine isOpen_iff_mem_nhds.mpr fun y hy => ?_
  obtain ⟨j, hj⟩ : ∃ j, D.eqn i j (e y) ≠ 0 := by
    by_contra h
    push Not at h
    exact hy.2 ((D.mem_piece_iff i y hy.1).mpr h)
  have hcont : ContinuousAt (fun z => D.eqn i j (e z)) y := by
    have h1 : ContinuousAt (D.eqn i j) (e y) :=
      ((D.eqn_holomorphic i j).continuousOn).continuousAt
        (hopen.mem_nhds (mem_image_of_mem e hy.1))
    exact h1.comp (e.continuousAt (D.nbhd_subset_source hy.1))
  filter_upwards [D.isOpen_nbhd.mem_nhds hy.1, hcont.eventually_ne hj] with z hz hzj
  exact ⟨hz, fun hzi => hzj ((D.mem_piece_iff i z hz).mp hzi j)⟩

omit [IsComplexManifold n M] in
/-- Near a point of `A ∩ W`, some nonempty relatively open part of `A` lies in one piece. -/
theorem exists_isOpen_subset_piece {O : Set M} (hO : IsOpen O) {y : M} (hyO : y ∈ O)
    (hyA : y ∈ A) (hyW : y ∈ D.nbhd) :
    ∃ i, ∃ O' : Set M, IsOpen O' ∧ O' ⊆ O ∧ (O' ∩ A).Nonempty ∧ O' ∩ A ⊆ D.piece i := by
  by_contra hcon
  push Not at hcon
  have key : ∀ m ≤ D.count, ∃ O' : Set M, IsOpen O' ∧ O' ⊆ O ∩ D.nbhd ∧ (O' ∩ A).Nonempty ∧
      ∀ i : Fin D.count, i.val < m → O' ∩ D.piece i = ∅ := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨O ∩ D.nbhd, hO.inter D.isOpen_nbhd, subset_rfl, ⟨y, ⟨hyO, hyW⟩, hyA⟩,
        fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ m ih =>
      intro hm
      obtain ⟨O', hO', hO'sub, hne, hdisj⟩ := ih (Nat.le_of_succ_le hm)
      obtain ⟨z, ⟨hzO', hzA⟩, hzi⟩ := not_subset.mp
        (hcon ⟨m, hm⟩ O' hO' (hO'sub.trans inter_subset_left) hne)
      refine ⟨O' ∩ (D.nbhd \ D.piece ⟨m, hm⟩), hO'.inter (D.isOpen_nbhd_diff_piece _),
        inter_subset_left.trans hO'sub, ⟨z, ⟨hzO', (hO'sub hzO').2, hzi⟩, hzA⟩, ?_⟩
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · exact subset_empty_iff.mp ((inter_subset_inter_left _ inter_subset_left).trans
          (hdisj i hlt).subset)
      · have hi' : i = ⟨m, hm⟩ := Fin.ext heq
        subst hi'
        exact eq_empty_iff_forall_notMem.mpr fun w hw => hw.1.2.2 hw.2
  obtain ⟨O', -, hO'sub, ⟨z, hzO', hzA⟩, hdisj⟩ := key D.count le_rfl
  have hz : z ∈ ⋃ i, D.piece i := by
    rw [← D.inter_nbhd_eq]
    exact ⟨hzA, (hO'sub hzO').2⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hz
  have := hdisj i i.isLt
  exact (eq_empty_iff_forall_notMem.mp this) z ⟨hzO', hi⟩

omit [IsComplexManifold n M] in
/-- Inside any open set meeting a piece there is a point of that piece, with an open
neighbourhood missing all other pieces. -/
theorem exists_isOpen_disjoint_others (i : Fin D.count) {O : Set M} (hO : IsOpen O)
    (hne : (O ∩ D.piece i).Nonempty) :
    ∃ O' : Set M, IsOpen O' ∧ O' ⊆ O ∧ (O' ∩ D.piece i).Nonempty ∧
      ∀ l, l ≠ i → O' ∩ D.piece l = ∅ := by
  have key : ∀ m, ∃ O' : Set M, IsOpen O' ∧ O' ⊆ O ∧ (O' ∩ D.piece i).Nonempty ∧
      ∀ l : Fin D.count, l.val < m → l ≠ i → O' ∩ D.piece l = ∅ := by
    intro m
    induction m with
    | zero => exact ⟨O, hO, subset_rfl, hne, fun l hl => absurd hl (Nat.not_lt_zero _)⟩
    | succ m ih =>
      obtain ⟨O', hO', hO'sub, hne', hdisj⟩ := ih
      by_cases hm : m < D.count
      · by_cases hmi : (⟨m, hm⟩ : Fin D.count) = i
        · refine ⟨O', hO', hO'sub, hne', fun l hl hli => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hlt | heq
          · exact hdisj l hlt hli
          · exact absurd (hmi ▸ Fin.ext heq) hli
        · obtain ⟨z, ⟨hzO', hzi⟩, hzl⟩ :=
            D.exists_mem_not_mem i ⟨m, hm⟩ (Ne.symm hmi) O' hO' hne'
          refine ⟨O' ∩ (D.nbhd \ D.piece ⟨m, hm⟩), hO'.inter (D.isOpen_nbhd_diff_piece _),
            inter_subset_left.trans hO'sub, ⟨z, ⟨hzO', D.piece_subset i hzi, hzl⟩, hzi⟩, ?_⟩
          intro l hl hli
          rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hlt | heq
          · exact subset_empty_iff.mp ((inter_subset_inter_left _ inter_subset_left).trans
              (hdisj l hlt hli).subset)
          · have hl' : l = ⟨m, hm⟩ := Fin.ext heq
            subst hl'
            exact eq_empty_iff_forall_notMem.mpr fun w hw => hw.1.2.2 hw.2
      · refine ⟨O', hO', hO'sub, hne', fun l hl hli => ?_⟩
        exact hdisj l (lt_of_lt_of_le l.isLt (not_lt.mp hm)) hli
  obtain ⟨O', hO', hO'sub, hne', hdisj⟩ := key D.count
  exact ⟨O', hO', hO'sub, hne', fun l hli => hdisj l l.isLt hli⟩

/-- **The strata near `p`.**  On the neighbourhood of the decomposition, the closure of the
regular points with dimension in `P` is the union of the pieces with dimension in `P`. -/
theorem closure_inter_nbhd_eq (P : ℕ → Prop) :
    closure (regularStratum (n := n) A P) ∩ D.nbhd = ⋃ i, ⋃ (_ : P (D.dim i)), D.piece i := by
  apply Subset.antisymm
  · rintro x ⟨hxcl, hxW⟩
    by_contra hxF
    set U := D.nbhd \ ⋃ i, ⋃ (_ : P (D.dim i)), D.piece i with hU
    have hUeq : U = D.nbhd ∩ ⋂ i, ⋂ (_ : P (D.dim i)), (D.nbhd \ D.piece i) := by
      ext z
      simp only [hU, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion,
        not_exists]
      exact ⟨fun h => ⟨h.1, fun i hi => ⟨h.1, h.2 i hi⟩⟩, fun h => ⟨h.1, fun i hi => (h.2 i hi).2⟩⟩
    have hUopen : IsOpen U := by
      rw [hUeq]
      exact D.isOpen_nbhd.inter (isOpen_iInter_of_finite fun i =>
        isOpen_iInter_of_finite fun _ => D.isOpen_nbhd_diff_piece i)
    obtain ⟨y, hyU, hyS⟩ := mem_closure_iff.mp hxcl U hUopen ⟨hxW, hxF⟩
    obtain ⟨j, hPj, hyj⟩ := mem_regularStratum.mp hyS
    obtain ⟨O, hOsub, hO, hyO⟩ := mem_nhds_iff.mp
      ((RegularPatchNeighborhood.eventually_regularAtDim hyj).and (hUopen.mem_nhds hyU))
    obtain ⟨i, O', hO', hO'sub, ⟨z, hzO', hzA⟩, hsub⟩ :=
      D.exists_isOpen_subset_piece hO hyO hyj.2.1 hyU.1
    have hzreg : RegularAtDim (n := n) A z j := (hOsub (hO'sub hzO')).1 hzA
    have hAO' : A ∩ O' = D.piece i ∩ O' := by
      apply Subset.antisymm
      · intro w hw
        exact ⟨hsub ⟨hw.2, hw.1⟩, hw.2⟩
      · intro w hw
        exact ⟨(D.piece_subset_inter i hw.1).1, hw.2⟩
    have hzi : RegularAtDim (n := n) (D.piece i) z j :=
      regularAtDim_of_inter_eq hO' hzO' hAO' hzreg
    have hji := D.eq_dim_of_regularAtDim i hzi
    have hzF : z ∈ ⋃ i, ⋃ (_ : P (D.dim i)), D.piece i :=
      mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hji ▸ hPj, hzi.2.1⟩⟩
    exact (hOsub (hO'sub hzO')).2.2 hzF
  · intro x hx
    obtain ⟨i, hx⟩ := mem_iUnion.mp hx
    obtain ⟨hPi, hxi⟩ := mem_iUnion.mp hx
    refine ⟨mem_closure_iff.mpr fun O hO hxO => ?_, D.piece_subset i hxi⟩
    obtain ⟨z, hzO, hzreg⟩ := mem_closure_iff.mp (D.subset_closure_regularLocus i hxi) O hO hxO
    obtain ⟨O₁, hO₁sub, hO₁, hzO₁⟩ := mem_nhds_iff.mp
      ((RegularPatchNeighborhood.eventually_regularAtDim hzreg).and
        ((hO.inter D.isOpen_nbhd).mem_nhds ⟨hzO, D.piece_subset i hzreg.2.1⟩))
    obtain ⟨O', hO', hO'sub, ⟨w, hwO', hwi⟩, hdisj⟩ :=
      D.exists_isOpen_disjoint_others i hO₁ ⟨z, hzO₁, hzreg.2.1⟩
    have hwreg : RegularAtDim (n := n) (D.piece i) w (D.dim i) := (hO₁sub (hO'sub hwO')).1 hwi
    have hAO' : D.piece i ∩ O' = A ∩ O' := by
      apply Subset.antisymm
      · intro v hv
        exact ⟨(D.piece_subset_inter i hv.1).1, hv.2⟩
      · intro v hv
        have hvW : v ∈ D.nbhd := (hO₁sub (hO'sub hv.2)).2.2
        have hv' : v ∈ ⋃ l, D.piece l := by
          rw [← D.inter_nbhd_eq]
          exact ⟨hv.1, hvW⟩
        obtain ⟨l, hl⟩ := mem_iUnion.mp hv'
        by_cases hli : l = i
        · exact ⟨hli ▸ hl, hv.2⟩
        · exact absurd ⟨hv.2, hl⟩ ((eq_empty_iff_forall_notMem.mp (hdisj l hli)) v)
    have hwA : RegularAtDim (n := n) A w (D.dim i) := regularAtDim_of_inter_eq hO' hwO' hAO' hwreg
    exact ⟨w, (hO₁sub (hO'sub hwO')).2.1, mem_regularStratum.mpr ⟨D.dim i, hPi, hwA⟩⟩

end

end SGPT.Foundations.Analysis.Pending.AnalyticLocalStatement.LocalDecomposition

namespace SGPT.Foundations.Analysis.Pending.PureDimension

open FirstPass AnalyticLocalStatement RegularPointDimension

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

omit [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- Finite products of holomorphic functions are holomorphic. -/
theorem differentiableOn_finset_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (u : Finset ι) (f : ι → E → ℂ) (s : Set E)
    (h : ∀ i ∈ u, DifferentiableOn ℂ (f i) s) :
    DifferentiableOn ℂ (fun z => ∏ i ∈ u, f i z) s := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [differentiableOn_const]
  | insert a u ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a u)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A presentation at a point off the closed set `A` of any subset of `A`. -/
theorem nonempty_presentation_of_not_mem {A S : Set M} (hA : IsClosed A) (hSA : S ⊆ A)
    {x : M} (hx : x ∉ A) : Nonempty (ComplexAnalyticPresentationAt (n := n) S x) := by
  have hsrc := mem_complexChartAt_source (n := n) x
  refine ⟨{ generatorCount := 1
            generator := fun _ _ => 1
            coordinateNeighborhood := (complexChartAt (n := n) x).val.target ∩
              (complexChartAt (n := n) x).val.symm ⁻¹' Aᶜ
            isOpen_coordinateNeighborhood :=
              (complexChartAt (n := n) x).val.isOpen_inter_preimage_symm hA.isOpen_compl
            center_mem_coordinateNeighborhood := ?_
            coordinateNeighborhood_subset_target := inter_subset_left
            generator_holomorphic := fun _ => differentiableOn_const 1
            zeroLocus := ?_ }⟩
  · refine ⟨(complexChartAt (n := n) x).val.map_source hsrc, ?_⟩
    change (complexChartAt (n := n) x).val.symm ((complexChartAt (n := n) x).val x) ∉ A
    rwa [(complexChartAt (n := n) x).val.left_inv hsrc]
  · intro y hy hyN
    have hyA : y ∉ A := by
      have h2 := hyN.2
      change (complexChartAt (n := n) x).val.symm ((complexChartAt (n := n) x).val y) ∉ A at h2
      rwa [(complexChartAt (n := n) x).val.left_inv hy] at h2
    constructor
    · intro hyS
      exact absurd (hSA hyS) hyA
    · intro h
      exact absurd (h 0) one_ne_zero

/-- A presentation at `p` of a set agreeing near `p` with a union of pieces of a local
decomposition. -/
theorem nonempty_presentation_of_inter_nbhd_eq {A S : Set M} {p : M}
    (D : LocalDecomposition (n := n) A p) (Q : Fin D.count → Prop)
    (hS : S ∩ D.nbhd = ⋃ i, ⋃ (_ : Q i), D.piece i) :
    Nonempty (ComplexAnalyticPresentationAt (n := n) S p) := by
  classical
  set e := (complexChartAt (n := n) p).val with he
  let ι := (i : {i // Q i}) → Fin (D.eqnCount i.1)
  let eqv := Fintype.equivFin ι
  let g : Fin (Fintype.card ι) → ComplexModel n → ℂ := fun c z =>
    ∏ i : {i // Q i}, D.eqn i.1 (eqv.symm c i) z
  have hopen : IsOpen (e '' D.nbhd) :=
    e.isOpen_image_of_subset_source D.isOpen_nbhd D.nbhd_subset_source
  refine ⟨{ generatorCount := Fintype.card ι
            generator := g
            coordinateNeighborhood := e '' D.nbhd
            isOpen_coordinateNeighborhood := hopen
            center_mem_coordinateNeighborhood := mem_image_of_mem e D.mem_nbhd
            coordinateNeighborhood_subset_target := ?_
            generator_holomorphic := ?_
            zeroLocus := ?_ }⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact e.map_source (D.nbhd_subset_source hy)
  · intro c
    exact differentiableOn_finset_prod _ _ _ fun (i : {i // Q i}) _ => D.eqn_holomorphic i.1 _
  · intro y hy hyN
    obtain ⟨y', hy'W, hy'y⟩ := hyN
    have hyW : y ∈ D.nbhd := by
      rwa [← e.injOn (D.nbhd_subset_source hy'W) hy hy'y]
    have hmem : y ∈ S ↔ ∃ i, Q i ∧ ∀ j, D.eqn i j (e y) = 0 := by
      have h1 : y ∈ S ↔ y ∈ S ∩ D.nbhd := ⟨fun h => ⟨h, hyW⟩, fun h => h.1⟩
      rw [h1, hS]
      simp only [mem_iUnion, exists_prop]
      exact exists_congr fun i => and_congr_right fun _ => D.mem_piece_iff i y hyW
    rw [hmem]
    constructor
    · rintro ⟨i, hQi, hi⟩ c
      exact Finset.prod_eq_zero (Finset.mem_univ ⟨i, hQi⟩) (hi _)
    · intro h
      by_contra hcon
      push Not at hcon
      have hch : ∀ i : {i // Q i}, ∃ j, D.eqn i.1 j (e y) ≠ 0 := fun i => hcon i.1 i.2
      choose c hc using hch
      have := h (eqv c)
      simp only [g, Equiv.symm_apply_apply] at this
      exact (Finset.prod_ne_zero_iff.mpr fun i _ => hc i) this

/-- **The dimension strata are analytic.** -/
theorem isComplexAnalyticSubset_closure_regularStratum {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (P : ℕ → Prop) :
    IsComplexAnalyticSubset (n := n) (closure (regularStratum (n := n) A P)) := by
  intro x
  by_cases hx : x ∈ A
  · obtain ⟨D⟩ := exists_localDecomposition (p := x) hA
    exact nonempty_presentation_of_inter_nbhd_eq D (fun i => P (D.dim i))
      (D.closure_inter_nbhd_eq P)
  · exact nonempty_presentation_of_not_mem hA.isClosed
      (closure_minimal (regularStratum_subset A P) hA.isClosed) hx

/-- A regular point of dimension `k` is not in the closure of the regular points of other
dimensions. -/
theorem not_mem_closure_regularStratum_ne {A : Set M} {x : M} {k : ℕ}
    (hx : RegularAtDim (n := n) A x k) :
    x ∉ closure (regularStratum (n := n) A (· ≠ k)) := by
  intro hcl
  obtain ⟨y, hy, hyS⟩ := mem_closure_iff_nhds.mp hcl _
    (RegularPatchNeighborhood.eventually_regularAtDim hx)
  obtain ⟨j, hjk, hyj⟩ := mem_regularStratum.mp hyS
  exact hjk (eq_of_regularAtDim hyj (hy hyj.2.1))

/-- **Irreducible analytic sets are pure-dimensional.** -/
theorem eq_dim_of_regularAtDim (V : ClosedIrreducibleAnalyticSubvariety n M) {x : M}
    {k : ℕ} (hx : RegularAtDim (n := n) V.carrier x k) : k = V.dim := by
  set A := V.carrier with hAdef
  set B := closure (regularStratum (n := n) A (· = V.dim)) with hB
  set C := closure (regularStratum (n := n) A (· ≠ V.dim)) with hC
  have hBA : B ⊆ A := closure_minimal (regularStratum_subset A _) V.isClosed_carrier
  have hCA : C ⊆ A := closure_minimal (regularStratum_subset A _) V.isClosed_carrier
  have hABC : A = B ∪ C := by
    refine Subset.antisymm ?_ (union_subset hBA hCA)
    intro y hy
    have hy' := RegularLocusDense.subset_closure_iUnion_regularLocus V.analytic hy
    have hsplit : (⋃ j, regularLocus (n := n) A j) =
        regularStratum (n := n) A (· = V.dim) ∪ regularStratum (n := n) A (· ≠ V.dim) := by
      ext z
      simp only [mem_iUnion, mem_union, mem_regularStratum, mem_regularLocus]
      constructor
      · rintro ⟨j, hj⟩
        by_cases hjm : j = V.dim
        · exact Or.inl ⟨j, hjm, hj⟩
        · exact Or.inr ⟨j, hjm, hj⟩
      · rintro (⟨j, -, hj⟩ | ⟨j, -, hj⟩) <;> exact ⟨j, hj⟩
    rwa [hsplit, closure_union] at hy'
  obtain ⟨x₀, hx₀⟩ := V.regularLocus_nonempty
  rcases V.irreducible_carrier.eq_left_or_eq_right
      (isComplexAnalyticSubset_closure_regularStratum V.analytic _)
      (isComplexAnalyticSubset_closure_regularStratum V.analytic _) hBA hCA hABC with hAB | hAC
  · by_contra hkm
    have hxB : x ∈ B := by rw [hB, ← hAB]; exact hx.2.1
    have hmono : B ⊆ closure (regularStratum (n := n) A (· ≠ k)) := by
      refine closure_mono fun z hz => ?_
      obtain ⟨j, hj, hzj⟩ := mem_regularStratum.mp hz
      exact mem_regularStratum.mpr ⟨j, fun hjk => hkm (hjk ▸ hj), hzj⟩
    exact not_mem_closure_regularStratum_ne hx (hmono hxB)
  · have hx₀C : x₀ ∈ C := by rw [hC, ← hAC]; exact hx₀.2.1
    exact absurd hx₀C (not_mem_closure_regularStratum_ne hx₀)

end

end SGPT.Foundations.Analysis.Pending.PureDimension
