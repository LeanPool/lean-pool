/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Whitney.BadSetDefinitions
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Whitney.KuhnCells
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Whitney.PartitionCovering

/-!
# SimplexPartition

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `d.simplex.partition`: the simplicial refinement `SW(□_m)` of `W(□_m)`

This module defines a local implementation of ABK26's `e.SW.def`, the paragraph
"The simplex partition" of `sss.affine.approximation`:

* the layer-`n` simplex scale `m − (n+1) − h_{n+1}` (`simplexScale`),
  equivalently the refinement depth `1 + (h_{n+1} − h_n)` below the layer-`n`
  cube;
* the layer-`n` cell family `S_{m−(n+1)−h_{n+1}}(□)` of one Whitney cube
  (`whitneySimplexCells`), with the printed cardinality
  `3^{d(1 + h_{n+1} − h_n)} · d!` and the printed size `3^{m−(n+1)−h_{n+1}}`;
* the simplex partition `SW(□_m) = ⋃_n ⋃_{□ ∈ W(□_m,n)} S_{m−(n+1)−h_{n+1}}(□)`
  (`simplexPartition`) and its membership characterization;
* the printed observation that a layer-`n` simplex has exactly the
  layer-`(n+1)` cube size is not recorded here but in
  `Affine.CommonCoarseMesh`, as
  `scale_eq_simplexScale_of_mem_whitneyLayer_succ`;
* exactness: the cells of `SW(□_m)` are pairwise disjoint and their union is
  the union of the Whitney cubes (`simplexPartition_pairwiseDisjoint`,
  `iUnion_carrier_simplexPartition`); composed with the proved Whitney covering
  of `PartitionCovering` this is the partition of the (open) root cube,
  `iUnion_carrier_simplexPartition_eq_openCubeSet`.  This *will* support the
  measure splitting of `p.bfA.multiscalebound` once the volume layer proves:
  that consumer needs, in addition, measurability of the cells and the volume
  facts (`|△_n^π| = 3^{dn}/d!`, hence the per-simplex refinement count), none
  of which is proved here.

## Compatibility scope

The manuscript infers from the size identity that `SW(□_m)` is a "valid
simplicial partition" with compatible adjacent sizes.  `SW(□_m)` therefore has
hanging vertices, and

> **this module makes no global face-to-face claim, and no downstream statement
> proved here needs one.**

Complete-face compatibility needs **two** ingredients, not one: the
nested-refinement lemma (proved here) *and* a face-alignment lemma for
equal-scale adjacent cubes, which is
`Provider/Affine/KuhnFaceAlignment.lean`'s
`closedCarrier_inter_subset_commonClosedFace`.

The independent overlap defect (neighborhoods of distinct bad components are
not disjoint) is untouched by this module: no statement below asserts or uses
disjointness of component neighborhoods, and the cell interface is
component-free, so the overlap-aware consumer statements remain available.

## References

* ABK26, `e.SW.def`; `e.simplex.def`.
-/

namespace Algsuperdiff.Section3.Provider.Whitney

open HCPolySupport

noncomputable section

variable {d : ℕ}

/-! ## The layer-dependent simplex scale -/

/-- **The simplex scale of `e.SW.def`**: a layer-`n` Whitney cube is decomposed
into simplices of size `3^{m-(n+1)-h_{n+1}}`. -/
def simplexScale (m : ℤ) (hn : ℕ → ℕ) (n : ℕ) : ℤ :=
  m - ((n : ℤ) + 1) - (hn (n + 1) : ℤ)

/-- The layer-`n` simplex scale is at most the layer-`n` cube scale, so the
decomposition of a layer-`n` cube is nonempty.  Uses only `h_n ≤ h_{n+1} + 1`. -/
theorem simplexScale_le_scale_of_mem_whitneyLayer {m : ℤ} {hn : ℕ → ℕ} {n : ℕ}
    (hstep : hn n ≤ hn (n + 1) + 1) {Q : TriadicCube d}
    (hQ : Q ∈ whitneyLayer m hn n) : simplexScale m hn n ≤ Q.scale := by
  rw [scale_eq_of_mem_whitneyLayer hQ, simplexScale]
  omega

/-! ## The cells of one Whitney cube -/

/-- **`S_{m-(n+1)-h_{n+1}}(□)`**: the simplices refining a layer-`n` Whitney cube. -/
def whitneySimplexCells (m : ℤ) (hn : ℕ → ℕ) (n : ℕ) (Q : TriadicCube d) :
    Finset (KuhnCell d) :=
  triadicSimplexPartition Q (simplexScale m hn n)

theorem mem_whitneySimplexCells_iff {m : ℤ} {hn : ℕ → ℕ} {n : ℕ}
    {Q : TriadicCube d} {T : KuhnCell d} :
    T ∈ whitneySimplexCells m hn n Q ↔
      T.supportCube ∈ descendantsAtScale Q (simplexScale m hn n) :=
  mem_triadicSimplexPartition_iff

private theorem cubeSet_subset_of_mem_descendantsAtScale {Q R : TriadicCube d}
    {j : ℤ} (h : R ∈ descendantsAtScale Q j) : cubeSet R ⊆ cubeSet Q := by
  by_cases hj : j ≤ Q.scale
  · rw [descendantsAtScale_eq_descendantsAtDepth Q hj] at h
    exact cubeSet_subset_of_mem_descendantsAtDepth h
  · rw [descendantsAtScale_eq_empty Q (by omega)] at h
    exact absurd h (Finset.notMem_empty _)

/-- Every cell of the layer-`n` decomposition sits inside its Whitney cube.  This
is the containment used. -/
theorem carrier_subset_cubeSet_of_mem_whitneySimplexCells {m : ℤ} {hn : ℕ → ℕ}
    {n : ℕ} {Q : TriadicCube d} {T : KuhnCell d}
    (hT : T ∈ whitneySimplexCells m hn n Q) : T.carrier ⊆ cubeSet Q :=
  T.carrier_subset_cubeSet.trans
    (cubeSet_subset_of_mem_descendantsAtScale (mem_whitneySimplexCells_iff.mp hT))

/-- The cells of one layer-`n` cube tile it exactly. -/
theorem cubeSet_eq_iUnion_whitneySimplexCells {m : ℤ} {hn : ℕ → ℕ} {n : ℕ}
    (hstep : hn n ≤ hn (n + 1) + 1) {Q : TriadicCube d}
    (hQ : Q ∈ whitneyLayer m hn n) :
    cubeSet Q =
      ⋃ T ∈ (whitneySimplexCells m hn n Q : Set (KuhnCell d)), T.carrier :=
  cubeSet_eq_iUnion_triadicSimplexPartition Q
    (simplexScale_le_scale_of_mem_whitneyLayer hstep hQ)

/-! ## The simplex partition `SW(□_m)` -/

/-- **ABK26 `e.SW.def`**: the simplex partition `SW(□_m) = ⋃_{n ∈ ℕ} ⋃_{□ ∈ W(□_m,
n)} S_{m-(n+1)-h_{n+1}}(□)`. -/
def simplexPartition (m : ℤ) (hn : ℕ → ℕ) : Set (KuhnCell d) :=
  {T | ∃ n : ℕ, ∃ Q ∈ whitneyLayer m hn n, T ∈ whitneySimplexCells m hn n Q}

theorem mem_simplexPartition_iff {m : ℤ} {hn : ℕ → ℕ} {T : KuhnCell d} :
    T ∈ simplexPartition m hn ↔
      ∃ n : ℕ, ∃ Q ∈ whitneyLayer m hn n, T ∈ whitneySimplexCells m hn n Q :=
  Iff.rfl

theorem mem_simplexPartition_of_mem_whitneySimplexCells {m : ℤ} {hn : ℕ → ℕ}
    {n : ℕ} {Q : TriadicCube d} (hQ : Q ∈ whitneyLayer m hn n) {T : KuhnCell d}
    (hT : T ∈ whitneySimplexCells m hn n Q) : T ∈ simplexPartition m hn :=
  ⟨n, Q, hQ, hT⟩

/-! ## Disjointness of the Whitney cubes -/

private theorem cubeCenter_mem_cubeSet (Q : TriadicCube d) :
    cubeCenter Q ∈ cubeSet Q := by
  have hs : (0 : ℝ) < cubeScaleFactor Q := zpow_pos (by norm_num) _
  intro i
  simp only [cubeCenter]
  constructor <;> nlinarith

private theorem eq_of_common_subcube {P A B R : TriadicCube d} {t : ℕ}
    (hA : A ∈ descendantsAtDepth P t) (hB : B ∈ descendantsAtDepth P t)
    (hRA : cubeSet R ⊆ cubeSet A) (hRB : cubeSet R ⊆ cubeSet B) : A = B := by
  by_contra hne
  have hdisj := pairwiseDisjoint_descendantsAtDepth P t hA hB hne
  exact Set.disjoint_left.mp hdisj (hRA (cubeCenter_mem_cubeSet R))
    (hRB (cubeCenter_mem_cubeSet R))

/-- A deeper Whitney cube is never a triadic descendant of a shallower one: the
layer-`n'` construction forces every ancestor at depth `n' - 1` to touch
`∂□_m`, while the layer-`n` cube already sits inside a non-touching child at
depth `n`. -/
private theorem not_descendant_of_mem_whitneyLayer_lt {m : ℤ} {hn : ℕ → ℕ}
    {n n' : ℕ} (hlt : n < n') {Q R : TriadicCube d}
    (hQ : Q ∈ whitneyLayer m hn n) (hR : R ∈ whitneyLayer m hn n') {k : ℕ}
    (hRQ : R ∈ descendantsAtDepth Q k) : False := by
  obtain ⟨hn1, A, hA, _, C, hC, hCnt, hQC⟩ := mem_whitneyLayer_iff.mp hQ
  obtain ⟨_, A', hA', hAt', C', hC', _, hRC'⟩ := mem_whitneyLayer_iff.mp hR
  have hCA : C ∈ descendantsAtDepth A 1 := by
    simpa only [descendantsAtDepth_one] using hC
  have hCroot : C ∈ descendantsAtDepth (originCube d m) n := by
    have h := mem_descendantsAtDepth_add hA hCA
    simpa only [show n - 1 + 1 = n from by omega] using h
  have hCscale : C.scale = m - (n : ℤ) := by
    have h := scale_eq_sub_of_mem_descendantsAtDepth hCroot
    simpa only [originCube] using h
  -- `R` descends from `C`
  have hRC : R ∈ descendantsAtDepth C (hn n + k) := mem_descendantsAtDepth_add hQC hRQ
  -- the depth-`n` ancestor of `A'` is `C`
  have hA'root : A' ∈ descendantsAtDepth (originCube d m) (n + (n' - 1 - n)) := by
    simpa only [show n + (n' - 1 - n) = n' - 1 from by omega] using hA'
  obtain ⟨U, hU, hA'U⟩ :=
    exists_descendant_ancestor_at_depth n (n' - 1 - n) hA'root
  have hC'A' : C' ∈ descendantsAtDepth A' 1 := by
    simpa only [descendantsAtDepth_one] using hC'
  have hRA' : R ∈ descendantsAtDepth A' (1 + hn n') := mem_descendantsAtDepth_add hC'A' hRC'
  have hRU : R ∈ descendantsAtDepth U ((n' - 1 - n) + (1 + hn n')) :=
    mem_descendantsAtDepth_add hA'U hRA'
  have hUC : U = C :=
    eq_of_common_subcube hU hCroot
      (cubeSet_subset_of_mem_descendantsAtDepth hRU)
      (cubeSet_subset_of_mem_descendantsAtDepth hRC)
  exact hCnt
    (touchesBoundary_of_mem_descendantsAtDepth (t := n) hCscale (hUC ▸ hA'U) hAt')

/-- **A Whitney cube belongs to exactly one layer.**  No hypothesis on the depth
profile `hn` is needed: this is the depth-`0` case of
`not_descendant_of_mem_whitneyLayer_lt`, i.e. the exit-depth argument run at the
cube itself (a cube is its own depth-`0` descendant). -/
private theorem layer_eq_of_mem_whitneyLayer {m : ℤ} {hn : ℕ → ℕ} {n n' : ℕ}
    {Q : TriadicCube d} (h : Q ∈ whitneyLayer m hn n)
    (h' : Q ∈ whitneyLayer m hn n') : n = n' := by
  have hself : Q ∈ descendantsAtDepth Q 0 := by
    simp only [descendantsAtDepth_zero, Finset.mem_singleton]
  rcases lt_trichotomy n n' with hlt | heq | hgt
  · exact absurd hself (fun hd => not_descendant_of_mem_whitneyLayer_lt hlt h h' hd)
  · exact heq
  · exact absurd hself (fun hd => not_descendant_of_mem_whitneyLayer_lt hgt h' h hd)

/-- **The Whitney cubes are pairwise disjoint.**  This is the cube-level input of
the exactness of `SW(□_m)`; it is not stated by `sss.whitney.partition` itself.
No hypothesis on the depth profile `hn` is needed: the statement is the proved
`whitneyPartition_pairwiseDisjoint_cubeSet` of `PartitionCovering`, whose
exit-depth proof is profile-free. -/
theorem disjoint_cubeSet_of_mem_whitneyPartition {m : ℤ} {hn : ℕ → ℕ}
    {Q R : TriadicCube d} (hQ : Q ∈ whitneyPartition m hn)
    (hR : R ∈ whitneyPartition m hn) (hne : Q ≠ R) :
    Disjoint (cubeSet Q) (cubeSet R) :=
  whitneyPartition_pairwiseDisjoint_cubeSet m hn hQ hR hne

/-! ## Exactness of `SW(□_m)` -/

/-- **The cells of `SW(□_m)` are pairwise disjoint.**  This is a partition
statement for the canonical half-open realizations; it is *not* a face-to-face
assertion (see the module docstring).  No hypothesis on the depth profile `hn`
is needed. -/
theorem simplexPartition_pairwiseDisjoint {m : ℤ} {hn : ℕ → ℕ} :
    (simplexPartition (d := d) m hn).PairwiseDisjoint KuhnCell.carrier := by
  intro T hT U hU hTU
  obtain ⟨n, Q, hQ, hTQ⟩ := hT
  obtain ⟨n', Q', hQ', hUQ⟩ := hU
  by_cases hQQ : Q = Q'
  · subst hQQ
    have hnn : n = n' := layer_eq_of_mem_whitneyLayer hQ hQ'
    subst hnn
    exact triadicSimplexPartition_pairwiseDisjoint Q (simplexScale m hn n) hTQ hUQ hTU
  · exact (disjoint_cubeSet_of_mem_whitneyPartition ⟨n, hQ⟩ ⟨n', hQ'⟩ hQQ).mono
      (carrier_subset_cubeSet_of_mem_whitneySimplexCells hTQ)
      (carrier_subset_cubeSet_of_mem_whitneySimplexCells hUQ)

/-- **`SW(□_m)` is an exact refinement of `W(□_m)`**: the canonical cells cover
exactly the Whitney cubes.  The Whitney covering `⋃_{□ ∈ W(□_m)} □ = □_m` is
proved (`openCubeSet_originCube_eq_iUnion_whitneyPartition`), so this composes
to the partition of the root cube:
`iUnion_carrier_simplexPartition_eq_openCubeSet`. -/
theorem iUnion_carrier_simplexPartition {m : ℤ} {hn : ℕ → ℕ}
    (hstep : ∀ n : ℕ, hn n ≤ hn (n + 1) + 1) :
    (⋃ T ∈ simplexPartition (d := d) m hn, T.carrier) =
      ⋃ Q ∈ whitneyPartition (d := d) m hn, cubeSet Q := by
  ext x
  constructor
  · intro hx
    obtain ⟨T, ⟨n, Q, hQ, hTQ⟩, hxT⟩ := by simpa only [Set.mem_iUnion] using hx
    exact Set.mem_iUnion.mpr
      ⟨Q, Set.mem_iUnion.mpr
        ⟨⟨n, hQ⟩, carrier_subset_cubeSet_of_mem_whitneySimplexCells hTQ hxT⟩⟩
  · intro hx
    obtain ⟨Q, ⟨n, hQ⟩, hxQ⟩ := by simpa only [Set.mem_iUnion] using hx
    rw [cubeSet_eq_iUnion_whitneySimplexCells (hstep n) hQ] at hxQ
    obtain ⟨T, hT, hxT⟩ := by simpa only [Set.mem_iUnion] using hxQ
    exact Set.mem_iUnion.mpr
      ⟨T, Set.mem_iUnion.mpr ⟨mem_simplexPartition_of_mem_whitneySimplexCells hQ hT, hxT⟩⟩

/-- **`SW(□_m)` tiles `□_m`**: the cells of the simplex partition cover the root
cube exactly.  Together with `simplexPartition_pairwiseDisjoint` this is the
partition-of-`□_m` statement; the carrier is the *open* root cube, which is the
manuscript's own `□_m` and the form forced by the termination clause of
`sss.whitney.partition` (see `PartitionCovering`).

This will support the measure splitting of `p.bfA.multiscalebound` once the
volume layer proves: that consumer needs, in addition, measurability of the
cells and the volume facts (`|△_n^π| = 3^{dn}/d!`, hence the per-simplex
refinement count), which are not proved here. -/
theorem iUnion_carrier_simplexPartition_eq_openCubeSet [NeZero d] {m : ℤ}
    {hn : ℕ → ℕ} (hstep : ∀ n : ℕ, hn n ≤ hn (n + 1) + 1) :
    (⋃ T ∈ simplexPartition (d := d) m hn, T.carrier) =
      openCubeSet (originCube d m) := by
  rw [iUnion_carrier_simplexPartition hstep,
    ← openCubeSet_originCube_eq_iUnion_whitneyPartition m hn]

end

end Algsuperdiff.Section3.Provider.Whitney
