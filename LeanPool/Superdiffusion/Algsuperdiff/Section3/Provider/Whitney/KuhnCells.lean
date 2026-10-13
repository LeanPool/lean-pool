/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Geometry.CubeMetric
public import LeanPool.HighContrastHomogenization.Support.Geometry.TriadicPartition
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Prod.Lex

/-!
# KuhnCells

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Triadic simplices and the standard simplicial decomposition `S_j(□)`

This module defines a local implementation of the simplex notation in ABK26's
"Triadic cubes and simplices" paragraph, which is the geometric input of
`e.SW.def`:

* the model ordered simplex and the triadic simplex `△_n^π(z)` of
  `e.simplex.def`;
* vertices `V(△)` and the fact that there are `d + 1` of them;
* the standard simplicial decomposition `S_j(□)` of a triadic cube into
  simplices of size `3^j`, together with its cardinality `3^{d(scale − j)} ·
  d!`, its exactness as a partition, and its nesting under further triadic
  subdivision.

## Carriers

A simplex is indexed by a `KuhnCell`: a triadic support cube together with a
permutation of the coordinates.  Its *open* realization `openCarrier` is the
manuscript's `△_n^π(z)` verbatim.  Because the open simplices of a cube omit
their common faces, an exact (rather than almost-everywhere) partition needs a
boundary convention; `carrier` is the canonical half-open realization obtained
by breaking coordinate ties with `Tuple.sort`.  `closedCarrier` is the closure.
The three are related by `openCarrier ⊆ carrier ⊆ closedCarrier`.

## Reading notes (recorded)

* The manuscript writes
  `S_n(z+□_m) = {z + △_n^π(z') : z' ∈ 3^n ℤ^d, △_n^π(z') ⊆ □_m}`.  Since the
  triadic grids are nested, `△_n^π(z') ⊆ □_m` selects exactly the scale-`n`
  triadic descendants of `□_m`; that is the indexing taken here
  (`descendantsAtScale`).  The condition `n ≤ m` of the display is carried as
  an explicit hypothesis where it is used; outside that range
  `triadicSimplexPartition` is empty, matching `descendantsAtScale`.
* No face-to-face or simplicial-complex claim is made here or anywhere
  downstream.

## References

* ABK26, (`e.simplex.def`).
-/

namespace Algsuperdiff.Section3.Provider.Whitney

open HCPolySupport

noncomputable section

variable {d : ℕ}

/-! ## The model ordered simplex -/

/-- The model open simplex of `e.simplex.def`: `{x ∈ ℝ^d: -1/2 < x_{π(1)} < ⋯ <
x_{π(d)} < 1/2}`, written as the conjunction of the coordinate box and the
`π`-ordering.  `mem_orderedUnitSimplex_iff_chain` shows this is the printed
chain. -/
def orderedUnitSimplex (pi : Equiv.Perm (Fin d)) : Set (Vec d) :=
  {x | (∀ i : Fin d, -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2) ∧
    ∀ i j : Fin d, i.val < j.val → x (pi i) < x (pi j)}

/-- **ABK26 `e.simplex.def`**: the triadic simplex of size `3^n` based at `z`,
`△_n^π(z) = z + 3^n · {x : -1/2 < x_{π(1)} < ⋯ < x_{π(d)} < 1/2}`. -/
def triadicSimplex (n : ℤ) (z : Vec d) (pi : Equiv.Perm (Fin d)) : Set (Vec d) :=
  (fun x : Vec d => z + (3 : ℝ) ^ n • x) '' orderedUnitSimplex pi

private theorem three_zpow_pos (n : ℤ) : (0 : ℝ) < (3 : ℝ) ^ n :=
  zpow_pos (by norm_num) n

/-- The translated/rescaled membership test for `△_n^π(z)`. -/
theorem mem_triadicSimplex_iff {n : ℤ} {z : Vec d} {pi : Equiv.Perm (Fin d)}
    {y : Vec d} :
    y ∈ triadicSimplex n z pi ↔
      (∀ i : Fin d, -(1 / 2 : ℝ) * (3 : ℝ) ^ n < y i - z i ∧
          y i - z i < (1 / 2 : ℝ) * (3 : ℝ) ^ n) ∧
        ∀ i j : Fin d, i.val < j.val → y (pi i) - z (pi i) < y (pi j) - z (pi j) := by
  have hpos := three_zpow_pos n
  constructor
  · rintro ⟨x, ⟨hbox, hord⟩, rfl⟩
    constructor
    · intro i
      have h := hbox i
      have hy : (z + (3 : ℝ) ^ n • x) i - z i = (3 : ℝ) ^ n * x i := by
        simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hy]
      constructor <;> nlinarith [h.1, h.2]
    · intro i j hij
      have h := hord i j hij
      have hy : ∀ k : Fin d, (z + (3 : ℝ) ^ n • x) k - z k = (3 : ℝ) ^ n * x k := by
        intro k
        simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hy, hy]
      nlinarith [h]
  · rintro ⟨hbox, hord⟩
    refine ⟨fun i => ((3 : ℝ) ^ n)⁻¹ * (y i - z i), ⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩
    · have h := hbox i
      show -(1 / 2 : ℝ) < ((3 : ℝ) ^ n)⁻¹ * (y i - z i) ∧
        ((3 : ℝ) ^ n)⁻¹ * (y i - z i) < 1 / 2
      rw [inv_mul_eq_div, lt_div_iff₀ hpos, div_lt_iff₀ hpos]
      exact ⟨h.1, h.2⟩
    · have h := hord i j hij
      show ((3 : ℝ) ^ n)⁻¹ * (y (pi i) - z (pi i)) <
        ((3 : ℝ) ^ n)⁻¹ * (y (pi j) - z (pi j))
      exact mul_lt_mul_of_pos_left h (inv_pos.2 hpos)
    · funext i
      have hne : ((3 : ℝ) ^ n) ≠ 0 := ne_of_gt hpos
      show z i + (3 : ℝ) ^ n * (((3 : ℝ) ^ n)⁻¹ * (y i - z i)) = y i
      rw [mul_inv_cancel_left₀ hne]
      ring

/-! ## Kuhn cells -/

/-- One triadic simplex, indexed by its support cube and the coordinate order
of `e.simplex.def`. -/
structure KuhnCell (d : ℕ) where
  /-- The triadic cube containing the simplex; its size is the simplex size. -/
  supportCube : TriadicCube d
  /-- The permutation `π` of `e.simplex.def`. -/
  order : Equiv.Perm (Fin d)
deriving DecidableEq

/-- Coordinates centered at the index point of a triadic cube. -/
def triadicLocalCoordinate (Q : TriadicCube d) (x : Vec d) (i : Fin d) : ℝ :=
  x i - (Q.index i : ℝ) * cubeScaleFactor Q

/-- The manuscript's open simplex `△_{scale}^{order}(center)` of a Kuhn cell. -/
def KuhnCell.openCarrier (T : KuhnCell d) : Set (Vec d) :=
  triadicSimplex T.supportCube.scale (cubeCenter T.supportCube) T.order

theorem KuhnCell.mem_openCarrier_iff {T : KuhnCell d} {x : Vec d} :
    x ∈ T.openCarrier ↔
      x ∈ openCubeSet T.supportCube ∧
        ∀ i j : Fin d, i.val < j.val →
          triadicLocalCoordinate T.supportCube x (T.order i) <
            triadicLocalCoordinate T.supportCube x (T.order j) := by
  rw [KuhnCell.openCarrier, mem_triadicSimplex_iff]
  constructor
  · rintro ⟨hbox, hord⟩
    refine ⟨fun i => ?_, hord⟩
    have h := hbox i
    simp only [cubeCenter, cubeScaleFactor] at h ⊢
    constructor <;> nlinarith [h.1, h.2]
  · rintro ⟨hbox, hord⟩
    refine ⟨fun i => ?_, hord⟩
    have h := hbox i
    simp only [cubeCenter, cubeScaleFactor] at h ⊢
    constructor <;> nlinarith [h.1, h.2]

theorem KuhnCell.openCarrier_subset_openCubeSet (T : KuhnCell d) :
    T.openCarrier ⊆ openCubeSet T.supportCube := fun _ hx =>
  (KuhnCell.mem_openCarrier_iff.mp hx).1

/-- The canonical half-open realization.  `Tuple.sort` assigns each coordinate
tie to exactly one cell, which turns the family of open simplices of a cube
into an exact partition of the half-open cube. -/
def KuhnCell.carrier (T : KuhnCell d) : Set (Vec d) :=
  {x | x ∈ cubeSet T.supportCube ∧
    T.order = Tuple.sort (triadicLocalCoordinate T.supportCube x)}

theorem KuhnCell.carrier_subset_cubeSet (T : KuhnCell d) :
    T.carrier ⊆ cubeSet T.supportCube := fun _ hx => hx.1

theorem KuhnCell.openCarrier_subset_carrier (T : KuhnCell d) :
    T.openCarrier ⊆ T.carrier := by
  intro x hx
  rw [KuhnCell.mem_openCarrier_iff] at hx
  refine ⟨openCubeSet_subset_cubeSet T.supportCube hx.1, ?_⟩
  refine (Tuple.eq_sort_iff (f := triadicLocalCoordinate T.supportCube x)
    (σ := T.order)).2 ⟨?_, ?_⟩
  · intro i j hij
    rcases eq_or_lt_of_le hij with rfl | hij
    · exact le_rfl
    · exact (hx.2 i j hij).le
  · intro i j hij heq
    exact absurd heq (ne_of_lt (hx.2 i j hij))

/-- The closed simplex: the closed support cube together with the weak
`order`-monotonicity of the local coordinates. -/
def KuhnCell.closedCarrier (T : KuhnCell d) : Set (Vec d) :=
  {x | x ∈ Metric.closedBall (cubeCenter T.supportCube) (cubeRadius T.supportCube) ∧
    ∀ i j : Fin d, i.val ≤ j.val →
      triadicLocalCoordinate T.supportCube x (T.order i) ≤
        triadicLocalCoordinate T.supportCube x (T.order j)}

theorem KuhnCell.carrier_subset_closedCarrier (T : KuhnCell d) :
    T.carrier ⊆ T.closedCarrier := by
  intro x hx
  refine ⟨cubeSet_subset_closedBall T.supportCube hx.1, ?_⟩
  intro i j hij
  rw [hx.2]
  exact Tuple.monotone_sort (triadicLocalCoordinate T.supportCube x) hij

theorem KuhnCell.openCarrier_subset_closedCarrier (T : KuhnCell d) :
    T.openCarrier ⊆ T.closedCarrier :=
  T.openCarrier_subset_carrier.trans T.carrier_subset_closedCarrier

/-! ## Vertices -/

/-- **`V(△)`**: the `k`-th vertex of a Kuhn cell.  It raises the last `k`
coordinates in the cell's order to the upper face and leaves the rest on the
lower face; `k = 0` is the lower corner and `k = d` the upper corner.

Disclosure (definitional stand-in).  ABK26 *defines* a vertex of a simplex to be
an **extreme point** of that simplex, and then observes that there are `d+1` of
them.  This declaration is instead the explicit corner **formula**, so it is a
stand-in for the printed definition, not a transcription of it.  What is proved
here is that the formula proves in the cell (`vertex_mem_closedCarrier`), is
injective, and yields exactly `d+1` points (`ncard_vertexSet`, the printed
count). -/
def KuhnCell.vertex (T : KuhnCell d) (k : Fin (d + 1)) : Vec d :=
  fun i =>
    ((T.supportCube.index i : ℝ) +
      if d ≤ (T.order.symm i).val + k.val then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) *
      cubeScaleFactor T.supportCube

/-- **`V(△)`**: the vertex set of a Kuhn cell. -/
def KuhnCell.vertexSet (T : KuhnCell d) : Set (Vec d) := Set.range T.vertex

theorem KuhnCell.vertex_mem_closedCarrier (T : KuhnCell d) (k : Fin (d + 1)) :
    T.vertex k ∈ T.closedCarrier := by
  have hs : (0 : ℝ) < cubeScaleFactor T.supportCube :=
    zpow_pos (by norm_num) _
  constructor
  · rw [closedBall_cubeCenter_eq_pi_Icc]
    intro i _
    simp only [KuhnCell.vertex, cubeCenter, cubeRadius]
    split_ifs <;> constructor <;> nlinarith
  · intro i j hij
    simp only [triadicLocalCoordinate, KuhnCell.vertex, Equiv.symm_apply_apply]
    by_cases hik : d ≤ i.val + k.val <;> by_cases hjk : d ≤ j.val + k.val <;>
      simp only [hik, hjk, ite_true, ite_false] <;> nlinarith

/-! ## The standard simplicial decomposition `S_j(□)` -/

/-- The enumeration equivalence used to count the cells of a decomposition. -/
def kuhnCellEquiv : (TriadicCube d × Equiv.Perm (Fin d)) ≃ KuhnCell d where
  toFun p := ⟨p.1, p.2⟩
  invFun T := (T.supportCube, T.order)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **ABK26 `S_j(□)`**: the decomposition of the triadic cube `Q` into the triadic
simplices of size `3^j` supported on its scale-`j` triadic descendants.  Empty
when `j > Q.scale`, matching the display's range `j ≤ m`. -/
def triadicSimplexPartition (Q : TriadicCube d) (j : ℤ) : Finset (KuhnCell d) :=
  (descendantsAtScale Q j ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin d)))).map
    kuhnCellEquiv.toEmbedding

@[simp] theorem mem_triadicSimplexPartition_iff {Q : TriadicCube d} {j : ℤ}
    {T : KuhnCell d} :
    T ∈ triadicSimplexPartition Q j ↔ T.supportCube ∈ descendantsAtScale Q j := by
  simp [triadicSimplexPartition, kuhnCellEquiv]

theorem triadicSimplexPartition_eq_empty {Q : TriadicCube d} {j : ℤ}
    (hj : Q.scale < j) : triadicSimplexPartition (d := d) Q j = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem fun T hT => ?_
  rw [mem_triadicSimplexPartition_iff, descendantsAtScale_eq_empty Q hj] at hT
  exact absurd hT (Finset.notMem_empty _)

/-- **The size clause of `S_j(□)`**: every simplex of `S_j(□)` has size `3^j`. -/
theorem supportCube_scale_eq_of_mem_triadicSimplexPartition {Q : TriadicCube d}
    {j : ℤ} (hj : j ≤ Q.scale) {T : KuhnCell d}
    (hT : T ∈ triadicSimplexPartition Q j) : T.supportCube.scale = j := by
  rw [mem_triadicSimplexPartition_iff, descendantsAtScale_eq_descendantsAtDepth Q hj] at hT
  have h := scale_eq_sub_of_mem_descendantsAtDepth hT
  omega

/-- The canonical half-open cells of `S_j(□)` cover the half-open cube exactly. -/
theorem cubeSet_eq_iUnion_triadicSimplexPartition (Q : TriadicCube d) {j : ℤ}
    (hj : j ≤ Q.scale) :
    cubeSet Q =
      ⋃ T ∈ (triadicSimplexPartition Q j : Set (KuhnCell d)), T.carrier := by
  ext x
  constructor
  · intro hx
    obtain ⟨R, hR, hxR⟩ :=
      exists_mem_descendantsAtDepth_of_mem_cubeSet (Int.toNat (Q.scale - j)) hx
    have hRmem : R ∈ descendantsAtScale Q j := by
      rw [descendantsAtScale_eq_descendantsAtDepth Q hj]
      exact hR
    refine Set.mem_iUnion.mpr
      ⟨⟨R, Tuple.sort (triadicLocalCoordinate R x)⟩,
        Set.mem_iUnion.mpr ⟨?_, hxR, rfl⟩⟩
    exact mem_triadicSimplexPartition_iff.mpr hRmem
  · intro hx
    obtain ⟨T, hT, hxT⟩ := by simpa only [Set.mem_iUnion] using hx
    have hTmem : T.supportCube ∈ descendantsAtDepth Q (Int.toNat (Q.scale - j)) := by
      rw [← descendantsAtScale_eq_descendantsAtDepth Q hj]
      exact mem_triadicSimplexPartition_iff.mp hT
    exact cubeSet_subset_of_mem_descendantsAtDepth hTmem (T.carrier_subset_cubeSet hxT)

theorem KuhnCell.disjoint_carrier_of_supportCube_eq {T U : KuhnCell d}
    (hTU : T ≠ U) (hsupport : T.supportCube = U.supportCube) :
    Disjoint T.carrier U.carrier := by
  rw [Set.disjoint_left]
  intro x hxT hxU
  refine hTU ?_
  cases T with
  | mk QT piT =>
      cases U with
      | mk QU piU =>
          simp only at hsupport
          subst QU
          simp only [KuhnCell.carrier, Set.mem_ofPred_eq] at hxT hxU
          simp only [KuhnCell.mk.injEq, true_and]
          exact hxT.2.trans hxU.2.symm

/-- The half-open cells of `S_j(□)` are pairwise disjoint, boundaries included. -/
theorem triadicSimplexPartition_pairwiseDisjoint (Q : TriadicCube d) (j : ℤ) :
    (triadicSimplexPartition Q j : Set (KuhnCell d)).PairwiseDisjoint
      KuhnCell.carrier := by
  classical
  intro T hT U hU hTU
  by_cases hsupport : T.supportCube = U.supportCube
  · exact KuhnCell.disjoint_carrier_of_supportCube_eq hTU hsupport
  · by_cases hj : j ≤ Q.scale
    · have hTm : T.supportCube ∈ descendantsAtDepth Q (Int.toNat (Q.scale - j)) := by
        rw [← descendantsAtScale_eq_descendantsAtDepth Q hj]
        exact mem_triadicSimplexPartition_iff.mp hT
      have hUm : U.supportCube ∈ descendantsAtDepth Q (Int.toNat (Q.scale - j)) := by
        rw [← descendantsAtScale_eq_descendantsAtDepth Q hj]
        exact mem_triadicSimplexPartition_iff.mp hU
      exact (pairwiseDisjoint_descendantsAtDepth Q _ hTm hUm hsupport).mono
        T.carrier_subset_cubeSet U.carrier_subset_cubeSet
    · rw [triadicSimplexPartition_eq_empty (by omega)] at hT
      exact absurd hT (Finset.notMem_empty _)

/-- The manuscript's open simplices of `S_j(□)` are pairwise disjoint. -/
theorem triadicSimplexPartition_openCarrier_pairwiseDisjoint (Q : TriadicCube d)
    (j : ℤ) :
    (triadicSimplexPartition Q j : Set (KuhnCell d)).PairwiseDisjoint
      KuhnCell.openCarrier :=
  (triadicSimplexPartition_pairwiseDisjoint Q j).mono
    KuhnCell.openCarrier_subset_carrier

/-! ## Nesting of the standard decompositions -/

/-- The lexicographic key that coarsens a child order across one triadic
subdivision: first the child's digit in that coordinate, then the child's own
rank. -/
def childKuhnOrderKey (digits : Fin d → Fin 3) (pi : Equiv.Perm (Fin d))
    (i : Fin d) : ℕ ×ₗ ℕ :=
  toLex ((digits i).val, (pi.symm i).val)

theorem childKuhnOrderKey_injective (digits : Fin d → Fin 3)
    (pi : Equiv.Perm (Fin d)) :
    Function.Injective (childKuhnOrderKey digits pi) := by
  intro i j hij
  have hrank : (pi.symm i).val = (pi.symm j).val :=
    congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).2) hij
  exact pi.symm.injective (Fin.ext hrank)

/-- The parent order induced by a child cube's digits and the child's order. -/
def coarsenedChildKuhnOrder (digits : Fin d → Fin 3) (pi : Equiv.Perm (Fin d)) :
    Equiv.Perm (Fin d) :=
  Tuple.sort (childKuhnOrderKey digits pi)

private theorem triadicLocalCoordinate_parent_eq_child_add_digit
    (Q : TriadicCube d) (digits : Fin d → Fin 3) (x : Vec d) (i : Fin d) :
    triadicLocalCoordinate Q x i =
      triadicLocalCoordinate
          ({ scale := Q.scale - 1
             index := fun j => 3 * Q.index j + (digits j : ℤ) - 1 } : TriadicCube d)
          x i +
        (((digits i : ℤ) : ℝ) - 1) *
          cubeScaleFactor
            ({ scale := Q.scale - 1
               index := fun j => 3 * Q.index j + (digits j : ℤ) - 1 } : TriadicCube d) := by
  have hscale :
      cubeScaleFactor
          ({ scale := Q.scale - 1
             index := fun j => 3 * Q.index j + (digits j : ℤ) - 1 } : TriadicCube d) =
        cubeScaleFactor Q / 3 := by
    simp [cubeScaleFactor, zpow_sub₀ (show (3 : ℝ) ≠ 0 by norm_num)]
  simp only [triadicLocalCoordinate, hscale]
  push_cast
  ring

private theorem openCarrier_child_subset_parent (Q : TriadicCube d)
    (digits : Fin d → Fin 3) (pi : Equiv.Perm (Fin d)) :
    KuhnCell.openCarrier
        ({ supportCube :=
             { scale := Q.scale - 1
               index := fun i => 3 * Q.index i + (digits i : ℤ) - 1 }
           order := pi } : KuhnCell d) ⊆
      KuhnCell.openCarrier
        ({ supportCube := Q, order := coarsenedChildKuhnOrder digits pi } : KuhnCell d) := by
  intro x hx
  rw [KuhnCell.mem_openCarrier_iff] at hx
  set R : TriadicCube d :=
    { scale := Q.scale - 1
      index := fun i => 3 * Q.index i + (digits i : ℤ) - 1 } with hR
  set sigma : Equiv.Perm (Fin d) := coarsenedChildKuhnOrder digits pi with hsigma
  have hRs : (0 : ℝ) < cubeScaleFactor R := zpow_pos (by norm_num) _
  rw [KuhnCell.mem_openCarrier_iff]
  refine ⟨openCubeSet_childCube_subset Q digits hx.1, ?_⟩
  intro i j hij
  have hkeyle :
      childKuhnOrderKey digits pi (sigma i) ≤ childKuhnOrderKey digits pi (sigma j) :=
    Tuple.monotone_sort (childKuhnOrderKey digits pi) (le_of_lt hij)
  have hkeyne :
      childKuhnOrderKey digits pi (sigma i) ≠ childKuhnOrderKey digits pi (sigma j) := by
    intro heq
    have hsig : sigma i = sigma j := childKuhnOrderKey_injective digits pi heq
    have hijne : i ≠ j := fun h => absurd (congrArg Fin.val h) (Nat.ne_of_lt hij)
    exact hijne (sigma.injective hsig)
  rw [triadicLocalCoordinate_parent_eq_child_add_digit Q digits x (sigma i),
    triadicLocalCoordinate_parent_eq_child_add_digit Q digits x (sigma j)]
  rcases Prod.Lex.toLex_lt_toLex.mp (lt_of_le_of_ne hkeyle hkeyne) with hdigit | ⟨hdigit, hrank⟩
  · have hsuccR :
        (((digits (sigma i) : ℤ) : ℝ) + 1) ≤ ((digits (sigma j) : ℤ) : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr hdigit
    have hlo := (hx.1 (sigma j)).1
    have hhi := (hx.1 (sigma i)).2
    simp only [triadicLocalCoordinate, hR] at hlo hhi ⊢
    nlinarith
  · have hlocal :
        triadicLocalCoordinate R x (sigma i) < triadicLocalCoordinate R x (sigma j) := by
      have hpi := hx.2 (pi.symm (sigma i)) (pi.symm (sigma j)) hrank
      simpa only [Equiv.apply_symm_apply] using hpi
    have hdigitR : ((digits (sigma i) : ℤ) : ℝ) = ((digits (sigma j) : ℤ) : ℝ) := by
      exact_mod_cast hdigit
    rw [hdigitR]
    linarith

/-- Every simplex of a deeper decomposition of `Q` lies in one of the `d!`
simplices of `Q` itself. -/
theorem exists_selfSimplex_openCarrier_superset (Q : TriadicCube d) :
    ∀ (depth : ℕ) {T : KuhnCell d},
      T.supportCube ∈ descendantsAtDepth Q depth →
        ∃ U ∈ triadicSimplexPartition Q Q.scale, T.openCarrier ⊆ U.openCarrier := by
  intro depth
  induction depth with
  | zero =>
      intro T hT
      refine ⟨T, mem_triadicSimplexPartition_iff.mpr ?_, Set.Subset.rfl⟩
      rw [descendantsAtScale_self]
      simpa using hT
  | succ depth ih =>
      intro T hT
      obtain ⟨R, hR, hchild⟩ := mem_descendantsAtDepth_succ_iff.mp hT
      obtain ⟨digits, hsupport⟩ := mem_childCubes_iff.mp hchild
      obtain ⟨U, hU, hVU⟩ :=
        ih (T := ⟨R, coarsenedChildKuhnOrder digits T.order⟩) hR
      refine ⟨U, hU, Set.Subset.trans ?_ hVU⟩
      have hTeq : T = ⟨T.supportCube, T.order⟩ := rfl
      rw [hTeq, hsupport]
      exact openCarrier_child_subset_parent R digits T.order

/-- **Nested standard decompositions.**  Every simplex of the finer decomposition
`S_{j'}(□)` lies inside a simplex of any coarser decomposition `S_j(□)`, `j' ≤
j ≤ Q.scale`.  This is the only cross-scale compatibility that `e.SW.def`
supports. -/
theorem triadicSimplexPartition_refines_openCarrier (Q : TriadicCube d) {j j' : ℤ}
    (hj : j ≤ Q.scale) (hj' : j' ≤ j) {T : KuhnCell d}
    (hT : T ∈ triadicSimplexPartition Q j') :
    ∃ U ∈ triadicSimplexPartition Q j, T.openCarrier ⊆ U.openCarrier := by
  have hj'Q : j' ≤ Q.scale := le_trans hj' hj
  have hTd : T.supportCube ∈ descendantsAtDepth Q (Int.toNat (Q.scale - j')) := by
    rw [← descendantsAtScale_eq_descendantsAtDepth Q hj'Q]
    exact mem_triadicSimplexPartition_iff.mp hT
  have hsplit :
      Int.toNat (Q.scale - j') = Int.toNat (Q.scale - j) + Int.toNat (j - j') := by
    omega
  rw [hsplit] at hTd
  obtain ⟨A, hA, hTA⟩ :=
    exists_descendant_ancestor_at_depth (Int.toNat (Q.scale - j))
      (Int.toNat (j - j')) hTd
  have hAscale : A.scale = j := by
    have := scale_eq_sub_of_mem_descendantsAtDepth hA
    omega
  obtain ⟨U, hU, hTU⟩ :=
    exists_selfSimplex_openCarrier_superset A (Int.toNat (j - j')) hTA
  refine ⟨U, ?_, hTU⟩
  rw [mem_triadicSimplexPartition_iff, descendantsAtScale_eq_descendantsAtDepth Q hj]
  have hUA : U.supportCube ∈ descendantsAtScale A A.scale :=
    mem_triadicSimplexPartition_iff.mp hU
  rw [descendantsAtScale_self, Finset.mem_singleton] at hUA
  rw [hUA]
  exact hA

end

end Algsuperdiff.Section3.Provider.Whitney
