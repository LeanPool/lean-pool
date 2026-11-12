/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertexDegreeTwo
public import LeanPool.ApollonianSuperharmonic.P5620T1BoundaryComponentCycle
public import LeanPool.ApollonianSuperharmonic.FourNeighborConnected
public import LeanPool.ApollonianSuperharmonic.GridRayCrossingIndexAdjacentCell
public import LeanPool.ApollonianSuperharmonic.P3475T1UnitSegmentIntersection
public import LeanPool.ApollonianSuperharmonic.P3381T1PolygonBoundary

-- [TABLET NODE: P3475T1GridBoundary]

/-!
# P3475T1GridBoundary

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace GridBoundaryConstruction

private theorem cells_nonempty (T : ProtoTile) (hinside : FourNeighborConnected (T.cells : Set
    LatticeCell)) : T.cells.Nonempty := by
  classical
  exact hinside.1

private theorem boundary_degree_two (T : ProtoTile) (hinside : FourNeighborConnected (T.cells :
    Set LatticeCell)) (hchecker : NoCheckerboardCellVertex (T.cells : Set LatticeCell)) : ∀ v ∈
    BoundaryFootprintVertices T, Set.ncard {e : Finset GaussianInt | e ∈ BoundaryFootprintEdges T
    ∧ v ∈ e} = 2 := by
  classical
  have cells_nonempty : T.cells.Nonempty := cells_nonempty T hinside
  intro v hv
  exact BoundaryFootprintVertexDegreeTwo T cells_nonempty hchecker v hv

private theorem gridPath_length (gridPath : List GaussianInt) (gridPath_length_four : 4 ≤
    gridPath.length) : 3 ≤ gridPath.length := by
  classical
  omega

private noncomputable abbrev cyclicEdges (gridPath : List GaussianInt) (y : GaussianInt) (x :
    GaussianInt) := (gridPath.zip gridPath.tail) ++ [(y, x)]

private theorem same_vertical_not_boundary (T : ProtoTile) (q : LatticeCell) (hstatus : q ∈
    T.cells ↔ q - 1 ∈
    T.cells) : ({q, q + ⟨0, 1⟩} : Finset GaussianInt) ∉ BoundaryFootprintEdges T := by
  classical
  rintro ⟨w, (⟨heq, hxor⟩ | ⟨heq, hxor⟩)⟩
  · have hw : w = q ∨ w = q + ⟨0, 1⟩ := by
      have : w ∈ ({q, q + ⟨0, 1⟩} : Finset GaussianInt) := by rw [heq]; simp
      simpa using this
    have hw1 : w + 1 = q ∨ w + 1 = q + ⟨0, 1⟩ := by
      have : w + 1 ∈ ({q, q + ⟨0, 1⟩} : Finset GaussianInt) := by rw [heq]; simp
      simpa using this
    rcases hw with rfl | rfl <;> simp [Zsqrtd.ext_iff] at hw1
  · have hw : w = q ∨ w = q + ⟨0, 1⟩ := by
      have : w ∈ ({q, q + ⟨0, 1⟩} : Finset GaussianInt) := by rw [heq]; simp
      simpa using this
    rcases hw with rfl | hw
    · rcases hxor with ⟨hq, hl⟩ | ⟨hq, hl⟩
      · exact hl (hstatus.mp hq)
      · exact hq (hstatus.mpr hl)
    · subst w
      have hw2 : q + ⟨0, 1⟩ + ⟨0, 1⟩ = q ∨
          q + ⟨0, 1⟩ + ⟨0, 1⟩ = q + ⟨0, 1⟩ := by
        have : q + ⟨0, 1⟩ + ⟨0, 1⟩ ∈
            ({q, q + ⟨0, 1⟩} : Finset GaussianInt) := by rw [heq]; simp
        simpa using this
      rcases hw2 with hw2 | hw2 <;>
        have hbad := congrArg Zsqrtd.im hw2 <;> simp at hbad; omega

private theorem same_horizontal_not_boundary (T : ProtoTile) (q : LatticeCell) (hstatus : q ∈
    T.cells ↔ q - ⟨0, 1⟩ ∈ T.cells) : ({q, q + 1} : Finset GaussianInt) ∉ BoundaryFootprintEdges
    T := by
  classical
  rintro ⟨w, (⟨heq, hxor⟩ | ⟨heq, hxor⟩)⟩
  · have hw : w = q ∨ w = q + 1 := by
      have : w ∈ ({q, q + 1} : Finset GaussianInt) := by rw [heq]; simp
      simpa using this
    rcases hw with rfl | hw
    · rcases hxor with ⟨hq, hl⟩ | ⟨hq, hl⟩
      · exact hl (hstatus.mp hq)
      · exact hq (hstatus.mpr hl)
    · subst w
      have hw2 : q + 1 + 1 = q ∨ q + 1 + 1 = q + 1 := by
        have : q + 1 + 1 ∈ ({q, q + 1} : Finset GaussianInt) := by rw [heq]; simp
        simpa using this
      rcases hw2 with hw2 | hw2 <;>
        have hbad := congrArg Zsqrtd.re hw2 <;> simp at hbad; omega
  · have hw : w = q ∨ w = q + 1 := by
      have : w ∈ ({q, q + 1} : Finset GaussianInt) := by rw [heq]; simp
      simpa using this
    have hwi : w + ⟨0, 1⟩ = q ∨ w + ⟨0, 1⟩ = q + 1 := by
      have : w + ⟨0, 1⟩ ∈ ({q, q + 1} : Finset GaussianInt) := by rw [heq]; simp
      simpa using this
    rcases hw with rfl | rfl <;> simp [Zsqrtd.ext_iff] at hwi

private theorem adjacent_index_same_status (T : ProtoTile) (gridPath : List GaussianInt) (y :
    GaussianInt) (x : GaussianInt) (cyclic_edge_boundary : ∀ (a b : GaussianInt), (a, b) ∈
    gridPath.zip gridPath.tail ++ [(y, x)] → {a, b} ∈
    ApollonianSuperharmonic.BoundaryFootprintEdges T) (gridPath_head : gridPath.head? = some x)
    (gridPath_last : gridPath.getLast? = some y) (gridPath_nodup : gridPath.Nodup)
    (gridPath_zip_fourNeighbor : ∀ (a b : GaussianInt), (a, b) ∈ gridPath.zip gridPath.tail →
    ApollonianSuperharmonic.FourNeighborAdjacent a b) (gridPath_close_fourNeighbor :
    ApollonianSuperharmonic.FourNeighborAdjacent y x) (gridPath_length_four : 4 ≤
    gridPath.length) (a b : LatticeCell) (hs : a ∈ T.cells ↔ b ∈ T.cells) (hab :
    FourNeighborAdjacent a b) : GridRayCrossingIndex a gridPath = GridRayCrossingIndex b gridPath
    := by
  classical
  have gridPath_length : 3 ≤ gridPath.length := gridPath_length gridPath gridPath_length_four
  have component_index_control := GridRayCrossingIndexAdjacentCell gridPath x y
    gridPath_head gridPath_last gridPath_nodup gridPath_length
    gridPath_zip_fourNeighbor gridPath_close_fourNeighbor
  have same_vertical_not_boundary (q : LatticeCell)
      (hstatus : q ∈ T.cells ↔ q - 1 ∈ T.cells) :
      ({q, q + ⟨0, 1⟩} : Finset GaussianInt) ∉ BoundaryFootprintEdges T :=
          same_vertical_not_boundary T q hstatus
  have same_horizontal_not_boundary (q : LatticeCell)
      (hstatus : q ∈ T.cells ↔ q - ⟨0, 1⟩ ∈ T.cells) :
      ({q, q + 1} : Finset GaussianInt) ∉ BoundaryFootprintEdges T :=
          same_horizontal_not_boundary T q hstatus
  rcases hab with rfl | rfl | rfl | rfl
  · symm
    apply (component_index_control a).1
    constructor <;> intro hc
    · apply same_vertical_not_boundary (a + 1)
        (by simpa using hs.symm)
      exact cyclic_edge_boundary _ _ hc
    · apply same_vertical_not_boundary (a + 1)
        (by simpa using hs.symm)
      simpa [Finset.pair_comm] using cyclic_edge_boundary _ _ hc
  · have heq := (component_index_control (a - 1)).1
      ⟨(fun hc => same_vertical_not_boundary a hs
        (by simpa using cyclic_edge_boundary _ _ hc)),
       (fun hc => same_vertical_not_boundary a hs
        (by simpa [Finset.pair_comm] using cyclic_edge_boundary _ _ hc))⟩
    simpa using heq
  · symm
    apply (component_index_control a).2.2.1
    constructor <;> intro hc
    · apply same_horizontal_not_boundary (a + ⟨0, 1⟩)
        (by simpa using hs.symm)
      simpa [Finset.pair_comm, add_comm, add_left_comm, add_assoc]
        using cyclic_edge_boundary _ _ hc
    · apply same_horizontal_not_boundary (a + ⟨0, 1⟩)
        (by simpa using hs.symm)
      simpa [add_comm, add_left_comm, add_assoc]
        using cyclic_edge_boundary _ _ hc
  · have heq := (component_index_control (a - ⟨0, 1⟩)).2.2.1
      ⟨(fun hc => same_horizontal_not_boundary a hs
        (by simpa [Finset.pair_comm, add_comm, add_left_comm, add_assoc]
          using cyclic_edge_boundary _ _ hc)),
       (fun hc => same_horizontal_not_boundary a hs
        (by simpa [add_comm, add_left_comm, add_assoc]
          using cyclic_edge_boundary _ _ hc))⟩
    simpa using heq

private theorem index_constant (S : Set LatticeCell) (hS : FourNeighborConnected S) (I :
    LatticeCell → Int) (hstep : ∀ a, a ∈ S → ∀ b, b ∈ S → FourNeighborAdjacent a b → I a = I b)
    (x : LatticeCell) (hx : x ∈ S) (y : LatticeCell) (hy : y ∈ S) : I x = I y := by
  classical
  obtain ⟨p, hhead, hlast, hmem, hadj⟩ := hS.2 x hx y hy
  have hchain : List.IsChain FourNeighborAdjacent p := by
    rw [List.isChain_iff_forall_rel_of_append_cons_cons]
    exact hadj
  have hindices : List.IsChain (fun a b => I a = I b) p :=
    hchain.imp_of_mem_imp (fun a b ha hb hab =>
      hstep a (hmem a ha) b (hmem b hb) hab)
  cases p with
  | nil => simp at hhead
  | cons a p =>
    have hax : a = x := by simpa using Option.some.inj hhead
    subst a
    have hymem : y ∈ x :: p := by
      rcases List.getLast?_eq_some_iff.mp hlast with ⟨l, hl⟩
      rw [hl]
      simp
    simp only [List.mem_cons] at hymem
    rcases hymem with hyx | hymem
    · exact congrArg I hyx.symm
    · exact hindices.rel_cons hymem

private noncomputable abbrev q0 (w : ApollonianSuperharmonic.LatticeCell) : LatticeCell := by
  classical
  exact ⟨w.re - 1, 0⟩

private theorem q0_outside (T : ProtoTile) (gridPath : List GaussianInt) (w :
    ApollonianSuperharmonic.LatticeCell) (hmin : ∀ x' ∈ T.cells ∪ gridPath.toFinset, w.re ≤
    x'.re) : (q0 w) ∉ T.cells := by
  classical
  let q0 : LatticeCell := ⟨w.re - 1, 0⟩
  change (q0 ∉ T.cells)
  intro hq
  have h := hmin q0 (Finset.mem_union_left _ hq)
  simp only [q0] at h
  omega

private theorem path_left (T : ProtoTile) (gridPath : List GaussianInt) (w :
    ApollonianSuperharmonic.LatticeCell) (hmin : ∀ x' ∈ T.cells ∪ gridPath.toFinset, w.re ≤
    x'.re) (a : GaussianInt) (ha : a ∈ gridPath) : (q0 w).re < a.re := by
  classical
  let q0 : LatticeCell := ⟨w.re - 1, 0⟩
  change (q0.re < a.re)
  have h := hmin a (Finset.mem_union_right _ (List.mem_toFinset.mpr ha))
  dsimp only [q0]
  omega

private noncomputable abbrev step (w : ApollonianSuperharmonic.LatticeCell) : GaussianInt →
    GaussianInt → Int := by
  classical
  let q0 : LatticeCell := ⟨w.re - 1, 0⟩
  exact fun a b =>
    if b = a + ⟨0, 1⟩ ∧ a.im = q0.im ∧ a.re ≤ q0.re then 1
    else if b = a - ⟨0, 1⟩ ∧ b.im = q0.im ∧ a.re ≤ q0.re then -1 else 0

private theorem step_zero (T : ProtoTile) (gridPath : List GaussianInt) (w :
    ApollonianSuperharmonic.LatticeCell) (hmin : ∀ x' ∈ T.cells ∪ gridPath.toFinset, w.re ≤
    x'.re) (a : GaussianInt) (ha : a ∈ gridPath) (b : GaussianInt) : (step w) a b = 0 := by
  classical
  let q0 : LatticeCell := ⟨w.re - 1, 0⟩
  have path_left (a : GaussianInt) (ha : a ∈ gridPath) : q0.re < a.re := path_left T gridPath w
      hmin a ha
  let step : GaussianInt → GaussianInt → Int := fun a b =>
    if b = a + ⟨0, 1⟩ ∧ a.im = q0.im ∧ a.re ≤ q0.re then 1
    else if b = a - ⟨0, 1⟩ ∧ b.im = q0.im ∧ a.re ≤ q0.re then -1 else 0
  change (step a b = 0)
  have hn : ¬ a.re ≤ q0.re := not_le.mpr (path_left a ha)
  simp only [step, hn, and_false, ite_false]

private theorem zip_zero (T : ProtoTile) (gridPath : List GaussianInt) (w :
    ApollonianSuperharmonic.LatticeCell) (hmin : ∀ x' ∈ T.cells ∪ gridPath.toFinset, w.re ≤
    x'.re) (r s : List GaussianInt) (hr : ∀ a ∈ r, a ∈ gridPath) : (List.zipWith (step w) r
    s).sum = 0 := by
  classical
  let q0 : LatticeCell := ⟨w.re - 1, 0⟩
  let step : GaussianInt → GaussianInt → Int := fun a b =>
    if b = a + ⟨0, 1⟩ ∧ a.im = q0.im ∧ a.re ≤ q0.re then 1
    else if b = a - ⟨0, 1⟩ ∧ b.im = q0.im ∧ a.re ≤ q0.re then -1 else 0
  have step_zero (a : GaussianInt) (ha : a ∈ gridPath) (b : GaussianInt) :
      step a b = 0 := step_zero T gridPath w hmin a ha b
  change ((List.zipWith step r s).sum = 0)
  induction r generalizing s with
  | nil => simp
  | cons a r ih =>
    cases s with
    | nil => simp
    | cons b s =>
      rw [List.zipWith_cons_cons, List.sum_cons,
        step_zero a (hr a (by simp)), ih s (fun c hc => hr c (by simp [hc]))]
      simp

private theorem q0_index_zero (T : ProtoTile) (gridPath : List GaussianInt) (y : GaussianInt) (x
    : GaussianInt) (gridPath_head : gridPath.head? = some x) (gridPath_last : gridPath.getLast? =
    some y) (w : ApollonianSuperharmonic.LatticeCell) (hmin : ∀ x' ∈ T.cells ∪ gridPath.toFinset,
    w.re ≤ x'.re) : GridRayCrossingIndex (q0 w) gridPath = 0 := by
  classical
  let q0 : LatticeCell := ⟨w.re - 1, 0⟩
  let step : GaussianInt → GaussianInt → Int := fun a b =>
    if b = a + ⟨0, 1⟩ ∧ a.im = q0.im ∧ a.re ≤ q0.re then 1
    else if b = a - ⟨0, 1⟩ ∧ b.im = q0.im ∧ a.re ≤ q0.re then -1 else 0
  have step_zero (a : GaussianInt) (ha : a ∈ gridPath) (b : GaussianInt) :
      step a b = 0 := step_zero T gridPath w hmin a ha b
  have zip_zero (r s : List GaussianInt) (hr : ∀ a ∈ r, a ∈ gridPath) :
      (List.zipWith step r s).sum = 0 := zip_zero T gridPath w hmin r s hr
  change (GridRayCrossingIndex q0 gridPath = 0)
  have hsum := zip_zero gridPath gridPath.tail (fun a ha => ha)
  have hy : y ∈ gridPath := by
    rcases List.getLast?_eq_some_iff.mp gridPath_last with ⟨l, hl⟩
    rw [hl]
    simp
  change (List.zipWith step gridPath gridPath.tail).sum +
    (match gridPath.getLast?, gridPath.head? with
     | some a, some b => step a b
     | _, _ => 0) = 0
  rw [hsum, gridPath_last, gridPath_head]
  simp only [step_zero y hy x, add_zero]

private theorem unoccupied_index_zero (T : ProtoTile) (houtside : FourNeighborConnected ((T.cells
    : Set LatticeCell)ᶜ)) (gridPath : List GaussianInt) (y : GaussianInt) (x : GaussianInt)
    (cyclic_edge_boundary : ∀ (a b : GaussianInt), (a, b) ∈ gridPath.zip gridPath.tail ++ [(y,
    x)] → {a, b} ∈ ApollonianSuperharmonic.BoundaryFootprintEdges T) (gridPath_head :
    gridPath.head? = some x) (gridPath_last : gridPath.getLast? = some y) (gridPath_nodup :
    gridPath.Nodup) (gridPath_zip_fourNeighbor : ∀ (a b : GaussianInt), (a, b) ∈ gridPath.zip
    gridPath.tail → ApollonianSuperharmonic.FourNeighborAdjacent a b)
    (gridPath_close_fourNeighbor : ApollonianSuperharmonic.FourNeighborAdjacent y x) (w :
    ApollonianSuperharmonic.LatticeCell) (gridPath_length_four : 4 ≤ gridPath.length) (hmin : ∀
    x' ∈ T.cells ∪ gridPath.toFinset, w.re ≤ x'.re) (q : LatticeCell) (hq : q ∉ T.cells) :
    GridRayCrossingIndex q gridPath = 0 := by
  classical
  have adjacent_index_same_status (a b : LatticeCell)
      (hs : a ∈ T.cells ↔ b ∈ T.cells) (hab : FourNeighborAdjacent a b) :
      GridRayCrossingIndex a gridPath = GridRayCrossingIndex b gridPath :=
          adjacent_index_same_status T gridPath y x cyclic_edge_boundary gridPath_head
          gridPath_last gridPath_nodup gridPath_zip_fourNeighbor gridPath_close_fourNeighbor
          gridPath_length_four a b hs hab
  have index_constant (S : Set LatticeCell) (hS : FourNeighborConnected S)
      (I : LatticeCell → Int)
      (hstep : ∀ a, a ∈ S → ∀ b, b ∈ S →
        FourNeighborAdjacent a b → I a = I b)
      (x : LatticeCell) (hx : x ∈ S) (y : LatticeCell) (hy : y ∈ S) :
      I x = I y := index_constant S hS I hstep x hx y hy
  let q0 : LatticeCell := ⟨w.re - 1, 0⟩
  have q0_outside : q0 ∉ T.cells := q0_outside T gridPath w hmin
  have q0_index_zero : GridRayCrossingIndex q0 gridPath = 0 := q0_index_zero T gridPath y x
      gridPath_head gridPath_last w hmin
  have hconst := index_constant ((T.cells : Set LatticeCell)ᶜ) houtside
    (fun a => GridRayCrossingIndex a gridPath)
    (fun a ha b hb hab => adjacent_index_same_status a b
      (by simp only [Finset.mem_coe, Set.mem_compl_iff] at ha hb; simp [ha, hb]) hab)
    q hq q0 q0_outside
  exact hconst.trans q0_index_zero

private theorem hrightJump (gridPath : List GaussianInt) (y : GaussianInt) (x : GaussianInt)
    (gridPath_head : gridPath.head? = some x) (gridPath_last : gridPath.getLast? = some y)
    (gridPath_nodup : gridPath.Nodup) (gridPath_zip_fourNeighbor : ∀ (a b : GaussianInt), (a, b)
    ∈ gridPath.zip gridPath.tail → ApollonianSuperharmonic.FourNeighborAdjacent a b)
    (gridPath_close_fourNeighbor : ApollonianSuperharmonic.FourNeighborAdjacent y x) (z :
    GaussianInt) (gridPath_length_four : 4 ≤ gridPath.length) (hrightCyclic : (z + 1, z + 1 + {
    re := 0, im := 1 }) ∈ gridPath.zip gridPath.tail ++ [(y, x)] ∨ (z + 1 + { re := 0, im := 1 },
    z + 1) ∈ gridPath.zip gridPath.tail ++ [(y, x)]) : Int.natAbs (GridRayCrossingIndex (z + 1)
    gridPath - GridRayCrossingIndex z gridPath) = 1 := by
  classical
  have gridPath_length : 3 ≤ gridPath.length := gridPath_length gridPath gridPath_length_four
  have component_index_control := GridRayCrossingIndexAdjacentCell gridPath x y
    gridPath_head gridPath_last gridPath_nodup gridPath_length
    gridPath_zip_fourNeighbor gridPath_close_fourNeighbor
  exact (component_index_control z).2.1 hrightCyclic

private theorem hzIndexNonzero (T : ProtoTile) (houtside : FourNeighborConnected ((T.cells : Set
    LatticeCell)ᶜ)) (gridPath : List GaussianInt) (y : GaussianInt) (x : GaussianInt)
    (cyclic_edge_boundary : ∀ (a b : GaussianInt), (a, b) ∈ gridPath.zip gridPath.tail ++ [(y,
    x)] → {a, b} ∈ ApollonianSuperharmonic.BoundaryFootprintEdges T) (gridPath_head :
    gridPath.head? = some x) (gridPath_last : gridPath.getLast? = some y) (gridPath_nodup :
    gridPath.Nodup) (gridPath_zip_fourNeighbor : ∀ (a b : GaussianInt), (a, b) ∈ gridPath.zip
    gridPath.tail → ApollonianSuperharmonic.FourNeighborAdjacent a b)
    (gridPath_close_fourNeighbor : ApollonianSuperharmonic.FourNeighborAdjacent y x) (z :
    GaussianInt) (w : ApollonianSuperharmonic.LatticeCell) (gridPath_length_four : 4 ≤
    gridPath.length) (hrightCyclic : (z + 1, z + 1 + { re := 0, im := 1 }) ∈ gridPath.zip
    gridPath.tail ++ [(y, x)] ∨ (z + 1 + { re := 0, im := 1 }, z + 1) ∈ gridPath.zip
    gridPath.tail ++ [(y, x)]) (hzout : z + 1 ∉ T.cells) (hmin : ∀ x' ∈ T.cells ∪
    gridPath.toFinset, w.re ≤ x'.re) : GridRayCrossingIndex z gridPath ≠ 0 := by
  classical
  have unoccupied_index_zero (q : LatticeCell) (hq : q ∉ T.cells) :
      GridRayCrossingIndex q gridPath = 0 := unoccupied_index_zero T houtside gridPath y x
          cyclic_edge_boundary gridPath_head gridPath_last gridPath_nodup
          gridPath_zip_fourNeighbor gridPath_close_fourNeighbor w gridPath_length_four hmin q hq
  have hrightJump :
      Int.natAbs (GridRayCrossingIndex (z + 1) gridPath -
        GridRayCrossingIndex z gridPath) = 1 := hrightJump gridPath y x gridPath_head
            gridPath_last gridPath_nodup gridPath_zip_fourNeighbor gridPath_close_fourNeighbor z
            gridPath_length_four hrightCyclic
  intro hz0
  rw [unoccupied_index_zero (z + 1) hzout, hz0] at hrightJump
  simp at hrightJump

private theorem occupied_index_nonzero (T : ProtoTile) (hinside : FourNeighborConnected (T.cells
    : Set LatticeCell)) (houtside : FourNeighborConnected ((T.cells : Set LatticeCell)ᶜ))
    (gridPath : List GaussianInt) (y : GaussianInt) (x : GaussianInt) (cyclic_edge_boundary : ∀
    (a b : GaussianInt), (a, b) ∈ gridPath.zip gridPath.tail ++ [(y, x)] → {a, b} ∈
    ApollonianSuperharmonic.BoundaryFootprintEdges T) (gridPath_head : gridPath.head? = some x)
    (gridPath_last : gridPath.getLast? = some y) (gridPath_nodup : gridPath.Nodup)
    (gridPath_zip_fourNeighbor : ∀ (a b : GaussianInt), (a, b) ∈ gridPath.zip gridPath.tail →
    ApollonianSuperharmonic.FourNeighborAdjacent a b) (gridPath_close_fourNeighbor :
    ApollonianSuperharmonic.FourNeighborAdjacent y x) (z : GaussianInt) (w :
    ApollonianSuperharmonic.LatticeCell) (gridPath_length_four : 4 ≤ gridPath.length)
    (hrightCyclic : (z + 1, z + 1 + { re := 0, im := 1 }) ∈ gridPath.zip gridPath.tail ++ [(y,
    x)] ∨ (z + 1 + { re := 0, im := 1 }, z + 1) ∈ gridPath.zip gridPath.tail ++ [(y, x)]) (hzout
    : z + 1 ∉ T.cells) (hz : z ∈ T.cells) (hmin : ∀ x' ∈ T.cells ∪ gridPath.toFinset, w.re ≤
    x'.re) (q : LatticeCell) (hq : q ∈ T.cells) : GridRayCrossingIndex q gridPath ≠ 0 := by
  classical
  have adjacent_index_same_status (a b : LatticeCell)
      (hs : a ∈ T.cells ↔ b ∈ T.cells) (hab : FourNeighborAdjacent a b) :
      GridRayCrossingIndex a gridPath = GridRayCrossingIndex b gridPath :=
          adjacent_index_same_status T gridPath y x cyclic_edge_boundary gridPath_head
          gridPath_last gridPath_nodup gridPath_zip_fourNeighbor gridPath_close_fourNeighbor
          gridPath_length_four a b hs hab
  have index_constant (S : Set LatticeCell) (hS : FourNeighborConnected S)
      (I : LatticeCell → Int)
      (hstep : ∀ a, a ∈ S → ∀ b, b ∈ S →
        FourNeighborAdjacent a b → I a = I b)
      (x : LatticeCell) (hx : x ∈ S) (y : LatticeCell) (hy : y ∈ S) :
      I x = I y := index_constant S hS I hstep x hx y hy
  have hzIndexNonzero : GridRayCrossingIndex z gridPath ≠ 0 := hzIndexNonzero T houtside gridPath
      y x cyclic_edge_boundary gridPath_head gridPath_last gridPath_nodup
      gridPath_zip_fourNeighbor gridPath_close_fourNeighbor z w gridPath_length_four hrightCyclic
      hzout hmin
  have hconst := index_constant (T.cells : Set LatticeCell) hinside
    (fun a => GridRayCrossingIndex a gridPath)
    (fun a ha b hb hab => adjacent_index_same_status a b
      (by simp only [Finset.mem_coe] at ha hb; simp [ha, hb]) hab) q hq z hz
  rw [hconst]
  exact hzIndexNonzero

private theorem boundary_edge_cyclic (T : ProtoTile) (hinside : FourNeighborConnected (T.cells :
    Set LatticeCell)) (houtside : FourNeighborConnected ((T.cells : Set LatticeCell)ᶜ)) (gridPath
    : List GaussianInt) (y : GaussianInt) (x : GaussianInt) (cyclic_edge_boundary : ∀ (a b :
    GaussianInt), (a, b) ∈ gridPath.zip gridPath.tail ++ [(y, x)] → {a, b} ∈
    ApollonianSuperharmonic.BoundaryFootprintEdges T) (gridPath_head : gridPath.head? = some x)
    (gridPath_last : gridPath.getLast? = some y) (gridPath_nodup : gridPath.Nodup)
    (gridPath_zip_fourNeighbor : ∀ (a b : GaussianInt), (a, b) ∈ gridPath.zip gridPath.tail →
    ApollonianSuperharmonic.FourNeighborAdjacent a b) (gridPath_close_fourNeighbor :
    ApollonianSuperharmonic.FourNeighborAdjacent y x) (z : GaussianInt) (w :
    ApollonianSuperharmonic.LatticeCell) (gridPath_length_four : 4 ≤ gridPath.length)
    (hrightCyclic : (z + 1, z + 1 + { re := 0, im := 1 }) ∈ gridPath.zip gridPath.tail ++ [(y,
    x)] ∨ (z + 1 + { re := 0, im := 1 }, z + 1) ∈ gridPath.zip gridPath.tail ++ [(y, x)]) (hzout
    : z + 1 ∉ T.cells) (hz : z ∈ T.cells) (hmin : ∀ x' ∈ T.cells ∪ gridPath.toFinset, w.re ≤
    x'.re) (e : Finset GaussianInt) (he : e ∈ BoundaryFootprintEdges T) : ∃ a b : GaussianInt, e
    = {a, b} ∧ ((a, b) ∈ (cyclicEdges gridPath y x) ∨ (b, a) ∈ (cyclicEdges gridPath y x)) := by
  classical
  have gridPath_length : 3 ≤ gridPath.length := gridPath_length gridPath gridPath_length_four
  have component_index_control := GridRayCrossingIndexAdjacentCell gridPath x y
    gridPath_head gridPath_last gridPath_nodup gridPath_length
    gridPath_zip_fourNeighbor gridPath_close_fourNeighbor
  let cyclicEdges := (gridPath.zip gridPath.tail) ++ [(y, x)]
  have unoccupied_index_zero (q : LatticeCell) (hq : q ∉ T.cells) :
      GridRayCrossingIndex q gridPath = 0 := unoccupied_index_zero T houtside gridPath y x
          cyclic_edge_boundary gridPath_head gridPath_last gridPath_nodup
          gridPath_zip_fourNeighbor gridPath_close_fourNeighbor w gridPath_length_four hmin q hq
  have occupied_index_nonzero (q : LatticeCell) (hq : q ∈ T.cells) :
      GridRayCrossingIndex q gridPath ≠ 0 := occupied_index_nonzero T hinside houtside gridPath y
          x cyclic_edge_boundary gridPath_head gridPath_last gridPath_nodup
          gridPath_zip_fourNeighbor gridPath_close_fourNeighbor z w gridPath_length_four
          hrightCyclic hzout hz hmin q hq
  change (∃ a b : GaussianInt, e = {a, b} ∧
        ((a, b) ∈ cyclicEdges ∨ (b, a) ∈ cyclicEdges))
  rcases he with ⟨q, (⟨rfl, hxor⟩ | ⟨rfl, hxor⟩)⟩
  · refine ⟨q, q + 1, rfl, ?_⟩
    by_contra hnone
    rw [not_or] at hnone
    have hcontrol := (component_index_control (q - ⟨0, 1⟩)).2.2.1
    have heq : GridRayCrossingIndex q gridPath =
        GridRayCrossingIndex (q - ⟨0, 1⟩) gridPath := by
      have hraw := hcontrol (by
        constructor
        · simpa [cyclicEdges, Zsqrtd.ext_iff, add_assoc, add_comm,
            add_left_comm] using hnone.2
        · simpa [cyclicEdges, Zsqrtd.ext_iff, add_assoc, add_comm,
            add_left_comm] using hnone.1)
      simpa [Zsqrtd.ext_iff] using hraw
    rcases hxor with ⟨hq, hbelow⟩ | ⟨hq, hbelow⟩
    · rw [unoccupied_index_zero (q - ⟨0, 1⟩) hbelow] at heq
      exact occupied_index_nonzero q hq heq
    · rw [unoccupied_index_zero q hq] at heq
      exact occupied_index_nonzero (q - ⟨0, 1⟩) hbelow heq.symm
  · refine ⟨q, q + ⟨0, 1⟩, rfl, ?_⟩
    by_contra hnone
    rw [not_or] at hnone
    have hcontrol := (component_index_control (q - 1)).1
    have heq : GridRayCrossingIndex q gridPath =
        GridRayCrossingIndex (q - 1) gridPath := by
      have hraw := hcontrol (by
        constructor
        · simpa [cyclicEdges, Zsqrtd.ext_iff] using hnone.1
        · simpa [cyclicEdges, Zsqrtd.ext_iff] using hnone.2)
      simpa [Zsqrtd.ext_iff] using hraw
    rcases hxor with ⟨hq, hleft⟩ | ⟨hq, hleft⟩
    · rw [unoccupied_index_zero (q - 1) hleft] at heq
      exact occupied_index_nonzero q hq heq
    · rw [unoccupied_index_zero q hq] at heq
      exact occupied_index_nonzero (q - 1) hleft heq.symm

private theorem zip_mem_decompose (gridPath : List GaussianInt) (gridPath_length_four : 4 ≤
    gridPath.length) (a b : GaussianInt) (hab : (a, b) ∈ gridPath.zip gridPath.tail) : ∃ l₁ l₂ :
    List GaussianInt, gridPath = l₁ ++ a :: b :: l₂ := by
  classical
  rw [List.mem_iff_getElem] at hab
  rcases hab with ⟨i, hi, hab⟩
  have hi' : i < gridPath.tail.length := by
    simpa [List.length_zip] using hi
  have hi0 : i < gridPath.length := by
    simp only [List.length_tail] at hi'
    omega
  have hi1 : i + 1 < gridPath.length := by
    simp only [List.length_tail] at hi'
    omega
  rw [List.getElem_zip, List.getElem_tail] at hab
  injection hab with ha hb
  refine ⟨gridPath.take i, gridPath.drop (i + 2), ?_⟩
  calc
    gridPath = gridPath.take i ++ gridPath.drop i :=
      (List.take_append_drop i gridPath).symm
    _ = gridPath.take i ++ gridPath[i] :: gridPath.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hi0]
    _ = gridPath.take i ++ gridPath[i] :: gridPath[i + 1] ::
        gridPath.drop (i + 2) := by
      rw [List.drop_eq_getElem_cons hi1]
    _ = gridPath.take i ++ a :: b :: gridPath.drop (i + 2) := by
      rw [ha, hb]

private theorem cyclic_endpoints_mem (gridPath : List GaussianInt) (y : GaussianInt) (x :
    GaussianInt) (gridPath_head : gridPath.head? = some x) (gridPath_last : gridPath.getLast? =
    some y) (gridPath_length_four : 4 ≤ gridPath.length) (a b : GaussianInt) (hab : (a, b) ∈
    (cyclicEdges gridPath y x)) : a ∈ gridPath ∧ b ∈ gridPath := by
  classical
  let cyclicEdges := (gridPath.zip gridPath.tail) ++ [(y, x)]
  have zip_mem_decompose (a b : GaussianInt)
      (hab : (a, b) ∈ gridPath.zip gridPath.tail) :
      ∃ l₁ l₂ : List GaussianInt, gridPath = l₁ ++ a :: b :: l₂ := zip_mem_decompose gridPath
          gridPath_length_four a b hab
  simp only [List.mem_append, List.mem_singleton] at hab
  rcases hab with hab | hab
  · rcases zip_mem_decompose a b hab with ⟨l₁, l₂, hpath⟩
    rw [hpath]
    simp
  · have hab' : a = y ∧ b = x := Prod.mk.inj hab
    constructor
    · rw [hab'.1]
      exact List.getLast?_eq_some_iff.mp gridPath_last |>.choose_spec ▸
        (by simp)
    · rw [hab'.2]
      rcases List.head?_eq_some_iff.mp gridPath_head with ⟨l, hl⟩
      rw [hl]
      simp

private theorem boundary_vertices_eq (T : ProtoTile) (hinside : FourNeighborConnected (T.cells :
    Set LatticeCell)) (houtside : FourNeighborConnected ((T.cells : Set LatticeCell)ᶜ)) (gridPath
    : List GaussianInt) (y : GaussianInt) (x : GaussianInt) (cyclic_edge_boundary : ∀ (a b :
    GaussianInt), (a, b) ∈ gridPath.zip gridPath.tail ++ [(y, x)] → {a, b} ∈
    ApollonianSuperharmonic.BoundaryFootprintEdges T) (gridPath_mem_boundary : ∀ a ∈ gridPath, a
    ∈ ApollonianSuperharmonic.BoundaryFootprintVertices T) (gridPath_head : gridPath.head? = some
    x) (gridPath_last : gridPath.getLast? = some y) (gridPath_nodup : gridPath.Nodup)
    (gridPath_zip_fourNeighbor : ∀ (a b : GaussianInt), (a, b) ∈ gridPath.zip gridPath.tail →
    ApollonianSuperharmonic.FourNeighborAdjacent a b) (gridPath_close_fourNeighbor :
    ApollonianSuperharmonic.FourNeighborAdjacent y x) (z : GaussianInt) (w :
    ApollonianSuperharmonic.LatticeCell) (gridPath_length_four : 4 ≤ gridPath.length)
    (hrightCyclic : (z + 1, z + 1 + { re := 0, im := 1 }) ∈ gridPath.zip gridPath.tail ++ [(y,
    x)] ∨ (z + 1 + { re := 0, im := 1 }, z + 1) ∈ gridPath.zip gridPath.tail ++ [(y, x)]) (hzout
    : z + 1 ∉ T.cells) (hz : z ∈ T.cells) (hmin : ∀ x' ∈ T.cells ∪ gridPath.toFinset, w.re ≤
    x'.re) : BoundaryFootprintVertices T = (gridPath.toFinset : Set GaussianInt) := by
  classical
  have cells_nonempty : T.cells.Nonempty := cells_nonempty T hinside
  let cyclicEdges := (gridPath.zip gridPath.tail) ++ [(y, x)]
  have boundary_edge_cyclic (e : Finset GaussianInt)
      (he : e ∈ BoundaryFootprintEdges T) :
      ∃ a b : GaussianInt, e = {a, b} ∧
        ((a, b) ∈ cyclicEdges ∨ (b, a) ∈ cyclicEdges) := boundary_edge_cyclic T hinside houtside
            gridPath y x cyclic_edge_boundary gridPath_head gridPath_last gridPath_nodup
            gridPath_zip_fourNeighbor gridPath_close_fourNeighbor z w gridPath_length_four
            hrightCyclic hzout hz hmin e he
  have cyclic_endpoints_mem (a b : GaussianInt) (hab : (a, b) ∈ cyclicEdges) :
      a ∈ gridPath ∧ b ∈ gridPath := cyclic_endpoints_mem gridPath y x gridPath_head
          gridPath_last gridPath_length_four a b hab
  ext v
  constructor
  · intro hv
    rw [BoundaryFootprintVertices, ite_eq_left cells_nonempty] at hv
    rcases hv with ⟨e, he, hve⟩
    rcases boundary_edge_cyclic e he with ⟨a, b, rfl, hab⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hve
    rw [Finset.mem_coe, List.mem_toFinset]
    rcases hab with hab | hab
    · rcases cyclic_endpoints_mem a b hab with ⟨ha, hb⟩
      exact hve.elim (fun h => h ▸ ha) (fun h => h ▸ hb)
    · rcases cyclic_endpoints_mem b a hab with ⟨hb, ha⟩
      exact hve.elim (fun h => h ▸ ha) (fun h => h ▸ hb)
  · intro hv
    rw [Finset.mem_coe, List.mem_toFinset] at hv
    exact gridPath_mem_boundary v hv

private noncomputable abbrev n (gridPath : List GaussianInt) := gridPath.length - 3

private theorem hn (gridPath : List GaussianInt) (gridPath_length_four : 4 ≤ gridPath.length) : (n
    gridPath) + 3 = gridPath.length := by
  classical
  let n := gridPath.length - 3
  change (n + 3 = gridPath.length)
  dsimp only [n]; omega

private noncomputable abbrev v (gridPath : List GaussianInt) (gridPath_length_four : 4 ≤
    gridPath.length) : Fin ((n gridPath) + 3) → GaussianInt := by
  classical
  let n := gridPath.length - 3
  have hn : n + 3 = gridPath.length := hn gridPath gridPath_length_four
  change (Fin (n + 3) → GaussianInt)
  exact fun i => gridPath[i.val]'(by rw [← hn]; exact i.isLt)

private theorem v_injective (gridPath : List GaussianInt) (gridPath_nodup : gridPath.Nodup)
    (gridPath_length_four : 4 ≤ gridPath.length) : Function.Injective (v gridPath
    gridPath_length_four) := by
  classical
  let n := gridPath.length - 3
  have hn : n + 3 = gridPath.length := hn gridPath gridPath_length_four
  let v : Fin (n + 3) → GaussianInt :=
    fun i => gridPath[i.val]'(by rw [← hn]; exact i.isLt)
  change (Function.Injective v)
  intro i j hij
  apply Fin.ext
  exact (gridPath_nodup.getElem_inj_iff).mp hij

private theorem successor_val {n : Nat} (i : Fin (n + 3)) : (i + 1).val = if i.val + 1 < n + 3
    then i.val + 1 else 0 := by
  by_cases hi : i.val + 1 < n + 3
  · simp [Fin.val_add, Nat.mod_eq_of_lt (show 1 < n + 3 by omega),
      Nat.mod_eq_of_lt hi, hi]
  · have he : i.val + 1 = n + 3 := by omega
    simp [Fin.val_add, Nat.mod_eq_of_lt (show 1 < n + 3 by omega), he]

private theorem v_head (gridPath : List GaussianInt) (x : GaussianInt) (gridPath_head :
    gridPath.head? = some x) (gridPath_length_four : 4 ≤ gridPath.length) : (v gridPath
    gridPath_length_four) 0 = x := by
  classical
  have gridPath_length : 3 ≤ gridPath.length := gridPath_length gridPath gridPath_length_four
  let n := gridPath.length - 3
  have hn : n + 3 = gridPath.length := hn gridPath gridPath_length_four
  let v : Fin (n + 3) → GaussianInt :=
    fun i => gridPath[i.val]'(by rw [← hn]; exact i.isLt)
  change (v 0 = x)
  have hne : gridPath ≠ [] := by intro h; simp [h] at gridPath_length
  change gridPath[0] = x
  rw [← List.head_eq_getElem hne]
  simpa [List.head?_eq_some_head hne] using gridPath_head

private theorem v_last (gridPath : List GaussianInt) (y : GaussianInt) (gridPath_last :
    gridPath.getLast? = some y) (gridPath_length_four : 4 ≤ gridPath.length) : (v gridPath
    gridPath_length_four) ⟨(n gridPath) + 2, by omega⟩ = y := by
  classical
  have gridPath_length : 3 ≤ gridPath.length := gridPath_length gridPath gridPath_length_four
  let n := gridPath.length - 3
  have hn : n + 3 = gridPath.length := hn gridPath gridPath_length_four
  let v : Fin (n + 3) → GaussianInt :=
    fun i => gridPath[i.val]'(by rw [← hn]; exact i.isLt)
  change (v ⟨n + 2, by omega⟩ = y)
  have hne : gridPath ≠ [] := by intro h; simp [h] at gridPath_length
  change gridPath[n + 2] = y
  have he : n + 2 = gridPath.length - 1 := by omega
  simp only [he]
  rw [← List.getLast_eq_getElem hne]
  rw [List.getLast?_eq_getLast_of_ne_nil hne] at gridPath_last
  exact Option.some.inj gridPath_last

private theorem cyclic_index (gridPath : List GaussianInt) (y : GaussianInt) (x : GaussianInt)
    (gridPath_head : gridPath.head? = some x) (gridPath_last : gridPath.getLast? = some y)
    (gridPath_length_four : 4 ≤ gridPath.length) (i : Fin ((n gridPath) + 3)) : ((v gridPath
    gridPath_length_four) i, (v gridPath gridPath_length_four) (i + 1)) ∈ (cyclicEdges gridPath y
    x) := by
  classical
  let cyclicEdges := (gridPath.zip gridPath.tail) ++ [(y, x)]
  let n := gridPath.length - 3
  have hn : n + 3 = gridPath.length := hn gridPath gridPath_length_four
  let v : Fin (n + 3) → GaussianInt :=
    fun i => gridPath[i.val]'(by rw [← hn]; exact i.isLt)
  have successor_val (i : Fin (n + 3)) :
      (i + 1).val = if i.val + 1 < n + 3 then i.val + 1 else 0 := successor_val i
  have v_head : v 0 = x := v_head gridPath x gridPath_head gridPath_length_four
  have v_last : v ⟨n + 2, by omega⟩ = y := v_last gridPath y gridPath_last gridPath_length_four
  change ((v i, v (i + 1)) ∈ cyclicEdges)
  have hi_bound : i.val < n + 3 := i.isLt
  by_cases hi : i.val + 1 < n + 3
  · have hvnext : v (i + 1) = gridPath[i.val + 1]'(by omega) := by
      simp only [v, successor_val, ite_eq_left hi]
    have hpair : (v i, v (i + 1)) ∈ gridPath.zip gridPath.tail := by
      rw [List.mem_iff_getElem]
      refine ⟨i.val, ?_, ?_⟩
      · simp only [List.length_zip, List.length_tail]; omega
      · rw [List.getElem_zip, List.getElem_tail, hvnext]
    exact List.mem_append_left _ hpair
  · have hiLast : i = ⟨n + 2, by omega⟩ := by
      apply Fin.ext
      change i.val = n + 2
      omega
    have hnext : i + 1 = 0 := by
      apply Fin.ext
      simp only [successor_val, ite_eq_right hi, Fin.val_zero]
    rw [hnext, hiLast, v_last, v_head]
    simp [cyclicEdges]

private theorem cyclic_rep (gridPath : List GaussianInt) (y : GaussianInt) (x : GaussianInt)
    (gridPath_head : gridPath.head? = some x) (gridPath_last : gridPath.getLast? = some y)
    (gridPath_length_four : 4 ≤ gridPath.length) (a b : GaussianInt) (hab : (a, b) ∈ (cyclicEdges
    gridPath y x)) : ∃ i : Fin ((n gridPath) + 3), a = (v gridPath gridPath_length_four) i ∧ b =
    (v gridPath gridPath_length_four) (i + 1) := by
  classical
  let cyclicEdges := (gridPath.zip gridPath.tail) ++ [(y, x)]
  let n := gridPath.length - 3
  have hn : n + 3 = gridPath.length := hn gridPath gridPath_length_four
  let v : Fin (n + 3) → GaussianInt :=
    fun i => gridPath[i.val]'(by rw [← hn]; exact i.isLt)
  have successor_val (i : Fin (n + 3)) :
      (i + 1).val = if i.val + 1 < n + 3 then i.val + 1 else 0 := successor_val i
  have v_head : v 0 = x := v_head gridPath x gridPath_head gridPath_length_four
  have v_last : v ⟨n + 2, by omega⟩ = y := v_last gridPath y gridPath_last gridPath_length_four
  change (∃ i : Fin (n + 3), a = v i ∧ b = v (i + 1))
  simp only [List.mem_append, List.mem_singleton] at hab
  rcases hab with hab | hab
  · rw [List.mem_iff_getElem] at hab
    rcases hab with ⟨j, hj, hab⟩
    have hj1 : j + 1 < gridPath.length := by
      simp only [List.length_zip, List.length_tail] at hj; omega
    rw [List.getElem_zip, List.getElem_tail] at hab
    have ha : gridPath[j] = a := congrArg Prod.fst hab
    have hb : gridPath[j + 1] = b := congrArg Prod.snd hab
    let i : Fin (n + 3) := ⟨j, by omega⟩
    refine ⟨i, ha.symm, ?_⟩
    have hi : i.val + 1 < n + 3 := by dsimp only [i]; omega
    simpa only [v, successor_val, ite_eq_left hi, i] using hb.symm
  · have hab' : a = y ∧ b = x := Prod.mk.inj hab
    refine ⟨⟨n + 2, by omega⟩, hab'.1.trans v_last.symm, ?_⟩
    have hnext : (⟨n + 2, by omega⟩ : Fin (n + 3)) + 1 = 0 := by
      apply Fin.ext
      simp [successor_val]
    rw [hnext, v_head]
    exact hab'.2

private theorem edge_distinct {n : Nat} (v : Fin (n + 3) → GaussianInt) (v_injective :
    Function.Injective v) (i j : Fin (n + 3)) (hij : i ≠ j) : ({v i, v (i + 1)} : Finset
    GaussianInt) ≠ {v j, v (j + 1)} := by
  classical
  intro he
  have hi : v i ∈ ({v j, v (j + 1)} : Finset GaussianInt) := by rw [← he]; simp
  have hi1 : v (i + 1) ∈ ({v j, v (j + 1)} : Finset GaussianInt) := by
    rw [← he]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hi1
  rcases hi with hi | hi
  · exact hij (v_injective hi)
  · have he1 : i = j + 1 := v_injective hi
    rcases hi1 with hi1 | hi1
    · have he2 : i + 1 = j := v_injective hi1
      have hv1 := congrArg Fin.val he1
      have hv2 := congrArg Fin.val he2
      simp only [successor_val] at hv1 hv2
      split_ifs at hv1 hv2 <;> omega
    · have he2 : i + 1 = j + 1 := v_injective hi1
      exact hij (add_right_cancel he2)

private theorem vertex_rational (gridPath : List GaussianInt) (gridPath_length_four : 4 ≤
    gridPath.length) (i : Fin ((n gridPath) + 3)) : ∃ r s : Rat, GaussianRealPoint ((v gridPath
    gridPath_length_four) i) = ((r : Real), (s : Real)) := by
  classical
  let n := gridPath.length - 3
  have hn : n + 3 = gridPath.length := hn gridPath gridPath_length_four
  let v : Fin (n + 3) → GaussianInt :=
    fun i => gridPath[i.val]'(by rw [← hn]; exact i.isLt)
  change (∃ r s : Rat, GaussianRealPoint (v i) = ((r : Real), (s : Real)))
  refine ⟨((v i).re : Rat), ((v i).im : Rat), ?_⟩
  simp only [GaussianRealPoint, Rat.cast_intCast]

private theorem point_injective : Function.Injective GaussianRealPoint := by
  classical
  intro a b hab
  apply Zsqrtd.ext
  · have h := congrArg Prod.fst hab
    change (a.re : Real) = (b.re : Real) at h
    exact_mod_cast h
  · have h := congrArg Prod.snd hab
    change (a.im : Real) = (b.im : Real) at h
    exact_mod_cast h

private theorem v_adj (gridPath : List GaussianInt) (y : GaussianInt) (x : GaussianInt)
    (gridPath_head : gridPath.head? = some x) (gridPath_last : gridPath.getLast? = some y)
    (gridPath_length_four : 4 ≤ gridPath.length) (cyclic_edge_fourNeighbor : ∀ (a b :
    GaussianInt), (a, b) ∈ gridPath.zip gridPath.tail ++ [(y, x)] →
    ApollonianSuperharmonic.FourNeighborAdjacent a b) (i : Fin ((n gridPath) + 3)) :
    FourNeighborAdjacent ((v gridPath gridPath_length_four) i) ((v gridPath gridPath_length_four)
    (i + 1)) := by
  classical
  let cyclicEdges := (gridPath.zip gridPath.tail) ++ [(y, x)]
  let n := gridPath.length - 3
  have hn : n + 3 = gridPath.length := hn gridPath gridPath_length_four
  let v : Fin (n + 3) → GaussianInt :=
    fun i => gridPath[i.val]'(by rw [← hn]; exact i.isLt)
  have cyclic_index (i : Fin (n + 3)) : (v i, v (i + 1)) ∈ cyclicEdges := cyclic_index gridPath y
      x gridPath_head gridPath_last gridPath_length_four i
  change (FourNeighborAdjacent (v i) (v (i + 1)))
  exact cyclic_edge_fourNeighbor _ _ (cyclic_index i)

private noncomputable abbrev polygon (gridPath : List GaussianInt) (y : GaussianInt) (x :
    GaussianInt) (gridPath_head : gridPath.head? = some x) (gridPath_last : gridPath.getLast? =
    some y) (gridPath_nodup : gridPath.Nodup) (gridPath_length_four : 4 ≤ gridPath.length)
    (cyclic_edge_fourNeighbor : ∀ (a b : GaussianInt), (a, b) ∈ gridPath.zip gridPath.tail ++
    [(y, x)] → ApollonianSuperharmonic.FourNeighborAdjacent a b) : P3381T1PolygonBoundary (n
    gridPath) := by
  classical
  let n := gridPath.length - 3
  have hn : n + 3 = gridPath.length := hn gridPath gridPath_length_four
  let v : Fin (n + 3) → GaussianInt :=
    fun i => gridPath[i.val]'(by rw [← hn]; exact i.isLt)
  have v_injective : Function.Injective v := v_injective gridPath gridPath_nodup
      gridPath_length_four
  have edge_distinct (i j : Fin (n + 3)) (hij : i ≠ j) :
      ({v i, v (i + 1)} : Finset GaussianInt) ≠ {v j, v (j + 1)} := edge_distinct v v_injective i
          j hij
  have vertex_rational (i : Fin (n + 3)) :
      ∃ r s : Rat, GaussianRealPoint (v i) = ((r : Real), (s : Real)) := vertex_rational gridPath
          gridPath_length_four i
  have point_injective : Function.Injective GaussianRealPoint := point_injective
  have v_adj (i : Fin (n + 3)) : FourNeighborAdjacent (v i) (v (i + 1)) := v_adj gridPath y x
      gridPath_head gridPath_last gridPath_length_four cyclic_edge_fourNeighbor i
  change (P3381T1PolygonBoundary n)
  exact {
      vertex := GaussianRealPoint ∘ v
      rational := vertex_rational
      injective := point_injective.comp v_injective
      edge_intersection := fun i j hij =>
        P3475T1UnitSegmentIntersection _ _ _ _ (v_adj i) (v_adj j)
          (edge_distinct i j hij) }

end GridBoundaryConstruction

theorem P3475T1GridBoundary (T : ProtoTile)
    (hinside : FourNeighborConnected (T.cells : Set LatticeCell))
    (houtside : FourNeighborConnected ((T.cells : Set LatticeCell)ᶜ))
    (hchecker : NoCheckerboardCellVertex (T.cells : Set LatticeCell)) :
    ∃ (n : Nat) (p : P3381T1PolygonBoundary n)
      (v : Fin (n + 3) → GaussianInt),
      (∀ i, p.vertex i = GaussianRealPoint (v i)) ∧
      (∀ i, FourNeighborAdjacent (v i) (v (i + 1))) ∧
      BoundaryFootprintVertices T = Set.range v ∧
      BoundaryFootprintEdges T = {e | ∃ i, e = {v i, v (i + 1)}} := by
-- BODY
  classical
  have cells_nonempty : T.cells.Nonempty := GridBoundaryConstruction.cells_nonempty T hinside
  have boundary_degree_two :
      ∀ v ∈ BoundaryFootprintVertices T,
        Set.ncard {e : Finset GaussianInt |
          e ∈ BoundaryFootprintEdges T ∧ v ∈ e} = 2 :=
              GridBoundaryConstruction.boundary_degree_two T hinside hchecker
  obtain ⟨gridPath, x, y, z, gridPath_nodup, gridPath_length_four,
      gridPath_head, gridPath_last, gridPath_chain, gridPath_close,
      gridPath_fourNeighbor, gridPath_close_fourNeighbor, gridPath_zip_fourNeighbor,
      gridPath_mem_boundary, hz, hmax, hzout, cyclic_edge_boundary,
      cyclic_edge_fourNeighbor, component_edge_cyclic, hrightCyclic⟩ :=
    P5620T1BoundaryComponentCycle T cells_nonempty boundary_degree_two
  have gridPath_length : 3 ≤ gridPath.length := GridBoundaryConstruction.gridPath_length gridPath
      gridPath_length_four
  have component_index_control := GridRayCrossingIndexAdjacentCell gridPath x y
    gridPath_head gridPath_last gridPath_nodup gridPath_length
    gridPath_zip_fourNeighbor gridPath_close_fourNeighbor
  let cyclicEdges := (gridPath.zip gridPath.tail) ++ [(y, x)]
  have same_vertical_not_boundary (q : LatticeCell)
      (hstatus : q ∈ T.cells ↔ q - 1 ∈ T.cells) :
      ({q, q + ⟨0, 1⟩} : Finset GaussianInt) ∉ BoundaryFootprintEdges T :=
          GridBoundaryConstruction.same_vertical_not_boundary T q hstatus
  have same_horizontal_not_boundary (q : LatticeCell)
      (hstatus : q ∈ T.cells ↔ q - ⟨0, 1⟩ ∈ T.cells) :
      ({q, q + 1} : Finset GaussianInt) ∉ BoundaryFootprintEdges T :=
          GridBoundaryConstruction.same_horizontal_not_boundary T q hstatus
  have adjacent_index_same_status (a b : LatticeCell)
      (hs : a ∈ T.cells ↔ b ∈ T.cells) (hab : FourNeighborAdjacent a b) :
      GridRayCrossingIndex a gridPath = GridRayCrossingIndex b gridPath :=
          GridBoundaryConstruction.adjacent_index_same_status T gridPath y x cyclic_edge_boundary
          gridPath_head gridPath_last gridPath_nodup gridPath_zip_fourNeighbor
          gridPath_close_fourNeighbor gridPath_length_four a b hs hab
  have index_constant (S : Set LatticeCell) (hS : FourNeighborConnected S)
      (I : LatticeCell → Int)
      (hstep : ∀ a, a ∈ S → ∀ b, b ∈ S →
        FourNeighborAdjacent a b → I a = I b)
      (x : LatticeCell) (hx : x ∈ S) (y : LatticeCell) (hy : y ∈ S) :
      I x = I y := GridBoundaryConstruction.index_constant S hS I hstep x hx y hy
  obtain ⟨w, hw, hmin⟩ := (T.cells ∪ gridPath.toFinset).exists_min_image
    (fun q => q.re) (by
      obtain ⟨a, ha⟩ := cells_nonempty
      exact ⟨a, Finset.mem_union_left _ ha⟩)
  let q0 : LatticeCell := ⟨w.re - 1, 0⟩
  have q0_outside : q0 ∉ T.cells := GridBoundaryConstruction.q0_outside T gridPath w hmin
  have path_left (a : GaussianInt) (ha : a ∈ gridPath) : q0.re < a.re :=
      GridBoundaryConstruction.path_left T gridPath w hmin a ha
  let step : GaussianInt → GaussianInt → Int := fun a b =>
    if b = a + ⟨0, 1⟩ ∧ a.im = q0.im ∧ a.re ≤ q0.re then 1
    else if b = a - ⟨0, 1⟩ ∧ b.im = q0.im ∧ a.re ≤ q0.re then -1 else 0
  have step_zero (a : GaussianInt) (ha : a ∈ gridPath) (b : GaussianInt) :
      step a b = 0 := GridBoundaryConstruction.step_zero T gridPath w hmin a ha b
  have zip_zero (r s : List GaussianInt) (hr : ∀ a ∈ r, a ∈ gridPath) :
      (List.zipWith step r s).sum = 0 := GridBoundaryConstruction.zip_zero T gridPath w hmin r s hr
  have q0_index_zero : GridRayCrossingIndex q0 gridPath = 0 :=
      GridBoundaryConstruction.q0_index_zero T gridPath y x gridPath_head gridPath_last w hmin
  have unoccupied_index_zero (q : LatticeCell) (hq : q ∉ T.cells) :
      GridRayCrossingIndex q gridPath = 0 := GridBoundaryConstruction.unoccupied_index_zero T
          houtside gridPath y x cyclic_edge_boundary gridPath_head gridPath_last gridPath_nodup
          gridPath_zip_fourNeighbor gridPath_close_fourNeighbor w gridPath_length_four hmin q hq
  have hrightJump :
      Int.natAbs (GridRayCrossingIndex (z + 1) gridPath -
        GridRayCrossingIndex z gridPath) = 1 := GridBoundaryConstruction.hrightJump gridPath y x
            gridPath_head gridPath_last gridPath_nodup gridPath_zip_fourNeighbor
            gridPath_close_fourNeighbor z gridPath_length_four hrightCyclic
  have hzIndexNonzero : GridRayCrossingIndex z gridPath ≠ 0 :=
      GridBoundaryConstruction.hzIndexNonzero T houtside gridPath y x cyclic_edge_boundary
      gridPath_head gridPath_last gridPath_nodup gridPath_zip_fourNeighbor
      gridPath_close_fourNeighbor z w gridPath_length_four hrightCyclic hzout hmin
  have occupied_index_nonzero (q : LatticeCell) (hq : q ∈ T.cells) :
      GridRayCrossingIndex q gridPath ≠ 0 := GridBoundaryConstruction.occupied_index_nonzero T
          hinside houtside gridPath y x cyclic_edge_boundary gridPath_head gridPath_last
          gridPath_nodup gridPath_zip_fourNeighbor gridPath_close_fourNeighbor z w
          gridPath_length_four hrightCyclic hzout hz hmin q hq
  have boundary_edge_cyclic (e : Finset GaussianInt)
      (he : e ∈ BoundaryFootprintEdges T) :
      ∃ a b : GaussianInt, e = {a, b} ∧
        ((a, b) ∈ cyclicEdges ∨ (b, a) ∈ cyclicEdges) :=
            GridBoundaryConstruction.boundary_edge_cyclic T hinside houtside gridPath y x
            cyclic_edge_boundary gridPath_head gridPath_last gridPath_nodup
            gridPath_zip_fourNeighbor gridPath_close_fourNeighbor z w gridPath_length_four
            hrightCyclic hzout hz hmin e he
  have zip_mem_decompose (a b : GaussianInt)
      (hab : (a, b) ∈ gridPath.zip gridPath.tail) :
      ∃ l₁ l₂ : List GaussianInt, gridPath = l₁ ++ a :: b :: l₂ :=
          GridBoundaryConstruction.zip_mem_decompose gridPath gridPath_length_four a b hab
  have cyclic_endpoints_mem (a b : GaussianInt) (hab : (a, b) ∈ cyclicEdges) :
      a ∈ gridPath ∧ b ∈ gridPath := GridBoundaryConstruction.cyclic_endpoints_mem gridPath y x
          gridPath_head gridPath_last gridPath_length_four a b hab
  have boundary_vertices_eq :
      BoundaryFootprintVertices T = (gridPath.toFinset : Set GaussianInt) :=
          GridBoundaryConstruction.boundary_vertices_eq T hinside houtside gridPath y x
          cyclic_edge_boundary gridPath_mem_boundary gridPath_head gridPath_last gridPath_nodup
          gridPath_zip_fourNeighbor gridPath_close_fourNeighbor z w gridPath_length_four
          hrightCyclic hzout hz hmin
  let n := gridPath.length - 3
  have hn : n + 3 = gridPath.length := GridBoundaryConstruction.hn gridPath gridPath_length_four
  let v : Fin (n + 3) → GaussianInt :=
    fun i => gridPath[i.val]'(by rw [← hn]; exact i.isLt)
  have v_injective : Function.Injective v := GridBoundaryConstruction.v_injective gridPath
      gridPath_nodup gridPath_length_four
  have successor_val (i : Fin (n + 3)) :
      (i + 1).val = if i.val + 1 < n + 3 then i.val + 1 else 0 :=
          GridBoundaryConstruction.successor_val i
  have v_head : v 0 = x := GridBoundaryConstruction.v_head gridPath x gridPath_head
      gridPath_length_four
  have v_last : v ⟨n + 2, by omega⟩ = y := GridBoundaryConstruction.v_last gridPath y
      gridPath_last gridPath_length_four
  have cyclic_index (i : Fin (n + 3)) : (v i, v (i + 1)) ∈ cyclicEdges :=
      GridBoundaryConstruction.cyclic_index gridPath y x gridPath_head gridPath_last
          gridPath_length_four i
  have cyclic_rep (a b : GaussianInt) (hab : (a, b) ∈ cyclicEdges) :
      ∃ i : Fin (n + 3), a = v i ∧ b = v (i + 1) := GridBoundaryConstruction.cyclic_rep gridPath
          y x gridPath_head gridPath_last gridPath_length_four a b hab
  have edge_distinct (i j : Fin (n + 3)) (hij : i ≠ j) :
      ({v i, v (i + 1)} : Finset GaussianInt) ≠ {v j, v (j + 1)} :=
          GridBoundaryConstruction.edge_distinct v v_injective
          i j hij
  have vertex_rational (i : Fin (n + 3)) :
      ∃ r s : Rat, GaussianRealPoint (v i) = ((r : Real), (s : Real)) :=
          GridBoundaryConstruction.vertex_rational gridPath gridPath_length_four i
  have point_injective : Function.Injective GaussianRealPoint :=
      GridBoundaryConstruction.point_injective
  have v_adj (i : Fin (n + 3)) : FourNeighborAdjacent (v i) (v (i + 1)) :=
      GridBoundaryConstruction.v_adj gridPath y x gridPath_head gridPath_last
          gridPath_length_four cyclic_edge_fourNeighbor i
  let polygon : P3381T1PolygonBoundary n :=
    { vertex := GaussianRealPoint ∘ v
      rational := vertex_rational
      injective := point_injective.comp v_injective
      edge_intersection := fun i j hij =>
        P3475T1UnitSegmentIntersection _ _ _ _ (v_adj i) (v_adj j)
          (edge_distinct i j hij) }
  refine ⟨n, polygon, v, fun _ => rfl, v_adj, ?_, ?_⟩
  · rw [boundary_vertices_eq]
    ext a
    simp only [Finset.mem_coe, List.mem_toFinset, Set.mem_range]
    constructor
    · intro ha
      rcases List.mem_iff_getElem.mp ha with ⟨i, hi, hia⟩
      exact ⟨⟨i, by omega⟩, hia⟩
    · rintro ⟨i, rfl⟩
      exact List.getElem_mem (by rw [← hn]; exact i.isLt)
  · ext e
    constructor
    · intro he
      rcases boundary_edge_cyclic e he with ⟨a, b, he, hab | hab⟩
      · obtain ⟨i, rfl, rfl⟩ := cyclic_rep a b hab
        exact ⟨i, he⟩
      · obtain ⟨i, rfl, rfl⟩ := cyclic_rep b a hab
        exact ⟨i, he.trans (Finset.pair_comm _ _)⟩
    · rintro ⟨i, rfl⟩
      exact cyclic_edge_boundary _ _ (cyclic_index i)

end ApollonianSuperharmonic

end
