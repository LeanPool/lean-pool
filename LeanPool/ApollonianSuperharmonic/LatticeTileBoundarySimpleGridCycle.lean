/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintEdges
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertexDegreeTwo
public import LeanPool.ApollonianSuperharmonic.ClosedSquareRealization
public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent
public import LeanPool.ApollonianSuperharmonic.P5620T1BoundaryComponentCycle
public import LeanPool.ApollonianSuperharmonic.GridRayCrossingIndexAdjacentCell
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.LatticeTileFourNeighborConnected
public import LeanPool.ApollonianSuperharmonic.LatticeTileNoCheckerboard
public import LeanPool.ApollonianSuperharmonic.ProtoTile
public import LeanPool.ApollonianSuperharmonic.SimpleGridCycle
public import LeanPool.ApollonianSuperharmonic.TileRealization
public import LeanPool.ApollonianSuperharmonic.TopologicalDiskGridRayCrossingIndexZero

-- [TABLET NODE: LatticeTileBoundarySimpleGridCycle]

/-!
# LatticeTileBoundarySimpleGridCycle

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace BoundaryCycleProof

private theorem closed_grid_index_zero :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (LatticeTile T) → (∀ (q : LatticeCell), ∀ (p : List GaussianInt), ∀ (x
            : GaussianInt), ∀ (y : GaussianInt), ((((q.re : Int) : Real) + (1 / 2 : Real)),
            (((q.im : Int) : Real) + (1 / 2 : Real))) ∉ TileRealization T → p.head? = some x →
            p.getLast? = some y → (∀ a b : GaussianInt, ∀ l₁ l₂ : List GaussianInt, p = l₁ ++ a
            :: b :: l₂ → FourNeighborAdjacent a b) → FourNeighborAdjacent y x → (∀ a b :
            GaussianInt, ((∃ l₁ l₂ : List GaussianInt, p = l₁ ++ a :: b :: l₂) ∨ (a = y ∧ b = x))
            → ∀ t : Set.Icc (0 : Real) 1, ((1 - (t : Real)) * ((a.re : Int) : Real) + (t : Real)
            * ((b.re : Int) : Real), (1 - (t : Real)) * ((a.im : Int) : Real) + (t : Real) *
            ((b.im : Int) : Real)) ∈ TileRealization T) → GridRayCrossingIndex q p = 0)
    ) := by
  classical
  intro T hT q p x y hq hhead hlast hadj hclose hedge
  exact TopologicalDiskGridRayCrossingIndexZero
    (TileRealization T) hT q hq p x y hhead hlast hadj hclose hedge

private theorem adjacent_grid_index_control :
    (by
      classical
      exact
        ∀ (p : List GaussianInt), ∀ (x : GaussianInt), ∀ (y : GaussianInt), p.head? = some x →
            p.getLast? = some y → p.Nodup → 3 ≤ p.length →
            (∀ a, ∀ b, (a, b) ∈ p.zip p.tail → FourNeighborAdjacent a b) →
            FourNeighborAdjacent y x →
            let cyclicEdges := (p.zip p.tail) ++ [(y, x)]
            ∀ q : LatticeCell,
              (((q + 1, q + 1 + ⟨0, 1⟩) ∉ cyclicEdges ∧
                  (q + 1 + ⟨0, 1⟩, q + 1) ∉ cyclicEdges) →
                  GridRayCrossingIndex (q + 1) p = GridRayCrossingIndex q p) ∧
              (((q + 1, q + 1 + ⟨0, 1⟩) ∈ cyclicEdges ∨
                  (q + 1 + ⟨0, 1⟩, q + 1) ∈ cyclicEdges) →
                  Int.natAbs (GridRayCrossingIndex (q + 1) p -
                    GridRayCrossingIndex q p) = 1) ∧
              (((q + 1 + ⟨0, 1⟩, q + ⟨0, 1⟩) ∉ cyclicEdges ∧
                  (q + ⟨0, 1⟩, q + 1 + ⟨0, 1⟩) ∉ cyclicEdges) →
                  GridRayCrossingIndex (q + ⟨0, 1⟩) p =
                    GridRayCrossingIndex q p) ∧
              (((q + 1 + ⟨0, 1⟩, q + ⟨0, 1⟩) ∈ cyclicEdges ∨
                  (q + ⟨0, 1⟩, q + 1 + ⟨0, 1⟩) ∈ cyclicEdges) →
                  Int.natAbs (GridRayCrossingIndex (q + ⟨0, 1⟩) p -
                    GridRayCrossingIndex q p) = 1)
    ) := by
  classical
  intro p x y hhead hlast hnodup hlen hadj hclose
  exact GridRayCrossingIndexAdjacentCell p x y hhead hlast hnodup hlen hadj hclose

private theorem boundary_edge_segment :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (∀ (e : Finset GaussianInt), (e ∈ BoundaryFootprintEdges T) → (e.card
            = 2)) → (∀ (a : GaussianInt), ∀ (b : GaussianInt), {a, b} ∈ BoundaryFootprintEdges T
            → ∀ (t : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)), (((1 : ℝ) - (↑t : ℝ)) * (↑a.re : ℝ) +
            (↑t : ℝ) * (↑b.re : ℝ), ((1 : ℝ) - (↑t : ℝ)) * (↑a.im : ℝ) + (↑t : ℝ) * (↑b.im : ℝ))
            ∈ TileRealization T)
    ) := by
  classical
  intro T boundary_edge_card_two a b hab
  have habne : a ≠ b := by
    intro heq
    subst b
    have hc := boundary_edge_card_two {a, a} hab
    simp at hc
  intro t
  rcases hab with ⟨q, (⟨heq, hocc⟩ | ⟨heq, hocc⟩)⟩
  · have ha : a = q ∨ a = q + 1 := by
      have : a ∈ ({q, q + 1} : Finset GaussianInt) := by rw [← heq]; simp
      simpa using this
    have hb : b = q ∨ b = q + 1 := by
      have : b ∈ ({q, q + 1} : Finset GaussianInt) := by rw [← heq]; simp
      simpa using this
    rcases hocc with ⟨hq, _⟩ | ⟨_, hq⟩
    · rw [TileRealization]
      refine Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨hq, ?_⟩⟩
      rcases ha with rfl | rfl
      · rcases hb with rfl | rfl
        · exact (habne rfl).elim
        · simp [ClosedSquareRealization]
          constructor <;> constructor <;> linarith [t.property.1, t.property.2]
      · rcases hb with rfl | rfl
        · simp [ClosedSquareRealization]
          constructor <;> constructor <;> linarith [t.property.1, t.property.2]
        · exact (habne rfl).elim
    · rw [TileRealization]
      refine Set.mem_iUnion.2 ⟨q - ⟨0, 1⟩, Set.mem_iUnion.2 ⟨hq, ?_⟩⟩
      rcases ha with rfl | rfl
      · rcases hb with rfl | rfl
        · exact (habne rfl).elim
        · simp [ClosedSquareRealization]
          constructor <;> constructor <;> linarith [t.property.1, t.property.2]
      · rcases hb with rfl | rfl
        · simp [ClosedSquareRealization]
          constructor <;> constructor <;> linarith [t.property.1, t.property.2]
        · exact (habne rfl).elim
  · have ha : a = q ∨ a = q + ⟨0, 1⟩ := by
      have : a ∈ ({q, q + ⟨0, 1⟩} : Finset GaussianInt) := by rw [← heq]; simp
      simpa using this
    have hb : b = q ∨ b = q + ⟨0, 1⟩ := by
      have : b ∈ ({q, q + ⟨0, 1⟩} : Finset GaussianInt) := by rw [← heq]; simp
      simpa using this
    rcases hocc with ⟨hq, _⟩ | ⟨_, hq⟩
    · rw [TileRealization]
      refine Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨hq, ?_⟩⟩
      rcases ha with rfl | rfl
      · rcases hb with rfl | rfl
        · exact (habne rfl).elim
        · simp [ClosedSquareRealization]
          constructor <;> constructor <;> linarith [t.property.1, t.property.2]
      · rcases hb with rfl | rfl
        · simp [ClosedSquareRealization]
          constructor <;> constructor <;> linarith [t.property.1, t.property.2]
        · exact (habne rfl).elim
    · rw [TileRealization]
      refine Set.mem_iUnion.2 ⟨q - 1, Set.mem_iUnion.2 ⟨hq, ?_⟩⟩
      rcases ha with rfl | rfl
      · rcases hb with rfl | rfl
        · exact (habne rfl).elim
        · simp [ClosedSquareRealization]
          constructor <;> constructor <;> linarith [t.property.1, t.property.2]
      · rcases hb with rfl | rfl
        · simp [ClosedSquareRealization]
          constructor <;> constructor <;> linarith [t.property.1, t.property.2]
        · exact (habne rfl).elim

private theorem unoccupied_center_outside :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (List GaussianInt) → (∀ q ∉ T.cells, ((↑q.re : ℝ) + (1 / 2 : ℝ),
            (↑q.im : ℝ) + (1 / 2 : ℝ)) ∉ TileRealization T)
    ) := by
  classical
  intro T gridPath q hq hcenter
  rw [TileRealization] at hcenter
  simp only [Set.mem_iUnion] at hcenter
  rcases hcenter with ⟨w, hw, hqw⟩
  simp only [ClosedSquareRealization, Set.mem_Icc] at hqw
  have hre_lt : (w.re : Int) < q.re + 1 := by
    exact_mod_cast (show ((w.re : Int) : Real) < ((q.re : Int) : Real) + 1 by
      linarith [hqw.1.1])
  have hre_gt : (q.re : Int) < w.re + 1 := by
    exact_mod_cast (show ((q.re : Int) : Real) < ((w.re : Int) : Real) + 1 by
      linarith [hqw.2.1])
  have him_lt : (w.im : Int) < q.im + 1 := by
    exact_mod_cast (show ((w.im : Int) : Real) < ((q.im : Int) : Real) + 1 by
      linarith [hqw.1.2])
  have him_gt : (q.im : Int) < w.im + 1 := by
    exact_mod_cast (show ((q.im : Int) : Real) < ((w.im : Int) : Real) + 1 by
      linarith [hqw.2.2])
  have hwq : w = q := by
    apply Zsqrtd.ext <;> omega
  exact hq (hwq ▸ hw)

private theorem unoccupied_index_zero :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (∀ (q : LatticeCell), ∀ (p : List GaussianInt), ∀ (x : GaussianInt), ∀
            (y : GaussianInt), ((((q.re : Int) : Real) + (1 / 2 : Real)), (((q.im : Int) : Real)
            + (1 / 2 : Real))) ∉ TileRealization T → p.head? = some x → p.getLast? = some y → (∀
            a b : GaussianInt, ∀ l₁ l₂ : List GaussianInt, p = l₁ ++ a :: b :: l₂ →
            FourNeighborAdjacent a b) → FourNeighborAdjacent y x → (∀ a b : GaussianInt, ((∃ l₁
            l₂ : List GaussianInt, p = l₁ ++ a :: b :: l₂) ∨ (a = y ∧ b = x)) → ∀ t : Set.Icc (0
            : Real) 1, ((1 - (t : Real)) * ((a.re : Int) : Real) + (t : Real) * ((b.re : Int) :
            Real), (1 - (t : Real)) * ((a.im : Int) : Real) + (t : Real) * ((b.im : Int) : Real))
            ∈ TileRealization T) → GridRayCrossingIndex q p = 0) → (∀ (gridPath : List
            GaussianInt), ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (z : GaussianInt),
            (gridPath.head? = some x) → ((gridPath.getLast? = some y) → ((List.IsChain (fun (a b
            : GaussianInt) => {a, b} ∈ BoundaryFootprintEdges T) gridPath) → (({y, x} ∈
            BoundaryFootprintEdges T) → ((List.IsChain FourNeighborAdjacent gridPath) →
            ((FourNeighborAdjacent y x) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), (a, b) ∈
            gridPath.zip gridPath.tail ++ [(y, x)] → {a, b} ∈ BoundaryFootprintEdges T) → ((∀ (a
            : GaussianInt), ∀ (b : GaussianInt), (a, b) ∈ gridPath.zip gridPath.tail ++ [(y, x)]
            → FourNeighborAdjacent a b) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), a ∈
            gridPath → {a, b} ∈ BoundaryFootprintEdges T → (a, b) ∈ gridPath.zip gridPath.tail ++
            [(y, x)] ∨ (b, a) ∈ gridPath.zip gridPath.tail ++ [(y, x)]) → (((z + (1 :
            GaussianInt), z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∈ gridPath.zip
            gridPath.tail ++ [(y, x)] ∨ (z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩, z + (1 :
            GaussianInt)) ∈ gridPath.zip gridPath.tail ++ [(y, x)]) → (
        let cyclicEdges := (gridPath.zip gridPath.tail) ++ [(y, x)]
        (
        let cyclicEdges := gridPath.zip gridPath.tail ++ [(y, x)];
    ∀ (q : LatticeCell), ((q + (1 : LatticeCell), q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∉
        cyclicEdges ∧
            (q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩, q + (1 : LatticeCell)) ∉ cyclicEdges →
          GridRayCrossingIndex (q + (1 : LatticeCell)) gridPath = GridRayCrossingIndex q gridPath) ∧
        ((q + (1 : LatticeCell), q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∈ cyclicEdges ∨
              (q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩, q + (1 : LatticeCell)) ∈ cyclicEdges →
            (GridRayCrossingIndex (q + (1 : LatticeCell)) gridPath - GridRayCrossingIndex q
                gridPath).natAbs = (1 : ℕ)) ∧
          ((q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩, q + ⟨(0 : ℤ), (1 : ℤ)⟩) ∉ cyclicEdges ∧
                (q + ⟨(0 : ℤ), (1 : ℤ)⟩, q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∉
                  cyclicEdges →
              GridRayCrossingIndex (q + ⟨(0 : ℤ), (1 : ℤ)⟩) gridPath = GridRayCrossingIndex q
                  gridPath) ∧
            ((q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩, q + ⟨(0 : ℤ), (1 : ℤ)⟩) ∈
                  cyclicEdges ∨
                (q + ⟨(0 : ℤ), (1 : ℤ)⟩, q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∈
                  cyclicEdges →
              (GridRayCrossingIndex (q + ⟨(0 : ℤ), (1 : ℤ)⟩) gridPath -
                    GridRayCrossingIndex q gridPath).natAbs =
                (1 : ℕ))) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), (({a, b} : Finset
                    GaussianInt) ∈ BoundaryFootprintEdges T) → (∀ t : Set.Icc (0 : Real) 1, ((1 -
                    (t : Real)) * ((a.re : Int) : Real) + (t : Real) * ((b.re : Int) : Real), (1
                    - (t : Real)) * ((a.im : Int) : Real) + (t : Real) * ((b.im : Int) : Real)) ∈
                    TileRealization T)) → ((∀ a b : GaussianInt, (a, b) ∈ cyclicEdges → ∀ t :
                    Set.Icc (0 : Real) 1, ((1 - (t : Real)) * ((a.re : Int) : Real) + (t : Real)
                    * ((b.re : Int) : Real), (1 - (t : Real)) * ((a.im : Int) : Real) + (t :
                    Real) * ((b.im : Int) : Real)) ∈ TileRealization T) → ((∀ (q : LatticeCell),
                    (q ∉ T.cells) → (((((q.re : Int) : Real) + (1 / 2 : Real)), (((q.im : Int) :
                    Real) + (1 / 2 : Real))) ∉ TileRealization T)) → (∀ q ∉ T.cells,
                    GridRayCrossingIndex q gridPath = (0 : ℤ))))))))))))))))
    ) := by
  classical
  intro T closed_grid_index_zero gridPath x y z gridPath_head gridPath_last gridPath_chain
      gridPath_close gridPath_fourNeighbor gridPath_close_fourNeighbor cyclic_edge_boundary
      cyclic_edge_fourNeighbor component_edge_cyclic hrightCyclic cyclicEdges
      component_index_control boundary_edge_segment cyclic_edge_segment unoccupied_center_outside
      q hq
  apply closed_grid_index_zero q gridPath x y
    (unoccupied_center_outside q hq) gridPath_head gridPath_last
  · intro a b l₁ l₂ hab
    rw [hab] at gridPath_fourNeighbor
    exact (List.isChain_append_cons_cons.mp gridPath_fourNeighbor).2.1
  · exact gridPath_close_fourNeighbor
  · intro a b hab
    apply boundary_edge_segment a b
    rcases hab with ⟨l₁, l₂, hab⟩ | ⟨rfl, rfl⟩
    · rw [hab] at gridPath_chain
      exact (List.isChain_append_cons_cons.mp gridPath_chain).2.1
    · exact gridPath_close

private theorem occupied_vertical_not_boundary :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (List GaussianInt) → ((GaussianInt) → (∀ q ∈ T.cells, q - (1 :
            LatticeCell) ∈ T.cells → {q, q + ⟨(0 : ℤ), (1 : ℤ)⟩} ∉ BoundaryFootprintEdges T))
    ) := by
  classical
  intro T gridPath z q hq hleft
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
    · simp [hq, hleft] at hxor
    · subst w
      have hw2 : q + ⟨0, 1⟩ + ⟨0, 1⟩ = q ∨
          q + ⟨0, 1⟩ + ⟨0, 1⟩ = q + ⟨0, 1⟩ := by
        have : q + ⟨0, 1⟩ + ⟨0, 1⟩ ∈
            ({q, q + ⟨0, 1⟩} : Finset GaussianInt) := by rw [heq]; simp
        simpa using this
      rcases hw2 with hw2 | hw2 <;>
        have hbad := congrArg Zsqrtd.im hw2 <;> simp at hbad; omega

private theorem occupied_horizontal_not_boundary :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (List GaussianInt) → ((GaussianInt) → (∀ q ∈ T.cells, q - ⟨(0 : ℤ), (1
            : ℤ)⟩ ∈ T.cells → {q, q + (1 : LatticeCell)} ∉ BoundaryFootprintEdges T))
    ) := by
  classical
  intro T gridPath z q hq hbelow
  rintro ⟨w, (⟨heq, hxor⟩ | ⟨heq, hxor⟩)⟩
  · have hw : w = q ∨ w = q + 1 := by
      have : w ∈ ({q, q + 1} : Finset GaussianInt) := by rw [heq]; simp
      simpa using this
    rcases hw with rfl | hw
    · simp [hq, hbelow] at hxor
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

private theorem occupied_adjacent_index_eq :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (gridPath : List GaussianInt), ∀ (x : GaussianInt), ∀ (y :
            GaussianInt), (∀ (a : GaussianInt), ∀ (b : GaussianInt), (a, b) ∈ gridPath.zip
            gridPath.tail ++ [(y, x)] → {a, b} ∈ BoundaryFootprintEdges T) → (
        (
        let cyclicEdges := gridPath.zip gridPath.tail ++ [(y, x)];
    ∀ (q : LatticeCell), ((q + (1 : LatticeCell), q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∉
        cyclicEdges ∧
            (q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩, q + (1 : LatticeCell)) ∉ cyclicEdges →
          GridRayCrossingIndex (q + (1 : LatticeCell)) gridPath = GridRayCrossingIndex q gridPath) ∧
        ((q + (1 : LatticeCell), q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∈ cyclicEdges ∨
              (q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩, q + (1 : LatticeCell)) ∈ cyclicEdges →
            (GridRayCrossingIndex (q + (1 : LatticeCell)) gridPath - GridRayCrossingIndex q
                gridPath).natAbs = (1 : ℕ)) ∧
          ((q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩, q + ⟨(0 : ℤ), (1 : ℤ)⟩) ∉ cyclicEdges ∧
                (q + ⟨(0 : ℤ), (1 : ℤ)⟩, q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∉
                  cyclicEdges →
              GridRayCrossingIndex (q + ⟨(0 : ℤ), (1 : ℤ)⟩) gridPath = GridRayCrossingIndex q
                  gridPath) ∧
            ((q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩, q + ⟨(0 : ℤ), (1 : ℤ)⟩) ∈
                  cyclicEdges ∨
                (q + ⟨(0 : ℤ), (1 : ℤ)⟩, q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∈
                  cyclicEdges →
              (GridRayCrossingIndex (q + ⟨(0 : ℤ), (1 : ℤ)⟩) gridPath -
                    GridRayCrossingIndex q gridPath).natAbs =
                (1 : ℕ))) → ((∀ (q : LatticeCell), (q ∈ T.cells) → ((q - 1 ∈ T.cells) → (({q,
                    q + ⟨0, 1⟩} : Finset GaussianInt) ∉ BoundaryFootprintEdges T))) → ((∀ (q :
                    LatticeCell), (q ∈ T.cells) → ((q - ⟨0, 1⟩ ∈ T.cells) → (({q, q + 1} : Finset
                    GaussianInt) ∉ BoundaryFootprintEdges T))) → (∀ (a : LatticeCell), ∀ (b :
                    LatticeCell), a ∈ T.cells → b ∈ T.cells → FourNeighborAdjacent a b →
                    GridRayCrossingIndex a gridPath = GridRayCrossingIndex b gridPath))))
    ) := by
  classical
  intro T gridPath x y cyclic_edge_boundary component_index_control
      occupied_vertical_not_boundary occupied_horizontal_not_boundary a b ha hb hab
  rcases hab with rfl | rfl | rfl | rfl
  · symm
    apply (component_index_control a).1
    constructor <;> intro hc
    · have hE := cyclic_edge_boundary _ _ hc
      exact occupied_vertical_not_boundary (a + 1) hb
        (by simpa [Zsqrtd.ext_iff] using ha)
        (by simpa [Zsqrtd.ext_iff] using hE)
    · have hE := cyclic_edge_boundary _ _ hc
      exact occupied_vertical_not_boundary (a + 1) hb
        (by simpa [Zsqrtd.ext_iff] using ha)
        (by simpa [Finset.pair_comm, Zsqrtd.ext_iff] using hE)
  · have h := (component_index_control (a - 1)).1
    have hleft : a - 1 ∈ T.cells := hb
    have hright : a - 1 + 1 ∈ T.cells := by
      simpa [Zsqrtd.ext_iff] using ha
    have heq := h ⟨
      (fun hc => occupied_vertical_not_boundary (a - 1 + 1) hright
        (by simpa [Zsqrtd.ext_iff] using hleft)
        (by have hE := cyclic_edge_boundary _ _ hc
            simpa [Zsqrtd.ext_iff] using hE)),
      (fun hc => occupied_vertical_not_boundary (a - 1 + 1) hright
        (by simpa [Zsqrtd.ext_iff] using hleft)
        (by have hE := cyclic_edge_boundary _ _ hc
            simpa [Finset.pair_comm, Zsqrtd.ext_iff] using hE))⟩
    simpa [Zsqrtd.ext_iff] using heq
  · symm
    apply (component_index_control a).2.2.1
    constructor <;> intro hc
    · have hE := cyclic_edge_boundary _ _ hc
      exact occupied_horizontal_not_boundary (a + ⟨0, 1⟩) hb
        (by simpa [Zsqrtd.ext_iff] using ha)
        (by simpa [Finset.pair_comm, Zsqrtd.ext_iff, add_assoc, add_comm,
          add_left_comm] using hE)
    · have hE := cyclic_edge_boundary _ _ hc
      exact occupied_horizontal_not_boundary (a + ⟨0, 1⟩) hb
        (by simpa [Zsqrtd.ext_iff] using ha)
        (by simpa [Zsqrtd.ext_iff, add_assoc, add_comm, add_left_comm] using hE)
  · have h := (component_index_control (a - ⟨0, 1⟩)).2.2.1
    have hbelow : a - ⟨0, 1⟩ ∈ T.cells := hb
    have htop : a - ⟨0, 1⟩ + ⟨0, 1⟩ ∈ T.cells := by
      simpa [Zsqrtd.ext_iff] using ha
    have heq := h ⟨
      (fun hc => occupied_horizontal_not_boundary
        (a - ⟨0, 1⟩ + ⟨0, 1⟩) htop
        (by simpa [Zsqrtd.ext_iff] using hbelow)
        (by have hE := cyclic_edge_boundary _ _ hc
            simpa [Finset.pair_comm, Zsqrtd.ext_iff, add_assoc, add_comm,
              add_left_comm] using hE)),
      (fun hc => occupied_horizontal_not_boundary
        (a - ⟨0, 1⟩ + ⟨0, 1⟩) htop
        (by simpa [Zsqrtd.ext_iff] using hbelow)
        (by have hE := cyclic_edge_boundary _ _ hc
            simpa [Zsqrtd.ext_iff, add_assoc, add_comm, add_left_comm] using hE))⟩
    simpa [Zsqrtd.ext_iff] using heq

private theorem occupied_index_eq_z :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (LatticeTile T) → (∀ (gridPath : List GaussianInt), ∀ (z :
            GaussianInt), (z ∈ T.cells) → ((∀ (a : LatticeCell), ∀ (b : LatticeCell), (a ∈
            T.cells) → ((b ∈ T.cells) → ((FourNeighborAdjacent a b) → (GridRayCrossingIndex a
            gridPath = GridRayCrossingIndex b gridPath)))) → (∀ q ∈ T.cells, GridRayCrossingIndex
            q gridPath = GridRayCrossingIndex z gridPath)))
    ) := by
  classical
  intro T hT gridPath z hz occupied_adjacent_index_eq q hq
  obtain ⟨r, hrHead, hrLast, hrMem, hrAdj⟩ :=
    (LatticeTileFourNeighborConnected T hT).2 q hq z hz
  have hrChain : List.IsChain FourNeighborAdjacent r := by
    rw [List.isChain_iff_forall_rel_of_append_cons_cons]
    exact hrAdj
  have hrIndexChain : List.IsChain
      (fun a b : LatticeCell =>
        GridRayCrossingIndex a gridPath = GridRayCrossingIndex b gridPath) r := by
    exact hrChain.imp_of_mem_imp (fun a b ha hb hab =>
      occupied_adjacent_index_eq a b (hrMem a ha) (hrMem b hb) hab)
  cases r with
  | nil => simp at hrHead
  | cons a r =>
      have haq : a = q := by simpa using Option.some.inj hrHead
      subst a
      have hzmem : z ∈ q :: r := by
        rcases List.getLast?_eq_some_iff.mp hrLast with ⟨l, hl⟩
        rw [hl]
        simp
      simp only [List.mem_cons] at hzmem
      rcases hzmem with hzq | hzmem
      · exact congrArg (fun w => GridRayCrossingIndex w gridPath) hzq.symm
      · exact hrIndexChain.rel_cons hzmem

private theorem boundary_edge_cyclic :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (gridPath : List GaussianInt), ∀ (x : GaussianInt), ∀ (y :
            GaussianInt),
        let cyclicEdges := (gridPath.zip gridPath.tail) ++ [(y, x)]
        (
        let cyclicEdges := gridPath.zip gridPath.tail ++ [(y, x)];
    ∀ (q : LatticeCell), ((q + (1 : LatticeCell), q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∉
        cyclicEdges ∧
            (q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩, q + (1 : LatticeCell)) ∉ cyclicEdges →
          GridRayCrossingIndex (q + (1 : LatticeCell)) gridPath = GridRayCrossingIndex q gridPath) ∧
        ((q + (1 : LatticeCell), q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∈ cyclicEdges ∨
              (q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩, q + (1 : LatticeCell)) ∈ cyclicEdges →
            (GridRayCrossingIndex (q + (1 : LatticeCell)) gridPath - GridRayCrossingIndex q
                gridPath).natAbs = (1 : ℕ)) ∧
          ((q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩, q + ⟨(0 : ℤ), (1 : ℤ)⟩) ∉ cyclicEdges ∧
                (q + ⟨(0 : ℤ), (1 : ℤ)⟩, q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∉
                  cyclicEdges →
              GridRayCrossingIndex (q + ⟨(0 : ℤ), (1 : ℤ)⟩) gridPath = GridRayCrossingIndex q
                  gridPath) ∧
            ((q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩, q + ⟨(0 : ℤ), (1 : ℤ)⟩) ∈
                  cyclicEdges ∨
                (q + ⟨(0 : ℤ), (1 : ℤ)⟩, q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∈
                  cyclicEdges →
              (GridRayCrossingIndex (q + ⟨(0 : ℤ), (1 : ℤ)⟩) gridPath -
                    GridRayCrossingIndex q gridPath).natAbs =
                (1 : ℕ))) → ((∀ (q : LatticeCell), (q ∉ T.cells) → (GridRayCrossingIndex q
                    gridPath = 0)) → ((∀ (q : LatticeCell), (q ∈ T.cells) → (GridRayCrossingIndex
                    q gridPath ≠ 0)) → (∀ e ∈ BoundaryFootprintEdges T, ∃ (a : GaussianInt) (b :
                    GaussianInt), e = {a, b} ∧ ((a, b) ∈ cyclicEdges ∨ (b, a) ∈ cyclicEdges))))
    ) := by
  classical
  intro T gridPath x y cyclicEdges component_index_control unoccupied_index_zero
      occupied_index_nonzero e he
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

private theorem zip_mem_decompose :
    (by
      classical
      exact
        ∀ (gridPath : List GaussianInt), (GaussianInt) → (((4 : ℕ) ≤ gridPath.length) → (∀ (a :
            GaussianInt), ∀ (b : GaussianInt), (a, b) ∈ gridPath.zip gridPath.tail → ∃ (l₁ : List
            GaussianInt) (l₂ : List GaussianInt), gridPath = l₁ ++ a :: b :: l₂))
    ) := by
  classical
  intro gridPath z gridPath_length_four a b hab
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

private theorem cyclic_endpoints_mem :
    (by
      classical
      exact
        ∀ (gridPath : List GaussianInt), ∀ (x : GaussianInt), ∀ (y : GaussianInt),
            (gridPath.head? = some x) → ((gridPath.getLast? = some y) → (
        let cyclicEdges := (gridPath.zip gridPath.tail) ++ [(y, x)]
        (∀ (a : GaussianInt), ∀ (b : GaussianInt), ((a, b) ∈ gridPath.zip gridPath.tail) → (∃ l₁
            l₂ : List GaussianInt, gridPath = l₁ ++ a :: b :: l₂)) → (∀ (a : GaussianInt), ∀ (b :
            GaussianInt), (a, b) ∈ cyclicEdges → a ∈ gridPath ∧ b ∈ gridPath)))
    ) := by
  classical
  intro gridPath x y gridPath_head gridPath_last cyclicEdges zip_mem_decompose a b hab
  simp only [cyclicEdges, List.mem_append, List.mem_singleton] at hab
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

private theorem boundary_vertices_eq :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (T.cells.Nonempty) → (∀ (gridPath : List GaussianInt), ∀ (x :
            GaussianInt), ∀ (y : GaussianInt), (∀ a ∈ gridPath, a ∈ BoundaryFootprintVertices T) → (
        let cyclicEdges := (gridPath.zip gridPath.tail) ++ [(y, x)]
        (∀ (e : Finset GaussianInt), (e ∈ BoundaryFootprintEdges T) → (∃ a b : GaussianInt, e =
            {a, b} ∧ ((a, b) ∈ cyclicEdges ∨ (b, a) ∈ cyclicEdges))) → ((∀ (a : GaussianInt), ∀
            (b : GaussianInt), ((a, b) ∈ cyclicEdges) → (a ∈ gridPath ∧ b ∈ gridPath)) →
            (BoundaryFootprintVertices T = (gridPath.toFinset : Set GaussianInt)))))
    ) := by
  classical
  intro T cells_nonempty gridPath x y gridPath_mem_boundary cyclicEdges boundary_edge_cyclic
      cyclic_endpoints_mem
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

private theorem boundary_edges_iff :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (gridPath : List GaussianInt), ∀ (x : GaussianInt), ∀ (y :
            GaussianInt), (List.IsChain (fun (a b : GaussianInt) => {a, b} ∈
            BoundaryFootprintEdges T) gridPath) → (({y, x} ∈ BoundaryFootprintEdges T) → (
        let cyclicEdges := (gridPath.zip gridPath.tail) ++ [(y, x)]
        (∀ (e : Finset GaussianInt), (e ∈ BoundaryFootprintEdges T) → (∃ a b : GaussianInt, e =
            {a, b} ∧ ((a, b) ∈ cyclicEdges ∨ (b, a) ∈ cyclicEdges))) → ((∀ (a : GaussianInt), ∀
            (b : GaussianInt), ((a, b) ∈ gridPath.zip gridPath.tail) → (∃ l₁ l₂ : List
            GaussianInt, gridPath = l₁ ++ a :: b :: l₂)) → (∀ (e : Finset GaussianInt), e ∈
            BoundaryFootprintEdges T ↔ e = {y, x} ∨ ∃ (a : GaussianInt) (b : GaussianInt) (l₁ :
            List GaussianInt) (l₂ : List GaussianInt), gridPath = l₁ ++ a :: b :: l₂ ∧ e = {a,
            b}))))
    ) := by
  classical
  intro T gridPath x y gridPath_chain gridPath_close cyclicEdges boundary_edge_cyclic
      zip_mem_decompose e
  constructor
  · intro he
    rcases boundary_edge_cyclic e he with ⟨a, b, heq, hab⟩
    rcases hab with hab | hab
    · simp only [cyclicEdges, List.mem_append, List.mem_singleton] at hab
      rcases hab with hab | hab
      · right
        rcases zip_mem_decompose a b hab with ⟨l₁, l₂, hp⟩
        exact ⟨a, b, l₁, l₂, hp, heq⟩
      · left
        have hab' : a = y ∧ b = x := Prod.mk.inj hab
        simpa [hab'.1, hab'.2] using heq
    · simp only [cyclicEdges, List.mem_append, List.mem_singleton] at hab
      rcases hab with hab | hab
      · right
        rcases zip_mem_decompose b a hab with ⟨l₁, l₂, hp⟩
        refine ⟨b, a, l₁, l₂, hp, ?_⟩
        simpa [Finset.pair_comm] using heq
      · left
        have hab' : b = y ∧ a = x := Prod.mk.inj hab
        simpa [hab'.1, hab'.2, Finset.pair_comm] using heq
  · rintro (rfl | ⟨a, b, l₁, l₂, hp, rfl⟩)
    · exact gridPath_close
    · rw [hp] at gridPath_chain
      exact (List.isChain_append_cons_cons.mp gridPath_chain).2.1

end BoundaryCycleProof

theorem LatticeTileBoundarySimpleGridCycle (T : ProtoTile) (hT : LatticeTile T) :
    SimpleGridCycle (BoundaryFootprintVertices T)
      (BoundaryFootprintEdges T) := by
-- BODY
  classical
  have closed_grid_index_zero :
      ∀ (q : LatticeCell) (p : List GaussianInt) (x y : GaussianInt),
        ((((q.re : Int) : Real) + (1 / 2 : Real)),
            (((q.im : Int) : Real) + (1 / 2 : Real))) ∉ TileRealization T →
        p.head? = some x → p.getLast? = some y →
        (∀ a b : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
          p = l₁ ++ a :: b :: l₂ → FourNeighborAdjacent a b) →
        FourNeighborAdjacent y x →
        (∀ a b : GaussianInt,
          ((∃ l₁ l₂ : List GaussianInt, p = l₁ ++ a :: b :: l₂) ∨
            (a = y ∧ b = x)) →
          ∀ t : Set.Icc (0 : Real) 1,
            ((1 - (t : Real)) * ((a.re : Int) : Real) +
                (t : Real) * ((b.re : Int) : Real),
              (1 - (t : Real)) * ((a.im : Int) : Real) +
                (t : Real) * ((b.im : Int) : Real)) ∈ TileRealization T) →
        GridRayCrossingIndex q p = 0 := BoundaryCycleProof.closed_grid_index_zero T hT
  have cells_nonempty : T.cells.Nonempty := by
    have realization_nonempty : (TileRealization T).Nonempty := by
      rcases hT with ⟨e⟩
      let x : Metric.closedBall (0 : Real × Real) 1 := ⟨0, by simp⟩
      exact ⟨e x, (e x).property⟩
    rcases realization_nonempty with ⟨p, hp⟩
    simp only [TileRealization, Set.mem_iUnion] at hp
    rcases hp with ⟨x, hx, _⟩
    exact ⟨x, hx⟩
  have boundary_degree_two :
      ∀ v ∈ BoundaryFootprintVertices T,
        Set.ncard {e : Finset GaussianInt |
          e ∈ BoundaryFootprintEdges T ∧ v ∈ e} = 2 := by
    intro v hv
    exact BoundaryFootprintVertexDegreeTwo T cells_nonempty
      (LatticeTileNoCheckerboard T hT) v hv
  have adjacent_grid_index_control :
      ∀ (p : List GaussianInt) (x y : GaussianInt),
        p.head? = some x → p.getLast? = some y → p.Nodup → 3 ≤ p.length →
        (∀ a b, (a, b) ∈ p.zip p.tail → FourNeighborAdjacent a b) →
        FourNeighborAdjacent y x →
        let cyclicEdges := (p.zip p.tail) ++ [(y, x)]
        ∀ q : LatticeCell,
          (((q + 1, q + 1 + ⟨0, 1⟩) ∉ cyclicEdges ∧
              (q + 1 + ⟨0, 1⟩, q + 1) ∉ cyclicEdges) →
              GridRayCrossingIndex (q + 1) p = GridRayCrossingIndex q p) ∧
          (((q + 1, q + 1 + ⟨0, 1⟩) ∈ cyclicEdges ∨
              (q + 1 + ⟨0, 1⟩, q + 1) ∈ cyclicEdges) →
              Int.natAbs (GridRayCrossingIndex (q + 1) p -
                GridRayCrossingIndex q p) = 1) ∧
          (((q + 1 + ⟨0, 1⟩, q + ⟨0, 1⟩) ∉ cyclicEdges ∧
              (q + ⟨0, 1⟩, q + 1 + ⟨0, 1⟩) ∉ cyclicEdges) →
              GridRayCrossingIndex (q + ⟨0, 1⟩) p =
                GridRayCrossingIndex q p) ∧
          (((q + 1 + ⟨0, 1⟩, q + ⟨0, 1⟩) ∈ cyclicEdges ∨
              (q + ⟨0, 1⟩, q + 1 + ⟨0, 1⟩) ∈ cyclicEdges) →
              Int.natAbs (GridRayCrossingIndex (q + ⟨0, 1⟩) p -
                GridRayCrossingIndex q p) = 1) := BoundaryCycleProof.adjacent_grid_index_control
  obtain ⟨gridPath, x, y, z, gridPath_nodup, gridPath_length_four,
      gridPath_head, gridPath_last, gridPath_chain, gridPath_close,
      gridPath_fourNeighbor, gridPath_close_fourNeighbor, gridPath_zip_fourNeighbor,
      gridPath_mem_boundary, hz, hmax, hzout, cyclic_edge_boundary,
      cyclic_edge_fourNeighbor, component_edge_cyclic, hrightCyclic⟩ :=
    P5620T1BoundaryComponentCycle T cells_nonempty boundary_degree_two
  have gridPath_length : 3 ≤ gridPath.length := by omega
  have component_index_control := adjacent_grid_index_control gridPath x y
    gridPath_head gridPath_last gridPath_nodup gridPath_length
    gridPath_zip_fourNeighbor gridPath_close_fourNeighbor
  let cyclicEdges := (gridPath.zip gridPath.tail) ++ [(y, x)]
  have boundary_edge_card_two (e : Finset GaussianInt)
      (he : e ∈ BoundaryFootprintEdges T) : e.card = 2 := by
    rcases he with ⟨z, (⟨rfl, hz⟩ | ⟨rfl, hz⟩)⟩
    · simp []
    · simp [Zsqrtd.ext_iff]
  have boundary_edge_segment (a b : GaussianInt)
      (hab : ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T) :
      ∀ t : Set.Icc (0 : Real) 1,
        ((1 - (t : Real)) * ((a.re : Int) : Real) +
            (t : Real) * ((b.re : Int) : Real),
          (1 - (t : Real)) * ((a.im : Int) : Real) +
            (t : Real) * ((b.im : Int) : Real)) ∈ TileRealization T :=
                BoundaryCycleProof.boundary_edge_segment T boundary_edge_card_two a b hab
  have cyclic_edge_segment :
      ∀ a b : GaussianInt, (a, b) ∈ cyclicEdges →
        ∀ t : Set.Icc (0 : Real) 1,
          ((1 - (t : Real)) * ((a.re : Int) : Real) +
              (t : Real) * ((b.re : Int) : Real),
            (1 - (t : Real)) * ((a.im : Int) : Real) +
              (t : Real) * ((b.im : Int) : Real)) ∈ TileRealization T := by
    intro a b hab
    exact boundary_edge_segment a b (cyclic_edge_boundary a b hab)
  have unoccupied_center_outside (q : LatticeCell) (hq : q ∉ T.cells) :
      ((((q.re : Int) : Real) + (1 / 2 : Real)),
          (((q.im : Int) : Real) + (1 / 2 : Real))) ∉ TileRealization T :=
              BoundaryCycleProof.unoccupied_center_outside T gridPath q hq
  have unoccupied_index_zero (q : LatticeCell) (hq : q ∉ T.cells) :
      GridRayCrossingIndex q gridPath = 0 := BoundaryCycleProof.unoccupied_index_zero T
          closed_grid_index_zero gridPath x y z gridPath_head gridPath_last gridPath_chain
          gridPath_close gridPath_fourNeighbor gridPath_close_fourNeighbor cyclic_edge_boundary
          cyclic_edge_fourNeighbor component_edge_cyclic hrightCyclic component_index_control
          boundary_edge_segment cyclic_edge_segment unoccupied_center_outside q hq
  have hrightJump :
      Int.natAbs (GridRayCrossingIndex (z + 1) gridPath -
        GridRayCrossingIndex z gridPath) = 1 := by
    exact (component_index_control z).2.1 hrightCyclic
  have hzIndexNonzero : GridRayCrossingIndex z gridPath ≠ 0 := by
    intro hz0
    rw [unoccupied_index_zero (z + 1) hzout, hz0] at hrightJump
    simp at hrightJump
  have occupied_vertical_not_boundary (q : LatticeCell)
      (hq : q ∈ T.cells) (hleft : q - 1 ∈ T.cells) :
      ({q, q + ⟨0, 1⟩} : Finset GaussianInt) ∉ BoundaryFootprintEdges T :=
          BoundaryCycleProof.occupied_vertical_not_boundary T gridPath z q hq hleft
  have occupied_horizontal_not_boundary (q : LatticeCell)
      (hq : q ∈ T.cells) (hbelow : q - ⟨0, 1⟩ ∈ T.cells) :
      ({q, q + 1} : Finset GaussianInt) ∉ BoundaryFootprintEdges T :=
          BoundaryCycleProof.occupied_horizontal_not_boundary T gridPath z q hq hbelow
  have occupied_adjacent_index_eq (a b : LatticeCell)
      (ha : a ∈ T.cells) (hb : b ∈ T.cells)
      (hab : FourNeighborAdjacent a b) :
      GridRayCrossingIndex a gridPath = GridRayCrossingIndex b gridPath :=
          BoundaryCycleProof.occupied_adjacent_index_eq T gridPath x y cyclic_edge_boundary
          component_index_control occupied_vertical_not_boundary occupied_horizontal_not_boundary
          a b ha hb hab
  have occupied_index_eq_z (q : LatticeCell) (hq : q ∈ T.cells) :
      GridRayCrossingIndex q gridPath = GridRayCrossingIndex z gridPath :=
          BoundaryCycleProof.occupied_index_eq_z T hT gridPath z hz occupied_adjacent_index_eq q hq
  have occupied_index_nonzero (q : LatticeCell) (hq : q ∈ T.cells) :
      GridRayCrossingIndex q gridPath ≠ 0 := by
    rw [occupied_index_eq_z q hq]
    exact hzIndexNonzero
  have boundary_edge_cyclic (e : Finset GaussianInt)
      (he : e ∈ BoundaryFootprintEdges T) :
      ∃ a b : GaussianInt, e = {a, b} ∧
        ((a, b) ∈ cyclicEdges ∨ (b, a) ∈ cyclicEdges) := BoundaryCycleProof.boundary_edge_cyclic
            T gridPath x y component_index_control unoccupied_index_zero occupied_index_nonzero e he
  have zip_mem_decompose (a b : GaussianInt)
      (hab : (a, b) ∈ gridPath.zip gridPath.tail) :
      ∃ l₁ l₂ : List GaussianInt, gridPath = l₁ ++ a :: b :: l₂ :=
          BoundaryCycleProof.zip_mem_decompose gridPath z gridPath_length_four a b hab
  have cyclic_endpoints_mem (a b : GaussianInt) (hab : (a, b) ∈ cyclicEdges) :
      a ∈ gridPath ∧ b ∈ gridPath := BoundaryCycleProof.cyclic_endpoints_mem gridPath x y
          gridPath_head gridPath_last zip_mem_decompose a b hab
  have boundary_vertices_eq :
      BoundaryFootprintVertices T = (gridPath.toFinset : Set GaussianInt) :=
          BoundaryCycleProof.boundary_vertices_eq T cells_nonempty gridPath x y
          gridPath_mem_boundary boundary_edge_cyclic cyclic_endpoints_mem
  have boundary_edges_iff (e : Finset GaussianInt) :
      e ∈ BoundaryFootprintEdges T ↔
        e = {y, x} ∨
          ∃ a b : GaussianInt, ∃ l₁ l₂ : List GaussianInt,
            gridPath = l₁ ++ a :: b :: l₂ ∧ e = {a, b} := BoundaryCycleProof.boundary_edges_iff T
                gridPath x y gridPath_chain gridPath_close boundary_edge_cyclic zip_mem_decompose e
  refine ⟨gridPath, x, y, gridPath_nodup, gridPath_length_four,
    gridPath_head, gridPath_last, boundary_vertices_eq, gridPath_close_fourNeighbor, ?_, ?_⟩
  · intro a b l₁ l₂ hab
    rw [hab] at gridPath_fourNeighbor
    exact (List.isChain_append_cons_cons.mp gridPath_fourNeighbor).2.1
  · exact boundary_edges_iff

end ApollonianSuperharmonic

end
