/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FourNeighborConnected
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.LatticeTileNoCheckerboard

-- [TABLET NODE: LatticeTileFourNeighborConnected]

/-!
# LatticeTileFourNeighborConnected

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FourNeighborProof

private theorem diskConnected :
    IsConnected (Metric.closedBall (0 : Real × Real) 1) := by
  classical
  have box : Metric.closedBall (0 : Real × Real) 1 =
      Set.Icc (-1 : Real) 1 ×ˢ Set.Icc (-1 : Real) 1 := by
    ext p
    simp only [Metric.mem_closedBall, Prod.dist_eq, Set.mem_prod, Set.mem_Icc]
    constructor
    · intro h
      have parts := max_le_iff.mp h
      norm_num at parts
      constructor
      · constructor
        · simp only [Real.dist_eq] at parts
          have q := abs_le.mp parts.1
          linarith
        · simp only [Real.dist_eq] at parts
          have q := abs_le.mp parts.1
          linarith
      · constructor
        · simp only [Real.dist_eq] at parts
          have q := abs_le.mp parts.2
          linarith
        · simp only [Real.dist_eq] at parts
          have q := abs_le.mp parts.2
          linarith
    · intro h
      apply max_le
      · rw [Real.dist_eq]
        norm_num
        exact abs_le.mpr ⟨by linarith [h.1.1], by linarith [h.1.2]⟩
      · rw [Real.dist_eq]
        norm_num
        exact abs_le.mpr ⟨by linarith [h.2.1], by linarith [h.2.2]⟩
  rw [box]
  exact (isConnected_Icc (by norm_num)).prod (isConnected_Icc (by norm_num))

private theorem realizationConnected :
    ∀ (T : ProtoTile), ∀ [ConnectedSpace (↑(TileRealization T) : Type)], IsConnected
        (TileRealization T) := by
  classical
  intro T this
  have imageConnected :=
    isConnected_univ.image (fun z : (TileRealization T) => (z : Real × Real))
      continuous_subtype_val.continuousOn
  have imageIsRange : IsConnected
      (Set.range (fun z : (TileRealization T) => (z : Real × Real))) := by
    convert imageConnected using 1; ext p; simp
  have rangeEq : Set.range (fun z : (TileRealization T) => (z : Real × Real)) =
      TileRealization T := by
    ext p
    constructor
    · rintro ⟨z, rfl⟩
      exact z.property
    · intro hp
      exact ⟨⟨p, hp⟩, rfl⟩
  rw [← rangeEq]
  exact imageIsRange

private theorem overlap :
    ∀ (a : LatticeCell), ∀ (b : LatticeCell), ∀ (p : Real × Real), p ∈ ClosedSquareRealization a
        → p ∈ ClosedSquareRealization b → a = b ∨ FourNeighborAdjacent a b ∨ (b = a + 1 + ⟨0, 1⟩
        ∨ b = a + 1 - ⟨0, 1⟩ ∨ b = a - 1 + ⟨0, 1⟩ ∨ b = a - 1 - ⟨0, 1⟩) := by
  classical
  intro a b p hp hq
  simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hp hq
  have hrlo : (-1 : ℝ) ≤ (a.re : ℝ) - b.re := by
    linarith [hp.1.1, hq.1.2]
  have hrhi : (a.re : ℝ) - b.re ≤ 1 := by
    linarith [hp.1.2, hq.1.1]
  have hilo : (-1 : ℝ) ≤ (a.im : ℝ) - b.im := by
    linarith [hp.2.1, hq.2.2]
  have hihi : (a.im : ℝ) - b.im ≤ 1 := by
    linarith [hp.2.2, hq.2.1]
  have rlo : (-1 : ℤ) ≤ a.re - b.re := by exact_mod_cast hrlo
  have rhi : a.re - b.re ≤ (1 : ℤ) := by exact_mod_cast hrhi
  have ilo : (-1 : ℤ) ≤ a.im - b.im := by exact_mod_cast hilo
  have ihi : a.im - b.im ≤ (1 : ℤ) := by exact_mod_cast hihi
  have rd : a.re - b.re = -1 ∨ a.re - b.re = 0 ∨ a.re - b.re = 1 := by omega
  have id : a.im - b.im = -1 ∨ a.im - b.im = 0 ∨ a.im - b.im = 1 := by omega
  rcases rd with hr | hr | hr <;> rcases id with hi | hi | hi
  all_goals
    simp_all [FourNeighborAdjacent, Zsqrtd.ext_iff]
    omega

private theorem reachXY :
    ∀ (T : ProtoTile), (IsConnected (TileRealization T)) → ((∀ (a : LatticeCell), ∀ (b :
        LatticeCell), ∀ (p : Real × Real), p ∈ ClosedSquareRealization a → p ∈
        ClosedSquareRealization b → a = b ∨ FourNeighborAdjacent a b ∨ (b = a + 1 + ⟨0, 1⟩ ∨ b =
        a + 1 - ⟨0, 1⟩ ∨ b = a - 1 + ⟨0, 1⟩ ∨ b = a - 1 - ⟨0, 1⟩)) → (∀ (x : LatticeCell), (x ∈
        (↑T.cells : Set LatticeCell)) → (∀ (y : LatticeCell), (y ∈ (↑T.cells : Set LatticeCell)) → (
    let step : LatticeCell → LatticeCell → Prop := fun a b =>
      FourNeighborAdjacent a b ∧ a ∈ (T.cells : Set LatticeCell) ∧
        b ∈ (T.cells : Set LatticeCell)
    let reachable : LatticeCell → LatticeCell → Prop :=
      Relation.ReflTransGen step
    (∀ z : LatticeCell, (ClosedSquareRealization z).Nonempty) → ((∀ (a : LatticeCell), ∀ (b :
        LatticeCell), a ∈ (T.cells : Set LatticeCell) → b ∈ (T.cells : Set LatticeCell) → ¬
        reachable a b → (b = a + 1 + ⟨0, 1⟩ ∨ b = a + 1 - ⟨0, 1⟩ ∨ b = a - 1 + ⟨0, 1⟩ ∨ b = a - 1
        - ⟨0, 1⟩) → False) → (reachable x y)))))) := by
  classical
  intro T realizationConnected overlap x hx y hy step reachable squareNonempty diagonalBridge
  by_contra notReach
  let component : Finset LatticeCell :=
    T.cells.filter (fun z => reachable x z)
  let remainder : Finset LatticeCell := T.cells \ component
  let firstUnion : Set (Real × Real) :=
    ⋃ z ∈ component, ClosedSquareRealization z
  let secondUnion : Set (Real × Real) :=
    ⋃ z ∈ remainder, ClosedSquareRealization z
  have hxComponent : x ∈ component := by
    exact Finset.mem_filter.2 ⟨hx, Relation.ReflTransGen.refl⟩
  have hyRemainder : y ∈ remainder := by
    refine Finset.mem_sdiff.2 ⟨hy, ?_⟩
    intro hyComponent
    exact notReach (Finset.mem_filter.1 hyComponent).2
  have firstClosed : IsClosed firstUnion := by
    dsimp [firstUnion]
    apply isClosed_biUnion_finset
    intro z hz
    exact isClosed_Icc
  have secondClosed : IsClosed secondUnion := by
    dsimp [secondUnion]
    apply isClosed_biUnion_finset
    intro z hz
    exact isClosed_Icc
  have unionCovers : TileRealization T ⊆ firstUnion ∪ secondUnion := by
    intro p hp
    rw [TileRealization] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨z, hz, hpz⟩ := hp
    by_cases hzC : z ∈ component
    · left
      exact Set.mem_iUnion.2 ⟨z, Set.mem_iUnion.2 ⟨hzC, hpz⟩⟩
    · right
      have hzR : z ∈ remainder := by
        exact Finset.mem_sdiff.2 ⟨hz, hzC⟩
      exact Set.mem_iUnion.2 ⟨z, Set.mem_iUnion.2 ⟨hzR, hpz⟩⟩
  have separated : firstUnion ∩ secondUnion = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro p hp
    change p ∈ (⋃ z ∈ component, ClosedSquareRealization z) ∩
      (⋃ z ∈ remainder, ClosedSquareRealization z) at hp
    have hfirstMem := hp.1
    have hsecondMem := hp.2
    rcases Set.mem_iUnion.1 hfirstMem with ⟨a, hfirstMem⟩
    rcases Set.mem_iUnion.1 hfirstMem with ⟨haC, hpa⟩
    rcases Set.mem_iUnion.1 hsecondMem with ⟨b, hsecondMem⟩
    rcases Set.mem_iUnion.1 hsecondMem with ⟨hbR, hpb⟩
    have haS : a ∈ (T.cells : Set LatticeCell) :=
      (Finset.mem_filter.1 haC).1
    have haReach : reachable x a := (Finset.mem_filter.1 haC).2
    have hbS : b ∈ (T.cells : Set LatticeCell) :=
      (Finset.mem_sdiff.1 hbR).1
    have hbNot : ¬ reachable x b := by
      intro hbReach
      exact (Finset.mem_sdiff.1 hbR).2 (Finset.mem_filter.2 ⟨hbS, hbReach⟩)
    rcases overlap a b p hpa hpb with hab | hab | hab
    · exact (Finset.mem_sdiff.1 hbR).2 (by simpa [hab] using haC)
    · exact hbNot (Relation.ReflTransGen.trans haReach
        (Relation.ReflTransGen.single ⟨hab, haS, hbS⟩))
    · exact diagonalBridge a b haS hbS (by
        intro habReach
        exact hbNot (Relation.ReflTransGen.trans haReach habReach)) hab
  have firstPoint : ∃ p, p ∈ TileRealization T ∧ p ∈ firstUnion := by
    rcases squareNonempty x with ⟨p, hp⟩
    refine ⟨p, ?_, ?_⟩
    · rw [TileRealization]
      exact Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨hx, hp⟩⟩
    · exact Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨hxComponent, hp⟩⟩
  have secondPoint : ∃ p, p ∈ TileRealization T ∧ p ∈ secondUnion := by
    rcases squareNonempty y with ⟨p, hp⟩
    refine ⟨p, ?_, ?_⟩
    · rw [TileRealization]
      exact Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨hy, hp⟩⟩
    · exact Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨hyRemainder, hp⟩⟩
  have separatedRelative : TileRealization T ∩ (firstUnion ∩ secondUnion) = ∅ := by
    rw [separated]
    simp
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp
    realizationConnected.isPreconnected firstUnion secondUnion firstClosed secondClosed
      unionCovers separatedRelative) with hfirst | hsecond
  · obtain ⟨p, hpT, hpA⟩ := secondPoint
    have hpAB : p ∈ firstUnion ∩ secondUnion := ⟨hfirst hpT, hpA⟩
    rw [separated] at hpAB
    exact hpAB
  · obtain ⟨p, hpT, hpB⟩ := firstPoint
    have hpAB : p ∈ firstUnion ∩ secondUnion := ⟨hpB, hsecond hpT⟩
    rw [separated] at hpAB
    exact hpAB

private theorem walk :
    ∀ (T : ProtoTile),
    let step : LatticeCell → LatticeCell → Prop := fun a b =>
      FourNeighborAdjacent a b ∧ a ∈ (T.cells : Set LatticeCell) ∧
        b ∈ (T.cells : Set LatticeCell)
    let reachable : LatticeCell → LatticeCell → Prop :=
      Relation.ReflTransGen step
    ∀ {a : LatticeCell}, ∀ {b : LatticeCell}, a ∈ (T.cells : Set LatticeCell) → b ∈ (T.cells :
        Set LatticeCell) → reachable a b → ∃ p : List LatticeCell, p.head? = some a ∧ p.getLast?
        = some b ∧ (∀ z ∈ p, z ∈ (T.cells : Set LatticeCell)) ∧ ∀ u v : LatticeCell, ∀ l₁ l₂ :
        List LatticeCell, p = l₁ ++ u :: v :: l₂ → FourNeighborAdjacent u v := by
  classical
  intro T step reachable a b ha hb hab
  induction hab using Relation.ReflTransGen.head_induction_on with
  | refl =>
      exact ⟨[b], by simp, by simp, by
        intro z hz
        rcases List.mem_singleton.mp hz with rfl
        exact hb,
          (List.isChain_iff_forall_rel_of_append_cons_cons).1
            (List.isChain_singleton b)⟩
  | @head a₀ c hstep hrest ih =>
      rcases hstep with ⟨huv, ha', hc⟩
      rcases ih hc with ⟨p, hphead, hplast, hpinside, hpedge⟩
      have pne : p ≠ [] := by
        intro hnil
        simp [hnil] at hphead
      have chainp : List.IsChain FourNeighborAdjacent p :=
        (List.isChain_iff_forall_rel_of_append_cons_cons).2 hpedge
      have chainnew : List.IsChain FourNeighborAdjacent ([a₀] ++ p) := by
        apply List.IsChain.append (by simp) chainp
        intro u hu' v hv'
        have huEq : u = a₀ := by simpa using hu'.symm
        have hvEq : v = c := by simpa [hphead] using hv'.symm
        simpa [huEq, hvEq] using huv
      refine ⟨[a₀] ++ p, ?_, ?_, ?_,
        (List.isChain_iff_forall_rel_of_append_cons_cons).1 chainnew⟩
      · simp
      · cases p with
        | nil => exact (pne rfl).elim
        | cons q r => simpa using hplast
      · intro z hz
        simp only [List.mem_append, List.mem_singleton] at hz
        rcases hz with rfl | hz
        · exact ha'
        · exact hpinside z hz

end FourNeighborProof

theorem LatticeTileFourNeighborConnected (T : ProtoTile) (hT : LatticeTile T) :
    FourNeighborConnected (T.cells : Set LatticeCell) := by
-- BODY
  classical
  have diskConnected : IsConnected (Metric.closedBall (0 : Real × Real) 1) :=
      FourNeighborProof.diskConnected
  rcases hT with ⟨home⟩
  have targetConnected : ConnectedSpace (TileRealization T) := by
    rw [← home.connectedSpace_iff]
    exact isConnected_iff_connectedSpace.mp diskConnected
  let := targetConnected
  have realizationConnected : IsConnected (TileRealization T) :=
      FourNeighborProof.realizationConnected T
  have noChecker := LatticeTileNoCheckerboard T ⟨home⟩
  have overlap : ∀ (a b : LatticeCell) (p : Real × Real),
      p ∈ ClosedSquareRealization a → p ∈ ClosedSquareRealization b →
      a = b ∨ FourNeighborAdjacent a b ∨
        (b = a + 1 + ⟨0, 1⟩ ∨ b = a + 1 - ⟨0, 1⟩ ∨
         b = a - 1 + ⟨0, 1⟩ ∨ b = a - 1 - ⟨0, 1⟩) := FourNeighborProof.overlap
  constructor
  · have cellsNonempty : T.cells.Nonempty := by
      by_contra empty
      have realizationEmpty : TileRealization T = ∅ := by
        rw [TileRealization]
        simp [Finset.not_nonempty_iff_eq_empty.mp empty]
      rw [realizationEmpty] at realizationConnected
      exact realizationConnected.nonempty.ne_empty rfl
    rcases cellsNonempty with ⟨x, hx⟩
    exact ⟨x, hx⟩
  · intro x hx y hy
    let step : LatticeCell → LatticeCell → Prop := fun a b =>
      FourNeighborAdjacent a b ∧ a ∈ (T.cells : Set LatticeCell) ∧
        b ∈ (T.cells : Set LatticeCell)
    let reachable : LatticeCell → LatticeCell → Prop :=
      Relation.ReflTransGen step
    have squareNonempty : ∀ z : LatticeCell,
        (ClosedSquareRealization z).Nonempty := by
      intro z
      refine ⟨(((z.re : Int) : Real), ((z.im : Int) : Real)), ?_⟩
      simp [ClosedSquareRealization]
    have diagonalBridge : ∀ (a b : LatticeCell),
        a ∈ (T.cells : Set LatticeCell) → b ∈ (T.cells : Set LatticeCell) →
        ¬ reachable a b →
        (b = a + 1 + ⟨0, 1⟩ ∨ b = a + 1 - ⟨0, 1⟩ ∨
         b = a - 1 + ⟨0, 1⟩ ∨ b = a - 1 - ⟨0, 1⟩) → False := by
      intro a b ha hb hab hdiag
      have sideForward : ∀ (u v : LatticeCell),
          FourNeighborAdjacent u v → u ∈ (T.cells : Set LatticeCell) →
          v ∈ (T.cells : Set LatticeCell) → reachable u v := by
        intro u v huv hu hv
        exact Relation.ReflTransGen.single ⟨huv, hu, hv⟩
      rcases hdiag with hdiag | hdiag | hdiag | hdiag
      · subst b
        by_cases hu : a + 1 ∈ (T.cells : Set LatticeCell)
        · exact hab (Relation.ReflTransGen.trans
            (sideForward a (a + 1) (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]) ha hu)
            (sideForward (a + 1) (a + 1 + ⟨0, 1⟩)
              (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]) hu hb))
        by_cases hv : a + ⟨0, 1⟩ ∈ (T.cells : Set LatticeCell)
        · exact hab (Relation.ReflTransGen.trans
            (sideForward a (a + ⟨0, 1⟩)
              (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]) ha hv)
            (sideForward (a + ⟨0, 1⟩) (a + 1 + ⟨0, 1⟩)
              (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]) hv hb))
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          noChecker (a + 1 + ⟨0, 1⟩) (Or.inl ⟨hb,
            by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using ha,
            by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hv,
            by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hu⟩)
      · subst b
        by_cases hu : a + 1 ∈ (T.cells : Set LatticeCell)
        · exact hab (Relation.ReflTransGen.trans
            (sideForward a (a + 1) (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]) ha hu)
            (sideForward (a + 1) (a + 1 - ⟨0, 1⟩)
              (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]) hu hb))
        by_cases hv : a - ⟨0, 1⟩ ∈ (T.cells : Set LatticeCell)
        · exact hab (Relation.ReflTransGen.trans
            (sideForward a (a - ⟨0, 1⟩)
              (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]) ha hv)
            (sideForward (a - ⟨0, 1⟩) (a + 1 - ⟨0, 1⟩)
              (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]) hv hb))
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          noChecker (a + 1) (Or.inr ⟨
            by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using ha,
            hb, hu,
            by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hv⟩)
      · subst b
        by_cases hu : a - 1 ∈ (T.cells : Set LatticeCell)
        · exact hab (Relation.ReflTransGen.trans
            (sideForward a (a - 1) (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]) ha hu)
            (sideForward (a - 1) (a - 1 + ⟨0, 1⟩)
              (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]) hu hb))
        by_cases hv : a + ⟨0, 1⟩ ∈ (T.cells : Set LatticeCell)
        · exact hab (Relation.ReflTransGen.trans
            (sideForward a (a + ⟨0, 1⟩)
              (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]) ha hv)
            (sideForward (a + ⟨0, 1⟩) (a - 1 + ⟨0, 1⟩)
              (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]) hv hb))
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          noChecker (a + ⟨0, 1⟩) (Or.inr ⟨
            by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hb,
            by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using ha, hv,
            by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hu⟩)
      · subst b
        by_cases hu : a - 1 ∈ (T.cells : Set LatticeCell)
        · exact hab (Relation.ReflTransGen.trans
            (sideForward a (a - 1) (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]) ha hu)
            (sideForward (a - 1) (a - 1 - ⟨0, 1⟩)
              (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]) hu hb))
        by_cases hv : a - ⟨0, 1⟩ ∈ (T.cells : Set LatticeCell)
        · exact hab (Relation.ReflTransGen.trans
            (sideForward a (a - ⟨0, 1⟩)
              (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]) ha hv)
            (sideForward (a - ⟨0, 1⟩) (a - 1 - ⟨0, 1⟩)
              (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]) hv hb))
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          noChecker a (Or.inl ⟨ha, hb, hu,
            by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hv⟩)
    have reachXY : reachable x y := FourNeighborProof.reachXY T realizationConnected overlap x hx
        y hy squareNonempty diagonalBridge
    have walk : ∀ {a b : LatticeCell}, a ∈ (T.cells : Set LatticeCell) →
        b ∈ (T.cells : Set LatticeCell) → reachable a b →
        ∃ p : List LatticeCell,
          p.head? = some a ∧ p.getLast? = some b ∧
          (∀ z ∈ p, z ∈ (T.cells : Set LatticeCell)) ∧
          ∀ u v : LatticeCell, ∀ l₁ l₂ : List LatticeCell,
            p = l₁ ++ u :: v :: l₂ → FourNeighborAdjacent u v := FourNeighborProof.walk T
    rcases walk hx hy reachXY with ⟨p, hphead, hplast, hpinside, hpedge⟩
    exact ⟨p, hphead, hplast, hpinside, hpedge⟩

end ApollonianSuperharmonic

end
