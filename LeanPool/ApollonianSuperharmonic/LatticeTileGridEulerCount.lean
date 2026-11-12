/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Set.Card
public import LeanPool.ApollonianSuperharmonic.FiniteBiconnectedHorizontalRunTree
public import LeanPool.ApollonianSuperharmonic.FiniteSquareIncidenceIdentities
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.LatticeTileComplementGridConnected
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure
public import LeanPool.ApollonianSuperharmonic.ProtoTile

/-!
# LatticeTileGridEulerCount

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

open scoped BigOperators

-- [TABLET NODE: LatticeTileGridEulerCount]
namespace GridEulerGeometry

private theorem hrun :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (LatticeTile T) → ((FourNeighborConnected (↑T.cells : Set LatticeCell)
            ∧ NoCheckerboardCellVertex (↑T.cells : Set LatticeCell) ∧ SimpleGridCycle
            (BoundaryFootprintVertices T) (BoundaryFootprintEdges T)) → (
        let I : GaussianInt := ⟨0, 1⟩
        let R := (T.cells.filter fun z => z - 1 ∉ T.cells).card
        let J := ((T.cells.filter fun z => z + I ∈ T.cells).filter fun z =>
          ¬ (z - 1 ∈ T.cells ∧ z - 1 + I ∈ T.cells)).card
        R = J + 1)) ) := by
  classical
  intro T hT hgrid I R J
  simpa [R, J, I] using
    FiniteBiconnectedHorizontalRunTree T.cells hgrid.1
      (LatticeTileComplementGridConnected T hT)

private theorem hparts :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let H := (T.cells.filter fun z => z - 1 ∈ T.cells).card
        let V := (T.cells.filter fun z => z + I ∈ T.cells).card
        let Q := (T.cells.filter fun z =>
          z + 1 ∈ T.cells ∧ z + I ∈ T.cells ∧ z + 1 + I ∈ T.cells).card
        let R := (T.cells.filter fun z => z - 1 ∉ T.cells).card
        let J := ((T.cells.filter fun z => z + I ∈ T.cells).filter fun z =>
          ¬ (z - 1 ∈ T.cells ∧ z - 1 + I ∈ T.cells)).card
        T.cells.card = H + R ∧ V = Q + J ) := by
  classical
  intro T I H V Q R J
  let vertical := T.cells.filter fun z => z + I ∈ T.cells
  have hcell := Finset.card_filter_add_card_filter_not
    (s := T.cells) (fun z => z - 1 ∈ T.cells)
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := vertical) (fun z => z - 1 ∈ T.cells ∧ z - 1 + I ∈ T.cells)
  have hQ :
      (vertical.filter fun z =>
          z - 1 ∈ T.cells ∧ z - 1 + I ∈ T.cells).card = Q := by
    change (vertical.filter fun z =>
        z - 1 ∈ T.cells ∧ z - 1 + I ∈ T.cells).card =
      (T.cells.filter fun z =>
        z + 1 ∈ T.cells ∧ z + I ∈ T.cells ∧
          z + 1 + I ∈ T.cells).card
    apply Finset.card_bij (fun z _ => z - 1)
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      rcases hz with ⟨hzv, hzleft, hzleftI⟩
      rw [Finset.mem_filter] at hzv
      refine ⟨hzleft, ?_, ?_, ?_⟩
      · simpa using hzv.1
      · simpa [I, Zsqrtd.ext_iff] using hzleftI
      · simpa [I, Zsqrtd.ext_iff] using hzv.2
    · intro a ha b hb hab
      apply_fun (fun z : GaussianInt => z + 1) at hab
      simpa using hab
    · intro q hq
      rw [Finset.mem_filter] at hq
      rcases hq with ⟨hqS, hq1, hqI, hq1I⟩
      refine ⟨q + 1, ?_, by simp⟩
      rw [Finset.mem_filter, Finset.mem_filter]
      refine ⟨⟨hq1, hq1I⟩, ?_, ?_⟩
      · simpa using hqS
      · simpa [I, Zsqrtd.ext_iff] using hqI
  constructor
  · change T.cells.card =
      (T.cells.filter fun z => z - 1 ∈ T.cells).card +
      (T.cells.filter fun z => z - 1 ∉ T.cells).card
    exact hcell.symm
  · change vertical.card = Q +
      (vertical.filter fun z =>
        ¬ (z - 1 ∈ T.cells ∧ z - 1 + I ∈ T.cells)).card
    rw [← hQ]
    exact hsplit.symm

private theorem hcornerMem :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        ∀ {z : GaussianInt}, (z ∈ T.cells) → (z ∈ cornerBag.toFinset) ) := by
  classical
  intro T I cornerBag z hz
  rw [Multiset.mem_toFinset, Multiset.mem_bind]
  exact ⟨z, hz, by simp⟩

private theorem hcornerCount :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        ∀ (z : GaussianInt), cornerBag.count z = (if z ∈ T.cells then 1 else 0) + (if z - 1 ∈
            T.cells then 1 else 0) + (if z - I ∈ T.cells then 1 else 0) + (if z - 1 - I ∈ T.cells
            then 1 else 0) ) := by
  classical
  intro T I cornerBag z
  dsimp only [cornerBag]
  rw [Multiset.count_bind, ← Finset.sum_eq_multiset_sum]
  simp only [Multiset.coe_count, List.count_cons, beq_iff_eq,
    List.count_nil]
  have h11 : ∀ c : GaussianInt, (c + 1 + I = z) ↔
      (c = z - 1 - I) := by
    intro c
    constructor <;> intro h
    · rw [← h]; ring
    · rw [h]; ring
  have hI : ∀ c : GaussianInt, (c + I = z) ↔ (c = z - I) := by
    intro c
    constructor <;> intro h
    · rw [← h]; ring
    · rw [h]; ring
  have h1 : ∀ c : GaussianInt, (c + 1 = z) ↔ (c = z - 1) := by
    intro c
    constructor <;> intro h
    · rw [← h]; ring
    · rw [h]; ring
  simp_rw [h11, hI, h1]
  simp only [Finset.sum_add_distrib, zero_add]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq',
    Finset.sum_ite_eq']
  omega

private theorem hpoint :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (NoCheckerboardCellVertex (T.cells : Set LatticeCell)) → (
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        (∀ (z : GaussianInt), cornerBag.count z = (if z ∈ T.cells then 1 else 0) + (if z - 1 ∈
            T.cells then 1 else 0) + (if z - I ∈ T.cells then 1 else 0) + (if z - 1 - I ∈ T.cells
            then 1 else 0)) → (∀ (z : GaussianInt), (if cornerBag.count z = 1 then 1 else 0) + 2
            * ((if z ∈ T.cells ∧ z - 1 ∈ T.cells then 1 else 0) + (if z - 1 ∈ T.cells ∧ z - 1 - I
            ∈ T.cells then 1 else 0) + (if z - 1 - I ∈ T.cells ∧ z - I ∈ T.cells then 1 else 0) +
            (if z - I ∈ T.cells ∧ z ∈ T.cells then 1 else 0)) = (if cornerBag.count z = 3 then 1
            else 0) + cornerBag.count z + 4 * (if z ∈ T.cells ∧ z - 1 ∈ T.cells ∧ z - I ∈ T.cells
            ∧ z - 1 - I ∈ T.cells then 1 else 0))) ) := by
  classical
  intro T hcheck I cornerBag hcornerCount z
  have hc := hcheck z
  change ¬ ((z ∈ T.cells ∧ z - 1 - I ∈ T.cells ∧
      z - 1 ∉ T.cells ∧ z - I ∉ T.cells) ∨
    (z - 1 ∈ T.cells ∧ z - I ∈ T.cells ∧
      z ∉ T.cells ∧ z - 1 - I ∉ T.cells)) at hc
  rw [hcornerCount]
  by_cases ha : z ∈ T.cells <;>
    by_cases hb : z - 1 ∈ T.cells <;>
    by_cases hc' : z - I ∈ T.cells <;>
    by_cases hd : z - 1 - I ∈ T.cells <;> simp_all

private theorem hAB :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        let H := (T.cells.filter fun z => z - 1 ∈ T.cells).card
        (∀ {z : GaussianInt}, (z ∈ T.cells) → (z ∈ cornerBag.toFinset)) →
            ((cornerBag.toFinset.filter fun z => z ∈ T.cells ∧ z - 1 ∈ T.cells).card = H) ) := by
  classical
  intro T I cornerBag H hcornerMem
  change (cornerBag.toFinset.filter fun z =>
      z ∈ T.cells ∧ z - 1 ∈ T.cells).card =
    (T.cells.filter fun z => z - 1 ∈ T.cells).card
  congr 1
  ext z
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨_, hz, hz1⟩
    exact ⟨hz, hz1⟩
  · rintro ⟨hz, hz1⟩
    exact ⟨hcornerMem hz, hz, hz1⟩

private theorem hDC :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        let H := (T.cells.filter fun z => z - 1 ∈ T.cells).card
        (cornerBag.toFinset.filter fun z => z - 1 - I ∈ T.cells ∧ z - I ∈ T.cells).card = H ) := by
  classical
  intro T I cornerBag H
  change (cornerBag.toFinset.filter fun z =>
      z - 1 - I ∈ T.cells ∧ z - I ∈ T.cells).card =
    (T.cells.filter fun z => z - 1 ∈ T.cells).card
  apply Finset.card_bij (fun z _ => z - I)
  · intro z hz
    rw [Finset.mem_filter] at hz ⊢
    refine ⟨hz.2.2, ?_⟩
    convert hz.2.1 using 1; ring
  · intro a ha b hb hab
    apply_fun (fun z : GaussianInt => z + I) at hab
    simpa using hab
  · intro q hq
    rw [Finset.mem_filter] at hq
    refine ⟨q + I, ?_, by simp⟩
    rw [Finset.mem_filter]
    refine ⟨?_, ?_, ?_⟩
    · rw [Multiset.mem_toFinset, Multiset.mem_bind]
      exact ⟨q, hq.1, by simp⟩
    · convert hq.2 using 1; ring
    · convert hq.1 using 1; ring

private theorem hCA :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        let V := (T.cells.filter fun z => z + I ∈ T.cells).card
        (cornerBag.toFinset.filter fun z => z - I ∈ T.cells ∧ z ∈ T.cells).card = V ) := by
  classical
  intro T I cornerBag V
  change (cornerBag.toFinset.filter fun z =>
      z - I ∈ T.cells ∧ z ∈ T.cells).card =
    (T.cells.filter fun z => z + I ∈ T.cells).card
  apply Finset.card_bij (fun z _ => z - I)
  · intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨hz.2.1, by simpa using hz.2.2⟩
  · intro a ha b hb hab
    apply_fun (fun z : GaussianInt => z + I) at hab
    simpa using hab
  · intro q hq
    rw [Finset.mem_filter] at hq
    refine ⟨q + I, ?_, by simp⟩
    rw [Finset.mem_filter]
    refine ⟨?_, ?_, ?_⟩
    · rw [Multiset.mem_toFinset, Multiset.mem_bind]
      exact ⟨q, hq.1, by simp⟩
    · convert hq.1 using 1; ring
    · simpa using hq.2

private theorem hBD :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        let V := (T.cells.filter fun z => z + I ∈ T.cells).card
        (cornerBag.toFinset.filter fun z => z - 1 ∈ T.cells ∧ z - 1 - I ∈ T.cells).card = V ) := by
  classical
  intro T I cornerBag V
  change (cornerBag.toFinset.filter fun z =>
      z - 1 ∈ T.cells ∧ z - 1 - I ∈ T.cells).card =
    (T.cells.filter fun z => z + I ∈ T.cells).card
  apply Finset.card_bij (fun z _ => z - 1 - I)
  · intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨hz.2.2, by simpa [I, Zsqrtd.ext_iff] using hz.2.1⟩
  · intro a ha b hb hab
    apply_fun (fun z : GaussianInt => z + 1 + I) at hab
    simpa using hab
  · intro q hq
    rw [Finset.mem_filter] at hq
    refine ⟨q + 1 + I, ?_, by ring⟩
    rw [Finset.mem_filter]
    refine ⟨?_, ?_, ?_⟩
    · rw [Multiset.mem_toFinset, Multiset.mem_bind]
      exact ⟨q, hq.1, by simp⟩
    · convert hq.2 using 1; ring
    · convert hq.1 using 1; ring

private theorem hfull :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        let Q := (T.cells.filter fun z =>
          z + 1 ∈ T.cells ∧ z + I ∈ T.cells ∧ z + 1 + I ∈ T.cells).card
        (cornerBag.toFinset.filter fun z => z ∈ T.cells ∧ z - 1 ∈ T.cells ∧ z - I ∈ T.cells ∧ z -
            1 - I ∈ T.cells).card = Q ) := by
  classical
  intro T I cornerBag Q
  change (cornerBag.toFinset.filter fun z =>
      z ∈ T.cells ∧ z - 1 ∈ T.cells ∧ z - I ∈ T.cells ∧
        z - 1 - I ∈ T.cells).card =
    (T.cells.filter fun z => z + 1 ∈ T.cells ∧
      z + I ∈ T.cells ∧ z + 1 + I ∈ T.cells).card
  apply Finset.card_bij (fun z _ => z - 1 - I)
  · intro z hz
    rw [Finset.mem_filter] at hz ⊢
    rcases hz with ⟨_, hz, hz1, hzI, hz1I⟩
    refine ⟨hz1I, ?_, ?_, ?_⟩
    · convert hzI using 1; ring
    · convert hz1 using 1; ring
    · convert hz using 1; ring
  · intro a ha b hb hab
    apply_fun (fun z : GaussianInt => z + 1 + I) at hab
    simpa using hab
  · intro q hq
    rw [Finset.mem_filter] at hq
    rcases hq with ⟨hq, hq1, hqI, hq1I⟩
    refine ⟨q + 1 + I, ?_, by ring⟩
    rw [Finset.mem_filter]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [Multiset.mem_toFinset, Multiset.mem_bind]
      exact ⟨q, hq, by simp⟩
    · simpa [I, Zsqrtd.ext_iff] using hq1I
    · convert hqI using 1; ring
    · convert hq1 using 1; ring
    · convert hq using 1; ring

private theorem hsum :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        let N : Nat → Nat := fun k =>
          (cornerBag.toFinset.filter fun z => cornerBag.count z = k).card
        let H := (T.cells.filter fun z => z - 1 ∈ T.cells).card
        let V := (T.cells.filter fun z => z + I ∈ T.cells).card
        let Q := (T.cells.filter fun z =>
          z + 1 ∈ T.cells ∧ z + I ∈ T.cells ∧ z + 1 + I ∈ T.cells).card
        let R := (T.cells.filter fun z => z - 1 ∉ T.cells).card
        let J := ((T.cells.filter fun z => z + I ∈ T.cells).filter fun z =>
          ¬ (z - 1 ∈ T.cells ∧ z - 1 + I ∈ T.cells)).card
        (R = J + 1) → ((T.cells.card = H + R ∧ V = Q + J) → ((∀ (z : GaussianInt), (if
            cornerBag.count z = 1 then 1 else 0) + 2 * ((if z ∈ T.cells ∧ z - 1 ∈ T.cells then 1
            else 0) + (if z - 1 ∈ T.cells ∧ z - 1 - I ∈ T.cells then 1 else 0) + (if z - 1 - I ∈
            T.cells ∧ z - I ∈ T.cells then 1 else 0) + (if z - I ∈ T.cells ∧ z ∈ T.cells then 1
            else 0)) = (if cornerBag.count z = 3 then 1 else 0) + cornerBag.count z + 4 * (if z ∈
            T.cells ∧ z - 1 ∈ T.cells ∧ z - I ∈ T.cells ∧ z - 1 - I ∈ T.cells then 1 else 0)) →
            (((cornerBag.toFinset.filter fun z => z ∈ T.cells ∧ z - 1 ∈ T.cells).card = H) →
            (((cornerBag.toFinset.filter fun z => z - 1 - I ∈ T.cells ∧ z - I ∈ T.cells).card =
            H) → (((cornerBag.toFinset.filter fun z => z - I ∈ T.cells ∧ z ∈ T.cells).card = V) →
            (((cornerBag.toFinset.filter fun z => z - 1 ∈ T.cells ∧ z - 1 - I ∈ T.cells).card =
            V) → (((cornerBag.toFinset.filter fun z => z ∈ T.cells ∧ z - 1 ∈ T.cells ∧ z - I ∈
            T.cells ∧ z - 1 - I ∈ T.cells).card = Q) → (N 1 + 4 * (H + V) = N 3 + 4 *
            T.cells.card + 4 * Q)))))))) ) := by
  classical
  intro T I cornerBag N H V Q R J hrun hparts hpoint hAB hDC hCA hBD hfull
  have hp : (∑ z ∈ cornerBag.toFinset,
      ((if cornerBag.count z = 1 then 1 else 0) +
        2 * ((if z ∈ T.cells ∧ z - 1 ∈ T.cells then 1 else 0) +
          (if z - 1 ∈ T.cells ∧ z - 1 - I ∈ T.cells then 1 else 0) +
          (if z - 1 - I ∈ T.cells ∧ z - I ∈ T.cells then 1 else 0) +
          (if z - I ∈ T.cells ∧ z ∈ T.cells then 1 else 0)))) =
      ∑ z ∈ cornerBag.toFinset,
        ((if cornerBag.count z = 3 then 1 else 0) +
          cornerBag.count z +
          4 * (if z ∈ T.cells ∧ z - 1 ∈ T.cells ∧
            z - I ∈ T.cells ∧ z - 1 - I ∈ T.cells then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro z _
    exact hpoint z
  simp only [Finset.sum_add_distrib] at hp
  simp_rw [← Finset.mul_sum] at hp
  simp only [Finset.sum_add_distrib] at hp
  simp? [hAB, hBD, hDC, hCA, hfull] at hp
  have hbag : cornerBag.card = 4 * T.cells.card := by
    simp [cornerBag, Nat.mul_comm]
  dsimp only [N]
  omega

end GridEulerGeometry

theorem LatticeTileGridEulerCount (T : ProtoTile) (hT : LatticeTile T) :
    (FootprintVertices T).ncard + T.cells.card =
      (FootprintEdges T).ncard + 1 := by
-- BODY
  classical
  have hgrid := LatticeTileGridStructure T hT
  have hne : T.cells.Nonempty := hgrid.1.1
  have hcheck : NoCheckerboardCellVertex (T.cells : Set LatticeCell) :=
    hgrid.2.1
  let I : GaussianInt := ⟨0, 1⟩
  let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
    ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
  let N : Nat → Nat := fun k =>
    (cornerBag.toFinset.filter fun z => cornerBag.count z = k).card
  have hincidence := FiniteSquareIncidenceIdentities T hne hcheck
  change 4 * T.cells.card = N 1 + 2 * N 2 + 3 * N 3 + 4 * N 4 ∧
      (FootprintVertices T).ncard = N 1 + N 2 + N 3 + N 4 ∧
      2 * (FootprintEdges T).ncard = 4 * T.cells.card +
        (BoundaryFootprintEdges T).ncard ∧
      (BoundaryFootprintEdges T).ncard = N 1 + N 2 + N 3 at hincidence
  rcases hincidence with ⟨hcorner, hvertex, hedge, hboundary⟩
  have hturn : N 1 = N 3 + 4 := by
    let H := (T.cells.filter fun z => z - 1 ∈ T.cells).card
    let V := (T.cells.filter fun z => z + I ∈ T.cells).card
    let Q := (T.cells.filter fun z =>
      z + 1 ∈ T.cells ∧ z + I ∈ T.cells ∧ z + 1 + I ∈ T.cells).card
    let R := (T.cells.filter fun z => z - 1 ∉ T.cells).card
    let J := ((T.cells.filter fun z => z + I ∈ T.cells).filter fun z =>
      ¬ (z - 1 ∈ T.cells ∧ z - 1 + I ∈ T.cells)).card
    have hrun : R = J + 1  := GridEulerGeometry.hrun T hT hgrid
    have hparts : T.cells.card = H + R ∧ V = Q + J  := GridEulerGeometry.hparts T
    have hEuler : T.cells.card + Q = H + V + 1 := by
      omega
    have hcornerMem {z : GaussianInt} (hz : z ∈ T.cells) := GridEulerGeometry.hcornerMem T (z :=
        z) hz
    have hcornerCount (z : GaussianInt) := GridEulerGeometry.hcornerCount T z
    have hpoint (z : GaussianInt) := GridEulerGeometry.hpoint T hcheck hcornerCount z
    have hAB := GridEulerGeometry.hAB T hcornerMem
    have hDC := GridEulerGeometry.hDC T
    have hCA := GridEulerGeometry.hCA T
    have hBD := GridEulerGeometry.hBD T
    have hfull := GridEulerGeometry.hfull T
    have hsum : N 1 + 4 * (H + V) =
        N 3 + 4 * T.cells.card + 4 * Q  := GridEulerGeometry.hsum T hrun hparts hpoint hAB hDC
            hCA hBD hfull
    omega
  omega

end ApollonianSuperharmonic

end
