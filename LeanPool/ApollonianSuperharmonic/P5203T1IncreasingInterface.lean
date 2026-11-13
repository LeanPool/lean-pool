/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.DiamondFootprintCoordinates

public import LeanPool.ApollonianSuperharmonic.TileTranslationProperties

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondVertexIncidence
public import LeanPool.ApollonianSuperharmonic.P5157T1AlternatingStaircase
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: P5203T1IncreasingInterface]

/-!
# P5203T1IncreasingInterface

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5203T1IncreasingInterface (k : Nat) (hk : 0 < k) (u : GaussianInt) :
    let T := TileTranslation (DiamondTile k) u
    let U := TileTranslation (DiamondTile k) (u + ⟨(k : Int) + 1, -(k : Int)⟩)
    let p := fun j : Nat => u + (⟨1 + (j / 2 : Nat), ((j + 1) / 2 : Nat)⟩ : GaussianInt)
    let V : Set GaussianInt := {z | 1 ≤ (z - u).re ∧ (z - u).re ≤ k ∧
      (z - u).re - 1 ≤ (z - u).im ∧ (z - u).im ≤ (z - u).re}
    let E : Set (Finset GaussianInt) := {e | ∃ j < 2 * k - 1, e = {p j, p (j + 1)}}
    T.cells.Nonempty ∧ U.cells.Nonempty ∧ Disjoint T.cells U.cells ∧
      BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U = V ∧
      BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U = E ∧
      SimpleGridPath V E := by
-- BODY
  classical
  have footprint (z : GaussianInt) :
      z ∈ FootprintVertices (DiamondTile k) ↔
        0 ≤ z.im ∧ z.im ≤ 2 * (k : Int) ∧
        -(k : Int) ≤ z.re ∧ z.re ≤ k ∧
        -(z.im + 1) ≤ z.re ∧ z.re ≤ z.im + 1 ∧
        -(2 * (k : Int) - z.im + 1) ≤ z.re ∧
          z.re ≤ 2 * (k : Int) - z.im + 1 := DiamondFootprintCoordinates.coordinates k hk z
  let D := DiamondTile k
  let b : GaussianInt := ⟨(k : Int) + 1, -(k : Int)⟩
  let T := TileTranslation D u
  let U := TileTranslation D (u + b)
  let p := fun j : Nat => u + (⟨1 + (j / 2 : Nat), ((j + 1) / 2 : Nat)⟩ : GaussianInt)
  let V : Set GaussianInt := {z | 1 ≤ (z - u).re ∧ (z - u).re ≤ k ∧
    (z - u).re - 1 ≤ (z - u).im ∧ (z - u).im ≤ (z - u).re}
  let E : Set (Finset GaussianInt) := {e | ∃ j < 2 * k - 1, e = {p j, p (j + 1)}}
  let F := fun z : GaussianInt =>
    0 ≤ z.im ∧ z.im ≤ 2 * (k : Int) ∧ -(k : Int) ≤ z.re ∧ z.re ≤ k ∧
    -(z.im + 1) ≤ z.re ∧ z.re ≤ z.im + 1 ∧
    -(2 * (k : Int) - z.im + 1) ≤ z.re ∧ z.re ≤ 2 * (k : Int) - z.im + 1
  let I := fun z : GaussianInt =>
    1 ≤ z.im ∧ z.im ≤ 2 * (k : Int) - 1 ∧
    -(z.im - 1) ≤ z.re ∧ z.re ≤ z.im - 1 ∧
    -(2 * (k : Int) - z.im - 1) ≤ z.re ∧ z.re ≤ 2 * (k : Int) - z.im - 1
  change T.cells.Nonempty ∧ U.cells.Nonempty ∧ Disjoint T.cells U.cells ∧
    BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U = V ∧
    BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U = E ∧ SimpleGridPath V E
  have cell (w z : GaussianInt) :
      z ∈ (TileTranslation D w).cells ↔ z - w ∈ DiamondCellDomain k :=
    TileTranslationProperties.mem_cells (DiamondTile k) w z
  have ne (w : GaussianInt) : (TileTranslation D w).cells.Nonempty := by
    refine ⟨w, (cell w w).mpr ?_⟩
    rw [sub_self]
    exact (P4194T1DiamondCellRows k 0).1.mpr (by norm_num; omega)
  have disj : Disjoint T.cells U.cells := by
    apply Finset.disjoint_left.mpr
    intro z hT hU
    have hT := (P4194T1DiamondCellRows k (z - u)).1.mp ((cell u z).mp hT)
    have hU := (P4194T1DiamondCellRows k (z - (u + b))).1.mp
      ((cell (u + b) z).mp hU)
    simp only [Zsqrtd.im_sub, Zsqrtd.im_add, Zsqrtd.re_sub, Zsqrtd.re_add, b] at hT hU
    omega
  have boundary (w z : GaussianInt) :
      z ∈ BoundaryFootprintVertices (TileTranslation D w) ↔ F (z - w) ∧ ¬I (z - w) := by
    have local_formula (x : GaussianInt) : x ∈ BoundaryFootprintVertices D ↔ F x ∧ ¬I x := by
      rw [(P4194T1DiamondVertexIncidence k hk x).2]
      apply and_congr
      · exact ((P4194T1DiamondVertexIncidence k hk x).1).symm.trans
          (footprint x)
      · rw [← not_forall]
        exact not_congr (P4194T1DiamondCellRows k x).2
    rw [(TileTranslationFormulas D w).2.2.2.2.2.2.2.1]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [GaussianTranslation] using (local_formula x).mp hx
    · intro hz
      exact ⟨z - w, (local_formula (z - w)).mpr hz, by simp [GaussianTranslation]⟩
  have hv : BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U = V := by
    ext z
    dsimp only [T, U]
    simp only [Set.mem_inter_iff, boundary]
    dsimp [V, F, I, b]
    omega
  have vp : V = {z | ∃ j ≤ 2 * k - 1, z = p j} := by
    ext z
    constructor
    · intro hz
      have hz : 1 ≤ (z - u).re ∧ (z - u).re ≤ k ∧
          (z - u).re - 1 ≤ (z - u).im ∧ (z - u).im ≤ (z - u).re := hz
      let j := ((z - u).re + (z - u).im - 1).toNat
      have hj : (j : Int) = (z - u).re + (z - u).im - 1 :=
        Int.toNat_of_nonneg (by omega)
      refine ⟨j, by omega, ?_⟩
      apply Zsqrtd.ext <;>
        simp only [p, Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_sub, Zsqrtd.im_sub] at * <;>
        omega
    · rintro ⟨j, hj, rfl⟩
      simp only [V, Set.mem_ofPred_eq, p, Zsqrtd.re_add, Zsqrtd.im_add,
        Zsqrtd.re_sub, Zsqrtd.im_sub]
      omega
  have peq (j : Nat) : P5157T1StaircasePoint (u + 1) false 1 j = p j := by
    ext <;> simp [P5157T1StaircasePoint, p]; ring
  have path : SimpleGridPath V E := by
    rw [vp]
    simpa only [peq] using
      (P5157T1AlternatingStaircase (u + 1) false 1 (Or.inl rfl)
        (2 * k - 1) (by omega)).2
  have even (t : Nat) : p (2 * t) = u + (⟨1 + (t : Int), (t : Int)⟩ : GaussianInt) := by
    ext <;> simp [p]; omega
  have odd (t : Nat) : p (2 * t + 1) =
      u + (⟨1 + (t : Int), (t : Int) + 1⟩ : GaussianInt) := by
    ext <;> simp [p] <;> omega
  have vertical (t : Nat) (ht : t < k) :
      ({p (2 * t), p (2 * t + 1)} : Finset GaussianInt) ∈
        BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U := by
    have step : p (2 * t + 1) = p (2 * t) + ⟨0, 1⟩ := by
      rw [even, odd]
      ext <;> simp; ring
    rw [step]
    constructor
    · refine ⟨p (2 * t), Or.inr ⟨rfl, Or.inr ?_⟩⟩
      simp only [T, cell, (P4194T1DiamondCellRows _ _).1, even,
        Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add,
        Zsqrtd.re_one, Zsqrtd.im_one]
      omega
    · refine ⟨p (2 * t), Or.inr ⟨rfl, Or.inl ?_⟩⟩
      simp only [U, cell, (P4194T1DiamondCellRows _ _).1, even,
        Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add,
        Zsqrtd.re_one, Zsqrtd.im_one, b]
      omega
  have horizontal (t : Nat) (ht : t + 1 < k) :
      ({p (2 * t + 1), p (2 * (t + 1))} : Finset GaussianInt) ∈
        BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U := by
    have step : p (2 * (t + 1)) = p (2 * t + 1) + 1 := by
      rw [even, odd]
      ext <;> simp; ring
    rw [step]
    constructor
    · refine ⟨p (2 * t + 1), Or.inl ⟨rfl, Or.inl ?_⟩⟩
      simp only [T, cell, (P4194T1DiamondCellRows _ _).1, odd,
        Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add]
      omega
    · refine ⟨p (2 * t + 1), Or.inl ⟨rfl, Or.inr ?_⟩⟩
      simp only [U, cell, (P4194T1DiamondCellRows _ _).1, odd,
        Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add, b]
      omega
  have rank (j : Nat) : (p j - u).re + (p j - u).im - 1 = (j : Int) := by
    simp only [p, Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add]
    omega
  have he : BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U = E := by
    ext e
    constructor
    · intro hh
      have ep (z : GaussianInt) (hz : z ∈ e) : ∃ j ≤ 2 * k - 1, z = p j := by
        have hb : z ∈ BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U :=
          ⟨by rw [BoundaryFootprintVertices, ite_eq_left (ne u)]; exact ⟨e, hh.1, hz⟩,
           by rw [BoundaryFootprintVertices, ite_eq_left (ne (u + b))]; exact ⟨e, hh.2, hz⟩⟩
        rw [hv, vp] at hb
        exact hb
      obtain ⟨z, hz⟩ := hh.1
      rcases hz with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · obtain ⟨i, hi, h0⟩ := ep z (by simp)
        obtain ⟨j, hj, h1⟩ := ep (z + 1) (by simp)
        have r0 := rank i
        have r1 := rank j
        rw [← h0] at r0
        rw [← h1] at r1
        simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add,
          Zsqrtd.re_one, Zsqrtd.im_one] at r0 r1
        have ij : j = i + 1 := by omega
        exact ⟨i, by omega, by rw [h1, h0, ij]⟩
      · obtain ⟨i, hi, h0⟩ := ep z (by simp)
        obtain ⟨j, hj, h1⟩ := ep (z + ⟨0, 1⟩) (by simp)
        have r0 := rank i
        have r1 := rank j
        rw [← h0] at r0
        rw [← h1] at r1
        simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add] at r0 r1
        have ij : j = i + 1 := by omega
        exact ⟨i, by omega, by rw [h1, h0, ij]⟩
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨t, ht | ht⟩ : ∃ t : Nat, j = 2 * t ∨ j = 2 * t + 1 :=
        ⟨j / 2, by omega⟩
      · subst j
        exact vertical t (by omega)
      · subst j
        rw [show 2 * t + 1 + 1 = 2 * (t + 1) by omega]
        exact horizontal t (by omega)
  exact ⟨ne u, ne (u + b), disj, hv, he, path⟩

end ApollonianSuperharmonic

end
