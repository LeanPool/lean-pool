/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondVertexIncidence
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.P5157T1StaircasePoint

-- [TABLET NODE: P5250T1CommonVertices]

/-!
# P5250T1CommonVertices

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5250T1CommonVertices (k : Nat) (hk : 1 < k) :
    let D := DiamondTile k
    let L := TileTranslation D ⟨0, -(2 * (k : Int))⟩
    let Eplus := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
    let Eminus := TileTranslation (DiamondTile (k - 1)) ⟨-(k : Int), 1 - (k : Int)⟩
    let N := 2 * (k - 1)
    let p := P5157T1StaircasePoint 1 false 1
    let q := P5157T1StaircasePoint 1 false (-1)
    let r := P5157T1StaircasePoint ⟨-(k : Int), (k : Int) - 1⟩ true (-1)
    BoundaryFootprintVertices D ∩ BoundaryFootprintVertices Eplus =
        {v | ∃ j ≤ N, v = p j} ∧
      BoundaryFootprintVertices L ∩ BoundaryFootprintVertices Eplus =
        {v | ∃ j ≤ N, v = q j} ∧
      BoundaryFootprintVertices D ∩ BoundaryFootprintVertices Eminus =
        {v | ∃ j ≤ N, v = r j} := by
-- BODY
  classical
  have footprint (m : Nat) (hm : 0 < m) (z : GaussianInt) :
      z ∈ FootprintVertices (DiamondTile m) ↔
        0 ≤ z.im ∧ z.im ≤ 2 * (m : Int) ∧
        -(m : Int) ≤ z.re ∧ z.re ≤ m ∧
        -(z.im + 1) ≤ z.re ∧ z.re ≤ z.im + 1 ∧
        -(2 * (m : Int) - z.im + 1) ≤ z.re ∧
          z.re ≤ 2 * (m : Int) - z.im + 1 := by
    rw [(P4194T1DiamondVertexIncidence m hm z).1]
    simp only [Fin.exists_fin_succ, Fin.exists_fin_succ, Fin.exists_fin_succ,
      Fin.exists_fin_succ]
    rw [show LatticeVertexIncidentCell z 0 = z by rfl,
      show LatticeVertexIncidentCell z (Fin.succ 0) = z - 1 by rfl,
      show LatticeVertexIncidentCell z (Fin.succ 0).succ = z - 1 - ⟨0, 1⟩ by rfl,
      show LatticeVertexIncidentCell z (Fin.succ 0).succ.succ = z - ⟨0, 1⟩ by rfl]
    rw [(P4194T1DiamondCellRows m z).1,
      (P4194T1DiamondCellRows m (z - 1)).1,
      (P4194T1DiamondCellRows m (z - 1 - ⟨0, 1⟩)).1,
      (P4194T1DiamondCellRows m (z - ⟨0, 1⟩)).1]
    simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one]
    simp []
    omega
  let F := fun (m : Nat) (z : GaussianInt) =>
    0 ≤ z.im ∧ z.im ≤ 2 * (m : Int) ∧ -(m : Int) ≤ z.re ∧ z.re ≤ m ∧
    -(z.im + 1) ≤ z.re ∧ z.re ≤ z.im + 1 ∧
    -(2 * (m : Int) - z.im + 1) ≤ z.re ∧ z.re ≤ 2 * (m : Int) - z.im + 1
  let I := fun (m : Nat) (z : GaussianInt) =>
    1 ≤ z.im ∧ z.im ≤ 2 * (m : Int) - 1 ∧
    -(z.im - 1) ≤ z.re ∧ z.re ≤ z.im - 1 ∧
    -(2 * (m : Int) - z.im - 1) ≤ z.re ∧ z.re ≤ 2 * (m : Int) - z.im - 1
  have boundary (m : Nat) (hm : 0 < m) (z : GaussianInt) :
      z ∈ BoundaryFootprintVertices (DiamondTile m) ↔ F m z ∧ ¬I m z := by
    rw [(P4194T1DiamondVertexIncidence m hm z).2]
    apply and_congr
    · exact ((P4194T1DiamondVertexIncidence m hm z).1).symm.trans
        (footprint m hm z)
    · rw [← not_forall]
      exact not_congr (P4194T1DiamondCellRows m z).2
  have boundaryTr (m : Nat) (hm : 0 < m) (u z : GaussianInt) :
      z ∈ BoundaryFootprintVertices (TileTranslation (DiamondTile m) u) ↔
        F m (z - u) ∧ ¬I m (z - u) := by
    rw [(TileTranslationFormulas (DiamondTile m) u).2.2.2.2.2.2.2.1]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [GaussianTranslation] using (boundary m hm w).mp hw
    · intro hz
      exact ⟨z - u, (boundary m hm (z - u)).mpr hz,
        by simp [GaussianTranslation]⟩
  have kp : 0 < k := by omega
  have np : 0 < k - 1 := by omega
  have coordP (z : GaussianInt) :
      (1 ≤ z.re ∧ z.re ≤ (k : Int) ∧ 0 ≤ z.im ∧
        z.im ≤ (k : Int) - 1 ∧ 0 ≤ z.re - z.im ∧ z.re - z.im ≤ 1) ↔
      ∃ j ≤ 2 * (k - 1), z = P5157T1StaircasePoint 1 false 1 j := by
    constructor
    · intro hz
      let j := (z.re + z.im - 1).toNat
      have hj : (j : Int) = z.re + z.im - 1 := Int.toNat_of_nonneg (by omega)
      refine ⟨j, by omega, ?_⟩
      ext <;> simp [P5157T1StaircasePoint] <;> omega
    · rintro ⟨j, hj, rfl⟩
      simp [P5157T1StaircasePoint]; omega
  have coordQ (z : GaussianInt) :
      (1 ≤ z.re ∧ z.re ≤ (k : Int) ∧ 1 - (k : Int) ≤ z.im ∧
        z.im ≤ 0 ∧ 0 ≤ z.re + z.im ∧ z.re + z.im ≤ 1) ↔
      ∃ j ≤ 2 * (k - 1), z = P5157T1StaircasePoint 1 false (-1) j := by
    constructor
    · intro hz
      let j := (z.re - z.im - 1).toNat
      have hj : (j : Int) = z.re - z.im - 1 := Int.toNat_of_nonneg (by omega)
      refine ⟨j, by omega, ?_⟩
      ext <;> simp [P5157T1StaircasePoint] <;> omega
    · rintro ⟨j, hj, rfl⟩
      simp [P5157T1StaircasePoint]; omega
  have coordR (z : GaussianInt) :
      (-(k : Int) ≤ z.re ∧ z.re ≤ -1 ∧ 0 ≤ z.im ∧
        z.im ≤ (k : Int) - 1 ∧ -1 ≤ z.re + z.im ∧ z.re + z.im ≤ 0) ↔
      ∃ j ≤ 2 * (k - 1), z =
        P5157T1StaircasePoint ⟨-(k : Int), (k : Int) - 1⟩ true (-1) j := by
    constructor
    · intro hz
      let j := (z.re - z.im + 2 * (k : Int) - 1).toNat
      have hj : (j : Int) = z.re - z.im + 2 * (k : Int) - 1 :=
        Int.toNat_of_nonneg (by omega)
      refine ⟨j, by omega, ?_⟩
      ext <;> simp [P5157T1StaircasePoint] <;> omega
    · rintro ⟨j, hj, rfl⟩
      simp [P5157T1StaircasePoint]; omega
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · ext z
    simp only [Set.mem_ofPred_eq]
    rw [← coordP]
    simp only [Set.mem_inter_iff, boundary k kp, boundaryTr (k - 1) np]
    dsimp [F, I]
    omega
  · ext z
    simp only [Set.mem_ofPred_eq]
    rw [← coordQ]
    simp only [Set.mem_inter_iff, boundaryTr k kp, boundaryTr (k - 1) np]
    dsimp [F, I]
    omega
  · ext z
    simp only [Set.mem_ofPred_eq]
    rw [← coordR]
    simp only [Set.mem_inter_iff, boundary k kp, boundaryTr (k - 1) np]
    dsimp [F, I]
    omega

end ApollonianSuperharmonic

end
