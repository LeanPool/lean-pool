/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5124T1ParentModel
public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondCellRows
public import LeanPool.ApollonianSuperharmonic.DiamondRecursiveQuadruple

-- [TABLET NODE: P5300T1CenteredCellGeometry]

/-!
# P5300T1CenteredCellGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5300T1CenteredCellGeometry (K : DiamondParameter) :
    let k := K.1
    let C : GaussianInt := ⟨0, 2 * (k : Int)⟩
    let c : Fin 3 → GaussianInt :=
      ![⟨1, 4 * (k : Int) + 1⟩,
        ⟨-2 * (k : Int) - 1, 2 * (k : Int) - 1⟩,
        ⟨2 * (k : Int), 0⟩]
    (DiamondTile k).cells.Nonempty ∧
    (DiamondTile k).cells.image (fun z => C - z - 1 - ⟨0, 1⟩) =
      (DiamondTile k).cells ∧
    ∀ t : Fin 3, 0 < ((DiamondRecursiveQuadruple K) t.succ).1 →
      let P := P5124T1ParentModel k t true
      P.cells.Nonempty ∧
      P.cells.image (fun z => c t - z - 1 - ⟨0, 1⟩) = P.cells := by
-- BODY
  classical
  have diamond (m : Nat) :
      (DiamondTile m).cells.image
        (fun z => (⟨0, 2 * (m : Int)⟩ : GaussianInt) - z - 1 - ⟨0, 1⟩) =
          (DiamondTile m).cells := by
    have mem (z : GaussianInt) : z ∈ DiamondCellDomain m ↔
        (⟨0, 2 * (m : Int)⟩ : GaussianInt) - z - 1 - ⟨0, 1⟩ ∈
          DiamondCellDomain m := by
      rw [(P4194T1DiamondCellRows m z).1,
        (P4194T1DiamondCellRows m _).1]
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one]
      omega
    change (DiamondCellDomain m).image _ = DiamondCellDomain m
    ext z
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mem x).mp hx
    · intro hz
      refine ⟨(⟨0, 2 * (m : Int)⟩ : GaussianInt) - z - 1 - ⟨0, 1⟩,
        (mem z).mp hz, ?_⟩
      abel
  have nonempty (m : Nat) (hm : 0 < m) : (DiamondTile m).cells.Nonempty := by
    refine ⟨0, (P4194T1DiamondCellRows m 0).1.mpr ?_⟩
    norm_num
    omega
  dsimp only
  refine ⟨nonempty K.1 K.2, diamond K.1, ?_⟩
  intro t hp
  fin_cases t
  · constructor
    · simp [P5124T1ParentModel]
    · simp [P5124T1ParentModel, Zsqrtd.ext_iff]
      ring
  · constructor
    · simp [P5124T1ParentModel]
    · simp [P5124T1ParentModel, Zsqrtd.ext_iff]
      constructor <;> ring
  · have hm : 0 < K.1 - 1 := by
      simp [DiamondRecursiveQuadruple] at hp
      by_contra hn
      have hz : K.1 - 1 = 0 := by omega
      simp [hz] at hp
    constructor
    · exact (nonempty (K.1 - 1) hm).image _
    · change ((DiamondTile (K.1 - 1)).cells.image
        (GaussianTranslation ⟨(K.1 : Int), 1 - (K.1 : Int)⟩)).image _ = _
      rw [Finset.image_image]
      have hfun : (fun z : GaussianInt =>
          (⟨2 * (K.1 : Int), 0⟩ : GaussianInt) -
            GaussianTranslation ⟨(K.1 : Int), 1 - (K.1 : Int)⟩ z - 1 - ⟨0, 1⟩) =
          GaussianTranslation ⟨(K.1 : Int), 1 - (K.1 : Int)⟩ ∘
            (fun z : GaussianInt =>
              (⟨0, 2 * ((K.1 - 1 : Nat) : Int)⟩ : GaussianInt) - z - 1 - ⟨0, 1⟩) := by
        funext z
        ext <;> simp [GaussianTranslation,
          Nat.cast_sub K.2] <;> ring
      change (DiamondTile (K.1 - 1)).cells.image
        (fun z : GaussianInt =>
          (⟨2 * (K.1 : Int), 0⟩ : GaussianInt) -
            GaussianTranslation ⟨(K.1 : Int), 1 - (K.1 : Int)⟩ z - 1 - ⟨0, 1⟩) = _
      rw [hfun, ← Finset.image_image, diamond]
      rfl

end ApollonianSuperharmonic

end
