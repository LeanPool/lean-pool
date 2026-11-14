/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5260T1PlacementLedger
public import LeanPool.ApollonianSuperharmonic.TileReflectionFormulas
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondCellRows

-- [TABLET NODE: P5290T1ColumnReflection]

/-!
# P5290T1ColumnReflection

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5290T1ColumnReflection (k : Nat) (hk : 0 < k)
    (i : Fin 3) (hi : i ≠ 2) (hreg : 1 < k ∨ i = 1) :
    let j : Fin 3 := if i = 0 then 1 else 0
    let S := P5260T1PlacementLedger k i false
    let T := P5260T1PlacementLedger k j true
    let D := DiamondTile k
    let J := fun z : GaussianInt => (⟨z.re, 2 * (k : Int) - z.im⟩ : GaussianInt)
    let rows : List (ProtoTile × ProtoTile) :=
      [(D, D),
       (TileTranslation D S.2.1.1, TileTranslation D T.2.1.1),
       (TileTranslation D S.2.1.2, TileTranslation D T.2.1.2),
       (S.1.1, T.1.1), (S.1.2, T.1.2)]
    (∀ A B, (A, B) ∈ rows →
      FootprintVertices B = J '' FootprintVertices A ∧
      FootprintEdges B = (fun e : Finset GaussianInt => e.image J) '' FootprintEdges A) ∧
    J S.2.2.1 = T.2.2.1 ∧ J S.2.2.2 = T.2.2.2 := by
-- BODY
  classical
  let J := fun z : GaussianInt => (⟨z.re, 2 * (k : Int) - z.im⟩ : GaussianInt)
  let C := fun z : GaussianInt => (⟨z.re, 2 * (k : Int) - 1 - z.im⟩ : GaussianInt)
  have invol (z : GaussianInt) : C (C z) = z := by ext <;> simp [C]
  have image_mem (A : Finset GaussianInt) (z : GaussianInt) :
      z ∈ A.image C ↔ C z ∈ A := by
    constructor
    · rintro hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      simpa only [invol] using hw
    · intro hz
      exact Finset.mem_image.mpr ⟨C z, hz, invol z⟩
  have cell (m : Nat) (u z : GaussianInt) :
      z ∈ (TileTranslation (DiamondTile m) u).cells ↔ z - u ∈ DiamondCellDomain m := by
    change z ∈ (DiamondCellDomain m).image (GaussianTranslation u) ↔ _
    constructor
    · intro hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      simpa [GaussianTranslation] using hw
    · intro hz
      exact Finset.mem_image.mpr ⟨z - u, hz, by simp [GaussianTranslation]⟩
  have diamond_cells (m : Nat) (u : GaussianInt) :
      (TileTranslation (DiamondTile m)
        ⟨u.re, 2 * (k : Int) - 2 * (m : Int) - u.im⟩).cells =
        (TileTranslation (DiamondTile m) u).cells.image C := by
    ext z
    rw [image_mem, cell, cell]
    rw [(P4194T1DiamondCellRows m _).1, (P4194T1DiamondCellRows m _).1]
    simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, C]
    omega
  have ne (m : Nat) (hm : 0 < m) (u : GaussianInt) :
      (TileTranslation (DiamondTile m) u).cells.Nonempty := by
    refine ⟨u, (cell m u u).mpr ?_⟩
    rw [sub_self, (P4194T1DiamondCellRows m 0).1]
    norm_num
    omega
  have zeroTr (A : ProtoTile) : TileTranslation A 0 = A := by
    have hz : GaussianTranslation (0 : GaussianInt) = id := by
      funext z; simp [GaussianTranslation]
    cases A
    simp [TileTranslation, hz, GaussianTranslation]
  have observables (A B : ProtoTile) (hA : A.cells.Nonempty)
      (hc : B.cells = A.cells.image C) :
      FootprintVertices B = J '' FootprintVertices A ∧
      FootprintEdges B = (fun e : Finset GaussianInt => e.image J) '' FootprintEdges A := by
    let F := TileTranslation (TileReflection A) ⟨0, 2 * (k : Int)⟩
    have fc : F.cells = A.cells.image C := by
      rw [(TileTranslationFormulas (TileReflection A) _).1,
        (TileReflectionFormulas A).1, Finset.image_image]
      congr 1
      funext z
      ext <;> simp [GaussianTranslation, GaussianReflection, C]; ring
    have hB : B.cells.Nonempty := by rw [hc]; exact hA.image C
    have hF : F.cells.Nonempty := by rw [fc]; exact hA.image C
    have vc : FootprintVertices B = FootprintVertices F := by
      unfold FootprintVertices
      rw [ite_eq_left hB, ite_eq_left hF, hc, fc]
    have ec : FootprintEdges B = FootprintEdges F := by
      simp only [FootprintEdges, hc, fc]
    have fJ : (fun z => GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)) = J := by
      funext z
      ext <;> simp [GaussianTranslation, GaussianReflection, J]; ring
    constructor
    · rw [vc, (TileTranslationFormulas (TileReflection A) _).2.2.2.2.2.1,
        (TileReflectionFormulas A).2.2.2.2.2.1, Set.image_image]
      simp only [fJ]
    · rw [ec, (TileTranslationFormulas (TileReflection A) _).2.2.2.2.2.2.1,
        (TileReflectionFormulas A).2.2.2.2.2.2.1, Set.image_image]
      have fE : (fun e : Finset GaussianInt =>
          (e.image GaussianReflection).image (GaussianTranslation ⟨0, 2 * (k : Int)⟩)) =
          (fun e : Finset GaussianInt => e.image J) := by
        funext e
        rw [Finset.image_image]
        simp only [Function.comp_def, fJ]
      simp only [fE]
  have diamonds (m : Nat) (hm : 0 < m) (u v : GaussianInt)
      (hv : v = ⟨u.re, 2 * (k : Int) - 2 * (m : Int) - u.im⟩) :
      FootprintVertices (TileTranslation (DiamondTile m) v) =
          J '' FootprintVertices (TileTranslation (DiamondTile m) u) ∧
      FootprintEdges (TileTranslation (DiamondTile m) v) =
          (fun e : Finset GaussianInt => e.image J) ''
            FootprintEdges (TileTranslation (DiamondTile m) u) := by
    subst v
    exact observables _ _ (ne m hm u) (diamond_cells m u)
  have units (z w : GaussianInt) (hw : w = C z) :
      FootprintVertices (⟨{w}, w⟩ : ProtoTile) =
          J '' FootprintVertices (⟨{z}, z⟩ : ProtoTile) ∧
      FootprintEdges (⟨{w}, w⟩ : ProtoTile) =
          (fun e : Finset GaussianInt => e.image J) '' FootprintEdges (⟨{z}, z⟩ : ProtoTile) := by
    subst w
    exact observables _ _ ⟨z, by simp⟩ (by simp)
  dsimp only
  fin_cases i
  · have hbig : 1 < k := hreg.resolve_right (by decide)
    refine ⟨?_, ?_, ?_⟩
    · intro A B hrow
      simp only [P5260T1PlacementLedger, Bool.false_eq_true, ↓reduceIte,
        Matrix.cons_val_zero, Matrix.cons_val_one, P5124T1ParentModel,
        List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with h | h | h | h | h <;> cases h
      · simpa only [zeroTr] using diamonds k hk 0 0 (by ext <;> simp)
      · exact diamonds k hk ⟨-(k : Int), (k : Int) + 1⟩ ⟨-(k : Int), -(k : Int) - 1⟩
          (by ext <;> simp; omega)
      · exact diamonds k hk ⟨(k : Int) + 1, (k : Int)⟩ ⟨(k : Int) + 1, -(k : Int)⟩
          (by ext <;> simp )
      · exact units ⟨0, 2 * (k : Int)⟩ ⟨0, -1⟩ (by ext <;> simp [C])
      · exact diamonds (k - 1) (by omega) ⟨(k : Int), (k : Int) + 1⟩ ⟨(k : Int), 1 - (k : Int)⟩
          (by ext <;> simp; omega)
    · ext <;> simp [P5260T1PlacementLedger]
    · ext <;> simp [P5260T1PlacementLedger]
  · refine ⟨?_, ?_, ?_⟩
    · intro A B hrow
      simp only [P5260T1PlacementLedger, Bool.false_eq_true, ↓reduceIte,
        Matrix.cons_val_zero, Matrix.cons_val_one, P5124T1ParentModel,
        List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with h | h | h | h | h <;> cases h
      · simpa only [zeroTr] using diamonds k hk 0 0 (by ext <;> simp)
      · exact diamonds k hk ⟨-(k : Int), -(k : Int) - 1⟩ ⟨-(k : Int), (k : Int) + 1⟩
          (by ext <;> simp; omega)
      · exact diamonds k hk ⟨-(k : Int) - 1, (k : Int)⟩ ⟨-(k : Int) - 1, -(k : Int)⟩
          (by ext <;> simp )
      · exact units ⟨-(k : Int) - 1, (k : Int) - 1⟩ ⟨-(k : Int) - 1, (k : Int)⟩
          (by ext <;> simp [C]; omega)
      · exact units ⟨-(k : Int) - 1, (k : Int)⟩ ⟨-(k : Int) - 1, (k : Int) - 1⟩
          (by ext <;> simp [C]; omega)
    · ext <;> simp [P5260T1PlacementLedger]; omega
    · ext <;> simp [P5260T1PlacementLedger]; omega
  · exact (hi rfl).elim

end ApollonianSuperharmonic

end
