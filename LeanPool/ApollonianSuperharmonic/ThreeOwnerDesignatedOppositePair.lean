/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell
public import LeanPool.ApollonianSuperharmonic.NoCheckerboardCellVertex

-- [TABLET NODE: ThreeOwnerDesignatedOppositePair]

/-!
# ThreeOwnerDesignatedOppositePair

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem ThreeOwnerDesignatedOppositePair :
    ∀ (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (Z : ProtoTile), ∀ (x : GaussianInt), (LatticeTile X)
        → ((LatticeTile Y) → ((LatticeTile Z) → ((Disjoint X.cells Y.cells) → ((Disjoint Y.cells
        Z.cells) → ((Disjoint Z.cells X.cells) → ((NoCheckerboardCellVertex (X.cells : Set
        LatticeCell)) → ((NoCheckerboardCellVertex (Y.cells : Set LatticeCell)) →
        ((NoCheckerboardCellVertex (Z.cells : Set LatticeCell)) → ((∀ j : Fin 4,
      LatticeVertexIncidentCell x j ∈ X.cells ∨
        LatticeVertexIncidentCell x j ∈ Y.cells ∨
        LatticeVertexIncidentCell x j ∈ Z.cells) → ((∃ j : Fin 4, LatticeVertexIncidentCell x j ∈
            X.cells) → ((∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ Y.cells) → ((∃ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ Z.cells) → (∀ D : ProtoTile, D = X ∨ D = Y ∨ D = Z →
      ∃ U V R : ProtoTile,
        (D = U ∨ D = V) ∧
        ((U = X ∧ V = Y ∧ R = Z) ∨
         (U = Y ∧ V = X ∧ R = Z) ∨
         (U = X ∧ V = Z ∧ R = Y) ∨
         (U = Z ∧ V = X ∧ R = Y) ∨
         (U = Y ∧ V = Z ∧ R = X) ∨
         (U = Z ∧ V = Y ∧ R = X)) ∧
        (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells ∧
          LatticeVertexIncidentCell x (j + 2) ∈ V.cells) ∧
        x ∈ FootprintVertices U ∧ x ∈ FootprintVertices V ∧
        (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
            y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
          y ∈ FootprintVertices U ∨ y ∈ FootprintVertices V)))))))))))))) := by
  intro X Y Z x hX hY hZ hXY hYZ hZX hcheckerX hcheckerY hcheckerZ hexhaust hXocc hYocc hZocc
-- BODY
  have no_opposite (P Q R : Fin 4 → Prop)
      (hPQ : ∀ j, P j → ¬ Q j)
      (hPR : ∀ j, P j → ¬ R j)
      (hQR : ∀ j, Q j → ¬ R j)
      (hcheck : ¬ ((P 0 ∧ P 2 ∧ ¬ P 1 ∧ ¬ P 3) ∨
        (P 1 ∧ P 3 ∧ ¬ P 0 ∧ ¬ P 2)))
      (hQocc : ∃ j, Q j) (hRocc : ∃ j, R j) :
      ∀ j, P j → ¬ P (j + 2) := by
    have positions : ∀ j k : Fin 4,
        k = j ∨ k = j + 1 ∨ k = j + 2 ∨ k = j + 3 := by
      decide +kernel
    have check (j : Fin 4) :
        ¬ (P j ∧ P (j + 2) ∧ ¬ P (j + 1) ∧ ¬ P (j + 3)) := by
      intro hj
      fin_cases j <;> norm_num at hj
      · exact hcheck (Or.inl hj)
      · exact hcheck (Or.inr ⟨hj.1, hj.2.1, hj.2.2.2, hj.2.2.1⟩)
      · exact hcheck (Or.inl ⟨hj.2.1, hj.1, hj.2.2.2, hj.2.2.1⟩)
      · exact hcheck (Or.inr ⟨hj.2.1, hj.1, hj.2.2.1, hj.2.2.2⟩)
    intro j hj hj2
    -- The other owners must occupy the two remaining positions.
    have side (S : Fin 4 → Prop) (hPS : ∀ k, P k → ¬ S k)
        (hSocc : ∃ k, S k) : S (j + 1) ∨ S (j + 3) := by
      obtain ⟨k, hk⟩ := hSocc
      rcases positions j k with hk0 | hk1 | hk2 | hk3
      · exact (hPS j hj (hk0 ▸ hk)).elim
      · exact Or.inl (hk1 ▸ hk)
      · exact (hPS (j + 2) hj2 (hk2 ▸ hk)).elim
      · exact Or.inr (hk3 ▸ hk)
    rcases side Q hPQ hQocc with hQ1 | hQ3
    · rcases side R hPR hRocc with hR1 | hR3
      · exact hQR (j + 1) hQ1 hR1
      · exact check j ⟨hj, hj2,
          fun hp => hPQ (j + 1) hp hQ1,
          fun hp => hPR (j + 3) hp hR3⟩
    · rcases side R hPR hRocc with hR1 | hR3
      · exact check j ⟨hj, hj2,
          fun hp => hPR (j + 1) hp hR1,
          fun hp => hPQ (j + 3) hp hQ3⟩
      · exact hQR (j + 3) hQ3 hR3
  let owns (T : ProtoTile) (j : Fin 4) : Prop :=
    LatticeVertexIncidentCell x j ∈ T.cells
  have check (T : ProtoTile)
      (hc : NoCheckerboardCellVertex (T.cells : Set LatticeCell)) :
      ¬ ((owns T 0 ∧ owns T 2 ∧ ¬ owns T 1 ∧ ¬ owns T 3) ∨
        (owns T 1 ∧ owns T 3 ∧ ¬ owns T 0 ∧ ¬ owns T 2)) := by
    simpa [owns, LatticeVertexIncidentCell] using hc x
  have hXY' : ∀ j, owns X j → ¬ owns Y j :=
    fun _ hj => Finset.disjoint_left.mp hXY hj
  have hYX' : ∀ j, owns Y j → ¬ owns X j :=
    fun _ hj => Finset.disjoint_left.mp hXY.symm hj
  have hYZ' : ∀ j, owns Y j → ¬ owns Z j :=
    fun _ hj => Finset.disjoint_left.mp hYZ hj
  have hZY' : ∀ j, owns Z j → ¬ owns Y j :=
    fun _ hj => Finset.disjoint_left.mp hYZ.symm hj
  have hZX' : ∀ j, owns Z j → ¬ owns X j :=
    fun _ hj => Finset.disjoint_left.mp hZX hj
  have hXZ' : ∀ j, owns X j → ¬ owns Z j :=
    fun _ hj => Finset.disjoint_left.mp hZX.symm hj
  have hnoX := no_opposite (owns X) (owns Y) (owns Z)
    hXY' hXZ' hYZ' (check X hcheckerX) hYocc hZocc
  have hnoY := no_opposite (owns Y) (owns Z) (owns X)
    hYZ' hYX' hZX' (check Y hcheckerY) hZocc hXocc
  have hnoZ := no_opposite (owns Z) (owns X) (owns Y)
    hZX' hZY' hXY' (check Z hcheckerZ) hXocc hYocc
  have cell_vertex (T : ProtoTile) (c : LatticeCell) (hc : c ∈ T.cells)
      (y : GaussianInt)
      (hy : y = c ∨ y = c + 1 ∨ y = c + ⟨0, 1⟩ ∨
        y = c + 1 + ⟨0, 1⟩) : y ∈ FootprintVertices T := by
    have hne : T.cells.Nonempty := ⟨c, hc⟩
    simp only [FootprintVertices, ite_eq_left hne]
    exact ⟨c, hc, hy⟩
  have incident_vertex (T : ProtoTile) (k : Fin 4)
      (hk : LatticeVertexIncidentCell x k ∈ T.cells) :
      x ∈ FootprintVertices T := by
    apply cell_vertex T _ hk
    fin_cases k <;> simp [LatticeVertexIncidentCell, Zsqrtd.ext_iff]
  have star (U V : ProtoTile) (j : Fin 4)
      (hU : LatticeVertexIncidentCell x j ∈ U.cells)
      (hV : LatticeVertexIncidentCell x (j + 2) ∈ V.cells) :
      x ∈ FootprintVertices U ∧ x ∈ FootprintVertices V ∧
        (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
            y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
          y ∈ FootprintVertices U ∨ y ∈ FootprintVertices V) := by
    refine ⟨incident_vertex U j hU, incident_vertex V (j + 2) hV, ?_⟩
    intro y hy
    have corners :
        (y = LatticeVertexIncidentCell x j ∨
          y = LatticeVertexIncidentCell x j + 1 ∨
          y = LatticeVertexIncidentCell x j + ⟨0, 1⟩ ∨
          y = LatticeVertexIncidentCell x j + 1 + ⟨0, 1⟩) ∨
        (y = LatticeVertexIncidentCell x (j + 2) ∨
          y = LatticeVertexIncidentCell x (j + 2) + 1 ∨
          y = LatticeVertexIncidentCell x (j + 2) + ⟨0, 1⟩ ∨
          y = LatticeVertexIncidentCell x (j + 2) + 1 + ⟨0, 1⟩) := by
      fin_cases j <;> rcases hy with rfl | rfl | rfl | rfl | rfl <;>
        simp [LatticeVertexIncidentCell, Zsqrtd.ext_iff]
    rcases corners with hc | hc
    · exact Or.inl (cell_vertex U _ hU y hc)
    · exact Or.inr (cell_vertex V _ hV y hc)
  intro D hD
  rcases hD with hD | hD | hD
  · subst D
    obtain ⟨j, hj⟩ := hXocc
    rcases hexhaust (j + 2) with hx | hy | hz
    · exact (hnoX j hj hx).elim
    · refine ⟨X, Y, Z, Or.inl rfl, ?_, ⟨j, hj, hy⟩, star X Y j hj hy⟩
      exact Or.inl ⟨rfl, rfl, rfl⟩
    · refine ⟨X, Z, Y, Or.inl rfl, ?_, ⟨j, hj, hz⟩, star X Z j hj hz⟩
      exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  · subst D
    obtain ⟨j, hj⟩ := hYocc
    rcases hexhaust (j + 2) with hx | hy | hz
    · refine ⟨Y, X, Z, Or.inl rfl, ?_, ⟨j, hj, hx⟩, star Y X j hj hx⟩
      exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
    · exact (hnoY j hj hy).elim
    · refine ⟨Y, Z, X, Or.inl rfl, ?_, ⟨j, hj, hz⟩, star Y Z j hj hz⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))
  · subst D
    obtain ⟨j, hj⟩ := hZocc
    rcases hexhaust (j + 2) with hx | hy | hz
    · refine ⟨Z, X, Y, Or.inl rfl, ?_, ⟨j, hj, hx⟩, star Z X j hj hx⟩
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
    · refine ⟨Z, Y, X, Or.inl rfl, ?_, ⟨j, hj, hy⟩, star Z Y j hj hy⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))
    · exact (hnoZ j hj hz).elim

end ApollonianSuperharmonic

end
