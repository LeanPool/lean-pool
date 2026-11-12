/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5110T1SquareInterface
public import LeanPool.ApollonianSuperharmonic.TouchingTriple

-- [TABLET NODE: P5110T1TranslationTriples]

/-!
# P5110T1TranslationTriples

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5110T1TranslationTriples (r s : Nat) (hr : 0 < r) (hs : 0 < s) :
    let q := r + s
    let A := FordTile q
    TouchingTriple A (TileTranslation A ⟨(q : Int), (r : Int)⟩)
        (TileTranslation A ⟨(q : Int), -(s : Int)⟩) ∧
    TouchingTriple A (TileTranslation A ⟨-(q : Int), (s : Int)⟩)
        (TileTranslation A ⟨0, (q : Int)⟩) ∧
    TouchingTriple A (TileTranslation A ⟨0, -(q : Int)⟩)
        (TileTranslation A ⟨-(q : Int), -(r : Int)⟩) := by
-- BODY
  have qpos : 0 < r + s := by omega
  have zero_shift : TileTranslation (FordTile (r + s)) 0 = FordTile (r + s) := by
    have h : GaussianTranslation 0 = id := by funext z; simp [GaussianTranslation]
    simp [TileTranslation, h]
  have swap (A B : ProtoTile) (h : TileTouching A B) : TileTouching B A := by
    rcases h with h | h | h
    · exact Or.inl ⟨h.2.1, h.1, h.2.2.1.symm, by simpa [Set.inter_comm] using h.2.2.2⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rcases P5110T1SquareInterface (r + s) (r + s) qpos qpos
        0 ⟨((r + s : Nat) : Int), (r : Int)⟩ true (by simp)
        (by dsimp; omega) with ⟨na, nb, dab, vab, _, _, _, _, pab⟩
    rcases P5110T1SquareInterface (r + s) (r + s) qpos qpos
        ⟨((r + s : Nat) : Int), -(s : Int)⟩
        ⟨((r + s : Nat) : Int), (r : Int)⟩ false (by dsimp; omega)
        (by dsimp; omega) with ⟨nc, nb', dcb, vcb, _, _, _, _, pcb⟩
    rcases P5110T1SquareInterface (r + s) (r + s) qpos qpos
        0 ⟨((r + s : Nat) : Int), -(s : Int)⟩ true (by simp)
        (by dsimp; omega) with ⟨_, _, dac, vac, _, _, _, _, pac⟩
    rw [zero_shift] at na dab vab pab dac vac pac
    refine ⟨Or.inl ⟨na, nb, dab, pab⟩,
      swap _ _ (Or.inl ⟨nc, nb', dcb, pcb⟩),
      swap _ _ (Or.inl ⟨na, nc, dac, pac⟩),
      ⟨((r + s : Nat) : Int), (r : Int)⟩, ?_, ?_⟩
    · have hab : (⟨((r + s : Nat) : Int), (r : Int)⟩ : GaussianInt) ∈
          BoundaryFootprintVertices (FordTile (r + s)) ∩
            BoundaryFootprintVertices (TileTranslation (FordTile (r + s))
              ⟨((r + s : Nat) : Int), (r : Int)⟩) := by
        rw [vab]; dsimp; omega
      have hac : (⟨((r + s : Nat) : Int), (r : Int)⟩ : GaussianInt) ∈
          BoundaryFootprintVertices (FordTile (r + s)) ∩
            BoundaryFootprintVertices (TileTranslation (FordTile (r + s))
              ⟨((r + s : Nat) : Int), -(s : Int)⟩) := by
        rw [vac]; dsimp; omega
      exact ⟨hab.1, hab.2, hac.2⟩
    · intro z hz
      have hab : z ∈ _ := show z ∈ BoundaryFootprintVertices (FordTile (r + s)) ∩
          BoundaryFootprintVertices (TileTranslation (FordTile (r + s))
            ⟨((r + s : Nat) : Int), (r : Int)⟩) from ⟨hz.1, hz.2.1⟩
      have hac : z ∈ _ := show z ∈ BoundaryFootprintVertices (FordTile (r + s)) ∩
          BoundaryFootprintVertices (TileTranslation (FordTile (r + s))
            ⟨((r + s : Nat) : Int), -(s : Int)⟩) from ⟨hz.1, hz.2.2⟩
      rw [vab] at hab
      rw [vac] at hac
      dsimp at hab hac
      apply Zsqrtd.ext <;> dsimp <;> omega
  · rcases P5110T1SquareInterface (r + s) (r + s) qpos qpos
        ⟨-((r + s : Nat) : Int), (s : Int)⟩ 0 true (by dsimp; omega)
        (by dsimp; omega) with ⟨nb, na, dba, vba, _, _, _, _, pba⟩
    rcases P5110T1SquareInterface (r + s) (r + s) qpos qpos
        ⟨-((r + s : Nat) : Int), (s : Int)⟩
        ⟨0, ((r + s : Nat) : Int)⟩ true (by dsimp; omega)
        (by dsimp; omega) with ⟨_, nc, dbc, vbc, _, _, _, _, pbc⟩
    rcases P5110T1SquareInterface (r + s) (r + s) qpos qpos
        0 ⟨0, ((r + s : Nat) : Int)⟩ false (by simp)
        (by dsimp; omega) with ⟨_, _, dac, vac, _, _, _, _, pac⟩
    rw [zero_shift] at na dba vba pba dac vac pac
    refine ⟨swap _ _ (Or.inl ⟨nb, na, dba, pba⟩),
      Or.inl ⟨nb, nc, dbc, pbc⟩, swap _ _ (Or.inl ⟨na, nc, dac, pac⟩),
      ⟨0, ((r + s : Nat) : Int)⟩, ?_, ?_⟩
    · have hba : (⟨0, ((r + s : Nat) : Int)⟩ : GaussianInt) ∈
          BoundaryFootprintVertices (TileTranslation (FordTile (r + s))
            ⟨-((r + s : Nat) : Int), (s : Int)⟩) ∩
          BoundaryFootprintVertices (FordTile (r + s)) := by
        rw [vba]; dsimp; omega
      have hbc : (⟨0, ((r + s : Nat) : Int)⟩ : GaussianInt) ∈
          BoundaryFootprintVertices (TileTranslation (FordTile (r + s))
            ⟨-((r + s : Nat) : Int), (s : Int)⟩) ∩
          BoundaryFootprintVertices (TileTranslation (FordTile (r + s))
            ⟨0, ((r + s : Nat) : Int)⟩) := by
        rw [vbc]; dsimp; omega
      exact ⟨hba.2, hba.1, hbc.2⟩
    · intro z hz
      have hba : z ∈ _ := show z ∈ BoundaryFootprintVertices
          (TileTranslation (FordTile (r + s)) ⟨-((r + s : Nat) : Int), (s : Int)⟩) ∩
          BoundaryFootprintVertices (FordTile (r + s)) from ⟨hz.2.1, hz.1⟩
      have hbc : z ∈ _ := show z ∈ BoundaryFootprintVertices
          (TileTranslation (FordTile (r + s)) ⟨-((r + s : Nat) : Int), (s : Int)⟩) ∩
          BoundaryFootprintVertices (TileTranslation (FordTile (r + s))
            ⟨0, ((r + s : Nat) : Int)⟩) from ⟨hz.2.1, hz.2.2⟩
      rw [vba] at hba
      rw [vbc] at hbc
      dsimp at hba hbc
      apply Zsqrtd.ext <;> dsimp <;> omega
  · rcases P5110T1SquareInterface (r + s) (r + s) qpos qpos
        ⟨0, -((r + s : Nat) : Int)⟩ 0 false (by dsimp; omega)
        (by dsimp; omega) with ⟨nb, na, dba, vba, _, _, _, _, pba⟩
    rcases P5110T1SquareInterface (r + s) (r + s) qpos qpos
        ⟨-((r + s : Nat) : Int), -(r : Int)⟩
        ⟨0, -((r + s : Nat) : Int)⟩ true (by dsimp; omega)
        (by dsimp; omega) with ⟨nc, _, dcb, vcb, _, _, _, _, pcb⟩
    rcases P5110T1SquareInterface (r + s) (r + s) qpos qpos
        ⟨-((r + s : Nat) : Int), -(r : Int)⟩ 0 true (by dsimp; omega)
        (by dsimp; omega) with ⟨_, _, dca, vca, _, _, _, _, pca⟩
    rw [zero_shift] at na dba vba pba dca vca pca
    refine ⟨swap _ _ (Or.inl ⟨nb, na, dba, pba⟩),
      swap _ _ (Or.inl ⟨nc, nb, dcb, pcb⟩), Or.inl ⟨nc, na, dca, pca⟩,
      0, ?_, ?_⟩
    · have hcb : (0 : GaussianInt) ∈ BoundaryFootprintVertices
          (TileTranslation (FordTile (r + s)) ⟨-((r + s : Nat) : Int), -(r : Int)⟩) ∩
          BoundaryFootprintVertices (TileTranslation (FordTile (r + s))
            ⟨0, -((r + s : Nat) : Int)⟩) := by
        rw [vcb]; dsimp; omega
      have hca : (0 : GaussianInt) ∈ BoundaryFootprintVertices
          (TileTranslation (FordTile (r + s)) ⟨-((r + s : Nat) : Int), -(r : Int)⟩) ∩
          BoundaryFootprintVertices (FordTile (r + s)) := by
        rw [vca]; dsimp; omega
      exact ⟨hca.2, hcb.2, hca.1⟩
    · intro z hz
      have hcb : z ∈ _ := show z ∈ BoundaryFootprintVertices
          (TileTranslation (FordTile (r + s)) ⟨-((r + s : Nat) : Int), -(r : Int)⟩) ∩
          BoundaryFootprintVertices (TileTranslation (FordTile (r + s))
            ⟨0, -((r + s : Nat) : Int)⟩) from ⟨hz.2.2, hz.2.1⟩
      have hca : z ∈ _ := show z ∈ BoundaryFootprintVertices
          (TileTranslation (FordTile (r + s)) ⟨-((r + s : Nat) : Int), -(r : Int)⟩) ∩
          BoundaryFootprintVertices (FordTile (r + s)) from ⟨hz.2.2, hz.1⟩
      rw [vcb] at hcb
      rw [vca] at hca
      dsimp at hcb hca
      apply Zsqrtd.ext <;> dsimp <;> omega

end ApollonianSuperharmonic

end
