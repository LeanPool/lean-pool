/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.P3102T2CommonEdgeSectorTransition

public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell
public import LeanPool.ApollonianSuperharmonic.LocalLatticeInterfaceSectors
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathPointTrichotomy
public import LeanPool.ApollonianSuperharmonic.TouchingTriple

-- [TABLET NODE: CoveredInterfaceOppositeIncidentCells]

/-!
# CoveredInterfaceOppositeIncidentCells

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace OppositeIncidentGeometry

private theorem owner_routing :
    (by
      classical
      exact
        ∀ (P : Fin 4 → Prop), ∀ (Q : Fin 4 → Prop), ∀ (R : Fin 4 → Prop), (∀ j, ¬ (P j ∧ Q j)) →
            ((∀ j, ¬ (P j ∧ R j)) → ((∀ j, ¬ (Q j ∧ R j)) → ((∀ j, P j ∨ Q j ∨ R j) → ((¬ ((P 0 ∧
            P 2 ∧ ¬ P 1 ∧ ¬ P 3) ∨
            (P 1 ∧ P 3 ∧ ¬ P 0 ∧ ¬ P 2))) → ((¬ ((Q 0 ∧ Q 2 ∧ ¬ Q 1 ∧ ¬ Q 3) ∨
            (Q 1 ∧ Q 3 ∧ ¬ Q 0 ∧ ¬ Q 2))) → ((∃ j, (P j ∧ Q (j + 1)) ∨ (Q j ∧ P (j + 1))) → ((∀
                j, ¬ (R j ∧ R (j + 1))) → (∃ j, P j ∧ Q (j + 2))))))))) ) := by
  classical
  intro P Q R hPQ hPR hQR hcover hcheckP hcheckQ htrans hnoR
  rcases htrans with ⟨j, hj⟩
  by_contra hop
  push Not at hop
  have add21 (r : Fin 4) : r + 2 + 1 = r + 3 := by fin_cases r <;> rfl
  have add11 (r : Fin 4) : r + 1 + 1 = r + 2 := by fin_cases r <;> rfl
  have add12 (r : Fin 4) : r + 1 + 2 = r + 3 := by fin_cases r <;> rfl
  have add13 (r : Fin 4) : r + 1 + 3 = r := by fin_cases r <;> rfl
  have add32 (r : Fin 4) : r + 3 + 2 = r + 1 := by fin_cases r <;> rfl
  have add22 (r : Fin 4) : r + 2 + 2 = r := by fin_cases r <;> rfl
  have checkP (r : Fin 4) :
      ¬ (P r ∧ P (r + 2) ∧ ¬ P (r + 1) ∧ ¬ P (r + 3)) := by
    intro hr
    fin_cases r <;> norm_num at hr
    · exact hcheckP (Or.inl hr)
    · exact hcheckP (Or.inr ⟨hr.1, hr.2.1, hr.2.2.2, hr.2.2.1⟩)
    · exact hcheckP (Or.inl ⟨hr.2.1, hr.1, hr.2.2.2, hr.2.2.1⟩)
    · exact hcheckP (Or.inr ⟨hr.2.1, hr.1, hr.2.2.1, hr.2.2.2⟩)
  have checkQ (r : Fin 4) :
      ¬ (Q r ∧ Q (r + 2) ∧ ¬ Q (r + 1) ∧ ¬ Q (r + 3)) := by
    intro hr
    fin_cases r <;> norm_num at hr
    · exact hcheckQ (Or.inl hr)
    · exact hcheckQ (Or.inr ⟨hr.1, hr.2.1, hr.2.2.2, hr.2.2.1⟩)
    · exact hcheckQ (Or.inl ⟨hr.2.1, hr.1, hr.2.2.2, hr.2.2.1⟩)
    · exact hcheckQ (Or.inr ⟨hr.2.1, hr.1, hr.2.2.1, hr.2.2.2⟩)
  rcases hj with hj | hj
  · have hnQ2 : ¬ Q (j + 2) := fun hq => hop j hj.1 hq
    have hnP3 : ¬ P (j + 3) := by
      intro hp
      exact hop (j + 3) hp (by simpa [add32] using hj.2)
    rcases hcover (j + 2) with hp2 | hq2 | hr2
    · rcases hcover (j + 3) with hp3 | hq3 | hr3
      · exact hnP3 hp3
      · exact checkP j ⟨hj.1, hp2, fun hp => hPQ (j + 1) ⟨hp, hj.2⟩,
          fun hp => hPQ (j + 3) ⟨hp, hq3⟩⟩
      · exact checkP j ⟨hj.1, hp2, fun hp => hPQ (j + 1) ⟨hp, hj.2⟩,
          fun hp => hPR (j + 3) ⟨hp, hr3⟩⟩
    · exact hnQ2 hq2
    · rcases hcover (j + 3) with hp3 | hq3 | hr3
      · exact hnP3 hp3
      · apply checkQ (j + 1)
        refine ⟨hj.2, ?_, ?_, ?_⟩
        · simpa [add12] using hq3
        · simpa [add11] using (fun hq => hQR (j + 2) ⟨hq, hr2⟩)
        · simpa [add13] using (fun hq => hPQ j ⟨hj.1, hq⟩)
      · exact hnoR (j + 2) ⟨hr2, by simpa [add21] using hr3⟩
  · have hnP2 : ¬ P (j + 2) := by
      intro hp
      exact hop (j + 2) hp (by simpa [add22] using hj.1)
    have hnQ3 : ¬ Q (j + 3) := fun hq => hop (j + 1) hj.2 (by
      simpa [add12] using hq)
    rcases hcover (j + 2) with hp2 | hq2 | hr2
    · exact hnP2 hp2
    · rcases hcover (j + 3) with hp3 | hq3 | hr3
      · apply checkQ j
        exact ⟨hj.1, hq2, fun hq => hPQ (j + 1) ⟨hj.2, hq⟩,
          fun hq => hPQ (j + 3) ⟨hp3, hq⟩⟩
      · exact hnQ3 hq3
      · apply checkQ j
        exact ⟨hj.1, hq2, fun hq => hPQ (j + 1) ⟨hj.2, hq⟩,
          fun hq => hQR (j + 3) ⟨hq, hr3⟩⟩
    · rcases hcover (j + 3) with hp3 | hq3 | hr3
      · apply checkP (j + 1)
        refine ⟨hj.2, ?_, ?_, ?_⟩
        · simpa [add12] using hp3
        · simpa [add11] using (fun hp => hPR (j + 2) ⟨hp, hr2⟩)
        · simpa [add13] using (fun hp => hPQ j ⟨hp, hj.1⟩)
      · exact hnQ3 hq3
      · exact hnoR (j + 2) ⟨hr2, by simpa [add21] using hr3⟩

private theorem hcheckP :
    (by
      classical
      exact
        ∀ (A : ProtoTile), (LatticeTile A) → (∀ (c : GaussianInt),
        let P : Fin 4 → Prop := fun j => LatticeVertexIncidentCell c j ∈ A.cells
        ¬ ((P 0 ∧ P 2 ∧ ¬ P 1 ∧ ¬ P 3) ∨ (P 1 ∧ P 3 ∧ ¬ P 0 ∧ ¬ P 2))) ) := by
  classical
  intro A hAlat c P
  simpa [P, LatticeVertexIncidentCell] using
    (LatticeTileGridStructure A hAlat).2.1 c

private theorem hcheckQ :
    (by
      classical
      exact
        ∀ (B : ProtoTile), (LatticeTile B) → (∀ (c : GaussianInt),
        let Q : Fin 4 → Prop := fun j => LatticeVertexIncidentCell c j ∈ B.cells
        ¬ ((Q 0 ∧ Q 2 ∧ ¬ Q 1 ∧ ¬ Q 3) ∨ (Q 1 ∧ Q 3 ∧ ¬ Q 0 ∧ ¬ Q 2))) ) := by
  classical
  intro B hBlat c Q
  simpa [Q, LatticeVertexIncidentCell] using
    (LatticeTileGridStructure B hBlat).2.1 c

private theorem hnoR :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), (∀ y ∈ FootprintVertices A, ∀ z ∈ FootprintVertices
            A, FourNeighborAdjacent y z → {y, z} ∈ FootprintEdges A) → ((∀ y ∈ FootprintVertices
            B, ∀ z ∈ FootprintVertices B, FourNeighborAdjacent y z → {y, z} ∈ FootprintEdges B) →
            (∀ (D : ProtoTile), ∀ (c : GaussianInt), (Disjoint A.cells D.cells) → ((Disjoint
            B.cells D.cells) → ((c ∈ FootprintVertices A ∩ FootprintVertices B ∩
            FootprintVertices D) → ((∀ (y : GaussianInt), y = c ∨ y = c + (1 : GaussianInt) ∨ y =
            c - (1 : GaussianInt) ∨ y = c + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨ y = c - (⟨(0 :
            ℤ), (1 : ℤ)⟩ : GaussianInt) → y ∈ FootprintVertices A ∨ y ∈ FootprintVertices B) → (
        let R : Fin 4 → Prop := fun j => LatticeVertexIncidentCell c j ∈ D.cells
        ∀ j, ¬ (R j ∧ R (j + 1)))))))) ) := by
  classical
  intro A B hAinduced hBinduced D c hAD hBD hc hstarc R
  let I : GaussianInt := ⟨0, 1⟩
  have horiz_unique (u v : GaussianInt)
      (h : ({u, u + 1} : Finset GaussianInt) = {v, v + 1}) : u = v := by
    have hu : u = v ∨ u = v + 1 := by
      have : u ∈ ({v, v + 1} : Finset GaussianInt) := by rw [← h]; simp
      simpa using this
    have hv : v = u ∨ v = u + 1 := by
      have : v ∈ ({u, u + 1} : Finset GaussianInt) := by rw [h]; simp
      simpa using this
    rcases hu with huv | huv
    · exact huv
    rcases hv with hvu | hvu
    · exact hvu.symm
    · have hre := congrArg Zsqrtd.re huv
      have hre' := congrArg Zsqrtd.re hvu
      norm_num at hre hre'
      omega
  have vert_unique (u v : GaussianInt)
      (h : ({u, u + I} : Finset GaussianInt) = {v, v + I}) : u = v := by
    have hu : u = v ∨ u = v + I := by
      have : u ∈ ({v, v + I} : Finset GaussianInt) := by rw [← h]; simp
      simpa using this
    have hv : v = u ∨ v = u + I := by
      have : v ∈ ({u, u + I} : Finset GaussianInt) := by rw [h]; simp
      simpa using this
    rcases hu with huv | huv
    · exact huv
    rcases hv with hvu | hvu
    · exact hvu.symm
    · have him := congrArg Zsqrtd.im huv
      have him' := congrArg Zsqrtd.im hvu
      simp [I] at him him'
      omega
  have horiz_ne_vert (u v : GaussianInt) :
      ({u, u + 1} : Finset GaussianInt) ≠ {v, v + I} := by
    intro h
    have hu : u = v ∨ u = v + I := by
      have : u ∈ ({v, v + I} : Finset GaussianInt) := by rw [← h]; simp
      simpa using this
    have hu1 : u + 1 = v ∨ u + 1 = v + I := by
      have : u + 1 ∈ ({v, v + I} : Finset GaussianInt) := by rw [← h]; simp
      simpa using this
    rcases hu with hu | hu <;> rcases hu1 with hu1 | hu1
    all_goals
      have hre := congrArg Zsqrtd.re hu
      have him := congrArg Zsqrtd.im hu
      have hre1 := congrArg Zsqrtd.re hu1
      have him1 := congrArg Zsqrtd.im hu1
      simp [I] at hre him hre1 him1
      omega
  have no_horizontal (U : ProtoTile) (z : GaussianInt)
      (hUD : Disjoint U.cells D.cells)
      (hU : ({z, z + 1} : Finset GaussianInt) ∈ FootprintEdges U)
      (hz : z ∈ D.cells) (hzI : z - I ∈ D.cells) : False := by
    have hD : ({z, z + 1} : Finset GaussianInt) ∈ FootprintEdges D :=
      ⟨z, hz, Or.inl rfl⟩
    have hcommon : ({z, z + 1} : Finset GaussianInt) ∈
        FootprintEdges U ∩ FootprintEdges D := ⟨hU, hD⟩
    rw [CellDisjointCommonEdgesBoundary U D hUD] at hcommon
    rcases hcommon.2 with ⟨w, ⟨hew, hw⟩ | ⟨hew, hw⟩⟩
    · have hwz : w = z := horiz_unique w z hew.symm
      subst w
      rcases hw with hw | hw
      · exact hw.2 hzI
      · exact hw.1 hz
    · exact (horiz_ne_vert z w hew).elim
  have no_vertical (U : ProtoTile) (z : GaussianInt)
      (hUD : Disjoint U.cells D.cells)
      (hU : ({z, z + I} : Finset GaussianInt) ∈ FootprintEdges U)
      (hz : z ∈ D.cells) (hz1 : z - 1 ∈ D.cells) : False := by
    have hD : ({z, z + I} : Finset GaussianInt) ∈ FootprintEdges D :=
      ⟨z, hz, Or.inr (Or.inl rfl)⟩
    have hcommon : ({z, z + I} : Finset GaussianInt) ∈
        FootprintEdges U ∩ FootprintEdges D := ⟨hU, hD⟩
    rw [CellDisjointCommonEdgesBoundary U D hUD] at hcommon
    rcases hcommon.2 with ⟨w, ⟨hew, hw⟩ | ⟨hew, hw⟩⟩
    · exact (horiz_ne_vert w z hew.symm).elim
    · have hwz : w = z := vert_unique w z hew.symm
      subst w
      rcases hw with hw | hw
      · exact hw.2 hz1
      · exact hw.1 hz
  intro r hr
  fin_cases r
  · have hD0 : c ∈ D.cells := by simpa [R, LatticeVertexIncidentCell] using hr.1
    have hD1 : c - 1 ∈ D.cells := by
      simpa [R, LatticeVertexIncidentCell] using hr.2
    rcases hstarc (c + I) (by right; right; right; left; rfl) with hyA | hyB
    · apply no_vertical A c hAD _ hD0 hD1
      exact hAinduced c hc.1.1 (c + I) hyA (by
        exact Or.inr (Or.inr (Or.inl rfl)))
    · apply no_vertical B c hBD _ hD0 hD1
      exact hBinduced c hc.1.2 (c + I) hyB (by
        exact Or.inr (Or.inr (Or.inl rfl)))
  · have hD1 : c - 1 ∈ D.cells := by
      simpa [R, LatticeVertexIncidentCell] using hr.1
    have hD2 : c - 1 - I ∈ D.cells := by
      simpa [R, LatticeVertexIncidentCell, I] using hr.2
    rcases hstarc (c - 1) (by right; right; left; rfl) with hyA | hyB
    · apply no_horizontal A (c - 1) hAD _ hD1 hD2
      simpa [I, Zsqrtd.ext_iff, Finset.pair_comm] using
        hAinduced c hc.1.1 (c - 1) hyA (Or.inr (Or.inl rfl))
    · apply no_horizontal B (c - 1) hBD _ hD1 hD2
      simpa [I, Zsqrtd.ext_iff, Finset.pair_comm] using
        hBinduced c hc.1.2 (c - 1) hyB (Or.inr (Or.inl rfl))
  · have hD2 : c - 1 - I ∈ D.cells := by
      simpa [R, LatticeVertexIncidentCell, I] using hr.1
    have hD3 : c - I ∈ D.cells := by
      simpa [R, LatticeVertexIncidentCell, I] using hr.2
    rcases hstarc (c - I) (by right; right; right; right; rfl) with hyA | hyB
    · apply no_vertical A (c - I) hAD _ hD3 _
      · simpa [I, Zsqrtd.ext_iff, Finset.pair_comm] using
          hAinduced c hc.1.1 (c - I) hyA (Or.inr (Or.inr (Or.inr rfl)))
      · simpa [I, Zsqrtd.ext_iff, sub_eq_add_neg, add_comm,
          add_left_comm, add_assoc] using hD2
    · apply no_vertical B (c - I) hBD _ hD3 _
      · simpa [I, Zsqrtd.ext_iff, Finset.pair_comm] using
          hBinduced c hc.1.2 (c - I) hyB (Or.inr (Or.inr (Or.inr rfl)))
      · simpa [I, Zsqrtd.ext_iff, sub_eq_add_neg, add_comm,
          add_left_comm, add_assoc] using hD2
  · have hD3 : c - I ∈ D.cells := by
      simpa [R, LatticeVertexIncidentCell, I] using hr.1
    have hD0 : c ∈ D.cells := by
      simpa [R, LatticeVertexIncidentCell] using hr.2
    rcases hstarc (c + 1) (by right; left; rfl) with hyA | hyB
    · apply no_horizontal A c hAD _ hD0 hD3
      exact hAinduced c hc.1.1 (c + 1) hyA (Or.inl rfl)
    · apply no_horizontal B c hBD _ hD0 hD3
      exact hBinduced c hc.1.2 (c + 1) hyB (Or.inl rfl)

end OppositeIncidentGeometry

theorem CoveredInterfaceOppositeIncidentCells
    (A B Aend Bend : ProtoTile) (a b x : GaussianInt)
    (hAlat : LatticeTile A) (hBlat : LatticeTile B)
    (hAendlat : LatticeTile Aend) (hBendlat : LatticeTile Bend)
    (hAB : Disjoint A.cells B.cells)
    (hAAend : Disjoint A.cells Aend.cells)
    (hBAend : Disjoint B.cells Aend.cells)
    (hABend : Disjoint A.cells Bend.cells)
    (hBBend : Disjoint B.cells Bend.cells)
    (hpath : SimpleGridPathBetween
      (FootprintVertices A ∩ FootprintVertices B)
      (FootprintEdges A ∩ FootprintEdges B) a b)
    (hedge : ∃ e : Finset GaussianInt,
      x ∈ e ∧ e ∈ FootprintEdges A ∩ FootprintEdges B)
    (hAtriple : TouchingTriple A B Aend)
    (hBtriple : TouchingTriple A B Bend)
    (ha : a ∈ FootprintVertices A ∩ FootprintVertices B ∩
      FootprintVertices Aend)
    (hb : b ∈ FootprintVertices A ∩ FootprintVertices B ∩
      FootprintVertices Bend)
    (hAinduced : ∀ y, y ∈ FootprintVertices A → ∀ z,
      z ∈ FootprintVertices A →
      FourNeighborAdjacent y z →
      ({y, z} : Finset GaussianInt) ∈ FootprintEdges A)
    (hBinduced : ∀ y, y ∈ FootprintVertices B → ∀ z,
      z ∈ FootprintVertices B →
      FourNeighborAdjacent y z →
      ({y, z} : Finset GaussianInt) ∈ FootprintEdges B)
    (hstar : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
      y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
      y ∈ FootprintVertices A ∨ y ∈ FootprintVertices B) :
    ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ A.cells ∧
      LatticeVertexIncidentCell x (j + 2) ∈ B.cells := by
-- BODY
  classical
  have owner_routing (P Q R : Fin 4 → Prop)
      (hPQ : ∀ j, ¬ (P j ∧ Q j))
      (hPR : ∀ j, ¬ (P j ∧ R j))
      (hQR : ∀ j, ¬ (Q j ∧ R j))
      (hcover : ∀ j, P j ∨ Q j ∨ R j)
      (hcheckP : ¬ ((P 0 ∧ P 2 ∧ ¬ P 1 ∧ ¬ P 3) ∨
        (P 1 ∧ P 3 ∧ ¬ P 0 ∧ ¬ P 2)))
      (hcheckQ : ¬ ((Q 0 ∧ Q 2 ∧ ¬ Q 1 ∧ ¬ Q 3) ∨
        (Q 1 ∧ Q 3 ∧ ¬ Q 0 ∧ ¬ Q 2)))
      (htrans : ∃ j, (P j ∧ Q (j + 1)) ∨ (Q j ∧ P (j + 1)))
      (hnoR : ∀ j, ¬ (R j ∧ R (j + 1))) :
      ∃ j, P j ∧ Q (j + 2) := OppositeIncidentGeometry.owner_routing P Q R hPQ hPR hQR hcover
          hcheckP hcheckQ htrans hnoR
  have endpoint (D : ProtoTile) (c : GaussianInt)
      (hDlat : LatticeTile D)
      (hAD : Disjoint A.cells D.cells) (hBD : Disjoint B.cells D.cells)
      (htriple : TouchingTriple A B D)
      (hc : c ∈ FootprintVertices A ∩ FootprintVertices B ∩
        FootprintVertices D)
      (hedgec : ∃ e : Finset GaussianInt,
        c ∈ e ∧ e ∈ FootprintEdges A ∩ FootprintEdges B)
      (hstarc : ∀ y, y = c ∨ y = c + 1 ∨ y = c - 1 ∨
        y = c + ⟨0, 1⟩ ∨ y = c - ⟨0, 1⟩ →
        y ∈ FootprintVertices A ∨ y ∈ FootprintVertices B) :
      ∃ j : Fin 4, LatticeVertexIncidentCell c j ∈ A.cells ∧
        LatticeVertexIncidentCell c (j + 2) ∈ B.cells := by
    let P : Fin 4 → Prop := fun j => LatticeVertexIncidentCell c j ∈ A.cells
    let Q : Fin 4 → Prop := fun j => LatticeVertexIncidentCell c j ∈ B.cells
    let R : Fin 4 → Prop := fun j => LatticeVertexIncidentCell c j ∈ D.cells
    have hdAB := Finset.disjoint_left.mp hAB
    have hdAD := Finset.disjoint_left.mp hAD
    have hdBD := Finset.disjoint_left.mp hBD
    have hPQ : ∀ j, ¬ (P j ∧ Q j) := fun j h => hdAB h.1 h.2
    have hPR : ∀ j, ¬ (P j ∧ R j) := fun j h => hdAD h.1 h.2
    have hQR : ∀ j, ¬ (Q j ∧ R j) := fun j h => hdBD h.1 h.2
    have hlocal := LocalLatticeInterfaceSectors.1 A B D c
      hAlat hBlat hDlat htriple hc
    have hcover : ∀ j, P j ∨ Q j ∨ R j := by
      simpa [P, Q, R] using hlocal.1
    have hcheckP : ¬ ((P 0 ∧ P 2 ∧ ¬ P 1 ∧ ¬ P 3) ∨
        (P 1 ∧ P 3 ∧ ¬ P 0 ∧ ¬ P 2)) := OppositeIncidentGeometry.hcheckP A hAlat c
    have hcheckQ : ¬ ((Q 0 ∧ Q 2 ∧ ¬ Q 1 ∧ ¬ Q 3) ∨
        (Q 1 ∧ Q 3 ∧ ¬ Q 0 ∧ ¬ Q 2)) := OppositeIncidentGeometry.hcheckQ B hBlat c
    rcases hedgec with ⟨e, hce, he⟩
    have htrans : ∃ j, (P j ∧ Q (j + 1)) ∨ (Q j ∧ P (j + 1)) := by
      obtain ⟨j, _, hj⟩ := P3102T2CommonEdgeSectorTransition A B c e hAB hce he
      exact ⟨j, hj⟩
    have hnoR : ∀ j, ¬ (R j ∧ R (j + 1)) := OppositeIncidentGeometry.hnoR A B hAinduced hBinduced
        D c hAD hBD hc hstarc
    simpa [P, Q] using
      owner_routing P Q R hPQ hPR hQR hcover hcheckP hcheckQ htrans hnoR
  rcases SimpleGridPathPointTrichotomy
      (FootprintVertices A ∩ FootprintVertices B)
      (FootprintEdges A ∩ FootprintEdges B) a b x hpath hedge with
    hxa | hxb | hinterior
  · subst x
    exact endpoint Aend a hAendlat hAAend hBAend hAtriple ha hedge hstar
  · subst x
    exact endpoint Bend b hBendlat hABend hBBend hBtriple hb hedge hstar
  · exact (LocalLatticeInterfaceSectors.2 A B x hAlat hBlat hAB hinterior).2

end ApollonianSuperharmonic

end
