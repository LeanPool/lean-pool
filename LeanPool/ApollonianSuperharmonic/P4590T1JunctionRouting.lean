/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4590T1MixedCompanionMarks
public import LeanPool.ApollonianSuperharmonic.P4590T1PositivePrototileDisk
public import LeanPool.ApollonianSuperharmonic.P4590T1OppositeCellsStar
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralInteriorWebRow
public import LeanPool.ApollonianSuperharmonic.LocalLatticeInterfaceSectors
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure

-- [TABLET NODE: P4590T1JunctionRouting]

/-!
# P4590T1JunctionRouting

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4590T1JunctionRouting
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q) (C : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (hT : LatticeTile T) (x : GaussianInt)
    (hx : x ∈ FootprintVertices T) (hxb : x ∉ BoundaryFootprintVertices T)
    (hjunction :
      (x ∈ FootprintVertices (cert.Q 1 true) ∩
        FootprintVertices (cert.S 2 false) ∩ FootprintVertices (cert.P 1 true)) ∨
      (x ∈ FootprintVertices (cert.Q 2 true) ∩
        FootprintVertices (cert.S 1 false) ∩ FootprintVertices (cert.P 1 false)) ∨
      (x ∈ FootprintVertices (cert.Q 1 true) ∩
        FootprintVertices (cert.P 1 true) ∩ FootprintVertices (cert.P 2 false)) ∨
      (x ∈ FootprintVertices (cert.S 1 false) ∩
        FootprintVertices (cert.P 1 false) ∩ FootprintVertices (cert.P 2 true))) :
    BandOrderedGeneralInteriorWebRow cert x true := by
-- BODY
  have hq2 : 0 < (q 2).1 := by have h := cfg.secondLarge; omega
  have hq3 : 0 < (q 3).1 := by
    have h := (ProperBandCurvatureStructure q cfg.proper).2.1 (2 : Fin 3)
    have hn := cfg.noLine 3
    change 0 ≤ (q 3).1 at h
    omega
  have hQ2 := P4590T1PositivePrototileDisk _ _ (cert.plus_occurrence 1 true).1
    (by change 0 < (cfg.firstPredecessor 2).1; rw [cfg.firstParentTwo]; exact hq2)
  have hQ3 := P4590T1PositivePrototileDisk _ _ (cert.plus_occurrence 2 true).1
    (by change 0 < (cfg.firstPredecessor 3).1; rw [cfg.firstParentThree]; exact hq3)
  have hS2 := P4590T1PositivePrototileDisk _ _ (cert.minus_occurrence 1 false).1
    (by change 0 < (cfg.firstPredecessor 2).1; rw [cfg.firstParentTwo]; exact hq2)
  have hS3 := P4590T1PositivePrototileDisk _ _ (cert.minus_occurrence 2 false).1
    (by change 0 < (cfg.firstPredecessor 3).1; rw [cfg.firstParentThree]; exact hq3)
  have ne (W : ProtoTile) (hW : LatticeTile W) : W.cells.Nonempty :=
    (LatticeTileGridStructure W hW).1.1
  have touchD (U V : ProtoTile) (hU : LatticeTile U) (hV : LatticeTile V)
      (ht : TileTouching U V) : Disjoint U.cells V.cells := by
    rcases ht with ht | ht | ht
    · exact ht.2.2.1
    · have hh := ne U hU; rw [ht.1] at hh; simp at hh
    · have hh := ne V hV; rw [ht.1] at hh; simp at hh
  have third_missing (U V W : ProtoTile)
      (hW : LatticeTile W) (hw : x ∈ FootprintVertices W)
      (hdU : Disjoint W.cells U.cells) (hdV : Disjoint W.cells V.cells) :
      ¬ (∀ z, z = x ∨ z = x - 1 ∨ z = x - ⟨0, 1⟩ ∨
        z = x - 1 - ⟨0, 1⟩ → z ∈ U.cells ∨ z ∈ V.cells) := by
    intro hall
    have hne := ne W hW
    simp only [FootprintVertices, hne, ite_true, Set.mem_ofPred_eq] at hw
    obtain ⟨z, hz, hcorner⟩ := hw
    have hbase : z = x ∨ z = x - 1 ∨ z = x - ⟨0, 1⟩ ∨
        z = x - 1 - ⟨0, 1⟩ := by
      rcases hcorner with h | h | h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inl (by rw [h]; simp))
      · exact Or.inr (Or.inr (Or.inl (by rw [h]; simp)))
      · exact Or.inr (Or.inr (Or.inr (by rw [h]; simp [sub_sub])))
    rcases hall z hbase with hu | hv
    · exact Finset.disjoint_left.mp hdU hz hu
    · exact Finset.disjoint_left.mp hdV hz hv
  have liftStar (U V U' V' : ProtoTile)
      (hu : FootprintVertices U ⊆ FootprintVertices U')
      (hv : FootprintVertices V ⊆ FootprintVertices V')
      (hstar : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
        y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices U ∨ y ∈ FootprintVertices V) :
      ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
        y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices U' ∨ y ∈ FootprintVertices V' := by
    intro y hy
    exact (hstar y hy).imp (fun h => hu h) (fun h => hv h)
  have swapStar (U V : ProtoTile)
      (hstar : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
        y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices U ∨ y ∈ FootprintVertices V) :
      ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
        y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices V ∨ y ∈ FootprintVertices U :=
    fun y hy => (hstar y hy).symm
  obtain ⟨m12, m13, m21, m31, m23, m32⟩ :=
    P4590T1MixedCompanionMarks q cfg C T cert hT x hx hxb
  have subQ2 := (cert.plus_occurrence 1 true).2.1
  have subQ3 := (cert.plus_occurrence 2 true).2.1
  have subS2 := (cert.minus_occurrence 1 false).2.1
  have subS3 := (cert.minus_occurrence 2 false).2.1
  rcases hjunction with h | h | h | h
  · have hA := subQ2 h.1.1
    have hB := subS3 h.1.2
    have hC := h.2
    have sec := LocalLatticeInterfaceSectors.1 _ _ _ x hQ2 hS3
      (cert.parent_lattice 1 true) cert.double_first h
    rcases sec.2.2.2.2 with opp | opp | opp
    · exact .largestPositive h.1.1 h.1.2
        (P4590T1OppositeCellsStar _ _ x opp) (by simp [hC])
    · apply BandOrderedGeneralInteriorWebRow.rightPositive h.1.1 hC
        (P4590T1OppositeCellsStar _ _ x opp)
      simpa only [Bool.true_eq_false, iff_false] using
        third_missing _ _ _ hS3 h.1.2
          (touchD _ _ hQ2 hS3 cert.double_first.1).symm
          (touchD _ _ hS3 (cert.parent_lattice 1 true) cert.double_first.2.1)
    · have st := P4590T1OppositeCellsStar _ _ x opp
      exact .outer21 hC hB
        (swapStar _ _ (liftStar _ _ _ _ subS3 (fun _ h => h) st))
        (by simp [hA]) ((m21 hC hB).trans (by simp [hA]))
  · have hA := subQ3 h.1.1
    have hB := subS2 h.1.2
    have hD := h.2
    have sec := LocalLatticeInterfaceSectors.1 _ _ _ x hQ3 hS2
      (cert.parent_lattice 1 false) cert.double_second h
    rcases sec.2.2.2.2 with opp | opp | opp
    · exact .largestReflected h.1.1 h.1.2
        (P4590T1OppositeCellsStar _ _ x opp) (by simp [hD])
    · have st := P4590T1OppositeCellsStar _ _ x opp
      exact .outer12 hA hD
        (liftStar _ _ _ _ subQ3 (fun _ h => h) st)
        (by simp [hB]) ((m12 hA hD).trans (by simp [hB]))
    · apply BandOrderedGeneralInteriorWebRow.rightReflected h.1.2 hD
        (P4590T1OppositeCellsStar _ _ x opp)
      simpa only [Bool.true_eq_false, iff_false] using
        third_missing _ _ _ hQ3 h.1.1
          (touchD _ _ hQ3 hS2 cert.double_second.1)
          (touchD _ _ (cert.parent_lattice 1 false) hQ3
            cert.double_second.2.2.1).symm
  · have hA := subQ2 h.1.1
    have hC := h.1.2
    have hF := h.2
    have sec := LocalLatticeInterfaceSectors.1 _ _ _ x hQ2
      (cert.parent_lattice 1 true) (cert.parent_lattice 2 false)
      cert.double_third h
    rcases sec.2.2.2.2 with opp | opp | opp
    · apply BandOrderedGeneralInteriorWebRow.rightPositive h.1.1 hC
        (P4590T1OppositeCellsStar _ _ x opp)
      simpa only [Bool.true_eq_false, iff_false] using
        third_missing _ _ _ (cert.parent_lattice 2 false) hF
          (touchD _ _ (cert.parent_lattice 2 false) hQ2
            cert.double_third.2.2.1)
          (touchD _ _ (cert.parent_lattice 1 true) (cert.parent_lattice 2 false)
            cert.double_third.2.1).symm
    · have st := P4590T1OppositeCellsStar _ _ x opp
      exact .outer13 hA hF
        (liftStar _ _ _ _ subQ2 (fun _ h => h) st)
        (by simp [hC]) ((m13 hA hF).trans (by simp [hC]))
    · exact .outer23 hC hF (P4590T1OppositeCellsStar _ _ x opp)
        (by simp [hA]) ((m23 hC hF).trans (by simp [hA]))
  · have hB := subS2 h.1.1
    have hD := h.1.2
    have hE := h.2
    have sec := LocalLatticeInterfaceSectors.1 _ _ _ x hS2
      (cert.parent_lattice 1 false) (cert.parent_lattice 2 true)
      cert.double_fourth h
    rcases sec.2.2.2.2 with opp | opp | opp
    · apply BandOrderedGeneralInteriorWebRow.rightReflected h.1.1 hD
        (P4590T1OppositeCellsStar _ _ x opp)
      simpa only [Bool.true_eq_false, iff_false] using
        third_missing _ _ _ (cert.parent_lattice 2 true) hE
          (touchD _ _ (cert.parent_lattice 2 true) hS2
            cert.double_fourth.2.2.1)
          (touchD _ _ (cert.parent_lattice 1 false) (cert.parent_lattice 2 true)
            cert.double_fourth.2.1).symm
    · have st := P4590T1OppositeCellsStar _ _ x opp
      exact .outer31 hE hB
        (swapStar _ _ (liftStar _ _ _ _ subS2 (fun _ h => h) st))
        (by simp [hD]) ((m31 hE hB).trans (by simp [hD]))
    · exact .outer32 hE hD
        (swapStar _ _ (P4590T1OppositeCellsStar _ _ x opp))
        (by simp [hB]) ((m32 hE hD).trans (by simp [hB]))

end ApollonianSuperharmonic

end
