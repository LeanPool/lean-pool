/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5124T1ParentModel
public import LeanPool.ApollonianSuperharmonic.P5124T1TranslatedDiamonds
public import LeanPool.ApollonianSuperharmonic.P5253T1OneEdgeInterface
public import LeanPool.ApollonianSuperharmonic.P5253T1TopSquareContacts
public import LeanPool.ApollonianSuperharmonic.P5253T1LeftSquareContacts
public import LeanPool.ApollonianSuperharmonic.P5253T1BottomSquareContact

-- [TABLET NODE: P5124T1UnitParents]

/-!
# P5124T1UnitParents

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5124T1UnitParents (k : Nat) (hk : 0 < k) :
    let D := DiamondTile k
    TouchingTriple D
      (TileTranslation D ⟨(k : Int) + 1, (k : Int)⟩)
      (P5124T1ParentModel k 0 true) ∧
    TouchingTriple D
      (TileTranslation D ⟨-(k : Int) - 1, (k : Int)⟩)
      (P5124T1ParentModel k 1 true) ∧
    TouchingTriple D (P5124T1ParentModel k 0 true)
      (P5124T1ParentModel k 1 false) := by
-- BODY
  classical
  let D := DiamondTile k
  let a : GaussianInt := ⟨(k : Int) + 1, (k : Int)⟩
  let b : GaussianInt := ⟨-(k : Int) - 1, (k : Int)⟩
  let z : GaussianInt := ⟨0, 2 * (k : Int)⟩
  let l : GaussianInt := ⟨-1, 2 * (k : Int)⟩
  let w : GaussianInt := ⟨-(k : Int) - 1, (k : Int) - 1⟩
  let unit := fun c : GaussianInt => (⟨{c}, c⟩ : ProtoTile)
  have zero (T : ProtoTile) : TileTranslation T 0 = T := by
    have hg : GaussianTranslation (0 : GaussianInt) = id := by
      funext x
      exact add_zero x
    cases T
    simp [TileTranslation, hg]
  have top := P5253T1TopSquareContacts k hk 0 0 (Or.inr rfl)
  have topLeft := P5253T1TopSquareContacts k hk 0 (-1) (Or.inl rfl)
  simp only [zero, zero_add] at top topLeft
  have left := P5253T1LeftSquareContacts k hk 0 ((k : Int) - 1) (Or.inl rfl)
  simp only [zero, zero_add] at left
  have az : a + (⟨-(k : Int) - 1, (k : Int)⟩ : GaussianInt) = z := by
    ext <;> simp [a, z]; ring
  have right := P5253T1LeftSquareContacts k hk a (k : Int) (Or.inr rfl)
  dsimp only at right
  rw [az] at right
  have bw : b - (⟨0, 1⟩ : GaussianInt) = w := by ext <;> simp [b, w]
  have bi : b = w + (⟨0, 1⟩ : GaussianInt) := by ext <;> simp [b, w]
  have bottom := P5253T1BottomSquareContact k hk b
  dsimp only at bottom
  rw [bw] at bottom
  have finish (T : ProtoTile) (c x y : GaussianInt)
      (h : T.cells.Nonempty ∧ Disjoint T.cells (unit c).cells ∧
        BoundaryFootprintVertices T ∩ BoundaryFootprintVertices (unit c) = {x, y} ∧
        {x, y} ∈ BoundaryFootprintEdges T)
      (he : {x, y} ∈ BoundaryFootprintEdges (unit c))
      (ha : y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩) :
      TileTouching T (unit c) ∧ TileTouching (unit c) T := by
    exact (P5253T1OneEdgeInterface T (unit c) x y h.1
      (Finset.singleton_nonempty c) h.2.1 h.2.2.1 h.2.2.2 he ha).2.2
  have unitEdge (c : GaussianInt) (e : Finset GaussianInt) :
      e ∈ BoundaryFootprintEdges (unit c) ↔
        e = {c, c + 1} ∨ e = {c, c + ⟨0, 1⟩} ∨
        e = {c + ⟨0, 1⟩, c + 1 + ⟨0, 1⟩} ∨
        e = {c + 1, c + 1 + ⟨0, 1⟩} := by
    rw [(P5253T1SingletonBoundary c c).2]
    rfl
  have du := finish D z z (z + 1) top
    ((unitEdge z _).mpr (Or.inl rfl)) (Or.inl rfl)
  have dl := finish D l l (l + 1) topLeft
    ((unitEdge l _).mpr (Or.inl rfl)) (Or.inl rfl)
  have dv := finish D w (w + 1) (w + 1 + ⟨0, 1⟩) left
    ((unitEdge w _).mpr (Or.inr (Or.inr (Or.inr rfl))))
    (Or.inr (Or.inr (Or.inl rfl)))
  have ru := finish (TileTranslation D a) z (z + 1) (z + 1 + ⟨0, 1⟩) right
    ((unitEdge z _).mpr (Or.inr (Or.inr (Or.inr rfl))))
    (Or.inr (Or.inr (Or.inl rfl)))
  have lv := finish (TileTranslation D b) w b (b + 1) bottom
    ((unitEdge w _).mpr (Or.inr (Or.inr (Or.inl (by rw [bi]; congr 1; abel)))))
    (Or.inl rfl)
  have ulVertices : BoundaryFootprintVertices (unit z) ∩
      BoundaryFootprintVertices (unit l) = {z, z + ⟨0, 1⟩} := by
    ext v
    rw [(P5253T1SingletonBoundary z z).1,
      (P5253T1SingletonBoundary l l).1]
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Zsqrtd.ext_iff, z, l, Zsqrtd.re_add, Zsqrtd.im_add,
      Zsqrtd.re_one, Zsqrtd.im_one]
    omega
  have ul : TileTouching (unit z) (unit l) := by
    have hd : Disjoint (unit z).cells (unit l).cells := by
      simp [unit, z, l, Zsqrtd.ext_iff]
    have ez := (unitEdge z {z, z + ⟨0, 1⟩}).mpr (Or.inr (Or.inl rfl))
    have el : {z, z + ⟨0, 1⟩} ∈ BoundaryFootprintEdges (unit l) := by
      have lz : l + 1 = z := by ext <;> simp [l, z]
      exact (unitEdge l _).mpr (Or.inr (Or.inr (Or.inr (by rw [lz]))))
    exact (P5253T1OneEdgeInterface (unit z) (unit l) z (z + ⟨0, 1⟩)
      (Finset.singleton_nonempty z) (Finset.singleton_nonempty l)
      hd ulVertices ez el (Or.inr (Or.inr (Or.inl rfl)))).2.2.1
  have unique (A B C : ProtoTile) (x y t : GaussianInt)
      (hAC : BoundaryFootprintVertices A ∩ BoundaryFootprintVertices C = {x, y})
      (hBC : BoundaryFootprintVertices B ∩ BoundaryFootprintVertices C = {t, y})
      (hxy : x ≠ y) (hxt : x ≠ t) :
      ∃! v, v ∈ BoundaryFootprintVertices A ∧ v ∈ BoundaryFootprintVertices B ∧
        v ∈ BoundaryFootprintVertices C := by
    have hyA : y ∈ BoundaryFootprintVertices A ∩ BoundaryFootprintVertices C := by
      rw [hAC]; simp
    have hyB : y ∈ BoundaryFootprintVertices B ∩ BoundaryFootprintVertices C := by
      rw [hBC]; simp
    refine ⟨y, ⟨hyA.1, hyB.1, hyA.2⟩, ?_⟩
    intro v hv
    have hA : v ∈ ({x, y} : Set GaussianInt) := by rw [← hAC]; exact ⟨hv.1, hv.2.2⟩
    have hB : v ∈ ({t, y} : Set GaussianInt) := by rw [← hBC]; exact ⟨hv.2.1, hv.2.2⟩
    rcases hA with hA | hA
    · rcases hB with hB | hB
      · exact False.elim (hxt (hA.symm.trans hB))
      · exact hB
    · exact hA
  have j0 := unique D (TileTranslation D a) (unit z) z (z + 1)
    (z + 1 + ⟨0, 1⟩) top.2.2.1
    (by simpa only [Set.pair_comm] using right.2.2.1)
    (by simp []) (by simp [Zsqrtd.ext_iff])
  have j1 := unique D (TileTranslation D b) (unit w) (w + 1)
    (w + 1 + ⟨0, 1⟩) (w + ⟨0, 1⟩) left.2.2.1
    (by simpa only [bi, add_assoc, add_comm, add_left_comm] using bottom.2.2.1)
    (by simp [Zsqrtd.ext_iff]) (by simp [Zsqrtd.ext_iff])
  have j2 := unique (unit z) (unit l) D (z + 1) z l
    (by simpa only [Set.inter_comm, Set.pair_comm] using top.2.2.1)
    (by
      have lz : l + 1 = z := by ext <;> simp [l, z]
      have h : BoundaryFootprintVertices D ∩ BoundaryFootprintVertices (unit l) =
          {l, l + 1} := topLeft.2.2.1
      rw [lz] at h
      simpa only [Set.inter_comm] using h)
    (by simp []) (by simp [z, l, Zsqrtd.ext_iff])
  obtain ⟨t0, t1, _⟩ := P5124T1TranslatedDiamonds k hk
  have result : TouchingTriple D (TileTranslation D a) (unit z) ∧
      TouchingTriple D (TileTranslation D b) (unit w) ∧
      TouchingTriple D (unit z) (unit l) :=
    ⟨⟨t0.1, ru.1, du.2, j0⟩, ⟨t1.1, lv.1, dv.2, j1⟩,
      ⟨du.1, ul, dl.2, by simpa only [and_assoc, and_comm, and_left_comm] using j2⟩⟩
  exact result

end ApollonianSuperharmonic

end
