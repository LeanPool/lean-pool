/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FinitePolyominoDiskCriterion
public import LeanPool.ApollonianSuperharmonic.P5617T1RectangleReachabilityAndBasepointConnectivity
public import LeanPool.ApollonianSuperharmonic.DiamondTile
public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondCellRows

-- [TABLET NODE: P5116T1UnitDeletionDisk]

/-!
# P5116T1UnitDeletionDisk

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5116T1UnitDeletionDisk (k : Nat) (hk : 0 < k)
    (x : GaussianInt)
    (hx : (x.re = -(k : Int) ∨ x.re = (k : Int) - 1) ∧
      (x.im = (k : Int) - 1 ∨ x.im = (k : Int)))
    (T : ProtoTile) (hcells : T.cells = (DiamondTile k).cells \ {x}) :
    LatticeTile T := by
-- BODY
  classical
  let reach (A : Set LatticeCell) := Relation.ReflTransGen
    (fun x y => FourNeighborAdjacent x y ∧ x ∈ A ∧ y ∈ A)
  have single (A : Set LatticeCell) {x y : LatticeCell}
      (hx : x ∈ A) (hy : y ∈ A) (hxy : FourNeighborAdjacent x y) :
      reach A x y := Relation.ReflTransGen.single ⟨hxy, hx, hy⟩
  obtain ⟨rect, connected⟩ := P5617T1RectangleReachabilityAndBasepointConnectivity
  have diamond (z : LatticeCell) : z ∈ (DiamondTile k).cells ↔
      0 ≤ z.im ∧ z.im < 2 * (k : Int) ∧
      -(z.im + 1) ≤ z.re ∧ z.re < z.im + 1 ∧
      -(2 * (k : Int) - z.im) ≤ z.re ∧ z.re < 2 * (k : Int) - z.im :=
    (P4194T1DiamondCellRows k z).1
  let A : Set LatticeCell := T.cells
  have mem (z : LatticeCell) : z ∈ A ↔ z ∈ (DiamondTile k).cells ∧ z ≠ x := by
    simp [A, hcells]
  let c : Int := if x.re = 0 then -1 else 0
  let o : LatticeCell := ⟨c, 0⟩
  have ho : o ∈ A := by
    rw [mem, diamond]
    simp only [o, ne_eq, Zsqrtd.ext_iff]
    dsimp [c]
    split_ifs <;> omega
  have inside : FourNeighborConnected A := by
    apply connected A o ho
    intro p hp
    have hp' := (mem p).mp hp
    rw [diamond] at hp'
    let m : LatticeCell := ⟨c, p.im⟩
    apply (rect A p m ?_).trans (rect A m o ?_)
    all_goals
      intro z h1 h2 h3 h4
      rw [mem, diamond]
      simp only [ne_eq, Zsqrtd.ext_iff] at hp' ⊢
      dsimp [m, o, c] at h1 h2 h3 h4 ⊢
      split_ifs at * <;> rcases hx with ⟨hx1 | hx1, hx2 | hx2⟩ <;> omega
  let e : LatticeCell := ⟨(k : Int) + 1, -1⟩
  have exterior (p : LatticeCell) (hp : p ∉ (DiamondTile k).cells) :
      reach Aᶜ p e := by
    let a : Int := if p.re < 0 then -(k : Int) - 1 else (k : Int) + 1
    let m : LatticeCell := ⟨a, p.im⟩
    let n : LatticeCell := ⟨a, -1⟩
    apply (rect Aᶜ p m ?_).trans ((rect Aᶜ m n ?_).trans (rect Aᶜ n e ?_))
    all_goals
      intro z h1 h2 h3 h4
      change z ∉ A
      rw [mem, diamond]
      rw [diamond] at hp
      dsimp [m, n, e, a] at h1 h2 h3 h4
      split_ifs at * <;> omega
  have he : e ∈ Aᶜ := by
    change e ∉ A
    rw [mem, diamond]
    simp [e]
  have outside : FourNeighborConnected Aᶜ := by
    apply connected Aᶜ e he
    intro p hp
    by_cases hpD : p ∈ (DiamondTile k).cells
    · have hpx : p = x := by
        change p ∉ A at hp
        rw [mem] at hp
        tauto
      subst p
      let n : LatticeCell := if x.re < 0 then x - 1 else x + 1
      have hnD : n ∉ (DiamondTile k).cells := by
        rw [diamond]
        dsimp [n]
        split_ifs <;> simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add,
          Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one] <;>
          rcases hx with ⟨hx1 | hx1, hx2 | hx2⟩ <;> omega
      have hn : n ∈ Aᶜ := by
        change n ∉ A
        rw [mem]
        tauto
      exact (single Aᶜ hp hn (by
        dsimp [n]; split_ifs <;> simp [FourNeighborAdjacent])).trans (exterior n hnD)
    · exact exterior p hpD
  have checker : NoCheckerboardCellVertex A := by
    intro z
    simp only [mem, diamond, ne_eq, Zsqrtd.ext_iff, Zsqrtd.re_sub, Zsqrtd.im_sub,
      Zsqrtd.re_one, Zsqrtd.im_one]
    norm_num
    rcases hx with ⟨hx1 | hx1, hx2 | hx2⟩ <;> omega
  exact FinitePolyominoDiskCriterion T inside outside checker

end ApollonianSuperharmonic

end
