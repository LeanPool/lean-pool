/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FinitePolyominoDiskCriterion
public import
    LeanPool.ApollonianSuperharmonic.P5617T1RectangleReachabilityAndBasepointConnectivity

-- [TABLET NODE: P5104T1CornerDeletionDisk]

/-!
# P5104T1CornerDeletionDisk

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5104T1CornerDeletionDisk :
    ∀ (T : ProtoTile), ∀ (q : Int), ∀ (a : Int), ∀ (b : Int), (0 < a) → ((a < q) → ((0 < b) → ((b
        < q) → (∀ (left : Bool), ∀ (bottom : Bool), (∀ z : GaussianInt, z ∈ T.cells ↔
      (0 ≤ z.re ∧ z.re < q ∧ 0 ≤ z.im ∧ z.im < q) ∧
        ¬ ((if left then z.re < a else a ≤ z.re) ∧
          (if bottom then z.im < b else b ≤ z.im))) → (LatticeTile T))))) := by
  intro T q a b ha haq hb hbq left bottom hcells
-- BODY
  classical
  let reach (A : Set LatticeCell) := Relation.ReflTransGen
    (fun x y => FourNeighborAdjacent x y ∧ x ∈ A ∧ y ∈ A)
  obtain ⟨rect, connected⟩ := P5617T1RectangleReachabilityAndBasepointConnectivity
  let A : Set LatticeCell := T.cells
  let o : LatticeCell := ⟨if left then q - 1 else 0,
    if bottom then q - 1 else 0⟩
  have ho : o ∈ A := by
    change o ∈ T.cells
    rw [hcells]
    cases left <;> cases bottom <;> simp [o] <;> omega
  have inside : FourNeighborConnected A := by
    apply connected A o ho
    intro x hx
    have hx' := (hcells x).mp hx
    let m : LatticeCell := ⟨o.re, x.im⟩
    apply Relation.ReflTransGen.trans (rect A x m ?_) (rect A m o ?_)
    all_goals
      intro z hl hu hb' ht
      change z ∈ T.cells
      rw [hcells]
      cases left <;> cases bottom <;>
        dsimp [m, o] at hl hu hb' ht hx' ⊢ <;> omega
  let e : LatticeCell := ⟨-1, -1⟩
  have exterior (x : LatticeCell)
      (hx : ¬ (0 ≤ x.re ∧ x.re < q ∧ 0 ≤ x.im ∧ x.im < q)) :
      reach Aᶜ x e := by
    have path (x y : LatticeCell)
        (h : ∀ z : LatticeCell,
          min x.re y.re ≤ z.re → z.re ≤ max x.re y.re →
          min x.im y.im ≤ z.im → z.im ≤ max x.im y.im →
          ¬ (0 ≤ z.re ∧ z.re < q ∧ 0 ≤ z.im ∧ z.im < q)) :
        reach Aᶜ x y := by
      apply rect
      intro z hl hu hb' ht
      change z ∉ T.cells
      rw [hcells]
      exact fun hz => h z hl hu hb' ht hz.1
    by_cases hl : x.re < 0
    · let m : LatticeCell := ⟨-1, x.im⟩
      exact (path x m (by intro z h1 h2 h3 h4; dsimp [m] at *; omega)).trans
        (path m e (by intro z h1 h2 h3 h4; dsimp [m, e] at *; omega))
    by_cases hr : q ≤ x.re
    · let m : LatticeCell := ⟨x.re, -1⟩
      exact (path x m (by intro z h1 h2 h3 h4; dsimp [m] at *; omega)).trans
        (path m e (by intro z h1 h2 h3 h4; dsimp [m, e] at *; omega))
    by_cases hb' : x.im < 0
    · exact path x e (by intro z h1 h2 h3 h4; dsimp [e] at *; omega)
    · let m : LatticeCell := ⟨-1, x.im⟩
      exact (path x m (by intro z h1 h2 h3 h4; dsimp [m] at *; omega)).trans
        (path m e (by intro z h1 h2 h3 h4; dsimp [m, e] at *; omega))
  have outside : FourNeighborConnected Aᶜ := by
    apply connected Aᶜ e
    · change e ∉ T.cells
      rw [hcells]
      simp [e]
    · intro x hx
      by_cases hbox : 0 ≤ x.re ∧ x.re < q ∧ 0 ≤ x.im ∧ x.im < q
      · let m : LatticeCell := ⟨if left then -1 else q, x.im⟩
        apply Relation.ReflTransGen.trans (rect Aᶜ x m ?_) (exterior m ?_)
        · intro z hl hu hb' ht
          change z ∉ T.cells
          change x ∉ T.cells at hx
          rw [hcells] at hx ⊢
          cases left <;> cases bottom <;>
            dsimp [m] at hl hu hb' ht hx ⊢ <;> omega
        · cases left <;> simp [m]
      · exact exterior x hbox
  have checker : NoCheckerboardCellVertex A := by
    intro z
    simp only [A, Finset.mem_coe, hcells, Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one,
      Zsqrtd.im_one]
    cases left <;> cases bottom <;> simp <;> omega
  exact FinitePolyominoDiskCriterion T inside outside checker

end ApollonianSuperharmonic

end
