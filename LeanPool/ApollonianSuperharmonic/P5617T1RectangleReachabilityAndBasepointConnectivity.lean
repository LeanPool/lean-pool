/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FourNeighborConnected

-- [TABLET NODE: P5617T1RectangleReachabilityAndBasepointConnectivity]

/-!
# P5617T1RectangleReachabilityAndBasepointConnectivity

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5617T1RectangleReachabilityAndBasepointConnectivity :
    (∀ (A : Set LatticeCell) (x y : LatticeCell),
      (∀ z : LatticeCell,
        min x.re y.re ≤ z.re → z.re ≤ max x.re y.re →
        min x.im y.im ≤ z.im → z.im ≤ max x.im y.im → z ∈ A) →
      Relation.ReflTransGen
        (fun x y => FourNeighborAdjacent x y ∧ x ∈ A ∧ y ∈ A) x y) ∧
    (∀ (A : Set LatticeCell) (o : LatticeCell), o ∈ A →
      (∀ x ∈ A, Relation.ReflTransGen
        (fun x y => FourNeighborAdjacent x y ∧ x ∈ A ∧ y ∈ A) x o) →
      FourNeighborConnected A) := by
-- BODY
  classical
  let reach (A : Set LatticeCell) := Relation.ReflTransGen
    (fun x y => FourNeighborAdjacent x y ∧ x ∈ A ∧ y ∈ A)
  have single (A : Set LatticeCell) {x y : LatticeCell}
      (hx : x ∈ A) (hy : y ∈ A) (hxy : FourNeighborAdjacent x y) :
      reach A x y := Relation.ReflTransGen.single ⟨hxy, hx, hy⟩
  have rect (A : Set LatticeCell) (x y : LatticeCell)
      (hbox : ∀ z : LatticeCell,
        min x.re y.re ≤ z.re → z.re ≤ max x.re y.re →
        min x.im y.im ≤ z.im → z.im ≤ max x.im y.im → z ∈ A) :
      reach A x y := by
    have row : ∀ k : Int, min x.re y.re ≤ k → k ≤ max x.re y.re →
        reach A (⟨k, x.im⟩ : LatticeCell) ⟨y.re, x.im⟩ := by
      intro k
      induction k using Int.inductionOn' (b := y.re) with
      | zero => intro _ _; exact Relation.ReflTransGen.refl
      | succ k hk ih =>
        intro hl hu
        apply Relation.ReflTransGen.trans (single A
          (hbox ⟨k + 1, x.im⟩ hl hu (by simp) (by simp))
          (hbox ⟨k, x.im⟩ (by dsimp; omega) (by dsimp; omega) (by simp) (by simp))
          (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]))
        exact ih (by omega) (by omega)
      | pred k hk ih =>
        intro hl hu
        apply Relation.ReflTransGen.trans (single A
          (hbox ⟨k - 1, x.im⟩ hl hu (by simp) (by simp))
          (hbox ⟨k, x.im⟩ (by dsimp; omega) (by dsimp; omega) (by simp) (by simp))
          (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]))
        exact ih (by omega) (by omega)
    have col : ∀ k : Int, min x.im y.im ≤ k → k ≤ max x.im y.im →
        reach A (⟨y.re, k⟩ : LatticeCell) y := by
      intro k
      induction k using Int.inductionOn' (b := y.im) with
      | zero =>
        intro _ _
        have he : (⟨y.re, y.im⟩ : LatticeCell) = y := by ext <;> rfl
        rw [he]
      | succ k hk ih =>
        intro hl hu
        apply Relation.ReflTransGen.trans (single A
          (hbox ⟨y.re, k + 1⟩ (by simp) (by simp) hl hu)
          (hbox ⟨y.re, k⟩ (by simp) (by simp) (by dsimp; omega) (by dsimp; omega))
          (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]))
        exact ih (by omega) (by omega)
      | pred k hk ih =>
        intro hl hu
        apply Relation.ReflTransGen.trans (single A
          (hbox ⟨y.re, k - 1⟩ (by simp) (by simp) hl hu)
          (hbox ⟨y.re, k⟩ (by simp) (by simp) (by dsimp; omega) (by dsimp; omega))
          (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]))
        exact ih (by omega) (by omega)
    have hx : (⟨x.re, x.im⟩ : LatticeCell) = x := by ext <;> rfl
    have hr := row x.re (min_le_left _ _) (le_max_left _ _)
    rw [hx] at hr
    exact hr.trans (col x.im (min_le_left _ _) (le_max_left _ _))
  have connected (A : Set LatticeCell) (o : LatticeCell) (ho : o ∈ A)
      (hto : ∀ x ∈ A, reach A x o) : FourNeighborConnected A := by
    have symm {x y : LatticeCell} (h : reach A x y) : reach A y x := by
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail h hstep ih =>
        exact (single A hstep.2.2 hstep.2.1 (by
          rcases hstep.1 with h | h | h | h <;> subst_vars <;>
            simp [FourNeighborAdjacent, Zsqrtd.ext_iff])).trans ih
    have walk : ∀ {x y : LatticeCell}, x ∈ A → reach A x y →
        ∃ p : List LatticeCell, p.head? = some x ∧ p.getLast? = some y ∧
          (∀ z ∈ p, z ∈ A) ∧
          ∀ u v : LatticeCell, ∀ l₁ l₂ : List LatticeCell,
            p = l₁ ++ u :: v :: l₂ → FourNeighborAdjacent u v := by
      intro x y hx hxy
      induction hxy using Relation.ReflTransGen.head_induction_on with
      | refl =>
        exact ⟨[y], by simp, by simp, by simpa,
          List.isChain_iff_forall_rel_of_append_cons_cons.mp
            (List.isChain_singleton y)⟩
      | @head x z hstep hrest ih =>
        obtain ⟨p, hphead, hplast, hpmem, hpchain⟩ := ih hstep.2.2
        have hpne : p ≠ [] := by intro h; simp [h] at hphead
        have hchain : List.IsChain FourNeighborAdjacent (x :: p) := by
          rw [List.isChain_cons]
          exact ⟨by simpa [hphead] using hstep.1,
            List.isChain_iff_forall_rel_of_append_cons_cons.mpr hpchain⟩
        refine ⟨x :: p, by simp, ?_, ?_,
          List.isChain_iff_forall_rel_of_append_cons_cons.mp hchain⟩
        · cases p with
          | nil => exact (hpne rfl).elim
          | cons z p => simpa using hplast
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact hx
          · exact hpmem z hz
    exact ⟨⟨o, ho⟩, fun x hx y hy => walk hx ((hto x hx).trans (symm (hto y hy)))⟩
  exact ⟨rect, connected⟩

end ApollonianSuperharmonic

end
