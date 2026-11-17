/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3161T1BlockTreeReachability
public import LeanPool.ApollonianSuperharmonic.P3161T1SquareTriangleComplement

-- [TABLET NODE: P3161T1AggregateComplementConnectivity]

/-!
# P3161T1AggregateComplementConnectivity

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3161T1AggregateComplementConnectivity
    (τ σ : Finset (Int × Int))
    (hτ : τ ∈ ({
      {(0, 0), (1, 0), (0, -1)},
      {(0, 0), (0, 1), (1, 1)},
      {(0, 0), (-1, -1), (-1, 0)}
    } : Finset (Finset (Int × Int))))
    (hσ : σ ⊆ τ)
    (a b : PeriodicSubtileIndex)
    (ha : (a.first, a.second) ∉ σ) (hb : (b.first, b.second) ∉ σ) :
    Relation.ReflTransGen
      (fun x y : PeriodicSubtileIndex ↦
        AllowedSubtileIncidence x y ∧ (x.first, x.second) ∉ σ ∧
          (y.first, y.second) ∉ σ) a b := by
-- BODY
  obtain ⟨d, hd⟩ : ∃ d : Int × Int, ∀ z ∈ τ,
      (z.1 - d.1, z.2 - z.1 - d.2) ∈
        ({(0, 0), (1, 0), (0, 1)} : Finset (Int × Int)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl
    · refine ⟨(0, -1), ?_⟩
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> norm_num
    · refine ⟨(0, 0), ?_⟩
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> norm_num
    · refine ⟨(-1, 0), ?_⟩
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> norm_num
  let f := fun z : Int × Int ↦ (z.1 - d.1, z.2 - z.1 - d.2)
  let g := fun z : Int × Int ↦ (z.1 + d.1, z.2 + z.1 + d.1 + d.2)
  have gf (z) : g (f z) = z := by
    apply Prod.ext <;> dsimp [f, g] <;> omega
  have fg (z) : f (g z) = z := by
    apply Prod.ext <;> dsimp [f, g] <;> omega
  let D := σ.image f
  have hD : D ⊆ {(0, 0), (1, 0), (0, 1)} := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact hd w (hσ hw)
  have absent (z) : z ∉ D → g z ∉ σ := by
    intro hz hw
    exact hz (Finset.mem_image.mpr ⟨g z, hw, fg z⟩)
  have absent' (z) (hz : z ∉ σ) : f z ∉ D := by
    intro h
    obtain ⟨w, hw, he⟩ := Finset.mem_image.mp h
    have hwz : w = z := by simpa only [gf] using congrArg g he
    exact hz (hwz ▸ hw)
  let R := fun x y : PeriodicSubtileIndex ↦
    AllowedSubtileIncidence x y ∧ (x.first, x.second) ∉ σ ∧
      (y.first, y.second) ∉ σ
  let A := fun z : Int × Int ↦ (⟨.A, z.1, z.2⟩ : PeriodicSubtileIndex)
  have rev {x y} (hxy : Relation.ReflTransGen R x y) :
      Relation.ReflTransGen R y x := by
    induction hxy with
    | refl => exact .refl
    | tail _ e ih => exact (Relation.ReflTransGen.single
        ⟨e.1.symm, e.2.2, e.2.1⟩).trans ih
  have up (m n : Int) (hm : (m, n) ∉ σ) (hn : (m, n + 1) ∉ σ) :
      Relation.ReflTransGen R (A (m, n)) (A (m, n + 1)) :=
    (Relation.ReflTransGen.single
      ⟨AllowedSubtileIncidence.AB01 m n, hm, hn⟩).trans
      (.single ⟨(AllowedSubtileIncidence.AB m (n + 1)).symm, hn, hn⟩)
  have right (m n : Int) (hm : (m, n) ∉ σ) (hn : (m + 1, n + 1) ∉ σ) :
      Relation.ReflTransGen R (A (m, n)) (A (m + 1, n + 1)) :=
    (Relation.ReflTransGen.single
      ⟨AllowedSubtileIncidence.AB11 m n, hm, hn⟩).trans
      (.single ⟨(AllowedSubtileIncidence.AB (m + 1) (n + 1)).symm, hn, hn⟩)
  have step (z w : Int × Int)
      (e : ((z.1 = w.1 ∧ (z.2 + 1 = w.2 ∨ w.2 + 1 = z.2)) ∨
        (z.2 = w.2 ∧ (z.1 + 1 = w.1 ∨ w.1 + 1 = z.1))) ∧
        z ∉ D ∧ w ∉ D) :
      Relation.ReflTransGen R (A (g z)) (A (g w)) := by
    have hz := absent z e.2.1
    have hw := absent w e.2.2
    rcases e.1 with ⟨hx, hy | hy⟩ | ⟨hy, hx | hx⟩
    · have he : g w = ((g z).1, (g z).2 + 1) := by
        apply Prod.ext <;> dsimp [g] <;> omega
      rw [he] at hw ⊢
      exact up _ _ hz hw
    · have he : g z = ((g w).1, (g w).2 + 1) := by
        apply Prod.ext <;> dsimp [g] <;> omega
      rw [he] at hz ⊢
      exact rev (up _ _ hw hz)
    · have he : g w = ((g z).1 + 1, (g z).2 + 1) := by
        apply Prod.ext <;> dsimp [g] <;> omega
      rw [he] at hw ⊢
      exact right _ _ hz hw
    · have he : g z = ((g w).1 + 1, (g w).2 + 1) := by
        apply Prod.ext <;> dsimp [g] <;> omega
      rw [he] at hz ⊢
      exact rev (right _ _ hw hz)
  have between : Relation.ReflTransGen R
      (A (a.first, a.second)) (A (b.first, b.second)) := by
    have h := P3161T1SquareTriangleComplement D hD
      (f (a.first, a.second)) (f (b.first, b.second))
      (absent' _ ha) (absent' _ hb)
    have lift : ∀ z w : Int × Int,
        Relation.ReflTransGen
          (fun x y : Int × Int ↦
            ((x.1 = y.1 ∧ (x.2 + 1 = y.2 ∨ y.2 + 1 = x.2)) ∨
              (x.2 = y.2 ∧ (x.1 + 1 = y.1 ∨ y.1 + 1 = x.1))) ∧
            x ∉ D ∧ y ∉ D) z w →
          Relation.ReflTransGen R (A (g z)) (A (g w)) := by
      intro z w hzw
      induction hzw with
      | refl => exact .refl
      | tail _ e ih => exact ih.trans (step _ _ e)
    simpa only [gf] using lift _ _ h
  cases a with | mk ca ma na =>
    cases b with | mk cb mb nb =>
      exact (P3161T1BlockTreeReachability (fun z ↦ z ∉ σ) ma na ha ca .A).trans
        (between.trans (P3161T1BlockTreeReachability (fun z ↦ z ∉ σ) mb nb hb .A cb))

end ApollonianSuperharmonic

end
