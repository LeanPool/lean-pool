/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble
public import Mathlib.Order.SuccPred.Int
public import Mathlib.Order.SuccPred.Relation

-- [TABLET NODE: P3161T1SquareTriangleComplement]

/-!
# P3161T1SquareTriangleComplement

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3161T1SquareTriangleComplement
    (S : Finset (Int × Int))
    (hS : S ⊆ {(0, 0), (1, 0), (0, 1)})
    (a b : Int × Int) (ha : a ∉ S) (hb : b ∉ S) :
    Relation.ReflTransGen
      (fun x y : Int × Int ↦
        ((x.1 = y.1 ∧ (x.2 + 1 = y.2 ∨ y.2 + 1 = x.2)) ∨
          (x.2 = y.2 ∧ (x.1 + 1 = y.1 ∨ y.1 + 1 = x.1))) ∧
        x ∉ S ∧ y ∉ S) a b := by
-- BODY
  let L : Finset (Int × Int) := {(0, 0), (1, 0), (0, 1)}
  let adj := fun x y : Int × Int ↦
    (x.1 = y.1 ∧ (x.2 + 1 = y.2 ∨ y.2 + 1 = x.2)) ∨
      (x.2 = y.2 ∧ (x.1 + 1 = y.1 ∨ y.1 + 1 = x.1))
  let R := fun x y : Int × Int ↦ adj x y ∧ x ∉ L ∧ y ∉ L
  have adjrev {x y} (h : adj x y) : adj y x := by
    rcases h with ⟨h, e | e⟩ | ⟨h, e | e⟩
    · exact Or.inl ⟨h.symm, Or.inr e⟩
    · exact Or.inl ⟨h.symm, Or.inl e⟩
    · exact Or.inr ⟨h.symm, Or.inr e⟩
    · exact Or.inr ⟨h.symm, Or.inl e⟩
  have rev {x y} (hxy : Relation.ReflTransGen R x y) :
      Relation.ReflTransGen R y x := by
    induction hxy with
    | refl => exact .refl
    | tail _ e ih => exact (Relation.ReflTransGen.single
        ⟨adjrev e.1, e.2.2, e.2.1⟩).trans ih
  have outside (x y : Int)
      (h : x ≤ -1 ∨ 2 ≤ x ∨ y ≤ -1 ∨ 2 ≤ y) : (x, y) ∉ L := by
    simp only [L, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega
  have segment (f : Int → Int × Int) (i j : Int) (hij : i ≤ j)
      (hf : ∀ k, i ≤ k → k ≤ j → f k ∉ L)
      (he : ∀ k, adj (f k) (f (k + 1))) :
      Relation.ReflTransGen R (f i) (f j) := by
    have h := reflTransGen_of_succ_of_le (fun k l : Int ↦ R (f k) (f l))
      (n := i) (m := j) (by
        intro k hk
        change i ≤ k ∧ k < j at hk
        change R (f k) (f (k + 1))
        exact ⟨he k, hf k hk.1 (by omega), hf (k + 1) (by omega) (by omega)⟩) hij
    clear hij hf
    induction h with
    | refl => exact .refl
    | tail _ e ih => exact ih.tail e
  have axis (f : Int → Int × Int) (i j : Int)
      (hf : ∀ k, min i j ≤ k → k ≤ max i j → f k ∉ L)
      (he : ∀ k, adj (f k) (f (k + 1))) :
      Relation.ReflTransGen R (f i) (f j) := by
    by_cases h : i ≤ j
    · exact segment f i j h (by simpa only [min_eq_left h, max_eq_right h] using hf) he
    · have h' : j ≤ i := by omega
      exact rev (segment f j i h'
        (by simpa only [min_eq_right h', max_eq_left h'] using hf) he)
  have horizontal (x x' y : Int)
      (h : ∀ k, min x x' ≤ k → k ≤ max x x' → (k, y) ∉ L) :
      Relation.ReflTransGen R (x, y) (x', y) :=
    axis (fun k ↦ (k, y)) x x' h (fun k ↦ Or.inr ⟨rfl, Or.inl rfl⟩)
  have vertical (x y y' : Int)
      (h : ∀ k, min y y' ≤ k → k ≤ max y y' → (x, k) ∉ L) :
      Relation.ReflTransGen R (x, y) (x, y') :=
    axis (fun k ↦ (x, k)) y y' h (fun k ↦ Or.inl ⟨rfl, Or.inl rfl⟩)
  have row (x x' y : Int) (hy : y ≤ -1 ∨ 2 ≤ y) :
      Relation.ReflTransGen R (x, y) (x', y) :=
    horizontal x x' y (fun k _ _ ↦ outside k y (Or.inr (Or.inr hy)))
  have col (x y y' : Int) (hx : x ≤ -1 ∨ 2 ≤ x) :
      Relation.ReflTransGen R (x, y) (x, y') :=
    vertical x y y' (fun k _ _ ↦ outside x k (by omega))
  have toHub (z : Int × Int) (hz : z ∉ L) :
      Relation.ReflTransGen R z (-1, -1) := by
    rcases z with ⟨x, y⟩
    by_cases hx : x ≤ -1
    · exact (horizontal x (-1) y (by
        intro k hk hk'
        exact outside k y (Or.inl (by omega)))).trans
        (col (-1) y (-1) (Or.inl (by omega)))
    by_cases hx' : 2 ≤ x
    · exact (horizontal x 2 y (by
        intro k hk hk'
        exact outside k y (Or.inr (Or.inl (by omega))))).trans
        ((col 2 y (-1) (Or.inr (by omega))).trans
          (row 2 (-1) (-1) (Or.inl (by omega))))
    by_cases hy : y ≤ -1
    · exact (vertical x y (-1) (by
        intro k hk hk'
        exact outside x k (Or.inr (Or.inr (Or.inl (by omega)))))).trans
        (row x (-1) (-1) (Or.inl (by omega)))
    by_cases hy' : 2 ≤ y
    · exact (vertical x y 2 (by
        intro k hk hk'
        exact outside x k (Or.inr (Or.inr (Or.inr (by omega)))))).trans
        ((row x (-1) 2 (Or.inr (by omega))).trans
          (col (-1) 2 (-1) (Or.inl (by omega))))
    have hxy : x = 1 ∧ y = 1 := by
      simp only [L, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hz
      omega
    rcases hxy with ⟨rfl, rfl⟩
    exact (Relation.ReflTransGen.single (r := R) (a := (1, 1)) (b := (1, 2))
      ⟨Or.inl ⟨rfl, Or.inl (by norm_num)⟩, hz, outside 1 2 (by omega)⟩).trans
      ((row 1 (-1) 2 (Or.inr (by omega))).trans
        (col (-1) 2 (-1) (Or.inl (by omega))))
  let R' := fun x y : Int × Int ↦ adj x y ∧ x ∉ S ∧ y ∉ S
  have mono {x y} (h : Relation.ReflTransGen R x y) :
      Relation.ReflTransGen R' x y := by
    induction h with
    | refl => exact .refl
    | tail _ e ih =>
      exact ih.tail ⟨e.1, fun hx ↦ e.2.1 (hS hx), fun hy ↦ e.2.2 (hS hy)⟩
  have rev' {x y} (hxy : Relation.ReflTransGen R' x y) :
      Relation.ReflTransGen R' y x := by
    induction hxy with
    | refl => exact .refl
    | tail _ e ih => exact (Relation.ReflTransGen.single
        ⟨adjrev e.1, e.2.2, e.2.1⟩).trans ih
  have restored (z : Int × Int) (hz : z ∉ S) :
      Relation.ReflTransGen R' z (-1, -1) := by
    by_cases h : z ∈ L
    · simp only [L, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl
      · exact (Relation.ReflTransGen.single (r := R') (a := (0, 0)) (b := (-1, 0))
          ⟨Or.inr ⟨rfl, Or.inr (by norm_num)⟩, hz,
            fun h ↦ outside (-1) 0 (by omega) (hS h)⟩).trans
          (mono (toHub (-1, 0) (outside (-1) 0 (by omega))))
      · exact (Relation.ReflTransGen.single (r := R') (a := (1, 0)) (b := (2, 0))
          ⟨Or.inr ⟨rfl, Or.inl (by norm_num)⟩, hz,
            fun h ↦ outside 2 0 (by omega) (hS h)⟩).trans
          (mono (toHub (2, 0) (outside 2 0 (by omega))))
      · exact (Relation.ReflTransGen.single (r := R') (a := (0, 1)) (b := (0, 2))
          ⟨Or.inl ⟨rfl, Or.inl (by norm_num)⟩, hz,
            fun h ↦ outside 0 2 (by omega) (hS h)⟩).trans
          (mono (toHub (0, 2) (outside 0 2 (by omega))))
    · exact mono (toHub z h)
  exact (restored a ha).trans (rev' (restored b hb))

end ApollonianSuperharmonic

end
