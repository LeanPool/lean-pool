/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5124T1BoundaryGeometry
public import LeanPool.ApollonianSuperharmonic.P5157T1StaircasePoint
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: P5250T1ConsecutiveEdges]

/-!
# P5250T1ConsecutiveEdges

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5250T1ConsecutiveEdges (k : Nat) (hk : 1 < k) :
    let D := DiamondTile k
    let L := TileTranslation D ⟨0, -(2 * (k : Int))⟩
    let Eplus := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
    let Eminus := TileTranslation (DiamondTile (k - 1)) ⟨-(k : Int), 1 - (k : Int)⟩
    let N := 2 * (k - 1)
    let p := P5157T1StaircasePoint 1 false 1
    let q := P5157T1StaircasePoint 1 false (-1)
    let r := P5157T1StaircasePoint ⟨-(k : Int), (k : Int) - 1⟩ true (-1)
    (∀ j < N, ({p j, p (j + 1)} : Finset GaussianInt) ∈
      BoundaryFootprintEdges D ∩ BoundaryFootprintEdges Eplus) ∧
    (∀ j < N, ({q j, q (j + 1)} : Finset GaussianInt) ∈
      BoundaryFootprintEdges L ∩ BoundaryFootprintEdges Eplus) ∧
    (∀ j < N, ({r j, r (j + 1)} : Finset GaussianInt) ∈
      BoundaryFootprintEdges D ∩ BoundaryFootprintEdges Eminus) := by
-- BODY
  classical
  have hor (m : Nat) (hm : 0 < m) (u : GaussianInt) (a b : Int)
      (h : (((b - u.im = 0 ∨ b - u.im = 2 * (m : Int)) ∧
          -1 ≤ a - u.re ∧ a - u.re < 1) ∨
        (1 ≤ b - u.im ∧ b - u.im < (m : Int) ∧
          (a - u.re = -(b - u.im) - 1 ∨ a - u.re = b - u.im)) ∨
        ((m : Int) < b - u.im ∧ b - u.im < 2 * (m : Int) ∧
          (a - u.re = b - u.im - 2 * (m : Int) - 1 ∨
            a - u.re = 2 * (m : Int) - (b - u.im))))) :
      ({⟨a, b⟩, ⟨a + 1, b⟩} : Finset GaussianInt) ∈
        BoundaryFootprintEdges (TileTranslation (DiamondTile m) u) := by
    rw [(TileTranslationFormulas (DiamondTile m) u).2.2.2.2.2.2.2.2]
    refine ⟨{⟨a - u.re, b - u.im⟩, ⟨a - u.re + 1, b - u.im⟩}, ?_, ?_⟩
    · rw [(P5124T1BoundaryGeometry m hm).1]
      exact ⟨a - u.re, b - u.im, Or.inl ⟨h, rfl⟩⟩
    · have h0 : GaussianTranslation u ⟨a - u.re, b - u.im⟩ = ⟨a, b⟩ := by
        ext <;> simp [GaussianTranslation]
      have h1 : GaussianTranslation u ⟨a - u.re + 1, b - u.im⟩ = ⟨a + 1, b⟩ := by
        ext <;> simp [GaussianTranslation]; ring
      simp only [Finset.image_insert, Finset.image_singleton, h0, h1]
  have ver (m : Nat) (hm : 0 < m) (u : GaussianInt) (a b : Int)
      (h : 0 ≤ b - u.im ∧ b - u.im < 2 * (m : Int) ∧
        (a - u.re = -min (b - u.im + 1) (2 * (m : Int) - (b - u.im)) ∨
         a - u.re = min (b - u.im + 1) (2 * (m : Int) - (b - u.im)))) :
      ({⟨a, b⟩, ⟨a, b + 1⟩} : Finset GaussianInt) ∈
        BoundaryFootprintEdges (TileTranslation (DiamondTile m) u) := by
    rw [(TileTranslationFormulas (DiamondTile m) u).2.2.2.2.2.2.2.2]
    refine ⟨{⟨a - u.re, b - u.im⟩, ⟨a - u.re, b - u.im + 1⟩}, ?_, ?_⟩
    · rw [(P5124T1BoundaryGeometry m hm).1]
      exact ⟨a - u.re, b - u.im, Or.inr ⟨h.1, h.2.1, h.2.2, rfl⟩⟩
    · have h0 : GaussianTranslation u ⟨a - u.re, b - u.im⟩ = ⟨a, b⟩ := by
        ext <;> simp [GaussianTranslation]
      have h1 : GaussianTranslation u ⟨a - u.re, b - u.im + 1⟩ = ⟨a, b + 1⟩ := by
        ext <;> simp [GaussianTranslation]; ring
      simp only [Finset.image_insert, Finset.image_singleton, h0, h1]
  have zero (m : Nat) : TileTranslation (DiamondTile m) 0 = DiamondTile m := by
    have h : GaussianTranslation (0 : GaussianInt) = id := by
      funext z
      simp [GaussianTranslation]
    simp [TileTranslation, h]
  have kp : 0 < k := by omega
  have np : 0 < k - 1 := by omega
  let p := P5157T1StaircasePoint 1 false 1
  let q := P5157T1StaircasePoint 1 false (-1)
  let r := P5157T1StaircasePoint ⟨-(k : Int), (k : Int) - 1⟩ true (-1)
  have pe (t : Nat) : p (2 * t) = ⟨1 + (t : Int), (t : Int)⟩ := by
    ext <;> simp [p, P5157T1StaircasePoint]; omega
  have po (t : Nat) : p (2 * t + 1) = ⟨1 + (t : Int), (t : Int) + 1⟩ := by
    ext <;> simp [p, P5157T1StaircasePoint] <;> omega
  have qe (t : Nat) : q (2 * t) = ⟨1 + (t : Int), -(t : Int)⟩ := by
    ext <;> simp [q, P5157T1StaircasePoint]; omega
  have qo (t : Nat) : q (2 * t + 1) = ⟨1 + (t : Int), -(t : Int) - 1⟩ := by
    ext <;> simp [q, P5157T1StaircasePoint] <;> omega
  have re (t : Nat) : r (2 * t) = ⟨-(k : Int) + t, (k : Int) - 1 - t⟩ := by
    ext <;> simp [r, P5157T1StaircasePoint] <;> omega
  have ro (t : Nat) : r (2 * t + 1) =
      ⟨-(k : Int) + t + 1, (k : Int) - 1 - t⟩ := by
    ext <;> simp [r, P5157T1StaircasePoint] <;> omega
  dsimp only
  change (∀ j < 2 * (k - 1), ({p j, p (j + 1)} : Finset GaussianInt) ∈ _ ∩ _) ∧
    (∀ j < 2 * (k - 1), ({q j, q (j + 1)} : Finset GaussianInt) ∈ _ ∩ _) ∧
    (∀ j < 2 * (k - 1), ({r j, r (j + 1)} : Finset GaussianInt) ∈ _ ∩ _)
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨t, ht | ht⟩ : ∃ t : Nat, j = 2 * t ∨ j = 2 * t + 1 :=
      ⟨j / 2, by omega⟩
    · subst j
      rw [pe, po]
      constructor
      · simpa only [zero] using ver k kp 0 (1 + t) t (by dsimp; omega)
      · exact ver (k - 1) np ⟨(k : Int), 1 - (k : Int)⟩
          (1 + t) t (by dsimp; omega)
    · subst j
      rw [show 2 * t + 1 + 1 = 2 * (t + 1) by omega, po, pe]
      have hcoord : (1 + ((t + 1 : Nat) : Int)) = (1 + (t : Int)) + 1 := by omega
      simp only [Nat.cast_add, Nat.cast_one] at hcoord ⊢
      constructor
      · simpa only [zero, hcoord] using hor k kp 0 (1 + t) (t + 1) (by dsimp; omega)
      · simpa only [hcoord] using hor (k - 1) np ⟨(k : Int), 1 - (k : Int)⟩
          (1 + t) (t + 1) (by dsimp; omega)
  · intro j hj
    obtain ⟨t, ht | ht⟩ : ∃ t : Nat, j = 2 * t ∨ j = 2 * t + 1 :=
      ⟨j / 2, by omega⟩
    · subst j
      rw [qe, qo, Finset.pair_comm]
      have hcoord : (⟨1 + (t : Int), -(t : Int) - 1 + 1⟩ : GaussianInt) =
          ⟨1 + (t : Int), -(t : Int)⟩ := by ext <;> simp
      constructor
      · simpa only [hcoord] using ver k kp ⟨0, -(2 * (k : Int))⟩
          (1 + t) (-(t : Int) - 1) (by dsimp; omega)
      · simpa only [hcoord] using ver (k - 1) np ⟨(k : Int), 1 - (k : Int)⟩
          (1 + t) (-(t : Int) - 1) (by dsimp; omega)
    · subst j
      rw [show 2 * t + 1 + 1 = 2 * (t + 1) by omega, qo, qe]
      have e : ({⟨1 + (t : Int), -(t : Int) - 1⟩,
          ⟨1 + ((t + 1 : Nat) : Int), -((t + 1 : Nat) : Int)⟩} : Finset GaussianInt) =
          {⟨1 + (t : Int), -(t : Int) - 1⟩,
           ⟨(1 + (t : Int)) + 1, -(t : Int) - 1⟩} := by
        have hx : (1 + ((t + 1 : Nat) : Int)) = (1 + (t : Int)) + 1 := by omega
        have hy : -((t + 1 : Nat) : Int) = -(t : Int) - 1 := by omega
        rw [hx, hy]
      rw [e]
      exact ⟨hor k kp ⟨0, -(2 * (k : Int))⟩ (1 + t) (-(t : Int) - 1)
          (by dsimp; omega),
        hor (k - 1) np ⟨(k : Int), 1 - (k : Int)⟩ (1 + t) (-(t : Int) - 1)
          (by dsimp; omega)⟩
  · intro j hj
    obtain ⟨t, ht | ht⟩ : ∃ t : Nat, j = 2 * t ∨ j = 2 * t + 1 :=
      ⟨j / 2, by omega⟩
    · subst j
      rw [re, ro]
      constructor
      · simpa only [zero] using hor k kp 0 (-(k : Int) + t) ((k : Int) - 1 - t)
          (by dsimp; omega)
      · exact hor (k - 1) np ⟨-(k : Int), 1 - (k : Int)⟩
          (-(k : Int) + t) ((k : Int) - 1 - t) (by dsimp; omega)
    · subst j
      rw [show 2 * t + 1 + 1 = 2 * (t + 1) by omega, ro, re, Finset.pair_comm]
      have e : ({⟨-(k : Int) + ((t + 1 : Nat) : Int),
              (k : Int) - 1 - ((t + 1 : Nat) : Int)⟩,
          ⟨-(k : Int) + t + 1, (k : Int) - 1 - t⟩} : Finset GaussianInt) =
          {⟨-(k : Int) + t + 1, (k : Int) - 2 - t⟩,
           ⟨-(k : Int) + t + 1, ((k : Int) - 2 - t) + 1⟩} := by
        have hx : -(k : Int) + ((t + 1 : Nat) : Int) = -(k : Int) + t + 1 := by omega
        have hy : (k : Int) - 1 - ((t + 1 : Nat) : Int) = (k : Int) - 2 - t := by omega
        have hy' : (k : Int) - 1 - t = ((k : Int) - 2 - t) + 1 := by omega
        rw [hx, hy, hy']
      rw [e]
      constructor
      · simpa only [zero] using ver k kp 0 (-(k : Int) + t + 1) ((k : Int) - 2 - t)
          (by dsimp; omega)
      · exact ver (k - 1) np ⟨-(k : Int), 1 - (k : Int)⟩
          (-(k : Int) + t + 1) ((k : Int) - 2 - t) (by dsimp; omega)

end ApollonianSuperharmonic

end
