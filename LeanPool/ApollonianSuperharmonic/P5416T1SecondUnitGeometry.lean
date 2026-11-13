/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5352T2PlacementData
public import LeanPool.ApollonianSuperharmonic.P5352T2DomainRows
public import LeanPool.ApollonianSuperharmonic.P5352T2Sources

-- [TABLET NODE: P5416T1SecondUnitGeometry]

/-!
# P5416T1SecondUnitGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5416T1SecondUnitGeometry (K : DiamondParameter) (hk : 1 < K.1)
    (s : Fin 4) (z : GaussianInt) :
    let d := ((P5352T2PlacementData K.1 1).2 s).1
    let r := ((P5352T2PlacementData K.1 1).2 s).2.2
    z ∈ FootprintVertices (DiamondTile K.1) →
    z - d ∈ FootprintVertices (P5352T2Sources K hk 2).1 →
    (∀ y, y = z ∨ y = z + 1 ∨ y = z - 1 ∨
          y = z + ⟨0, 1⟩ ∨ y = z - ⟨0, 1⟩ →
      y ∈ FootprintVertices (DiamondTile K.1) ∨
        y - d ∈ FootprintVertices (P5352T2Sources K hk 2).1) →
    z = ![⟨-(K.1 : Int), (K.1 : Int)⟩, ⟨0, 0⟩,
      ⟨(K.1 : Int), (K.1 : Int)⟩, ⟨0, 2*(K.1 : Int)⟩] s ∧
    (z - r ∈ FootprintVertices (DiamondTile K.1) ↔ s = 1 ∨ s = 3) := by
-- BODY
  classical
  let k : Int := K.1
  let C (p q : Int) : Prop :=
    0 ≤ q ∧ q ≤ 2*k ∧ -k ≤ p ∧ p ≤ k ∧
      -q-1 ≤ p ∧ p ≤ q+1 ∧ -(2*k-q+1) ≤ p ∧ p ≤ 2*k-q+1
  let U (p q : Int) : Prop := 0 ≤ p ∧ p ≤ 1 ∧ 0 ≤ q ∧ q ≤ 1
  have cmem (x : GaussianInt) :
      x ∈ FootprintVertices (DiamondTile K.1) ↔ C x.re x.im :=
    (P5352T2DomainRows K x).1
  have umem (x : GaussianInt) :
      x ∈ FootprintVertices (P5352T2Sources K hk 2).1 ↔ U x.re x.im := by
    simp only [P5352T2Sources, Matrix.cons_val_two]
    simp [FootprintVertices]
    simp only [Zsqrtd.ext_iff, Zsqrtd.re_zero, Zsqrtd.im_zero,
      Zsqrtd.re_one, Zsqrtd.im_one, Zsqrtd.re_add, Zsqrtd.im_add]
    dsimp [U]
    omega
  dsimp only
  intro hzA hzP hcov
  have center := (cmem z).mp hzA
  have unitCenter := (umem _).mp hzP
  let d := ((P5352T2PlacementData K.1 1).2 s).1
  have covered (p q : Int)
      (h : (⟨p,q⟩ : GaussianInt) = z ∨ ⟨p,q⟩ = z+1 ∨ ⟨p,q⟩ = z-1 ∨
        ⟨p,q⟩ = z+⟨0,1⟩ ∨ ⟨p,q⟩ = z-⟨0,1⟩) :
      C p q ∨ U (p-d.re) (q-d.im) := by
    rcases hcov _ h with h | h
    · exact Or.inl ((cmem _).mp h)
    · exact Or.inr ((umem _).mp h)
  clear hzA hzP hcov umem
  fin_cases s
  · have hs := covered z.re (z.im-1)
      (Or.inr (Or.inr (Or.inr (Or.inr (by ext <;> simp)))))
    change U (z.re-(-k-1)) (z.im-(k-1)) at unitCenter
    change C z.re (z.im-1) ∨ U (z.re-(-k-1)) (z.im-1-(k-1)) at hs
    have hz : z = ⟨-k,k⟩ := by
      dsimp [C, U] at center unitCenter hs
      ext <;> dsimp <;> omega
    subst z
    refine ⟨rfl, ?_⟩
    rw [cmem]
    change C (-k-(-k)) (k-(-k-1)) ↔ (0 : Fin 4) = 1 ∨ (0 : Fin 4) = 3
    norm_num
    dsimp [C]
    omega
  · have he := covered (z.re+1) z.im (Or.inr (Or.inl (by ext <;> simp)))
    change U (z.re-0) (z.im-(-1)) at unitCenter
    change C (z.re+1) z.im ∨ U (z.re+1-0) (z.im-(-1)) at he
    have hz : z = ⟨0,0⟩ := by
      dsimp [C, U] at center unitCenter he
      ext <;> dsimp <;> omega
    subst z
    refine ⟨rfl, ?_⟩
    rw [cmem]
    change C (0-(-k)) (0-(-k-1)) ↔ (1 : Fin 4) = 1 ∨ (1 : Fin 4) = 3
    norm_num
    dsimp [C]
    omega
  · have hn := covered z.re (z.im+1)
      (Or.inr (Or.inr (Or.inr (Or.inl (by ext <;> simp)))))
    change U (z.re-k) (z.im-k) at unitCenter
    change C z.re (z.im+1) ∨ U (z.re-k) (z.im+1-k) at hn
    have hz : z = ⟨k,k⟩ := by
      dsimp [C, U] at center unitCenter hn
      ext <;> dsimp <;> omega
    subst z
    refine ⟨rfl, ?_⟩
    rw [cmem]
    change C (k-k) (k-(k+1)) ↔ (2 : Fin 4) = 1 ∨ (2 : Fin 4) = 3
    norm_num
    dsimp [C]
    omega
  · have hw := covered (z.re-1) z.im
      (Or.inr (Or.inr (Or.inl (by ext <;> simp))))
    change U (z.re-(-1)) (z.im-2*k) at unitCenter
    change C (z.re-1) z.im ∨ U (z.re-1-(-1)) (z.im-2*k) at hw
    have hz : z = ⟨0,2*k⟩ := by
      dsimp [C, U] at center unitCenter hw
      ext <;> dsimp <;> omega
    subst z
    refine ⟨rfl, ?_⟩
    rw [cmem]
    change C (0-k) (2*k-(k+1)) ↔ (3 : Fin 4) = 1 ∨ (3 : Fin 4) = 3
    norm_num
    dsimp [C]
    omega

end ApollonianSuperharmonic

end
