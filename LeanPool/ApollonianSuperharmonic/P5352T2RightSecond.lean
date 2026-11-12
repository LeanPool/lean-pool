/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5352T2PlacementData
public import LeanPool.ApollonianSuperharmonic.P5352T2DomainRows
public import LeanPool.ApollonianSuperharmonic.P4207T1FloorArithmetic
public import LeanPool.ApollonianSuperharmonic.DiamondLaplacianTable

-- [TABLET NODE: P5352T2RightSecond]

/-!
# P5352T2RightSecond

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace DiamondRightSecond

private theorem fourCells :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, -k-1⟩
        let covered (x : GaussianInt) : Prop :=
          ∀ y, y=x ∨ y=x-1 ∨ y=x-⟨0,1⟩ ∨ y=x-1-⟨0,1⟩ →
            y ∈ DiamondCellDomain K.1 ∨ y-rho ∈ DiamondCellDomain K.1
        ∀ (x : GaussianInt), covered x ↔ (x ∈ DiamondCellDomain K.1 ∨ x - rho ∈ DiamondCellDomain
            K.1) ∧ (x - (1 : GaussianInt) ∈ DiamondCellDomain K.1 ∨ x - (1 : GaussianInt) - rho ∈
            DiamondCellDomain K.1) ∧ (x - ⟨(0 : ℤ), (1 : ℤ)⟩ ∈ DiamondCellDomain K.1 ∨ x - ⟨(0 :
            ℤ), (1 : ℤ)⟩ - rho ∈ DiamondCellDomain K.1) ∧ (x - (1 : GaussianInt) - ⟨(0 : ℤ), (1 :
            ℤ)⟩ ∈ DiamondCellDomain K.1 ∨ x - (1 : GaussianInt) - ⟨(0 : ℤ), (1 : ℤ)⟩ - rho ∈
            DiamondCellDomain K.1) ) := by
  classical
  intro K k rho covered x
  constructor
  · intro h
    exact ⟨h x (Or.inl rfl), h (x-1) (Or.inr (Or.inl rfl)),
      h (x-⟨0,1⟩) (Or.inr (Or.inr (Or.inl rfl))),
      h (x-1-⟨0,1⟩) (Or.inr (Or.inr (Or.inr rfl)))⟩
  · rintro ⟨h0,h1,h2,h3⟩ y (rfl | rfl | rfl | rfl)
    · exact h0
    · exact h1
    · exact h2
    · exact h3

private theorem contact :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (z : GaussianInt),
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, -k-1⟩
        (z ∈ FootprintVertices (DiamondTile K.1)) → ((z - rho ∈ FootprintVertices (DiamondTile
            K.1)) → ((∀ (x : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) ↔ 0 ≤ x.im ∧
            x.im ≤ 2*k ∧ -k ≤ x.re ∧ x.re ≤ k ∧ -x.im-1 ≤ x.re ∧ x.re ≤ x.im+1 ∧ -(2*k-x.im+1) ≤
            x.re ∧ x.re ≤ 2*k-x.im+1) → ((∃ t : Int, 0 ≤ t ∧ t < k ∧ z = ⟨-1-t,t⟩) ∨ (∃ t : Int,
            0 ≤ t ∧ t < k ∧ z = ⟨-t,t⟩)))) ) := by
  classical
  intro K z k rho hz hzR foot
  have h0 := (foot z).mp hz
  have h1 := (foot (z-rho)).mp hzR
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub] at h1
  dsimp [rho] at h1
  have hd : z.re+z.im = -1 ∨ z.re+z.im = 0 := by omega
  rcases hd with hd | hd
  · left
    refine ⟨z.im, by omega, by omega, ?_⟩
    ext <;> dsimp; omega
  · right
    refine ⟨z.im, by omega, by omega, ?_⟩
    ext <;> dsimp; omega

private theorem cellsA :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, -k-1⟩
        let covered (x : GaussianInt) : Prop :=
          ∀ y, y=x ∨ y=x-1 ∨ y=x-⟨0,1⟩ ∨ y=x-1-⟨0,1⟩ →
            y ∈ DiamondCellDomain K.1 ∨ y-rho ∈ DiamondCellDomain K.1
        (∀ (x : GaussianInt), x ∈ DiamondCellDomain K.1 ↔ 0 ≤ x.im ∧ x.im < 2*k ∧ -(x.im+1) ≤
            x.re ∧ x.re < x.im+1 ∧ -(2*k-x.im) ≤ x.re ∧ x.re < 2*k-x.im) → ((∀ (x : GaussianInt),
            covered x ↔ (x ∈ DiamondCellDomain K.1 ∨ x-rho ∈ DiamondCellDomain K.1) ∧ (x-1 ∈
            DiamondCellDomain K.1 ∨ x-1-rho ∈ DiamondCellDomain K.1) ∧ (x-⟨0,1⟩ ∈
            DiamondCellDomain K.1 ∨ x-⟨0,1⟩-rho ∈ DiamondCellDomain K.1) ∧ (x-1-⟨0,1⟩ ∈
            DiamondCellDomain K.1 ∨ x-1-⟨0,1⟩-rho ∈ DiamondCellDomain K.1)) → (∀ (t : ℤ), (0 : ℤ)
            ≤ t → t < k → (covered ⟨(-1 : ℤ) - t, t⟩ ↔ t + (1 : ℤ) < k)))) ) := by
  classical
  intro K hk k rho covered cell fourCells t ht0 htk
  rw [fourCells]
  simp only [cell, Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one]
  dsimp [rho]
  omega

private theorem cellsB :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, -k-1⟩
        let covered (x : GaussianInt) : Prop :=
          ∀ y, y=x ∨ y=x-1 ∨ y=x-⟨0,1⟩ ∨ y=x-1-⟨0,1⟩ →
            y ∈ DiamondCellDomain K.1 ∨ y-rho ∈ DiamondCellDomain K.1
        (∀ (x : GaussianInt), x ∈ DiamondCellDomain K.1 ↔ 0 ≤ x.im ∧ x.im < 2*k ∧ -(x.im+1) ≤
            x.re ∧ x.re < x.im+1 ∧ -(2*k-x.im) ≤ x.re ∧ x.re < 2*k-x.im) → ((∀ (x : GaussianInt),
            covered x ↔ (x ∈ DiamondCellDomain K.1 ∨ x-rho ∈ DiamondCellDomain K.1) ∧ (x-1 ∈
            DiamondCellDomain K.1 ∨ x-1-rho ∈ DiamondCellDomain K.1) ∧ (x-⟨0,1⟩ ∈
            DiamondCellDomain K.1 ∨ x-⟨0,1⟩-rho ∈ DiamondCellDomain K.1) ∧ (x-1-⟨0,1⟩ ∈
            DiamondCellDomain K.1 ∨ x-1-⟨0,1⟩-rho ∈ DiamondCellDomain K.1)) → (∀ (t : ℤ), (0 : ℤ)
            ≤ t → t < k → (covered ⟨-t, t⟩ ↔ (0 : ℤ) < t)))) ) := by
  classical
  intro K hk k rho covered cell fourCells t ht0 htk
  rw [fourCells]
  simp only [cell, Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one]
  dsimp [rho]
  omega

private theorem footAE :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        (∀ (x : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) ↔ 0 ≤ x.im ∧ x.im ≤ 2*k ∧
            -k ≤ x.re ∧ x.re ≤ k ∧ -x.im-1 ≤ x.re ∧ x.re ≤ x.im+1 ∧ -(2*k-x.im+1) ≤ x.re ∧ x.re ≤
            2*k-x.im+1) → (∀ (t : ℤ), (0 : ℤ) ≤ t → t < k → ⟨(-1 : ℤ) - t, t⟩ + (1 : ℤ√(-1 : ℤ))
            ∈ FootprintVertices (DiamondTile K.1))) ) := by
  classical
  intro K hk k foot t ht0 htk
  rw [foot]
  simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one]
  omega

private theorem footAN :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        (∀ (x : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) ↔ 0 ≤ x.im ∧ x.im ≤ 2*k ∧
            -k ≤ x.re ∧ x.re ≤ k ∧ -x.im-1 ≤ x.re ∧ x.re ≤ x.im+1 ∧ -(2*k-x.im+1) ≤ x.re ∧ x.re ≤
            2*k-x.im+1) → (∀ (t : ℤ), (0 : ℤ) ≤ t → t < k → ⟨(-1 : ℤ) - t, t⟩ + ⟨(0 : ℤ), (1 :
            ℤ)⟩ ∈ FootprintVertices (DiamondTile K.1))) ) := by
  classical
  intro K hk k foot t ht0 htk
  rw [foot]
  simp only [Zsqrtd.re_add, Zsqrtd.im_add]
  omega

private theorem footAW :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, -k-1⟩
        (∀ (x : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) ↔ 0 ≤ x.im ∧ x.im ≤ 2*k ∧
            -k ≤ x.re ∧ x.re ≤ k ∧ -x.im-1 ≤ x.re ∧ x.re ≤ x.im+1 ∧ -(2*k-x.im+1) ≤ x.re ∧ x.re ≤
            2*k-x.im+1) → (∀ (t : ℤ), (0 : ℤ) ≤ t → t < k → ⟨(-1 : ℤ) - t, t⟩ - (1 : ℤ√(-1 : ℤ))
            - rho ∈ FootprintVertices (DiamondTile K.1))) ) := by
  classical
  intro K hk k rho foot t ht0 htk
  rw [foot]
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one]
  dsimp [rho]
  omega

private theorem footAS :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, -k-1⟩
        (∀ (x : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) ↔ 0 ≤ x.im ∧ x.im ≤ 2*k ∧
            -k ≤ x.re ∧ x.re ≤ k ∧ -x.im-1 ≤ x.re ∧ x.re ≤ x.im+1 ∧ -(2*k-x.im+1) ≤ x.re ∧ x.re ≤
            2*k-x.im+1) → (∀ (t : ℤ), (0 : ℤ) ≤ t → t < k → ⟨(-1 : ℤ) - t, t⟩ - ⟨(0 : ℤ), (1 :
            ℤ)⟩ - rho ∈ FootprintVertices (DiamondTile K.1))) ) := by
  classical
  intro K hk k rho foot t ht0 htk
  rw [foot]
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
  dsimp [rho]
  omega

private theorem footBE :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        (∀ (x : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) ↔ 0 ≤ x.im ∧ x.im ≤ 2*k ∧
            -k ≤ x.re ∧ x.re ≤ k ∧ -x.im-1 ≤ x.re ∧ x.re ≤ x.im+1 ∧ -(2*k-x.im+1) ≤ x.re ∧ x.re ≤
            2*k-x.im+1) → (∀ (t : ℤ), (0 : ℤ) ≤ t → t < k → ⟨-t, t⟩ + (1 : ℤ√(-1 : ℤ)) ∈
            FootprintVertices (DiamondTile K.1))) ) := by
  classical
  intro K hk k foot t ht0 htk
  rw [foot]
  simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one]
  omega

private theorem footBW :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        (∀ (x : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) ↔ 0 ≤ x.im ∧ x.im ≤ 2*k ∧
            -k ≤ x.re ∧ x.re ≤ k ∧ -x.im-1 ≤ x.re ∧ x.re ≤ x.im+1 ∧ -(2*k-x.im+1) ≤ x.re ∧ x.re ≤
            2*k-x.im+1) → (∀ (t : ℤ), (0 : ℤ) ≤ t → t < k → ⟨-t, t⟩ - (1 : ℤ√(-1 : ℤ)) ∈
            FootprintVertices (DiamondTile K.1))) ) := by
  classical
  intro K hk k foot t ht0 htk
  rw [foot]
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one]
  omega

private theorem footBN :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        (∀ (x : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) ↔ 0 ≤ x.im ∧ x.im ≤ 2*k ∧
            -k ≤ x.re ∧ x.re ≤ k ∧ -x.im-1 ≤ x.re ∧ x.re ≤ x.im+1 ∧ -(2*k-x.im+1) ≤ x.re ∧ x.re ≤
            2*k-x.im+1) → (∀ (t : ℤ), (0 : ℤ) ≤ t → t < k → ⟨-t, t⟩ + ⟨(0 : ℤ), (1 : ℤ)⟩ ∈
            FootprintVertices (DiamondTile K.1))) ) := by
  classical
  intro K hk k foot t ht0 htk
  rw [foot]
  simp only [Zsqrtd.re_add, Zsqrtd.im_add]
  omega

private theorem footBS :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, -k-1⟩
        (∀ (x : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) ↔ 0 ≤ x.im ∧ x.im ≤ 2*k ∧
            -k ≤ x.re ∧ x.re ≤ k ∧ -x.im-1 ≤ x.re ∧ x.re ≤ x.im+1 ∧ -(2*k-x.im+1) ≤ x.re ∧ x.re ≤
            2*k-x.im+1) → (∀ (t : ℤ), (0 : ℤ) ≤ t → t < k → ⟨-t, t⟩ - ⟨(0 : ℤ), (1 : ℤ)⟩ - rho ∈
            FootprintVertices (DiamondTile K.1))) ) := by
  classical
  intro K hk k rho foot t ht0 htk
  rw [foot]
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
  dsimp [rho]
  omega

private theorem tri :
    (by
      classical
      exact
        (DiamondParameter) → (∀ (a : ℤ), (2 : ℤ) * (a * (a - (1 : ℤ)) / (2 : ℤ)) = a * (a - (1 :
            ℤ))) ) := by
  classical
  intro K a
  rcases Int.emod_two_eq_zero_or_one a with h | h
  · have ha : a = 2*(a/2) := by omega
    rw [ha]
    rw [show 2*(a/2)*(2*(a/2)-1) = 2*((a/2)*(2*(a/2)-1)) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num : (2:Int) ≠ 0)]
  · have ha : a = 2*(a/2)+1 := by omega
    rw [ha]
    rw [show (2*(a/2)+1)*(2*(a/2)+1-1) = 2*((2*(a/2)+1)*(a/2)) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num : (2:Int) ≠ 0)]

private theorem square :
    (by
      classical
      exact
        (DiamondParameter) → (∀ (a : ℤ), (4 : ℤ) * (a ^ (2 : ℕ) / (4 : ℤ)) = a ^ (2 : ℕ) - a % (2
            : ℤ)) ) := by
  classical
  intro K a
  rcases Int.emod_two_eq_zero_or_one a with h | h
  · have ha : a = 2*(a/2) := by omega
    have he : a^2 = 4*(a/2)^2 := by
      conv_lhs => rw [ha]
      ring
    rw [he, Int.mul_ediv_cancel_left _ (by norm_num : (4:Int) ≠ 0), h]
    ring
  · have ha : a = 2*(a/2)+1 := by omega
    have he : a^2 = 4*((a/2)^2+a/2)+1 := by
      conv_lhs => rw [ha]
      ring
    rw [he, h]
    omega

private theorem scale :
    (by
      classical
      exact
        let Q (a b : Int) : Int :=
          (Int.natAbs a : Int)*((Int.natAbs a : Int)-1)/2-(a-b)^2/4
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        (∀ (a : Int), 2*(a*(a-1)/2) = a*(a-1)) → ((∀ (a : Int), 4*(a^2/4) = a^2-a%2) → (∀ (a :
            ℤ), ∀ (b : ℤ), (4 : ℤ) * Q a b = S a b)) ) := by
  classical
  intro Q S tri square a b
  have ht := tri (Int.natAbs a : Int)
  have hs := square (a-b)
  have ha : (Int.natAbs a : Int)^2 = a^2 := by
    rw [Int.natCast_natAbs, sq_abs]
  dsimp [Q, S]
  rw [Int.natCast_natAbs] at ht ha ⊢
  nlinarith only [ht, hs, ha]

private theorem sEven :
    (by
      classical
      exact
        (DiamondParameter) → (
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        ∀ (a : ℤ), ∀ (b : ℤ), ∀ (m : ℤ), a - b = (2 : ℤ) * m → S a b = (2 : ℤ) * a ^ (2 : ℕ) - (2
            : ℤ) * |a| - (4 : ℤ) * m ^ (2 : ℕ)) ) := by
  classical
  intro K S a b m h
  dsimp [S]
  rw [h, show (2*m)%2 = 0 by omega]
  ring

private theorem sOdd :
    (by
      classical
      exact
        (DiamondParameter) → (
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        ∀ (a : ℤ), ∀ (b : ℤ), ∀ (m : ℤ), a - b = (2 : ℤ) * m + (1 : ℤ) → S a b = (2 : ℤ) * a ^ (2
            : ℕ) - (2 : ℤ) * |a| - (4 : ℤ) * m ^ (2 : ℕ) - (4 : ℤ) * m) ) := by
  classical
  intro K S a b m h
  dsimp [S]
  rw [h, show (2*m+1)%2 = 1 by omega]
  ring

private theorem valR :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, -k-1⟩
        (∀ (y : GaussianInt), y - rho ∈ FootprintVertices (DiamondTile K.1) → f y =
            DiamondOdometer K (y - rho) + -k * y.re + B) → (
        let Q (a b : Int) : Int :=
          (Int.natAbs a : Int)*((Int.natAbs a : Int)-1)/2-(a-b)^2/4
        ∀ (x : GaussianInt), x - rho ∈ FootprintVertices (DiamondTile K.1) → f x = Q (x - rho).re
            (x - rho).im - k * x.re + B) ) := by
  classical
  intro K f B k rho hR Q x hx
  rw [hR x hx, (P5352T2DomainRows K (x-rho)).2 hx]
  dsimp [Q]
  ring

private theorem diffC :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let Q (a b : Int) : Int :=
          (Int.natAbs a : Int)*((Int.natAbs a : Int)-1)/2-(a-b)^2/4
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        (∀ (a : Int), ∀ (b : Int), 4*Q a b = S a b) → ((∀ (x : GaussianInt), (x ∈
            FootprintVertices (DiamondTile K.1)) → (f x = Q x.re x.im)) → (∀ (x : GaussianInt), ∀
            (y : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) → y ∈ FootprintVertices
            (DiamondTile K.1) → (4 : ℤ) * (f y - f x) = S y.re y.im - S x.re x.im)) ) := by
  classical
  intro K f Q S scale valC x y hx hy
  rw [valC x hx, valC y hy]
  linear_combination scale y.re y.im - scale x.re x.im

private theorem diffR :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, -k-1⟩
        let Q (a b : Int) : Int :=
          (Int.natAbs a : Int)*((Int.natAbs a : Int)-1)/2-(a-b)^2/4
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        (∀ (a : Int), ∀ (b : Int), 4*Q a b = S a b) → ((∀ (x : GaussianInt), (x-rho ∈
            FootprintVertices (DiamondTile K.1)) → (f x = Q (x-rho).re (x-rho).im-k*x.re+B)) → (∀
            (x : GaussianInt), ∀ (y : GaussianInt), x - rho ∈ FootprintVertices (DiamondTile K.1)
            → y - rho ∈ FootprintVertices (DiamondTile K.1) → (4 : ℤ) * (f y - f x) = S (y -
            rho).re (y - rho).im - S (x - rho).re (x - rho).im - (4 : ℤ) * k * (y - x).re)) ) := by
  classical
  intro K f B k rho Q S scale valR x y hx hy
  rw [valR x hx, valR y hy]
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
  linear_combination scale (y.re-rho.re) (y.im-rho.im) -
    scale (x.re-rho.re) (x.im-rho.im)

private theorem lap :
    (by
      classical
      exact
        ∀ (f : IntegerLatticeFunction), ∀ (x : GaussianInt), FourNeighborLaplacian f x = f (x +
            (1 : GaussianInt)) - f x + (f (x - (1 : GaussianInt)) - f x) + (f (x + ⟨(0 : ℤ), (1 :
            ℤ)⟩) - f x) + (f (x - ⟨(0 : ℤ), (1 : ℤ)⟩) - f x) ) := by
  classical
  intro f x
  unfold FourNeighborLaplacian
  ring

private theorem eastAt316 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        (∀ (t : Int), (0 ≤ t) → ((t < k) → ((⟨-1-t,t⟩ : GaussianInt)+1 ∈ FootprintVertices
            (DiamondTile K.1)))) → (
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        (∀ (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m) → (S a b = 2*a^2-2*|a|-4*m^2)) → ((∀
            (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m+1) → (S a b = 2*a^2-2*|a|-4*m^2-4*m))
            → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), (x ∈ FootprintVertices (DiamondTile
            K.1)) → ((y ∈ FootprintVertices (DiamondTile K.1)) → (4*(f y-f x) = S y.re y.im-S
            x.re x.im))) → (∀ (t : ℤ), ((0 : ℤ) ≤ t) → ((t < k) → ((⟨(-1 : ℤ) - t, t⟩ ∈
            FootprintVertices (DiamondTile K.1)) → (f ((⟨-1-t,t⟩ : GaussianInt)+1)-f ⟨-1-t,t⟩ =
            0))))))) ) := by
  classical
  intro K f k footAE S sEven sOdd diffC t ht0 htk hz
  have h := diffC _ _ hz (footAE t ht0 htk)
  rw [sEven _ _ (-t) (by dsimp; ring), sOdd _ _ (-t-1) (by dsimp; ring)] at h
  simp only [Zsqrtd.re_add, Zsqrtd.re_one] at h
  simp (disch := omega) only [abs_of_nonpos] at h
  nlinarith only [h]

private theorem northAt322 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        (∀ (t : Int), (0 ≤ t) → ((t < k) → ((⟨-1-t,t⟩ : GaussianInt)+⟨0,1⟩ ∈ FootprintVertices
            (DiamondTile K.1)))) → (
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        (∀ (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m) → (S a b = 2*a^2-2*|a|-4*m^2)) → ((∀
            (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m+1) → (S a b = 2*a^2-2*|a|-4*m^2-4*m))
            → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), (x ∈ FootprintVertices (DiamondTile
            K.1)) → ((y ∈ FootprintVertices (DiamondTile K.1)) → (4*(f y-f x) = S y.re y.im-S
            x.re x.im))) → (∀ (t : ℤ), ((0 : ℤ) ≤ t) → ((t < k) → ((⟨(-1 : ℤ) - t, t⟩ ∈
            FootprintVertices (DiamondTile K.1)) → (f ((⟨-1-t,t⟩ : GaussianInt)+⟨0,1⟩)-f ⟨-1-t,t⟩
            = -t-1))))))) ) := by
  classical
  intro K f k footAN S sEven sOdd diffC t ht0 htk hz
  have h := diffC _ _ hz (footAN t ht0 htk)
  rw [sEven _ _ (-t-1) (by dsimp; ring), sOdd _ _ (-t-1) (by dsimp; ring)] at h
  simp only [Zsqrtd.re_add] at h
  simp (disch := omega) only [abs_of_nonpos] at h
  nlinarith only [h]

private theorem westAt328 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, -k-1⟩
        (∀ (t : Int), (0 ≤ t) → ((t < k) → ((⟨-1-t,t⟩ : GaussianInt)-1-rho ∈ FootprintVertices
            (DiamondTile K.1)))) → (
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        (∀ (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m) → (S a b = 2*a^2-2*|a|-4*m^2)) → ((∀
            (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m+1) → (S a b = 2*a^2-2*|a|-4*m^2-4*m))
            → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), (x-rho ∈ FootprintVertices (DiamondTile
            K.1)) → ((y-rho ∈ FootprintVertices (DiamondTile K.1)) → (4*(f y-f x) = S (y-rho).re
            (y-rho).im-S (x-rho).re (x-rho).im - 4*k*(y-x).re))) → (∀ (t : ℤ), ((0 : ℤ) ≤ t) →
            ((t < k) → ((⟨(-1 : ℤ) - t, t⟩ - rho ∈ FootprintVertices (DiamondTile K.1)) → ((f
            ((⟨-1-t,t⟩ : GaussianInt)+⟨0,1⟩)-f ⟨-1-t,t⟩ = -t-1) → (f ((⟨-1-t,t⟩ :
            GaussianInt)-1)-f ⟨-1-t,t⟩ = if t+1=k then 0 else 1)))))))) ) := by
  classical
  intro K f k rho footAW S sEven sOdd diffR t ht0 htk hzR north
  have h := diffR _ _ hzR (footAW t ht0 htk)
  rw [sOdd _ _ (-t-2) (by dsimp [rho]; ring),
    sEven _ _ (-t-1) (by dsimp [rho]; ring)] at h
  simp only [rho, Zsqrtd.re_sub, Zsqrtd.re_one] at h
  by_cases ht : t+1=k
  · rw [ite_eq_left ht]
    simp (disch := omega) only [abs_of_nonpos] at h
    nlinarith only [h, ht]
  · rw [ite_eq_right ht]
    simp (disch := omega) only [abs_of_nonneg] at h
    nlinarith only [h]

private theorem southAt341 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, -k-1⟩
        (∀ (t : Int), (0 ≤ t) → ((t < k) → ((⟨-1-t,t⟩ : GaussianInt)-⟨0,1⟩-rho ∈
            FootprintVertices (DiamondTile K.1)))) → (
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        (∀ (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m) → (S a b = 2*a^2-2*|a|-4*m^2)) → ((∀
            (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m+1) → (S a b = 2*a^2-2*|a|-4*m^2-4*m))
            → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), (x-rho ∈ FootprintVertices (DiamondTile
            K.1)) → ((y-rho ∈ FootprintVertices (DiamondTile K.1)) → (4*(f y-f x) = S (y-rho).re
            (y-rho).im-S (x-rho).re (x-rho).im - 4*k*(y-x).re))) → (∀ (t : ℤ), ((0 : ℤ) ≤ t) →
            ((t < k) → ((⟨(-1 : ℤ) - t, t⟩ - rho ∈ FootprintVertices (DiamondTile K.1)) → ((f
            ((⟨-1-t,t⟩ : GaussianInt)+⟨0,1⟩)-f ⟨-1-t,t⟩ = -t-1) → ((f ((⟨-1-t,t⟩ :
            GaussianInt)-1)-f ⟨-1-t,t⟩ = if t+1=k then 0 else 1) → (f ((⟨-1-t,t⟩ :
            GaussianInt)-⟨0,1⟩)-f ⟨-1-t,t⟩ = t+1))))))))) ) := by
  classical
  intro K f k rho footAS S sEven sOdd diffR t ht0 htk hzR north west
  have h := diffR _ _ hzR (footAS t ht0 htk)
  rw [sOdd _ _ (-t-1) (by dsimp [rho]; ring),
    sEven _ _ (-t-1) (by dsimp [rho]; ring)] at h
  simp only [rho, Zsqrtd.re_sub] at h
  simp (disch := omega) only [abs_of_nonneg] at h
  nlinarith only [h]

private theorem htAt355 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, -k-1⟩
        let covered (x : GaussianInt) : Prop :=
          ∀ y, y=x ∨ y=x-1 ∨ y=x-⟨0,1⟩ ∨ y=x-1-⟨0,1⟩ →
            y ∈ DiamondCellDomain K.1 ∨ y-rho ∈ DiamondCellDomain K.1
        ∀ (t : ℤ), (t < k) → ((covered ⟨(-1 : ℤ) - t, t⟩ ↔ t + (1 : ℤ) < k) → ((f ((⟨-1-t,t⟩ :
            GaussianInt)+⟨0,1⟩)-f ⟨-1-t,t⟩ = -t-1) → ((f ((⟨-1-t,t⟩ : GaussianInt)-1)-f ⟨-1-t,t⟩
            = if t+1=k then 0 else 1) → ((f ((⟨-1-t,t⟩ : GaussianInt)-⟨0,1⟩)-f ⟨-1-t,t⟩ = t+1) →
            ((¬covered ⟨(-1 : ℤ) - t, t⟩) → (t+1 = k)))))) ) := by
  classical
  intro K f k rho covered t htk cells north west south hc
  have : ¬ t+1 < k := fun ht => hc (cells.mpr ht)
  omega

private theorem eastAt361 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        (∀ (t : Int), (0 ≤ t) → ((t < k) → ((⟨-t,t⟩ : GaussianInt)+1 ∈ FootprintVertices
            (DiamondTile K.1)))) → (
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        (∀ (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m) → (S a b = 2*a^2-2*|a|-4*m^2)) → ((∀
            (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m+1) → (S a b = 2*a^2-2*|a|-4*m^2-4*m))
            → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), (x ∈ FootprintVertices (DiamondTile
            K.1)) → ((y ∈ FootprintVertices (DiamondTile K.1)) → (4*(f y-f x) = S y.re y.im-S
            x.re x.im))) → (∀ (t : ℤ), ((0 : ℤ) ≤ t) → ((t < k) → ((⟨-t, t⟩ ∈ FootprintVertices
            (DiamondTile K.1)) → (f ((⟨-t,t⟩ : GaussianInt)+1)-f ⟨-t,t⟩ = if t=0 then 0 else
            1))))))) ) := by
  classical
  intro K f k footBE S sEven sOdd diffC t ht0 htk hz
  have h := diffC _ _ hz (footBE t ht0 htk)
  rw [sOdd _ _ (-t) (by dsimp; ring), sEven _ _ (-t) (by dsimp; ring)] at h
  simp only [Zsqrtd.re_add, Zsqrtd.re_one] at h
  by_cases ht : t=0
  · rw [ite_eq_left ht]
    simp (disch := omega) only [abs_of_nonneg] at h
    nlinarith only [h, ht]
  · rw [ite_eq_right ht]
    simp (disch := omega) only [abs_of_nonpos] at h
    nlinarith only [h]

private theorem westAt373 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        (∀ (t : Int), (0 ≤ t) → ((t < k) → ((⟨-t,t⟩ : GaussianInt)-1 ∈ FootprintVertices
            (DiamondTile K.1)))) → (
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        (∀ (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m) → (S a b = 2*a^2-2*|a|-4*m^2)) → ((∀
            (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m+1) → (S a b = 2*a^2-2*|a|-4*m^2-4*m))
            → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), (x ∈ FootprintVertices (DiamondTile
            K.1)) → ((y ∈ FootprintVertices (DiamondTile K.1)) → (4*(f y-f x) = S y.re y.im-S
            x.re x.im))) → (∀ (t : ℤ), ((0 : ℤ) ≤ t) → ((t < k) → ((⟨-t, t⟩ ∈ FootprintVertices
            (DiamondTile K.1)) → (f ((⟨-t,t⟩ : GaussianInt)-1)-f ⟨-t,t⟩ = 0))))))) ) := by
  classical
  intro K f k footBW S sEven sOdd diffC t ht0 htk hz
  have h := diffC _ _ hz (footBW t ht0 htk)
  rw [sOdd _ _ (-t-1) (by dsimp; ring), sEven _ _ (-t) (by dsimp; ring)] at h
  simp only [Zsqrtd.re_sub, Zsqrtd.re_one] at h
  simp (disch := omega) only [abs_of_nonpos] at h
  nlinarith only [h]

private theorem northAt379 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        (∀ (t : Int), (0 ≤ t) → ((t < k) → ((⟨-t,t⟩ : GaussianInt)+⟨0,1⟩ ∈ FootprintVertices
            (DiamondTile K.1)))) → (
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        (∀ (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m) → (S a b = 2*a^2-2*|a|-4*m^2)) → ((∀
            (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m+1) → (S a b = 2*a^2-2*|a|-4*m^2-4*m))
            → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), (x ∈ FootprintVertices (DiamondTile
            K.1)) → ((y ∈ FootprintVertices (DiamondTile K.1)) → (4*(f y-f x) = S y.re y.im-S
            x.re x.im))) → (∀ (t : ℤ), ((0 : ℤ) ≤ t) → ((t < k) → ((⟨-t, t⟩ ∈ FootprintVertices
            (DiamondTile K.1)) → (f ((⟨-t,t⟩ : GaussianInt)+⟨0,1⟩)-f ⟨-t,t⟩ = -t))))))) ) := by
  classical
  intro K f k footBN S sEven sOdd diffC t ht0 htk hz
  have h := diffC _ _ hz (footBN t ht0 htk)
  rw [sOdd _ _ (-t-1) (by dsimp; ring), sEven _ _ (-t) (by dsimp; ring)] at h
  simp only [Zsqrtd.re_add] at h
  simp (disch := omega) only [abs_of_nonpos] at h
  nlinarith only [h]

private theorem southAt385 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, -k-1⟩
        (∀ (t : Int), (0 ≤ t) → ((t < k) → ((⟨-t,t⟩ : GaussianInt)-⟨0,1⟩-rho ∈ FootprintVertices
            (DiamondTile K.1)))) → (
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        (∀ (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m) → (S a b = 2*a^2-2*|a|-4*m^2)) → ((∀
            (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m+1) → (S a b = 2*a^2-2*|a|-4*m^2-4*m))
            → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), (x-rho ∈ FootprintVertices (DiamondTile
            K.1)) → ((y-rho ∈ FootprintVertices (DiamondTile K.1)) → (4*(f y-f x) = S (y-rho).re
            (y-rho).im-S (x-rho).re (x-rho).im - 4*k*(y-x).re))) → (∀ (t : ℤ), ((0 : ℤ) ≤ t) →
            ((t < k) → ((⟨-t, t⟩ - rho ∈ FootprintVertices (DiamondTile K.1)) → ((f ((⟨-t,t⟩ :
            GaussianInt)-1)-f ⟨-t,t⟩ = 0) → ((f ((⟨-t,t⟩ : GaussianInt)+⟨0,1⟩)-f ⟨-t,t⟩ = -t) →
            (f ((⟨-t,t⟩ : GaussianInt)-⟨0,1⟩)-f ⟨-t,t⟩ = t))))))))) ) := by
  classical
  intro K f k rho footBS S sEven sOdd diffR t ht0 htk hzR west north
  have h := diffR _ _ hzR (footBS t ht0 htk)
  rw [sEven _ _ (-t) (by dsimp [rho]; ring),
    sOdd _ _ (-t-1) (by dsimp [rho]; ring)] at h
  simp only [rho, Zsqrtd.re_sub] at h
  simp (disch := omega) only [abs_of_nonneg] at h
  nlinarith only [h]

private theorem htAt399 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, -k-1⟩
        let covered (x : GaussianInt) : Prop :=
          ∀ y, y=x ∨ y=x-1 ∨ y=x-⟨0,1⟩ ∨ y=x-1-⟨0,1⟩ →
            y ∈ DiamondCellDomain K.1 ∨ y-rho ∈ DiamondCellDomain K.1
        ∀ (t : ℤ), ((0 : ℤ) ≤ t) → ((covered ⟨-t, t⟩ ↔ (0 : ℤ) < t) → ((f ((⟨-t,t⟩ :
            GaussianInt)-1)-f ⟨-t,t⟩ = 0) → ((f ((⟨-t,t⟩ : GaussianInt)+⟨0,1⟩)-f ⟨-t,t⟩ = -t) →
            ((f ((⟨-t,t⟩ : GaussianInt)-⟨0,1⟩)-f ⟨-t,t⟩ = t) → ((¬covered ⟨-t, t⟩) → (t=0)))))) )
            := by
  classical
  intro K f k rho covered t ht0 cells west north south hc
  have : ¬ 0 < t := fun ht => hc (cells.mpr ht)
  omega

end DiamondRightSecond

theorem P5352T2RightSecond (K : DiamondParameter) (hk : 1 < K.1)
    (f : IntegerLatticeFunction) (B : Int) (z : GaussianInt) :
    let A := P5352T2Sources K hk 0
    let M := (P5352T2PlacementData K.1 1).1
    (∀ y, y ∈ FootprintVertices A.1 → f y = A.2.1 y) →
    (∀ y, y - M.1 ∈ FootprintVertices A.1 →
      f y = A.2.1 (y - M.1) + M.2.re*y.re + M.2.im*y.im + B) →
    z ∈ FootprintVertices A.1 → z - M.1 ∈ FootprintVertices A.1 →
    (∀ y, y = z ∨ y = z + 1 ∨ y = z - 1 ∨
          y = z + ⟨0, 1⟩ ∨ y = z - ⟨0, 1⟩ →
      y ∈ FootprintVertices A.1 ∨ y - M.1 ∈ FootprintVertices A.1) →
    ((∀ y, y = z ∨ y = z - 1 ∨ y = z - ⟨0, 1⟩ ∨
          y = z - 1 - ⟨0, 1⟩ →
        y ∈ A.1.cells ∨ y - M.1 ∈ A.1.cells) → FourNeighborLaplacian f z = 1) ∧
    (¬ (∀ y, y = z ∨ y = z - 1 ∨ y = z - ⟨0, 1⟩ ∨
          y = z - 1 - ⟨0, 1⟩ →
        y ∈ A.1.cells ∨ y - M.1 ∈ A.1.cells) → FourNeighborLaplacian f z = 0) := by
-- BODY
  exact (by
    classical
    dsimp only
    intro hC hR hz hzR hstar
    let k : Int := K.1
    let rho : GaussianInt := ⟨-k, -k-1⟩
    have hkI : 2 ≤ k := by dsimp [k]; exact_mod_cast hk
    change (∀ y, y ∈ FootprintVertices (DiamondTile K.1) →
      f y = DiamondOdometer K y) at hC
    change (∀ y, y-rho ∈ FootprintVertices (DiamondTile K.1) →
      f y = DiamondOdometer K (y-rho) + (-k)*y.re + 0*y.im+B) at hR
    simp only [zero_mul, add_zero] at hR
    change z ∈ FootprintVertices (DiamondTile K.1) at hz
    change z-rho ∈ FootprintVertices (DiamondTile K.1) at hzR
    let covered (x : GaussianInt) : Prop :=
      ∀ y, y=x ∨ y=x-1 ∨ y=x-⟨0,1⟩ ∨ y=x-1-⟨0,1⟩ →
        y ∈ DiamondCellDomain K.1 ∨ y-rho ∈ DiamondCellDomain K.1
    change (covered z → FourNeighborLaplacian f z = 1) ∧
      (¬ covered z → FourNeighborLaplacian f z = 0)
    have foot (x : GaussianInt) :
        x ∈ FootprintVertices (DiamondTile K.1) ↔
        0 ≤ x.im ∧ x.im ≤ 2*k ∧ -k ≤ x.re ∧ x.re ≤ k ∧
        -x.im-1 ≤ x.re ∧ x.re ≤ x.im+1 ∧
        -(2*k-x.im+1) ≤ x.re ∧ x.re ≤ 2*k-x.im+1 :=
      (P5352T2DomainRows K x).1
    have cell (x : GaussianInt) :
        x ∈ DiamondCellDomain K.1 ↔
        0 ≤ x.im ∧ x.im < 2*k ∧ -(x.im+1) ≤ x.re ∧ x.re < x.im+1 ∧
        -(2*k-x.im) ≤ x.re ∧ x.re < 2*k-x.im :=
      (P4194T1DiamondCellRows K.1 x).1
    have fourCells (x : GaussianInt) := DiamondRightSecond.fourCells K x
    -- Classify the common footprint before evaluating either formula.
    have contact := DiamondRightSecond.contact K z hz hzR foot
    -- These cell tests are independent of the star's footprint coverage.
    have cellsA (t : Int) (ht0 : 0 ≤ t) (htk : t < k) := DiamondRightSecond.cellsA K hk cell
        fourCells t ht0 htk
    have cellsB (t : Int) (ht0 : 0 ≤ t) (htk : t < k) := DiamondRightSecond.cellsB K hk cell
        fourCells t ht0 htk
    have footAE (t : Int) (ht0 : 0 ≤ t) (htk : t < k) := DiamondRightSecond.footAE K hk foot t
        ht0 htk
    have footAN (t : Int) (ht0 : 0 ≤ t) (htk : t < k) := DiamondRightSecond.footAN K hk foot t
        ht0 htk
    have footAW (t : Int) (ht0 : 0 ≤ t) (htk : t < k) := DiamondRightSecond.footAW K hk foot t
        ht0 htk
    have footAS (t : Int) (ht0 : 0 ≤ t) (htk : t < k) := DiamondRightSecond.footAS K hk foot t
        ht0 htk
    have footBE (t : Int) (ht0 : 0 ≤ t) (htk : t < k) := DiamondRightSecond.footBE K hk foot t
        ht0 htk
    have footBW (t : Int) (ht0 : 0 ≤ t) (htk : t < k) := DiamondRightSecond.footBW K hk foot t
        ht0 htk
    have footBN (t : Int) (ht0 : 0 ≤ t) (htk : t < k) := DiamondRightSecond.footBN K hk foot t
        ht0 htk
    have footBS (t : Int) (ht0 : 0 ≤ t) (htk : t < k) := DiamondRightSecond.footBS K hk foot t
        ht0 htk
    let Q (a b : Int) : Int :=
      (Int.natAbs a : Int)*((Int.natAbs a : Int)-1)/2-(a-b)^2/4
    let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
    have tri (a : Int) := DiamondRightSecond.tri K a
    have square (a : Int) := DiamondRightSecond.square K a
    have scale (a b : Int) := DiamondRightSecond.scale tri square a b
    have sEven (a b m : Int) (h : a-b = 2*m) := DiamondRightSecond.sEven K a b m h
    have sOdd (a b m : Int) (h : a-b = 2*m+1) := DiamondRightSecond.sOdd K a b m h
    have valC (x : GaussianInt) (hx : x ∈ FootprintVertices (DiamondTile K.1)) :
        f x = Q x.re x.im := (hC x hx).trans ((P5352T2DomainRows K x).2 hx)
    have valR (x : GaussianInt) (hx : x-rho ∈ FootprintVertices (DiamondTile K.1)) :=
        DiamondRightSecond.valR K f B hR x hx
    have diffC (x y : GaussianInt)
        (hx : x ∈ FootprintVertices (DiamondTile K.1))
        (hy : y ∈ FootprintVertices (DiamondTile K.1)) := DiamondRightSecond.diffC K f scale valC
            x y hx hy
    -- Subtraction at the common center cancels B.
    have diffR (x y : GaussianInt)
        (hx : x-rho ∈ FootprintVertices (DiamondTile K.1))
        (hy : y-rho ∈ FootprintVertices (DiamondTile K.1)) := DiamondRightSecond.diffR K f B
            scale valR x y hx hy
    have lap (x : GaussianInt) : FourNeighborLaplacian f x =
        (f (x+1)-f x)+(f (x-1)-f x)+
          (f (x+⟨0,1⟩)-f x)+(f (x-⟨0,1⟩)-f x) := DiamondRightSecond.lap f x
    rcases contact with ⟨t,ht0,htk,rfl⟩ | ⟨t,ht0,htk,rfl⟩
    · have cells := cellsA t ht0 htk
      have east : f ((⟨-1-t,t⟩ : GaussianInt)+1)-f ⟨-1-t,t⟩ = 0 := DiamondRightSecond.eastAt316 K
          f footAE sEven sOdd diffC t ht0 htk hz
      have north : f ((⟨-1-t,t⟩ : GaussianInt)+⟨0,1⟩)-f ⟨-1-t,t⟩ = -t-1 :=
          DiamondRightSecond.northAt322 K f footAN sEven sOdd diffC t ht0 htk hz
      have west : f ((⟨-1-t,t⟩ : GaussianInt)-1)-f ⟨-1-t,t⟩ =
          if t+1=k then 0 else 1 := DiamondRightSecond.westAt328 K f footAW sEven sOdd diffR t
              ht0 htk hzR north
      have south : f ((⟨-1-t,t⟩ : GaussianInt)-⟨0,1⟩)-f ⟨-1-t,t⟩ = t+1 :=
          DiamondRightSecond.southAt341 K f footAS sEven sOdd diffR t ht0 htk hzR north west
      rw [lap, east, west, north, south]
      constructor
      · intro hc
        have ht : t+1 ≠ k := by have := cells.mp hc; omega
        rw [ite_eq_right ht]
        ring
      · intro hc
        have ht : t+1 = k := DiamondRightSecond.htAt355 K f t htk cells north west south hc
        rw [ite_eq_left ht]
        ring
    · have cells := cellsB t ht0 htk
      have east : f ((⟨-t,t⟩ : GaussianInt)+1)-f ⟨-t,t⟩ =
          if t=0 then 0 else 1 := DiamondRightSecond.eastAt361 K f footBE sEven sOdd diffC t ht0
              htk hz
      have west : f ((⟨-t,t⟩ : GaussianInt)-1)-f ⟨-t,t⟩ = 0 := DiamondRightSecond.westAt373 K f
          footBW sEven sOdd diffC t ht0 htk hz
      have north : f ((⟨-t,t⟩ : GaussianInt)+⟨0,1⟩)-f ⟨-t,t⟩ = -t :=
          DiamondRightSecond.northAt379 K f footBN sEven sOdd diffC t ht0 htk hz
      have south : f ((⟨-t,t⟩ : GaussianInt)-⟨0,1⟩)-f ⟨-t,t⟩ = t := DiamondRightSecond.southAt385
          K f footBS sEven sOdd diffR t ht0 htk hzR west north
      rw [lap, east, west, north, south]
      constructor
      · intro hc
        have ht : t ≠ 0 := by have := cells.mp hc; omega
        rw [ite_eq_right ht]
        ring
      · intro hc
        have ht : t=0 := DiamondRightSecond.htAt399 K f t ht0 cells west north south hc
        rw [ite_eq_left ht]
        ring
  )

end ApollonianSuperharmonic

end
