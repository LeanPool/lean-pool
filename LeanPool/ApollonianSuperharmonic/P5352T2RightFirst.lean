/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacianProperties
public import LeanPool.ApollonianSuperharmonic.DiamondQuadraticArithmetic

public import LeanPool.ApollonianSuperharmonic.P5352T2PlacementData
public import LeanPool.ApollonianSuperharmonic.P5352T2DomainRows
public import LeanPool.ApollonianSuperharmonic.P5352T2Sources

-- [TABLET NODE: P5352T2RightFirst]

/-!
# P5352T2RightFirst

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace DiamondRightFirst

private theorem fourCells :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, k+1⟩
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
        let rho : GaussianInt := ⟨-k, k+1⟩
        (z ∈ FootprintVertices (DiamondTile K.1)) → ((z - rho ∈ FootprintVertices (DiamondTile
            K.1)) → ((∀ (x : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) ↔ 0 ≤ x.im ∧
            x.im ≤ 2*k ∧ -k ≤ x.re ∧ x.re ≤ k ∧ -x.im-1 ≤ x.re ∧ x.re ≤ x.im+1 ∧ -(2*k-x.im+1) ≤
            x.re ∧ x.re ≤ 2*k-x.im+1) → ((∃ t : Int, 0 ≤ t ∧ t < k ∧ z = ⟨-k+t,k+t+1⟩) ∨ (∃ t :
            Int, 0 ≤ t ∧ t < k ∧ z = ⟨-k+t+1,k+t+1⟩)))) ) := by
  classical
  intro K z k rho hz hzR foot
  have h0 := (foot z).mp hz
  have h1 := (foot (z-rho)).mp hzR
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub] at h1
  dsimp [rho] at h1
  have hd : z.im-z.re = 2*k ∨ z.im-z.re = 2*k+1 := by omega
  rcases hd with hd | hd
  · right
    refine ⟨z.re+k-1, by omega, by omega, ?_⟩
    ext <;> dsimp <;> omega
  · left
    refine ⟨z.re+k, by omega, by omega, ?_⟩
    ext <;> dsimp <;> omega





private theorem valR :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, k+1⟩
        (∀ (y : GaussianInt), y - rho ∈ FootprintVertices (DiamondTile K.1) → f y =
            DiamondOdometer K (y - rho) + y.re + -k * y.im + B) → (
        let Q (a b : Int) : Int :=
          (Int.natAbs a : Int)*((Int.natAbs a : Int)-1)/2-(a-b)^2/4
        ∀ (x : GaussianInt), x - rho ∈ FootprintVertices (DiamondTile K.1) → f x = Q (x - rho).re
            (x - rho).im + x.re - k * x.im + B) ) := by
  classical
  intro K f B k rho hR Q x hx
  rw [hR x hx, (P5352T2DomainRows K (x-rho)).2 hx]
  dsimp [Q]
  ring


private theorem diffR :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, k+1⟩
        let Q (a b : Int) : Int :=
          (Int.natAbs a : Int)*((Int.natAbs a : Int)-1)/2-(a-b)^2/4
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        (∀ (a : Int), ∀ (b : Int), 4*Q a b = S a b) → ((∀ (x : GaussianInt), (x-rho ∈
            FootprintVertices (DiamondTile K.1)) → (f x = Q (x-rho).re (x-rho).im +
            x.re-k*x.im+B)) → (∀ (x : GaussianInt), ∀ (y : GaussianInt), x - rho ∈
            FootprintVertices (DiamondTile K.1) → y - rho ∈ FootprintVertices (DiamondTile K.1) →
            (4 : ℤ) * (f y - f x) = S (y - rho).re (y - rho).im - S (x - rho).re (x - rho).im +
            (4 : ℤ) * ((y - x).re - k * (y - x).im))) ) := by
  classical
  intro K f B k rho Q S scale valR x y hx hy
  rw [valR x hx, valR y hy]
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
  linear_combination scale (y.re-rho.re) (y.im-rho.im) -
    scale (x.re-rho.re) (x.im-rho.im)

private theorem cellsAt260 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, k+1⟩
        let covered (x : GaussianInt) : Prop :=
          ∀ y, y=x ∨ y=x-1 ∨ y=x-⟨0,1⟩ ∨ y=x-1-⟨0,1⟩ →
            y ∈ DiamondCellDomain K.1 ∨ y-rho ∈ DiamondCellDomain K.1
        (∀ (x : GaussianInt), x ∈ DiamondCellDomain K.1 ↔ 0 ≤ x.im ∧ x.im < 2*k ∧ -(x.im+1) ≤
            x.re ∧ x.re < x.im+1 ∧ -(2*k-x.im) ≤ x.re ∧ x.re < 2*k-x.im) → ((∀ (x : GaussianInt),
            covered x ↔ (x ∈ DiamondCellDomain K.1 ∨ x-rho ∈ DiamondCellDomain K.1) ∧ (x-1 ∈
            DiamondCellDomain K.1 ∨ x-1-rho ∈ DiamondCellDomain K.1) ∧ (x-⟨0,1⟩ ∈
            DiamondCellDomain K.1 ∨ x-⟨0,1⟩-rho ∈ DiamondCellDomain K.1) ∧ (x-1-⟨0,1⟩ ∈
            DiamondCellDomain K.1 ∨ x-1-⟨0,1⟩-rho ∈ DiamondCellDomain K.1)) → (∀ (t : ℤ), ((0 :
            ℤ) ≤ t) → ((t < k) → (covered ⟨-k+t,k+t+1⟩ ↔ 0 < t))))) ) := by
  classical
  intro K hk k rho covered cell fourCells t ht0 htk
  rw [fourCells]
  simp only [cell, Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one]
  dsimp [rho]
  omega

private theorem heAt265 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        (∀ (x : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) ↔ 0 ≤ x.im ∧ x.im ≤ 2*k ∧
            -k ≤ x.re ∧ x.re ≤ k ∧ -x.im-1 ≤ x.re ∧ x.re ≤ x.im+1 ∧ -(2*k-x.im+1) ≤ x.re ∧ x.re ≤
            2*k-x.im+1) → (∀ (t : ℤ), ((0 : ℤ) ≤ t) → ((t < k) → ((⟨-k+t,k+t+1⟩ : GaussianInt)+1
            ∈ FootprintVertices (DiamondTile K.1))))) ) := by
  classical
  intro K hk k foot t ht0 htk
  rw [foot]
  simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one]
  omega

private theorem hsAt270 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        (∀ (x : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) ↔ 0 ≤ x.im ∧ x.im ≤ 2*k ∧
            -k ≤ x.re ∧ x.re ≤ k ∧ -x.im-1 ≤ x.re ∧ x.re ≤ x.im+1 ∧ -(2*k-x.im+1) ≤ x.re ∧ x.re ≤
            2*k-x.im+1) → (∀ (t : ℤ), ((0 : ℤ) ≤ t) → ((t < k) → ((⟨-k+t,k+t+1⟩ :
            GaussianInt)-⟨0,1⟩ ∈ FootprintVertices (DiamondTile K.1))))) ) := by
  classical
  intro K hk k foot t ht0 htk
  rw [foot]
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
  omega

private theorem hwAt275 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, k+1⟩
        (∀ (x : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) ↔ 0 ≤ x.im ∧ x.im ≤ 2*k ∧
            -k ≤ x.re ∧ x.re ≤ k ∧ -x.im-1 ≤ x.re ∧ x.re ≤ x.im+1 ∧ -(2*k-x.im+1) ≤ x.re ∧ x.re ≤
            2*k-x.im+1) → (∀ (t : ℤ), ((0 : ℤ) ≤ t) → ((t < k) → ((⟨-k+t,k+t+1⟩ :
            GaussianInt)-1-rho ∈ FootprintVertices (DiamondTile K.1))))) ) := by
  classical
  intro K hk k rho foot t ht0 htk
  rw [foot]
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one]
  dsimp [rho]
  omega

private theorem hnAt281 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, k+1⟩
        (∀ (x : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) ↔ 0 ≤ x.im ∧ x.im ≤ 2*k ∧
            -k ≤ x.re ∧ x.re ≤ k ∧ -x.im-1 ≤ x.re ∧ x.re ≤ x.im+1 ∧ -(2*k-x.im+1) ≤ x.re ∧ x.re ≤
            2*k-x.im+1) → (∀ (t : ℤ), ((0 : ℤ) ≤ t) → ((t < k) → ((⟨-k+t,k+t+1⟩ :
            GaussianInt)+⟨0,1⟩-rho ∈ FootprintVertices (DiamondTile K.1))))) ) := by
  classical
  intro K hk k rho foot t ht0 htk
  rw [foot]
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add]
  dsimp [rho]
  omega

private theorem eastAt287 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        (∀ (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m) → (S a b = 2*a^2-2*|a|-4*m^2)) → ((∀
            (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m+1) → (S a b = 2*a^2-2*|a|-4*m^2-4*m))
            → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), (x ∈ FootprintVertices (DiamondTile
            K.1)) → ((y ∈ FootprintVertices (DiamondTile K.1)) → (4*(f y-f x) = S y.re y.im-S
            x.re x.im))) → (∀ (t : ℤ), (t < k) → ((⟨-k + t, k + t + (1 : ℤ)⟩ ∈ FootprintVertices
            (DiamondTile K.1)) → (((⟨-k+t,k+t+1⟩ : GaussianInt)+1 ∈ FootprintVertices
            (DiamondTile K.1)) → (f ((⟨-k+t,k+t+1⟩ : GaussianInt)+1)-f ⟨-k+t,k+t+1⟩ = t+1)))))) )
            := by
  classical
  intro K f k S sEven sOdd diffC t htk hz he
  have h := diffC _ _ hz he
  rw [sEven _ _ (-k) (by dsimp; ring), sOdd _ _ (-k-1) (by dsimp; ring)] at h
  simp only [Zsqrtd.re_add, Zsqrtd.re_one] at h
  simp (disch := omega) only [abs_of_nonpos] at h
  nlinarith only [h]

private theorem southAt293 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        (∀ (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m) → (S a b = 2*a^2-2*|a|-4*m^2)) → ((∀
            (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m+1) → (S a b = 2*a^2-2*|a|-4*m^2-4*m))
            → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), (x ∈ FootprintVertices (DiamondTile
            K.1)) → ((y ∈ FootprintVertices (DiamondTile K.1)) → (4*(f y-f x) = S y.re y.im-S
            x.re x.im))) → (∀ (t : ℤ), (t < k) → ((⟨-k + t, k + t + (1 : ℤ)⟩ ∈ FootprintVertices
            (DiamondTile K.1)) → (((⟨-k+t,k+t+1⟩ : GaussianInt)-⟨0,1⟩ ∈ FootprintVertices
            (DiamondTile K.1)) → ((f ((⟨-k+t,k+t+1⟩ : GaussianInt)+1)-f ⟨-k+t,k+t+1⟩ = t+1) → (f
            ((⟨-k+t,k+t+1⟩ : GaussianInt)-⟨0,1⟩)-f ⟨-k+t,k+t+1⟩ = k))))))) ) := by
  classical
  intro K f k S sEven sOdd diffC t htk hz hs east
  have h := diffC _ _ hz hs
  rw [sEven _ _ (-k) (by dsimp; ring), sOdd _ _ (-k-1) (by dsimp; ring)] at h
  simp only [Zsqrtd.re_sub] at h
  simp (disch := omega) only [abs_of_nonpos] at h
  nlinarith only [h]

private theorem westAt299 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, k+1⟩
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        (∀ (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m) → (S a b = 2*a^2-2*|a|-4*m^2)) → ((∀
            (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m+1) → (S a b = 2*a^2-2*|a|-4*m^2-4*m))
            → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), (x-rho ∈ FootprintVertices (DiamondTile
            K.1)) → ((y-rho ∈ FootprintVertices (DiamondTile K.1)) → (4*(f y-f x) = S (y-rho).re
            (y-rho).im-S (x-rho).re (x-rho).im + 4*((y-x).re-k*(y-x).im)))) → (∀ (t : ℤ), ((0 :
            ℤ) ≤ t) → ((⟨-k + t, k + t + (1 : ℤ)⟩ - rho ∈ FootprintVertices (DiamondTile K.1)) →
            (((⟨-k+t,k+t+1⟩ : GaussianInt)-1-rho ∈ FootprintVertices (DiamondTile K.1)) → ((f
            ((⟨-k+t,k+t+1⟩ : GaussianInt)+1)-f ⟨-k+t,k+t+1⟩ = t+1) → (f ((⟨-k+t,k+t+1⟩ :
            GaussianInt)-1)-f ⟨-k+t,k+t+1⟩ = if t=0 then -1 else -t))))))) ) := by
  classical
  intro K f k rho S sEven sOdd diffR t ht0 hzR hw east
  have h := diffR _ _ hzR hw
  rw [sOdd _ _ (-1) (by dsimp [rho]; ring), sEven _ _ 0 (by dsimp [rho]; ring)] at h
  simp only [rho, Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one] at h
  by_cases ht : t=0
  · rw [ite_eq_left ht]
    simp (disch := omega) only [abs_of_nonpos] at h
    nlinarith only [h, ht]
  · rw [ite_eq_right ht]
    simp (disch := omega) only [abs_of_nonneg] at h
    nlinarith only [h]

private theorem northAt311 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, k+1⟩
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        (∀ (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m) → (S a b = 2*a^2-2*|a|-4*m^2)) → ((∀
            (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m+1) → (S a b = 2*a^2-2*|a|-4*m^2-4*m))
            → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), (x-rho ∈ FootprintVertices (DiamondTile
            K.1)) → ((y-rho ∈ FootprintVertices (DiamondTile K.1)) → (4*(f y-f x) = S (y-rho).re
            (y-rho).im-S (x-rho).re (x-rho).im + 4*((y-x).re-k*(y-x).im)))) → (∀ (t : ℤ), ((0 :
            ℤ) ≤ t) → ((⟨-k + t, k + t + (1 : ℤ)⟩ - rho ∈ FootprintVertices (DiamondTile K.1)) →
            (((⟨-k+t,k+t+1⟩ : GaussianInt)+⟨0,1⟩-rho ∈ FootprintVertices (DiamondTile K.1)) → ((f
            ((⟨-k+t,k+t+1⟩ : GaussianInt)+1)-f ⟨-k+t,k+t+1⟩ = t+1) → ((f ((⟨-k+t,k+t+1⟩ :
            GaussianInt)-1)-f ⟨-k+t,k+t+1⟩ = if t=0 then -1 else -t) → (f ((⟨-k+t,k+t+1⟩ :
            GaussianInt)+⟨0,1⟩)-f ⟨-k+t,k+t+1⟩ = -k)))))))) ) := by
  classical
  intro K f k rho S sEven sOdd diffR t ht0 hzR hn east west
  have h := diffR _ _ hzR hn
  rw [sOdd _ _ (-1) (by dsimp [rho]; ring), sEven _ _ 0 (by dsimp [rho]; ring)] at h
  simp only [rho, Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add] at h
  simp (disch := omega) only [abs_of_nonneg] at h
  nlinarith only [h]

private theorem htAt324 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, k+1⟩
        let covered (x : GaussianInt) : Prop :=
          ∀ y, y=x ∨ y=x-1 ∨ y=x-⟨0,1⟩ ∨ y=x-1-⟨0,1⟩ →
            y ∈ DiamondCellDomain K.1 ∨ y-rho ∈ DiamondCellDomain K.1
        ∀ (t : ℤ), ((0 : ℤ) ≤ t) → ((covered ⟨-k+t,k+t+1⟩ ↔ 0 < t) → ((f ((⟨-k+t,k+t+1⟩ :
            GaussianInt)+1)-f ⟨-k+t,k+t+1⟩ = t+1) → ((f ((⟨-k+t,k+t+1⟩ : GaussianInt)-1)-f
            ⟨-k+t,k+t+1⟩ = if t=0 then -1 else -t) → ((¬covered ⟨-k + t, k + t + (1 : ℤ)⟩) → (t =
            0))))) ) := by
  classical
  intro K f k rho covered t ht0 cells east west hc
  have : ¬ 0 < t := fun ht => hc (cells.mpr ht)
  omega

private theorem cellsAt329 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, k+1⟩
        let covered (x : GaussianInt) : Prop :=
          ∀ y, y=x ∨ y=x-1 ∨ y=x-⟨0,1⟩ ∨ y=x-1-⟨0,1⟩ →
            y ∈ DiamondCellDomain K.1 ∨ y-rho ∈ DiamondCellDomain K.1
        (∀ (x : GaussianInt), x ∈ DiamondCellDomain K.1 ↔ 0 ≤ x.im ∧ x.im < 2*k ∧ -(x.im+1) ≤
            x.re ∧ x.re < x.im+1 ∧ -(2*k-x.im) ≤ x.re ∧ x.re < 2*k-x.im) → ((∀ (x : GaussianInt),
            covered x ↔ (x ∈ DiamondCellDomain K.1 ∨ x-rho ∈ DiamondCellDomain K.1) ∧ (x-1 ∈
            DiamondCellDomain K.1 ∨ x-1-rho ∈ DiamondCellDomain K.1) ∧ (x-⟨0,1⟩ ∈
            DiamondCellDomain K.1 ∨ x-⟨0,1⟩-rho ∈ DiamondCellDomain K.1) ∧ (x-1-⟨0,1⟩ ∈
            DiamondCellDomain K.1 ∨ x-1-⟨0,1⟩-rho ∈ DiamondCellDomain K.1)) → (∀ (t : ℤ), ((0 :
            ℤ) ≤ t) → ((t < k) → (covered ⟨-k+t+1,k+t+1⟩ ↔ t+1 < k))))) ) := by
  classical
  intro K hk k rho covered cell fourCells t ht0 htk
  rw [fourCells]
  simp only [cell, Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one]
  dsimp [rho]
  omega

private theorem heAt334 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        (∀ (x : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) ↔ 0 ≤ x.im ∧ x.im ≤ 2*k ∧
            -k ≤ x.re ∧ x.re ≤ k ∧ -x.im-1 ≤ x.re ∧ x.re ≤ x.im+1 ∧ -(2*k-x.im+1) ≤ x.re ∧ x.re ≤
            2*k-x.im+1) → (∀ (t : ℤ), ((0 : ℤ) ≤ t) → ((t < k) → ((⟨-k+t+1,k+t+1⟩ :
            GaussianInt)+1 ∈ FootprintVertices (DiamondTile K.1))))) ) := by
  classical
  intro K hk k foot t ht0 htk
  rw [foot]
  simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one]
  omega

private theorem hwAt339 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        (∀ (x : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) ↔ 0 ≤ x.im ∧ x.im ≤ 2*k ∧
            -k ≤ x.re ∧ x.re ≤ k ∧ -x.im-1 ≤ x.re ∧ x.re ≤ x.im+1 ∧ -(2*k-x.im+1) ≤ x.re ∧ x.re ≤
            2*k-x.im+1) → (∀ (t : ℤ), ((0 : ℤ) ≤ t) → ((t < k) → ((⟨-k+t+1,k+t+1⟩ :
            GaussianInt)-1 ∈ FootprintVertices (DiamondTile K.1))))) ) := by
  classical
  intro K hk k foot t ht0 htk
  rw [foot]
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one]
  omega

private theorem hsAt344 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        (∀ (x : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) ↔ 0 ≤ x.im ∧ x.im ≤ 2*k ∧
            -k ≤ x.re ∧ x.re ≤ k ∧ -x.im-1 ≤ x.re ∧ x.re ≤ x.im+1 ∧ -(2*k-x.im+1) ≤ x.re ∧ x.re ≤
            2*k-x.im+1) → (∀ (t : ℤ), ((0 : ℤ) ≤ t) → ((t < k) → ((⟨-k+t+1,k+t+1⟩ :
            GaussianInt)-⟨0,1⟩ ∈ FootprintVertices (DiamondTile K.1))))) ) := by
  classical
  intro K hk k foot t ht0 htk
  rw [foot]
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
  omega

private theorem hnAt349 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, k+1⟩
        (∀ (x : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) ↔ 0 ≤ x.im ∧ x.im ≤ 2*k ∧
            -k ≤ x.re ∧ x.re ≤ k ∧ -x.im-1 ≤ x.re ∧ x.re ≤ x.im+1 ∧ -(2*k-x.im+1) ≤ x.re ∧ x.re ≤
            2*k-x.im+1) → (∀ (t : ℤ), ((0 : ℤ) ≤ t) → ((t < k) → ((⟨-k+t+1,k+t+1⟩ :
            GaussianInt)+⟨0,1⟩-rho ∈ FootprintVertices (DiamondTile K.1))))) ) := by
  classical
  intro K hk k rho foot t ht0 htk
  rw [foot]
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add]
  dsimp [rho]
  omega

private theorem eastAt355 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        (∀ (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m) → (S a b = 2*a^2-2*|a|-4*m^2)) → ((∀
            (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m+1) → (S a b = 2*a^2-2*|a|-4*m^2-4*m))
            → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), (x ∈ FootprintVertices (DiamondTile
            K.1)) → ((y ∈ FootprintVertices (DiamondTile K.1)) → (4*(f y-f x) = S y.re y.im-S
            x.re x.im))) → (∀ (t : ℤ), (t < k) → ((⟨-k + t + (1 : ℤ), k + t + (1 : ℤ)⟩ ∈
            FootprintVertices (DiamondTile K.1)) → (((⟨-k+t+1,k+t+1⟩ : GaussianInt)+1 ∈
            FootprintVertices (DiamondTile K.1)) → (f ((⟨-k+t+1,k+t+1⟩ : GaussianInt)+1)-f
            ⟨-k+t+1,k+t+1⟩ = if t+1=k then k else t+2)))))) ) := by
  classical
  intro K f k S sEven sOdd diffC t htk hz he
  have h := diffC _ _ hz he
  rw [sOdd _ _ (-k) (by dsimp; ring), sEven _ _ (-k) (by dsimp; ring)] at h
  simp only [Zsqrtd.re_add, Zsqrtd.re_one] at h
  by_cases ht : t+1=k
  · rw [ite_eq_left ht]
    simp (disch := omega) only [abs_of_nonneg] at h
    nlinarith only [h, ht]
  · rw [ite_eq_right ht]
    simp (disch := omega) only [abs_of_nonpos] at h
    nlinarith only [h]

private theorem westAt367 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        (∀ (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m) → (S a b = 2*a^2-2*|a|-4*m^2)) → ((∀
            (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m+1) → (S a b = 2*a^2-2*|a|-4*m^2-4*m))
            → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), (x ∈ FootprintVertices (DiamondTile
            K.1)) → ((y ∈ FootprintVertices (DiamondTile K.1)) → (4*(f y-f x) = S y.re y.im-S
            x.re x.im))) → (∀ (t : ℤ), (t < k) → ((⟨-k + t + (1 : ℤ), k + t + (1 : ℤ)⟩ ∈
            FootprintVertices (DiamondTile K.1)) → (((⟨-k+t+1,k+t+1⟩ : GaussianInt)-1 ∈
            FootprintVertices (DiamondTile K.1)) → (f ((⟨-k+t+1,k+t+1⟩ : GaussianInt)-1)-f
            ⟨-k+t+1,k+t+1⟩ = -t-1)))))) ) := by
  classical
  intro K f k S sEven sOdd diffC t htk hz hw
  have h := diffC _ _ hz hw
  rw [sOdd _ _ (-k-1) (by dsimp; ring), sEven _ _ (-k) (by dsimp; ring)] at h
  simp only [Zsqrtd.re_sub, Zsqrtd.re_one] at h
  simp (disch := omega) only [abs_of_nonpos] at h
  nlinarith only [h]

private theorem southAt373 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        (∀ (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m) → (S a b = 2*a^2-2*|a|-4*m^2)) → ((∀
            (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m+1) → (S a b = 2*a^2-2*|a|-4*m^2-4*m))
            → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), (x ∈ FootprintVertices (DiamondTile
            K.1)) → ((y ∈ FootprintVertices (DiamondTile K.1)) → (4*(f y-f x) = S y.re y.im-S
            x.re x.im))) → (∀ (t : ℤ), (t < k) → ((⟨-k + t + (1 : ℤ), k + t + (1 : ℤ)⟩ ∈
            FootprintVertices (DiamondTile K.1)) → (((⟨-k+t+1,k+t+1⟩ : GaussianInt)-⟨0,1⟩ ∈
            FootprintVertices (DiamondTile K.1)) → ((f ((⟨-k+t+1,k+t+1⟩ : GaussianInt)-1)-f
            ⟨-k+t+1,k+t+1⟩ = -t-1) → (f ((⟨-k+t+1,k+t+1⟩ : GaussianInt)-⟨0,1⟩)-f ⟨-k+t+1,k+t+1⟩ =
            k))))))) ) := by
  classical
  intro K f k S sEven sOdd diffC t htk hz hs west
  have h := diffC _ _ hz hs
  rw [sOdd _ _ (-k) (by dsimp; ring), sEven _ _ (-k) (by dsimp; ring)] at h
  simp only [Zsqrtd.re_sub] at h
  simp (disch := omega) only [abs_of_nonpos] at h
  nlinarith only [h]

private theorem northAt379 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, k+1⟩
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        (∀ (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m) → (S a b = 2*a^2-2*|a|-4*m^2)) → ((∀
            (a : Int), ∀ (b : Int), ∀ (m : Int), (a-b = 2*m+1) → (S a b = 2*a^2-2*|a|-4*m^2-4*m))
            → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), (x-rho ∈ FootprintVertices (DiamondTile
            K.1)) → ((y-rho ∈ FootprintVertices (DiamondTile K.1)) → (4*(f y-f x) = S (y-rho).re
            (y-rho).im-S (x-rho).re (x-rho).im + 4*((y-x).re-k*(y-x).im)))) → (∀ (t : ℤ), ((0 :
            ℤ) ≤ t) → ((⟨-k + t + (1 : ℤ), k + t + (1 : ℤ)⟩ - rho ∈ FootprintVertices
            (DiamondTile K.1)) → (((⟨-k+t+1,k+t+1⟩ : GaussianInt)+⟨0,1⟩-rho ∈ FootprintVertices
            (DiamondTile K.1)) → ((f ((⟨-k+t+1,k+t+1⟩ : GaussianInt)-1)-f ⟨-k+t+1,k+t+1⟩ = -t-1)
            → (f ((⟨-k+t+1,k+t+1⟩ : GaussianInt)+⟨0,1⟩)-f ⟨-k+t+1,k+t+1⟩ = -k))))))) ) := by
  classical
  intro K f k rho S sEven sOdd diffR t ht0 hzR hn west
  have h := diffR _ _ hzR hn
  rw [sEven _ _ 0 (by dsimp [rho]; ring), sOdd _ _ 0 (by dsimp [rho]; ring)] at h
  simp only [rho, Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add] at h
  simp (disch := omega) only [abs_of_nonneg] at h
  nlinarith only [h]

private theorem htAt392 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        let rho : GaussianInt := ⟨-k, k+1⟩
        let covered (x : GaussianInt) : Prop :=
          ∀ y, y=x ∨ y=x-1 ∨ y=x-⟨0,1⟩ ∨ y=x-1-⟨0,1⟩ →
            y ∈ DiamondCellDomain K.1 ∨ y-rho ∈ DiamondCellDomain K.1
        ∀ (t : ℤ), (t < k) → ((covered ⟨-k+t+1,k+t+1⟩ ↔ t+1 < k) → ((f ((⟨-k+t+1,k+t+1⟩ :
            GaussianInt)-1)-f ⟨-k+t+1,k+t+1⟩ = -t-1) → ((f ((⟨-k+t+1,k+t+1⟩ :
            GaussianInt)-⟨0,1⟩)-f ⟨-k+t+1,k+t+1⟩ = k) → ((f ((⟨-k+t+1,k+t+1⟩ :
            GaussianInt)+⟨0,1⟩)-f ⟨-k+t+1,k+t+1⟩ = -k) → ((¬covered ⟨-k + t + (1 : ℤ), k + t + (1
            : ℤ)⟩) → (t+1 = k)))))) ) := by
  classical
  intro K f k rho covered t htk cells west south north hc
  have : ¬ t+1 < k := fun ht => hc (cells.mpr ht)
  omega

end DiamondRightFirst

theorem P5352T2RightFirst (K : DiamondParameter) (hk : 1 < K.1)
    (f : IntegerLatticeFunction) (B : Int) (z : GaussianInt) :
    let A := P5352T2Sources K hk 0
    let M := (P5352T2PlacementData K.1 0).1
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
    let rho : GaussianInt := ⟨-k, k+1⟩
    change (∀ y, y ∈ FootprintVertices (DiamondTile K.1) →
      f y = DiamondOdometer K y) at hC
    change (∀ y, y-rho ∈ FootprintVertices (DiamondTile K.1) →
      f y = DiamondOdometer K (y-rho) + 1*y.re + (-k)*y.im+B) at hR
    simp only [one_mul] at hR
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
    have fourCells (x : GaussianInt) := DiamondRightFirst.fourCells K x
    -- The common footprint consists of the two staircase rows.
    have contact := DiamondRightFirst.contact K z hz hzR foot
    let Q (a b : Int) : Int :=
      (Int.natAbs a : Int)*((Int.natAbs a : Int)-1)/2-(a-b)^2/4
    have tri (a : Int) := DiamondQuadraticArithmetic.triangularScale a
    have square (a : Int) := DiamondQuadraticArithmetic.squareScale a
    -- Scaling removes both divisions, including for negative odd arguments.
    have scale (a b : Int) := DiamondQuadraticArithmetic.quadraticScale tri square a b
    have sEven (a b m : Int) (h : a-b = 2*m) := DiamondQuadraticArithmetic.evenDifference a b m h
    have sOdd (a b m : Int) (h : a-b = 2*m+1) := DiamondQuadraticArithmetic.oddDifference a b m h
    have valC (x : GaussianInt) (hx : x ∈ FootprintVertices (DiamondTile K.1)) :
        f x = Q x.re x.im := (hC x hx).trans ((P5352T2DomainRows K x).2 hx)
    have valR (x : GaussianInt) (hx : x-rho ∈ FootprintVertices (DiamondTile K.1)) :=
        DiamondRightFirst.valR K f B hR x hx
    have diffC (x y : GaussianInt)
        (hx : x ∈ FootprintVertices (DiamondTile K.1))
        (hy : y ∈ FootprintVertices (DiamondTile K.1)) :=
            DiamondQuadraticArithmetic.differenceScale K f scale valC
            x y hx hy
    -- Subtract in the same translated source so B cancels.
    have diffR (x y : GaussianInt)
        (hx : x-rho ∈ FootprintVertices (DiamondTile K.1))
        (hy : y-rho ∈ FootprintVertices (DiamondTile K.1)) := DiamondRightFirst.diffR K f B scale
            valR x y hx hy
    have lap (x : GaussianInt) : FourNeighborLaplacian f x =
        (f (x+1)-f x)+(f (x-1)-f x)+
          (f (x+⟨0,1⟩)-f x)+(f (x-⟨0,1⟩)-f x) := FourNeighborLaplacianProperties.differences f x
    rcases contact with ⟨t,ht0,htk,rfl⟩ | ⟨t,ht0,htk,rfl⟩
    · have cells : covered ⟨-k+t,k+t+1⟩ ↔ 0 < t := DiamondRightFirst.cellsAt260 K hk cell
        fourCells t ht0 htk
      have he := DiamondRightFirst.heAt265 K hk foot t ht0 htk
      have hs := DiamondRightFirst.hsAt270 K hk foot t ht0 htk
      have hw := DiamondRightFirst.hwAt275 K hk foot t ht0 htk
      have hn := DiamondRightFirst.hnAt281 K hk foot t ht0 htk
      have east : f ((⟨-k+t,k+t+1⟩ : GaussianInt)+1)-f ⟨-k+t,k+t+1⟩ = t+1 :=
          DiamondRightFirst.eastAt287 K f sEven sOdd diffC t htk hz he
      have south : f ((⟨-k+t,k+t+1⟩ : GaussianInt)-⟨0,1⟩)-f ⟨-k+t,k+t+1⟩ = k :=
          DiamondRightFirst.southAt293 K f sEven sOdd diffC t htk hz hs east
      have west : f ((⟨-k+t,k+t+1⟩ : GaussianInt)-1)-f ⟨-k+t,k+t+1⟩ =
          if t=0 then -1 else -t := DiamondRightFirst.westAt299 K f sEven sOdd diffR t ht0 hzR hw
              east
      have north : f ((⟨-k+t,k+t+1⟩ : GaussianInt)+⟨0,1⟩)-f ⟨-k+t,k+t+1⟩ = -k :=
          DiamondRightFirst.northAt311 K f sEven sOdd diffR t ht0 hzR hn east west
      rw [lap, east, west, north, south]
      constructor
      · intro hc
        have ht : t ≠ 0 := by have := cells.mp hc; omega
        rw [ite_eq_right ht]
        ring
      · intro hc
        have ht : t = 0 := DiamondRightFirst.htAt324 K f t ht0 cells east west hc
        rw [ite_eq_left ht, ht]
        ring
    · have cells : covered ⟨-k+t+1,k+t+1⟩ ↔ t+1 < k := DiamondRightFirst.cellsAt329 K hk cell
        fourCells t ht0 htk
      have he := DiamondRightFirst.heAt334 K hk foot t ht0 htk
      have hw := DiamondRightFirst.hwAt339 K hk foot t ht0 htk
      have hs := DiamondRightFirst.hsAt344 K hk foot t ht0 htk
      have hn := DiamondRightFirst.hnAt349 K hk foot t ht0 htk
      have east : f ((⟨-k+t+1,k+t+1⟩ : GaussianInt)+1)-f ⟨-k+t+1,k+t+1⟩ =
          if t+1=k then k else t+2 := DiamondRightFirst.eastAt355 K f sEven sOdd diffC t htk hz he
      have west : f ((⟨-k+t+1,k+t+1⟩ : GaussianInt)-1)-f ⟨-k+t+1,k+t+1⟩ = -t-1 :=
          DiamondRightFirst.westAt367 K f sEven sOdd diffC t htk hz hw
      have south : f ((⟨-k+t+1,k+t+1⟩ : GaussianInt)-⟨0,1⟩)-f ⟨-k+t+1,k+t+1⟩ = k :=
          DiamondRightFirst.southAt373 K f sEven sOdd diffC t htk hz hs west
      have north : f ((⟨-k+t+1,k+t+1⟩ : GaussianInt)+⟨0,1⟩)-f ⟨-k+t+1,k+t+1⟩ = -k :=
          DiamondRightFirst.northAt379 K f sEven sOdd diffR t ht0 hzR hn west
      rw [lap, east, west, north, south]
      constructor
      · intro hc
        have ht : t+1 ≠ k := by have := cells.mp hc; omega
        rw [ite_eq_right ht]
        ring
      · intro hc
        have ht : t+1 = k := DiamondRightFirst.htAt392 K f t htk cells west south north hc
        rw [ite_eq_left ht]
        omega
  )

end ApollonianSuperharmonic

end
