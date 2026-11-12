/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5352T2PlacementData
public import LeanPool.ApollonianSuperharmonic.P5352T2DomainRows
public import LeanPool.ApollonianSuperharmonic.DiamondLaplacianTable
public import LeanPool.ApollonianSuperharmonic.P5352T2Sources

-- [TABLET NODE: P5352T2Predecessor3]

/-!
# P5352T2Predecessor3

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FourthPredecessorCases

private theorem hkm :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        ((K.1-1 : Nat) : Int) = k-1) ) := by
  classical
  intro K hk k
  rw [Nat.cast_sub (by omega : 1 ≤ K.1)]
  dsimp [k]

private theorem childMem :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let k : Int := K.1
        ∀ (a : ℤ), ∀ (b : ℤ), (0 : ℤ) ≤ b ∧ b ≤ (2 : ℤ) * k ∧ -k ≤ a ∧ a ≤ k ∧ -b - (1 : ℤ) ≤ a ∧
            a ≤ b + (1 : ℤ) ∧ -((2 : ℤ) * k - b + (1 : ℤ)) ≤ a ∧ a ≤ (2 : ℤ) * k - b + (1 : ℤ) →
            ⟨a, b⟩ ∈ FootprintVertices (DiamondTile K.1) ) := by
  classical
  intro K k a b h
  apply (P5352T2DomainRows K ⟨a,b⟩).1.mpr
  simpa [k] using h

private theorem predMem :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        (((K.1-1 : Nat) : Int) = k-1) → (∀ (a : ℤ), ∀ (b : ℤ), (0 : ℤ) ≤ b ∧ b ≤ (2 : ℤ) * (k -
            (1 : ℤ)) ∧ -(k - (1 : ℤ)) ≤ a ∧ a ≤ k - (1 : ℤ) ∧ -b - (1 : ℤ) ≤ a ∧ a ≤ b + (1 : ℤ)
            ∧ -((2 : ℤ) * (k - (1 : ℤ)) - b + (1 : ℤ)) ≤ a ∧ a ≤ (2 : ℤ) * (k - (1 : ℤ)) - b + (1
            : ℤ) → ⟨a, b⟩ ∈ FootprintVertices (DiamondTile (K.1 - (1 : ℕ))))) ) := by
  classical
  intro K hk k hkm a b h
  apply (P5352T2DomainRows ⟨K.1-1, by omega⟩ ⟨a,b⟩).1.mpr
  simpa [hkm] using h

private theorem childValue :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (f : IntegerLatticeFunction),
        let child := P5352T2Sources K hk 0
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1)/2 - (a-b)^2/4
        (∀ y ∈ FootprintVertices child.1, f y = child.2.1 y) → ((child.1 = DiamondTile K.1) →
            ((child.2.1 = DiamondOdometer K) → (∀ w ∈ FootprintVertices (DiamondTile K.1), f w =
            Q w.re w.im))) ) := by
  classical
  intro K hk f child Q hchild hchildTile hchildSrc w hw
  have h := hchild w (by rw [hchildTile]; exact hw)
  rw [hchildSrc] at h
  rw [h, (P5352T2DomainRows K w).2 hw]

private theorem childOdo :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (f : IntegerLatticeFunction),
        let child := P5352T2Sources K hk 0
        (∀ y ∈ FootprintVertices child.1, f y = child.2.1 y) → ((child.1 = DiamondTile K.1) →
            ((child.2.1 = DiamondOdometer K) → (∀ w ∈ FootprintVertices (DiamondTile K.1), f w =
            DiamondOdometer K w))) ) := by
  classical
  intro K hk f child hchild hchildTile hchildSrc w hw
  have h := hchild w (by rw [hchildTile]; exact hw)
  simpa [hchildSrc] using h

private theorem predValue :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1),
        let k : Int := K.1
        let pred := P5352T2Sources K hk 3
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1)/2 - (a-b)^2/4
        ∀ (hkm : ((K.1-1 : Nat) : Int) = k-1), (pred.2.1 = DiamondOdometer ⟨K.1-1,
            by omega⟩) → (∀ w ∈ FootprintVertices (DiamondTile (K.1 - (1 : ℕ))), pred.2.1 w = Q
                w.re w.im)) := by
  classical
  intro K hk k pred Q hkm hpredSrc w hw
  let Kp : DiamondParameter := ⟨K.1-1, by omega⟩
  have h := (P5352T2DomainRows Kp w).2 (by simpa [Kp] using hw)
  rw [hpredSrc]
  simpa [Q] using h

private theorem predTranslatedValue :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (f : IntegerLatticeFunction), ∀ (B :
            Int),
        let k : Int := K.1
        let pred := P5352T2Sources K hk 3
        let d : GaussianInt := ⟨-k, 1-k⟩
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1)/2 - (a-b)^2/4
        (∀ (y : GaussianInt), y - d ∈ FootprintVertices pred.1 → f y = pred.2.1 (y - d) + (⟨(1 :
            ℤ) - k, (-1 : ℤ)⟩ : GaussianInt).re * y.re + (⟨(1 : ℤ) - k, (-1 : ℤ)⟩ :
            GaussianInt).im * y.im + B) → ((pred.1 = DiamondTile (K.1-1)) → ((∀ (w :
            GaussianInt), (w ∈ FootprintVertices (DiamondTile (K.1-1))) → (pred.2.1 w = Q w.re
            w.im)) → (∀ (y : GaussianInt), y - d ∈ FootprintVertices (DiamondTile (K.1 - (1 :
            ℕ))) → f y = Q (y - d).re (y - d).im + ((1 : ℤ) - k) * y.re - y.im + B))) ) := by
  classical
  intro K hk f B k pred d Q hpred hpredTile predValue y hy
  have h := hpred y (by rw [hpredTile]; exact hy)
  have hv := predValue (y-d) hy
  rw [hv] at h
  convert h using 1; ring

private theorem floorEven :
    (by
      classical
      exact
        ∀ (m : ℤ), ((-2 : ℤ) * m) ^ (2 : ℕ) / (4 : ℤ) = m ^ (2 : ℕ) ) := by
  classical
  intro m
  have h := P4207T1FloorArithmetic.1 0 (-m)
  have he : 0+2*(-m) = -2*m := by ring
  simpa [he] using h

private theorem floorOdd :
    (by
      classical
      exact
        (DiamondParameter) → (∀ (m : ℤ), ((1 : ℤ) - (2 : ℤ) * m) ^ (2 : ℕ) / (4 : ℤ) = m ^ (2 :
            ℕ) - m) ) := by
  classical
  intro K m
  have h := P4207T1FloorArithmetic.1 1 (-m)
  have he : 1+2*(-m) = 1-2*m := by ring
  rw [he] at h
  norm_num at h ⊢
  omega

private theorem cases :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let k : Int := K.1
        (((K.1-1 : Nat) : Int) = k-1) → (∀ (a : ℤ), ∀ (b : ℤ), ((0 : ℤ) ≤ b ∧ b ≤ (2 : ℤ) * (↑K.1
            : ℤ) ∧ -(↑K.1 : ℤ) ≤ a ∧ a ≤ (↑K.1 : ℤ) ∧ -b - (1 : ℤ) ≤ a ∧ a ≤ b + (1 : ℤ) ∧ -((2 :
            ℤ) * (↑K.1 : ℤ) - b + (1 : ℤ)) ≤ a ∧ a ≤ (2 : ℤ) * (↑K.1 : ℤ) - b + (1 : ℤ)) → (((0 :
            ℤ) ≤ b - ((1 : ℤ) - k) ∧ b - ((1 : ℤ) - k) ≤ (2 : ℤ) * (k - (1 : ℤ)) ∧ -(k - (1 : ℤ))
            ≤ a - -k ∧ a - -k ≤ k - (1 : ℤ) ∧ -(b - ((1 : ℤ) - k)) - (1 : ℤ) ≤ a - -k ∧ a - -k ≤
            b - ((1 : ℤ) - k) + (1 : ℤ) ∧ -((2 : ℤ) * (k - (1 : ℤ)) - (b - ((1 : ℤ) - k)) + (1 :
            ℤ)) ≤ a - -k ∧ a - -k ≤ (2 : ℤ) * (k - (1 : ℤ)) - (b - ((1 : ℤ) - k)) + (1 : ℤ)) →
            ((∃ t : Int, 1 ≤ t ∧ t ≤ k ∧ a = -t ∧ b = t-1) ∨ (∃ t : Int, 1 ≤ t ∧ t < k ∧ a = -t ∧
            b = t)))) ) := by
  classical
  intro K k hkm a b hc hp
  have hs : a+b=-1 ∨ a+b=0 := by omega
  rcases hs with hs | hs
  · left
    refine ⟨-a, ?_, ?_, ?_, ?_⟩ <;> omega
  · right
    refine ⟨-a, ?_, ?_, ?_, ?_⟩ <;> omega

private theorem hComp :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1),
        let k : Int := K.1
        let child := P5352T2Sources K hk 0
        let pred := P5352T2Sources K hk 3
        let d : GaussianInt := ⟨-k, 1-k⟩
        let r : GaussianInt := ⟨-2*k, 0⟩
        (((K.1-1 : Nat) : Int) = k-1) → ((∀ (a : Int), ∀ (b : Int), (0 ≤ b ∧ b ≤ 2*k ∧ -k ≤ a ∧ a
            ≤ k ∧ -b-1 ≤ a ∧ a ≤ b+1 ∧ -(2*k-b+1) ≤ a ∧ a ≤ 2*k-b+1) → ((⟨a,b⟩ : GaussianInt) ∈
            FootprintVertices (DiamondTile K.1))) → (∀ (t : ℤ), ((1 : ℤ) ≤ t) → ((t ≤ k) → ((⟨-t,
            t - (1 : ℤ)⟩ ∈ FootprintVertices child.1) → ((⟨-t, t - (1 : ℤ)⟩ - d ∈
            FootprintVertices pred.1) → ((∀ (y : GaussianInt), y = ⟨-t, t - (1 : ℤ)⟩ ∨ y = ⟨-t, t
            - (1 : ℤ)⟩ + (1 : GaussianInt) ∨ y = ⟨-t, t - (1 : ℤ)⟩ - (1 : GaussianInt) ∨ y = ⟨-t,
            t - (1 : ℤ)⟩ + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ y = ⟨-t, t - (1 : ℤ)⟩ - ⟨(0 : ℤ), (1 : ℤ)⟩ → y ∈
            FootprintVertices child.1 ∨ y - d ∈ FootprintVertices pred.1) → (((0 : ℤ) ≤ t - (1 :
            ℤ) ∧ t - (1 : ℤ) ≤ (2 : ℤ) * (↑K.1 : ℤ) ∧ -(↑K.1 : ℤ) ≤ -t ∧ -t ≤ (↑K.1 : ℤ) ∧ -(t -
            (1 : ℤ)) - (1 : ℤ) ≤ -t ∧ -t ≤ t - (1 : ℤ) + (1 : ℤ) ∧ -((2 : ℤ) * (↑K.1 : ℤ) - (t -
            (1 : ℤ)) + (1 : ℤ)) ≤ -t ∧ -t ≤ (2 : ℤ) * (↑K.1 : ℤ) - (t - (1 : ℤ)) + (1 : ℤ)) →
            (((0 : ℤ) ≤ t - (1 : ℤ) - ((1 : ℤ) - k) ∧ t - (1 : ℤ) - ((1 : ℤ) - k) ≤ (2 : ℤ) * (k
            - (1 : ℤ)) ∧ -(k - (1 : ℤ)) ≤ -t - -k ∧ -t - -k ≤ k - (1 : ℤ) ∧ -(t - (1 : ℤ) - ((1 :
            ℤ) - k)) - (1 : ℤ) ≤ -t - -k ∧ -t - -k ≤ t - (1 : ℤ) - ((1 : ℤ) - k) + (1 : ℤ) ∧ -((2
            : ℤ) * (k - (1 : ℤ)) - (t - (1 : ℤ) - ((1 : ℤ) - k)) + (1 : ℤ)) ≤ -t - -k ∧ -t - -k ≤
            (2 : ℤ) * (k - (1 : ℤ)) - (t - (1 : ℤ) - ((1 : ℤ) - k)) + (1 : ℤ)) → (
        let x : GaussianInt := ⟨-t,t-1⟩
        x-r ∈ FootprintVertices (DiamondTile K.1) ↔ t=k))))))))) ) := by
  classical
  intro K hk k child pred d r hkm childMem t ht1 htk hz hpz hcover hc hp x
  constructor
  · intro hh
    have h := (P5352T2DomainRows K (x-r)).1.mp hh
    simp only [x, r, Zsqrtd.re_sub, Zsqrtd.im_sub] at h
    omega
  · intro ht
    subst t
    have hm : x-r = (⟨k,k-1⟩ : GaussianInt) := by
      ext <;> simp [x,r]; ring
    rw [hm]
    exact childMem k (k-1) (by omega)

private theorem hPC :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1),
        let k : Int := K.1
        let pred := P5352T2Sources K hk 3
        let d : GaussianInt := ⟨-k, 1-k⟩
        (pred.1 = DiamondTile (K.1-1)) → (∀ (t : ℤ), (⟨-t, t - (1 : ℤ)⟩ - d ∈ FootprintVertices
            pred.1) → (
        let x : GaussianInt := ⟨-t,t-1⟩
        x-d ∈ FootprintVertices (DiamondTile (K.1-1)))) ) := by
  classical
  intro K hk k pred d hpredTile t hpz x
  have hpz' := hpredTile ▸ hpz
  simpa [x,d] using hpz'

private theorem hPW :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        (((K.1-1 : Nat) : Int) = k-1) → ((∀ (a : Int), ∀ (b : Int), (0 ≤ b ∧ b ≤ 2*(k-1) ∧ -(k-1)
            ≤ a ∧ a ≤ k-1 ∧ -b-1 ≤ a ∧ a ≤ b+1 ∧ -(2*(k-1)-b+1) ≤ a ∧ a ≤ 2*(k-1)-b+1) → ((⟨a,b⟩
            : GaussianInt) ∈ FootprintVertices (DiamondTile (K.1-1)))) → (∀ (t : ℤ), ((1 : ℤ) ≤
            t) → ((t ≤ k) → (((0 : ℤ) ≤ t - (1 : ℤ) - ((1 : ℤ) - k) ∧ t - (1 : ℤ) - ((1 : ℤ) - k)
            ≤ (2 : ℤ) * (k - (1 : ℤ)) ∧ -(k - (1 : ℤ)) ≤ -t - -k ∧ -t - -k ≤ k - (1 : ℤ) ∧ -(t -
            (1 : ℤ) - ((1 : ℤ) - k)) - (1 : ℤ) ≤ -t - -k ∧ -t - -k ≤ t - (1 : ℤ) - ((1 : ℤ) - k)
            + (1 : ℤ) ∧ -((2 : ℤ) * (k - (1 : ℤ)) - (t - (1 : ℤ) - ((1 : ℤ) - k)) + (1 : ℤ)) ≤ -t
            - -k ∧ -t - -k ≤ (2 : ℤ) * (k - (1 : ℤ)) - (t - (1 : ℤ) - ((1 : ℤ) - k)) + (1 : ℤ)) →
            ((⟨k-t-1,k+t-2⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile (K.1-1)))))))) ) := by
  classical
  intro K hk k hkm predMem t ht1 htk hp
  apply predMem; omega

private theorem hPS :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        (((K.1-1 : Nat) : Int) = k-1) → ((∀ (a : Int), ∀ (b : Int), (0 ≤ b ∧ b ≤ 2*(k-1) ∧ -(k-1)
            ≤ a ∧ a ≤ k-1 ∧ -b-1 ≤ a ∧ a ≤ b+1 ∧ -(2*(k-1)-b+1) ≤ a ∧ a ≤ 2*(k-1)-b+1) → ((⟨a,b⟩
            : GaussianInt) ∈ FootprintVertices (DiamondTile (K.1-1)))) → (∀ (t : ℤ), ((1 : ℤ) ≤
            t) → ((t ≤ k) → (((0 : ℤ) ≤ t - (1 : ℤ) - ((1 : ℤ) - k) ∧ t - (1 : ℤ) - ((1 : ℤ) - k)
            ≤ (2 : ℤ) * (k - (1 : ℤ)) ∧ -(k - (1 : ℤ)) ≤ -t - -k ∧ -t - -k ≤ k - (1 : ℤ) ∧ -(t -
            (1 : ℤ) - ((1 : ℤ) - k)) - (1 : ℤ) ≤ -t - -k ∧ -t - -k ≤ t - (1 : ℤ) - ((1 : ℤ) - k)
            + (1 : ℤ) ∧ -((2 : ℤ) * (k - (1 : ℤ)) - (t - (1 : ℤ) - ((1 : ℤ) - k)) + (1 : ℤ)) ≤ -t
            - -k ∧ -t - -k ≤ (2 : ℤ) * (k - (1 : ℤ)) - (t - (1 : ℤ) - ((1 : ℤ) - k)) + (1 : ℤ)) →
            ((⟨k-t,k+t-3⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile (K.1-1)))))))) ) := by
  classical
  intro K hk k hkm predMem t ht1 htk hp
  apply predMem; omega

private theorem hPredC :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        let d : GaussianInt := ⟨-k, 1-k⟩
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1)/2 - (a-b)^2/4
        (∀ (y : GaussianInt), (y-d ∈ FootprintVertices (DiamondTile (K.1-1))) → (f y = Q (y-d).re
            (y-d).im + (1-k)*y.re-y.im+B)) → (∀ (t : ℤ),
        let x : GaussianInt := ⟨-t,t-1⟩
        (x-d ∈ FootprintVertices (DiamondTile (K.1-1))) → (f x = Q (k-t) (k+t-2) + (1-k)*(-t) -
            (t-1)+B)) ) := by
  classical
  intro K f B k d Q predTranslatedValue t x hPC
  have h := predTranslatedValue x (by
    simpa [x,d] using hPC)
  convert h using 1; simp [x,d]; congr 1 <;> ring

private theorem hPredW :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        let d : GaussianInt := ⟨-k, 1-k⟩
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1)/2 - (a-b)^2/4
        (∀ (y : GaussianInt), (y-d ∈ FootprintVertices (DiamondTile (K.1-1))) → (f y = Q (y-d).re
            (y-d).im + (1-k)*y.re-y.im+B)) → (∀ (t : ℤ), ((⟨k-t-1,k+t-2⟩ : GaussianInt) ∈
            FootprintVertices (DiamondTile (K.1-1))) → (f (⟨-t-1,t-1⟩ : GaussianInt) = Q (k-t-1)
            (k+t-2) + (1-k)*(-t-1) - (t-1)+B)) ) := by
  classical
  intro K f B k d Q predTranslatedValue t hPW
  have hy : (⟨-t-1,t-1⟩ : GaussianInt)-d = ⟨k-t-1,k+t-2⟩ := by
    ext <;> simp [d] <;> ring
  have h := predTranslatedValue ⟨-t-1,t-1⟩ (by rw [hy]; exact hPW)
  convert h using 1; simp [hy,d]

private theorem hPredS :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        let d : GaussianInt := ⟨-k, 1-k⟩
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1)/2 - (a-b)^2/4
        (∀ (y : GaussianInt), (y-d ∈ FootprintVertices (DiamondTile (K.1-1))) → (f y = Q (y-d).re
            (y-d).im + (1-k)*y.re-y.im+B)) → (∀ (t : ℤ), ((⟨k-t,k+t-3⟩ : GaussianInt) ∈
            FootprintVertices (DiamondTile (K.1-1))) → (f (⟨-t,t-2⟩ : GaussianInt) = Q (k-t)
            (k+t-3) + (1-k)*(-t) - (t-2)+B)) ) := by
  classical
  intro K f B k d Q predTranslatedValue t hPS
  have hy : (⟨-t,t-2⟩ : GaussianInt)-d = ⟨k-t,k+t-3⟩ := by
    ext <;> simp [d] <;> ring
  have h := predTranslatedValue ⟨-t,t-2⟩ (by rw [hy]; exact hPS)
  convert h using 1; simp [hy,d]

private theorem tri :
    (by
      classical
      exact
        (DiamondParameter) → ((IntegerLatticeFunction) → ((Int) → ((ℤ) → (∀ (n : ℤ), (2 : ℤ) * (n
            * (n - (1 : ℤ)) / (2 : ℤ)) = n * (n - (1 : ℤ)))))) ) := by
  classical
  intro K f B t n
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · have hn : n=2*(n/2) := by omega
    rw [hn]
    have he : 2*(n/2)*(2*(n/2)-1)=2*((n/2)*(2*(n/2)-1)) := by ring
    rw [he, Int.mul_ediv_cancel_left _ (by norm_num : (2:Int) ≠ 0)]
  · have hn : n=2*(n/2)+1 := by omega
    rw [hn]
    have he : (2*(n/2)+1)*(2*(n/2)+1-1)=
        2*((2*(n/2)+1)*(n/2)) := by ring
    rw [he, Int.mul_ediv_cancel_left _ (by norm_num : (2:Int) ≠ 0)]

private theorem tdiff :
    (by
      classical
      exact
        (∀ (n : Int), 2*(n*(n-1)/2)=n*(n-1)) → (∀ (n : ℤ), n * (n - (1 : ℤ)) / (2 : ℤ) - (n - (1
            : ℤ)) * (n - (2 : ℤ)) / (2 : ℤ) = n - (1 : ℤ)) ) := by
  classical
  intro tri n
  have h0 := tri n
  have h1 : 2*((n-1)*(n-2)/2)=(n-1)*(n-2) := by
    simpa [show n-1-1=n-2 by ring] using tri (n-1)
  have he : 2*(n*(n-1)/2-(n-1)*(n-2)/2)=2*(n-1) := by
    rw [mul_sub, h0, h1]
    ring
  exact mul_left_cancel₀ (by norm_num : (2:Int) ≠ 0) he

private theorem qChildC :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1)/2 - (a-b)^2/4
        (∀ (m : Int), (1-2*m)^2/4 = m^2-m) → (∀ (t : ℤ), ((1 : ℤ) ≤ t) → (
        let x : GaussianInt := ⟨-t,t-1⟩
        (f x = Q (-t) (t-1)) → ((f x = Q (k-t) (k+t-2) + (1-k)*(-t) - (t-1)+B) → ((f (⟨-t-1,t-1⟩
            : GaussianInt) = Q (k-t-1) (k+t-2) + (1-k)*(-t-1) - (t-1)+B) → ((∀ (n : Int),
            2*(n*(n-1)/2)=n*(n-1)) → (Q (-t) (t-1) = -(t*(t-1)/2))))))) ) := by
  classical
  intro K f B k Q floorOdd t ht1 x hChildC hPredC hPredW tri
  simp only [Q, Int.natCast_natAbs]
  rw [abs_of_nonpos (by omega : -t ≤ 0)]
  simp only [neg_neg]
  rw [show -t-(t-1)=1-2*t by ring, floorOdd]
  have hp : t^2-t=2*(t*(t-1)/2) := by
    have h := tri t
    simpa [show t*(t-1)=t^2-t by ring] using h.symm
  rw [hp]
  ring

private theorem qChildE :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1)/2 - (a-b)^2/4
        (∀ (m : Int), (-2*m)^2/4 = m^2) → (∀ (t : ℤ), ((1 : ℤ) ≤ t) → (
        let x : GaussianInt := ⟨-t,t-1⟩
        (f x = Q (-t) (t-1)) → ((f x = Q (k-t) (k+t-2) + (1-k)*(-t) - (t-1)+B) → ((f (⟨-t-1,t-1⟩
            : GaussianInt) = Q (k-t-1) (k+t-2) + (1-k)*(-t-1) - (t-1)+B) → ((∀ (n : Int),
            2*(n*(n-1)/2)=n*(n-1)) → ((∀ (n : Int), n*(n-1)/2-(n-1)*(n-2)/2=n-1) → (Q (1-t) (t-1)
            = -(t*(t-1)/2)))))))) ) := by
  classical
  intro K f B k Q floorEven t ht1 x hChildC hPredC hPredW tri tdiff
  simp only [Q, Int.natCast_natAbs]
  rw [abs_of_nonpos (by omega : 1-t ≤ 0)]
  simp only [neg_sub]
  rw [show (1-t)-(t-1)=-2*(t-1) by ring, floorEven]
  have ht : 2*((t-1)*(t-2)/2)=(t-1)*(t-2) := by
    simpa [show t-1-1=t-2 by ring] using tri (t-1)
  have hs : (t-1)^2=2*((t-1)*(t-2)/2)+(t-1) := by rw [ht]; ring
  have he : t*(t-1)/2=(t-1)*(t-2)/2+(t-1) := by
    have h := tdiff t
    omega
  rw [hs, he]
  ring

private theorem qChildN :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1)/2 - (a-b)^2/4
        (∀ (m : Int), (-2*m)^2/4 = m^2) → (∀ (t : ℤ), ((1 : ℤ) ≤ t) → (
        let x : GaussianInt := ⟨-t,t-1⟩
        (f x = Q (-t) (t-1)) → ((f x = Q (k-t) (k+t-2) + (1-k)*(-t) - (t-1)+B) → ((f (⟨-t-1,t-1⟩
            : GaussianInt) = Q (k-t-1) (k+t-2) + (1-k)*(-t-1) - (t-1)+B) → ((∀ (n : Int),
            2*(n*(n-1)/2)=n*(n-1)) → ((∀ (n : Int), n*(n-1)/2-(n-1)*(n-2)/2=n-1) → (Q (-t) t =
            -(t*(t+1)/2)))))))) ) := by
  classical
  intro K f B k Q floorEven t ht1 x hChildC hPredC hPredW tri tdiff
  simp only [Q, Int.natCast_natAbs]
  rw [abs_of_nonpos (by omega : -t ≤ 0)]
  simp only [neg_neg]
  rw [show -t-t=-2*t by ring, floorEven]
  have hs : t^2=2*(t*(t-1)/2)+t := by
    have hp : t^2=t*(t-1)+t := by ring
    calc
      t^2 = t*(t-1)+t := hp
      _ = 2*(t*(t-1)/2)+t := by
        exact congrArg (fun u : Int => u+t) (tri t).symm
  have hn : t*(t+1)/2=t*(t-1)/2+t := by
    have h := tdiff (t+1)
    have h' : (t+1)*t/2-t*(t-1)/2=t := by
      simpa [show t+1-1=t by ring, show t+1-2=t-1 by ring] using h
    have hmul : (t+1)*t/2=t*(t+1)/2 := by ring
    rw [← hmul]
    omega
  rw [hs, hn]
  ring

private theorem qPredC :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1)/2 - (a-b)^2/4
        (((K.1-1 : Nat) : Int) = k-1) → ((∀ (m : Int), (-2*m)^2/4 = m^2) → (∀ (t : ℤ), (t ≤ k) → (
        let x : GaussianInt := ⟨-t,t-1⟩
        (f x = Q (-t) (t-1)) → ((f x = Q (k-t) (k+t-2) + (1-k)*(-t) - (t-1)+B) → ((f (⟨-t-1,t-1⟩
            : GaussianInt) = Q (k-t-1) (k+t-2) + (1-k)*(-t-1) - (t-1)+B) → (Q (k-t) (k+t-2) =
            (k-t)*(k-t-1)/2-(t-1)^2)))))) ) := by
  classical
  intro K f B k Q hkm floorEven t htk x hChildC hPredC hPredW
  simp only [Q, Int.natCast_natAbs]
  rw [abs_of_nonneg (by omega : 0 ≤ k-t)]
  rw [show (k-t)-(k+t-2)=-2*(t-1) by ring, floorEven]

private theorem qPredWlt :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1)/2 - (a-b)^2/4
        (((K.1-1 : Nat) : Int) = k-1) → ((∀ (m : Int), (1-2*m)^2/4 = m^2-m) → (∀ (t : ℤ),
        let x : GaussianInt := ⟨-t,t-1⟩
        (f x = Q (-t) (t-1)) → ((f x = Q (k-t) (k+t-2) + (1-k)*(-t) - (t-1)+B) → ((f (⟨-t-1,t-1⟩
            : GaussianInt) = Q (k-t-1) (k+t-2) + (1-k)*(-t-1) - (t-1)+B) → (t < k → Q (k - t - (1
            : ℤ)) (k + t - (2 : ℤ)) = (k - t - (1 : ℤ)) * (k - t - (2 : ℤ)) / (2 : ℤ) - (t * t -
            t)))))) ) := by
  classical
  intro K f B k Q hkm floorOdd t x hChildC hPredC hPredW ht
  simp only [Q, Int.natCast_natAbs]
  rw [abs_of_nonneg (by omega : 0 ≤ k-t-1)]
  rw [show (k-t-1)-(k+t-2)=1-2*t by ring, floorOdd]
  ring

private theorem qPredWeq :
    (by
      classical
        exact
        ∀ (K : DiamondParameter),
          let k : Int := K.1;
          let Q : Int → Int → Int := fun a b =>
            (Int.natAbs a : Int) * ((Int.natAbs a : Int) - 1) / 2 - (a - b) ^ 2 / 4;
          (∀ (m : Int), (1 - 2 * m) ^ 2 / 4 = m ^ 2 - m) →
            (∀ (t : ℤ),
              (t = k → Q (k - t - (1 : ℤ)) (k + t - (2 : ℤ)) = -(t * t - t)))) := by
  classical
  intro K k Q floorOdd t ht
  subst t
  simp only [Q, Int.natCast_natAbs]
  have ha : k-k-1 = (-1 : Int) := by omega
  rw [ha]
  simp only [Int.reduceNeg, abs_neg, abs_one, sub_self, mul_zero, EuclideanDomain.zero_div,
      zero_sub, neg_sub]
  rw [show (-1:Int)-(k+k-2)=1-2*k by ring, floorOdd]
  norm_num
  ring

private theorem qPredS :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1)/2 - (a-b)^2/4
        (((K.1-1 : Nat) : Int) = k-1) → ((∀ (m : Int), (1-2*m)^2/4 = m^2-m) → (∀ (t : ℤ), (t ≤ k)
            → (
        let x : GaussianInt := ⟨-t,t-1⟩
        (f x = Q (-t) (t-1)) → ((f x = Q (k-t) (k+t-2) + (1-k)*(-t) - (t-1)+B) → ((f (⟨-t-1,t-1⟩
            : GaussianInt) = Q (k-t-1) (k+t-2) + (1-k)*(-t-1) - (t-1)+B) → (Q (k-t) (k+t-3) =
            (k-t)*(k-t-1)/2-((t-1)^2-(t-1)))))))) ) := by
  classical
  intro K f B k Q hkm floorOdd t htk x hChildC hPredC hPredW
  simp only [Q, Int.natCast_natAbs]
  rw [abs_of_nonneg (by omega : 0 ≤ k-t)]
  rw [show (k-t)-(k+t-3)=1-2*(t-1) by ring, floorOdd]

private theorem hEastDiff :
    (by
      classical
      exact
        ∀ (f : IntegerLatticeFunction),
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1)/2 - (a-b)^2/4
        ∀ (t : ℤ),
        let x : GaussianInt := ⟨-t,t-1⟩
        (f x = Q (-t) (t-1)) → ((f (⟨1-t,t-1⟩ : GaussianInt) = Q (1-t) (t-1)) → ((Q (-t) (t-1) =
            -(t*(t-1)/2)) → ((Q (1-t) (t-1) = -(t*(t-1)/2)) → (f (x+1)-f x = 0)))) ) := by
  classical
  intro f Q t x hChildC hChildE qChildC qChildE
  have he : x+1 = ⟨1-t,t-1⟩ := by ext <;> simp [x]; ring
  rw [he, hChildE, hChildC, qChildE, qChildC]
  ring

private theorem hWestDiff :
    (by
      classical
        exact
        ∀ (K : DiamondParameter),
          ∀ (f : IntegerLatticeFunction),
            ∀ (B : Int),
              let k : Int := K.1;
              let Q : Int → Int → Int := fun a b =>
                (Int.natAbs a : Int) * ((Int.natAbs a : Int) - 1) / 2 -
                  (a - b) ^ 2 / 4;
              (∀ (t : ℤ),
                ((t ≤ k) →
                  (let x : GaussianInt := ⟨-t, t - 1⟩;
                  ((f x = Q (-t) (t - 1)) →
                    ((f (⟨-t - 1, t - 1⟩ : GaussianInt) =
                        Q (k - t - 1) (k + t - 2) + (1 - k) * (-t - 1) - (t - 1) +
                          B) →
                      ((∀ (n : Int),
                          n * (n - 1) / 2 - (n - 1) * (n - 2) / 2 = n - 1) →
                        ((Q (k - t) (k + t - 2) =
                            (k - t) * (k - t - 1) / 2 - (t - 1) ^ 2) →
                          (((t < k) →
                              (Q (k - t - 1) (k + t - 2) =
                                (k - t - 1) * (k - t - 2) / 2 - (t * t - t))) →
                            (((t = k) →
                                (Q (k - t - 1) (k + t - 2) = -(t * t - t))) →
                              ((Q (-t) (t - 1) =
                                  Q (k - t) (k + t - 2) + (1 - k) * (-t) - (t - 1) +
                                    B) →
                                (f (x - 1) - f x =
                                  if t = k then 0 else 1)))))))))))) := by
  classical
  intro K f B k Q t htk x hChildC hPredW tdiff qPredC qPredWlt qPredWeq hAgree
  have hw : x-1 = ⟨-t-1,t-1⟩ := by ext <;> simp [x]
  rw [hw, hPredW, hChildC, hAgree]
  by_cases ht : t=k
  · subst t
    simp only []
    rw [qPredWeq rfl, qPredC]
    norm_num
    ring
  · have hlt : t<k := by omega
    rw [ite_eq_right ht, qPredWlt hlt, qPredC]
    have htd : (k-t)*(k-t-1)/2-(k-t-1)*(k-t-2)/2=k-t-1 := by
      simpa [show k-t-1-1=k-t-2 by ring] using tdiff (k-t)
    have htd' : (k-t-1)*(k-t-2)/2-(k-t)*(k-t-1)/2=1-(k-t) := by
      have h := htd
      omega
    linear_combination htd'

private theorem hNorthDiff :
    (by
      classical
      exact
        ∀ (f : IntegerLatticeFunction),
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1)/2 - (a-b)^2/4
        ∀ (t : ℤ),
        let x : GaussianInt := ⟨-t,t-1⟩
        (f x = Q (-t) (t-1)) → ((f (⟨-t,t⟩ : GaussianInt) = Q (-t) t) → ((∀ (n : Int),
            n*(n-1)/2-(n-1)*(n-2)/2=n-1) → ((Q (-t) (t-1) = -(t*(t-1)/2)) → ((Q (-t) t =
            -(t*(t+1)/2)) → (f (x+⟨0,1⟩)-f x = -t))))) ) := by
  classical
  intro f Q t x hChildC hChildN tdiff qChildC qChildN
  have hn : x+⟨0,1⟩ = ⟨-t,t⟩ := by ext <;> simp [x]
  rw [hn, hChildN, hChildC, qChildN, qChildC]
  have h := tdiff (t+1)
  have h' : (t+1)*t/2-t*(t-1)/2=t := by
    simpa [show t+1-1=t by ring, show t+1-2=t-1 by ring] using h
  have hquot : t*(t+1)/2=(t+1)*t/2 := by
    exact congrArg (fun n : Int => n/2) (by ring)
  rw [hquot]
  linear_combination -h'

private theorem hSouthDiff :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1)/2 - (a-b)^2/4
        ∀ (t : ℤ),
        let x : GaussianInt := ⟨-t,t-1⟩
        (f x = Q (-t) (t-1)) → ((f (⟨-t,t-2⟩ : GaussianInt) = Q (k-t) (k+t-3) + (1-k)*(-t) -
            (t-2)+B) → ((Q (k-t) (k+t-2) = (k-t)*(k-t-1)/2-(t-1)^2) → ((Q (k-t) (k+t-3) =
            (k-t)*(k-t-1)/2-((t-1)^2-(t-1))) → ((Q (-t) (t-1) = Q (k-t) (k+t-2) +
            (1-k)*(-t)-(t-1)+B) → (f (x-⟨0,1⟩)-f x = t))))) ) := by
  classical
  intro K f B k Q t x hChildC hPredS qPredC qPredS hAgree
  have hs : x-⟨0,1⟩ = ⟨-t,t-2⟩ := by ext <;> simp [x]; ring
  rw [hs, hPredS, hChildC, hAgree, qPredS, qPredC]
  ring

private theorem lapIdentity :
    (by
      classical
      exact
        ∀ (g : IntegerLatticeFunction), ∀ (w : GaussianInt), FourNeighborLaplacian g w = g (w +
            (1 : GaussianInt)) - g w + (g (w - (1 : GaussianInt)) - g w) + (g (w + ⟨(0 : ℤ), (1 :
            ℤ)⟩) - g w) + (g (w - ⟨(0 : ℤ), (1 : ℤ)⟩) - g w) ) := by
  classical
  intro g w
  unfold FourNeighborLaplacian
  ring

private theorem lap0 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        ∀ (t : ℤ),
        let x : GaussianInt := ⟨-t,t-1⟩
        (f (x+1)-f x = 0) → ((f (x-1)-f x = if t=k then 0 else 1) → ((f (x+⟨0,1⟩)-f x = -t) → ((f
            (x-⟨0,1⟩)-f x = t) → ((∀ (g : IntegerLatticeFunction), ∀ (w : GaussianInt),
            FourNeighborLaplacian g w = (g (w+1)-g w)+(g (w-1)-g w)+ (g (w+⟨0,1⟩)-g w)+(g
            (w-⟨0,1⟩)-g w)) → (t = k → FourNeighborLaplacian f x = (0 : ℤ)))))) ) := by
  classical
  intro K f k t x hEastDiff hWestDiff hNorthDiff hSouthDiff lapIdentity ht
  rw [lapIdentity, hEastDiff, hWestDiff, hNorthDiff, hSouthDiff, ite_eq_left ht]
  ring

private theorem lap1 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        ∀ (t : ℤ),
        let x : GaussianInt := ⟨-t,t-1⟩
        (f (x+1)-f x = 0) → ((f (x-1)-f x = if t=k then 0 else 1) → ((f (x+⟨0,1⟩)-f x = -t) → ((f
            (x-⟨0,1⟩)-f x = t) → ((∀ (g : IntegerLatticeFunction), ∀ (w : GaussianInt),
            FourNeighborLaplacian g w = (g (w+1)-g w)+(g (w-1)-g w)+ (g (w+⟨0,1⟩)-g w)+(g
            (w-⟨0,1⟩)-g w)) → (t ≠ k → FourNeighborLaplacian f x = (1 : ℤ)))))) ) := by
  classical
  intro K f k t x hEastDiff hWestDiff hNorthDiff hSouthDiff lapIdentity ht
  rw [lapIdentity, hEastDiff, hWestDiff, hNorthDiff, hSouthDiff, ite_eq_right ht]
  ring

private theorem htAt413 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1),
        let k : Int := K.1
        let child := P5352T2Sources K hk 0
        let r : GaussianInt := ⟨-2*k, 0⟩
        (child.1 = DiamondTile K.1) → (∀ (t : ℤ), (⟨-t, t - (1 : ℤ)⟩ - r ∉ FootprintVertices
            child.1) → (
        let x : GaussianInt := ⟨-t,t-1⟩
        (x-r ∈ FootprintVertices (DiamondTile K.1) ↔ t=k) → (t≠k))) ) := by
  classical
  intro K hk k child r hchildTile t hc x hComp ht
  apply hc
  have hh := hComp.mpr ht
  simpa [hchildTile] using hh

private theorem hLap :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (u : ℤ),
        let x : GaussianInt := ⟨-u,u⟩
        (f x = DiamondOdometer K x) → ((f ⟨(1 : ℤ) - u, u⟩ = DiamondOdometer K ⟨(1 : ℤ) - u, u⟩)
            → ((f ⟨-u - (1 : ℤ), u⟩ = DiamondOdometer K ⟨-u - (1 : ℤ), u⟩) → ((f ⟨-u, u + (1 :
            ℤ)⟩ = DiamondOdometer K ⟨-u, u + (1 : ℤ)⟩) → ((f ⟨-u, u - (1 : ℤ)⟩ = DiamondOdometer
            K ⟨-u, u - (1 : ℤ)⟩) → ((x+1 = (⟨1-u,u⟩ : GaussianInt)) → ((x-1 = (⟨-u-1,u⟩ :
            GaussianInt)) → ((x+⟨0,1⟩ = (⟨-u,u+1⟩ : GaussianInt)) → ((x-⟨0,1⟩ = (⟨-u,u-1⟩ :
            GaussianInt)) → (FourNeighborLaplacian f x = FourNeighborLaplacian (DiamondOdometer
            K) x))))))))) ) := by
  classical
  intro K f u x h0 h1 h2 h3 h4 he hw hn hs
  unfold FourNeighborLaplacian
  rw [he, hw, hn, hs, h1, h2, h3, h4, h0]

private theorem huK :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), (IntegerLatticeFunction) → (
        let k : Int := K.1
        (((K.1-1 : Nat) : Int) = k-1) → (∀ (u : ℤ), (u < k) → (u ≤ (K.1 : Int)))) ) := by
  classical
  intro K f k hkm u huk
  have huK' : u ≤ k := by omega
  exact_mod_cast huK'

private theorem habsA :
    (by
      classical
      exact
        (DiamondParameter) → ((IntegerLatticeFunction) → (∀ (u : ℤ), ((1 : ℤ) ≤ u) → ((Int.natAbs
            (-u) : Int) = u))) ) := by
  classical
  intro K f u hu1
  rw [Int.natCast_natAbs, abs_of_nonpos (by omega : -u ≤ 0)]
  ring

private theorem habsB :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let k : Int := K.1
        (((K.1 : Nat) : Int) = k) → (∀ (u : ℤ), (u-(K.1:Int) ≤ 0) → ((Int.natAbs (u-(K.1:Int)) :
            Int) = k-u)) ) := by
  classical
  intro K k hkc u hle
  rw [Int.natCast_natAbs, abs_of_nonpos hle]
  rw [hkc]
  ring

private theorem hNotTrue :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let k : Int := K.1
        (((K.1-1 : Nat) : Int) = k-1) → (∀ (u : ℤ),
        let x : GaussianInt := ⟨-u,u⟩
        ((Int.natAbs (-u) : Int) = u) → (((Int.natAbs (u-(K.1:Int)) : Int) = k-u) → (x ∉
            DiamondVertexDomains K true))) ) := by
  classical
  intro K k hkm u x habsA habsB
  change ¬ (Int.natAbs (-u) + Int.natAbs (u-(K.1:Int)) ≤ K.1-1)
  intro hi
  have hiI : ((Int.natAbs (-u) + Int.natAbs (u-(K.1:Int)) : Nat) : Int) ≤
      ((K.1-1 : Nat) : Int) := by exact_mod_cast hi
  rw [Nat.cast_add, habsA, habsB, hkm] at hiI
  clear * - hiI
  omega

private theorem hCompFalse :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), (IntegerLatticeFunction) → (
        let k : Int := K.1
        let r : GaussianInt := ⟨-2*k, 0⟩
        (((K.1-1 : Nat) : Int) = k-1) → (∀ (u : ℤ), (u < k) → (
        let x : GaussianInt := ⟨-u,u⟩
        ((Int.natAbs (-u) : Int) = u) → (((Int.natAbs (u-(K.1:Int)) : Int) = k-u) → (x-r ∉
            FootprintVertices (DiamondTile K.1)))))) ) := by
  classical
  intro K f k r hkm u huk x habsA habsB hh
  have h := (P5352T2DomainRows K (x-r)).1.mp hh
  simp only [x, r, Zsqrtd.re_sub, Zsqrtd.im_sub] at h
  omega

end FourthPredecessorCases

theorem P5352T2Predecessor3 (K : DiamondParameter) (hk : 1 < K.1)
    (f : IntegerLatticeFunction) (B : Int) (z : GaussianInt) :
    let A := P5352T2Sources K hk 0
    let D := P5352T2Sources K hk 3
    let M := (P5352T2PlacementData K.1 2).2 3
    (∀ y, y ∈ FootprintVertices A.1 → f y = A.2.1 y) →
    (∀ y, y - M.1 ∈ FootprintVertices D.1 →
      f y = D.2.1 (y - M.1) + M.2.1.re*y.re + M.2.1.im*y.im + B) →
    z ∈ FootprintVertices A.1 → z - M.1 ∈ FootprintVertices D.1 →
    (∀ y, y = z ∨ y = z + 1 ∨ y = z - 1 ∨
          y = z + ⟨0, 1⟩ ∨ y = z - ⟨0, 1⟩ →
      y ∈ FootprintVertices A.1 ∨ y - M.1 ∈ FootprintVertices D.1) →
    (z - M.2.2 ∈ FootprintVertices A.1 → FourNeighborLaplacian f z = 0) ∧
    (z - M.2.2 ∉ FootprintVertices A.1 → FourNeighborLaplacian f z = 1) := by
-- BODY
  exact (by
    classical
    let k : Int := K.1
    let child := P5352T2Sources K hk 0
    let pred := P5352T2Sources K hk 3
    let M := (P5352T2PlacementData K.1 2).2 3
    let d : GaussianInt := ⟨-k, 1-k⟩
    let r : GaussianInt := ⟨-2*k, 0⟩
    let Q : Int → Int → Int := fun a b =>
      (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1)/2 - (a-b)^2/4
    have hk2 : 2 ≤ k := by dsimp [k]; exact_mod_cast (show 2 ≤ K.1 by omega)
    have hm : M.1 = d ∧ M.2.1 = ⟨1-k,-1⟩ ∧ M.2.2 = r := by
      simp [M, d, r, P5352T2PlacementData, k]
    rcases hm with ⟨hd, ha, hr⟩
    change
      (∀ y, y ∈ FootprintVertices child.1 → f y = child.2.1 y) →
      (∀ y, y - M.1 ∈ FootprintVertices pred.1 →
        f y = pred.2.1 (y-M.1) + M.2.1.re*y.re + M.2.1.im*y.im+B) →
      z ∈ FootprintVertices child.1 → z-M.1 ∈ FootprintVertices pred.1 →
      (∀ y, y=z ∨ y=z+1 ∨ y=z-1 ∨ y=z+⟨0,1⟩ ∨ y=z-⟨0,1⟩ →
        y ∈ FootprintVertices child.1 ∨ y-M.1 ∈ FootprintVertices pred.1) →
      (z-M.2.2 ∈ FootprintVertices child.1 → FourNeighborLaplacian f z=0) ∧
      (z-M.2.2 ∉ FootprintVertices child.1 → FourNeighborLaplacian f z=1)
    intro hchild hpred hz hpz hcover
    rw [hd, ha] at hpred
    rw [hd] at hpz hcover
    rw [hr] at ⊢
    have hkc : ((K.1 : Nat) : Int) = k := by rfl
    have hkm : ((K.1-1 : Nat) : Int) = k-1 := FourthPredecessorCases.hkm K hk
    obtain ⟨_, _, _, hFoot, _, _⟩ := DiamondTileOdometerRestriction K
    have hchildTile : child.1 = DiamondTile K.1 := by simp [child, P5352T2Sources]
    have hpredTile : pred.1 = DiamondTile (K.1-1) := by simp [pred, P5352T2Sources]
    have hchildSrc : child.2.1 = DiamondOdometer K := by
      simp [child, P5352T2Sources]
    have hpredSrc : pred.2.1 = DiamondOdometer ⟨K.1-1, by omega⟩ := by
      simp [pred, P5352T2Sources]
    have childMem (a b : Int)
        (h : 0 ≤ b ∧ b ≤ 2*k ∧ -k ≤ a ∧ a ≤ k ∧ -b-1 ≤ a ∧ a ≤ b+1 ∧
          -(2*k-b+1) ≤ a ∧ a ≤ 2*k-b+1) := FourthPredecessorCases.childMem K a b h
    have predMem (a b : Int)
        (h : 0 ≤ b ∧ b ≤ 2*(k-1) ∧ -(k-1) ≤ a ∧ a ≤ k-1 ∧
          -b-1 ≤ a ∧ a ≤ b+1 ∧ -(2*(k-1)-b+1) ≤ a ∧ a ≤ 2*(k-1)-b+1) :=
              FourthPredecessorCases.predMem K hk hkm a b h
    let Kp : DiamondParameter := ⟨K.1-1, by omega⟩
    have childValue (w : GaussianInt)
        (hw : w ∈ FootprintVertices (DiamondTile K.1)) :
        f w = Q w.re w.im := FourthPredecessorCases.childValue K hk f hchild hchildTile hchildSrc
            w hw
    have childOdo (w : GaussianInt)
        (hw : w ∈ FootprintVertices (DiamondTile K.1)) := FourthPredecessorCases.childOdo K hk f
            hchild hchildTile hchildSrc w hw
    have predValue (w : GaussianInt)
        (hw : w ∈ FootprintVertices (DiamondTile (K.1-1))) := FourthPredecessorCases.predValue K
            hk hkm hpredSrc w hw
    have predTranslatedValue (y : GaussianInt)
        (hy : y-d ∈ FootprintVertices (DiamondTile (K.1-1))) :=
            FourthPredecessorCases.predTranslatedValue K hk f B hpred hpredTile predValue y hy
    have floorEven (m : Int) := FourthPredecessorCases.floorEven m
    have floorOdd (m : Int) := FourthPredecessorCases.floorOdd K m
    rcases z with ⟨a,b⟩
    have hc := (P5352T2DomainRows K ⟨a,b⟩).1.mp (by simpa [hchildTile] using hz)
    have hp := (P5352T2DomainRows ⟨K.1-1, by omega⟩ (⟨a,b⟩-d)).1.mp (by
      simpa [hpredTile, d, hkm] using hpz)
    rw [hkm] at hp
    simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, d] at hp
    simp only [] at hc
    have cases := FourthPredecessorCases.cases K hkm a b hc hp
    rcases cases with ⟨t, ht1, htk, ha0, hb0⟩ | ⟨u, hu1, huk, ha0, hb0⟩
    · -- A_t = (-t,t-1)
      subst a
      subst b
      let x : GaussianInt := ⟨-t,t-1⟩
      have hComp : x-r ∈ FootprintVertices (DiamondTile K.1) ↔ t=k :=
          FourthPredecessorCases.hComp K hk hkm childMem t ht1 htk hz hpz hcover hc hp
      have hX : x ∈ FootprintVertices (DiamondTile K.1) := by
        apply childMem (-t) (t-1); omega
      have hE : (⟨1-t,t-1⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1) := by
        apply childMem (1-t) (t-1); omega
      have hN : (⟨-t,t⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1) := by
        apply childMem (-t) t; omega
      have hPC := FourthPredecessorCases.hPC K hk hpredTile t hpz
      have hPW := FourthPredecessorCases.hPW K hk hkm predMem t ht1 htk hp
      have hPS := FourthPredecessorCases.hPS K hk hkm predMem t ht1 htk hp
      have hChildC : f x = Q (-t) (t-1) := by simpa [x] using childValue x hX
      have hChildE : f (⟨1-t,t-1⟩ : GaussianInt) = Q (1-t) (t-1) := by
        exact childValue _ hE
      have hChildN : f (⟨-t,t⟩ : GaussianInt) = Q (-t) t := by
        exact childValue _ hN
      have hPredC : f x = Q (k-t) (k+t-2) + (1-k)*(-t) - (t-1)+B := FourthPredecessorCases.hPredC
          K f B predTranslatedValue t hPC
      have hPredW := FourthPredecessorCases.hPredW K f B predTranslatedValue t hPW
      have hPredS := FourthPredecessorCases.hPredS K f B predTranslatedValue t hPS
      have tri (n : Int) := FourthPredecessorCases.tri K f B t n
      have tdiff (n : Int) := FourthPredecessorCases.tdiff tri n
      have qChildC := FourthPredecessorCases.qChildC K f B floorOdd t ht1 hChildC hPredC hPredW tri
      have qChildE := FourthPredecessorCases.qChildE K f B floorEven t ht1 hChildC hPredC hPredW
          tri tdiff
      have qChildN := FourthPredecessorCases.qChildN K f B floorEven t ht1 hChildC hPredC hPredW
          tri tdiff
      have qPredC := FourthPredecessorCases.qPredC K f B hkm floorEven t htk hChildC hPredC hPredW
      have qPredWlt (ht : t<k) := FourthPredecessorCases.qPredWlt K f B hkm floorOdd t hChildC
          hPredC hPredW ht
      have qPredWeq (ht : t=k) := FourthPredecessorCases.qPredWeq K floorOdd t ht
      have qPredS := FourthPredecessorCases.qPredS K f B hkm floorOdd t htk hChildC hPredC hPredW
      have hAgree : Q (-t) (t-1) = Q (k-t) (k+t-2) +
          (1-k)*(-t)-(t-1)+B := by rw [← hChildC, hPredC]
      have hEastDiff := FourthPredecessorCases.hEastDiff f t hChildC hChildE qChildC qChildE
      have hWestDiff := FourthPredecessorCases.hWestDiff K f B t htk hChildC hPredW tdiff qPredC
          qPredWlt qPredWeq hAgree
      have hNorthDiff := FourthPredecessorCases.hNorthDiff f t hChildC hChildN tdiff qChildC qChildN
      have hSouthDiff := FourthPredecessorCases.hSouthDiff K f B t hChildC hPredS qPredC qPredS
          hAgree
      have lapIdentity (g : IntegerLatticeFunction) (w : GaussianInt) :=
          FourthPredecessorCases.lapIdentity g w
      have lap0 (ht : t=k) := FourthPredecessorCases.lap0 K f t hEastDiff hWestDiff hNorthDiff
          hSouthDiff lapIdentity ht
      have lap1 (ht : t≠k) := FourthPredecessorCases.lap1 K f t hEastDiff hWestDiff hNorthDiff
          hSouthDiff lapIdentity ht
      constructor
      · intro hc
        have ht := hComp.mp (by simpa [hchildTile] using hc)
        exact lap0 ht
      · intro hc
        have ht : t≠k := FourthPredecessorCases.htAt413 K hk hchildTile t hc hComp
        exact lap1 ht
    · -- B_t = (-t,t)
      clear hpred hpz hcover hp hc
      subst a
      subst b
      let x : GaussianInt := ⟨-u,u⟩
      have hX : x ∈ FootprintVertices (DiamondTile K.1) := by
        apply childMem (-u) u; omega
      have hE : (⟨1-u,u⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1) := by
        apply childMem (1-u) u; omega
      have hW : (⟨-u-1,u⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1) := by
        apply childMem (-u-1) u; omega
      have hN : (⟨-u,u+1⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1) := by
        apply childMem (-u) (u+1); omega
      have hS : (⟨-u,u-1⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1) := by
        apply childMem (-u) (u-1); omega
      have h0 := childOdo x hX
      have h1 := childOdo ⟨1-u,u⟩ hE
      have h2 := childOdo ⟨-u-1,u⟩ hW
      have h3 := childOdo ⟨-u,u+1⟩ hN
      have h4 := childOdo ⟨-u,u-1⟩ hS
      have he : x+1 = (⟨1-u,u⟩ : GaussianInt) := by ext <;> simp [x]; ring
      have hw : x-1 = (⟨-u-1,u⟩ : GaussianInt) := by ext <;> simp [x]
      have hn : x+⟨0,1⟩ = (⟨-u,u+1⟩ : GaussianInt) := by ext <;> simp [x]
      have hs : x-⟨0,1⟩ = (⟨-u,u-1⟩ : GaussianInt) := by ext <;> simp [x]
      have hLap := FourthPredecessorCases.hLap K f u h0 h1 h2 h3 h4 he hw hn hs
      have huK := FourthPredecessorCases.huK K f hkm u huk
      have hFalse : x ∈ DiamondVertexDomains K false := by
        exact hFoot ▸ hX
      have habsA := FourthPredecessorCases.habsA K f u hu1
      have hle : u-(K.1:Int) ≤ 0 := by rw [hkc]; omega
      have habsB := FourthPredecessorCases.habsB K hkc u hle
      have hNotTrue := FourthPredecessorCases.hNotTrue K hkm u habsA habsB
      have htable := (DiamondLaplacianTable K).2.1 x hFalse hNotTrue
      have hLapOne : FourNeighborLaplacian f x=1 := hLap.trans htable
      have hCompFalse := FourthPredecessorCases.hCompFalse K f hkm u huk habsA habsB
      constructor
      · intro hh
        exact (hCompFalse hh).elim
      · intro _
        exact hLapOne)

end ApollonianSuperharmonic

end
