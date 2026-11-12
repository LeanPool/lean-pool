/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.EvenSquareQuotient
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacianProperties

public import LeanPool.ApollonianSuperharmonic.P5352T2PlacementData
public import LeanPool.ApollonianSuperharmonic.P5352T2DomainRows
public import LeanPool.ApollonianSuperharmonic.DiamondLaplacianTable
public import LeanPool.ApollonianSuperharmonic.P5352T2Sources

-- [TABLET NODE: P5352T2Predecessor2]

/-!
# P5352T2Predecessor2

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace SecondPredecessorProof

private theorem childValue :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (f : IntegerLatticeFunction),
        let child := P5352T2Sources K hk 0
        (∀ y ∈ FootprintVertices child.1, f y = child.2.1 y) → (
        let Q : Int → Int → Int := fun x y =>
          (Int.natAbs x : Int) * ((Int.natAbs x : Int)-1)/2 - (x-y)^2/4
        ∀ w ∈ FootprintVertices (DiamondTile K.1), f w = Q w.re w.im) ) := by
  classical
  intro K hk f child hchild Q w hw
  have hw' : w∈FootprintVertices child.1 := by simpa [child,P5352T2Sources] using hw
  rw [hchild w hw']
  simpa [Q,child,P5352T2Sources] using (P5352T2DomainRows K w).2 hw

private theorem childOdometer :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (f : IntegerLatticeFunction),
        let child := P5352T2Sources K hk 0
        (∀ y ∈ FootprintVertices child.1, f y = child.2.1 y) → (∀ w ∈ FootprintVertices
            (DiamondTile K.1), f w = DiamondOdometer K w) ) := by
  classical
  intro K hk f child hchild w hw
  have hw' : w∈FootprintVertices child.1 := by simpa [child,P5352T2Sources] using hw
  simpa [child,P5352T2Sources] using hchild w hw'

private theorem predFoot :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        (ℤ) → ((ℤ) → (((↑(K.1 - (1 : ℕ)) : ℤ) = k - (1 : ℤ)) → (∀ (w : GaussianInt), (0 : ℤ) ≤
            w.im ∧ w.im ≤ (2 : ℤ) * (k - (1 : ℤ)) ∧ -(k - (1 : ℤ)) ≤ w.re ∧ w.re ≤ k - (1 : ℤ) ∧
            -w.im - (1 : ℤ) ≤ w.re ∧ w.re ≤ w.im + (1 : ℤ) ∧ -((2 : ℤ) * (k - (1 : ℤ)) - w.im +
            (1 : ℤ)) ≤ w.re ∧ w.re ≤ (2 : ℤ) * (k - (1 : ℤ)) - w.im + (1 : ℤ) → w ∈
            FootprintVertices (DiamondTile (K.1 - (1 : ℕ))))))) ) := by
  classical
  intro K hk k a b hcast w hw
  apply (P5352T2DomainRows ⟨K.1-1,by omega⟩ w).1.mpr
  simpa [hcast] using hw

private theorem predValue :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1),
        let k : Int := K.1
        ∀ (a : ℤ), ∀ (b : ℤ), ∀ (hcast : (↑(K.1 - (1 : ℕ)) : ℤ) = k - (1 : ℤ)),
        let Q : Int → Int → Int := fun x y =>
          (Int.natAbs x : Int) * ((Int.natAbs x : Int)-1)/2 - (x-y)^2/4
        ∀ (w : GaussianInt), (w∈FootprintVertices (DiamondTile (K.1-1))) → (DiamondOdometer
            ⟨K.1-1,by omega⟩ w=Q w.re w.im)) := by
  classical
  intro K hk k a b hcast Q w hw
  simpa [Q] using (P5352T2DomainRows ⟨K.1-1,by omega⟩ w).2 hw

private theorem predTranslatedValue :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (f : IntegerLatticeFunction), ∀ (B :
            Int),
        let k : Int := K.1
        let d : GaussianInt := ⟨-k,k+1⟩
        let pred := P5352T2Sources K hk 3
        ∀ (hpred : ∀ (y : GaussianInt), y - d ∈ FootprintVertices pred.1 → f y = pred.2.1 (y - d)
            + (⟨(1 : ℤ), -k⟩ : GaussianInt).re * y.re + (⟨(1 : ℤ), -k⟩ : GaussianInt).im * y.im +
                B), ∀ (a : ℤ), ∀ (b : ℤ), ∀ (hcast : (↑(K.1 - (1 : ℕ)) : ℤ) = k - (1 : ℤ)),
        let Q : Int → Int → Int := fun x y =>
          (Int.natAbs x : Int) * ((Int.natAbs x : Int)-1)/2 - (x-y)^2/4
        (∀ (w : GaussianInt), (w∈FootprintVertices (DiamondTile (K.1-1))) → (DiamondOdometer
            ⟨K.1-1,by omega⟩ w=Q w.re w.im)) → (∀ (y : GaussianInt), y - d ∈ FootprintVertices
            (DiamondTile (K.1 - (1 : ℕ))) → f y = Q (y - d).re (y - d).im + y.re - k * y.im + B))
                := by
  classical
  intro K hk f B k d pred hpred a b hcast Q predValue y hy
  have hp : y-d∈FootprintVertices pred.1 := by
    simpa [pred,P5352T2Sources] using hy
  have heq := hpred y hp
  have hv := predValue (y-d) hy
  have heq' : f y = DiamondOdometer ⟨K.1-1,by omega⟩ (y-d) + y.re-k*y.im+B := by
    simpa [pred,P5352T2Sources,sub_eq_add_neg] using heq
  rw [hv] at heq'
  simpa [d,sub_eq_add_neg] using heq'

private theorem tri :
    (by
      classical
      exact
        (DiamondParameter) → ((ℤ) → ((ℤ) → (
        let T : Int → Int := fun n => n*(n-1)/2
        ∀ (n : ℤ), (2 : ℤ) * T n = n * (n - (1 : ℤ))))) ) := by
  classical
  intro K a b T n
  dsimp [T]
  rcases Int.emod_two_eq_zero_or_one n with h|h
  · have hn : n=2*(n/2) := by omega
    rw [hn]
    have he : 2*(n/2)*(2*(n/2)-1)=2*((n/2)*(2*(n/2)-1)) := by ring
    rw [he,Int.mul_ediv_cancel_left _ (by norm_num : (2:Int)≠0)]
  · have hn : n=2*(n/2)+1 := by omega
    rw [hn]
    have he : (2*(n/2)+1)*(2*(n/2)+1-1)=
        2*((2*(n/2)+1)*(n/2)) := by ring
    rw [he,Int.mul_ediv_cancel_left _ (by norm_num : (2:Int)≠0)]

private theorem tdiff :
    (by
      classical
      exact
        (DiamondParameter) → ((ℤ) → ((ℤ) → (
        let T : Int → Int := fun n => n*(n-1)/2
        (∀ (n : Int), 2*T n=n*(n-1)) → (∀ (n : ℤ), T n - T (n - (1 : ℤ)) = n - (1 : ℤ))))) ) := by
  classical
  intro K a b T tri n
  have h1 := tri n
  have h2 := tri (n-1)
  have h : 2 * (T n - T (n - 1)) = 2 * (n - 1) := by
    rw [mul_sub,h1,h2]
    ring
  omega

private theorem tdiffRev :
    (by
      classical
      exact
        (DiamondParameter) → ((ℤ) → ((ℤ) → (
        let T : Int → Int := fun n => n*(n-1)/2
        (∀ (n : Int), T n - T (n - 1) = n - 1) → (∀ (n : ℤ), T (n - (1 : ℤ)) - T n = (1 : ℤ) -
            n)))) ) := by
  classical
  intro K a b T tdiff n
  have h := tdiff n
  omega


private theorem floorOdd :
    (by
      classical
      exact
        (DiamondParameter) → ((ℤ) → ((ℤ) → (∀ (m : ℤ), ((2 : ℤ) * m + (1 : ℤ)) ^ (2 : ℕ) / (4 :
            ℤ) = m ^ (2 : ℕ) + m))) ) := by
  classical
  intro K a b m
  have h := P4207T1FloorArithmetic.1 1 m
  have he : 1+2*m=2*m+1 := by ring
  rw [he] at h
  norm_num at h ⊢
  omega

private theorem ht :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let k : Int := K.1
        ∀ (a : ℤ), ∀ (b : ℤ), (k < b ∧ b ≤ (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ -(k - (1 :
            ℤ)) ≤ a + k ∧ a + k ≤ k - (1 : ℤ) ∧ k < a + k + (1 : ℤ) + b ∧ a + k ≤ b - (k + (1 :
            ℤ)) + (1 : ℤ) ∧ b ≤ (1 : ℤ) + (a + k) + (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ a +
            k ≤ (2 : ℤ) * (k - (1 : ℤ)) - (b - (k + (1 : ℤ))) + (1 : ℤ)) → (((↑(K.1 - (1 : ℕ)) :
            ℤ) = k - (1 : ℤ)) → (((0 : ℤ) ≤ b ∧ b ≤ (2 : ℤ) * k ∧ -k ≤ a ∧ a ≤ k ∧ -b - (1 : ℤ) ≤
            a ∧ a ≤ b + (1 : ℤ) ∧ -((2 : ℤ) * k - b + (1 : ℤ)) ≤ a ∧ a ≤ (2 : ℤ) * k - b + (1 :
            ℤ)) → (1≤-a ∧ -a≤k ∧ (b=2*k+1+a ∨ b=2*k+a)))) ) := by
  classical
  intro K k a b hdpred hcast hdchild
  have h : -k≤a ∧ a≤-1 ∧ (b-a=2*k+1 ∨ b-a=2*k) := by omega
  omega

private theorem hcompAt243 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1),
        let k : Int := K.1
        let r : GaussianInt := ⟨-2*k,0⟩
        let child := P5352T2Sources K hk 0
        (child.1=DiamondTile K.1) → (∀ (a : ℤ), ∀ (b : ℤ), (k < b ∧ b ≤ (2 : ℤ) * (k - (1 : ℤ)) +
            (k + (1 : ℤ)) ∧ -(k - (1 : ℤ)) ≤ a + k ∧ a + k ≤ k - (1 : ℤ) ∧ k < a + k + (1 : ℤ) +
            b ∧ a + k ≤ b - (k + (1 : ℤ)) + (1 : ℤ) ∧ b ≤ (1 : ℤ) + (a + k) + (2 : ℤ) * (k - (1 :
            ℤ)) + (k + (1 : ℤ)) ∧ a + k ≤ (2 : ℤ) * (k - (1 : ℤ)) - (b - (k + (1 : ℤ))) + (1 :
            ℤ)) → (((↑(K.1 - (1 : ℕ)) : ℤ) = k - (1 : ℤ)) → ((b = (2 : ℤ) * k + (1 : ℤ) + a) → (
        let t : Int := -a
        (a=-t ∧ b=2*k+1-t) → ((1≤t ∧ t≤k) → (
        let zA : GaussianInt := ⟨-t,2*k+1-t⟩
        zA-r ∈ FootprintVertices child.1 ↔ t=k)))))) ) := by
  classical
  intro K hk k r child hchildTile a b hdpred hcast hb t hcoords htrange zA
  constructor
  · intro hh
    have hdom := (P5352T2DomainRows K (zA-r)).1.mp
      (hchildTile ▸ hh)
    simp [zA,r] at hdom
    omega
  · intro he
    subst t
    have hmem : zA-r=⟨k, k+1⟩ := by
      ext <;> simp [zA,r] <;> omega
    rw [hmem]
    exact hchildTile.symm ▸ (P5352T2DomainRows K ⟨k,k+1⟩).1.mpr (by
      constructor <;> simp <;> omega)

private theorem hce :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        ∀ (a : ℤ), ∀ (b : ℤ), (k < b ∧ b ≤ (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ -(k - (1 :
            ℤ)) ≤ a + k ∧ a + k ≤ k - (1 : ℤ) ∧ k < a + k + (1 : ℤ) + b ∧ a + k ≤ b - (k + (1 :
            ℤ)) + (1 : ℤ) ∧ b ≤ (1 : ℤ) + (a + k) + (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ a +
            k ≤ (2 : ℤ) * (k - (1 : ℤ)) - (b - (k + (1 : ℤ))) + (1 : ℤ)) → (((↑(K.1 - (1 : ℕ)) :
            ℤ) = k - (1 : ℤ)) → ((∀ (x : Int), ∀ (y : Int), (0≤y ∧ y≤2*k ∧ -k≤x ∧ x≤k ∧ -y-1≤x ∧
            x≤y+1 ∧ -(2*k-y+1)≤x ∧ x≤2*k-y+1) → ((⟨x,y⟩:GaussianInt)∈FootprintVertices
            (DiamondTile K.1))) → ((b = (2 : ℤ) * k + (1 : ℤ) + a) → (
        let t : Int := -a
        let zA : GaussianInt := ⟨-t,2*k+1-t⟩
        (zA+1)∈FootprintVertices (DiamondTile K.1)))))) ) := by
  classical
  intro K hk k a b hdpred hcast childMem hb t zA
  have he : zA+1=(⟨1-t,2*k+1-t⟩:GaussianInt) := by ext <;> simp [zA]; ring
  rw [he]
  exact childMem (1-t) (2*k+1-t) (by constructor <;> omega)

private theorem hcs :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        ∀ (a : ℤ), ∀ (b : ℤ), (k < b ∧ b ≤ (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ -(k - (1 :
            ℤ)) ≤ a + k ∧ a + k ≤ k - (1 : ℤ) ∧ k < a + k + (1 : ℤ) + b ∧ a + k ≤ b - (k + (1 :
            ℤ)) + (1 : ℤ) ∧ b ≤ (1 : ℤ) + (a + k) + (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ a +
            k ≤ (2 : ℤ) * (k - (1 : ℤ)) - (b - (k + (1 : ℤ))) + (1 : ℤ)) → (((↑(K.1 - (1 : ℕ)) :
            ℤ) = k - (1 : ℤ)) → ((∀ (x : Int), ∀ (y : Int), (0≤y ∧ y≤2*k ∧ -k≤x ∧ x≤k ∧ -y-1≤x ∧
            x≤y+1 ∧ -(2*k-y+1)≤x ∧ x≤2*k-y+1) → ((⟨x,y⟩:GaussianInt)∈FootprintVertices
            (DiamondTile K.1))) → ((b = (2 : ℤ) * k + (1 : ℤ) + a) → (
        let t : Int := -a
        let zA : GaussianInt := ⟨-t,2*k+1-t⟩
        (zA-⟨0,1⟩)∈FootprintVertices (DiamondTile K.1)))))) ) := by
  classical
  intro K hk k a b hdpred hcast childMem hb t zA
  have hs : zA-⟨0,1⟩=(⟨-t,2*k-t⟩:GaussianInt) := by ext <;> simp [zA]; ring
  rw [hs]
  exact childMem (-t) (2*k-t) (by constructor <;> omega)

private theorem hpw :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        let d : GaussianInt := ⟨-k,k+1⟩
        ∀ (a : ℤ), ∀ (b : ℤ), (k < b ∧ b ≤ (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ -(k - (1 :
            ℤ)) ≤ a + k ∧ a + k ≤ k - (1 : ℤ) ∧ k < a + k + (1 : ℤ) + b ∧ a + k ≤ b - (k + (1 :
            ℤ)) + (1 : ℤ) ∧ b ≤ (1 : ℤ) + (a + k) + (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ a +
            k ≤ (2 : ℤ) * (k - (1 : ℤ)) - (b - (k + (1 : ℤ))) + (1 : ℤ)) → (((↑(K.1 - (1 : ℕ)) :
            ℤ) = k - (1 : ℤ)) → ((∀ (w : GaussianInt), (0≤w.im ∧ w.im≤2*(k-1) ∧ -(k-1)≤w.re ∧
            w.re≤k-1 ∧ -w.im-1≤w.re ∧ w.re≤w.im+1 ∧ -(2*(k-1)-w.im+1)≤w.re ∧ w.re≤2*(k-1)-w.im+1)
            → (w∈FootprintVertices (DiamondTile (K.1-1)))) → ((b = (2 : ℤ) * k + (1 : ℤ) + a) → (
        let t : Int := -a
        let zA : GaussianInt := ⟨-t,2*k+1-t⟩
        (zA-1)-d∈FootprintVertices (DiamondTile (K.1-1))))))) ) := by
  classical
  intro K hk k d a b hdpred hcast predFoot hb t zA
  apply predFoot
  constructor <;> simp [zA,d] <;> omega

private theorem hpn :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        let d : GaussianInt := ⟨-k,k+1⟩
        ∀ (a : ℤ), ∀ (b : ℤ), (k < b ∧ b ≤ (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ -(k - (1 :
            ℤ)) ≤ a + k ∧ a + k ≤ k - (1 : ℤ) ∧ k < a + k + (1 : ℤ) + b ∧ a + k ≤ b - (k + (1 :
            ℤ)) + (1 : ℤ) ∧ b ≤ (1 : ℤ) + (a + k) + (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ a +
            k ≤ (2 : ℤ) * (k - (1 : ℤ)) - (b - (k + (1 : ℤ))) + (1 : ℤ)) → (((↑(K.1 - (1 : ℕ)) :
            ℤ) = k - (1 : ℤ)) → ((∀ (w : GaussianInt), (0≤w.im ∧ w.im≤2*(k-1) ∧ -(k-1)≤w.re ∧
            w.re≤k-1 ∧ -w.im-1≤w.re ∧ w.re≤w.im+1 ∧ -(2*(k-1)-w.im+1)≤w.re ∧ w.re≤2*(k-1)-w.im+1)
            → (w∈FootprintVertices (DiamondTile (K.1-1)))) → ((b = (2 : ℤ) * k + (1 : ℤ) + a) → (
        let t : Int := -a
        let zA : GaussianInt := ⟨-t,2*k+1-t⟩
        (zA+⟨0,1⟩)-d∈FootprintVertices (DiamondTile (K.1-1))))))) ) := by
  classical
  intro K hk k d a b hdpred hcast predFoot hb t zA
  apply predFoot
  constructor <;> simp [zA,d] <;> omega

private theorem hEAt277 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        ∀ (a : ℤ),
        let Q : Int → Int → Int := fun x y =>
          (Int.natAbs x : Int) * ((Int.natAbs x : Int)-1)/2 - (x-y)^2/4
        (∀ (w : GaussianInt), (w ∈ FootprintVertices (DiamondTile K.1)) → (f w=Q w.re w.im)) → (
        let t : Int := -a
        let zA : GaussianInt := ⟨-t,2*k+1-t⟩
        ((zA+1)∈FootprintVertices (DiamondTile K.1)) → (f (zA+1)=Q (1-t) (2*k+1-t))) ) := by
  classical
  intro K f k a Q childValue t zA hce
  have he : zA+1=(⟨1-t,2*k+1-t⟩:GaussianInt) := by ext <;> simp [zA]; ring
  rw [he]
  have hm : (⟨1-t,2*k+1-t⟩:GaussianInt)∈FootprintVertices (DiamondTile K.1) := by
    rw [← he]
    exact hce
  exact childValue _ hm

private theorem hSAt284 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        ∀ (a : ℤ),
        let Q : Int → Int → Int := fun x y =>
          (Int.natAbs x : Int) * ((Int.natAbs x : Int)-1)/2 - (x-y)^2/4
        (∀ (w : GaussianInt), (w ∈ FootprintVertices (DiamondTile K.1)) → (f w=Q w.re w.im)) → (
        let t : Int := -a
        let zA : GaussianInt := ⟨-t,2*k+1-t⟩
        ((zA-⟨0,1⟩)∈FootprintVertices (DiamondTile K.1)) → (f (zA-⟨0,1⟩)=Q (-t) (2*k-t))) ) := by
  classical
  intro K f k a Q childValue t zA hcs
  have he : zA-⟨0,1⟩=(⟨-t,2*k-t⟩:GaussianInt) := by ext <;> simp [zA]; ring
  rw [he]
  have hm : (⟨-t,2*k-t⟩:GaussianInt)∈FootprintVertices (DiamondTile K.1) := by
    rw [← he]
    exact hcs
  exact childValue _ hm

private theorem hPC :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        let d : GaussianInt := ⟨-k,k+1⟩
        ∀ (a : ℤ),
        let Q : Int → Int → Int := fun x y =>
          (Int.natAbs x : Int) * ((Int.natAbs x : Int)-1)/2 - (x-y)^2/4
        (∀ (y : GaussianInt), (y-d∈FootprintVertices (DiamondTile (K.1-1))) → (f y=Q (y-d).re
            (y-d).im+y.re-k*y.im+B)) → (
        let t : Int := -a
        let zA : GaussianInt := ⟨-t,2*k+1-t⟩
        (zA-d∈FootprintVertices (DiamondTile (K.1-1))) → (f zA=Q (k-t) (k-t)+(-t)-k*(2*k+1-t)+B))
            ) := by
  classical
  intro K f B k d a Q predTranslatedValue t zA hp0
  have hv := predTranslatedValue zA (by simpa [zA,d] using hp0)
  convert hv using 1; simp [zA,d]; ring

private theorem hPW :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        let d : GaussianInt := ⟨-k,k+1⟩
        ∀ (a : ℤ),
        let Q : Int → Int → Int := fun x y =>
          (Int.natAbs x : Int) * ((Int.natAbs x : Int)-1)/2 - (x-y)^2/4
        (∀ (y : GaussianInt), (y-d∈FootprintVertices (DiamondTile (K.1-1))) → (f y=Q (y-d).re
            (y-d).im+y.re-k*y.im+B)) → (
        let t : Int := -a
        let zA : GaussianInt := ⟨-t,2*k+1-t⟩
        ((zA-1)-d∈FootprintVertices (DiamondTile (K.1-1))) → (f (zA-1)=Q (k-t-1)
            (k-t)+(-t-1)-k*(2*k+1-t)+B)) ) := by
  classical
  intro K f B k d a Q predTranslatedValue t zA hpw
  have he : (zA-1)-d=(⟨k-t-1,k-t⟩:GaussianInt) := by ext <;> simp [zA,d] <;> ring
  have hv := predTranslatedValue (zA-1) hpw
  convert hv using 1; simp [zA,d]; ring

private theorem hPN :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        let d : GaussianInt := ⟨-k,k+1⟩
        ∀ (a : ℤ),
        let Q : Int → Int → Int := fun x y =>
          (Int.natAbs x : Int) * ((Int.natAbs x : Int)-1)/2 - (x-y)^2/4
        (∀ (y : GaussianInt), (y-d∈FootprintVertices (DiamondTile (K.1-1))) → (f y=Q (y-d).re
            (y-d).im+y.re-k*y.im+B)) → (
        let t : Int := -a
        let zA : GaussianInt := ⟨-t,2*k+1-t⟩
        ((zA+⟨0,1⟩)-d∈FootprintVertices (DiamondTile (K.1-1))) → (f (zA+⟨0,1⟩)=Q (k-t)
            (k+1-t)+(-t)-k*(2*k+2-t)+B)) ) := by
  classical
  intro K f B k d a Q predTranslatedValue t zA hpn
  have he : (zA+⟨0,1⟩)-d=(⟨k-t,k+1-t⟩:GaussianInt) := by ext <;> simp [zA,d] <;> ring
  have hv := predTranslatedValue (zA+⟨0,1⟩) hpn
  convert hv using 1; simp [zA,d]; ring

private theorem qC :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        ∀ (a : ℤ), ∀ (b : ℤ), (k < b ∧ b ≤ (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ -(k - (1 :
            ℤ)) ≤ a + k ∧ a + k ≤ k - (1 : ℤ) ∧ k < a + k + (1 : ℤ) + b ∧ a + k ≤ b - (k + (1 :
            ℤ)) + (1 : ℤ) ∧ b ≤ (1 : ℤ) + (a + k) + (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ a +
            k ≤ (2 : ℤ) * (k - (1 : ℤ)) - (b - (k + (1 : ℤ))) + (1 : ℤ)) → (
        let Q : Int → Int → Int := fun x y =>
          (Int.natAbs x : Int) * ((Int.natAbs x : Int)-1)/2 - (x-y)^2/4
        let T : Int → Int := fun n => n*(n-1)/2
        (∀ (m : Int), (2*m+1)^2/4=m^2+m) → (
        let t : Int := -a
        let zA : GaussianInt := ⟨-t,2*k+1-t⟩
        (f zA=Q (-t) (2*k+1-t)) → ((f zA=Q (k-t) (k-t)+(-t)-k*(2*k+1-t)+B) → ((f (zA-1)=Q (k-t-1)
            (k-t)+(-t-1)-k*(2*k+1-t)+B) → ((f (zA+⟨0,1⟩)=Q (k-t) (k+1-t)+(-t)-k*(2*k+2-t)+B) → (Q
            (-t) (2*k+1-t)=T t-(k*k+k))))))) ) := by
  classical
  intro K f B k a b hdpred Q T floorOdd t zA hC hPC hPW hPN
  unfold Q
  have ha : (Int.natAbs (-t):Int)=t := by
    rw [Int.natCast_natAbs,abs_of_nonpos (show -t≤0 by omega)]; omega
  have hs : (-t-(2*k+1-t))^2/4=k*k+k := by
    rw [show -t-(2*k+1-t)=2*(-k-1)+1 by ring,floorOdd]
    ring
  rw [ha,hs]

private theorem qE :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        ∀ (a : ℤ), ∀ (b : ℤ), (k < b ∧ b ≤ (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ -(k - (1 :
            ℤ)) ≤ a + k ∧ a + k ≤ k - (1 : ℤ) ∧ k < a + k + (1 : ℤ) + b ∧ a + k ≤ b - (k + (1 :
            ℤ)) + (1 : ℤ) ∧ b ≤ (1 : ℤ) + (a + k) + (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ a +
            k ≤ (2 : ℤ) * (k - (1 : ℤ)) - (b - (k + (1 : ℤ))) + (1 : ℤ)) → (
        let Q : Int → Int → Int := fun x y =>
          (Int.natAbs x : Int) * ((Int.natAbs x : Int)-1)/2 - (x-y)^2/4
        let T : Int → Int := fun n => n*(n-1)/2
        (∀ (m : Int), (2*m)^2/4=m^2) → (
        let t : Int := -a
        let zA : GaussianInt := ⟨-t,2*k+1-t⟩
        (f zA=Q (-t) (2*k+1-t)) → ((f zA=Q (k-t) (k-t)+(-t)-k*(2*k+1-t)+B) → ((f (zA-1)=Q (k-t-1)
            (k-t)+(-t-1)-k*(2*k+1-t)+B) → ((f (zA+⟨0,1⟩)=Q (k-t) (k+1-t)+(-t)-k*(2*k+2-t)+B) → (Q
            (1-t) (2*k+1-t)=T (t-1)-k*k)))))) ) := by
  classical
  intro K f B k a b hdpred Q T floorEven t zA hC hPC hPW hPN
  unfold Q
  have ha : (Int.natAbs (1-t):Int)=t-1 := by
    rw [Int.natCast_natAbs,abs_of_nonpos (show 1-t≤0 by omega)]; omega
  have hs : ((1-t)-(2*k+1-t))^2/4=k*k := by
    rw [show (1-t)-(2*k+1-t)=2*(-k) by ring,floorEven]
    ring
  rw [ha,hs]

private theorem qS :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        ∀ (a : ℤ), ∀ (b : ℤ), (k < b ∧ b ≤ (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ -(k - (1 :
            ℤ)) ≤ a + k ∧ a + k ≤ k - (1 : ℤ) ∧ k < a + k + (1 : ℤ) + b ∧ a + k ≤ b - (k + (1 :
            ℤ)) + (1 : ℤ) ∧ b ≤ (1 : ℤ) + (a + k) + (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ a +
            k ≤ (2 : ℤ) * (k - (1 : ℤ)) - (b - (k + (1 : ℤ))) + (1 : ℤ)) → (
        let Q : Int → Int → Int := fun x y =>
          (Int.natAbs x : Int) * ((Int.natAbs x : Int)-1)/2 - (x-y)^2/4
        let T : Int → Int := fun n => n*(n-1)/2
        (∀ (m : Int), (2*m)^2/4=m^2) → (
        let t : Int := -a
        let zA : GaussianInt := ⟨-t,2*k+1-t⟩
        (f zA=Q (-t) (2*k+1-t)) → ((f zA=Q (k-t) (k-t)+(-t)-k*(2*k+1-t)+B) → ((f (zA-1)=Q (k-t-1)
            (k-t)+(-t-1)-k*(2*k+1-t)+B) → ((f (zA+⟨0,1⟩)=Q (k-t) (k+1-t)+(-t)-k*(2*k+2-t)+B) → (Q
            (-t) (2*k-t)=T t-k*k)))))) ) := by
  classical
  intro K f B k a b hdpred Q T floorEven t zA hC hPC hPW hPN
  unfold Q
  have ha : (Int.natAbs (-t):Int)=t := by
    rw [Int.natCast_natAbs,abs_of_nonpos (show -t≤0 by omega)]; omega
  have hs : (-t-(2*k-t))^2/4=k*k := by
    rw [show -t-(2*k-t)=2*(-k) by ring,floorEven]
    ring
  rw [ha,hs]

private theorem qPC :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        ∀ (a : ℤ), ∀ (b : ℤ), (k < b ∧ b ≤ (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ -(k - (1 :
            ℤ)) ≤ a + k ∧ a + k ≤ k - (1 : ℤ) ∧ k < a + k + (1 : ℤ) + b ∧ a + k ≤ b - (k + (1 :
            ℤ)) + (1 : ℤ) ∧ b ≤ (1 : ℤ) + (a + k) + (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ a +
            k ≤ (2 : ℤ) * (k - (1 : ℤ)) - (b - (k + (1 : ℤ))) + (1 : ℤ)) → (((↑(K.1 - (1 : ℕ)) :
            ℤ) = k - (1 : ℤ)) → (
        let Q : Int → Int → Int := fun x y =>
          (Int.natAbs x : Int) * ((Int.natAbs x : Int)-1)/2 - (x-y)^2/4
        let T : Int → Int := fun n => n*(n-1)/2
        (b = (2 : ℤ) * k + (1 : ℤ) + a) → (
        let t : Int := -a
        let zA : GaussianInt := ⟨-t,2*k+1-t⟩
        (f zA=Q (-t) (2*k+1-t)) → ((f zA=Q (k-t) (k-t)+(-t)-k*(2*k+1-t)+B) → ((f (zA-1)=Q (k-t-1)
            (k-t)+(-t-1)-k*(2*k+1-t)+B) → ((f (zA+⟨0,1⟩)=Q (k-t) (k+1-t)+(-t)-k*(2*k+2-t)+B) →
            ((Q (-t) (2*k+1-t)=T t-(k*k+k)) → (Q (k-t) (k-t)=T (k-t))))))))) ) := by
  classical
  intro K f B k a b hdpred hcast Q T hb t zA hC hPC hPW hPN qC
  unfold Q
  have ha : (Int.natAbs (k-t):Int)=k-t := by
    rw [Int.natCast_natAbs,abs_of_nonneg (show 0≤k-t by omega)]
  rw [ha]
  norm_num [T]

private theorem qPWeq :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let k : Int := K.1
        ∀ (a : ℤ),
        let Q : Int → Int → Int := fun x y =>
          (Int.natAbs x : Int) * ((Int.natAbs x : Int)-1)/2 - (x-y)^2/4
        let t : Int := -a
        t = k → Q (k - t - (1 : ℤ)) (k - t) = (0 : ℤ) ) := by
  classical
  intro K k a Q t heq
  rw [heq]
  norm_num [Q,Int.natCast_natAbs]

private theorem hEastDiff :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        ∀ (a : ℤ),
        let Q : Int → Int → Int := fun x y =>
          (Int.natAbs x : Int) * ((Int.natAbs x : Int)-1)/2 - (x-y)^2/4
        let T : Int → Int := fun n => n*(n-1)/2
        (∀ (n : Int), T (n-1)-T n=1-n) → (
        let t : Int := -a
        let zA : GaussianInt := ⟨-t,2*k+1-t⟩
        (f zA=Q (-t) (2*k+1-t)) → ((f (zA+1)=Q (1-t) (2*k+1-t)) → ((Q (-t) (2*k+1-t)=T t-(k*k+k))
            → ((Q (1-t) (2*k+1-t)=T (t-1)-k*k) → (f (zA+1)-f zA=k+1-t))))) ) := by
  classical
  intro K f k a Q T tdiffRev t zA hC hE qC qE
  rw [hE,hC,qE,qC]
  calc
    T (t-1)-k*k-(T t-(k*k+k))=T (t-1)-T t+k := by ring
    _ = (1-t)+k := by rw [tdiffRev]
    _ = k+1-t := by ring

private theorem hWestDiff :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        ∀ (a : ℤ),
        let Q : Int → Int → Int := fun x y =>
          (Int.natAbs x : Int) * ((Int.natAbs x : Int)-1)/2 - (x-y)^2/4
        let T : Int → Int := fun n => n*(n-1)/2
        (∀ (n : Int), T (n-1)-T n=1-n) → (
        let t : Int := -a
        let zA : GaussianInt := ⟨-t,2*k+1-t⟩
        (f zA=Q (k-t) (k-t)+(-t)-k*(2*k+1-t)+B) → ((f (zA-1)=Q (k-t-1)
            (k-t)+(-t-1)-k*(2*k+1-t)+B) → ((Q (k-t) (k-t)=T (k-t)) → (((t<k) → (Q (k-t-1) (k-t)=T
            (k-t-1))) → (t < k → f (zA - (1 : GaussianInt)) - f zA = t - k))))) ) := by
  classical
  intro K f B k a Q T tdiffRev t zA hPC hPW qPC qPWlt hlt
  rw [hPW,hPC,qPWlt hlt,qPC]
  calc
    T (k-t-1) + (-t-1)-k*(2*k+1-t)+B -
        (T (k-t)+(-t)-k*(2*k+1-t)+B) = T (k-t-1)-T (k-t)-1 := by ring
    _ = (1-(k-t))-1 := by rw [tdiffRev]
    _ = t-k := by ring

private theorem hNorthDiff :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        ∀ (a : ℤ),
        let Q : Int → Int → Int := fun x y =>
          (Int.natAbs x : Int) * ((Int.natAbs x : Int)-1)/2 - (x-y)^2/4
        let T : Int → Int := fun n => n*(n-1)/2
        let t : Int := -a
        let zA : GaussianInt := ⟨-t,2*k+1-t⟩
        (f zA=Q (k-t) (k-t)+(-t)-k*(2*k+1-t)+B) → ((f (zA+⟨0,1⟩)=Q (k-t)
            (k+1-t)+(-t)-k*(2*k+2-t)+B) → ((Q (k-t) (k-t)=T (k-t)) → ((Q (k-t) (k+1-t)=T (k-t)) →
            (f (zA+⟨0,1⟩)-f zA= -k)))) ) := by
  classical
  intro K f B k a Q T t zA hPC hPN qPC qPN
  rw [hPN,hPC,qPN,qPC]
  ring

private theorem hSouthDiff :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        ∀ (a : ℤ),
        let Q : Int → Int → Int := fun x y =>
          (Int.natAbs x : Int) * ((Int.natAbs x : Int)-1)/2 - (x-y)^2/4
        let T : Int → Int := fun n => n*(n-1)/2
        let t : Int := -a
        let zA : GaussianInt := ⟨-t,2*k+1-t⟩
        (f zA=Q (-t) (2*k+1-t)) → ((f (zA-⟨0,1⟩)=Q (-t) (2*k-t)) → ((Q (-t) (2*k+1-t)=T
            t-(k*k+k)) → ((Q (-t) (2*k-t)=T t-k*k) → (f (zA-⟨0,1⟩)-f zA=k)))) ) := by
  classical
  intro K f k a Q T t zA hC hS qC qS
  rw [hS,hC,qS,qC]
  ring

private theorem hWestDiffEq :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        ∀ (a : ℤ),
        let Q : Int → Int → Int := fun x y =>
          (Int.natAbs x : Int) * ((Int.natAbs x : Int)-1)/2 - (x-y)^2/4
        let T : Int → Int := fun n => n*(n-1)/2
        let t : Int := -a
        let zA : GaussianInt := ⟨-t,2*k+1-t⟩
        (f zA=Q (k-t) (k-t)+(-t)-k*(2*k+1-t)+B) → ((f (zA-1)=Q (k-t-1)
            (k-t)+(-t-1)-k*(2*k+1-t)+B) → ((Q (k-t) (k-t)=T (k-t)) → (((t=k) → (Q (k-t-1)
            (k-t)=0)) → (t=k → f (zA-1)-f zA= -1)))) ) := by
  classical
  intro K f B k a Q T t zA hPC hPW qPC qPWeq heq
  rw [hPW,hPC,qPWeq heq,qPC]
  rw [heq]
  simp [T]
  ring

private theorem hneq :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1),
        let k : Int := K.1
        let r : GaussianInt := ⟨-2*k,0⟩
        let child := P5352T2Sources K hk 0
        (child.1=DiamondTile K.1) → (∀ (a : ℤ),
        let t : Int := -a
        let zA : GaussianInt := ⟨-t,2*k+1-t⟩
        (zA-r ∈ FootprintVertices child.1 ↔ t=k) → ((zA - r ∉ FootprintVertices child.1) →
            (t≠k))) ) := by
  classical
  intro K hk k r child hchildTile a t zA hcomp hmem heq
  apply hmem
  exact hchildTile.symm ▸ hcomp.mpr heq

private theorem heAt394 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        ∀ (a : ℤ), ∀ (b : ℤ), (k < b ∧ b ≤ (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ -(k - (1 :
            ℤ)) ≤ a + k ∧ a + k ≤ k - (1 : ℤ) ∧ k < a + k + (1 : ℤ) + b ∧ a + k ≤ b - (k + (1 :
            ℤ)) + (1 : ℤ) ∧ b ≤ (1 : ℤ) + (a + k) + (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ a +
            k ≤ (2 : ℤ) * (k - (1 : ℤ)) - (b - (k + (1 : ℤ))) + (1 : ℤ)) → (((↑(K.1 - (1 : ℕ)) :
            ℤ) = k - (1 : ℤ)) → ((∀ (x : Int), ∀ (y : Int), (0≤y ∧ y≤2*k ∧ -k≤x ∧ x≤k ∧ -y-1≤x ∧
            x≤y+1 ∧ -(2*k-y+1)≤x ∧ x≤2*k-y+1) → ((⟨x,y⟩:GaussianInt)∈FootprintVertices
            (DiamondTile K.1))) → ((b = (2 : ℤ) * k + a) → (
        let t : Int := -a
        let zB : GaussianInt := ⟨-t,2*k-t⟩
        (zB+1)∈FootprintVertices (DiamondTile K.1)))))) ) := by
  classical
  intro K hk k a b hdpred hcast childMem hb t zB
  have heq : zB+1=(⟨1-t,2*k-t⟩:GaussianInt) := by ext <;> simp [zB]; ring
  rw [heq]
  exact childMem (1-t) (2*k-t) (by constructor <;> omega)

private theorem hw :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        ∀ (a : ℤ), ∀ (b : ℤ), (k < b ∧ b ≤ (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ -(k - (1 :
            ℤ)) ≤ a + k ∧ a + k ≤ k - (1 : ℤ) ∧ k < a + k + (1 : ℤ) + b ∧ a + k ≤ b - (k + (1 :
            ℤ)) + (1 : ℤ) ∧ b ≤ (1 : ℤ) + (a + k) + (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ a +
            k ≤ (2 : ℤ) * (k - (1 : ℤ)) - (b - (k + (1 : ℤ))) + (1 : ℤ)) → (((↑(K.1 - (1 : ℕ)) :
            ℤ) = k - (1 : ℤ)) → ((∀ (x : Int), ∀ (y : Int), (0≤y ∧ y≤2*k ∧ -k≤x ∧ x≤k ∧ -y-1≤x ∧
            x≤y+1 ∧ -(2*k-y+1)≤x ∧ x≤2*k-y+1) → ((⟨x,y⟩:GaussianInt)∈FootprintVertices
            (DiamondTile K.1))) → ((b = (2 : ℤ) * k + a) → (
        let t : Int := -a
        let zB : GaussianInt := ⟨-t,2*k-t⟩
        (zB-1)∈FootprintVertices (DiamondTile K.1)))))) ) := by
  classical
  intro K hk k a b hdpred hcast childMem hb t zB
  have heq : zB-1=(⟨-t-1,2*k-t⟩:GaussianInt) := by ext <;> simp [zB]
  rw [heq]
  exact childMem (-t-1) (2*k-t) (by constructor <;> omega)

private theorem hnAt402 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        ∀ (a : ℤ), ∀ (b : ℤ), (k < b ∧ b ≤ (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ -(k - (1 :
            ℤ)) ≤ a + k ∧ a + k ≤ k - (1 : ℤ) ∧ k < a + k + (1 : ℤ) + b ∧ a + k ≤ b - (k + (1 :
            ℤ)) + (1 : ℤ) ∧ b ≤ (1 : ℤ) + (a + k) + (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ a +
            k ≤ (2 : ℤ) * (k - (1 : ℤ)) - (b - (k + (1 : ℤ))) + (1 : ℤ)) → (((↑(K.1 - (1 : ℕ)) :
            ℤ) = k - (1 : ℤ)) → ((∀ (x : Int), ∀ (y : Int), (0≤y ∧ y≤2*k ∧ -k≤x ∧ x≤k ∧ -y-1≤x ∧
            x≤y+1 ∧ -(2*k-y+1)≤x ∧ x≤2*k-y+1) → ((⟨x,y⟩:GaussianInt)∈FootprintVertices
            (DiamondTile K.1))) → ((b = (2 : ℤ) * k + a) → (
        let t : Int := -a
        let zB : GaussianInt := ⟨-t,2*k-t⟩
        (zB+⟨0,1⟩)∈FootprintVertices (DiamondTile K.1)))))) ) := by
  classical
  intro K hk k a b hdpred hcast childMem hb t zB
  have heq : zB+⟨0,1⟩=(⟨-t,2*k+1-t⟩:GaussianInt) := by ext <;> simp [zB]; ring
  rw [heq]
  exact childMem (-t) (2*k+1-t) (by constructor <;> omega)

private theorem hsAt406 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        ∀ (a : ℤ), ∀ (b : ℤ), (k < b ∧ b ≤ (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ -(k - (1 :
            ℤ)) ≤ a + k ∧ a + k ≤ k - (1 : ℤ) ∧ k < a + k + (1 : ℤ) + b ∧ a + k ≤ b - (k + (1 :
            ℤ)) + (1 : ℤ) ∧ b ≤ (1 : ℤ) + (a + k) + (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ a +
            k ≤ (2 : ℤ) * (k - (1 : ℤ)) - (b - (k + (1 : ℤ))) + (1 : ℤ)) → (((↑(K.1 - (1 : ℕ)) :
            ℤ) = k - (1 : ℤ)) → ((∀ (x : Int), ∀ (y : Int), (0≤y ∧ y≤2*k ∧ -k≤x ∧ x≤k ∧ -y-1≤x ∧
            x≤y+1 ∧ -(2*k-y+1)≤x ∧ x≤2*k-y+1) → ((⟨x,y⟩:GaussianInt)∈FootprintVertices
            (DiamondTile K.1))) → ((b = (2 : ℤ) * k + a) → (
        let t : Int := -a
        let zB : GaussianInt := ⟨-t,2*k-t⟩
        (zB-⟨0,1⟩)∈FootprintVertices (DiamondTile K.1)))))) ) := by
  classical
  intro K hk k a b hdpred hcast childMem hb t zB
  have heq : zB-⟨0,1⟩=(⟨-t,2*k-t-1⟩:GaussianInt) := by ext <;> simp [zB]
  rw [heq]
  exact childMem (-t) (2*k-t-1) (by constructor <;> omega)

private theorem hdomAt410 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let k : Int := K.1
        ∀ (a : ℤ),
        let t : Int := -a
        let zB : GaussianInt := ⟨-t,2*k-t⟩
        (zB∈FootprintVertices (DiamondTile K.1)) → (zB∈DiamondVertexDomains K false) ) := by
  classical
  intro K k a t zB hc
  obtain ⟨_,_,_,hfp,_,_⟩ := DiamondTileOdometerRestriction K
  exact hfp ▸ hc

private theorem hnot :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let k : Int := K.1
        ∀ (a : ℤ), ∀ (b : ℤ), (k < b ∧ b ≤ (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ -(k - (1 :
            ℤ)) ≤ a + k ∧ a + k ≤ k - (1 : ℤ) ∧ k < a + k + (1 : ℤ) + b ∧ a + k ≤ b - (k + (1 :
            ℤ)) + (1 : ℤ) ∧ b ≤ (1 : ℤ) + (a + k) + (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧ a +
            k ≤ (2 : ℤ) * (k - (1 : ℤ)) - (b - (k + (1 : ℤ))) + (1 : ℤ)) → (((↑(K.1 - (1 : ℕ)) :
            ℤ) = k - (1 : ℤ)) → ((b = (2 : ℤ) * k + a) → (
        let t : Int := -a
        let zB : GaussianInt := ⟨-t,2*k-t⟩
        zB∉DiamondVertexDomains K true))) ) := by
  classical
  intro K k a b hdpred hcast hb t zB
  change ¬ (Int.natAbs zB.re+Int.natAbs (zB.im-(K.1:Int))≤K.1-1)
  intro hh
  have hhI : ((Int.natAbs zB.re+Int.natAbs (zB.im-(K.1:Int)):Nat):Int)≤
      ((K.1-1:Nat):Int) := by exact_mod_cast hh
  have ha : (Int.natAbs zB.re:Int)=t := by
    change (Int.natAbs (-t):Int)=t
    rw [Int.natCast_natAbs,abs_of_nonpos (show -t≤0 by omega)]
    omega
  have hb' : (Int.natAbs (zB.im-(K.1:Int)):Int)=k-t := by
    change (Int.natAbs (2*k-t-(K.1:Int)):Int)=k-t
    rw [Int.natCast_natAbs,abs_of_nonneg (show 0≤2*k-t-(K.1:Int) by dsimp [k]; omega)]
    dsimp [k]
    omega
  rw [Int.natCast_add,ha,hb',hcast] at hhI
  omega

private theorem htable' :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let k : Int := K.1
        ∀ (a : ℤ),
        let t : Int := -a
        let zB : GaussianInt := ⟨-t,2*k-t⟩
        (FourNeighborLaplacian (DiamondOdometer K) zB = (1 : ℤ)) → ((DiamondOdometer K
            (zB+1)-DiamondOdometer K zB)+ (DiamondOdometer K (zB-1)-DiamondOdometer K zB)+
            (DiamondOdometer K (zB+⟨0,1⟩)-DiamondOdometer K zB)+ (DiamondOdometer K
            (zB-⟨0,1⟩)-DiamondOdometer K zB)=1) ) := by
  classical
  intro K k a t zB htable
  rw [FourNeighborLaplacian] at htable
  linarith

private theorem hcompAt447 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), (IntegerLatticeFunction) → (
        let k : Int := K.1
        let r : GaussianInt := ⟨-2*k,0⟩
        let child := P5352T2Sources K hk 0
        (child.1=DiamondTile K.1) → (∀ (a : ℤ), ∀ (b : ℤ), (k < b ∧ b ≤ (2 : ℤ) * (k - (1 : ℤ)) +
            (k + (1 : ℤ)) ∧ -(k - (1 : ℤ)) ≤ a + k ∧ a + k ≤ k - (1 : ℤ) ∧ k < a + k + (1 : ℤ) +
            b ∧ a + k ≤ b - (k + (1 : ℤ)) + (1 : ℤ) ∧ b ≤ (1 : ℤ) + (a + k) + (2 : ℤ) * (k - (1 :
            ℤ)) + (k + (1 : ℤ)) ∧ a + k ≤ (2 : ℤ) * (k - (1 : ℤ)) - (b - (k + (1 : ℤ))) + (1 :
            ℤ)) → (((↑(K.1 - (1 : ℕ)) : ℤ) = k - (1 : ℤ)) → ((b = (2 : ℤ) * k + a) → (
        let t : Int := -a
        let zB : GaussianInt := ⟨-t,2*k-t⟩
        zB-r∉FootprintVertices child.1))))) ) := by
  classical
  intro K hk f k r child hchildTile a b hdpred hcast hb t zB hmem
  have hd := (P5352T2DomainRows K (zB-r)).1.mp (hchildTile ▸ hmem)
  simp [zB,r] at hd
  omega

end SecondPredecessorProof

theorem P5352T2Predecessor2 (K : DiamondParameter) (hk : 1 < K.1)
    (f : IntegerLatticeFunction) (B : Int) (z : GaussianInt) :
    let A := P5352T2Sources K hk 0
    let D := P5352T2Sources K hk 3
    let M := (P5352T2PlacementData K.1 2).2 2
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
    have lap_identity (g : IntegerLatticeFunction) (x : GaussianInt) :
        FourNeighborLaplacian g x =
          (g (x+1)-g x)+(g (x-1)-g x)+
            (g (x+⟨0,1⟩)-g x)+(g (x-⟨0,1⟩)-g x) := FourNeighborLaplacianProperties.differences g x
    let k : Int := K.1
    let d : GaussianInt := ⟨-k,k+1⟩
    let r : GaussianInt := ⟨-2*k,0⟩
    let child := P5352T2Sources K hk 0
    let pred := P5352T2Sources K hk 3
    let M := (P5352T2PlacementData K.1 2).2 2
    have hkI : 2 ≤ k := by dsimp [k]; exact_mod_cast (show 2 ≤ K.1 by omega)
    have hm : M.1=d ∧ M.2.1=⟨1,-k⟩ ∧ M.2.2=r := by
      simp [M,d,r,P5352T2PlacementData,k]
    rcases hm with ⟨hdisp,hcoeff,hr⟩
    have hchildTile : child.1=DiamondTile K.1 := by simp [child,P5352T2Sources]
    change
      (∀ y, y ∈ FootprintVertices child.1 → f y=child.2.1 y) →
      (∀ y, y-M.1 ∈ FootprintVertices pred.1 →
        f y=pred.2.1 (y-M.1)+M.2.1.re*y.re+M.2.1.im*y.im+B) →
      z ∈ FootprintVertices child.1 → z-M.1 ∈ FootprintVertices pred.1 →
      (∀ y, y=z ∨ y=z+1 ∨ y=z-1 ∨ y=z+⟨0,1⟩ ∨ y=z-⟨0,1⟩ →
        y ∈ FootprintVertices child.1 ∨ y-M.1 ∈ FootprintVertices pred.1) →
      (z-M.2.2 ∈ FootprintVertices child.1 → FourNeighborLaplacian f z=0) ∧
      (z-M.2.2 ∉ FootprintVertices child.1 → FourNeighborLaplacian f z=1)
    intro hchild hpred hz hpz hcover
    rw [hdisp] at hpz hcover
    rw [hdisp,hcoeff] at hpred
    rw [hr] at ⊢
    have hdchild := (P5352T2DomainRows K z).1.mp hz
    have hdpred := (P5352T2DomainRows ⟨K.1-1,by omega⟩ (z-d)).1.mp hpz
    rcases z with ⟨a,b⟩
    simp only [Int.reduceNeg, Zsqrtd.im_sub, Int.sub_nonneg, Order.add_one_le_iff,
        tsub_le_iff_right, Zsqrtd.re_sub, sub_neg_eq_add, neg_sub, neg_add_rev,
        neg_add_le_iff_le_add, d] at hdpred
    have hcast : ((K.1-1 : Nat) : Int)=k-1 := by dsimp [k]; omega
    rw [hcast] at hdpred
    change (0≤b ∧ b≤2*k ∧ -k≤a ∧ a≤k ∧ -b-1≤a ∧ a≤b+1 ∧
      -(2*k-b+1)≤a ∧ a≤2*k-b+1) at hdchild
    let Q : Int → Int → Int := fun x y =>
      (Int.natAbs x : Int) * ((Int.natAbs x : Int)-1)/2 - (x-y)^2/4
    have childValue (w : GaussianInt)
        (hw : w ∈ FootprintVertices (DiamondTile K.1)) :
        f w=Q w.re w.im := SecondPredecessorProof.childValue K hk f hchild w hw
    have childMem (x y : Int)
        (h : 0≤y ∧ y≤2*k ∧ -k≤x ∧ x≤k ∧ -y-1≤x ∧ x≤y+1 ∧
          -(2*k-y+1)≤x ∧ x≤2*k-y+1) :
        (⟨x,y⟩:GaussianInt)∈FootprintVertices (DiamondTile K.1) :=
      (P5352T2DomainRows K ⟨x,y⟩).1.mpr h
    have childOdometer (w : GaussianInt)
        (hw : w∈FootprintVertices (DiamondTile K.1)) :
        f w=DiamondOdometer K w := SecondPredecessorProof.childOdometer K hk f hchild w hw
    have predFoot (w : GaussianInt)
        (hw : 0≤w.im ∧ w.im≤2*(k-1) ∧ -(k-1)≤w.re ∧ w.re≤k-1 ∧
          -w.im-1≤w.re ∧ w.re≤w.im+1 ∧
          -(2*(k-1)-w.im+1)≤w.re ∧ w.re≤2*(k-1)-w.im+1) := SecondPredecessorProof.predFoot K hk a b
            hcast w hw
    have predValue (w : GaussianInt)
        (hw : w∈FootprintVertices (DiamondTile (K.1-1))) := SecondPredecessorProof.predValue K hk a
            b hcast w hw
    have predTranslatedValue (y : GaussianInt)
        (hy : y-d∈FootprintVertices (DiamondTile (K.1-1))) :=
            SecondPredecessorProof.predTranslatedValue K hk
            f B hpred a b hcast predValue y hy
    let T : Int → Int := fun n => n*(n-1)/2
    have tri (n : Int) := SecondPredecessorProof.tri K a b n
    have tdiff (n : Int) := SecondPredecessorProof.tdiff K a b tri n
    have tdiffRev (n : Int) := SecondPredecessorProof.tdiffRev K a b tdiff n
    have floorEven (m : Int) := EvenSquareQuotient.square m
    have floorOdd (m : Int) := SecondPredecessorProof.floorOdd K a b m
    have ht := SecondPredecessorProof.ht K a b hdpred hcast
        hdchild
    rcases ht with ⟨ht1,htk,hb⟩
    rcases hb with hb | hb
    · let t : Int := -a
      have hcoords : a=-t ∧ b=2*k+1-t := by dsimp [t]; omega
      have htrange : 1≤t ∧ t≤k := by dsimp [t]; omega
      let zA : GaussianInt := ⟨-t,2*k+1-t⟩
      -- The two translated-source neighbors and the three child values are evaluated below.
      have hcomp : zA-r ∈ FootprintVertices child.1 ↔ t=k := SecondPredecessorProof.hcompAt243 K
          hk hchildTile a b hdpred hcast hb hcoords htrange
      have hc0 : zA∈FootprintVertices (DiamondTile K.1) := by
        exact childMem (-t) (2*k+1-t) (by constructor <;> omega)
      have hce := SecondPredecessorProof.hce K hk a
          b hdpred hcast childMem hb
      have hcs := SecondPredecessorProof.hcs K
          hk a b hdpred hcast childMem hb
      have hp0 : zA-d∈FootprintVertices (DiamondTile (K.1-1)) := by
        simpa [zA,hcoords,pred,P5352T2Sources] using hpz
      have hpw := SecondPredecessorProof.hpw K
          hk a b hdpred hcast predFoot hb
      have hpn := SecondPredecessorProof.hpn K hk a b hdpred hcast predFoot hb
      have hC : f zA=Q (-t) (2*k+1-t) := by
        simpa [zA] using childValue zA hc0
      have hE : f (zA+1)=Q (1-t) (2*k+1-t) := SecondPredecessorProof.hEAt277 K f a childValue hce
      have hS : f (zA-⟨0,1⟩)=Q (-t) (2*k-t) := SecondPredecessorProof.hSAt284 K f a childValue hcs
      have hPC := SecondPredecessorProof.hPC K f B a
          predTranslatedValue hp0
      have hPW := SecondPredecessorProof.hPW K f
          B a predTranslatedValue hpw
      have hPN := SecondPredecessorProof.hPN K
          f B a predTranslatedValue hpn
      have qC := SecondPredecessorProof.qC K f B a b hdpred
          floorOdd hC hPC hPW hPN
      have qE := SecondPredecessorProof.qE K f B a b hdpred
          floorEven hC hPC hPW hPN
      have qS := SecondPredecessorProof.qS K f B a b hdpred floorEven hC
          hPC hPW hPN
      have qPC := SecondPredecessorProof.qPC K f B a b hdpred hcast hb hC
          hPC hPW hPN qC
      have qPN := (show
          Q (k-t) (k+1-t)=T (k-t)
        from by
          classical
          unfold Q
          have ha : (Int.natAbs (k-t):Int)=k-t := by
            rw [Int.natCast_natAbs,abs_of_nonneg (show 0≤k-t by omega)]
          rw [ha]
          norm_num [T])
      have qPWlt (hlt : t<k) := (show
          Q (k - t - (1 : ℤ)) (k - t) = T (k - t - (1 : ℤ))
        from by
          classical
          unfold Q
          have ha : (Int.natAbs (k-t-1):Int)=k-t-1 := by
            rw [Int.natCast_natAbs,abs_of_nonneg (show 0≤k-t-1 by omega)]
          rw [ha]
          norm_num [T])
      have qPWeq (heq : t=k) := SecondPredecessorProof.qPWeq K a heq
      have hEastDiff : f (zA+1)-f zA=k+1-t := SecondPredecessorProof.hEastDiff K f a tdiffRev hC
          hE qC qE
      have hWestDiff (hlt : t<k) : f (zA-1)-f zA=t-k := SecondPredecessorProof.hWestDiff K f B a
          tdiffRev hPC hPW qPC qPWlt hlt
      have hNorthDiff : f (zA+⟨0,1⟩)-f zA= -k := SecondPredecessorProof.hNorthDiff K f B a hPC
          hPN qPC qPN
      have hSouthDiff : f (zA-⟨0,1⟩)-f zA=k := SecondPredecessorProof.hSouthDiff K f a hC hS qC qS
      have hWestDiffEq : t=k → f (zA-1)-f zA= -1 := SecondPredecessorProof.hWestDiffEq K f B a
          hPC hPW qPC qPWeq
      have hzA : (⟨a,b⟩:GaussianInt)=zA := by ext <;> simp [zA,hcoords]
      rw [hzA] at ⊢
      refine ⟨?_,?_⟩
      · intro hmem
        have heq : t=k := hcomp.mp (by simpa [child,hchildTile] using hmem)
        rw [lap_identity,hEastDiff,hWestDiffEq heq,hNorthDiff,hSouthDiff,heq]
        ring
      · intro hmem
        have hneq := SecondPredecessorProof.hneq K hk hchildTile a hcomp hmem
        have hlt : t<k := by omega
        rw [lap_identity,hEastDiff,hWestDiff hlt,hNorthDiff,hSouthDiff]
        omega
    · let t : Int := -a
      have hcoords : a=-t ∧ b=2*k-t := by dsimp [t]; omega
      have htrange : 1≤t ∧ t<k := by dsimp [t]; omega
      let zB : GaussianInt := ⟨-t,2*k-t⟩
      have hzB : (⟨a,b⟩:GaussianInt)=zB := by ext <;> simp [zB,hcoords]
      have hc : zB∈FootprintVertices (DiamondTile K.1) :=
        childMem (-t) (2*k-t) (by constructor <;> omega)
      have he : (zB+1)∈FootprintVertices (DiamondTile K.1) := SecondPredecessorProof.heAt394 K hk
          a b hdpred hcast childMem hb
      have hw : (zB-1)∈FootprintVertices (DiamondTile K.1) := SecondPredecessorProof.hw K hk a b
          hdpred hcast childMem hb
      have hn : (zB+⟨0,1⟩)∈FootprintVertices (DiamondTile K.1) := SecondPredecessorProof.hnAt402
          K hk a b hdpred hcast childMem hb
      have hs : (zB-⟨0,1⟩)∈FootprintVertices (DiamondTile K.1) := SecondPredecessorProof.hsAt406
          K hk a b hdpred hcast childMem hb
      have hdom := SecondPredecessorProof.hdomAt410 K a hc
      have hnot := SecondPredecessorProof.hnot K a b hdpred
          hcast hb
      have htable := (DiamondLaplacianTable K).2.1 zB hdom hnot
      have hE : f (zB+1)=DiamondOdometer K (zB+1) := by
        exact childOdometer _ (by simpa [hchildTile] using he)
      have hW : f (zB-1)=DiamondOdometer K (zB-1) := by
        exact childOdometer _ (by simpa [hchildTile] using hw)
      have hN : f (zB+⟨0,1⟩)=DiamondOdometer K (zB+⟨0,1⟩) := by
        exact childOdometer _ (by simpa [hchildTile] using hn)
      have hS : f (zB-⟨0,1⟩)=DiamondOdometer K (zB-⟨0,1⟩) := by
        exact childOdometer _ (by simpa [hchildTile] using hs)
      have hC : f zB=DiamondOdometer K zB := by
        exact childOdometer _ (by simpa [hchildTile] using hc)
      have htable' := SecondPredecessorProof.htable'
              K a htable
      have hcomp : zB-r∉FootprintVertices child.1 := SecondPredecessorProof.hcompAt447 K hk f
          hchildTile a b hdpred hcast hb
      rw [hzB] at ⊢
      refine ⟨?_,?_⟩
      · intro hm
        exact (hcomp hm).elim
      · intro _
        rw [lap_identity,hE,hW,hN,hS,hC]
        exact htable'
  )

end ApollonianSuperharmonic

end
