/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.EvenSquareQuotient
public import LeanPool.ApollonianSuperharmonic.DiamondQuadraticArithmetic

public import LeanPool.ApollonianSuperharmonic.P5352T2PlacementData
public import LeanPool.ApollonianSuperharmonic.P5352T2DomainRows
public import LeanPool.ApollonianSuperharmonic.P5352T2Sources

-- [TABLET NODE: P5491T1DiamondRightBoundary]

/-!
# P5491T1DiamondRightBoundary

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace DiamondRightBoundaryProof

private abbrev tri := ApollonianSuperharmonic.DiamondQuadraticArithmetic.triangularScale

private theorem hposResult :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1),
        let n : Int := K.1
        (∀ (i : Fin 3), ∀ (x : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) → x -
            (P5352T2PlacementData K.1 i).1.1 ∈ FootprintVertices (DiamondTile K.1) →
            (P5352T2Sources K hk 0).2.1 (x - (P5352T2PlacementData K.1 i).1.1) +
            (P5352T2PlacementData K.1 i).1.2.re*x.re + (P5352T2PlacementData K.1
            i).1.2.im*x.im - (P5352T2Sources K hk 0).2.1 x = if i.val = 0 then -(n*(n+1))/2
            else if i.val = 1 then n*(n-1)/2 else n*(n-1)) → (∀ (i : Fin 3), ∀ (x : GaussianInt),
            x ∈ FootprintVertices (DiamondTile K.1) → x - (P5352T2PlacementData K.1 i).1.1 ∈
            FootprintVertices (DiamondTile K.1) → (P5352T2Sources K hk 0).2.1 (x -
            (P5352T2PlacementData K.1 i).1.1) + (P5352T2PlacementData K.1 i).1.2.re*x.re +
            (P5352T2PlacementData K.1 i).1.2.im*x.im - (P5352T2Sources K hk 0).2.1 x = if
            i.val = 0 then -(n*(n+1))/2 else if i.val = 1 then n*(n-1)/2 else n*(n-1)) ) := by
  classical
  intro K hk n hpositive
  exact hpositive

end DiamondRightBoundaryProof

namespace DiamondBoundaryDetails

private theorem hF :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ z ∈ FootprintVertices
            (DiamondTile K.1), (P5352T2Sources K hk (0 : Fin (4 : ℕ))).2.1 z =
            (↑z.re.natAbs : ℤ) * ((↑z.re.natAbs : ℤ) - (1 : ℤ)) / (2 : ℤ) - (z.re - z.im) ^ (2 :
            ℕ) / (4 : ℤ) ) := by
  classical
  intro K hk z hz
  simp only [P5352T2Sources]
  exact (P5352T2DomainRows K z).2 hz

private abbrev hfloorEven := ApollonianSuperharmonic.EvenSquareQuotient.square

private theorem hfloorOdd :
    (by
      classical
      exact
        ∀ (m : ℤ), ((2 : ℤ) * m + (1 : ℤ)) ^ (2 : ℕ) / (4 : ℤ) = m * (m + (1 : ℤ)) ) := by
  classical
  intro m
  have hh := P4207T1FloorArithmetic.1 (1:Int) m
  have he : (1:Int) + 2*m = 2*m+1 := by ring
  rw [he] at hh
  norm_num at hh ⊢
  nlinarith

private theorem foot :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let n : Int := K.1
        ∀ (z : GaussianInt), z ∈ FootprintVertices (DiamondTile K.1) ↔ (0 : ℤ) ≤ z.im ∧ z.im
            ≤ (2 : ℤ) * n ∧ -n ≤ z.re ∧ z.re ≤ n ∧ -z.im - (1 : ℤ) ≤ z.re ∧ z.re ≤ z.im + (1 : ℤ)
            ∧ -((2 : ℤ) * n - z.im + (1 : ℤ)) ≤ z.re ∧ z.re ≤ (2 : ℤ) * n - z.im + (1 : ℤ) ) := by
  classical
  intro K n z
  simpa [n] using (P5352T2DomainRows K z).1

private theorem hs1At258 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let n : Int := K.1
        ∀ (x : GaussianInt),
        let v : Int := x.im
        let r : Int := v-n-1
        (r+1-(↑K.1+1+r-(↑K.1+1)))^2/4 = 0 ) := by
  classical
  intro K n x v r
  have he : r+1-(↑K.1+1+r-(↑K.1+1)) = 1 := by ring
  rw [he]
  norm_num

private theorem hs2At262 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let n : Int := K.1
        (∀ (m : Int), (2*m)^2/4 = m^2) → (∀ (x : GaussianInt),
        let v : Int := x.im
        let r : Int := v-n-1
        (-(K.1:Int)+1+r-(↑K.1+1+r))^2/4 = (K.1:Int)^2) ) := by
  classical
  intro K n hfloorEven x v r
  have he : -(K.1:Int)+1+r-(↑K.1+1+r) = 2*(-(K.1:Int)) := by ring
  rw [he]
  have hf := hfloorEven (-(K.1:Int))
  nlinarith

private theorem hpolyAt270 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let n : Int := K.1
        ∀ (x : GaussianInt),
        let v : Int := x.im
        let r : Int := v-n-1
        (r+1)*(r) - (-( -(K.1:Int)+1+r))*( -( -(K.1:Int)+1+r)-1) + 2*(-(K.1:Int)+1+r) -
            2*(K.1:Int)*((K.1:Int)+1+r) + 2*(K.1:Int)^2 + (K.1:Int)*((K.1:Int)+1) = 0 ) := by
  classical
  intro K n x v r
  ring

private theorem hdvdAt275 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((2 : ℤ) * (((↑K.1 : ℤ) + (1 : ℤ)) * ((↑K.1 : ℤ) + (1
            : ℤ) - (1 : ℤ)) / (2 : ℤ)) = ((↑K.1 : ℤ) + (1 : ℤ)) * ((↑K.1 : ℤ) + (1 : ℤ)
            - (1 : ℤ))) → ((2:Int) ∣ (K.1:Int)*((K.1:Int)+1)) ) := by
  classical
  intro K ht3
  refine ⟨((K.1:Int)+1)*(K.1:Int)/2, ?_⟩
  simpa [mul_comm] using ht3.symm

private theorem ht3'At278 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((2 : ℤ) * (((↑K.1 : ℤ) + (1 : ℤ)) * ((↑K.1 : ℤ) + (1
            : ℤ) - (1 : ℤ)) / (2 : ℤ)) = ((↑K.1 : ℤ) + (1 : ℤ)) * ((↑K.1 : ℤ) + (1 : ℤ)
            - (1 : ℤ))) → (2*((K.1:Int)*((K.1:Int)+1)/2) = (K.1:Int)*((K.1:Int)+1)) ) := by
  classical
  intro K ht3
  simpa [mul_comm] using ht3

private theorem hs1At299 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let n : Int := K.1
        ∀ (x : GaussianInt),
        let v : Int := x.im
        let r : Int := v-n-1
        (r-(↑K.1+1+r-(↑K.1+1)))^2/4 = 0 ) := by
  classical
  intro K n x v r
  have he : r-(↑K.1+1+r-(↑K.1+1)) = 0 := by ring
  rw [he]
  norm_num

private theorem hs2At303 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let n : Int := K.1
        (∀ (m : Int), (2*m+1)^2/4 = m*(m+1)) → (∀ (x : GaussianInt),
        let v : Int := x.im
        let r : Int := v-n-1
        (-(K.1:Int)+r-(↑K.1+1+r))^2/4 = (K.1:Int)*((K.1:Int)+1)) ) := by
  classical
  intro K n hfloorOdd x v r
  have he : -(K.1:Int)+r-(↑K.1+1+r) = 2*(-(K.1:Int)-1)+1 := by ring
  rw [he, hfloorOdd (-(K.1:Int)-1)]
  ring

private theorem hpolyAt310 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let n : Int := K.1
        ∀ (x : GaussianInt),
        let v : Int := x.im
        let r : Int := v-n-1
        r*(r-1) - ((K.1:Int)-r)*((K.1:Int)-r-1) + 3*(K.1:Int)*((K.1:Int)+1) + 2*(1-(K.1:Int))*r -
            2*(K.1:Int)^2 - 4*(K.1:Int) = 0 ) := by
  classical
  intro K n x v r
  ring

private theorem hs1At341 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), (∀ (m : Int), (2*m)^2/4 = m^2) → (∀ (x : GaussianInt),
        let v : Int := x.im
        let r : Int := v
        (-r-1-(-(K.1:Int)) - (r-(-(K.1:Int)-1)))^2/4 = (r+1)^2) ) := by
  classical
  intro K hfloorEven x v r
  have he : -r-1-(-(K.1:Int)) - (r-(-(K.1:Int)-1)) = -2*(r+1) := by ring
  rw [he]
  have hf := hfloorEven (-(r+1))
  have he' : (-2*(r+1))^2/4 = (2*-(r+1))^2/4 := by
    congr 2; ring
  rw [he', hf]
  ring

private theorem hs2At349 :
    (by
      classical
      exact
        (∀ (m : Int), (2*m+1)^2/4 = m*(m+1)) → (∀ (x : GaussianInt),
        let v : Int := x.im
        let r : Int := v
        (-r-1-r)^2/4 = r*(r+1)) ) := by
  classical
  intro hfloorOdd x v r
  have he : -r-1-r = 2*(-r-1)+1 := by ring
  rw [he, hfloorOdd (-r-1)]
  ring

private theorem hpolyAt356 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (x : GaussianInt),
        let v : Int := x.im
        let r : Int := v
        ((K.1:Int)-r-1)*((K.1:Int)-r-2) + (r+1)*r - 2*(r+1)^2 + 2*(K.1:Int)*(r+1) -
            (K.1:Int)*((K.1:Int)-1) = 0 ) := by
  classical
  intro K x v r
  ring

private theorem hs1At382 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), (∀ (m : Int), (2*m+1)^2/4 = m*(m+1)) → (∀ (x : GaussianInt),
        let v : Int := x.im
        let r : Int := v
        (-r-(-(K.1:Int)) - (r-(-(K.1:Int)-1)))^2/4 = r*(r+1)) ) := by
  classical
  intro K hfloorOdd x v r
  have he : -r-(-(K.1:Int)) - (r-(-(K.1:Int)-1)) = 2*(-r-1)+1 := by ring
  rw [he, hfloorOdd (-r-1)]
  ring

private theorem hs2At386 :
    (by
      classical
      exact
        (∀ (m : Int), (2*m)^2/4 = m^2) → (∀ (x : GaussianInt),
        let v : Int := x.im
        let r : Int := v
        (-r-r)^2/4 = r^2) ) := by
  classical
  intro hfloorEven x v r
  have he : -r-r = 2*(-r) := by ring
  rw [he]
  have hf := hfloorEven (-r)
  rw [hf]
  ring

private theorem hpolyAt395 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (x : GaussianInt),
        let v : Int := x.im
        let r : Int := v
        ((K.1:Int)-r)*((K.1:Int)-r-1) - r*(r-1) + 2*r^2 - 2*r*(r+1) + 2*(K.1:Int)*r -
            (K.1:Int)*((K.1:Int)-1) = 0 ) := by
  classical
  intro K x v r
  ring

private theorem habsTAt417 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let n : Int := K.1
        ∀ (x : GaussianInt), ((0 : ℤ) ≤ x.im ∧ x.im ≤ (2 : ℤ) * n ∧ -n ≤ x.re ∧ x.re ≤ n ∧ -x.im
            - (1 : ℤ) ≤ x.re ∧ x.re ≤ x.im + (1 : ℤ) ∧ -((2 : ℤ) * n - x.im + (1 : ℤ)) ≤ x.re ∧
            x.re ≤ (2 : ℤ) * n - x.im + (1 : ℤ)) → (((0 : ℤ) ≤ x.im ∧ x.im ≤ (2 : ℤ) * (↑K.1
            : ℤ) ∧ (2 : ℤ) * (↑K.1 : ℤ) ≤ x.re + (↑K.1 : ℤ) ∧ x.re ≤ (↑K.1 : ℤ) +
            (2 : ℤ) * (↑K.1 : ℤ) ∧ -x.im ≤ x.re - (2 : ℤ) * (↑K.1 : ℤ) + (1 : ℤ) ∧ x.re
            ≤ x.im + (1 : ℤ) + (2 : ℤ) * (↑K.1 : ℤ) ∧ x.im ≤ (1 : ℤ) + (x.re - (2 : ℤ) *
            (↑K.1 : ℤ)) + (2 : ℤ) * (↑K.1 : ℤ) ∧ x.re ≤ (2 : ℤ) * (↑K.1 : ℤ) -
            x.im + (1 : ℤ) + (2 : ℤ) * (↑K.1 : ℤ)) → (|(K.1:Int)-2*(K.1:Int)| = (K.1:Int))))
            ) := by
  classical
  intro K hk n x hxy hxyD
  rw [show (K.1:Int)-2*(K.1:Int) = -(K.1:Int) by ring]
  rw [abs_of_neg (show -(K.1:Int) < 0 by omega)]
  simp

private theorem hfAt425 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), (∀ (m : Int), (2*m+1)^2/4 = m*(m+1)) →
            (((K.1:Int)-2*(K.1:Int)-((K.1:Int)-1))^2/4 = (K.1:Int)*((K.1:Int)-1)) ) := by
  classical
  intro K hfloorOdd
  have he : (K.1:Int)-2*(K.1:Int)-((K.1:Int)-1) = 2*(-(K.1:Int))+1 := by ring
  rw [he, hfloorOdd (-(K.1:Int))]
  ring

private theorem hfAt446 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), (∀ (m : Int), (2*m)^2/4 = m^2) →
            (((K.1:Int)-2*(K.1:Int)-(K.1:Int))^2/4 = (K.1:Int)^2) ) := by
  classical
  intro K hfloorEven
  have he : (K.1:Int)-2*(K.1:Int)-(K.1:Int) = 2*(-(K.1:Int)) := by ring
  rw [he, hfloorEven]
  ring

private theorem hfAt467 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), (∀ (m : Int), (2*m+1)^2/4 = m*(m+1)) →
            (((K.1:Int)-2*(K.1:Int)-((K.1:Int)+1))^2/4 = (K.1:Int)*((K.1:Int)+1)) ) := by
  classical
  intro K hfloorOdd
  have he : (K.1:Int)-2*(K.1:Int)-((K.1:Int)+1) = 2*(-(K.1:Int)-1)+1 := by ring
  rw [he, hfloorOdd (-(K.1:Int)-1)]
  ring

private theorem hp' :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (i : Fin 3),
        let n : Int := K.1
        let c : Int := if i.val = 0 then -(n*(n+1))/2 else
          if i.val = 1 then n*(n-1)/2 else n*(n-1)
        let M := (P5352T2PlacementData K.1 i).1
        ∀ (x : GaussianInt), ((P5352T2Sources K hk (0 : Fin (4 : ℕ))).2.1 (x + M.1 -
            (P5352T2PlacementData K.1 i).1.1) + (P5352T2PlacementData K.1 i).1.2.re
            * (x + M.1).re + (P5352T2PlacementData K.1 i).1.2.im * (x + M.1).im -
            (P5352T2Sources K hk (0 : Fin (4 : ℕ))).2.1 (x + M.1) = if (↑i : ℕ) = (0 : ℕ) then
            -(n * (n + (1 : ℤ))) / (2 : ℤ) else if (↑i : ℕ) = (1 : ℕ) then n * (n - (1 : ℤ)) / (2
            : ℤ) else n * (n - (1 : ℤ))) → ((P5352T2Sources K hk 0).2.1 x +
            M.2.re*(x.re+M.1.re) + M.2.im*(x.im+M.1.im) - (P5352T2Sources K hk 0).2.1 (x+M.1) =
            c) ) := by
  classical
  intro K hk i n c M x hp
  simpa [M, c] using hp

private theorem hx1At508 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (i : Fin 3), ∀ (x :
            GaussianInt), ((x - if true = true then (P5352T2PlacementData K.1 i).1.1 else
            -(P5352T2PlacementData K.1 i).1.1) ∈ FootprintVertices (P5352T2Sources K hk
            (0 : Fin (4 : ℕ))).1) → (x-(P5352T2PlacementData K.1 i).1.1 ∈ FootprintVertices
            (DiamondTile K.1)) ) := by
  classical
  intro K hk i x hxD
  simpa [P5352T2Sources] using hxD

end DiamondBoundaryDetails

namespace DiamondPositiveBoundary

private theorem hpositive :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1),
        let n : Int := K.1
        (∀ z ∈ FootprintVertices (DiamondTile K.1), (P5352T2Sources K hk (0 : Fin (4 :
            ℕ))).2.1 z = (↑z.re.natAbs : ℤ) * ((↑z.re.natAbs : ℤ) - (1 : ℤ)) / (2 : ℤ) - (z.re -
            z.im) ^ (2 : ℕ) / (4 : ℤ)) → ((∀ (m : ℤ), ((2 : ℤ) * m) ^ (2 : ℕ) / (4 : ℤ) = m ^ (2
            : ℕ)) → ((∀ (m : ℤ), ((2 : ℤ) * m + (1 : ℤ)) ^ (2 : ℕ) / (4 : ℤ) = m * (m + (1 : ℤ)))
            → ((∀ (a : Int), 2*(a*(a-1)/2) = a*(a-1)) → ((∀ (z : GaussianInt), z ∈
            FootprintVertices (DiamondTile K.1) ↔ (0 : ℤ) ≤ z.im ∧ z.im ≤ (2 : ℤ) * (↑K.1 : ℤ) ∧
                -(↑K.1 : ℤ) ≤ z.re ∧ z.re ≤ (↑K.1 : ℤ) ∧ -z.im - (1 : ℤ) ≤ z.re ∧
            z.re ≤ z.im + (1 : ℤ) ∧ -((2 : ℤ) * (↑K.1 : ℤ) - z.im + (1 : ℤ)) ≤ z.re ∧ z.re ≤
            (2 : ℤ) * (↑K.1 : ℤ) - z.im + (1 : ℤ)) → (∀ (i : Fin 3), ∀ (x : GaussianInt), x
            ∈ FootprintVertices (DiamondTile K.1) → x - (P5352T2PlacementData K.1 i).1.1 ∈
            FootprintVertices (DiamondTile K.1) → (P5352T2Sources K hk 0).2.1 (x -
            (P5352T2PlacementData K.1 i).1.1) + (P5352T2PlacementData K.1 i).1.2.re*x.re +
            (P5352T2PlacementData K.1 i).1.2.im*x.im - (P5352T2Sources K hk 0).2.1 x = if
            i.val = 0 then -(n*(n+1))/2 else if i.val = 1 then n*(n-1)/2 else n*(n-1)))))) ) := by
  classical
  intro K hk n hF hfloorEven hfloorOdd tri foot i x hx hxD
  have habsB : |(K.1 : Int)| = (K.1 : Int) :=
    abs_of_nonneg (show 0 ≤ (K.1 : Int) by omega)
  have triangularCurvature := tri (K.1 : Int)
  let u : Int := x.re
  let v : Int := x.im
  have hxy := (foot x).mp hx
  have hxyD := (foot (x-(P5352T2PlacementData K.1 i).1.1)).mp hxD
  fin_cases i
  · simp only [Int.reduceNeg, P5352T2PlacementData, Nat.succ_eq_add_one, Nat.reduceAdd,
      neg_mul, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Zsqrtd.im_sub, Int.sub_nonneg,
      Order.add_one_le_iff, tsub_le_iff_right, Zsqrtd.re_sub, sub_neg_eq_add,
      add_le_iff_nonpos_left, neg_sub, neg_add_rev, neg_add_le_iff_le_add] at hxyD
    have hd : v-u = 2*n ∨ v-u = 2*n+1 := by
      omega
    rcases hd with hd | hd
    · let r : Int := v-n-1
      have hr0 : 0 ≤ r := by dsimp [r]; omega
      have hrn : r < n := by dsimp [r]; omega
      have hxe : x = ⟨-n+1+r,n+1+r⟩ := by
        ext <;> simp [r,v]; omega
      rw [hxe]
      simp only [Fin.isValue, Int.reduceNeg, P5352T2PlacementData, Nat.succ_eq_add_one,
          Nat.reduceAdd, neg_mul, Fin.zero_eta, Matrix.cons_val_zero, one_mul, ↓reduceIte]
      rw [hF _ (by simpa [P5352T2PlacementData, n, hxe] using hxD),
        hF _ (by simpa [hxe] using hx)]
      simp only [n]
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
      simp only [Int.natCast_natAbs]
      have hrabs : 0 ≤ r+1 := by omega
      have huabs : -n+1+r ≤ 0 := by omega
      have harg : -(K.1 : Int)+1+r- -(K.1 : Int) = r+1 := by ring
      rw [harg]
      have huabs' : -(K.1:Int)+1+r ≤ 0 := by simpa [n] using huabs
      rw [abs_of_nonneg hrabs]
      rw [abs_of_nonpos huabs']
      have hs1 := DiamondBoundaryDetails.hs1At258 K x
      have hs2 := DiamondBoundaryDetails.hs2At262 K hfloorEven x
      rw [hs1, hs2]
      have ht1 := tri (r+1)
      have ht2 := tri (-( -(K.1:Int)+1+r))
      have hpoly := DiamondBoundaryDetails.hpolyAt270 K x
      have ht3 := tri ((K.1:Int)+1)
      have hdvd := DiamondBoundaryDetails.hdvdAt275 K ht3
      have ht3' := DiamondBoundaryDetails.ht3'At278 K ht3
      rw [Int.neg_ediv_of_dvd hdvd]
      apply (mul_left_cancel₀ (by norm_num : (2:Int) ≠ 0))
      nlinarith [ht1, ht2, hpoly, ht3']
    · let r : Int := v-n-1
      have hr0 : 0 ≤ r := by dsimp [r]; omega
      have hrn : r < n := by dsimp [r]; omega
      have hxe : x = ⟨-n+r,n+1+r⟩ := by
        ext <;> simp [r,v]; omega
      rw [hxe]
      simp only [Fin.isValue, Int.reduceNeg, P5352T2PlacementData, Nat.succ_eq_add_one,
          Nat.reduceAdd, neg_mul, Fin.zero_eta, Matrix.cons_val_zero, one_mul, ↓reduceIte]
      rw [hF _ (by simpa [P5352T2PlacementData, n, hxe] using hxD),
        hF _ (by simpa [hxe] using hx)]
      simp only [n, Zsqrtd.re_sub, Zsqrtd.im_sub, Int.natCast_natAbs]
      have huabs : -n+r ≤ 0 := by omega
      have huabs' : -(K.1:Int)+r ≤ 0 := by simpa [n] using huabs
      have harg : -(K.1:Int)+r- -(K.1:Int) = r := by ring
      rw [harg]
      rw [abs_of_nonneg hr0, abs_of_nonpos huabs']
      have hs1 := DiamondBoundaryDetails.hs1At299 K x
      have hs2 := DiamondBoundaryDetails.hs2At303 K hfloorOdd x
      rw [hs1, hs2]
      have ht1 := tri r
      have ht2 := tri ((K.1:Int)-r)
      have hpoly := DiamondBoundaryDetails.hpolyAt310 K x
      have ht3 := tri ((K.1:Int)+1)
      have hdvd := DiamondBoundaryDetails.hdvdAt275 K ht3
      have ht3' : 2*((K.1:Int)*((K.1:Int)+1)/2) =
          (K.1:Int)*((K.1:Int)+1) := by simpa [mul_comm] using ht3
      rw [Int.neg_ediv_of_dvd hdvd]
      apply (mul_left_cancel₀ (by norm_num : (2:Int) ≠ 0))
      have habsRe : -(-(K.1:Int)+r) = (K.1:Int)-r := by ring
      rw [habsRe]
      linear_combination ht1 - ht2 + hpoly + ht3'
  · simp only [Int.reduceNeg, P5352T2PlacementData, Nat.succ_eq_add_one, Nat.reduceAdd,
      neg_mul, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
      Zsqrtd.im_sub, Int.sub_nonneg, tsub_le_iff_right, Zsqrtd.re_sub, sub_neg_eq_add,
      add_le_iff_nonpos_left, neg_sub, neg_add_rev, neg_add_le_iff_le_add] at hxyD
    have hd : u+v = -1 ∨ u+v = 0 := by omega
    rcases hd with hd | hd
    · let r : Int := v
      have hr0 : 0 ≤ r := by dsimp [r]; omega
      have hrn : r < n := by dsimp [r]; omega
      have hxe : x = ⟨-r-1,r⟩ := by ext <;> simp [r,v]; omega
      rw [hxe]
      simp only [Fin.isValue, Int.reduceNeg, P5352T2PlacementData, Nat.succ_eq_add_one,
          Nat.reduceAdd, neg_mul, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
          zero_mul, add_zero, one_ne_zero, ↓reduceIte]
      rw [hF _ (by simpa [P5352T2PlacementData, n, hxe] using hxD),
        hF _ (by simpa [hxe] using hx)]
      simp only [n, Zsqrtd.re_sub, Zsqrtd.im_sub, Int.natCast_natAbs]
      have harg : (K.1:Int)-r-1 ≥ 0 := by omega
      have huabs : -r-1 ≤ 0 := by omega
      have harg' : 0 ≤ -r-1 - (-(K.1:Int)) := by nlinarith [harg]
      rw [abs_of_nonneg harg', abs_of_nonpos huabs]
      have hs1 := DiamondBoundaryDetails.hs1At341 K hfloorEven x
      have hs2 := DiamondBoundaryDetails.hs2At349 hfloorOdd x
      rw [hs1, hs2]
      have ht1 := tri ((K.1:Int)-r-1)
      have ht2 := tri (r+1)
      have hpoly := DiamondBoundaryDetails.hpolyAt356 K x
      apply (mul_left_cancel₀ (by norm_num : (2:Int) ≠ 0))
      have hre : -r-1 - (-(K.1:Int)) = (K.1:Int)-r-1 := by ring
      have hbr : -(-r-1) = r+1 := by ring
      rw [hre, hbr]
      have htr : r+1-1 = r := by omega
      rw [htr] at ht2 ⊢
      linear_combination ht1 - ht2 + hpoly - triangularCurvature
    · let r : Int := v
      have hr0 : 0 ≤ r := by dsimp [r]; omega
      have hrn : r < n := by dsimp [r]; omega
      have hxe : x = ⟨-r,r⟩ := by ext <;> simp [r,v]; omega
      rw [hxe]
      simp only [Fin.isValue, Int.reduceNeg, P5352T2PlacementData, Nat.succ_eq_add_one,
          Nat.reduceAdd, neg_mul, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
          mul_neg, neg_neg, zero_mul, add_zero, one_ne_zero, ↓reduceIte]
      rw [hF _ (by simpa [P5352T2PlacementData, n, hxe] using hxD),
        hF _ (by simpa [hxe] using hx)]
      simp only [n, Zsqrtd.re_sub, Zsqrtd.im_sub, Int.natCast_natAbs]
      have harg : (K.1:Int)-r ≥ 0 := by omega
      have huabs : -r ≤ 0 := by omega
      have harg' : 0 ≤ -r - (-(K.1:Int)) := by nlinarith [harg]
      rw [abs_of_nonneg harg', abs_of_nonpos huabs]
      have hs1 := DiamondBoundaryDetails.hs1At382 K hfloorOdd x
      have hs2 := DiamondBoundaryDetails.hs2At386 hfloorEven x
      rw [hs1, hs2]
      have ht1 := tri ((K.1:Int)-r)
      have ht2 := tri r
      have hpoly := DiamondBoundaryDetails.hpolyAt395 K x
      apply (mul_left_cancel₀ (by norm_num : (2:Int) ≠ 0))
      have hre : -r - (-(K.1:Int)) = (K.1:Int)-r := by ring
      have hbaseT : -(-r)*(-(-r)-1) = r*(r-1) := by ring
      rw [hre, hbaseT]
      linear_combination ht1 - ht2 + hpoly - triangularCurvature
  · simp only [Int.reduceNeg, P5352T2PlacementData, Nat.succ_eq_add_one, Nat.reduceAdd,
      neg_mul, Fin.reduceFinMk, Matrix.cons_val, Zsqrtd.im_sub, sub_zero, Zsqrtd.re_sub,
      neg_le_sub_iff_le_add, tsub_le_iff_right, neg_add_rev, neg_sub, neg_add_le_iff_le_add]
      at hxyD
    have hu : u = n := by omega
    have hv : v = n-1 ∨ v = n ∨ v = n+1 := by omega
    rcases hv with hv | hv | hv
    · have hxe : x = ⟨n,n-1⟩ := by ext <;> simp [u,v,hu,hv]
      rw [hxe]
      simp only [Fin.isValue, Int.reduceNeg, P5352T2PlacementData, Nat.succ_eq_add_one,
          Nat.reduceAdd, neg_mul, Fin.reduceFinMk, Matrix.cons_val, OfNat.ofNat_ne_zero,
          ↓reduceIte, OfNat.ofNat_ne_one]
      rw [hF _ (by simpa [P5352T2PlacementData, n, hxe] using hxD),
        hF _ (by simpa [hxe] using hx)]
      simp only [n, Zsqrtd.re_sub, Zsqrtd.im_sub, Int.natCast_natAbs]
      have habsT := DiamondBoundaryDetails.habsTAt417 K
          hk x hxy hxyD
      rw [habsT, habsB]
      simp only [sub_zero]
      have hf := DiamondBoundaryDetails.hfAt425 K hfloorOdd
      have hxSq : ((K.1:Int)-((K.1:Int)-1))^2/4 = 0 := by norm_num
      rw [hf, hxSq]
      ring
    · have hxe : x = ⟨n,n⟩ := by ext <;> simp [u,v,hu,hv]
      rw [hxe]
      simp only [Fin.isValue, Int.reduceNeg, P5352T2PlacementData, Nat.succ_eq_add_one,
          Nat.reduceAdd, neg_mul, Fin.reduceFinMk, Matrix.cons_val, OfNat.ofNat_ne_zero,
          ↓reduceIte, OfNat.ofNat_ne_one]
      rw [hF _ (by simpa [P5352T2PlacementData, n, hxe] using hxD),
        hF _ (by simpa [hxe] using hx)]
      simp only [n, Zsqrtd.re_sub, Zsqrtd.im_sub, Int.natCast_natAbs]
      have habsT := DiamondBoundaryDetails.habsTAt417 K
          hk x hxy hxyD
      rw [habsT, habsB]
      simp only [sub_zero]
      have hf := DiamondBoundaryDetails.hfAt446 K hfloorEven
      have hxSq : ((K.1:Int)-(K.1:Int))^2/4 = 0 := by norm_num
      rw [hf, hxSq]
      ring
    · have hxe : x = ⟨n,n+1⟩ := by ext <;> simp [u,v,hu,hv]
      rw [hxe]
      simp only [Fin.isValue, Int.reduceNeg, P5352T2PlacementData, Nat.succ_eq_add_one,
          Nat.reduceAdd, neg_mul, Fin.reduceFinMk, Matrix.cons_val, OfNat.ofNat_ne_zero,
          ↓reduceIte, OfNat.ofNat_ne_one]
      rw [hF _ (by simpa [P5352T2PlacementData, n, hxe] using hxD),
        hF _ (by simpa [hxe] using hx)]
      simp only [n, Zsqrtd.re_sub, Zsqrtd.im_sub, Int.natCast_natAbs]
      have habsT := DiamondBoundaryDetails.habsTAt417 K
          hk x hxy hxyD
      rw [habsT, habsB]
      simp only [sub_zero]
      have hf := DiamondBoundaryDetails.hfAt467 K hfloorOdd
      have hxSq : ((K.1:Int)-((K.1:Int)+1))^2/4 = 0 := by norm_num
      rw [hf, hxSq]
      ring

end DiamondPositiveBoundary

theorem P5491T1DiamondRightBoundary (K : DiamondParameter) (hk : 1 < K.1)
    (i : Fin 3) (e : Bool) :
    let A := P5352T2Sources K hk 0
    let M := (P5352T2PlacementData K.1 i).1
    let d := if e then M.1 else -M.1
    let a := if e then M.2 else -M.2
    ∃ b : ℤ, ∀ x : GaussianInt,
      x ∈ FootprintVertices A.1 → x-d ∈ FootprintVertices A.1 →
      A.2.1 (x-d) + a.re*x.re + a.im*x.im - A.2.1 x = b := by
-- BODY
  dsimp only
  let n : Int := K.1
  have hn : 2 ≤ n := by dsimp [n]; exact_mod_cast hk
  have hA : (P5352T2Sources K hk 0).1 = DiamondTile K.1 := by
    simp [P5352T2Sources]
  have hF (z : GaussianInt) (hz : z ∈ FootprintVertices (DiamondTile K.1)) :=
      DiamondBoundaryDetails.hF K hk z hz
  have hfloorEven (m : Int) := DiamondBoundaryDetails.hfloorEven m
  have hfloorOdd (m : Int) := DiamondBoundaryDetails.hfloorOdd m
  let Q (a b : Int) : Int :=
    (Int.natAbs a : Int)*((Int.natAbs a : Int)-1)/2-(a-b)^2/4
  let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
  have tri (a : Int) : 2*(a*(a-1)/2) = a*(a-1) := DiamondRightBoundaryProof.tri a
  have square (a : Int) : 4*(a^2/4) = a^2-a%2 := DiamondQuadraticArithmetic.squareScale a
  have scale (a b : Int) := DiamondQuadraticArithmetic.quadraticScale tri square a b
  have foot (z : GaussianInt) := DiamondBoundaryDetails.foot K z
  have hpositive : ∀ (i : Fin 3) (x : GaussianInt),
      x ∈ FootprintVertices (DiamondTile K.1) →
      x - (P5352T2PlacementData K.1 i).1.1 ∈ FootprintVertices (DiamondTile K.1) →
      (P5352T2Sources K hk 0).2.1
          (x - (P5352T2PlacementData K.1 i).1.1) +
        (P5352T2PlacementData K.1 i).1.2.re*x.re +
        (P5352T2PlacementData K.1 i).1.2.im*x.im -
        (P5352T2Sources K hk 0).2.1 x =
          if i.val = 0 then -(n*(n+1))/2 else
          if i.val = 1 then n*(n-1)/2 else n*(n-1) := DiamondPositiveBoundary.hpositive K hk hF
              hfloorEven hfloorOdd tri foot
  have hposResult : ∀ (i : Fin 3) (x : GaussianInt),
      x ∈ FootprintVertices (DiamondTile K.1) →
      x - (P5352T2PlacementData K.1 i).1.1 ∈ FootprintVertices (DiamondTile K.1) →
      (P5352T2Sources K hk 0).2.1
          (x - (P5352T2PlacementData K.1 i).1.1) +
        (P5352T2PlacementData K.1 i).1.2.re*x.re +
        (P5352T2PlacementData K.1 i).1.2.im*x.im -
        (P5352T2Sources K hk 0).2.1 x =
          if i.val = 0 then -(n*(n+1))/2 else
          if i.val = 1 then n*(n-1)/2 else n*(n-1) := DiamondRightBoundaryProof.hposResult K hk
              hpositive
  let c : Int := if i.val = 0 then -(n*(n+1))/2 else
    if i.val = 1 then n*(n-1)/2 else n*(n-1)
  cases e
  · let M := (P5352T2PlacementData K.1 i).1
    refine ⟨M.2.re*M.1.re + M.2.im*M.1.im - c, ?_⟩
    intro x hx hxD
    have hx0 : x ∈ FootprintVertices (DiamondTile K.1) := by
      simpa [P5352T2Sources] using hx
    have hx1 : x+M.1 ∈ FootprintVertices (DiamondTile K.1) := by
      simpa [P5352T2Sources, M, P5352T2PlacementData] using hxD
    have hp := hposResult i (x+M.1) hx1 (by simpa [M] using hx0)
    have hp' := DiamondBoundaryDetails.hp' K hk i x hp
    simp only [Bool.false_eq_true, ↓reduceIte, sub_neg_eq_add]
    simp only [M,
      Zsqrtd.re_neg, Zsqrtd.im_neg] at hp' ⊢
    linear_combination -hp'
  · refine ⟨c, ?_⟩
    intro x hx hxD
    have hx0 : x ∈ FootprintVertices (DiamondTile K.1) := by
      simpa [P5352T2Sources] using hx
    have hx1 := DiamondBoundaryDetails.hx1At508 K hk i x hxD
    have hp := hposResult i x hx0 hx1
    simpa [P5352T2Sources, P5352T2PlacementData, c] using hp

end ApollonianSuperharmonic

end
