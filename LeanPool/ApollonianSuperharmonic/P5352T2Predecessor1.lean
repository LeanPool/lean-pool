/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.DiamondQuadraticArithmetic
public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.EvenSquareQuotient
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacianProperties

public import LeanPool.ApollonianSuperharmonic.P5352T2PlacementData
public import LeanPool.ApollonianSuperharmonic.P5352T2DomainRows
public import LeanPool.ApollonianSuperharmonic.DiamondLaplacianTable
public import LeanPool.ApollonianSuperharmonic.P5352T2Sources

-- [TABLET NODE: P5352T2Predecessor1]

/-!
# P5352T2Predecessor1

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FirstPredecessorProof


private theorem predMem :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
          (1 : ℕ) < K.1 →
            let k : Int := K.1;
            (↑(K.1 - (1 : ℕ)) : ℤ) = k - (1 : ℤ) →
              ∀ (a : ℤ),
                ∀ (b : ℤ),
                  (0 : ℤ) ≤ b →
                    b ≤ (2 : ℤ) * (k - (1 : ℤ)) →
                      -(k - (1 : ℤ)) ≤ a →
                        a ≤ k - (1 : ℤ) →
                          -b - (1 : ℤ) ≤ a →
                            a ≤ b + (1 : ℤ) →
                              -((2 : ℤ) * (k - (1 : ℤ)) - b + (1 : ℤ)) ≤ a →
                                a ≤ (2 : ℤ) * (k - (1 : ℤ)) - b + (1 : ℤ) →
                                ⟨a, b⟩ ∈ FootprintVertices (DiamondTile (K.1 - (1 : ℕ)))
    ) := by
  classical
  intro K hk k hcast a b hb0 hb1 ha0 ha1 hs0 hs1 ht0 ht1
  apply (P5352T2DomainRows ⟨K.1-1,by omega⟩ ⟨a,b⟩).1.mpr
  simpa [hcast] using And.intro hb0 (And.intro hb1 (And.intro ha0
    (And.intro ha1 (And.intro hs0 (And.intro hs1 (And.intro ht0 ht1))))))

private theorem hcenter :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        let child := P5352T2Sources K hk 0
        (∀ y ∈ FootprintVertices child.1, f y = child.2.1 y) → (∀ (p : ℤ), (⟨p, (2 : ℤ) * k - p⟩
            ∈ FootprintVertices child.1) → (f ⟨p,2*k-p⟩ = DiamondOdometer K ⟨p,2*k-p⟩)) ) := by
  classical
  intro K hk f k child hchild p hz
  have := hchild _ (by simpa [child,P5352T2Sources] using hz)
  simpa [child,P5352T2Sources] using this

private theorem hEval :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (f : IntegerLatticeFunction),
        let child := P5352T2Sources K hk 0
        (child.1 = DiamondTile K.1) → ((∀ y ∈ FootprintVertices child.1, f y = child.2.1 y) → (∀
            w ∈ FootprintVertices (DiamondTile K.1), f w = DiamondOdometer K w)) ) := by
  classical
  intro K hk f child hchildTile hchild w hw
  have := hchild w (by simpa [child,P5352T2Sources] using (hchildTile ▸ hw))
  simpa [child,P5352T2Sources] using this

private theorem hdom :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1),
        let k : Int := K.1
        let child := P5352T2Sources K hk 0
        (child.1 = DiamondTile K.1) → (∀ (p : ℤ), (⟨p, (2 : ℤ) * k - p⟩ ∈ FootprintVertices
            child.1) → ((⟨p,2*k-p⟩ : GaussianInt) ∈ DiamondVertexDomains K false)) ) := by
  classical
  intro K hk k child hchildTile p hz
  obtain ⟨_,_,_,hf,_⟩ := DiamondTileOdometerRestriction K
  exact hf ▸ (hchildTile ▸ (by simpa [child,P5352T2Sources] using hz))

private theorem hnot :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
          let k : Int := K.1
          ∀ (p : ℤ),
            (↑(K.1 - (1 : ℕ)) : ℤ) = k - (1 : ℤ) →
              (1 : ℤ) ≤ p →
                k < (2 : ℤ) * k - p ∧
                    (2 : ℤ) * k - p ≤ (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧
                      k ≤ p + (k - (1 : ℤ)) ∧
                        p ≤ k - (1 : ℤ) + k ∧
                          k < p - k + (1 : ℤ) + ((2 : ℤ) * k - p) ∧
                            p ≤ (2 : ℤ) * k - p - (k + (1 : ℤ)) + (1 : ℤ) + k ∧
                              (2 : ℤ) * k - p ≤
                                (1 : ℤ) + (p - k) + (2 : ℤ) * (k - (1 : ℤ)) +
                                (k + (1 : ℤ)) ∧
                                p ≤
                                (2 : ℤ) * (k - (1 : ℤ)) -
                                ((2 : ℤ) * k - p - (k + (1 : ℤ))) +
                                (1 : ℤ) +
                                k →
                  (⟨p, 2 * k - p⟩ : GaussianInt) ∉ DiamondVertexDomains K true
    )
            := by
  classical
  intro K k p hcast hp1 hdpred
  change ¬ (Int.natAbs p + Int.natAbs (2*k-p-(K.1:Int)) ≤ K.1-1)
  intro hh
  have hpabs : (Int.natAbs p : Int)=p := by rw [Int.natCast_natAbs,abs_of_nonneg (by omega)]
  have hqabs : (Int.natAbs (2*k-p-(K.1:Int)) : Int)=k-p := by
    rw [Int.natCast_natAbs,abs_of_nonneg (by dsimp [k]; omega)]
    dsimp [k]
    ring
  have hKsub : ((K.1-1 : Nat) : Int)=k-1 := by
    rw [Nat.cast_sub (by omega : 1≤K.1)]
    rfl
  have hhI : ((Int.natAbs p + Int.natAbs (2*k-p-(K.1:Int)) : Nat) : Int) ≤
      ((K.1-1 : Nat) : Int) := by exact_mod_cast hh
  rw [Int.natCast_add,hpabs,hqabs,hKsub] at hhI
  have hh' : p+(k-p)≤k-1 := hhI
  dsimp [k] at hh'
  omega

private theorem hvE :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        ∀ (p : ℤ), ((⟨p+1,2*k-p⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1)) → ((∀ (w :
            GaussianInt), (w ∈ FootprintVertices (DiamondTile K.1)) → (f w = DiamondOdometer K
            w)) → (f (⟨p,2*k-p⟩+1)=DiamondOdometer K (⟨p,2*k-p⟩+1))) ) := by
  classical
  intro K f k p hE hEval
  have he : (⟨p,2*k-p⟩:GaussianInt)+1=⟨p+1,2*k-p⟩ := by ext <;> simp
  rw [he]; exact hEval _ hE

private theorem hvW :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        ∀ (p : ℤ), ((⟨p-1,2*k-p⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1)) → ((∀ (w :
            GaussianInt), (w ∈ FootprintVertices (DiamondTile K.1)) → (f w = DiamondOdometer K
            w)) → (f (⟨p,2*k-p⟩-1)=DiamondOdometer K (⟨p,2*k-p⟩-1))) ) := by
  classical
  intro K f k p hW hEval
  have he : (⟨p,2*k-p⟩:GaussianInt)-1=⟨p-1,2*k-p⟩ := by ext <;> simp
  rw [he]; exact hEval _ hW

private theorem hvN :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        ∀ (p : ℤ), ((⟨p,2*k+1-p⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1)) → ((∀ (w :
            GaussianInt), (w ∈ FootprintVertices (DiamondTile K.1)) → (f w = DiamondOdometer K
            w)) → (f (⟨p,2*k-p⟩+⟨0,1⟩)=DiamondOdometer K (⟨p,2*k-p⟩+⟨0,1⟩))) ) := by
  classical
  intro K f k p hN hEval
  have he : (⟨p,2*k-p⟩:GaussianInt)+⟨0,1⟩=⟨p,2*k+1-p⟩ := by ext <;> simp; omega
  rw [he]; exact hEval _ hN

private theorem hvS :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        ∀ (p : ℤ), ((⟨p,2*k-p-1⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1)) → ((∀ (w :
            GaussianInt), (w ∈ FootprintVertices (DiamondTile K.1)) → (f w = DiamondOdometer K
            w)) → (f (⟨p,2*k-p⟩-⟨0,1⟩)=DiamondOdometer K (⟨p,2*k-p⟩-⟨0,1⟩))) ) := by
  classical
  intro K f k p hS hEval
  have he : (⟨p,2*k-p⟩:GaussianInt)-⟨0,1⟩=⟨p,2*k-p-1⟩ := by ext <;> simp
  rw [he]; exact hEval _ hS

private theorem hcompAt229 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
          ∀ (hk : (1 : ℕ) < K.1),
            let k : Int := K.1
            let r : GaussianInt := ⟨2 * k, 0⟩
            let child := P5352T2Sources K hk 0
            child.1 = DiamondTile K.1 →
              ∀ (p : ℤ),
                (↑(K.1 - (1 : ℕ)) : ℤ) = k - (1 : ℤ) →
                  k < (2 : ℤ) * k - p ∧
                      (2 : ℤ) * k - p ≤ (2 : ℤ) * (k - (1 : ℤ)) + (k + (1 : ℤ)) ∧
                        k ≤ p + (k - (1 : ℤ)) ∧
                          p ≤ k - (1 : ℤ) + k ∧
                            k < p - k + (1 : ℤ) + ((2 : ℤ) * k - p) ∧
                              p ≤ (2 : ℤ) * k - p - (k + (1 : ℤ)) + (1 : ℤ) + k ∧
                                (2 : ℤ) * k - p ≤
                                (1 : ℤ) + (p - k) + (2 : ℤ) * (k - (1 : ℤ)) +
                                (k + (1 : ℤ)) ∧
                                p ≤
                                (2 : ℤ) * (k - (1 : ℤ)) -
                                ((2 : ℤ) * k - p - (k + (1 : ℤ))) +
                                (1 : ℤ) +
                                k →
                    (⟨p, 2 * k - p⟩ : GaussianInt) - r ∉ FootprintVertices child.1
    ) := by
  classical
  intro K hk k r child hchildTile p hcast hdpred hc
  have hb := (P5352T2DomainRows K (⟨p,2*k-p⟩-r)).1.mp (hchildTile ▸ hc)
  simp [r] at hb
  omega

private theorem hcenterC :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        let child := P5352T2Sources K hk 0
        (∀ y ∈ FootprintVertices child.1, f y = child.2.1 y) → (∀ (p : ℤ), (⟨p, (2 : ℤ) * k + (1
            : ℤ) - p⟩ ∈ FootprintVertices child.1) → (f ⟨p,2*k+1-p⟩ = DiamondOdometer K
            ⟨p,2*k+1-p⟩)) ) := by
  classical
  intro K hk f k child hchild p hz
  have := hchild _ (by simpa [child,P5352T2Sources] using hz)
  simpa [child,P5352T2Sources] using this

private theorem hWval :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        let child := P5352T2Sources K hk 0
        (child.1 = DiamondTile K.1) → ((∀ y ∈ FootprintVertices child.1, f y = child.2.1 y) → (∀
            (p : ℤ), ((⟨p-1,2*k+1-p⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1)) → (f
            (⟨p,2*k+1-p⟩-1)=DiamondOdometer K (⟨p,2*k+1-p⟩-1)))) ) := by
  classical
  intro K hk f k child hchildTile hchild p hW
  have he : (⟨p,2*k+1-p⟩:GaussianInt)-1=⟨p-1,2*k+1-p⟩ := by ext <;> simp
  rw [he]
  have hh := hchild _ (by simpa [child,P5352T2Sources] using (hchildTile ▸ hW))
  simpa [child,P5352T2Sources] using hh

private theorem hSval :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        let child := P5352T2Sources K hk 0
        (child.1 = DiamondTile K.1) → ((∀ y ∈ FootprintVertices child.1, f y = child.2.1 y) → (∀
            (p : ℤ), ((⟨p,2*k-p⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1)) → (f
            (⟨p,2*k+1-p⟩-⟨0,1⟩)=DiamondOdometer K (⟨p,2*k+1-p⟩-⟨0,1⟩)))) ) := by
  classical
  intro K hk f k child hchildTile hchild p hS
  have he : (⟨p,2*k+1-p⟩:GaussianInt)-⟨0,1⟩=⟨p,2*k-p⟩ := by ext <;> simp; omega
  rw [he]
  have hh := hchild _ (by simpa [child,P5352T2Sources] using (hchildTile ▸ hS))
  simpa [child,P5352T2Sources] using hh

private theorem hPval :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (f : IntegerLatticeFunction), ∀ (B :
            Int),
        let k : Int := K.1;
        let d : GaussianInt := ⟨k,k+1⟩;
        let pred := P5352T2Sources K hk 3;
        (∀ (y : GaussianInt), y - d ∈ FootprintVertices pred.1 → f y = pred.2.1 (y - d)
            + (⟨k, (0 : ℤ)⟩ : GaussianInt).re * y.re + (⟨k, (0 : ℤ)⟩ : GaussianInt).im * y.im +
                B) → (
        (∀ (hcast : (↑(K.1
            - (1 : ℕ)) : ℤ) = k - (1 : ℤ)), ∀ (y : GaussianInt), ∀ (w : GaussianInt), (y-d
            ∈ FootprintVertices pred.1) → ((y-d=w) → (f y = DiamondOdometer (⟨K.1-1,by
            omega⟩) w + k*y.re+B))))) := by
  classical
  intro K hk f B k d pred hpred hcast y w hy heq
  have hh := hpred y (by simpa [pred,P5352T2Sources] using hy)
  rw [heq] at hh
  simpa [pred,P5352T2Sources] using hh

private theorem hPcenter :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (f : IntegerLatticeFunction), ∀ (B :
            Int),
        let k : Int := K.1
        let d : GaussianInt := ⟨k,k+1⟩
        let pred := P5352T2Sources K hk 3
        ∀ (p : ℤ), ∀ (hcast : (↑(K.1 - (1 : ℕ)) : ℤ) = k - (1 : ℤ)), (⟨p, (2 : ℤ) * k +
            (1 : ℤ) - p⟩ - d ∈ FootprintVertices pred.1) → ((∀ (y : GaussianInt), ∀ (w :
                GaussianInt), (y-d ∈ FootprintVertices pred.1) → ((y-d=w) → (f y =
            DiamondOdometer (⟨K.1-1,by omega⟩) w + k*y.re+B))) → (f ⟨p,2*k+1-p⟩ =
          DiamondOdometer (⟨K.1-1,by omega⟩) ⟨p-k,k-p⟩ + k*p+B))) := by
  classical
  intro K hk f B k d pred p hcast hpz hPval
  have he : (⟨p,2*k+1-p⟩:GaussianInt)-d=⟨p-k,k-p⟩ := by ext <;> simp [d]; ring
  have hv := hPval _ _ (by simpa [pred,P5352T2Sources] using hpz) he
  simpa using hv

private theorem hPeval :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (f : IntegerLatticeFunction), ∀ (B :
            Int),
        let k : Int := K.1
        let d : GaussianInt := ⟨k,k+1⟩
        let pred := P5352T2Sources K hk 3
        ∀ (p : ℤ), ∀ (hcast : (↑(K.1 - (1 : ℕ)) : ℤ) = k - (1 : ℤ)), ((⟨p+1-k,k-p⟩ :
            GaussianInt) ∈ FootprintVertices (DiamondTile (K.1-1))) →
                (((⟨p,2*k+1-p⟩:GaussianInt)+1-d=⟨p+1-k,k-p⟩) → ((∀ (y : GaussianInt), ∀ (w :
                GaussianInt), (y-d ∈ FootprintVertices pred.1) → ((y-d=w) → (f y =
            DiamondOdometer (⟨K.1-1,by omega⟩) w + k*y.re+B))) → (f (⟨p,2*k+1-p⟩+1) =
          DiamondOdometer (⟨K.1-1,by omega⟩) ⟨p+1-k,k-p⟩ + k*(p+1)+B)))) := by
  classical
  intro K hk f B k d pred p hcast hPe hearg hPval
  have hv := hPval _ _ (by rw [hearg]; exact hPe) hearg
  simpa using hv

private theorem hPnval :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (f : IntegerLatticeFunction), ∀ (B :
            Int),
        let k : Int := K.1
        let d : GaussianInt := ⟨k,k+1⟩
        let pred := P5352T2Sources K hk 3
        ∀ (p : ℤ), ∀ (hcast : (↑(K.1 - (1 : ℕ)) : ℤ) = k - (1 : ℤ)), ((⟨p-k,k+1-p⟩ :
            GaussianInt) ∈ FootprintVertices (DiamondTile (K.1-1))) →
                (((⟨p,2*k+1-p⟩:GaussianInt)+⟨0,1⟩-d=⟨p-k,k+1-p⟩) → ((∀ (y : GaussianInt), ∀ (w :
                GaussianInt), (y-d ∈ FootprintVertices pred.1) → ((y-d=w) → (f y =
            DiamondOdometer (⟨K.1-1,by omega⟩) w + k*y.re+B))) → (f (⟨p,2*k+1-p⟩+⟨0,1⟩) =
          DiamondOdometer (⟨K.1-1,by omega⟩) ⟨p-k,k+1-p⟩ + k*p+B)))) := by
  classical
  intro K hk f B k d pred p hcast hPn hnarg hPval
  have hv := hPval _ _ (by rw [hnarg]; exact hPn) hnarg
  simpa using hv


private theorem sqOdd :
    (by
      classical
      exact
        ∀ (m : ℤ), ((2 : ℤ) * m + (1 : ℤ)) ^ (2 : ℕ) / (4 : ℤ) = m ^ (2 : ℕ) + m
    ) := by
  classical
  intro m
  have h := P4207T1FloorArithmetic.1 1 m
  have he : 1+2*m=2*m+1 := by ring
  rw [he] at h
  norm_num at h ⊢
  omega

private abbrev tri := ApollonianSuperharmonic.DiamondQuadraticArithmetic.triangularScale

private theorem tdiff :
    (∀ (a : Int), 2 * (a * (a - 1) / 2) = a * (a - 1)) →
      ∀ (a : Int), a * (a - 1) / 2 - (a - 1) * (a - 2) / 2 = a - 1 := by
  classical
  intro tri a
  have h1 := tri a
  have h2 := tri (a-1)
  have he : 2*(a*(a-1)/2-(a-1)*(a-2)/2)=2*(a-1) := by
    have h2' : 2*((a-1)*(a-2)/2)=(a-1)*(a-2) := by
      simpa [show a-1-1=a-2 by ring] using h2
    calc
      2*(a*(a-1)/2-(a-1)*(a-2)/2) = 2*(a*(a-1)/2)-2*((a-1)*(a-2)/2) := by ring
      _ = a*(a-1)-(a-1)*(a-2) := by rw [h1,h2']
      _ = 2*(a-1) := by ring
  omega

private theorem tdiffRev :
    (by
      classical
      exact
        (∀ (a : Int), a * (a - 1) / 2 - (a - 1) * (a - 2) / 2 = a - 1) →
          ∀ (a : ℤ),
            (a - (1 : ℤ)) * (a - (2 : ℤ)) / (2 : ℤ) - a * (a - (1 : ℤ)) / (2 : ℤ) =
              (1 : ℤ) - a
    ) := by
  classical
  intro tdiff a
  have hh := tdiff a
  omega

private theorem qpc :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let k : Int := K.1
        ∀ (p : ℤ),
        let Q (a b : Int) : Int := (Int.natAbs a : Int)*((Int.natAbs a : Int)-1)/2-(a-b)^2/4
        (∀ (m : Int), (2*m)^2/4=m^2) → (((Int.natAbs (p-k) : Int)=k-p) → (Q (p-k)
            (k-p)=(k-p)*(k-p-1)/2-(p-k)^2)) ) := by
  classical
  intro K k p Q sqEven absKm
  simp only [Q,absKm]
  rw [show (p-k)-(k-p)=2*(p-k) by ring,sqEven]

private theorem hPcenterQ :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
          ∀ (hk : (1 : ℕ) < K.1),
            let k : Int := K.1;
            let d : GaussianInt := ⟨k, k + 1⟩;
            let pred := P5352T2Sources K hk 3;
            ∀ (p : ℤ),
              ∀ (hcast : (↑(K.1 - (1 : ℕ)) : ℤ) = k - (1 : ℤ)),
                ⟨p, (2 : ℤ) * k + (1 : ℤ) - p⟩ - d ∈ FootprintVertices pred.1 →
                  let Q (a b : Int) : Int :=
                    (Int.natAbs a : Int) * ((Int.natAbs a : Int) - 1) / 2 -
                      (a - b) ^ 2 / 4;
                  (Int.natAbs (p - 1) : Int) = p - 1 →
                    ∀ (absKm : (Int.natAbs (p - k) : Int) = k - p),
                      DiamondOdometer ⟨K.1 - 1, by omega⟩ ⟨p - k, k - p⟩ =
                        Q (p - k) (k - p)
    ) := by
  classical
  intro K hk k d pred p hcast hpz Q absPm absKm
  have he : (⟨p,2*k+1-p⟩:GaussianInt)-d=⟨p-k,k-p⟩ := by ext <;> simp [d]; ring
  have hm : (⟨p-k,k-p⟩:GaussianInt) ∈ FootprintVertices (DiamondTile (K.1-1)) := by
    have hh := hpz
    rw [he] at hh
    simpa [pred,P5352T2Sources] using hh
  simpa [Q] using (P5352T2DomainRows ⟨K.1-1,by omega⟩ ⟨p-k,k-p⟩).2 hm

private theorem absKme (p k : Int) (hpk : p ≤ k) :
    (Int.natAbs (p + 1 - k) : Int) = if p = k then 1 else k - p - 1 := by
  by_cases equal : p = k
  · subst p
    norm_num
  · rw [Int.natCast_natAbs, abs_of_nonpos (by omega)]
    simp [equal]
    omega

private theorem hqvals :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let k : Int := K.1
        ∀ (p : ℤ),
        let Q (a b : Int) : Int := (Int.natAbs a : Int)*((Int.natAbs a : Int)-1)/2-(a-b)^2/4
        (∀ (m : Int), (2*m)^2/4=m^2) → ((∀ (m : Int), (2*m+1)^2/4=m^2+m) → (((Int.natAbs p :
            Int)=p) → (((Int.natAbs (p-1) : Int)=p-1) → (((Int.natAbs (p-k) : Int)=k-p) →
            (((Int.natAbs (p+1-k) : Int)=if p=k then 1 else k-p-1) → (Q p (2*k+1-p) =
            p*(p-1)/2-(p-k)*(p-k-1) ∧ Q (p-1) (2*k+1-p)=(p-1)*(p-2)/2-(p-k-1)^2 ∧ Q p
            (2*k-p)=p*(p-1)/2-(p-k)^2 ∧ Q (p+1-k) (k-p)=(if p=k then 0 else
            (k-p-1)*(k-p-2)/2-((p-k)^2+(p-k))) ∧ Q (p-k)
            (k+1-p)=(k-p)*(k-p-1)/2-((p-k-1)^2+(p-k-1)))))))) ) := by
  classical
  intro K k p Q sqEven sqOdd absP absPm absKm absKme
  constructor
  · simp only [Q,absP]
    rw [show p-(2*k+1-p)=2*(p-k)-1 by ring]
    have hsq : (2*(p-k)-1)^2/4=(p-k)*(p-k-1) := by
      have hh := sqOdd (p-k-1)
      have he : 2*(p-k)-1=2*(p-k-1)+1 := by ring
      rw [he,hh]
      ring
    rw [hsq]
  constructor
  · simp only [Q,absPm]
    rw [show (p-1)-(2*k+1-p)=2*(p-k-1) by ring, sqEven]
    congr 1; ring
  constructor
  · simp only [Q,absP]
    rw [show p-(2*k-p)=2*(p-k) by ring,sqEven]
  constructor
  · simp only [Q,absKme]
    by_cases hp : p=k
    · simp [hp]
    · simp only [hp, ↓reduceIte]
      rw [show (p+1-k)-(k-p)=2*(p-k)+1 by ring,sqOdd]
      congr 1; ring
  · simp only [Q,absKm]
    rw [show (p-k)-(k+1-p)=2*(p-k)-1 by ring]
    have hh := sqOdd (p-k-1)
    have he : 2*(p-k)-1=2*(p-k-1)+1 := by ring
    rw [he,hh]

private theorem hcval :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        ∀ (p : ℤ), (f ⟨p,2*k+1-p⟩ = DiamondOdometer K ⟨p,2*k+1-p⟩) → (
        let Q (a b : Int) : Int := (Int.natAbs a : Int)*((Int.natAbs a : Int)-1)/2-(a-b)^2/4
        (DiamondOdometer K ⟨p,2*k+1-p⟩=Q p (2*k+1-p)) → (f ⟨p,2*k+1-p⟩=Q p (2*k+1-p))) ) := by
  classical
  intro K f k p hcenterC Q qc
  calc
    f ⟨p,2*k+1-p⟩ = DiamondOdometer K ⟨p,2*k+1-p⟩ := hcenterC
    _ = Q p (2*k+1-p) := qc

private theorem hwval :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        ∀ (p : ℤ), (f (⟨p,2*k+1-p⟩-1)=DiamondOdometer K (⟨p,2*k+1-p⟩-1)) → (
        let Q (a b : Int) : Int := (Int.natAbs a : Int)*((Int.natAbs a : Int)-1)/2-(a-b)^2/4
        (DiamondOdometer K ⟨p-1,2*k+1-p⟩=Q (p-1) (2*k+1-p)) →
            (((⟨p,2*k+1-p⟩:GaussianInt)-1=⟨p-1,2*k+1-p⟩) → (f (⟨p,2*k+1-p⟩-1)=Q (p-1)
            (2*k+1-p)))) ) := by
  classical
  intro K f k p hWval Q qw hwcoord
  calc
    f (⟨p,2*k+1-p⟩-1) = DiamondOdometer K (⟨p,2*k+1-p⟩-1) := hWval
    _ = DiamondOdometer K ⟨p-1,2*k+1-p⟩ := by rw [hwcoord]
    _ = Q (p-1) (2*k+1-p) := qw

private theorem hsval :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        ∀ (p : ℤ), (f (⟨p,2*k+1-p⟩-⟨0,1⟩)=DiamondOdometer K (⟨p,2*k+1-p⟩-⟨0,1⟩)) → (
        let Q (a b : Int) : Int := (Int.natAbs a : Int)*((Int.natAbs a : Int)-1)/2-(a-b)^2/4
        (DiamondOdometer K ⟨p,2*k-p⟩=Q p (2*k-p)) → (((⟨p,2*k+1-p⟩:GaussianInt)-⟨0,1⟩=⟨p,2*k-p⟩)
            → (f (⟨p,2*k+1-p⟩-⟨0,1⟩)=Q p (2*k-p)))) ) := by
  classical
  intro K f k p hSval Q qs hscoord
  calc
    f (⟨p,2*k+1-p⟩-⟨0,1⟩) = DiamondOdometer K (⟨p,2*k+1-p⟩-⟨0,1⟩) := hSval
    _ = DiamondOdometer K ⟨p,2*k-p⟩ := by rw [hscoord]
    _ = Q p (2*k-p) := qs

private theorem hEAt404 (p k B : Int) (f : IntegerLatticeFunction)
    (Q : Int → Int → Int)
    (triangular : ∀ a : Int, (a - 1) * (a - 2) / 2 - a * (a - 1) / 2 = 1 - a)
    (east : f (⟨p, 2 * k + 1 - p⟩ + 1) = Q (p + 1 - k) (k - p) + k * (p + 1) + B)
    (center : f ⟨p, 2 * k + 1 - p⟩ = Q (p - k) (k - p) + k * p + B)
    (eastFormula : Q (p + 1 - k) (k - p) = if p = k then 0 else
      (k - p - 1) * (k - p - 2) / 2 - ((p - k) ^ 2 + (p - k)))
    (centerFormula : Q (p - k) (k - p) = (k - p) * (k - p - 1) / 2 - (p - k) ^ 2) :
    f (⟨p, 2 * k + 1 - p⟩ + 1) - f ⟨p, 2 * k + 1 - p⟩ =
      if p = k then k else k + 1 := by
  rw [east, center, eastFormula, centerFormula]
  by_cases equal : p = k
  · subst p
    simp
    ring
  · simp only [ite_eq_right equal]
    have difference := triangular (k - p)
    nlinarith only [difference]

private theorem hWdiff :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        ∀ (p : ℤ),
        let Q (a b : Int) : Int := (Int.natAbs a : Int)*((Int.natAbs a : Int)-1)/2-(a-b)^2/4
        (∀ (a : Int), (a-1)*(a-2)/2-a*(a-1)/2=1-a) → ((Q p ((2 : ℤ) * k + (1 : ℤ) - p) = p * (p -
            (1 : ℤ)) / (2 : ℤ) - (p - k) * (p - k - (1 : ℤ))) → ((Q (p - (1 : ℤ)) ((2 : ℤ) * k +
            (1 : ℤ) - p) = (p - (1 : ℤ)) * (p - (2 : ℤ)) / (2 : ℤ) - (p - k - (1 : ℤ)) ^ (2 : ℕ))
            → ((f ⟨p,2*k+1-p⟩=Q p (2*k+1-p)) → ((f (⟨p,2*k+1-p⟩-1)=Q (p-1) (2*k+1-p)) → (f
            (⟨p,2*k+1-p⟩-1)-f ⟨p,2*k+1-p⟩ = -k))))) ) := by
  classical
  intro K f k p Q tdiffRev hqc hqw hcval hwval
  rw [hwval,hcval,hqw,hqc]
  calc
    (p-1)*(p-2)/2-(p-k-1)^2-(p*(p-1)/2-(p-k)*(p-k-1)) =
        ((p-1)*(p-2)/2-p*(p-1)/2)+(-(p-k-1)^2+(p-k)*(p-k-1)) := by ring
    _ = (1-p)+(p-k-1) := by rw [tdiffRev p]; ring
    _ = -k := by ring

private theorem hNdiff (p k B : Int) (f : IntegerLatticeFunction)
    (Q : Int → Int → Int)
    (north : f (⟨p, 2 * k + 1 - p⟩ + ⟨0, 1⟩) = Q (p - k) (k + 1 - p) + k * p + B)
    (center : f ⟨p, 2 * k + 1 - p⟩ = Q (p - k) (k - p) + k * p + B)
    (northFormula : Q (p - k) (k + 1 - p) =
      (k - p) * (k - p - 1) / 2 - ((p - k - 1) ^ 2 + (p - k - 1)))
    (centerFormula : Q (p - k) (k - p) = (k - p) * (k - p - 1) / 2 - (p - k) ^ 2) :
    f (⟨p, 2 * k + 1 - p⟩ + ⟨0, 1⟩) - f ⟨p, 2 * k + 1 - p⟩ =
      if p = k then 0 else p - k := by
  rw [north, center, northFormula, centerFormula]
  by_cases equal : p = k
  · subst p
    simp
  · simp only [ite_eq_right equal]
    ring

private theorem hSdiff (p k : Int) (f : IntegerLatticeFunction)
    (Q : Int → Int → Int)
    (south : f (⟨p, 2 * k + 1 - p⟩ - ⟨0, 1⟩) = Q p (2 * k - p))
    (center : f ⟨p, 2 * k + 1 - p⟩ = Q p (2 * k + 1 - p))
    (southFormula : Q p (2 * k - p) = p * (p - 1) / 2 - (p - k) ^ 2)
    (centerFormula : Q p (2 * k + 1 - p) = p * (p - 1) / 2 - (p - k) * (p - k - 1)) :
    f (⟨p, 2 * k + 1 - p⟩ - ⟨0, 1⟩) - f ⟨p, 2 * k + 1 - p⟩ =
      if p = k then 0 else k - p := by
  rw [south, center, southFormula, centerFormula]
  by_cases equal : p = k
  · subst p
    simp
  · simp only [ite_eq_right equal]
    ring

private theorem hcompAt434 (K : DiamondParameter) (hk : 1 < K.1) (p : Int)
    (upper : p ≤ (K.1 : Int)) :
    (⟨p, 2 * (K.1 : Int) + 1 - p⟩ : GaussianInt) - ⟨2 * (K.1 : Int), 0⟩ ∈
      FootprintVertices (DiamondTile K.1) ↔ p = (K.1 : Int) := by
  have positive : 2 ≤ (K.1 : Int) := by exact_mod_cast (show 2 ≤ K.1 by omega)
  rw [(P5352T2DomainRows K _).1]
  simp only [Zsqrtd.im_sub, Zsqrtd.re_sub, sub_zero]
  constructor
  · intro bounds
    omega
  · intro equal
    subst p
    omega

private theorem hlap0 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), (∀ (g :
            IntegerLatticeFunction), ∀ (x : GaussianInt), FourNeighborLaplacian g x = (g (x+1)-g
            x)+(g (x-1)-g x)+ (g (x+⟨0,1⟩)-g x)+(g (x-⟨0,1⟩)-g x)) → (
        let k : Int := K.1
        ∀ (p : ℤ), (f (⟨p,2*k+1-p⟩+1)-f ⟨p,2*k+1-p⟩ = if p=k then k else k+1) → ((f
            (⟨p,2*k+1-p⟩-1)-f ⟨p,2*k+1-p⟩ = -k) → ((f (⟨p,2*k+1-p⟩+⟨0,1⟩)-f ⟨p,2*k+1-p⟩ = if p=k
            then 0 else p-k) → ((f (⟨p,2*k+1-p⟩-⟨0,1⟩)-f ⟨p,2*k+1-p⟩ = if p=k then 0 else k-p) →
            (p = k → FourNeighborLaplacian f ⟨p, (2 : ℤ) * k + (1 : ℤ) - p⟩ = (0 : ℤ)))))) ) := by
  classical
  intro K f lap_identity k p hE hWdiff hNdiff hSdiff hp
  rw [lap_identity,hE,hWdiff,hNdiff,hSdiff]
  simp [hp]

private theorem hlap1 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), (∀ (g :
            IntegerLatticeFunction), ∀ (x : GaussianInt), FourNeighborLaplacian g x = (g (x+1)-g
            x)+(g (x-1)-g x)+ (g (x+⟨0,1⟩)-g x)+(g (x-⟨0,1⟩)-g x)) → (
        let k : Int := K.1
        ∀ (p : ℤ), (f (⟨p,2*k+1-p⟩+1)-f ⟨p,2*k+1-p⟩ = if p=k then k else k+1) → ((f
            (⟨p,2*k+1-p⟩-1)-f ⟨p,2*k+1-p⟩ = -k) → ((f (⟨p,2*k+1-p⟩+⟨0,1⟩)-f ⟨p,2*k+1-p⟩ = if p=k
            then 0 else p-k) → ((f (⟨p,2*k+1-p⟩-⟨0,1⟩)-f ⟨p,2*k+1-p⟩ = if p=k then 0 else k-p) →
            (p ≠ k → FourNeighborLaplacian f ⟨p, (2 : ℤ) * k + (1 : ℤ) - p⟩ = (1 : ℤ)))))) ) := by
  classical
  intro K f lap_identity k p hE hWdiff hNdiff hSdiff hp
  rw [lap_identity,hE,hWdiff,hNdiff,hSdiff]
  simp [hp]; ring

end FirstPredecessorProof

theorem P5352T2Predecessor1 (K : DiamondParameter) (hk : 1 < K.1)
    (f : IntegerLatticeFunction) (B : Int) (z : GaussianInt) :
    let A := P5352T2Sources K hk 0
    let D := P5352T2Sources K hk 3
    let M := (P5352T2PlacementData K.1 2).2 1
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
    have lap_identity (g : IntegerLatticeFunction) (x : GaussianInt) :=
        FourNeighborLaplacianProperties.differences g x
    let k : Int := K.1
    let d : GaussianInt := ⟨k,k+1⟩
    let r : GaussianInt := ⟨2*k,0⟩
    let child := P5352T2Sources K hk 0
    let pred := P5352T2Sources K hk 3
    let M := (P5352T2PlacementData K.1 2).2 1
    have hkI : 2 ≤ k := by dsimp [k]; exact_mod_cast (show 2 ≤ K.1 by omega)
    have hm : M.1 = d ∧ M.2.1 = ⟨k,0⟩ ∧ M.2.2 = r := by
      simp [M, d, r, P5352T2PlacementData, k]
    rcases hm with ⟨hdisp,hcoeff,hr⟩
    have hchildTile : child.1 = DiamondTile K.1 := by simp [child,P5352T2Sources]
    change
      (∀ y, y ∈ FootprintVertices child.1 → f y = child.2.1 y) →
      (∀ y, y - M.1 ∈ FootprintVertices pred.1 →
        f y = pred.2.1 (y-M.1)+M.2.1.re*y.re+M.2.1.im*y.im+B) →
      z ∈ FootprintVertices child.1 → z-M.1 ∈ FootprintVertices pred.1 →
      (∀ y, y=z ∨ y=z+1 ∨ y=z-1 ∨ y=z+⟨0,1⟩ ∨ y=z-⟨0,1⟩ →
        y ∈ FootprintVertices child.1 ∨ y-M.1 ∈ FootprintVertices pred.1) →
      (z-M.2.2 ∈ FootprintVertices child.1 → FourNeighborLaplacian f z=0) ∧
      (z-M.2.2 ∉ FootprintVertices child.1 → FourNeighborLaplacian f z=1)
    intro hchild hpred hz hpz hcover
    rw [hdisp,hcoeff] at hpred
    rw [hdisp] at hpz hcover
    rw [hr] at ⊢
    have hdchild := (P5352T2DomainRows K z).1.mp hz
    have hdpred := (P5352T2DomainRows ⟨K.1-1,by omega⟩ (z-d)).1.mp hpz
    rcases z with ⟨p,q⟩
    simp only [Int.reduceNeg, Zsqrtd.im_sub, Int.sub_nonneg, Order.add_one_le_iff,
        tsub_le_iff_right, Zsqrtd.re_sub, neg_le_sub_iff_le_add, neg_sub, neg_add_rev,
        neg_add_le_iff_le_add, d] at hdpred
    have hcast : ((K.1-1 : Nat) : Int)=k-1 := by dsimp [k]; omega
    rw [hcast] at hdpred
    change (0≤q ∧ q≤2*k ∧ -k≤p ∧ p≤k ∧ -q-1≤p ∧ p≤q+1 ∧
      -(2*k-q+1)≤p ∧ p≤2*k-q+1) at hdchild
    have hloc : 1≤p ∧ p≤k ∧ (q=2*k-p ∨ q=2*k+1-p) := by omega
    rcases hloc with ⟨hp1,hpk,hq⟩
    have childMem (a b : Int)
        (hb0 : 0≤b) (hb1 : b≤2*k) (ha0 : -k≤a) (ha1 : a≤k)
        (hs0 : -b-1≤a) (hs1 : a≤b+1)
        (ht0 : -(2*k-b+1)≤a) (ht1 : a≤2*k-b+1) :
        (⟨a,b⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1) :=
      (P5352T2DomainRows K ⟨a,b⟩).1.mpr ⟨hb0,hb1,ha0,ha1,hs0,hs1,ht0,ht1⟩
    have predMem (a b : Int)
        (hb0 : 0≤b) (hb1 : b≤2*(k-1)) (ha0 : -(k-1)≤a) (ha1 : a≤k-1)
        (hs0 : -b-1≤a) (hs1 : a≤b+1)
        (ht0 : -(2*(k-1)-b+1)≤a) (ht1 : a≤2*(k-1)-b+1) := FirstPredecessorProof.predMem K hk
            hcast a b hb0 hb1 ha0 ha1 hs0 hs1 ht0 ht1
    rcases hq with hqB | hqA
    · subst q
      have hplt : p<k := by omega
      -- The unmarked staircase has its entire star in the child footprint.
      have hE : (⟨p+1,2*k-p⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1) := by
        apply childMem <;> clear * - hp1 hplt hkI <;> omega
      have hW : (⟨p-1,2*k-p⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1) := by
        apply childMem <;> clear * - hp1 hplt hkI <;> omega
      have hN : (⟨p,2*k+1-p⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1) := by
        apply childMem <;> clear * - hp1 hplt hkI <;> omega
      have hS : (⟨p,2*k-p-1⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1) := by
        apply childMem <;> clear * - hp1 hplt hkI <;> omega
      have hcenter : f ⟨p,2*k-p⟩ = DiamondOdometer K ⟨p,2*k-p⟩ := FirstPredecessorProof.hcenter K
          hk f hchild p hz
      have hEval (w : GaussianInt) (hw : w ∈ FootprintVertices (DiamondTile K.1)) :=
          FirstPredecessorProof.hEval K hk f hchildTile hchild w hw
      have hdom := FirstPredecessorProof.hdom K hk hchildTile p hz
      have hnot := FirstPredecessorProof.hnot K p hcast hp1 hdpred
      have htable := (DiamondLaplacianTable K).2.1 ⟨p,2*k-p⟩ hdom hnot
      have hvE : f (⟨p,2*k-p⟩+1)=DiamondOdometer K (⟨p,2*k-p⟩+1) := FirstPredecessorProof.hvE K f
          p hE hEval
      have hvW : f (⟨p,2*k-p⟩-1)=DiamondOdometer K (⟨p,2*k-p⟩-1) := FirstPredecessorProof.hvW K f
          p hW hEval
      have hvN : f (⟨p,2*k-p⟩+⟨0,1⟩)=DiamondOdometer K (⟨p,2*k-p⟩+⟨0,1⟩) :=
          FirstPredecessorProof.hvN K f p hN hEval
      have hvS : f (⟨p,2*k-p⟩-⟨0,1⟩)=DiamondOdometer K (⟨p,2*k-p⟩-⟨0,1⟩) :=
          FirstPredecessorProof.hvS K f p hS hEval
      have hcomp := FirstPredecessorProof.hcompAt229 K hk hchildTile p hcast hdpred
      refine ⟨fun hc => (hcomp hc).elim, ?_⟩
      intro _
      rw [FourNeighborLaplacian,hvE,hvW,hvN,hvS,hcenter]
      exact htable
    · subst q
      -- Marked staircase: east and north come from the predecessor, west and south from the child.
      have hW : (⟨p-1,2*k+1-p⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1) := by
        apply childMem <;> clear * - hp1 hpk hkI <;> omega
      have hS : (⟨p,2*k-p⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1) := by
        apply childMem <;> clear * - hp1 hpk hkI <;> omega
      have hPe : (⟨p+1-k,k-p⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile (K.1-1)) := by
        apply predMem <;> clear * - hp1 hpk hkI <;> omega
      have hPn : (⟨p-k,k+1-p⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile (K.1-1)) := by
        apply predMem <;> clear * - hp1 hpk hkI <;> omega
      have hearg : (⟨p,2*k+1-p⟩:GaussianInt)+1-d=⟨p+1-k,k-p⟩ := by ext <;> simp [d]; ring
      have hnarg : (⟨p,2*k+1-p⟩:GaussianInt)+⟨0,1⟩-d=⟨p-k,k+1-p⟩ := by ext <;> simp [d]; ring
      have hcenterC := FirstPredecessorProof.hcenterC K hk f hchild p hz
      have hWval := FirstPredecessorProof.hWval K hk f hchildTile hchild p hW
      have hSval := FirstPredecessorProof.hSval K hk f hchildTile hchild p hS
      have hPval (y : GaussianInt) (w : GaussianInt)
          (hy : y-d ∈ FootprintVertices pred.1) (heq : y-d=w) := FirstPredecessorProof.hPval K
              hk f B hpred hcast y w hy heq
      have hPcenter : f ⟨p,2*k+1-p⟩ =
          DiamondOdometer (⟨K.1-1,by omega⟩) ⟨p-k,k-p⟩ + k*p+B := FirstPredecessorProof.hPcenter
              K hk f B p hcast hpz hPval
      have hPeval : f (⟨p,2*k+1-p⟩+1) =
          DiamondOdometer (⟨K.1-1,by omega⟩) ⟨p+1-k,k-p⟩ + k*(p+1)+B :=
              FirstPredecessorProof.hPeval K hk f B p hcast hPe hearg hPval
      have hPnval : f (⟨p,2*k+1-p⟩+⟨0,1⟩) =
          DiamondOdometer (⟨K.1-1,by omega⟩) ⟨p-k,k+1-p⟩ + k*p+B := FirstPredecessorProof.hPnval
              K hk f B p hcast hPn hnarg hPval
      -- The closed-form restriction turns the four source values into floor-polynomial values.
      let Q (a b : Int) : Int := (Int.natAbs a : Int)*((Int.natAbs a : Int)-1)/2-(a-b)^2/4
      have qc : DiamondOdometer K ⟨p,2*k+1-p⟩=Q p (2*k+1-p) := by
        simpa [Q] using (P5352T2DomainRows K ⟨p,2*k+1-p⟩).2 (hchildTile ▸ (by simpa
            [child,P5352T2Sources] using hz))
      have qw : DiamondOdometer K ⟨p-1,2*k+1-p⟩=Q (p-1) (2*k+1-p) := by
        simpa [Q] using (P5352T2DomainRows K ⟨p-1,2*k+1-p⟩).2 (hchildTile ▸ hW)
      have qs : DiamondOdometer K ⟨p,2*k-p⟩=Q p (2*k-p) := by
        simpa [Q] using (P5352T2DomainRows K ⟨p,2*k-p⟩).2 (hchildTile ▸ hS)
      have qe : DiamondOdometer (⟨K.1-1,by omega⟩) ⟨p+1-k,k-p⟩=Q (p+1-k) (k-p) := by
        simpa [Q] using (P5352T2DomainRows ⟨K.1-1,by omega⟩ ⟨p+1-k,k-p⟩).2 hPe
      have qn : DiamondOdometer (⟨K.1-1,by omega⟩) ⟨p-k,k+1-p⟩=Q (p-k) (k+1-p) := by
        simpa [Q] using (P5352T2DomainRows ⟨K.1-1,by omega⟩ ⟨p-k,k+1-p⟩).2 hPn
      -- The exact four increments follow by reducing the even and odd squares.
      have sqEven (m : Int) := EvenSquareQuotient.square m
      have sqOdd (m : Int) := FirstPredecessorProof.sqOdd m
      have tri (a : Int) := FirstPredecessorProof.tri a
      have tdiff (a : Int) := FirstPredecessorProof.tdiff tri a
      have tdiffRev (a : Int) := FirstPredecessorProof.tdiffRev tdiff a
      have absP : (Int.natAbs p : Int)=p := by rw [Int.natCast_natAbs,abs_of_nonneg (by omega)]
      have absPm : (Int.natAbs (p-1) : Int)=p-1 := by rw [Int.natCast_natAbs,abs_of_nonneg (by
          omega)]
      have absKm : (Int.natAbs (p-k) : Int)=k-p := by
        rw [Int.natCast_natAbs,abs_of_nonpos (by omega)]; omega
      have qpc := FirstPredecessorProof.qpc K p sqEven absKm
      have hPcenterQ : DiamondOdometer (⟨K.1-1,by omega⟩) ⟨p-k,k-p⟩=Q (p-k) (k-p) :=
          FirstPredecessorProof.hPcenterQ K hk p hcast hpz absPm absKm
      have hPcval : f ⟨p,2*k+1-p⟩=Q (p-k) (k-p)+k*p+B := by
        rw [hPcenter,hPcenterQ]
      have absKme := FirstPredecessorProof.absKme p k hpk
      have hqvals := FirstPredecessorProof.hqvals K p
              sqEven sqOdd absP absPm absKm absKme
      rcases hqvals with ⟨hqc,hqw,hqs,hqe,hqn⟩
      have hcval := FirstPredecessorProof.hcval K f p hcenterC qc
      have hwcoord : (⟨p,2*k+1-p⟩:GaussianInt)-1=⟨p-1,2*k+1-p⟩ := by ext <;> simp
      have hscoord : (⟨p,2*k+1-p⟩:GaussianInt)-⟨0,1⟩=⟨p,2*k-p⟩ := by ext <;> simp; omega
      have hwval := FirstPredecessorProof.hwval K f p hWval
          qw hwcoord
      have hsval := FirstPredecessorProof.hsval K f p hSval
          qs hscoord
      have heval : f (⟨p,2*k+1-p⟩+1)=Q (p+1-k) (k-p)+k*(p+1)+B := by simpa [qe] using hPeval
      have hnval : f (⟨p,2*k+1-p⟩+⟨0,1⟩)=Q (p-k) (k+1-p)+k*p+B := by simpa [qn] using hPnval
      have hE := FirstPredecessorProof.hEAt404 p k B f Q tdiffRev heval hPcval hqe qpc
      have hWdiff := FirstPredecessorProof.hWdiff K f p
          tdiffRev hqc hqw hcval hwval
      have hNdiff := FirstPredecessorProof.hNdiff p k B f Q hnval hPcval hqn qpc
      have hSdiff := FirstPredecessorProof.hSdiff p k f Q hsval hcval hqs hqc
      have hcomp := (by
        simpa only [hchildTile] using FirstPredecessorProof.hcompAt434 K hk p hpk)
      have hlap0 (hp : p=k) := FirstPredecessorProof.hlap0 K f lap_identity p hE hWdiff hNdiff
          hSdiff hp
      have hlap1 (hp : p≠k) := FirstPredecessorProof.hlap1 K f lap_identity p hE hWdiff hNdiff
          hSdiff hp
      refine ⟨?_, ?_⟩
      · intro hh
        have hp : p=k := hcomp.mp (hchildTile ▸ hh)
        exact hlap0 hp
      · intro hh
        have hp : p≠k := by intro he; apply hh; exact hchildTile.symm ▸ hcomp.mpr he
        exact hlap1 hp
  )

end ApollonianSuperharmonic

end
