/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5352T2PlacementData
public import LeanPool.ApollonianSuperharmonic.P5352T2DomainRows
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian
public import LeanPool.ApollonianSuperharmonic.P5352T2Sources

-- [TABLET NODE: P5352T2RightHorizontal]

/-!
# P5352T2RightHorizontal

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace DiamondRightHorizontal

private theorem hcoords :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let n : Int := K.1
        ∀ w ∈ FootprintVertices (DiamondTile K.1), (0 : ℤ) ≤ w.im ∧ w.im ≤ (2 : ℤ) * n ∧ -n ≤
            w.re ∧ w.re ≤ n ∧ -w.im - (1 : ℤ) ≤ w.re ∧ w.re ≤ w.im + (1 : ℤ) ∧ -((2 : ℤ) * n -
            w.im + (1 : ℤ)) ≤ w.re ∧ w.re ≤ (2 : ℤ) * n - w.im + (1 : ℤ) ) := by
  classical
  intro K n w hw
  simpa [n] using (P5352T2DomainRows K w).1.mp hw

private theorem hz' :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (z : GaussianInt), (z -
            (P5352T2PlacementData K.1 (2 : Fin (3 : ℕ))).1.1 ∈ FootprintVertices
            (P5352T2Sources K hk (0 : Fin (4 : ℕ))).1) → (
        let n : Int := K.1
        let M : GaussianInt := ⟨2*n, 0⟩
        ((P5352T2PlacementData K.1 2).1.1 = M) → (((P5352T2Sources K hk 0).1 = DiamondTile
            K.1) → (z - M ∈ FootprintVertices (DiamondTile K.1)))) ) := by
  classical
  intro K hk z hzM n M hM hA
  simpa [hM] using (show z - (P5352T2PlacementData K.1 2).1.1 ∈
    FootprintVertices (DiamondTile K.1) by simpa [hA] using hzM)

private theorem hzr :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (z : GaussianInt),
        let n : Int := K.1
        let M : GaussianInt := ⟨2*n, 0⟩
        ((0 : ℤ) ≤ z.im ∧ z.im ≤ (2 : ℤ) * n ∧ -n ≤ z.re ∧ z.re ≤ n ∧ -z.im - (1 : ℤ) ≤ z.re ∧
            z.re ≤ z.im + (1 : ℤ) ∧ -((2 : ℤ) * n - z.im + (1 : ℤ)) ≤ z.re ∧ z.re ≤ (2 : ℤ) * n -
            z.im + (1 : ℤ)) → (((0 : ℤ) ≤ (z - M).im ∧ (z - M).im ≤ (2 : ℤ) * n ∧ -n ≤ (z - M).re
            ∧ (z - M).re ≤ n ∧ -(z - M).im - (1 : ℤ) ≤ (z - M).re ∧ (z - M).re ≤ (z - M).im + (1
            : ℤ) ∧ -((2 : ℤ) * n - (z - M).im + (1 : ℤ)) ≤ (z - M).re ∧ (z - M).re ≤ (2 : ℤ) * n
            - (z - M).im + (1 : ℤ)) → (z.re = n)) ) := by
  classical
  intro K z n M hzB hzMB
  have hlow := hzMB.2.2.1
  dsimp [M] at hlow
  omega

private theorem hzi :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (z : GaussianInt), (∀ (y :
            GaussianInt), y = z ∨ y = z + (1 : GaussianInt) ∨ y = z - (1 : GaussianInt) ∨ y = z +
            ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ y = z - ⟨(0 : ℤ), (1 : ℤ)⟩ → y ∈ FootprintVertices
            (P5352T2Sources K hk (0 : Fin (4 : ℕ))).1 ∨ y - (P5352T2PlacementData K.1 (2 :
            Fin (3 : ℕ))).1.1 ∈ FootprintVertices (P5352T2Sources K hk (0 : Fin (4 : ℕ))).1) → (
        let n : Int := K.1
        let M : GaussianInt := ⟨2*n, 0⟩
        ((P5352T2PlacementData K.1 2).1.1 = M) → (((P5352T2Sources K hk 0).1 = DiamondTile
            K.1) → ((∀ (w : GaussianInt), (w ∈ FootprintVertices (DiamondTile K.1)) → (0 ≤ w.im ∧
            w.im ≤ 2*n ∧ -n ≤ w.re ∧ w.re ≤ n ∧ -w.im-1 ≤ w.re ∧ w.re ≤ w.im+1 ∧ -(2*n-w.im+1) ≤
            w.re ∧ w.re ≤ 2*n-w.im+1)) → (((0 : ℤ) ≤ z.im ∧ z.im ≤ (2 : ℤ) * n ∧ -n ≤ z.re ∧ z.re
            ≤ n ∧ -z.im - (1 : ℤ) ≤ z.re ∧ z.re ≤ z.im + (1 : ℤ) ∧ -((2 : ℤ) * n - z.im + (1 :
            ℤ)) ≤ z.re ∧ z.re ≤ (2 : ℤ) * n - z.im + (1 : ℤ)) → (((0 : ℤ) ≤ (z - M).im ∧ (z -
            M).im ≤ (2 : ℤ) * n ∧ -n ≤ (z - M).re ∧ (z - M).re ≤ n ∧ -(z - M).im - (1 : ℤ) ≤ (z -
            M).re ∧ (z - M).re ≤ (z - M).im + (1 : ℤ) ∧ -((2 : ℤ) * n - (z - M).im + (1 : ℤ)) ≤
            (z - M).re ∧ (z - M).re ≤ (2 : ℤ) * n - (z - M).im + (1 : ℤ)) → ((z.re = n) → (z.im =
            n))))))) ) := by
  classical
  intro K hk z hstar n M hM hA hcoords hzB hzMB hzr
  rcases hzB with ⟨_, _, _, _, _, hzlo, _, _⟩
  rcases hzMB with ⟨_, _, _, _, _, _, hbound, _⟩
  have him : (z-M).im = z.im := by simp [M]
  have hre : (z-M).re = z.re-2*n := by simp [M]
  have hnotlow : z.im ≠ n-1 := by
    intro heq
    have hsouth := hstar (z-⟨0,1⟩) (Or.inr (Or.inr (Or.inr (Or.inr rfl))) :
      z-⟨0,1⟩ = z ∨ z-⟨0,1⟩ = z+1 ∨ z-⟨0,1⟩ = z-1 ∨
        z-⟨0,1⟩ = z+⟨0,1⟩ ∨ z-⟨0,1⟩ = z-⟨0,1⟩)
    rcases hsouth with hp | hc
    · have hr := hcoords (z-⟨0,1⟩) (by simpa [hA] using hp)
      have hh := hr.2.2.2.2.2.1
      have hsr : (z-⟨0,1⟩).re = n := by simp [Zsqrtd.re_sub, hzr]
      have hsi : (z-⟨0,1⟩).im = n-2 := by simp [Zsqrtd.im_sub, heq]; ring
      rw [hsr,hsi] at hh
      omega
    · have hr := hcoords ((z-⟨0,1⟩)-M) (by
        simpa [hA, hM] using hc)
      have hh := hr.2.2.2.2.1
      have hcr : ((z-⟨0,1⟩)-M).re = -n := by simp [Zsqrtd.re_sub, M, hzr]; ring
      have hci : ((z-⟨0,1⟩)-M).im = n-2 := by simp [Zsqrtd.im_sub, M, heq]; ring
      rw [hcr,hci] at hh
      omega
  have hnotup : z.im ≠ n+1 := by
    intro heq
    have hnorth := hstar (z+⟨0,1⟩) (Or.inr (Or.inr (Or.inr (Or.inl rfl))) :
      z+⟨0,1⟩ = z ∨ z+⟨0,1⟩ = z+1 ∨ z+⟨0,1⟩ = z-1 ∨
        z+⟨0,1⟩ = z+⟨0,1⟩ ∨ z+⟨0,1⟩ = z-⟨0,1⟩)
    rcases hnorth with hp | hc
    · have hr := hcoords (z+⟨0,1⟩) (by simpa [hA] using hp)
      rcases hr with ⟨_,_,_,_,_,_,_,hh⟩
      have hnr : (z+⟨0,1⟩).re = n := by simp [Zsqrtd.re_add, hzr]
      have hni : (z+⟨0,1⟩).im = n+2 := by simp [Zsqrtd.im_add, heq]; ring
      rw [hnr,hni] at hh
      omega
    · have hr := hcoords ((z+⟨0,1⟩)-M) (by
        simpa [hA, hM] using hc)
      rcases hr with ⟨_,_,_,_,_,_,hh,_⟩
      have hnr : ((z+⟨0,1⟩)-M).re = -n := by simp [Zsqrtd.re_sub, Zsqrtd.re_add, M, hzr]; ring
      have hni : ((z+⟨0,1⟩)-M).im = n+2 := by simp [Zsqrtd.im_sub, Zsqrtd.im_add, M, heq]; ring
      rw [hnr,hni] at hh
      omega
  omega

private theorem foot :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let n : Int := K.1
        ∀ (a : ℤ), ∀ (b : ℤ), (0 : ℤ) ≤ b ∧ b ≤ (2 : ℤ) * n ∧ -n ≤ a ∧ a ≤ n ∧ -b - (1 : ℤ) ≤ a ∧
            a ≤ b + (1 : ℤ) ∧ -((2 : ℤ) * n - b + (1 : ℤ)) ≤ a ∧ a ≤ (2 : ℤ) * n - b + (1 : ℤ) →
            ⟨a, b⟩ ∈ FootprintVertices (DiamondTile K.1) ) := by
  classical
  intro K n a b hb
  apply (P5352T2DomainRows K ⟨a,b⟩).1.mpr
  simpa using hb

private theorem cellD :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let n : Int := K.1
        ∀ (a : ℤ), ∀ (b : ℤ), (0 : ℤ) ≤ b ∧ b < (2 : ℤ) * n ∧ -(b + (1 : ℤ)) ≤ a ∧ a < b + (1 :
            ℤ) ∧ -((2 : ℤ) * n - b) ≤ a ∧ a < (2 : ℤ) * n - b → ⟨a, b⟩ ∈ DiamondCellDomain K.1 )
            := by
  classical
  intro K n a b hb
  apply (P4194T1DiamondCellRows K.1 ⟨a,b⟩).1.mpr
  simpa using hb

private theorem coverCells :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (z : GaussianInt),
        let n : Int := K.1
        let M : GaussianInt := ⟨2*n, 0⟩
        ((P5352T2PlacementData K.1 2).1.1 = M) → (((P5352T2Sources K hk 0).1 = DiamondTile
            K.1) → ((z.re = n) → ((z = ⟨n,n⟩) → ((∀ (a : Int), ∀ (b : Int), (0 ≤ b ∧ b < 2*n ∧
            -(b+1) ≤ a ∧ a < b+1 ∧ -(2*n-b) ≤ a ∧ a < 2*n-b) → ((⟨a,b⟩ : GaussianInt) ∈
            DiamondCellDomain K.1)) → (∀ y : GaussianInt, y = z ∨ y = z-1 ∨ y = z-⟨0,1⟩ ∨ y =
            z-1-⟨0,1⟩ → y ∈ (P5352T2Sources K hk 0).1.cells ∨ y-(P5352T2PlacementData K.1
            2).1.1 ∈ (P5352T2Sources K hk 0).1.cells))))) ) := by
  classical
  intro K hk z n M hM hA hzr hzc cellD y hy
  rcases hy with h | h | h | h <;> subst y
  · right
    have hc := cellD (-n) n (by constructor <;> omega)
    rw [hzc, hM, hA, DiamondTile]
    change (⟨n,n⟩ : GaussianInt)-M ∈ DiamondCellDomain K.1
    rw [show (⟨n,n⟩ : GaussianInt)-M = ⟨-n,n⟩ by ext <;> simp [M]; ring]
    exact hc
  · left
    have hc := cellD (n-1) n (by constructor <;> omega)
    rw [hzc, hA, DiamondTile]
    change (⟨n,n⟩ : GaussianInt)-1 ∈ DiamondCellDomain K.1
    rw [show (⟨n,n⟩ : GaussianInt)-1 = ⟨n-1,n⟩ by ext <;> simp ]
    exact hc
  · right
    have hc := cellD (-n) (n-1) (by constructor <;> omega)
    rw [hzc, hM, hA, DiamondTile]
    change (⟨n,n⟩ : GaussianInt)-⟨0,1⟩-M ∈ DiamondCellDomain K.1
    rw [show (⟨n,n⟩ : GaussianInt)-⟨0,1⟩-M = ⟨-n,n-1⟩ by ext <;> simp [M]; ring]
    exact hc
  · left
    have hc := cellD (n-1) (n-1) (by constructor <;> omega)
    rw [hzc, hA, DiamondTile]
    change (⟨n,n⟩ : GaussianInt)-1-⟨0,1⟩ ∈ DiamondCellDomain K.1
    rw [show (⟨n,n⟩ : GaussianInt)-1-⟨0,1⟩ = ⟨n-1,n-1⟩ by ext <;> simp ]
    exact hc

private theorem hchildEast :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (∀ (z : GaussianInt),
        let n : Int := K.1
        let M : GaussianInt := ⟨2*n, 0⟩
        (z.re = n) → ((∀ (a : Int), ∀ (b : Int), (0 ≤ b ∧ b ≤ 2*n ∧ -n ≤ a ∧ a ≤ n ∧ -b-1 ≤ a ∧ a
            ≤ b+1 ∧ -(2*n-b+1) ≤ a ∧ a ≤ 2*n-b+1) → ((⟨a,b⟩ : GaussianInt) ∈ FootprintVertices
            (DiamondTile K.1))) → ((z+1 = ⟨n+1,n⟩) → ((z+1)-M ∈ FootprintVertices (DiamondTile
            K.1))))) ) := by
  classical
  intro K hk z n M hzr foot hEc
  rw [hEc]
  have hpt : (⟨n+1,n⟩ : GaussianInt)-M = ⟨1-n,n⟩ := by ext <;> simp [M]; ring
  rw [hpt]
  exact foot (1-n) n (by constructor <;> omega)

private theorem hparent :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
          ∀ (hk : (1 : ℕ) < K.1),
            ∀ (f : IntegerLatticeFunction),
              (∀ y ∈ FootprintVertices (P5352T2Sources K hk (0 : Fin (4 : ℕ))).1,
                  f y = (P5352T2Sources K hk (0 : Fin (4 : ℕ))).2.1 y) →
                let Q (x : GaussianInt) : Int :=
                  (Int.natAbs x.re : Int) * ((Int.natAbs x.re : Int) - 1) / 2 -
                    (x.re - x.im) ^ 2 / 4;
                ∀ w ∈ FootprintVertices (DiamondTile K.1), f w = Q w
    ) := by
  classical
  intro K hk f hC Q w hw
  have hv := hC w hw
  have hval := (P5352T2DomainRows K w).2 hw
  simpa [P5352T2Sources, Q] using hv.trans hval

private theorem hfChildCenter :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (f : IntegerLatticeFunction), ∀ (B :
            Int), ∀ (z : GaussianInt), (∀ (y : GaussianInt), y - (P5352T2PlacementData K.1 (2 :
            Fin (3 : ℕ))).1.1 ∈ FootprintVertices (P5352T2Sources K hk (0 : Fin (4 : ℕ))).1 → f
            y = (P5352T2Sources K hk (0 : Fin (4 : ℕ))).2.1 (y - (P5352T2PlacementData K.1 (2
            : Fin (3 : ℕ))).1.1) + (P5352T2PlacementData K.1 (2 : Fin (3 : ℕ))).1.2.re * y.re +
            (P5352T2PlacementData K.1 (2 : Fin (3 : ℕ))).1.2.im * y.im + B) → ((z -
            (P5352T2PlacementData K.1 (2 : Fin (3 : ℕ))).1.1 ∈ FootprintVertices
            (P5352T2Sources K hk (0 : Fin (4 : ℕ))).1) → (
        let n : Int := K.1
        let M : GaussianInt := ⟨2*n, 0⟩
        let Q (x : GaussianInt) : Int :=
          (Int.natAbs x.re : Int) * ((Int.natAbs x.re : Int)-1)/2 -
            (x.re-x.im)^2/4
        ((P5352T2PlacementData K.1 2).1.1 = M) → (((P5352T2PlacementData K.1 2).1.2 =
            ⟨n-1,n⟩) → (((P5352T2Sources K hk 0).1 = DiamondTile K.1) → (f z = Q (z-M) +
            (n-1)*z.re + n*z.im + B))))) ) := by
  classical
  intro K hk f B z hR hzM n M Q hM hbeta hA
  have hv := hR z (by simpa [hA, hM] using hzM)
  have hval := (P5352T2DomainRows K (z-M)).2 (by simpa [hA, hM] using hzM)
  simpa [P5352T2Sources, hM, hbeta, Q] using hv.trans (congrArg (fun v => v +
    (P5352T2PlacementData K.1 2).1.2.re*z.re +
    (P5352T2PlacementData K.1 2).1.2.im*z.im+B) hval)

private theorem hfEast :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (f : IntegerLatticeFunction), ∀ (B :
            Int), ∀ (z : GaussianInt), (∀ (y : GaussianInt), y - (P5352T2PlacementData K.1 (2 :
            Fin (3 : ℕ))).1.1 ∈ FootprintVertices (P5352T2Sources K hk (0 : Fin (4 : ℕ))).1 → f
            y = (P5352T2Sources K hk (0 : Fin (4 : ℕ))).2.1 (y - (P5352T2PlacementData K.1 (2
            : Fin (3 : ℕ))).1.1) + (P5352T2PlacementData K.1 (2 : Fin (3 : ℕ))).1.2.re * y.re +
            (P5352T2PlacementData K.1 (2 : Fin (3 : ℕ))).1.2.im * y.im + B) → (
        let n : Int := K.1
        let M : GaussianInt := ⟨2*n, 0⟩
        let Q (x : GaussianInt) : Int :=
          (Int.natAbs x.re : Int) * ((Int.natAbs x.re : Int)-1)/2 -
            (x.re-x.im)^2/4
        ((P5352T2PlacementData K.1 2).1.1 = M) → (((P5352T2PlacementData K.1 2).1.2 =
            ⟨n-1,n⟩) → (((P5352T2Sources K hk 0).1 = DiamondTile K.1) → (((z+1)-M ∈
            FootprintVertices (DiamondTile K.1)) → (f (z+1) = Q ((z+1)-M) + (n-1)*(z+1).re +
            n*(z+1).im + B))))) ) := by
  classical
  intro K hk f B z hR n M Q hM hbeta hA hchildEast
  have he := hR (z+1) (by simpa [hM, hA] using hchildEast)
  have hval := (P5352T2DomainRows K ((z+1)-M)).2 (by simpa [hM, hA] using hchildEast)
  simpa [P5352T2Sources, hM, hbeta, Q] using he.trans (congrArg (fun v => v +
    (P5352T2PlacementData K.1 2).1.2.re*(z+1).re +
    (P5352T2PlacementData K.1 2).1.2.im*(z+1).im+B) hval)

private theorem hsq1 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
          let n : Int := K.1;
          (1 - 2 * n) ^ 2 / 4 = n ^ 2 - n
    ) := by
  classical
  intro K n
  have h := P4207T1FloorArithmetic.1 1 (-n)
  norm_num at h ⊢
  rw [show 1 + -(2*n) = 1-2*n by ring] at h
  omega

private theorem hsq0' :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let n : Int := K.1
        ((-2*n)^2/4 = n^2) → ((-n-n)^2/4 = n^2) ) := by
  classical
  intro K n hsq0
  rw [show -n-n = -2*n by ring]
  exact hsq0

private theorem hsq1' :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let n : Int := K.1
        ((1-2*n)^2/4 = n^2-n) → ((1-n-n)^2/4 = n^2-n) ) := by
  classical
  intro K n hsq1
  rw [show 1-n-n = 1-2*n by ring]
  exact hsq1

private theorem qChildCenter :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        (
        (∀ (z :
            GaussianInt),
        let n : Int := K.1;
        let Q (x : GaussianInt) : Int :=
          (Int.natAbs x.re : Int) * ((Int.natAbs x.re : Int)-1)/2 -
            (x.re-x.im)^2/4;
        (z.re = n) → (((1-2*n)^2/4 = n^2-n) → (((-n-n)^2/4 = n^2) → (((1-n-n)^2/4 = n^2-n) → (Q
            ⟨-n,n⟩ = n*(n-1)/2-n^2))))))) ) := by
  classical
  intro K hk z n Q hzr hsq1 hsq0' hsq1'
  change (Int.natAbs (-n) : Int) * ((Int.natAbs (-n) : Int)-1)/2 -
    (-n-n)^2/4 = n*(n-1)/2-n^2
  simp only [Int.natCast_natAbs, abs_of_nonpos (show -n ≤ 0 by omega)]
  rw [hsq0']
  ring

private theorem qChildEast :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        (
        (∀ (z :
            GaussianInt),
        let n : Int := K.1;
        let Q (x : GaussianInt) : Int :=
          (Int.natAbs x.re : Int) * ((Int.natAbs x.re : Int)-1)/2 -
            (x.re-x.im)^2/4;
        (z.re = n) → (((1-2*n)^2/4 = n^2-n) → (((-n-n)^2/4 = n^2) → (((1-n-n)^2/4 = n^2-n) → (Q
            ⟨1-n,n⟩ = (n-1)*(n-2)/2-(n^2-n)))))))) ) := by
  classical
  intro K hk z n Q hzr hsq1 hsq0' hsq1'
  change (Int.natAbs (1-n) : Int) * ((Int.natAbs (1-n) : Int)-1)/2 -
    ((1-n)-n)^2/4 = (n-1)*(n-2)/2-(n^2-n)
  simp only [Int.natCast_natAbs, abs_of_nonpos (show 1-n ≤ 0 by omega)]
  rw [hsq1']
  ring

private theorem hLap :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
          ∀ (f : IntegerLatticeFunction),
            ∀ (B : Int),
              ∀ (z : GaussianInt),
                let n : Int := K.1;
                let M : GaussianInt := ⟨2 * n, 0⟩;
                let Q (x : GaussianInt) : Int :=
                  (Int.natAbs x.re : Int) * ((Int.natAbs x.re : Int) - 1) / 2 -
                    (x.re - x.im) ^ 2 / 4;
                z = ⟨n, n⟩ →
                  z - 1 = ⟨n - 1, n⟩ →
                    z + ⟨0, 1⟩ = ⟨n, n + 1⟩ →
                      z - ⟨0, 1⟩ = ⟨n, n - 1⟩ →
                        z + 1 = ⟨n + 1, n⟩ →
                          f z = Q z →
                            f (z - 1) = Q (z - 1) →
                              f (z + ⟨0, 1⟩) = Q (z + ⟨0, 1⟩) →
                                f (z - ⟨0, 1⟩) = Q (z - ⟨0, 1⟩) →
                                f z = Q (z - M) + (n - 1) * z.re + n * z.im + B →
                                f (z + 1) =
                                Q (z + 1 - M) + (n - 1) * (z + 1).re + n * (z + 1).im +
                                B →
                                Q ⟨n, n⟩ = n * (n - 1) / 2 →
                                Q ⟨n - 1, n⟩ = (n - 1) * (n - 2) / 2 →
                                Q ⟨n, n + 1⟩ = n * (n - 1) / 2 →
                                Q ⟨n, n - 1⟩ = n * (n - 1) / 2 →
                                (-n - n) ^ 2 / 4 = n ^ 2 →
                                (1 - n - n) ^ 2 / 4 = n ^ 2 - n →
                                Q ⟨-n, n⟩ = n * (n - 1) / 2 - n ^ 2 →
                                Q ⟨1 - n, n⟩ = (n - 1) * (n - 2) / 2 - (n ^ 2 - n) →
                                z - M = ⟨-n, n⟩ →
                                z + 1 - M = ⟨1 - n, n⟩ → FourNeighborLaplacian f z = 1
    ) := by
  classical
  intro K f B z n M Q hzc hWc hNc hSc hEc hfCenter hfWest hfNorth hfSouth hfChildCenter hfEast
      qCenter qWest qNorth qSouth hsq0' hsq1' qChildCenter qChildEast hChildCenter hChildEast
  have hB : B = n-n^2 := by
    rw [hfCenter] at hfChildCenter
    rw [hChildCenter, qChildCenter] at hfChildCenter
    rw [hzc, qCenter] at hfChildCenter
    change n*(n-1)/2 = n*(n-1)/2 - n^2 + (n-1)*n+n*n+B at hfChildCenter
    ring_nf at hfChildCenter ⊢
    omega
  have hv0 : f z = n*(n-1)/2 := by rw [hfCenter, hzc, qCenter]
  have hvW : f (z-1) = (n-1)*(n-2)/2 := by rw [hfWest, hWc, qWest]
  have hvN : f (z+⟨0,1⟩) = n*(n-1)/2 := by rw [hfNorth, hNc, qNorth]
  have hvS : f (z-⟨0,1⟩) = n*(n-1)/2 := by rw [hfSouth, hSc, qSouth]
  have hvE : f (z+1) = (n-1)*(n-2)/2 + 2*n-1 := by
    rw [hfEast, hChildEast, qChildEast, hEc, hB]
    simp
    ring
  have tri (a : Int) : 2 * (a * (a-1) / 2) = a * (a-1) := by
    rcases Int.emod_two_eq_zero_or_one a with h | h
    · have ha : a = 2 * (a / 2) := by omega
      rw [ha]
      have he : 2 * (a / 2) * (2 * (a / 2) - 1) =
          2 * ((a / 2) * (2 * (a / 2) - 1)) := by ring
      rw [he, Int.mul_ediv_cancel_left _ (by norm_num : (2 : Int) ≠ 0)]
    · have ha : a = 2 * (a / 2) + 1 := by omega
      rw [ha]
      have he : (2 * (a / 2) + 1) * (2 * (a / 2) + 1 - 1) =
          2 * ((2 * (a / 2) + 1) * (a / 2)) := by ring
      rw [he, Int.mul_ediv_cancel_left _ (by norm_num : (2 : Int) ≠ 0)]
  have htri : (n-1)*(n-2)/2 - n*(n-1)/2 = 1-n := by
    have h1 := tri (n-1)
    have h2 := tri n
    have h1' : 2*((n-1)*(n-2)/2) = (n-1)*(n-2) := by
      convert h1 using 1 <;> congr 1 <;> ring
    have hd : 2*((n-1)*(n-2)/2 - n*(n-1)/2) = 2*(1-n) := by
      rw [mul_sub, h1', h2]
      ring
    omega
  rw [FourNeighborLaplacian, hvE, hvW, hvN, hvS, hv0]
  linear_combination 2 * htri

end DiamondRightHorizontal

theorem P5352T2RightHorizontal (K : DiamondParameter) (hk : 1 < K.1)
    (f : IntegerLatticeFunction) (B : Int) (z : GaussianInt) :
    let A := P5352T2Sources K hk 0
    let M := (P5352T2PlacementData K.1 2).1
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
  dsimp only
  intro hC hR hz hzM hstar
  let n : Int := K.1
  let M : GaussianInt := ⟨2*n, 0⟩
  let Q (x : GaussianInt) : Int :=
    (Int.natAbs x.re : Int) * ((Int.natAbs x.re : Int)-1)/2 -
      (x.re-x.im)^2/4
  have hM : (P5352T2PlacementData K.1 2).1.1 = M := by
    simp [P5352T2PlacementData, M, n]
  have hbeta : (P5352T2PlacementData K.1 2).1.2 = ⟨n-1,n⟩ := by
    simp [P5352T2PlacementData, n]
  have hA : (P5352T2Sources K hk 0).1 = DiamondTile K.1 := by
    simp [P5352T2Sources]
  have hcoords (w : GaussianInt) (hw : w ∈ FootprintVertices (DiamondTile K.1)) :
      0 ≤ w.im ∧ w.im ≤ 2*n ∧ -n ≤ w.re ∧ w.re ≤ n ∧
        -w.im-1 ≤ w.re ∧ w.re ≤ w.im+1 ∧
        -(2*n-w.im+1) ≤ w.re ∧ w.re ≤ 2*n-w.im+1 := DiamondRightHorizontal.hcoords K w hw
  have hz' := DiamondRightHorizontal.hz' K hk z hzM hM hA
  have hzB := hcoords z (by simpa [hA] using hz)
  have hzMB := hcoords (z-M) hz'
  have hzr : z.re = n := DiamondRightHorizontal.hzr K z hzB hzMB
  have hzi : z.im = n := DiamondRightHorizontal.hzi K hk z hstar hM hA hcoords hzB hzMB hzr
  have hzc : z = ⟨n,n⟩ := by ext <;> simp [hzr,hzi]
  have foot (a b : Int)
      (hb : 0 ≤ b ∧ b ≤ 2*n ∧ -n ≤ a ∧ a ≤ n ∧
        -b-1 ≤ a ∧ a ≤ b+1 ∧ -(2*n-b+1) ≤ a ∧ a ≤ 2*n-b+1) :
      (⟨a,b⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1) := DiamondRightHorizontal.foot
          K a b hb
  have cellD (a b : Int)
      (hb : 0 ≤ b ∧ b < 2*n ∧ -(b+1) ≤ a ∧ a < b+1 ∧
        -(2*n-b) ≤ a ∧ a < 2*n-b) := DiamondRightHorizontal.cellD K a b hb
  have coverCells := DiamondRightHorizontal.coverCells K hk z hM hA hzr hzc cellD
  have hWc : z-1 = ⟨n-1,n⟩ := by rw [hzc]; ext <;> simp
  have hNc : z+⟨0,1⟩ = ⟨n,n+1⟩ := by rw [hzc]; ext <;> simp
  have hSc : z-⟨0,1⟩ = ⟨n,n-1⟩ := by rw [hzc]; ext <;> simp
  have hEc : z+1 = ⟨n+1,n⟩ := by rw [hzc]; ext <;> simp
  have hw : z-1 ∈ FootprintVertices (DiamondTile K.1) := by
    rw [hWc]; exact foot (n-1) n (by constructor <;> omega)
  have hnorth : z+⟨0,1⟩ ∈ FootprintVertices (DiamondTile K.1) := by
    rw [hNc]; exact foot n (n+1) (by constructor <;> omega)
  have hsouth : z-⟨0,1⟩ ∈ FootprintVertices (DiamondTile K.1) := by
    rw [hSc]; exact foot n (n-1) (by constructor <;> omega)
  have hchildEast := DiamondRightHorizontal.hchildEast K hk z hzr foot hEc
  have hparent (w : GaussianInt) (hw : w ∈ FootprintVertices (DiamondTile K.1)) :
      f w = Q w := DiamondRightHorizontal.hparent K hk f hC w hw
  have hfCenter : f z = Q z := hparent z (by simpa [hA] using hz)
  have hfWest : f (z-1) = Q (z-1) := hparent (z-1) hw
  have hfNorth : f (z+⟨0,1⟩) = Q (z+⟨0,1⟩) := hparent _ hnorth
  have hfSouth : f (z-⟨0,1⟩) = Q (z-⟨0,1⟩) := hparent _ hsouth
  have hfChildCenter := DiamondRightHorizontal.hfChildCenter K hk f B z hR hzM hM hbeta hA
  have hfEast := DiamondRightHorizontal.hfEast K hk f B z hR hM hbeta hA hchildEast
  have qCenter : Q ⟨n,n⟩ = n*(n-1)/2 := by
    simp [Q, abs_of_nonneg (show 0 ≤ n by omega)]
  have qWest : Q ⟨n-1,n⟩ = (n-1)*(n-2)/2 := by
    simp [Q, abs_of_nonneg (show 0 ≤ n-1 by omega)]; ring
  have qNorth : Q ⟨n,n+1⟩ = n*(n-1)/2 := by
    simp [Q, abs_of_nonneg (show 0 ≤ n by omega)]
  have qSouth : Q ⟨n,n-1⟩ = n*(n-1)/2 := by
    simp [Q, abs_of_nonneg (show 0 ≤ n by omega)]
  have hsq0 : (-2*n)^2/4 = n^2 := by
    simpa using (P4207T1FloorArithmetic.1 0 (-n))
  have hsq1 := DiamondRightHorizontal.hsq1 K
  have hsq0' := DiamondRightHorizontal.hsq0' K hsq0
  have hsq1' := DiamondRightHorizontal.hsq1' K hsq1
  have qChildCenter := DiamondRightHorizontal.qChildCenter K hk z hzr hsq1 hsq0' hsq1'
  have qChildEast := DiamondRightHorizontal.qChildEast K hk z hzr hsq1 hsq0' hsq1'
  have hChildCenter : z-M = ⟨-n,n⟩ := by rw [hzc]; ext <;> simp [M]; ring
  have hChildEast : (z+1)-M = ⟨1-n,n⟩ := by rw [hzc]; ext <;> simp [M]; ring
  have hLap := DiamondRightHorizontal.hLap K f B z hzc hWc hNc hSc hEc hfCenter hfWest
      hfNorth hfSouth hfChildCenter hfEast qCenter qWest qNorth qSouth hsq0' hsq1'
      qChildCenter qChildEast hChildCenter hChildEast
  refine ⟨?_, ?_⟩
  · intro _
    exact hLap
  · intro hbad
    exact (hbad coverCells).elim

end ApollonianSuperharmonic

end
