/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacianProperties

public import LeanPool.ApollonianSuperharmonic.P5352T2PlacementData
public import LeanPool.ApollonianSuperharmonic.P5352T2DomainRows
public import LeanPool.ApollonianSuperharmonic.DiamondLaplacianTable
public import LeanPool.ApollonianSuperharmonic.P5352T2Sources

-- [TABLET NODE: P5352T2Predecessor0]

/-!
# P5352T2Predecessor0

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FirstPredecessorCases


private theorem endAlgebra :
    (by
      classical
      exact
        ∀ (b : ℤ), -((b - (1 : ℤ)) ^ (2 : ℕ) - (b - (1 : ℤ))) + (b - (1 : ℤ)) * (b - (1 : ℤ)) -
            (-(b - (1 : ℤ)) ^ (2 : ℕ) + (b - (1 : ℤ)) * (b - (1 : ℤ))) = b - (1 : ℤ) ) := by
  classical
  intro b
  ring

private theorem endAlgebraB :
    (by
      classical
      exact
        ∀ (b : ℤ), ∀ (c : ℤ), -((b - (1 : ℤ)) ^ (2 : ℕ) - (b - (1 : ℤ))) + (b - (1 : ℤ)) * (b -
            (1 : ℤ)) + c - ((0 / 2 : ℤ) - (b - (1 : ℤ)) ^ (2 : ℕ) + (b - (1 : ℤ)) * (b - (1 : ℤ))
            + c) = b - (1 : ℤ) ) := by
  classical
  intro b c
  norm_num

private theorem childMem :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let k : Int := K.1
        ∀ (a : ℤ), ∀ (b : ℤ), (0 : ℤ) ≤ b → b ≤ (2 : ℤ) * k → -k ≤ a → a ≤ k → -b - (1 : ℤ) ≤ a →
            a ≤ b + (1 : ℤ) → -((2 : ℤ) * k - b + (1 : ℤ)) ≤ a → a ≤ (2 : ℤ) * k - b + (1 : ℤ) →
            ⟨a, b⟩ ∈ FootprintVertices (DiamondTile K.1) ) := by
  classical
  intro K k a b hb0 hb1 ha0 ha1 hs0 hs1 ht0 ht1
  exact (P5352T2DomainRows K ⟨a,b⟩).1.mpr
    ⟨hb0, hb1, ha0, ha1, hs0, hs1, ht0, ht1⟩

private theorem boundaryCase :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        let d : GaussianInt := ⟨k, 1-k⟩
        let r : GaussianInt := ⟨2*k, 0⟩
        let child := P5352T2Sources K hk 0
        let pred := P5352T2Sources K hk 3
        (∀ y ∈ FootprintVertices child.1, f y = child.2.1 y) → (((2 : ℤ) ≤ k) → (∀ (p : ℤ), ∀ (q
            : ℤ), (⟨p, q⟩ ∈ FootprintVertices child.1) → ((⟨p, q⟩ - d ∈ FootprintVertices pred.1)
            → ((∀ (y : GaussianInt), y = ⟨p, q⟩ ∨ y = ⟨p, q⟩ + (1 : GaussianInt) ∨ y = ⟨p, q⟩ -
            (1 : GaussianInt) ∨ y = ⟨p, q⟩ + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ y = ⟨p, q⟩ - ⟨(0 : ℤ), (1 : ℤ)⟩
            → y ∈ FootprintVertices child.1 ∨ y - d ∈ FootprintVertices pred.1) → (((1 : ℤ) ≤ q +
            k ∧ q ≤ (2 : ℤ) * (k - (1 : ℤ)) + ((1 : ℤ) - k) ∧ k ≤ p + (k - (1 : ℤ)) ∧ p ≤ k - (1
            : ℤ) + k ∧ (1 : ℤ) ≤ p - k + (1 : ℤ) + q + k ∧ p ≤ q - ((1 : ℤ) - k) + (1 : ℤ) + k ∧
            q ≤ (1 : ℤ) + (p - k) + (2 : ℤ) * (k - (1 : ℤ)) + ((1 : ℤ) - k) ∧ p ≤ (2 : ℤ) * (k -
            (1 : ℤ)) - (q - ((1 : ℤ) - k)) + (1 : ℤ) + k) → (((↑(K.1 - (1 : ℕ)) : ℤ) = k - (1 :
            ℤ)) → (((0 : ℤ) ≤ q ∧ q ≤ (2 : ℤ) * k ∧ -k ≤ p ∧ p ≤ k ∧ -q - (1 : ℤ) ≤ p ∧ p ≤ q +
            (1 : ℤ) ∧ -((2 : ℤ) * k - q + (1 : ℤ)) ≤ p ∧ p ≤ (2 : ℤ) * k - q + (1 : ℤ)) → (((1 :
            ℤ) ≤ p) → ((q = p - (1 : ℤ) ∨ q = p) → ((∀ (a : Int), ∀ (b : Int), (0 ≤ b) → ((b ≤
            2*k) → ((-k ≤ a) → ((a ≤ k) → ((-b-1 ≤ a) → ((a ≤ b+1) → ((-(2*k-b+1) ≤ a) → ((a ≤
            2*k-b+1) → ((⟨a,b⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1)))))))))) → (q
            = p → (⟨p, p⟩ - r ∈ FootprintVertices child.1 → FourNeighborLaplacian f ⟨p, p⟩ = (0 :
            ℤ)) ∧ (⟨p, p⟩ - r ∉ FootprintVertices child.1 → FourNeighborLaplacian f ⟨p, p⟩ = (1 :
            ℤ))))))))))))) ) := by
  classical
  intro K hk f k d r child pred hchild hkI p q hz hpz hcover hdpred hcast hdchild hp1 hq childMem
      hqp
  subst q
  have hplt : p < k := by omega
  have hpadd : p+1 ≤ k := Int.lt_iff_add_one_le.mp hplt
  have hEb : 0 ≤ p ∧ p ≤ 2*k ∧ -k ≤ p+1 ∧ p+1 ≤ k ∧
      -p-1 ≤ p+1 ∧ p+1 ≤ p+1 ∧ -(2*k-p+1) ≤ p+1 ∧ p+1 ≤ 2*k-p+1 := by
    omega
  have hWb : 0 ≤ p ∧ p ≤ 2*k ∧ -k ≤ p-1 ∧ p-1 ≤ k ∧
      -p-1 ≤ p-1 ∧ p-1 ≤ p+1 ∧ -(2*k-p+1) ≤ p-1 ∧ p-1 ≤ 2*k-p+1 := by
    omega
  have hNb : 0 ≤ p+1 ∧ p+1 ≤ 2*k ∧ -k ≤ p ∧ p ≤ k ∧
      -(p+1)-1 ≤ p ∧ p ≤ p+1+1 ∧ -(2*k-(p+1)+1) ≤ p ∧ p ≤ 2*k-(p+1)+1 := by
    omega
  have hSb : 0 ≤ p-1 ∧ p-1 ≤ 2*k ∧ -k ≤ p ∧ p ≤ k ∧
      -(p-1)-1 ≤ p ∧ p ≤ p-1+1 ∧ -(2*k-(p-1)+1) ≤ p ∧ p ≤ 2*k-(p-1)+1 := by
    omega
  have hE : (⟨p+1,p⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1) :=
    childMem (p+1) p hEb.1 hEb.2.1 hEb.2.2.1 hEb.2.2.2.1
      hEb.2.2.2.2.1 hEb.2.2.2.2.2.1 hEb.2.2.2.2.2.2.1 hEb.2.2.2.2.2.2.2
  have hW : (⟨p-1,p⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1) :=
    childMem (p-1) p hWb.1 hWb.2.1 hWb.2.2.1 hWb.2.2.2.1
      hWb.2.2.2.2.1 hWb.2.2.2.2.2.1 hWb.2.2.2.2.2.2.1 hWb.2.2.2.2.2.2.2
  have hN : (⟨p,p+1⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1) :=
    childMem p (p+1) hNb.1 hNb.2.1 hNb.2.2.1 hNb.2.2.2.1
      hNb.2.2.2.2.1 hNb.2.2.2.2.2.1 hNb.2.2.2.2.2.2.1 hNb.2.2.2.2.2.2.2
  have hS : (⟨p,p-1⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1) :=
    childMem p (p-1) hSb.1 hSb.2.1 hSb.2.2.1 hSb.2.2.2.1
      hSb.2.2.2.2.1 hSb.2.2.2.2.2.1 hSb.2.2.2.2.2.2.1 hSb.2.2.2.2.2.2.2
  have fval (w : GaussianInt) (hw : w ∈ FootprintVertices (DiamondTile K.1)) :
      f w = DiamondOdometer K w := by
    simpa [child, P5352T2Sources] using hchild w (by
      simpa [child, P5352T2Sources] using hw)
  have hcenter : f ⟨p,p⟩ = DiamondOdometer K ⟨p,p⟩ := fval _ hz
  have heast : f (⟨p,p⟩+1) = DiamondOdometer K (⟨p,p⟩+1) := by
    have he : (⟨p,p⟩ : GaussianInt)+1 = ⟨p+1,p⟩ := by ext <;> simp
    rw [he]
    exact fval _ hE
  have hwest : f (⟨p,p⟩-1) = DiamondOdometer K (⟨p,p⟩-1) := by
    have he : (⟨p,p⟩ : GaussianInt)-1 = ⟨p-1,p⟩ := by ext <;> simp
    rw [he]
    exact fval _ hW
  have hnorth : f (⟨p,p⟩+⟨0,1⟩) = DiamondOdometer K (⟨p,p⟩+⟨0,1⟩) := by
    have he : (⟨p,p⟩ : GaussianInt)+⟨0,1⟩ = ⟨p,p+1⟩ := by ext <;> simp
    rw [he]
    exact fval _ hN
  have hsouth : f (⟨p,p⟩-⟨0,1⟩) = DiamondOdometer K (⟨p,p⟩-⟨0,1⟩) := by
    have he : (⟨p,p⟩ : GaussianInt)-⟨0,1⟩ = ⟨p,p-1⟩ := by ext <;> simp
    rw [he]
    exact fval _ hS
  have hpn : (Int.natAbs p : Int) = p := by
    rw [Int.natCast_natAbs, abs_of_nonneg (show 0 ≤ p by omega)]
  have hqn : (Int.natAbs (p-k) : Int) = k-p := by
    rw [Int.natCast_natAbs, abs_of_nonpos (show p-k ≤ 0 by omega)]
    omega
  have hKsub : ((K.1-1 : Nat) : Int) = k-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ K.1)]
    dsimp [k]
  have hnot : (⟨p,p⟩ : GaussianInt) ∉ DiamondVertexDomains K true := by
    change ¬ (Int.natAbs p + Int.natAbs (p-(K.1:Int)) ≤ K.1-1)
    intro hh
    have hhI : ((Int.natAbs p + Int.natAbs (p-(K.1:Int)) : Nat) : Int) ≤
        ((K.1-1 : Nat) : Int) := by exact_mod_cast hh
    rw [Int.natCast_add, hpn, hqn, hKsub] at hhI
    omega
  have hdom : (⟨p,p⟩ : GaussianInt) ∈ DiamondVertexDomains K false := by
    obtain ⟨_, _, _, hfp, _, _⟩ := DiamondTileOdometerRestriction K
    exact hfp ▸ (by simpa [child, P5352T2Sources] using hz)
  have htable := (DiamondLaplacianTable K).2.1 ⟨p,p⟩ hdom hnot
  have hcomp : (⟨p,p⟩ : GaussianInt)-r ∉ FootprintVertices child.1 := by
    intro hc
    have hb := (P5352T2DomainRows K (⟨p,p⟩-r)).1.mp (by
      simpa [child, P5352T2Sources] using hc)
    simp [r] at hb
    omega
  refine ⟨fun hc => (hcomp hc).elim, ?_⟩
  intro _
  rw [FourNeighborLaplacian, heast, hwest, hnorth, hsouth, hcenter]
  exact htable

private theorem childValue :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (f : IntegerLatticeFunction),
        let child := P5352T2Sources K hk 0
        (∀ y ∈ FootprintVertices child.1, f y = child.2.1 y) → (
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1) / 2 - (a-b)^2/4
        ∀ w ∈ FootprintVertices (DiamondTile K.1), f w = Q w.re w.im) ) := by
  classical
  intro K hk f child hchild Q w hw
  have hw' : w ∈ FootprintVertices child.1 := by
    simpa [child, P5352T2Sources] using hw
  rw [hchild w hw']
  simpa [Q, child, P5352T2Sources] using (P5352T2DomainRows K w).2 hw

private theorem predFoot :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        (ℤ) → ((ℤ) → (((↑(K.1 - (1 : ℕ)) : ℤ) = k - (1 : ℤ)) → (∀ (w : GaussianInt), (0 :
            ℤ) ≤ w.im ∧ w.im ≤ (2 : ℤ) * (k - (1 : ℤ)) ∧ -(k - (1 : ℤ)) ≤
            w.re ∧ w.re ≤ k - (1 : ℤ) ∧ -w.im - (1 : ℤ) ≤ w.re ∧ w.re ≤ w.im + (1 : ℤ) ∧ -((2 :
            ℤ) * (k - (1 : ℤ)) - w.im + (1 : ℤ)) ≤ w.re ∧ w.re ≤ (2 : ℤ) * (k - (1 : ℤ)) - w.im +
            (1 : ℤ) → w ∈ FootprintVertices (DiamondTile (K.1 - (1 : ℕ)))))))) := by
  classical
  intro K hk k p q hcast w hw
  let Kp : DiamondParameter := ⟨K.1-1, by omega⟩
  apply (P5352T2DomainRows Kp w).1.mpr
  simpa [Kp, hcast] using hw

private theorem predValue :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1),
        let k : Int := K.1
        let pred := P5352T2Sources K hk 3
        ∀ (p : ℤ), ∀ (q : ℤ), ∀ (hcast : (↑(K.1 - (1 : ℕ)) : ℤ) = k - (1 : ℤ)),
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1) / 2 - (a-b)^2/4
        ∀ w ∈ FootprintVertices (DiamondTile (K.1 - (1 : ℕ))), pred.2.1 w = Q w.re w.im ) := by
  classical
  intro K hk k pred p q hcast Q w hw
  let Kp : DiamondParameter := ⟨K.1-1, by omega⟩
  simpa [Q, pred, Kp, P5352T2Sources] using (P5352T2DomainRows Kp w).2 hw

private theorem predTranslatedValue :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (f : IntegerLatticeFunction), ∀ (B :
            Int),
        let k : Int := K.1
        let d : GaussianInt := ⟨k, 1-k⟩
        let pred := P5352T2Sources K hk 3
        (∀ (y : GaussianInt), y - d ∈ FootprintVertices pred.1 → f y = pred.2.1 (y - d) + (⟨(0 :
            ℤ), k - (1 : ℤ)⟩ : GaussianInt).re * y.re + (⟨(0 : ℤ), k - (1 : ℤ)⟩ : GaussianInt).im
            * y.im + B) → (
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1) / 2 - (a-b)^2/4
        (∀ (w : GaussianInt), (w ∈ FootprintVertices (DiamondTile (K.1-1))) → (pred.2.1 w = Q
            w.re w.im)) → (∀ (y : GaussianInt), y - d ∈ FootprintVertices (DiamondTile (K.1 - (1
            : ℕ))) → f y = Q (y - d).re (y - d).im + (k - (1 : ℤ)) * y.im + B)) ) := by
  classical
  intro K hk f B k d pred hpred Q predValue y hy
  have h := hpred y (by simpa [pred, P5352T2Sources] using hy)
  have hv := predValue (y-d) hy
  have h' : f y = pred.2.1 (y-d) + (k-1)*y.im+B := by simpa using h
  rw [hv] at h'
  simpa [d] using h'

private theorem hComp :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1),
        let k : Int := K.1
        let d : GaussianInt := ⟨k, 1-k⟩
        let r : GaussianInt := ⟨2*k, 0⟩
        let child := P5352T2Sources K hk 0
        let pred := P5352T2Sources K hk 3
        ∀ (p : ℤ), ∀ (q : ℤ), (⟨p, q⟩ ∈ FootprintVertices child.1) → ((⟨p, q⟩ - d ∈
            FootprintVertices pred.1) → (((↑(K.1 - (1 : ℕ)) : ℤ) = k - (1 : ℤ)) → (((1 : ℤ) ≤ p)
            → ((p ≤ k) → ((∀ (a : Int), ∀ (b : Int), (0 ≤ b) → ((b ≤ 2*k) → ((-k ≤ a) → ((a ≤ k)
            → ((-b-1 ≤ a) → ((a ≤ b+1) → ((-(2*k-b+1) ≤ a) → ((a ≤ 2*k-b+1) → ((⟨a,b⟩ :
            GaussianInt) ∈ FootprintVertices (DiamondTile K.1)))))))))) → ((q = p - (1 : ℤ)) → (
        let zA : GaussianInt := ⟨p,p-1⟩
        (zA ∈ FootprintVertices (DiamondTile K.1)) → (zA-r ∈ FootprintVertices (DiamondTile K.1)
            ↔ p=k)))))))) ) := by
  classical
  intro K hk k d r child pred p q hz hpz hcast hp1 hpk childMem hq zA hzA
  constructor
  · intro hh
    have hb := (P5352T2DomainRows K (zA-r)).1.mp hh
    have hl := hb.2.2.1
    have hre : (zA-r).re = p-2*k := by simp [zA,r]
    rw [hre] at hl
    omega
  · intro hp
    subst p
    have he : zA-r = (⟨-k,k-1⟩ : GaussianInt) := by
      ext <;> simp [zA,r]; omega
    rw [he]
    exact childMem (-k) (k-1) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)

private theorem hPe :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        ∀ (p : ℤ), ∀ (q : ℤ), ((↑(K.1 - (1 : ℕ)) : ℤ) = k - (1 : ℤ)) → (((1 : ℤ) ≤ p) → ((p ≤ k)
            → ((∀ (w : GaussianInt), (0 ≤ w.im ∧ w.im ≤ 2*(k-1) ∧ -(k-1) ≤ w.re ∧ w.re ≤ k-1 ∧
            -w.im-1 ≤ w.re ∧ w.re ≤ w.im+1 ∧ -(2*(k-1)-w.im+1) ≤ w.re ∧ w.re ≤ 2*(k-1)-w.im+1) →
            (w ∈ FootprintVertices (DiamondTile (K.1-1)))) → ((q = p - (1 : ℤ)) →
            (((⟨p+1-k,p+k-2⟩ : GaussianInt)) ∈ FootprintVertices (DiamondTile (K.1-1)))))))) ) := by
  classical
  intro K hk k p q hcast hp1 hpk predFoot hq
  apply predFoot
  constructor <;> simp [] <;> omega

private theorem hPs :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        ∀ (p : ℤ), ∀ (q : ℤ), ((↑(K.1 - (1 : ℕ)) : ℤ) = k - (1 : ℤ)) → (((1 : ℤ) ≤ p) → ((p ≤ k)
            → ((∀ (w : GaussianInt), (0 ≤ w.im ∧ w.im ≤ 2*(k-1) ∧ -(k-1) ≤ w.re ∧ w.re ≤ k-1 ∧
            -w.im-1 ≤ w.re ∧ w.re ≤ w.im+1 ∧ -(2*(k-1)-w.im+1) ≤ w.re ∧ w.re ≤ 2*(k-1)-w.im+1) →
            (w ∈ FootprintVertices (DiamondTile (K.1-1)))) → ((q = p - (1 : ℤ)) → (((⟨p-k,p+k-3⟩
            : GaussianInt)) ∈ FootprintVertices (DiamondTile (K.1-1)))))))) ) := by
  classical
  intro K hk k p q hcast hp1 hpk predFoot hq
  apply predFoot
  constructor <;> simp [] <;> omega

private theorem hCW :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (p : ℤ),
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1) / 2 - (a-b)^2/4
        (∀ (w : GaussianInt), (w ∈ FootprintVertices (DiamondTile K.1)) → (f w = Q w.re w.im)) → (
        let zA : GaussianInt := ⟨p,p-1⟩
        ((⟨p-1,p-1⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1)) → (
        let valW : Int := Q (p-1) (p-1)
        f (zA-1) = valW)) ) := by
  classical
  intro K f p Q childValue zA hW valW
  have hw : zA-1 = (⟨p-1,p-1⟩ : GaussianInt) := by ext <;> simp [zA]
  rw [hw]
  exact childValue _ hW

private theorem hCN :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (p : ℤ),
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1) / 2 - (a-b)^2/4
        (∀ (w : GaussianInt), (w ∈ FootprintVertices (DiamondTile K.1)) → (f w = Q w.re w.im)) → (
        let zA : GaussianInt := ⟨p,p-1⟩
        ((⟨p,p⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1)) → (
        let valN : Int := Q p p
        f (zA+⟨0,1⟩) = valN)) ) := by
  classical
  intro K f p Q childValue zA hN valN
  have hw : zA+⟨0,1⟩ = (⟨p,p⟩ : GaussianInt) := by ext <;> simp [zA]
  rw [hw]
  exact childValue _ hN

private theorem hPcenter :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        let d : GaussianInt := ⟨k, 1-k⟩
        ∀ (p : ℤ),
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1) / 2 - (a-b)^2/4
        (∀ (y : GaussianInt), (y-d ∈ FootprintVertices (DiamondTile (K.1-1))) → (f y = Q (y-d).re
            (y-d).im + (k-1)*y.im+B)) → (
        let zA : GaussianInt := ⟨p,p-1⟩
        ((zA-d) ∈ FootprintVertices (DiamondTile (K.1-1))) → (
        let valC : Int := Q (p-k) (p-1-(1-k))
        f zA = valC + (k-1)*(p-1)+B)) ) := by
  classical
  intro K f B k d p Q predTranslatedValue zA hP0 valC
  have hv := predTranslatedValue zA hP0
  simpa [valC, zA, d] using hv

private theorem hPeast :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        let d : GaussianInt := ⟨k, 1-k⟩
        ∀ (p : ℤ),
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1) / 2 - (a-b)^2/4
        (∀ (y : GaussianInt), (y-d ∈ FootprintVertices (DiamondTile (K.1-1))) → (f y = Q (y-d).re
            (y-d).im + (k-1)*y.im+B)) → (
        let zA : GaussianInt := ⟨p,p-1⟩
        ((zA+1)-d = (⟨p+1-k,p+k-2⟩ : GaussianInt)) → ((((⟨p+1-k,p+k-2⟩ : GaussianInt)) ∈
            FootprintVertices (DiamondTile (K.1-1))) → (f (zA+1) = Q (p+1-k) (p-1-(1-k)) +
            (k-1)*(p-1)+B))) ) := by
  classical
  intro K f B k d p Q predTranslatedValue zA he hPe
  have hv := predTranslatedValue (zA+1) (by rw [he]; exact hPe)
  simpa [zA, d] using hv

private theorem hPsouth :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        let d : GaussianInt := ⟨k, 1-k⟩
        ∀ (p : ℤ),
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1) / 2 - (a-b)^2/4
        (∀ (y : GaussianInt), (y-d ∈ FootprintVertices (DiamondTile (K.1-1))) → (f y = Q (y-d).re
            (y-d).im + (k-1)*y.im+B)) → (
        let zA : GaussianInt := ⟨p,p-1⟩
        let valS : Int := Q (p-k) (p-1-1-(1-k))
        ((zA-⟨0,1⟩)-d = (⟨p-k,p+k-3⟩ : GaussianInt)) → ((((⟨p-k,p+k-3⟩ : GaussianInt)) ∈
            FootprintVertices (DiamondTile (K.1-1))) → (f (zA-⟨0,1⟩) = valS + (k-1)*(p-2)+B))) )
            := by
  classical
  intro K f B k d p Q predTranslatedValue zA valS hs hPs
  have hv := predTranslatedValue (zA-⟨0,1⟩) (by rw [hs]; exact hPs)
  calc
    f (zA-⟨0,1⟩) = valS + (k-1)*(p-1-1)+B := by
      simpa [valS, zA, d] using hv
    _ = _ := by congr 1; ring

private theorem qCW :
    (by
      classical
      exact
        (
        (
        (∀ (p : ℤ), ∀ (q : ℤ), ((1 : ℤ)
            ≤ p) → (
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1) / 2 - (a-b)^2/4;
        (q = p - (1 : ℤ)) → (
        let valW : Int := Q (p-1) (p-1);
        valW = (p-1)*(p-2)/2))))) ) := by
  classical
  intro p q hp1 Q hq valW
  simp [valW, Q, abs_of_nonneg (show 0 ≤ p-1 by omega)]
  ring

private theorem floorEven :
    (by
      classical
      exact
        ∀ (m : ℤ), ((-2 : ℤ) * m) ^ (2 : ℕ) / (4 : ℤ) = m ^ (2 : ℕ) ) := by
  classical
  intro m
  have h := P4207T1FloorArithmetic.1 0 (-m)
  simpa using h

private theorem floorOdd :
    (by
      classical
      exact
        (DiamondParameter) → ((IntegerLatticeFunction) → ((Int) → ((ℤ) → ((ℤ) → (∀ (m : ℤ), ((1 :
            ℤ) - (2 : ℤ) * m) ^ (2 : ℕ) / (4 : ℤ) = m ^ (2 : ℕ) - m))))) ) := by
  classical
  intro K f B p q m
  have h := P4207T1FloorArithmetic.1 1 (-m)
  have h' : 1 + 2*(-m) = 1-2*m := by ring
  rw [h'] at h
  norm_num at h ⊢
  omega

private theorem qP0 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        (
        (
        let k : Int := K.1;
        ∀ (p : ℤ), ∀ (q : ℤ), (p ≤ k) → (
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1) / 2 - (a-b)^2/4;
        (q = p - (1 : ℤ)) → (
        let valC : Int := Q (p-k) (p-1-(1-k));
        (∀ (m : Int), (-2*m)^2/4 = m^2) → (valC = (k-p)*(k-p-1)/2-(k-1)^2))))) ) := by
  classical
  intro K k p q hpk Q hq valC floorEven
  simp only [valC, Q, Int.natCast_natAbs]
  rw [abs_of_nonpos (show p-k ≤ 0 by omega)]
  rw [show (p-k)-(p-1-(1-k)) = -2*(k-1) by ring, floorEven]
  congr 1; ring

private theorem qPeLt :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        (
        (
        let k : Int := K.1;
        ∀ (p : ℤ), (ℤ) →
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1) / 2 - (a-b)^2/4;
        ((∀ (m : Int), (1-2*m)^2/4 = m^2-m) → (p < k → Q (p + (1 : ℤ) - k) (p
            - (1 : ℤ) - ((1 : ℤ) - k)) = (k - p - (1 : ℤ)) * (k - p - (2 : ℤ)) / (2 : ℤ) - ((k -
            (1 : ℤ)) ^ (2 : ℕ) - (k - (1 : ℤ))))))) ) := by
  classical
  intro K k p q Q floorOdd hpk'
  simp only [Q, Int.natCast_natAbs]
  rw [abs_of_nonpos (show p+1-k ≤ 0 by omega)]
  rw [show (p+1-k)-(p-1-(1-k)) = 1-2*(k-1) by ring, floorOdd]
  congr 1; ring

private theorem qPeEq :
    (by
      classical
        exact
        ∀ (K : DiamondParameter),
          let k : Int := K.1;
          ∀ (p : ℤ),
            (let Q : Int → Int → Int := fun a b =>
              (Int.natAbs a : Int) * ((Int.natAbs a : Int) - 1) / 2 -
                (a - b) ^ 2 / 4;
            ((∀ (m : Int), (1 - 2 * m) ^ 2 / 4 = m ^ 2 - m) →
              (p = k →
                Q (p + (1 : ℤ) - k) (p - (1 : ℤ) - ((1 : ℤ) - k)) =
                  -((k - (1 : ℤ)) ^ (2 : ℕ) - (k - (1 : ℤ))))))) := by
  classical
  intro K k p Q floorOdd hpk'
  subst p
  simp only [Q, Int.natCast_natAbs]
  rw [show k+1-k = 1 by omega, abs_of_nonneg (show 0 ≤ (1:Int) by omega)]
  have hsquare : (1-(k-1-(1-k)))^2/4 = (k-1)^2-(k-1) := by
    rw [show 1-(k-1-(1-k)) = 1-2*(k-1) by ring, floorOdd]
  rw [hsquare]
  norm_num

private theorem qPs :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        (
        (
        let k : Int := K.1;
        ∀ (p : ℤ), ∀ (q : ℤ), (p ≤ k) → (
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1) / 2 - (a-b)^2/4;
        (q = p - (1 : ℤ)) → (
        let valS : Int := Q (p-k) (p-1-1-(1-k));
        (∀ (m : Int), (1-2*m)^2/4 = m^2-m) → (valS = (k-p)*(k-p-1)/2-((k-1)^2-(k-1))))))) ) := by
  classical
  intro K k p q hpk Q hq valS floorOdd
  simp only [valS, Q, Int.natCast_natAbs]
  rw [abs_of_nonpos (show p-k ≤ 0 by omega)]
  rw [show (p-k)-(p-1-1-(1-k)) = 1-2*(k-1) by ring, floorOdd]
  rw [show -(p-k) = k-p by omega]

private theorem tri :
    (by
      classical
      exact
        (DiamondParameter) → ((IntegerLatticeFunction) → ((Int) → ((ℤ) → ((ℤ) → (∀ (a : ℤ), (2 :
            ℤ) * (a * (a - (1 : ℤ)) / (2 : ℤ)) = a * (a - (1 : ℤ))))))) ) := by
  classical
  intro K f B p q a
  rcases Int.emod_two_eq_zero_or_one a with h | h
  · have ha : a = 2*(a/2) := by omega
    rw [ha]
    have he : 2*(a/2)*(2*(a/2)-1) = 2*((a/2)*(2*(a/2)-1)) := by ring
    rw [he, Int.mul_ediv_cancel_left _ (by norm_num : (2:Int) ≠ 0)]
  · have ha : a = 2*(a/2)+1 := by omega
    rw [ha]
    have he : (2*(a/2)+1)*(2*(a/2)+1-1) =
        2*((2*(a/2)+1)*(a/2)) := by ring
    rw [he, Int.mul_ediv_cancel_left _ (by norm_num : (2:Int) ≠ 0)]

private theorem tdiff :
    (by
      classical
      exact
        (DiamondParameter) → ((IntegerLatticeFunction) → ((Int) → ((ℤ) → ((ℤ) → ((∀ (a : Int),
            2*(a*(a-1)/2) = a*(a-1)) → (∀ (a : ℤ), a * (a - (1 : ℤ)) / (2 : ℤ) - (a - (1 : ℤ)) *
            (a - (2 : ℤ)) / (2 : ℤ) = a - (1 : ℤ))))))) ) := by
  classical
  intro K f B p q tri a
  have h := tri a
  have h' : 2*((a-1)*(a-2)/2) = (a-1)*(a-2) := by
    simpa [show a-1-1 = a-2 by ring] using tri (a-1)
  have he : 2*(a*(a-1)/2-(a-1)*(a-2)/2) = 2*(a-1) := by
    rw [mul_sub, h, h']
    ring
  omega

private theorem tdiffRev :
    (by
      classical
      exact
        (DiamondParameter) → ((IntegerLatticeFunction) → ((Int) → ((ℤ) → ((ℤ) → ((∀ (a : Int),
            a*(a-1)/2-(a-1)*(a-2)/2 = a-1) → (∀ (a : ℤ), (a - (1 : ℤ)) * (a - (2 : ℤ)) / (2 : ℤ)
            - a * (a - (1 : ℤ)) / (2 : ℤ) = (1 : ℤ) - a)))))) ) := by
  classical
  intro K f B p q tdiff a
  have ht := tdiff a
  omega

private theorem hEastDiff :
    (by
      classical
        exact
        ∀ (K : DiamondParameter),
          ∀ (f : IntegerLatticeFunction),
            ∀ (B : Int),
              (∀ (a : Int), ∀ (b : Int), 1 - (b - a) + (b - 1) = a) →
                ((∀ (b : Int),
                    ∀ (c : Int),
                      -((b - 1) ^ 2 - (b - 1)) + (b - 1) * (b - 1) + c -
                          (0 / 2 - (b - 1) ^ 2 + (b - 1) * (b - 1) + c) =
                        b - 1) →
                  (let k : Int := K.1;
                  ∀ (p : ℤ),
                    (p ≤ k) →
                      (let Q : Int → Int → Int := fun a b =>
                        (Int.natAbs a : Int) * ((Int.natAbs a : Int) - 1) / 2 -
                          (a - b) ^ 2 / 4;
                      (let zA : GaussianInt := ⟨p, p - 1⟩;
                      let valC : Int := Q (p - k) (p - 1 - (1 - k));
                      (f zA = valC + (k - 1) * (p - 1) + B) →
                        ((f (zA + 1) =
                            Q (p + 1 - k) (p - 1 - (1 - k)) + (k - 1) * (p - 1) +
                              B) →
                          ((valC = (k - p) * (k - p - 1) / 2 - (k - 1) ^ 2) →
                            (((p < k) →
                                (Q (p + 1 - k) (p - 1 - (1 - k)) =
                                  (k - p - 1) * (k - p - 2) / 2 -
                                    ((k - 1) ^ 2 - (k - 1)))) →
                              (((p = k) →
                                  (Q (p + 1 - k) (p - 1 - (1 - k)) =
                                    -((k - 1) ^ 2 - (k - 1)))) →
                                ((∀ (a : Int),
                                    (a - 1) * (a - 2) / 2 - a * (a - 1) / 2 =
                                      1 - a) →
                                  (f (zA + 1) - f zA =
                                    if p = k then k - 1 else p))))))))))) := by
  classical
  intro K f B eastAlgebra endAlgebraB k p hpk Q zA valC hPcenter hPeast qP0 qPeLt qPeEq tdiffRev
  by_cases hp : p=k
  · rw [hPeast, hPcenter, qPeEq hp, qP0]
    rw [hp]
    simp only [sub_self, zero_mul, zero_sub]
    exact endAlgebraB k B
  · have hlt : p<k := by omega
    rw [hPeast, hPcenter, qPeLt hlt, qP0]
    rw [ite_eq_right hp]
    have hsum :
        (k-p-1)*(k-p-2)/2-((k-1)^2-(k-1))+(k-1)*(p-1)+B-
          ((k-p)*(k-p-1)/2-(k-1)^2+(k-1)*(p-1)+B) =
        ((k-p-1)*(k-p-2)/2-(k-p)*(k-p-1)/2)+(k-1) := by abel
    rw [hsum, tdiffRev (k-p)]
    exact eastAlgebra p k

private theorem hWestDiff :
    (by
      classical
      exact
        ∀ (f : IntegerLatticeFunction), (∀ {a : Int}, ∀ {b : Int}, ∀ {c : Int}, ∀ {d : Int},
            (a=b) → ((c=d) → (a-c = b-d))) → (∀ (p : ℤ),
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1) / 2 - (a-b)^2/4
        let zA : GaussianInt := ⟨p,p-1⟩
        let val0 : Int := Q p (p-1)
        let valW : Int := Q (p-1) (p-1)
        (f zA = val0) → ((f (zA-1) = valW) → ((val0 = p*(p-1)/2) → ((valW = (p-1)*(p-2)/2) → ((∀
            (a : Int), (a-1)*(a-2)/2-a*(a-1)/2 = 1-a) → (f (zA-1)-f zA = 1-p)))))) ) := by
  classical
  intro f subDiff p Q zA val0 valW hC0 hCW qC0 qCW tdiffRev
  calc
    f (zA-1)-f zA = valW-val0 := subDiff hCW hC0
    _ = 1-p := by
      rw [qCW,qC0]
      rw [tdiffRev p]

private theorem hNorthDiff :
    (by
      classical
      exact
        ∀ (f : IntegerLatticeFunction), (∀ {a : Int}, ∀ {b : Int}, ∀ {c : Int}, ∀ {d : Int},
            (a=b) → ((c=d) → (a-c = b-d))) → (∀ (p : ℤ),
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1) / 2 - (a-b)^2/4
        let zA : GaussianInt := ⟨p,p-1⟩
        let val0 : Int := Q p (p-1)
        let valN : Int := Q p p
        (f zA = val0) → ((f (zA+⟨0,1⟩) = valN) → ((val0 = p*(p-1)/2) → ((valN = p*(p-1)/2) → (f
            (zA+⟨0,1⟩)-f zA = 0))))) ) := by
  classical
  intro f subDiff p Q zA val0 valN hC0 hCN qC0 qCN
  exact (by
    have hval : valN=val0 := by
      calc
        valN = p*(p-1)/2 := qCN
        _ = val0 := qC0.symm
    calc
      f (zA+⟨0,1⟩)-f zA = valN-val0 := subDiff hCN hC0
      _ = 0 := by exact sub_eq_zero.mpr hval
  )

private theorem hSouthDiff :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int), (∀ {a : Int}, ∀
            {b : Int}, ∀ {c : Int}, ∀ {d : Int}, (a=b) → ((c=d) → (a-c = b-d))) → ((∀ (a : Int),
            ∀ (b : Int), (b-1)*(a-2)-(b-1)*(a-1)=-(b-1)) → (
        let k : Int := K.1
        ∀ (p : ℤ),
        let Q : Int → Int → Int := fun a b =>
          (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1) / 2 - (a-b)^2/4
        let zA : GaussianInt := ⟨p,p-1⟩
        let valS : Int := Q (p-k) (p-1-1-(1-k))
        let valC : Int := Q (p-k) (p-1-(1-k))
        (f zA = valC + (k-1)*(p-1)+B) → ((f (zA-⟨0,1⟩) = valS + (k-1)*(p-2)+B) → ((valS - valC =
            k-1) → (f (zA-⟨0,1⟩)-f zA = 0))))) ) := by
  classical
  intro K f B subDiff productGap k p Q zA valS valC hPcenter hPsouth hQdelta
  calc
    f (zA-⟨0,1⟩)-f zA =
        valS+(k-1)*(p-2)+B - (valC+(k-1)*(p-1)+B) := subDiff hPsouth hPcenter
    _ = 0 := by
      have hdelta : valS-valC=k-1 := hQdelta
      have hsum : valS+(k-1)*(p-2)+B - (valC+(k-1)*(p-1)+B) =
          (valS-valC)+((k-1)*(p-2)-(k-1)*(p-1)) := by abel
      rw [hsum, hdelta]
      have hgap := productGap p k
      calc
        (k-1)+((k-1)*(p-2)-(k-1)*(p-1)) = (k-1)+(-(k-1)) :=
          congrArg (fun t : Int => (k-1)+t) hgap
        _ = 0 := add_neg_cancel (k-1)

private theorem hLapZero :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), (∀ (g :
            IntegerLatticeFunction), ∀ (x : GaussianInt), FourNeighborLaplacian g x = (g (x+1)-g
            x)+(g (x-1)-g x)+ (g (x+⟨0,1⟩)-g x)+(g (x-⟨0,1⟩)-g x)) → ((∀ (a : Int),
            (a-1)+(1-a)=0) → (
        let k : Int := K.1
        ∀ (p : ℤ),
        let zA : GaussianInt := ⟨p,p-1⟩
        (f (zA+1)-f zA = if p=k then k-1 else p) → ((f (zA-1)-f zA = 1-p) → ((f (zA+⟨0,1⟩)-f zA =
            0) → ((f (zA-⟨0,1⟩)-f zA = 0) → (p = k → FourNeighborLaplacian f zA = (0 : ℤ))))))) )
            := by
  classical
  intro K f lap_identity lapZeroAlgebra k p zA hEastDiff hWestDiff hNorthDiff hSouthDiff hp
  rw [ite_eq_left hp] at hEastDiff
  have he : f (zA+1)-f zA = k-1 := hEastDiff
  rw [lap_identity, he, hWestDiff, hNorthDiff, hSouthDiff]
  rw [hp]
  simpa only [Int.add_zero] using lapZeroAlgebra k

private theorem hLapOne :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), (∀ (g :
            IntegerLatticeFunction), ∀ (x : GaussianInt), FourNeighborLaplacian g x = (g (x+1)-g
            x)+(g (x-1)-g x)+ (g (x+⟨0,1⟩)-g x)+(g (x-⟨0,1⟩)-g x)) → ((∀ (a : Int), a+(1-a)=1) → (
        let k : Int := K.1
        ∀ (p : ℤ),
        let zA : GaussianInt := ⟨p,p-1⟩
        (f (zA+1)-f zA = if p=k then k-1 else p) → ((f (zA-1)-f zA = 1-p) → ((f (zA+⟨0,1⟩)-f zA =
            0) → ((f (zA-⟨0,1⟩)-f zA = 0) → (p ≠ k → FourNeighborLaplacian f zA = (1 : ℤ))))))) )
            := by
  classical
  intro K f lap_identity lapOneAlgebra k p zA hEastDiff hWestDiff hNorthDiff hSouthDiff hp
  rw [ite_eq_right hp] at hEastDiff
  have he : f (zA+1)-f zA = p := hEastDiff
  rw [lap_identity, he, hWestDiff, hNorthDiff, hSouthDiff]
  simpa only [Int.add_zero] using lapOneAlgebra p

private theorem hce :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1),
        let k : Int := K.1
        let r : GaussianInt := ⟨2*k, 0⟩
        let child := P5352T2Sources K hk 0
        (child.1 = DiamondTile K.1) → (∀ (p : ℤ),
        let zA : GaussianInt := ⟨p,p-1⟩
        (zA = (⟨p,p-1⟩ : GaussianInt)) → ((⟨p, p - (1 : ℤ)⟩ - r ∈ FootprintVertices child.1) →
            (zA-r ∈ FootprintVertices (DiamondTile K.1)))) ) := by
  classical
  intro K hk k r child hchildTile p zA hzEq hc
  have hpEq : zA-r = (⟨p,p-1⟩ : GaussianInt)-r :=
    congrArg (fun w : GaussianInt => w-r) hzEq
  rw [hpEq]
  exact hchildTile ▸ hc

private theorem hpAt505 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1),
        let k : Int := K.1
        let r : GaussianInt := ⟨2*k, 0⟩
        let child := P5352T2Sources K hk 0
        (child.1 = DiamondTile K.1) → (∀ (p : ℤ),
        let zA : GaussianInt := ⟨p,p-1⟩
        (zA-r ∈ FootprintVertices (DiamondTile K.1) ↔ p=k) → ((zA = (⟨p,p-1⟩ : GaussianInt)) →
            ((⟨p, p - (1 : ℤ)⟩ - r ∉ FootprintVertices child.1) → (p≠k)))) ) := by
  classical
  intro K hk k r child hchildTile p zA hComp hzEq hn heq
  apply hn
  have hc := hComp.mpr heq
  have hpEq : zA-r = (⟨p,p-1⟩ : GaussianInt)-r :=
    congrArg (fun w : GaussianInt => w-r) hzEq
  rw [← hpEq]
  exact hchildTile.symm ▸ hc

end FirstPredecessorCases

theorem P5352T2Predecessor0 (K : DiamondParameter) (hk : 1 < K.1)
    (f : IntegerLatticeFunction) (B : Int) (z : GaussianInt) :
    let A := P5352T2Sources K hk 0
    let D := P5352T2Sources K hk 3
    let M := (P5352T2PlacementData K.1 2).2 0
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
    have subDiff {a b c d : Int} (hab : a=b) (hcd : c=d) :
        a-c = b-d := by rw [hab, hcd]
    have eastAlgebra (a b : Int) : 1-(b-a)+(b-1)=a := by ring
    have productGap (a b : Int) : (b-1)*(a-2)-(b-1)*(a-1)=-(b-1) := by ring
    have lapZeroAlgebra (a : Int) : (a-1)+(1-a)=0 := by ring
    have lapOneAlgebra (a : Int) : a+(1-a)=1 := by ring
    have endAlgebra (b : Int) := FirstPredecessorCases.endAlgebra b
    have endAlgebraB (b c : Int) := FirstPredecessorCases.endAlgebraB b c
    let k : Int := K.1
    let d : GaussianInt := ⟨k, 1-k⟩
    let r : GaussianInt := ⟨2*k, 0⟩
    let child := P5352T2Sources K hk 0
    let pred := P5352T2Sources K hk 3
    let M := (P5352T2PlacementData K.1 2).2 0
    have hchildTile : child.1 = DiamondTile K.1 := by simp [child, P5352T2Sources]
    change
      (∀ y, y ∈ FootprintVertices child.1 → f y = child.2.1 y) →
      (∀ y, y - M.1 ∈ FootprintVertices pred.1 →
        f y = pred.2.1 (y - M.1) + M.2.1.re*y.re + M.2.1.im*y.im + B) →
      z ∈ FootprintVertices child.1 → z - M.1 ∈ FootprintVertices pred.1 →
      (∀ y, y = z ∨ y = z + 1 ∨ y = z - 1 ∨
            y = z + ⟨0, 1⟩ ∨ y = z - ⟨0, 1⟩ →
        y ∈ FootprintVertices child.1 ∨ y - M.1 ∈ FootprintVertices pred.1) →
      (z - M.2.2 ∈ FootprintVertices child.1 → FourNeighborLaplacian f z = 0) ∧
      (z - M.2.2 ∉ FootprintVertices child.1 → FourNeighborLaplacian f z = 1)
    intro hchild hpred hz hpz hcover
    have hkI : 2 ≤ k := by dsimp [k]; exact_mod_cast (show 2 ≤ K.1 by omega)
    have hm : M.1 = d ∧ M.2.1 = ⟨0,k-1⟩ ∧ M.2.2 = r := by
      simp [M, d, r, P5352T2PlacementData, k]
    rcases hm with ⟨hdisp, hcoeff, hr⟩
    rw [hdisp, hcoeff] at hpred
    rw [hdisp] at hpz hcover
    rw [hr] at ⊢
    have hdchild := (P5352T2DomainRows K z).1.mp hz
    have hdpred := (P5352T2DomainRows ⟨K.1-1, by omega⟩ (z-d)).1.mp hpz
    rcases z with ⟨p,q⟩
    simp only [Int.reduceNeg, Zsqrtd.im_sub, Int.sub_nonneg, tsub_le_iff_right, Zsqrtd.re_sub,
        neg_le_sub_iff_le_add, neg_sub, neg_add_rev, neg_add_le_iff_le_add, d] at hdpred
    have hcast : (↑(K.1-1) : Int) = k-1 := by dsimp [k]; omega
    rw [hcast] at hdpred
    change (0 ≤ q ∧ q ≤ 2*k ∧ -k ≤ p ∧ p ≤ k ∧ -q-1 ≤ p ∧ p ≤ q+1 ∧
      -(2*k-q+1) ≤ p ∧ p ≤ 2*k-q+1) at hdchild
    have hpq : 1 ≤ p ∧ p ≤ k ∧ (q = p-1 ∨ q = p) := by omega
    rcases hpq with ⟨hp1,hpk,hq⟩
    have childMem (a b : Int)
        (hb0 : 0 ≤ b) (hb1 : b ≤ 2*k) (ha0 : -k ≤ a) (ha1 : a ≤ k)
        (hs0 : -b-1 ≤ a) (hs1 : a ≤ b+1)
        (ht0 : -(2*k-b+1) ≤ a) (ht1 : a ≤ 2*k-b+1) := FirstPredecessorCases.childMem K a b hb0
            hb1 ha0 ha1 hs0 hs1 ht0 ht1
    have boundaryCase (hqp : q=p) :
        ((⟨p,p⟩ : GaussianInt)-r ∈ FootprintVertices child.1 →
          FourNeighborLaplacian f ⟨p,p⟩ = 0) ∧
        ((⟨p,p⟩ : GaussianInt)-r ∉ FootprintVertices child.1 →
          FourNeighborLaplacian f ⟨p,p⟩ = 1) := FirstPredecessorCases.boundaryCase K hk f hchild
              hkI p q hz hpz hcover hdpred hcast hdchild hp1 hq childMem hqp
    let Q : Int → Int → Int := fun a b =>
      (Int.natAbs a : Int) * ((Int.natAbs a : Int)-1) / 2 - (a-b)^2/4
    have childValue (w : GaussianInt)
        (hw : w ∈ FootprintVertices (DiamondTile K.1)) := FirstPredecessorCases.childValue K hk f
            hchild w hw
    let Kp : DiamondParameter := ⟨K.1-1, by omega⟩
    have predFoot (w : GaussianInt)
        (hw : 0 ≤ w.im ∧ w.im ≤ 2*(k-1) ∧ -(k-1) ≤ w.re ∧ w.re ≤ k-1 ∧
          -w.im-1 ≤ w.re ∧ w.re ≤ w.im+1 ∧
          -(2*(k-1)-w.im+1) ≤ w.re ∧ w.re ≤ 2*(k-1)-w.im+1) := FirstPredecessorCases.predFoot K
              hk p q hcast w hw
    have predValue (w : GaussianInt)
        (hw : w ∈ FootprintVertices (DiamondTile (K.1-1))) := FirstPredecessorCases.predValue K
            hk p q hcast w hw
    have predTranslatedValue (y : GaussianInt)
        (hy : y-d ∈ FootprintVertices (DiamondTile (K.1-1))) :=
            FirstPredecessorCases.predTranslatedValue K hk f B hpred predValue y hy
    rcases hq with hq | hq
    · -- Staircase centers A_t=(t,t-1).
      clear hcover hdpred hdchild hpred boundaryCase hdisp hcoeff hr M
      let zA : GaussianInt := ⟨p,p-1⟩
      have hzA : zA ∈ FootprintVertices (DiamondTile K.1) := by
        simpa [zA, child, P5352T2Sources, hq] using hz
      have hComp := FirstPredecessorCases.hComp K hk p q hz hpz hcast hp1 hpk childMem hq hzA
      have hzEq : zA = (⟨p,p-1⟩ : GaussianInt) := rfl
      have hW : (⟨p-1,p-1⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1) :=
        childMem (p-1) (p-1) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega)
      have hN : (⟨p,p⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile K.1) :=
        childMem p p (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega)
      have hP0 : (zA-d) ∈ FootprintVertices (DiamondTile (K.1-1)) := by
        simpa [zA, pred, P5352T2Sources, hq] using hpz
      clear hpz Kp
      let valS : Int := Q (p-k) (p-1-1-(1-k))
      let valC : Int := Q (p-k) (p-1-(1-k))
      have he : (zA+1)-d = (⟨p+1-k,p+k-2⟩ : GaussianInt) := by
        ext <;> simp [d] <;> ring
      have hs : (zA-⟨0,1⟩)-d = (⟨p-k,p+k-3⟩ : GaussianInt) := by
        ext <;> simp [d] <;> ring
      have hPe := FirstPredecessorCases.hPe K hk p q hcast hp1 hpk predFoot hq
      have hPs := FirstPredecessorCases.hPs K hk p q hcast hp1 hpk predFoot hq
      let val0 : Int := Q p (p-1)
      let valW : Int := Q (p-1) (p-1)
      let valN : Int := Q p p
      have hC0 : f zA = val0 := childValue zA hzA
      have hCW := FirstPredecessorCases.hCW K f p childValue hW
      have hCN := FirstPredecessorCases.hCN K f p childValue hN
      have hPcenter := FirstPredecessorCases.hPcenter K f B p predTranslatedValue hP0
      have hPeast := FirstPredecessorCases.hPeast K f B p predTranslatedValue he hPe
      have hPsouth := FirstPredecessorCases.hPsouth K f B p predTranslatedValue hs hPs
      clear hP0 hPe hPs predValue predTranslatedValue predFoot pred hcast
        hzA hW hN hz hchild childMem childValue
      have qC0 : val0 = p*(p-1)/2 := by
        simp [val0, Q, abs_of_nonneg (show 0 ≤ p by omega)]
      have qCW := FirstPredecessorCases.qCW p q hp1 hq
      have qCN : valN = p*(p-1)/2 := by
        simp [valN, Q, abs_of_nonneg (show 0 ≤ p by omega)]
      have qCS : Q p (p-2) = p*(p-1)/2-1 := by
        simp [Q, abs_of_nonneg (show 0 ≤ p by omega)]
      have floorEven (m : Int) := FirstPredecessorCases.floorEven m
      have floorOdd (m : Int) := FirstPredecessorCases.floorOdd K f B p q m
      have qP0 := FirstPredecessorCases.qP0 K p q hpk hq floorEven
      have qPeLt (hpk' : p < k) := FirstPredecessorCases.qPeLt K p q floorOdd hpk'
      have qPeEq (hpk' : p = k) := FirstPredecessorCases.qPeEq K p floorOdd hpk'
      have qPs := FirstPredecessorCases.qPs K p q hpk hq floorOdd
      have hQdelta : valS - valC = k-1 := by
        linear_combination qPs-qP0
      have tri (a : Int) := FirstPredecessorCases.tri K f B p q a
      have tdiff (a : Int) := FirstPredecessorCases.tdiff K f B p q tri a
      have tdiffRev (a : Int) := FirstPredecessorCases.tdiffRev K f B p q tdiff a
      have hEastDiff := FirstPredecessorCases.hEastDiff K f B eastAlgebra endAlgebraB p hpk
          hPcenter hPeast qP0 qPeLt qPeEq tdiffRev
      have hWestDiff := FirstPredecessorCases.hWestDiff f subDiff p hC0 hCW qC0 qCW tdiffRev
      have hNorthDiff := FirstPredecessorCases.hNorthDiff f subDiff p hC0 hCN qC0 qCN
      have hSouthDiff := FirstPredecessorCases.hSouthDiff K f B subDiff productGap p hPcenter
          hPsouth hQdelta
      have hLapZero (hp : p=k) := FirstPredecessorCases.hLapZero K f lap_identity lapZeroAlgebra
          p hEastDiff hWestDiff hNorthDiff hSouthDiff hp
      have hLapOne (hp : p≠k) := FirstPredecessorCases.hLapOne K f lap_identity lapOneAlgebra p
          hEastDiff hWestDiff hNorthDiff hSouthDiff hp
      rw [hq]
      refine ⟨?_, ?_⟩
      · intro hc
        have hce := FirstPredecessorCases.hce K hk hchildTile p hzEq hc
        have hp : p=k := hComp.mp hce
        exact hLapZero hp
      · intro hn
        have hp := FirstPredecessorCases.hpAt505 K hk hchildTile p hComp hzEq hn
        exact hLapOne hp
    · rw [hq]
      exact boundaryCase hq
  )

end ApollonianSuperharmonic

end
