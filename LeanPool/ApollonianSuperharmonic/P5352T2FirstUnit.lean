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

-- [TABLET NODE: P5352T2FirstUnit]

/-!
# P5352T2FirstUnit

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FirstUnitProof

private theorem umem :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1),
        let U (p q : Int) : Prop := 0 ≤ p ∧ p ≤ 1 ∧ 0 ≤ q ∧ q ≤ 1
        ∀ (x : GaussianInt), x ∈ FootprintVertices (P5352T2Sources K hk (1 : Fin (4 : ℕ))).1 ↔
            U x.re x.im ) := by
  classical
  intro K hk U x
  simp only [P5352T2Sources, Matrix.cons_val_one, Matrix.cons_val_zero]
  simp [FootprintVertices]
  simp only [Zsqrtd.ext_iff, Zsqrtd.re_zero, Zsqrtd.im_zero,
    Zsqrtd.re_one, Zsqrtd.im_one, Zsqrtd.re_add, Zsqrtd.im_add]
  dsimp [U]
  omega

private theorem sqm :
    (by
      classical
      exact
        ∀ (t : ℤ), ((-1 : ℤ) - (2 : ℤ) * t) ^ (2 : ℕ) / (4 : ℤ) = t ^ (2 : ℕ) + t ) := by
  classical
  intro t
  have h := P4207T1FloorArithmetic.1 (-1) (-t)
  rw [show -1+2*(-t) = -1-2*t by ring] at h
  norm_num at h
  nlinarith only [h]

private theorem sqp :
    (by
      classical
      exact
        ∀ (t : ℤ), ((1 : ℤ) - (2 : ℤ) * t) ^ (2 : ℕ) / (4 : ℤ) = t ^ (2 : ℕ) - t ) := by
  classical
  intro t
  have h := P4207T1FloorArithmetic.1 1 (-t)
  rw [show 1+2*(-t) = 1-2*t by ring] at h
  norm_num at h
  nlinarith only [h]

private theorem triDiff :
    (by
      classical
      exact
        ∀ (t : ℤ),
          t * (t - (1 : ℤ)) / (2 : ℤ) - (t - (1 : ℤ)) * (t - (2 : ℤ)) / (2 : ℤ) =
            t - (1 : ℤ)
    ) := by
  classical
  intro t
  have he : t*(t-1) = (t-1)*(t-2)+(t-1)*2 := by ring
  omega

private theorem child :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let k : Int := K.1
        let C (p q : Int) : Prop :=
          0 ≤ q ∧ q ≤ 2*k ∧ -k ≤ p ∧ p ≤ k ∧
            -q-1 ≤ p ∧ p ≤ q+1 ∧ -(2*k-q+1) ≤ p ∧ p ≤ 2*k-q+1
        (∀ (x : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) ↔ C x.re x.im) → ((∀ y ∈
            FootprintVertices (DiamondTile K.1), f y = DiamondOdometer K y) → (∀ (p : ℤ), ∀ (q :
            ℤ), C p q → f ⟨p, q⟩ = P4207T1DiamondFormula ⟨p, q⟩)) ) := by
  classical
  intro K f k C cmem hA p q h
  rw [hA _ ((cmem _).mpr h)]
  exact (P5352T2DomainRows K _).2 ((cmem _).mpr h)

private theorem parent :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (s : Fin 4), ∀ (f :
            IntegerLatticeFunction), ∀ (B : Int),
        let U (p q : Int) : Prop := 0 ≤ p ∧ p ≤ 1 ∧ 0 ≤ q ∧ q ≤ 1
        (∀ (x : GaussianInt), x ∈ FootprintVertices (P5352T2Sources K hk 1).1 ↔ U x.re x.im) →
            ((∀ (y : GaussianInt), y - ((P5352T2PlacementData K.1 (0 : Fin (3 : ℕ))).2 s).1 ∈
            FootprintVertices (P5352T2Sources K hk (1 : Fin (4 : ℕ))).1 → f y =
            (P5352T2Sources K hk (1 : Fin (4 : ℕ))).2.1 (y - ((P5352T2PlacementData K.1 (0 :
            Fin (3 : ℕ))).2 s).1) + ((P5352T2PlacementData K.1 (0 : Fin (3 : ℕ))).2 s).2.1.re *
            y.re + ((P5352T2PlacementData K.1 (0 : Fin (3 : ℕ))).2 s).2.1.im * y.im + B) → (
        let d := ((P5352T2PlacementData K.1 0).2 s).1
        let a := ((P5352T2PlacementData K.1 0).2 s).2.1
        ∀ (p : ℤ), ∀ (q : ℤ), U (p - d.re) (q - d.im) → f ⟨p, q⟩ = (if p - d.re = (1 : ℤ) ∧ q -
            d.im = (1 : ℤ) then (1 : ℤ) else (0 : ℤ)) + a.re * p + a.im * q + B)) ) := by
  classical
  intro K hk s f B U umem hP d a p q h
  have hh := hP ⟨p,q⟩ ((umem _).mpr h)
  simpa only [P5352T2Sources, Matrix.cons_val_one, Matrix.cons_val_zero,
    CurvatureOneOdometer, Zsqrtd.ext_iff, Zsqrtd.re_add, Zsqrtd.im_add,
    Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one,
    zero_add, add_zero, d, a] using hh

private theorem covered :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (hk : (1 : ℕ) < K.1), ∀ (s : Fin 4), ∀ (z : GaussianInt),
        let k : Int := K.1
        let C (p q : Int) : Prop :=
          0 ≤ q ∧ q ≤ 2*k ∧ -k ≤ p ∧ p ≤ k ∧
            -q-1 ≤ p ∧ p ≤ q+1 ∧ -(2*k-q+1) ≤ p ∧ p ≤ 2*k-q+1
        let U (p q : Int) : Prop := 0 ≤ p ∧ p ≤ 1 ∧ 0 ≤ q ∧ q ≤ 1
        (∀ (x : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) ↔ C x.re x.im) → ((∀ (x :
            GaussianInt), x ∈ FootprintVertices (P5352T2Sources K hk 1).1 ↔ U x.re x.im) → ((∀
            (y : GaussianInt), y = z ∨ y = z + (1 : GaussianInt) ∨ y = z - (1 : GaussianInt) ∨ y
            = z + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ y = z - ⟨(0 : ℤ), (1 : ℤ)⟩ → y ∈ FootprintVertices
            (P5352T2Sources K hk (0 : Fin (4 : ℕ))).1 ∨ y - ((P5352T2PlacementData K.1 (0 :
            Fin (3 : ℕ))).2 s).1 ∈ FootprintVertices (P5352T2Sources K hk (1 : Fin (4 : ℕ))).1)
            → (
        let d := ((P5352T2PlacementData K.1 0).2 s).1
        ∀ (p : ℤ), ∀ (q : ℤ), ⟨p, q⟩ = z ∨ ⟨p, q⟩ = z + (1 : GaussianInt) ∨ ⟨p, q⟩ = z - (1 :
            GaussianInt) ∨ ⟨p, q⟩ = z + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ ⟨p, q⟩ = z - ⟨(0 : ℤ), (1 : ℤ)⟩ → C
            p q ∨ U (p - d.re) (q - d.im)))) ) := by
  classical
  intro K hk s z k C U cmem umem hcov d p q h
  rcases hcov _ h with h | h
  · exact Or.inl ((cmem _).mp h)
  · exact Or.inr ((umem _).mp h)

private theorem lap :
    (by
      classical
      exact
        ∀ (f : IntegerLatticeFunction), ∀ (p : ℤ), ∀ (q : ℤ), FourNeighborLaplacian f ⟨p, q⟩ = f
            ⟨p + (1 : ℤ), q⟩ - f ⟨p, q⟩ + (f ⟨p - (1 : ℤ), q⟩ - f ⟨p, q⟩) + (f ⟨p, q + (1 : ℤ)⟩ -
            f ⟨p, q⟩) + (f ⟨p, q - (1 : ℤ)⟩ - f ⟨p, q⟩) ) := by
  classical
  intro f p q
  rw [FourNeighborLaplacian,
    show (⟨p,q⟩ : GaussianInt)+1 = ⟨p+1,q⟩ by ext <;> simp,
    show (⟨p,q⟩ : GaussianInt)-1 = ⟨p-1,q⟩ by ext <;> simp,
    show (⟨p,q⟩ : GaussianInt)+⟨0,1⟩ = ⟨p,q+1⟩ by ext <;> simp,
    show (⟨p,q⟩ : GaussianInt)-⟨0,1⟩ = ⟨p,q-1⟩ by ext <;> simp]
  ring

private theorem hzAt199 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (z : GaussianInt),
        let k : Int := K.1
        let C (p q : Int) : Prop :=
          0 ≤ q ∧ q ≤ 2*k ∧ -k ≤ p ∧ p ≤ k ∧
            -q-1 ≤ p ∧ p ≤ q+1 ∧ -(2*k-q+1) ≤ p ∧ p ≤ 2*k-q+1
        let U (p q : Int) : Prop := 0 ≤ p ∧ p ≤ 1 ∧ 0 ≤ q ∧ q ≤ 1
        (C z.re z.im) → ((U (z.re - (0 : ℤ)) (z.im - (2 : ℤ) * k)) → ((C (z.re + (1 : ℤ)) z.im ∨
            U (z.re + (1 : ℤ) - (0 : ℤ)) (z.im - (2 : ℤ) * k)) → (z = ⟨0,2*k⟩))) ) := by
  classical
  intro K z k C U center unitCenter he
  dsimp [C, U] at center unitCenter he
  ext <;> dsimp <;> omega

private theorem hmarkAt203 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        let C (p q : Int) : Prop :=
          0 ≤ q ∧ q ≤ 2*k ∧ -k ≤ p ∧ p ≤ k ∧
            -q-1 ≤ p ∧ p ≤ q+1 ∧ -(2*k-q+1) ≤ p ∧ p ≤ 2*k-q+1
        (∀ (x : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) ↔ C x.re x.im) → (
        let r : GaussianInt := ⟨-k, k+1⟩
        (⟨0,2*k⟩ : GaussianInt) - r ∈ FootprintVertices (DiamondTile K.1))) ) := by
  classical
  intro K hk k C cmem r
  rw [cmem]
  change C (0-(-k)) (2*k-(k+1))
  dsimp [C]
  omega

private theorem hlAt223 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        let k : Int := K.1
        (∀ (p : Int), ∀ (q : Int), FourNeighborLaplacian f ⟨p,q⟩ = (f ⟨p+1,q⟩ - f ⟨p,q⟩) + (f
            ⟨p-1,q⟩ - f ⟨p,q⟩) + (f ⟨p,q+1⟩ - f ⟨p,q⟩) + (f ⟨p,q-1⟩ - f ⟨p,q⟩)) → ((f ⟨(1 : ℤ),
            (2 : ℤ) * k⟩ = -(k ^ (2 : ℕ) - k)) → ((f ⟨(0 : ℤ), (2 : ℤ) * k + (1 : ℤ)⟩ = -(k * ((2
            : ℤ) * k + (1 : ℤ))) + B) → ((f ⟨(0 : ℤ), (2 : ℤ) * k⟩ = -(k * ((2 : ℤ) * k)) + B) →
            ((f ⟨0,2*k+1⟩ - f ⟨0,2*k⟩ = -k) → ((f ⟨(-1 : ℤ), (2 : ℤ) * k⟩ = -(k ^ (2 : ℕ) + k)) →
            ((f ⟨(0 : ℤ), (2 : ℤ) * k - (1 : ℤ)⟩ = -(k ^ (2 : ℕ) - k)) → ((f ⟨(0 : ℤ), (2 : ℤ) *
            k⟩ = -k ^ (2 : ℕ)) → (FourNeighborLaplacian f ⟨0,2*k⟩ = 0)))))))) ) := by
  classical
  intro K f B k lap he hdiffN hdiffZ hn hw hs hc
  rw [lap]
  norm_num only [zero_add, zero_sub]
  omega

private theorem hzAt234 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (z : GaussianInt),
        let k : Int := K.1
        let C (p q : Int) : Prop :=
          0 ≤ q ∧ q ≤ 2*k ∧ -k ≤ p ∧ p ≤ k ∧
            -q-1 ≤ p ∧ p ≤ q+1 ∧ -(2*k-q+1) ≤ p ∧ p ≤ 2*k-q+1
        let U (p q : Int) : Prop := 0 ≤ p ∧ p ≤ 1 ∧ 0 ≤ q ∧ q ≤ 1
        (C z.re z.im) → ((U (z.re - (-k - (1 : ℤ))) (z.im - k)) → ((C z.re (z.im + (1 : ℤ)) ∨ U
            (z.re - (-k - (1 : ℤ))) (z.im + (1 : ℤ) - k)) → (z = ⟨-k,k⟩))) ) := by
  classical
  intro K z k C U center unitCenter hn
  dsimp [C, U] at center unitCenter hn
  ext <;> dsimp <;> omega

private theorem hmarkAt238 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let k : Int := K.1
        let C (p q : Int) : Prop :=
          0 ≤ q ∧ q ≤ 2*k ∧ -k ≤ p ∧ p ≤ k ∧
            -q-1 ≤ p ∧ p ≤ q+1 ∧ -(2*k-q+1) ≤ p ∧ p ≤ 2*k-q+1
        (∀ (x : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) ↔ C x.re x.im) → (
        let r : GaussianInt := ⟨-k, k+1⟩
        (⟨-k,k⟩ : GaussianInt) - r ∉ FootprintVertices (DiamondTile K.1)) ) := by
  classical
  intro K k C cmem r
  rw [cmem]
  change ¬ C (-k-(-k)) (k-(k+1))
  dsimp [C]
  omega

private theorem haAt253 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
          (1 : ℕ) < K.1 →
            let k : Int := K.1;
            (Int.natAbs (1 - k) : Int) = k - 1
    ) := by
  classical
  intro K hk k
  rw [Int.natCast_natAbs, abs_of_nonpos (by omega : 1-k ≤ 0)]
  omega

private theorem hbAt256 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
          (1 : ℕ) < K.1 →
            let k : Int := K.1;
            (Int.natAbs (1 - k) : Int) = k - 1 → (Int.natAbs (-k) : Int) = k
    ) := by
  classical
  intro K hk k ha
  rw [Int.natCast_natAbs, abs_of_nonpos (by omega : -k ≤ 0)]
  omega

private theorem hzAt275 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (z : GaussianInt),
        let k : Int := K.1
        let C (p q : Int) : Prop :=
          0 ≤ q ∧ q ≤ 2*k ∧ -k ≤ p ∧ p ≤ k ∧
            -q-1 ≤ p ∧ p ≤ q+1 ∧ -(2*k-q+1) ≤ p ∧ p ≤ 2*k-q+1
        let U (p q : Int) : Prop := 0 ≤ p ∧ p ≤ 1 ∧ 0 ≤ q ∧ q ≤ 1
        (C z.re z.im) → ((U (z.re - (-1 : ℤ)) (z.im - (-1 : ℤ))) → ((C (z.re - (1 : ℤ)) z.im ∨ U
            (z.re - (1 : ℤ) - (-1 : ℤ)) (z.im - (-1 : ℤ))) → (z = ⟨0,0⟩))) ) := by
  classical
  intro K z k C U center unitCenter hw
  dsimp [C, U] at center unitCenter hw
  ext <;> dsimp <;> omega

private theorem hmarkAt279 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ((1 : ℕ) < K.1) → (
        let k : Int := K.1
        let C (p q : Int) : Prop :=
          0 ≤ q ∧ q ≤ 2*k ∧ -k ≤ p ∧ p ≤ k ∧
            -q-1 ≤ p ∧ p ≤ q+1 ∧ -(2*k-q+1) ≤ p ∧ p ≤ 2*k-q+1
        (∀ (x : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) ↔ C x.re x.im) → (
        let r : GaussianInt := ⟨k, -k-1⟩
        (⟨0,0⟩ : GaussianInt) - r ∈ FootprintVertices (DiamondTile K.1))) ) := by
  classical
  intro K hk k C cmem r
  rw [cmem]
  change C (0-k) (0-(-k-1))
  dsimp [C]
  omega

private theorem hlAt294 :
    (by
      classical
      exact
        (∀ (f : IntegerLatticeFunction), ∀ (B : Int), (∀ (p : Int), ∀ (q :
            Int), FourNeighborLaplacian f ⟨p,q⟩ = (f ⟨p+1,q⟩ - f ⟨p,q⟩) + (f ⟨p-1,q⟩ - f ⟨p,q⟩) +
            (f ⟨p,q+1⟩ - f ⟨p,q⟩) + (f ⟨p,q-1⟩ - f ⟨p,q⟩)) → ((f ⟨(-1 : ℤ), (0 : ℤ)⟩ = (0 : ℤ)) →
            ((f ⟨(0 : ℤ), (-1 : ℤ)⟩ = (1 : ℤ) + B) → ((f ⟨(0 : ℤ), (0 : ℤ)⟩ = (1 : ℤ) + B) → ((f
            ⟨(1 : ℤ), (0 : ℤ)⟩ = (0 : ℤ)) → ((f ⟨(0 : ℤ), (1 : ℤ)⟩ = (0 : ℤ)) → ((f ⟨(0 : ℤ), (0
            : ℤ)⟩ = (0 : ℤ)) → (FourNeighborLaplacian f ⟨0,0⟩ = 0)))))))) ) := by
  classical
  intro f B lap hw hdiffS hdiffZ he hn hc
  rw [lap]
  norm_num only [zero_add, zero_sub]
  omega

private theorem hzAt305 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (z : GaussianInt),
        let k : Int := K.1
        let C (p q : Int) : Prop :=
          0 ≤ q ∧ q ≤ 2*k ∧ -k ≤ p ∧ p ≤ k ∧
            -q-1 ≤ p ∧ p ≤ q+1 ∧ -(2*k-q+1) ≤ p ∧ p ≤ 2*k-q+1
        let U (p q : Int) : Prop := 0 ≤ p ∧ p ≤ 1 ∧ 0 ≤ q ∧ q ≤ 1
        (C z.re z.im) → ((U (z.re - k) (z.im - (k - (1 : ℤ)))) → ((C z.re (z.im - (1 : ℤ)) ∨ U
            (z.re - k) (z.im - (1 : ℤ) - (k - (1 : ℤ)))) → (z = ⟨k,k⟩))) ) := by
  classical
  intro K z k C U center unitCenter hs
  dsimp [C, U] at center unitCenter hs
  ext <;> dsimp <;> omega

private theorem hmarkAt309 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let k : Int := K.1
        let C (p q : Int) : Prop :=
          0 ≤ q ∧ q ≤ 2*k ∧ -k ≤ p ∧ p ≤ k ∧
            -q-1 ≤ p ∧ p ≤ q+1 ∧ -(2*k-q+1) ≤ p ∧ p ≤ 2*k-q+1
        (∀ (x : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) ↔ C x.re x.im) → (
        let r : GaussianInt := ⟨k, -k-1⟩
        (⟨k,k⟩ : GaussianInt) - r ∉ FootprintVertices (DiamondTile K.1)) ) := by
  classical
  intro K k C cmem r
  rw [cmem]
  change ¬ C (k-k) (k-(-k-1))
  dsimp [C]
  omega

end FirstUnitProof

theorem P5352T2FirstUnit (K : DiamondParameter) (hk : 1 < K.1)
    (s : Fin 4) (f : IntegerLatticeFunction) (B : Int) (z : GaussianInt) :
    let A := P5352T2Sources K hk 0
    let D := P5352T2Sources K hk 1
    let M := (P5352T2PlacementData K.1 0).2 s
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
      x ∈ FootprintVertices (P5352T2Sources K hk 1).1 ↔ U x.re x.im := FirstUnitProof.umem K hk x
  have sq0 (t : Int) : (2*t)^2/4 = t^2 := by
    simpa using (P4207T1FloorArithmetic.1 0 t)
  have sqm (t : Int) : (-1-2*t)^2/4 = t^2+t := FirstUnitProof.sqm t
  have sqp (t : Int) : (1-2*t)^2/4 = t^2-t := FirstUnitProof.sqp t
  have triDiff (t : Int) :
      t*(t-1)/2 - (t-1)*(t-2)/2 = t-1 := FirstUnitProof.triDiff t
  dsimp only
  intro hA hP hzA hzP hcov
  change ∀ y, y ∈ FootprintVertices (DiamondTile K.1) →
    f y = DiamondOdometer K y at hA
  have child (p q : Int) (h : C p q) :
      f ⟨p,q⟩ = P4207T1DiamondFormula ⟨p,q⟩ := FirstUnitProof.child K f cmem hA p q h
  have center := (cmem z).mp hzA
  have unitCenter := (umem _).mp hzP
  let d := ((P5352T2PlacementData K.1 0).2 s).1
  let a := ((P5352T2PlacementData K.1 0).2 s).2.1
  let r := ((P5352T2PlacementData K.1 0).2 s).2.2
  have parent (p q : Int) (h : U (p-d.re) (q-d.im)) :
      f ⟨p,q⟩ = (if p-d.re = 1 ∧ q-d.im = 1 then 1 else 0) +
        a.re*p + a.im*q + B := FirstUnitProof.parent K hk s f B umem hP p q h
  have covered (p q : Int)
      (h : (⟨p,q⟩ : GaussianInt) = z ∨ ⟨p,q⟩ = z+1 ∨ ⟨p,q⟩ = z-1 ∨
        ⟨p,q⟩ = z+⟨0,1⟩ ∨ ⟨p,q⟩ = z-⟨0,1⟩) :
      C p q ∨ U (p-d.re) (q-d.im) := FirstUnitProof.covered K hk s z cmem umem hcov p q h
  have lap (p q : Int) : FourNeighborLaplacian f ⟨p,q⟩ =
      (f ⟨p+1,q⟩ - f ⟨p,q⟩) + (f ⟨p-1,q⟩ - f ⟨p,q⟩) +
      (f ⟨p,q+1⟩ - f ⟨p,q⟩) + (f ⟨p,q-1⟩ - f ⟨p,q⟩) := FirstUnitProof.lap f p q
  clear hA hP hzA hzP hcov umem
  fin_cases s
  · have he := covered (z.re+1) z.im (Or.inr (Or.inl (by ext <;> simp)))
    change U (z.re-0) (z.im-2*k) at unitCenter
    change C (z.re+1) z.im ∨ U (z.re+1-0) (z.im-2*k) at he
    change ∀ p q, U (p-0) (q-2*k) →
      f ⟨p,q⟩ = (if p-0=1 ∧ q-2*k=1 then 1 else 0) + k*p + (-k)*q + B at parent
    have hz : z = ⟨0,2*k⟩ := FirstUnitProof.hzAt199 K z center unitCenter he
    subst z
    have hmark : (⟨0,2*k⟩ : GaussianInt) - r ∈
        FootprintVertices (DiamondTile K.1) := FirstUnitProof.hmarkAt203 K hk cmem
    have hdiffN := parent 0 (2*k+1) (by dsimp [U]; omega)
    have hdiffZ := parent 0 (2*k) (by dsimp [U]; omega)
    norm_num at hdiffN hdiffZ
    have hn : f ⟨0,2*k+1⟩ - f ⟨0,2*k⟩ = -k := by
      nlinarith only [hdiffN, hdiffZ]
    have he := child 1 (2*k) (by dsimp [C]; omega)
    have hw := child (-1) (2*k) (by dsimp [C]; omega)
    have hs := child 0 (2*k-1) (by dsimp [C]; omega)
    have hc := child 0 (2*k) (by dsimp [C]; omega)
    norm_num [P4207T1DiamondFormula] at he hw hs hc
    rw [sqp] at he
    rw [sqm] at hw
    rw [sqp] at hs
    rw [sq0] at hc
    have hl : FourNeighborLaplacian f ⟨0,2*k⟩ = 0 := FirstUnitProof.hlAt223 K f B lap he hdiffN
        hdiffZ hn hw hs hc
    exact ⟨fun _ => hl, fun h => False.elim (h hmark)⟩
  · have hn := covered z.re (z.im+1)
      (Or.inr (Or.inr (Or.inr (Or.inl (by ext <;> simp)))))
    change U (z.re-(-k-1)) (z.im-k) at unitCenter
    change C z.re (z.im+1) ∨ U (z.re-(-k-1)) (z.im+1-k) at hn
    change ∀ p q, U (p-(-k-1)) (q-k) →
      f ⟨p,q⟩ = (if p-(-k-1)=1 ∧ q-k=1 then 1 else 0) + 0*p + (-k-1)*q + B at parent
    have hz : z = ⟨-k,k⟩ := FirstUnitProof.hzAt234 K z center unitCenter hn
    subst z
    have hmark : (⟨-k,k⟩ : GaussianInt) - r ∉
        FootprintVertices (DiamondTile K.1) := FirstUnitProof.hmarkAt238 K cmem
    have hdiffW := parent (-k-1) k (by dsimp [U]; omega)
    have hdiffZ := parent (-k) k (by dsimp [U]; omega)
    norm_num at hdiffW hdiffZ
    have hw : f ⟨-k-1,k⟩ - f ⟨-k,k⟩ = 0 := by
      omega
    have he := child (1-k) k (by dsimp [C]; omega)
    have hn := child (-k) (k+1) (by dsimp [C]; omega)
    have hs := child (-k) (k-1) (by dsimp [C]; omega)
    have hc := child (-k) k (by dsimp [C]; omega)
    have ha : (Int.natAbs (1-k) : Int) = k-1 := FirstUnitProof.haAt253 K hk
    have hb : (Int.natAbs (-k) : Int) = k := FirstUnitProof.hbAt256 K hk ha
    simp only [P4207T1DiamondFormula, ha, hb] at he hn hs hc
    rw [show 1-k-k = 1-2*k by ring, show k-1-1 = k-2 by ring, sqp] at he
    rw [show -k-(k+1) = -1-2*k by ring, sqm] at hn
    rw [show -k-(k-1) = 1-2*k by ring, sqp] at hs
    rw [show -k-k = -(2*k) by ring, neg_sq, sq0] at hc
    have ht := triDiff k
    have hl : FourNeighborLaplacian f ⟨-k,k⟩ = 1 := (show
        FourNeighborLaplacian f ⟨-k,k⟩ = 1
      from by
        classical
        rw [lap, show -k+1 = 1-k by ring]
        omega)
    exact ⟨fun h => False.elim (hmark h), fun _ => hl⟩
  · have hw := covered (z.re-1) z.im
      (Or.inr (Or.inr (Or.inl (by ext <;> simp))))
    change U (z.re-(-1)) (z.im-(-1)) at unitCenter
    change C (z.re-1) z.im ∨ U (z.re-1-(-1)) (z.im-(-1)) at hw
    change ∀ p q, U (p-(-1)) (q-(-1)) →
      f ⟨p,q⟩ = (if p-(-1)=1 ∧ q-(-1)=1 then 1 else 0) + (-1)*p + (-1)*q + B at parent
    have hz : z = ⟨0,0⟩ := FirstUnitProof.hzAt275 K z center unitCenter hw
    subst z
    have hmark : (⟨0,0⟩ : GaussianInt) - r ∈
        FootprintVertices (DiamondTile K.1) := FirstUnitProof.hmarkAt279 K hk cmem
    have hdiffS := parent 0 (-1) (by dsimp [U]; omega)
    have hdiffZ := parent 0 0 (by dsimp [U]; omega)
    norm_num at hdiffS hdiffZ
    have hs : f ⟨0,-1⟩ - f ⟨0,0⟩ = 0 := by omega
    have he := child 1 0 (by dsimp [C]; omega)
    have hw := child (-1) 0 (by dsimp [C]; omega)
    have hn := child 0 1 (by dsimp [C]; omega)
    have hc := child 0 0 (by dsimp [C]; omega)
    norm_num [P4207T1DiamondFormula] at he hw hn hc
    have hl : FourNeighborLaplacian f ⟨0,0⟩ = 0 := FirstUnitProof.hlAt294 f B lap hw hdiffS
        hdiffZ he hn hc
    exact ⟨fun _ => hl, fun h => False.elim (h hmark)⟩
  · have hs := covered z.re (z.im-1)
      (Or.inr (Or.inr (Or.inr (Or.inr (by ext <;> simp)))))
    change U (z.re-k) (z.im-(k-1)) at unitCenter
    change C z.re (z.im-1) ∨ U (z.re-k) (z.im-1-(k-1)) at hs
    change ∀ p q, U (p-k) (q-(k-1)) →
      f ⟨p,q⟩ = (if p-k=1 ∧ q-(k-1)=1 then 1 else 0) + (k-1)*p + 0*q + B at parent
    have hz : z = ⟨k,k⟩ := FirstUnitProof.hzAt305 K z center unitCenter hs
    subst z
    have hmark : (⟨k,k⟩ : GaussianInt) - r ∉
        FootprintVertices (DiamondTile K.1) := FirstUnitProof.hmarkAt309 K cmem
    have hdiffE := parent (k+1) k (by dsimp [U]; omega)
    have hdiffZ := parent k k (by dsimp [U]; omega)
    norm_num at hdiffE hdiffZ
    have he : f ⟨k+1,k⟩ - f ⟨k,k⟩ = k := by
      nlinarith only [hdiffE, hdiffZ]
    have hw := child (k-1) k (by dsimp [C]; omega)
    have hn := child k (k+1) (by dsimp [C]; omega)
    have hs := child k (k-1) (by dsimp [C]; omega)
    have hc := child k k (by dsimp [C]; omega)
    have ha : (Int.natAbs (k-1) : Int) = k-1 := by
      rw [Int.natCast_natAbs, abs_of_nonneg (by omega : 0 ≤ k-1)]
    have hb : (Int.natAbs k : Int) = k := by
      rw [Int.natCast_natAbs, abs_of_nonneg (by omega : 0 ≤ k)]
    norm_num [P4207T1DiamondFormula, ha, hb] at hw hn hs hc
    rw [show k-1-1 = k-2 by ring] at hw
    have ht := triDiff k
    have hl : FourNeighborLaplacian f ⟨k,k⟩ = 1 := (show
        FourNeighborLaplacian f ⟨k,k⟩ = 1
      from by
        classical
        rw [lap]
        omega)
    exact ⟨fun h => False.elim (hmark h), fun _ => hl⟩

end ApollonianSuperharmonic

end
