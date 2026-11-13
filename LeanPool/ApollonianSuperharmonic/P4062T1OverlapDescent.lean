/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacianProperties
public import LeanPool.ApollonianSuperharmonic.FordInteriorSquareCoordinates

public import LeanPool.ApollonianSuperharmonic.FordOdometer
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian
public import LeanPool.ApollonianSuperharmonic.P4062T1RecursiveInteriors
public import Mathlib.RingTheory.Int.Basic

-- [TABLET NODE: P4062T1OverlapDescent]

/-!
# P4062T1OverlapDescent

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace OverlapDescentDetails


private theorem hcrossdet :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), P.p₁ * (P.q₂ : Int) - P.p₂ * (P.q₁ : Int) = 1 ) := by
  classical
  intro P
  have hd := P.det₁
  have hsumI : (P.q : Int) = P.q₁ + P.q₂ := by exact_mod_cast P.sum_q
  rw [hsumI, P.sum_p] at hd
  nlinarith only [hd]

private theorem hpos₁ :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (P₁ : FordFareyParameter),
            (2 : ℕ) < P.q → P₁.q = P.q₁ → P.q = P.q₁ + P.q₂ → 0 < P.q₁
    ) := by
  classical
  intro P P₁ hP hq₁ hsum
  by_contra hn
  have hz : P.q₁ = 0 := by omega
  have hd : (P.q : Int) ∣ (1 : Int) := by
    refine ⟨P.p₁, ?_⟩
    have h := P.det₁
    rw [hz] at h
    have hm : P.p₁ * (P.q : Int) = 1 := by simpa using h
    calc 1 = P.p₁ * (P.q : Int) := hm.symm
      _ = (P.q : Int) * P.p₁ := by ring
  have hq : 2 < (P.q : Int) := by exact_mod_cast hP
  have hl := Int.le_of_dvd (by norm_num : (0 : Int) < 1) hd
  omega

private theorem hred₁ :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (P.p₁ * (P.q₂ : Int) - P.p₂ * (P.q₁ : Int) = 1) →
            (Nat.Coprime P.q₁ P.p₁.natAbs ∧ Nat.Coprime P.q₂ P.p₂.natAbs) ) := by
  classical
  intro P hcrossdet
  have h₁ : IsCoprime (P.q₁ : Int) P.p₁ :=
    ⟨-P.p₂, (P.q₂ : Int), by nlinarith only [hcrossdet]⟩
  have h₂ : IsCoprime (P.q₂ : Int) P.p₂ :=
    ⟨P.p₁, -(P.q₁ : Int), by nlinarith only [hcrossdet]⟩
  exact ⟨by simpa using Int.isCoprime_iff_nat_coprime.mp h₁,
    by simpa using Int.isCoprime_iff_nat_coprime.mp h₂⟩

private theorem hrec₀' :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (P₁ : FordFareyParameter), (∀ x ∈
            FordRecursiveVertexDomains P (0 : Fin (4 : ℕ)), Classical.choose
            FordOdometerFamilyExistsUnique P x = Classical.choose FordOdometerFamilyExistsUnique
            P₁ x) → (∀ x, x ∈ FordRecursiveVertexDomains P 0 → FordOdometer P x = FordOdometer P₁
            x) ) := by
  classical
  intro P P₁ hrec₀ x hx
  simpa [FordOdometer] using hrec₀ x hx

private theorem hrec₁' :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (P₁ : FordFareyParameter), (∀ x ∈
            FordRecursiveVertexDomains P (1 : Fin (4 : ℕ)), Classical.choose
            FordOdometerFamilyExistsUnique P x = Classical.choose FordOdometerFamilyExistsUnique
            P₁ (x - ⟨(↑P.q₂ : ℤ), (↑P.q₂ : ℤ)⟩) + P.p₂ * x.re + P.p₂ * x.im - P.p₂ * (↑P.q₂ : ℤ)
            + (1 : ℤ)) → (∀ x, x ∈ FordRecursiveVertexDomains P 1 → FordOdometer P x =
            FordOdometer P₁ (x - ⟨(P.q₂ : Int), (P.q₂ : Int)⟩) + P.p₂ * x.re + P.p₂ * x.im - P.p₂
            * (P.q₂ : Int) + 1) ) := by
  classical
  intro P P₁ hrec₁ x hx
  simpa [FordOdometer] using hrec₁ x hx

private theorem hrec₂' :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (P₂ : FordFareyParameter), (∀ x ∈
            FordRecursiveVertexDomains P (2 : Fin (4 : ℕ)), Classical.choose
            FordOdometerFamilyExistsUnique P x = Classical.choose FordOdometerFamilyExistsUnique
            P₂ (x - ⟨(↑P.q₁ : ℤ), (0 : ℤ)⟩) + P.p₁ * x.im) → (∀ x, x ∈ FordRecursiveVertexDomains
            P 2 → FordOdometer P x = FordOdometer P₂ (x - ⟨(P.q₁ : Int), 0⟩) + P.p₁ * x.im) ) := by
  classical
  intro P P₂ hrec₂ x hx
  simpa [FordOdometer] using hrec₂ x hx

private theorem hrec₃' :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (P₂ : FordFareyParameter), (∀ x ∈
            FordRecursiveVertexDomains P (3 : Fin (4 : ℕ)), Classical.choose
            FordOdometerFamilyExistsUnique P x = Classical.choose FordOdometerFamilyExistsUnique
            P₂ (x - ⟨(0 : ℤ), (↑P.q₁ : ℤ)⟩) + P.p₁ * x.re) → (∀ x, x ∈ FordRecursiveVertexDomains
            P 3 → FordOdometer P x = FordOdometer P₂ (x - ⟨0, (P.q₁ : Int)⟩) + P.p₁ * x.re) ) := by
  classical
  intro P P₂ hrec₃ x hx
  simpa [FordOdometer] using hrec₃ x hx

private theorem hrec0Member :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (z : GaussianInt), (0 : ℤ) ≤ z.re → z.re ≤ (↑P.q₁ : ℤ) → (0
            : ℤ) ≤ z.im → z.im ≤ (↑P.q₁ : ℤ) → z ∈ FordRecursiveVertexDomains P (0 : Fin (4 : ℕ))
            ) := by
  classical
  intro P z a b c d
  change 0 ≤ z.re ∧ z.re ≤ (P.q₁ : Int) ∧
    0 ≤ z.im ∧ z.im ≤ (P.q₁ : Int)
  exact ⟨a, b, c, d⟩

private theorem hrec1Member :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (z : GaussianInt), (↑P.q₂ : ℤ) ≤ z.re → z.re ≤ (↑P.q : ℤ) →
            (↑P.q₂ : ℤ) ≤ z.im → z.im ≤ (↑P.q : ℤ) → z ∈ FordRecursiveVertexDomains P (1 : Fin (4
            : ℕ)) ) := by
  classical
  intro P z a b c d
  change (P.q₂ : Int) ≤ z.re ∧ z.re ≤ (P.q : Int) ∧
    (P.q₂ : Int) ≤ z.im ∧ z.im ≤ (P.q : Int)
  exact ⟨a, b, c, d⟩

private theorem hrec2Member :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (z : GaussianInt), (↑P.q₁ : ℤ) ≤ z.re → z.re ≤ (↑P.q : ℤ) →
            (0 : ℤ) ≤ z.im → z.im ≤ (↑P.q₂ : ℤ) → z ∈ FordRecursiveVertexDomains P (2 : Fin (4 :
            ℕ)) ) := by
  classical
  intro P z a b c d
  change (P.q₁ : Int) ≤ z.re ∧ z.re ≤ (P.q : Int) ∧
    0 ≤ z.im ∧ z.im ≤ (P.q₂ : Int)
  exact ⟨a, b, c, d⟩

private theorem hrec3Member :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (z : GaussianInt), (0 : ℤ) ≤ z.re → z.re ≤ (↑P.q₂ : ℤ) →
            (↑P.q₁ : ℤ) ≤ z.im → z.im ≤ (↑P.q : ℤ) → z ∈ FordRecursiveVertexDomains P (3 : Fin (4
            : ℕ)) ) := by
  classical
  intro P z a b c d
  change 0 ≤ z.re ∧ z.re ≤ (P.q₂ : Int) ∧
    (P.q₁ : Int) ≤ z.im ∧ z.im ≤ (P.q : Int)
  exact ⟨a, b, c, d⟩

private theorem hdetdiffAt260 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          P.p₁ * (P.q₂ : Int) - P.p₂ * (P.q₁ : Int) = 1 →
            P.q₂ < P.q₁ →
              (P.p₁ - P.p₂) * (P.q₁ : Int) - ((P.q₁ - P.q₂ : Nat) : Int) * P.p₁ = 1
    ) := by
  classical
  intro P hcrossdet horder
  rw [Nat.cast_sub (by omega : P.q₂ ≤ P.q₁)]
  nlinarith only [hcrossdet]

private theorem hcopAt264 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          P.p₁ * (P.q₂ : Int) - P.p₂ * (P.q₁ : Int) = 1 →
            P.q₂ < P.q₁ → Nat.Coprime (P.q₁ - P.q₂) (P.p₁ - P.p₂).natAbs
    ) := by
  classical
  intro P hcrossdet horder
  have hc : IsCoprime ((P.q₁-P.q₂ : Nat) : Int) (P.p₁-P.p₂) := by
    have hx : (P.p₁-P.p₂) * (P.q₂ : Int) -
        P.p₂ * ((P.q₁-P.q₂ : Nat) : Int) = 1 := by
      rw [Nat.cast_sub (by omega : P.q₂ ≤ P.q₁)]
      nlinarith only [hcrossdet]
    exact ⟨-P.p₂, P.q₂, by nlinarith only [hx]⟩
  simpa using Int.isCoprime_iff_nat_coprime.mp hc

private theorem hparAt293 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        (
        (∀ (hP : (2 :
            ℕ) < P.q), ∀ (hsum : P.q = P.q₁ + P.q₂), ∀ (hcrossdet : P.p₁ * (P.q₂ :
            Int) - P.p₂ * (P.q₁ : Int) = 1), ∀ (hpos₁ : 0 < P.q₁), ∀ (hpos₂ : 0 < P.q₂), ∀
                (horder : P.q₂ < P.q₁), ∀ (hdlt : P.q₁ - P.q₂ < P.q), ∀ (hdetdiff : (P.p₁-P.p₂) *
            (P.q₁ : Int) - ((P.q₁-P.q₂ : Nat) : Int) * P.p₁ = 1), ∀ (H : FordFareyParameter), ∀
                (hHq : H.q = P.q₁ - P.q₂), ∀ (hredParent : Nat.Coprime P.q₁ P.p₁.natAbs),
        let Q : FordFareyParameter := by
          have hdet₂ : P.p₂ * (P.q₁ : Int) -
              (P.q₂ : Int) * P.p₁ = -1 := by nlinarith only [hcrossdet]
          refine FordFareyParameter.mk P.p₁ P.q₁ hpos₁ hredParent
            (P.p₁-P.p₂) (P.q₁-P.q₂) P.p₂ P.q₂ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · ring
          · omega
          · exact hdetdiff
          · exact hdet₂
          · omega
          · exact hpos₂
          · intro hu
            have : P.q₁ = 1 := by simpa using hu
            omega;
        Q.p₁ = P.p₁-P.p₂ ∧ Q.q₁ = P.q₁-P.q₂ ∧ Q.p₂ = P.p₂ ∧ Q.q₂ = P.q₂))) := by
  classical
  intro P hP hsum hcrossdet hpos₁ hpos₂ horder hdlt hdetdiff H hHq hredParent Q
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem hch₀' :
    (by
      classical
      exact
        ∀ (P₁ : FordFareyParameter), ∀ (H : FordFareyParameter), (∀ x ∈
            FordRecursiveVertexDomains P₁ (0 : Fin (4 : ℕ)), Classical.choose
            FordOdometerFamilyExistsUnique P₁ x = Classical.choose FordOdometerFamilyExistsUnique
            H x) → (∀ y, y ∈ FordRecursiveVertexDomains P₁ 0 → FordOdometer P₁ y = FordOdometer H
            y) ) := by
  classical
  intro P₁ H hch₀ y hy
  simpa [FordOdometer] using hch₀ y hy

private theorem hch₁' :
    (by
      classical
      exact
        ∀ (P₁ : FordFareyParameter), ∀ (H : FordFareyParameter), (∀ x ∈
            FordRecursiveVertexDomains P₁ (1 : Fin (4 : ℕ)), Classical.choose
            FordOdometerFamilyExistsUnique P₁ x = Classical.choose FordOdometerFamilyExistsUnique
            H (x - ⟨(↑P₁.q₂ : ℤ), (↑P₁.q₂ : ℤ)⟩) + P₁.p₂ * x.re + P₁.p₂ * x.im - P₁.p₂ * (↑P₁.q₂
            : ℤ) + (1 : ℤ)) → (∀ z, z ∈ FordRecursiveVertexDomains P₁ 1 → FordOdometer P₁ z =
            FordOdometer H (z-⟨(P₁.q₂ : Int), (P₁.q₂ : Int)⟩) + P₁.p₂*z.re + P₁.p₂*z.im -
            P₁.p₂*(P₁.q₂ : Int)+1) ) := by
  classical
  intro P₁ H hch₁ z hz
  simpa [FordOdometer] using hch₁ z hz

private theorem hcoordsAt312 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          (∀ (q : Nat),
              ∀ (x : GaussianInt),
                x ∈ P4062T1InteriorSquare q ↔
                  1 ≤ x.re ∧ x.re ≤ (q : Int) - 1 ∧ 1 ≤ x.im ∧ x.im ≤ (q : Int) - 1) →
            ∀ (hr : Fin (4 : ℕ) → Finset GaussianInt),
              hr 0 = P4062T1InteriorSquare P.q₁ →
                (hr 1 =
                    (P4062T1InteriorSquare P.q₁).image fun y =>
                      y + ⟨(P.q₂ : Int), (P.q₂ : Int)⟩) →
                  FordFareyParameter →
                    ∀ x ∈ hr (0 : Fin (4 : ℕ)) ∩ hr (1 : Fin (4 : ℕ)),
                      (↑P.q₂ : ℤ) + (1 : ℤ) ≤ x.re ∧
                        x.re ≤ (↑P.q₁ : ℤ) - (1 : ℤ) ∧
                          (↑P.q₂ : ℤ) + (1 : ℤ) ≤ x.im ∧ x.im ≤ (↑P.q₁ : ℤ) - (1 : ℤ)
    ) := by
  classical
  intro P squareCoordinates hr hA0 hA1 H x hx
  rcases Finset.mem_inter.mp hx with ⟨h0,h1⟩
  rw [hA0] at h0
  have b0 := (squareCoordinates P.q₁ x).mp h0
  rw [hA1] at h1
  obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp h1
  have by' := (squareCoordinates P.q₁ y).mp hy
  have hxy' : x = y + ⟨(P.q₂ : Int), (P.q₂ : Int)⟩ := hxy.symm
  rcases b0 with ⟨b0r,b0r',b0i,b0i'⟩
  rcases by' with ⟨byr,byr',byi,byi'⟩
  subst x
  simp only [Zsqrtd.re_add, Zsqrtd.im_add]
  exact ⟨by omega, by omega, by omega, by omega⟩

private theorem htargetAt327 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (P₁ : FordFareyParameter),
                                                                                        (
                     ((P₁.q = P.q₁) → (∀ (hsum : P.q = P.q₁ + P.q₂), ∀ (hcrossdet : P.p₁ * (P.q₂
            : Int) - P.p₂ * (P.q₁ : Int) = 1), ∀ (hpos₁ : 0 < P.q₁), ∀ (hpos₂ : 0 < P.q₂), (∀ x,
            x ∈ FordRecursiveVertexDomains P 0 →
            FordOdometer P x = FordOdometer P₁ x) → ((∀ x, x ∈
            FordRecursiveVertexDomains P 1 → FordOdometer P x = FordOdometer P₁ (x - ⟨(P.q₂ :
            Int), (P.q₂ : Int)⟩) + P.p₂ * x.re + P.p₂ * x.im - P.p₂ * (P.q₂ : Int) + 1) → ((∀ (f
                : GaussianInt → Int), ∀ (f' : GaussianInt → Int), ∀ (x : GaussianInt), ∀ (t :
                GaussianInt), ∀ (A : Int), ∀ (B : Int), ∀ (C : Int), (f x = f'
            (x - t) + A * x.re + B * x.im + C) → ((f (x - 1) = f' ((x - t) - 1) + A * (x - 1).re
            + B * (x - 1).im + C) → ((f (x + 1) = f' ((x - t) + 1) + A * (x + 1).re + B * (x +
            1).im + C) → ((f (x - ⟨0, 1⟩) = f' ((x - t) - ⟨0, 1⟩) + A * (x - ⟨0, 1⟩).re + B * (x
            - ⟨0, 1⟩).im + C) → ((f (x + ⟨0, 1⟩) = f' ((x - t) + ⟨0, 1⟩) + A * (x + ⟨0, 1⟩).re +
            B * (x + ⟨0, 1⟩).im + C) → (FourNeighborLaplacian f x = FourNeighborLaplacian f' (x -
            t))))))) → ((∀ (z : GaussianInt), (0 ≤ z.re) → ((z.re ≤ (P.q₁ : Int)) →
            ((0 ≤ z.im) → ((z.im ≤ (P.q₁ : Int)) → (z ∈ FordRecursiveVertexDomains P 0))))) → ((∀
                (z : GaussianInt), ((P.q₂ : Int) ≤ z.re) → ((z.re ≤ (P.q : Int)) →
            (((P.q₂ : Int) ≤ z.im) → ((z.im ≤ (P.q : Int)) → (z ∈ FordRecursiveVertexDomains P
            1))))) → (∀ (hr : Fin (4 : ℕ) → Finset GaussianInt), ∀ (horder : P.q₂ < P.q₁), ∀
                (hdlt : P.q₁ - P.q₂ < P.q), ∀ (hdetdiff : (P.p₁-P.p₂) * (P.q₁ : Int) -
                ((P.q₁-P.q₂ : Nat) :
            Int) * P.p₁ = 1), ∀ (H : FordFareyParameter), ∀ (hHq : H.q = P.q₁ - P.q₂), ∀
                (hredParent : Nat.Coprime P.q₁ P.p₁.natAbs),
        let Q : FordFareyParameter := by
          have hdet₂ : P.p₂ * (P.q₁ : Int) -
              (P.q₂ : Int) * P.p₁ = -1 := by nlinarith only [hcrossdet]
          refine FordFareyParameter.mk P.p₁ P.q₁ hpos₁ hredParent
            (P.p₁-P.p₂) (P.q₁-P.q₂) P.p₂ P.q₂ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · ring
          · omega
          · exact hdetdiff
          · exact hdet₂
          · omega
          · exact hpos₂
          · intro hu
            have : P.q₁ = 1 := by simpa using hu
            omega
        ∀ (R : FordFareyParameter), (R.p = P.p₁ ∧ R.q = P.q₁) → ((Q.p₁ = P.p₁-P.p₂ ∧ Q.q₁ =
            P.q₁-P.q₂ ∧ Q.p₂ = P.p₂ ∧ Q.q₂ = P.q₂) → ((P₁.p₁ = P.p₁-P.p₂ ∧ P₁.q₁ = P.q₁-P.q₂ ∧
            P₁.p₂ = P.p₂ ∧ P₁.q₂ = P.q₂) → ((∀ y, y ∈ FordRecursiveVertexDomains P₁ 0 →
            FordOdometer P₁ y = FordOdometer H y) → ((∀ z, z ∈ FordRecursiveVertexDomains P₁ 1 →
            FordOdometer P₁ z = FordOdometer H (z-⟨(P₁.q₂ : Int), (P₁.q₂ : Int)⟩) + P₁.p₂*z.re +
            P₁.p₂*z.im - P₁.p₂*(P₁.q₂ : Int)+1) → ((∀ (x : GaussianInt), (x ∈ hr 0 ∩ hr 1) →
            ((P.q₂ : Int)+1 ≤ x.re ∧ x.re ≤ (P.q₁ : Int)-1 ∧ (P.q₂ : Int)+1 ≤ x.im ∧ x.im ≤ (P.q₁
            : Int)-1)) → (∀ x ∈ hr 0 ∩ hr 1, FourNeighborLaplacian (FordOdometer P) x =
            FourNeighborLaplacian (FordOdometer H) (x-⟨(P.q₂ : Int), (P.q₂ :
                Int)⟩)))))))))))))))) := by
  classical
  intro P P₁ hq₁ hsum hcrossdet hpos₁ hpos₂ hrec₀' hrec₁' hlapAffine hrec0Member hrec1Member hr
      horder hdlt hdetdiff H hHq hredParent Q R hR hpar hparP hch₀' hch₁' hcoords x hx
  have hb := hcoords x hx
  have hpt (z : GaussianInt) (hzr : (P.q₂ : Int) ≤ z.re)
      (hzr' : z.re ≤ (P.q₁ : Int)) (hzi : (P.q₂ : Int) ≤ z.im)
      (hzi' : z.im ≤ (P.q₁ : Int)) :
      FordOdometer P z = FordOdometer H
        (z-⟨(P.q₂ : Int), (P.q₂ : Int)⟩) +
          P.p₂*z.re + P.p₂*z.im - P.p₂*(P.q₂ : Int)+1 := by
    have hz0 := hrec0Member z (by omega) (by omega) (by omega) (by omega)
    have hz1 : z ∈ FordRecursiveVertexDomains P 1 := by
      apply hrec1Member z hzr ?_ hzi ?_
      · have hs : (P.q₁ : Int) + P.q₂ = P.q := by exact_mod_cast P.sum_q.symm
        omega
      · have hs : (P.q₁ : Int) + P.q₂ = P.q := by exact_mod_cast P.sum_q.symm
        omega
    have hy0 : z-⟨(P.q₂ : Int), (P.q₂ : Int)⟩ ∈
        FordRecursiveVertexDomains P₁ 0 := by
      change 0 ≤ (z-⟨(P.q₂ : Int),(P.q₂ : Int)⟩).re ∧
        (z-⟨(P.q₂ : Int),(P.q₂ : Int)⟩).re ≤ (P₁.q₁ : Int) ∧
        0 ≤ (z-⟨(P.q₂ : Int),(P.q₂ : Int)⟩).im ∧
        (z-⟨(P.q₂ : Int),(P.q₂ : Int)⟩).im ≤ (P₁.q₁ : Int)
      rw [hparP.2.1]
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub,
        ]
      constructor <;> omega
    have hzchild1 : z ∈ FordRecursiveVertexDomains P₁ 1 := by
      change (P₁.q₂ : Int) ≤ z.re ∧ z.re ≤ (P₁.q : Int) ∧
        (P₁.q₂ : Int) ≤ z.im ∧ z.im ≤ (P₁.q : Int)
      rw [hparP.2.2.2, hq₁]
      exact ⟨by omega, by omega, by omega, by omega⟩
    have houter0 := hrec₀' z hz0
    have houter1 := hrec₁' z hz1
    have hchild0 := hch₀' (z-⟨(P.q₂ : Int),(P.q₂ : Int)⟩) hy0
    have hchild1 := hch₁' z hzchild1
    have hshift : z-⟨(P.q₂ : Int),(P.q₂ : Int)⟩ =
        z-⟨(P₁.q₂ : Int),(P₁.q₂ : Int)⟩ := by rw [hparP.2.2.2]
    rw [← hshift, hparP.2.2.1, hparP.2.2.2] at hchild1
    calc
      FordOdometer P z = FordOdometer P₁ z := houter0
      _ = FordOdometer H (z-⟨(P.q₂ : Int),(P.q₂ : Int)⟩) +
            P.p₂*z.re + P.p₂*z.im - P.p₂*(P.q₂ : Int)+1 := by
          convert hchild1 using 1
  have ht := hlapAffine (FordOdometer P) (FordOdometer H) x
    ⟨(P.q₂ : Int),(P.q₂ : Int)⟩ P.p₂ P.p₂
    (-P.p₂*(P.q₂ : Int)+1)
  apply ht
  · convert hpt x (by omega) (by omega) (by omega) (by omega) using 1; ring
  · convert hpt (x-1) (by
      simp only [Zsqrtd.re_sub, Zsqrtd.re_one]
      omega)
      (by
          simp only [Zsqrtd.re_sub, Zsqrtd.re_one]
          omega)
      (by
          simp only [Zsqrtd.im_sub, Zsqrtd.im_one]
          omega)
      (by
          simp only [Zsqrtd.im_sub, Zsqrtd.im_one]
          omega) using 1; ring
  · convert hpt (x+1) (by
      simp only [Zsqrtd.re_add, Zsqrtd.re_one]
      omega)
      (by
          simp only [Zsqrtd.re_add, Zsqrtd.re_one]
          omega)
      (by
          simp only [Zsqrtd.im_add, Zsqrtd.im_one]
          omega)
      (by
          simp only [Zsqrtd.im_add, Zsqrtd.im_one]
          omega) using 1; ring
  · convert hpt (x-⟨0,1⟩) (by
      simp only [Zsqrtd.re_sub]
      omega)
      (by
          simp only [Zsqrtd.re_sub]
          omega)
      (by
          simp only [Zsqrtd.im_sub]
          omega)
      (by
          simp only [Zsqrtd.im_sub]
          omega) using 1; ring
  · convert hpt (x+⟨0,1⟩) (by
      simp only [Zsqrtd.re_add]
      omega)
      (by
          simp only [Zsqrtd.re_add]
          omega)
      (by
          simp only [Zsqrtd.im_add]
          omega)
      (by
          simp only [Zsqrtd.im_add]
          omega) using 1; ring

private theorem hdetdiffAt465 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          P.p₁ * (P.q₂ : Int) - P.p₂ * (P.q₁ : Int) = 1 →
            P.q₁ < P.q₂ →
              (P.p₂ - P.p₁) * (P.q₂ : Int) - ((P.q₂ - P.q₁ : Nat) : Int) * P.p₂ = -1
    ) := by
  classical
  intro P hcrossdet horder
  rw [Nat.cast_sub (by omega : P.q₁ ≤ P.q₂)]
  nlinarith only [hcrossdet]

private theorem hcopAt469 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          P.p₁ * (P.q₂ : Int) - P.p₂ * (P.q₁ : Int) = 1 →
            P.q₁ < P.q₂ → Nat.Coprime (P.q₂ - P.q₁) (P.p₂ - P.p₁).natAbs
    ) := by
  classical
  intro P hcrossdet horder
  have hc : IsCoprime ((P.q₂-P.q₁ : Nat) : Int) (P.p₂-P.p₁) := by
    have hx : P.p₁ * ((P.q₂-P.q₁ : Nat) : Int) -
        (P.q₁ : Int) * (P.p₂-P.p₁) = 1 := by
      rw [Nat.cast_sub (by omega : P.q₁ ≤ P.q₂)]
      nlinarith only [hcrossdet]
    exact ⟨P.p₁, -(P.q₁ : Int), by nlinarith only [hx]⟩
  simpa using Int.isCoprime_iff_nat_coprime.mp hc

private theorem hparAt498 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        (∀ (P₂ : FordFareyParameter), ∀ (hP :
            (2 : ℕ) < P.q), ∀ (hsum : P.q = P.q₁ + P.q₂), ∀ (hcrossdet : P.p₁ * (P.q₂ :
            Int) - P.p₂ * (P.q₁ : Int) = 1), ∀ (hpos₂ : 0 < P.q₂), ∀ (horder : P.q₁ < P.q₂), ∀
                (hdiff : 0 < P.q₂ - P.q₁), ∀ (hdetdiff : (P.p₂-P.p₁) * (P.q₂ : Int) - ((P.q₂-P.q₁ :
            Nat) : Int) * P.p₂ = -1), ∀ (H : FordFareyParameter), ∀ (hHq : H.q = P.q₂ - P.q₁), ∀
                (hredParent : Nat.Coprime P.q₂ P.p₂.natAbs),
        let Q : FordFareyParameter := by
          have hdet₁ : P.p₁ * (P.q₂ : Int) -
              (P.q₁ : Int) * P.p₂ = 1 := by nlinarith [hcrossdet]
          refine FordFareyParameter.mk P.p₂ P.q₂ hpos₂ hredParent
            P.p₁ P.q₁ (P.p₂-P.p₁) (P.q₂-P.q₁) ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · ring
          · omega
          · exact hdet₁
          · exact hdetdiff
          · omega
          · omega
          · intro hu
            have : P.q₂ = 1 := by simpa using hu
            omega;
        (Q = P₂) → (P₂.p₁ = P.p₁ ∧ P₂.q₁ = P.q₁ ∧ P₂.p₂ = P.p₂-P.p₁ ∧ P₂.q₂ = P.q₂-P.q₁))) := by
  classical
  intro P P₂ hP hsum hcrossdet hpos₂ horder hdiff hdetdiff H hHq hredParent Q hQeq
  simpa [hQeq] using (show Q.p₁ = P.p₁ ∧ Q.q₁ = P.q₁ ∧
    Q.p₂ = P.p₂-P.p₁ ∧ Q.q₂ = P.q₂-P.q₁ from ⟨rfl,rfl,rfl,rfl⟩)

private theorem hch₃' :
    (by
      classical
      exact
        ∀ (P₂ : FordFareyParameter), ∀ (H : FordFareyParameter), (∀ x ∈
            FordRecursiveVertexDomains P₂ (3 : Fin (4 : ℕ)), Classical.choose
            FordOdometerFamilyExistsUnique P₂ x = Classical.choose FordOdometerFamilyExistsUnique
            H (x - ⟨(0 : ℤ), (↑P₂.q₁ : ℤ)⟩) + P₂.p₁ * x.re) → (∀ z, z ∈
            FordRecursiveVertexDomains P₂ 3 → FordOdometer P₂ z = FordOdometer H (z-⟨0,(P₂.q₁ :
            Int)⟩) + P₂.p₁*z.re) ) := by
  classical
  intro P₂ H hch₃ z hz
  simpa [FordOdometer] using hch₃ z hz

private theorem hcoordsAt511 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          FordFareyParameter →
            (∀ (q : Nat),
                ∀ (x : GaussianInt),
                  x ∈ P4062T1InteriorSquare q ↔
                    1 ≤ x.re ∧ x.re ≤ (q : Int) - 1 ∧ 1 ≤ x.im ∧ x.im ≤ (q : Int) - 1) →
              ∀ (hr : Fin (4 : ℕ) → Finset GaussianInt),
                (hr 2 =
                    (P4062T1InteriorSquare P.q₂).image fun y => y + ⟨(P.q₁ : Int), 0⟩) →
                  (hr 3 =
                      (P4062T1InteriorSquare P.q₂).image fun y => y + ⟨0, (P.q₁ : Int)⟩) →
                    FordFareyParameter →
                      ∀ x ∈ hr (2 : Fin (4 : ℕ)) ∩ hr (3 : Fin (4 : ℕ)),
                        (↑P.q₁ : ℤ) + (1 : ℤ) ≤ x.re ∧
                          x.re ≤ (↑P.q₂ : ℤ) - (1 : ℤ) ∧
                            (↑P.q₁ : ℤ) + (1 : ℤ) ≤ x.im ∧ x.im ≤ (↑P.q₂ : ℤ) - (1 : ℤ)
    ) := by
  classical
  intro P P₂ squareCoordinates hr hA2 hA3 R x hx
  rcases Finset.mem_inter.mp hx with ⟨h2,h3⟩
  rw [hA2] at h2
  rw [hA3] at h3
  obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp h2
  obtain ⟨z, hz, hxz⟩ := Finset.mem_image.mp h3
  have by' := (squareCoordinates P.q₂ y).mp hy
  have bz' := (squareCoordinates P.q₂ z).mp hz
  have hxy' : x = y+⟨(P.q₁ : Int),0⟩ := hxy.symm
  have hxz' : x = z+⟨0,(P.q₁ : Int)⟩ := hxz.symm
  subst x
  rcases by' with ⟨yr,yr',yi,yi'⟩
  rcases bz' with ⟨zr,zr',zi,zi'⟩
  have hrel := hxz'
  have hrelR : y.re + (P.q₁ : Int) = z.re := by
    have hh := congrArg Zsqrtd.re hrel
    simpa only [Zsqrtd.re_add, Zsqrtd.re_zero, add_zero] using hh
  have hrelI : y.im = z.im + (P.q₁ : Int) := by
    have hh := congrArg Zsqrtd.im hrel
    calc
      y.im = y.im + 0 := by ring
      _ = z.im + (P.q₁ : Int) := by simpa only [Zsqrtd.im_add,
        Zsqrtd.im_zero, add_zero] using hh
  have hreX : (y+⟨(P.q₁ : Int),0⟩).re = y.re + P.q₁ := by
    simp only [Zsqrtd.re_add]
  have himX : (y+⟨(P.q₁ : Int),0⟩).im = y.im := by
    simp only [Zsqrtd.im_add, add_zero]
  rw [hreX, himX]
  exact ⟨by omega, by omega, by omega, by omega⟩

private theorem htargetAt542 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (P₂ : FordFareyParameter),
            P₂.q = P.q₂ →
              P.q = P.q₁ + P.q₂ →
                P.q₂ < P.q →
                  (∀ x,
                      x ∈ FordRecursiveVertexDomains P 2 →
                        FordOdometer P x =
                          FordOdometer P₂ (x - ⟨(P.q₁ : Int), 0⟩) + P.p₁ * x.im) →
                    (∀ (f : GaussianInt → Int),
                        ∀ (f' : GaussianInt → Int),
                          ∀ (x : GaussianInt),
                            ∀ (t : GaussianInt),
                              ∀ (A : Int),
                                ∀ (B : Int),
                                ∀ (C : Int),
                                f x = f' (x - t) + A * x.re + B * x.im + C →
                                f (x - 1) =
                                f' (x - t - 1) + A * (x - 1).re + B * (x - 1).im + C →
                                f (x + 1) =
                                f' (x - t + 1) + A * (x + 1).re + B * (x + 1).im + C →
                                f (x - ⟨0, 1⟩) =
                                f' (x - t - ⟨0, 1⟩) + A * (x - ⟨0, 1⟩).re +
                                B * (x - ⟨0, 1⟩).im +
                                C →
                                f (x + ⟨0, 1⟩) =
                                f' (x - t + ⟨0, 1⟩) + A * (x + ⟨0, 1⟩).re +
                                B * (x + ⟨0, 1⟩).im +
                                C →
                                FourNeighborLaplacian f x =
                                FourNeighborLaplacian f' (x - t)) →
                      (∀ (z : GaussianInt),
                          (P.q₁ : Int) ≤ z.re →
                            z.re ≤ (P.q : Int) →
                              0 ≤ z.im →
                                z.im ≤ (P.q₂ : Int) →
                                z ∈ FordRecursiveVertexDomains P 2) →
                        ∀ (hr : Fin (4 : ℕ) → Finset GaussianInt),
                          P.q₁ < P.q₂ →
                            ∀ (H : FordFareyParameter),
                              ∀ (R : FordFareyParameter),
                                R.p = P.p₂ ∧ R.q = P.q₂ →
                                P₂.p₁ = P.p₁ ∧
                                P₂.q₁ = P.q₁ ∧ P₂.p₂ = P.p₂ - P.p₁ ∧ P₂.q₂ = P.q₂ - P.q₁ →
                                (∀ z,
                                z ∈ FordRecursiveVertexDomains P₂ 3 →
                                FordOdometer P₂ z =
                                FordOdometer H (z - ⟨0, (P₂.q₁ : Int)⟩) + P₂.p₁ * z.re) →
                                (∀ (x : GaussianInt),
                                x ∈ hr 2 ∩ hr 3 →
                                (P.q₁ : Int) + 1 ≤ x.re ∧
                                x.re ≤ (P.q₂ : Int) - 1 ∧
                                (P.q₁ : Int) + 1 ≤ x.im ∧ x.im ≤ (P.q₂ : Int) - 1) →
                                ∀ x ∈ hr 2 ∩ hr 3,
                                FourNeighborLaplacian (FordOdometer P) x =
                                FourNeighborLaplacian (FordOdometer H)
                                (x - ⟨(P.q₁ : Int), (P.q₁ : Int)⟩)
    ) := by
  classical
  intro P P₂ hq₂ hsum hlt₂ hrec₂' hlapAffine hrec2Member hr horder H R hR hpar hch₃' hcoords x
      hx
  have hb := hcoords x hx
  have hpt (z : GaussianInt) (hzr : (P.q₁ : Int) ≤ z.re)
      (hzr' : z.re ≤ (P.q₂ : Int)) (hzi : (P.q₁ : Int) ≤ z.im)
      (hzi' : z.im ≤ (P.q₂ : Int)) :
      FordOdometer P z = FordOdometer H
        (z-⟨(P.q₁ : Int),(P.q₁ : Int)⟩) +
          P.p₁*z.re + P.p₁*z.im - P.p₁*(P.q₁ : Int) := by
    have hz2 : z ∈ FordRecursiveVertexDomains P 2 := by
      apply hrec2Member z hzr ?_ ?_ hzi'
      · have hs : (P.q₁ : Int)+P.q₂=P.q := by exact_mod_cast P.sum_q.symm
        omega
      · omega
    have hv2 : z-⟨(P.q₁ : Int),0⟩ ∈ FordRecursiveVertexDomains P₂ 3 := by
      change 0 ≤ (z-⟨(P.q₁ : Int),0⟩).re ∧
        (z-⟨(P.q₁ : Int),0⟩).re ≤ (P₂.q₂ : Int) ∧
        (P₂.q₁ : Int) ≤ (z-⟨(P.q₁ : Int),0⟩).im ∧
        (z-⟨(P.q₁ : Int),0⟩).im ≤ (P₂.q : Int)
      rw [hpar.2.2.2, hpar.2.1, hq₂]
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub,
        ]
      constructor <;> omega
    have houter := hrec₂' z hz2
    have hinner := hch₃' (z-⟨(P.q₁ : Int),0⟩) hv2
    rw [hpar.1, hpar.2.1] at hinner
    calc
      FordOdometer P z = FordOdometer P₂ (z-⟨(P.q₁ : Int),0⟩) +
          P.p₁*z.im := houter
      _ = FordOdometer H (z-⟨(P.q₁ : Int),(P.q₁ : Int)⟩) +
          P.p₁*z.re + P.p₁*z.im - P.p₁*(P.q₁ : Int) := by
        rw [hinner]
        have harg : z-⟨(P.q₁ : Int),0⟩-⟨0,(P.q₁ : Int)⟩ =
            z-⟨(P.q₁ : Int),(P.q₁ : Int)⟩ := by
          ext <;> simp only [Zsqrtd.re_sub, Zsqrtd.im_sub,
            ] <;> ring
        rw [harg]
        simp only [Zsqrtd.re_sub]
        ring
  have ht := hlapAffine (FordOdometer P) (FordOdometer H) x
    ⟨(P.q₁ : Int),(P.q₁ : Int)⟩ P.p₁ P.p₁
    (-P.p₁*(P.q₁ : Int))
  apply ht
  · convert hpt x (by omega) (by omega) (by omega) (by omega) using 1; ring
  · convert hpt (x-1) (by
      simp only [Zsqrtd.re_sub, Zsqrtd.re_one]
      omega)
      (by
          simp only [Zsqrtd.re_sub, Zsqrtd.re_one]
          omega)
      (by
          simp only [Zsqrtd.im_sub, Zsqrtd.im_one]
          omega)
      (by
          simp only [Zsqrtd.im_sub, Zsqrtd.im_one]
          omega) using 1; ring
  · convert hpt (x+1) (by
      simp only [Zsqrtd.re_add, Zsqrtd.re_one]
      omega)
      (by
          simp only [Zsqrtd.re_add, Zsqrtd.re_one]
          omega)
      (by
          simp only [Zsqrtd.im_add, Zsqrtd.im_one]
          omega)
      (by
          simp only [Zsqrtd.im_add, Zsqrtd.im_one]
          omega) using 1; ring
  · convert hpt (x-⟨0,1⟩) (by
      simp only [Zsqrtd.re_sub]
      omega)
      (by
          simp only [Zsqrtd.re_sub]
          omega)
      (by
          simp only [Zsqrtd.im_sub]
          omega)
      (by
          simp only [Zsqrtd.im_sub]
          omega) using 1; ring
  · convert hpt (x+⟨0,1⟩) (by
      simp only [Zsqrtd.re_add]
      omega)
      (by
          simp only [Zsqrtd.re_add]
          omega)
      (by
          simp only [Zsqrtd.im_add]
          omega)
      (by
          simp only [Zsqrtd.im_add]
          omega) using 1; ring

private theorem hyAt644 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        (∀ (P₂ : FordFareyParameter), (∀ (q :
            Nat), ∀ (x : GaussianInt), x ∈ P4062T1InteriorSquare q ↔ 1 ≤ x.re ∧ x.re ≤ (q :
            Int) - 1 ∧ 1 ≤ x.im ∧ x.im ≤ (q : Int) - 1) → ((P.q₁ < P.q₂) → (
        (∀ (R : FordFareyParameter), (R.p = P.p₂ ∧ R.q = P.q₂) → ((P₂.p₁ = P.p₁ ∧ P₂.q₁ =
            P.q₁ ∧ P₂.p₂ = P.p₂-P.p₁ ∧ P₂.q₂ = P.q₂-P.q₁) → (∀ (x : GaussianInt), ((↑P.q₁ : ℤ) +
            (1 : ℤ) ≤ x.re ∧ x.re ≤ (↑P.q₂ : ℤ) - (1 : ℤ) ∧ (↑P.q₁ : ℤ) + (1 : ℤ) ≤ x.im ∧ x.im ≤
            (↑P.q₂ : ℤ) - (1 : ℤ)) → (
        let y : GaussianInt := x-⟨(P.q₁ : Int),(P.q₁ : Int)⟩;
        y ∈ P4062T1InteriorSquare (P.q₂-P.q₁)))))))) ) := by
  classical
  intro P P₂ squareCoordinates horder R hR hpar x hc y
  apply (squareCoordinates (P.q₂-P.q₁) y).mpr
  dsimp [y]
  rw [Nat.cast_sub (by omega : P.q₁ ≤ P.q₂)]
  exact ⟨by omega, by omega, by omega, by omega⟩

private theorem hcastAt656 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        (∀ (P₂ : FordFareyParameter), (P.q₁ <
            P.q₂) → (∀ (H : FordFareyParameter), (H.q = P.q₂ - P.q₁) → (∀ (R :
            FordFareyParameter), (R.p = P.p₂ ∧ R.q = P.q₂) → ((P₂.p₁ = P.p₁ ∧ P₂.q₁ = P.q₁ ∧
            P₂.p₂ = P.p₂-P.p₁ ∧ P₂.q₂ = P.q₂-P.q₁) → (
        ((H.q : Int) = (P.q₂ :
            Int)-P.q₁)))))) ) := by
  classical
  intro P P₂ horder H hHq R hR hpar
  calc
    (H.q : Int) = ((P.q₂-P.q₁ : Nat) : Int) := by exact_mod_cast hHq
    _ = (P.q₂ : Int)-P.q₁ := by
      rw [Nat.cast_sub (by omega : P.q₁ ≤ P.q₂)]

private theorem hu :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        (∀ (P₂ : FordFareyParameter), (∀ (q :
            Nat), ∀ (x : GaussianInt), x ∈ P4062T1InteriorSquare q ↔ 1 ≤ x.re ∧ x.re ≤ (q :
            Int) - 1 ∧ 1 ≤ x.im ∧ x.im ≤ (q : Int) - 1) → ((P.q = P.q₁ + P.q₂) → ((P.q₂ - P.q₁ <
            P.q) → (∀ (H : FordFareyParameter), (H.q = P.q₂ - P.q₁) → (∀ (R :
            FordFareyParameter), (R.p = P.p₂ ∧ R.q = P.q₂) → ((P₂.p₁ = P.p₁ ∧ P₂.q₁ = P.q₁ ∧
            P₂.p₂ = P.p₂-P.p₁ ∧ P₂.q₂ = P.q₂-P.q₁) → (∀ (y : GaussianInt), ((1 : ℤ) ≤ y.re ∧ y.re
            ≤ (↑H.q : ℤ) - (1 : ℤ) ∧ (1 : ℤ) ≤ y.im ∧ y.im ≤ (↑H.q : ℤ) - (1 : ℤ)) → (((H.q :
            Int) = (P.q₂ : Int)-P.q₁) → (y+⟨0,(P.q₁ : Int)⟩ ∈ P4062T1InteriorSquare
            P.q₂))))))))) ) := by
  classical
  intro P P₂ squareCoordinates hsum hdlt H hHq R hR hpar y hyc hcast
  apply (squareCoordinates P.q₂ _).mpr
  simp only [Zsqrtd.re_add, Zsqrtd.im_add,
    ]
  exact ⟨by omega, by omega, by omega, by omega⟩

private theorem hv :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        (∀ (P₂ : FordFareyParameter), (∀ (q :
            Nat), ∀ (x : GaussianInt), x ∈ P4062T1InteriorSquare q ↔ 1 ≤ x.re ∧ x.re ≤ (q :
            Int) - 1 ∧ 1 ≤ x.im ∧ x.im ≤ (q : Int) - 1) → ((P.q = P.q₁ + P.q₂) → ((P.q₂ - P.q₁ <
            P.q) → (∀ (H : FordFareyParameter), (H.q = P.q₂ - P.q₁) → (∀ (R :
            FordFareyParameter), (R.p = P.p₂ ∧ R.q = P.q₂) → ((P₂.p₁ = P.p₁ ∧ P₂.q₁ = P.q₁ ∧
            P₂.p₂ = P.p₂-P.p₁ ∧ P₂.q₂ = P.q₂-P.q₁) → (∀ (y : GaussianInt), ((1 : ℤ) ≤ y.re ∧ y.re
            ≤ (↑H.q : ℤ) - (1 : ℤ) ∧ (1 : ℤ) ≤ y.im ∧ y.im ≤ (↑H.q : ℤ) - (1 : ℤ)) → (((H.q :
            Int) = (P.q₂ : Int)-P.q₁) → (y+⟨(P.q₁ : Int),0⟩ ∈ P4062T1InteriorSquare
            P.q₂))))))))) ) := by
  classical
  intro P P₂ squareCoordinates hsum hdlt H hHq R hR hpar y hyc hcast
  apply (squareCoordinates P.q₂ _).mpr
  simp only [Zsqrtd.re_add, Zsqrtd.im_add,
    ]
  exact ⟨by omega, by omega, by omega, by omega⟩

private theorem hmem2 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (hr : Fin (4 : ℕ) → Finset GaussianInt), (hr 2 =
            (P4062T1InteriorSquare P.q₂).image (fun y => y+⟨(P.q₁ : Int),0⟩)) → (∀ (y :
            GaussianInt), (y+⟨0,(P.q₁ : Int)⟩ ∈ P4062T1InteriorSquare P.q₂) → (y+⟨(P.q₁ :
            Int),(P.q₁ : Int)⟩ ∈ hr 2)) ) := by
  classical
  intro P hr hA2 y hu
  rw [hA2]
  apply Finset.mem_image.mpr
  refine ⟨y+⟨0,(P.q₁ : Int)⟩, hu, ?_⟩
  ext <;> simp only [Zsqrtd.re_add, Zsqrtd.im_add,
    ] <;> ring

private theorem hmem3 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (hr : Fin (4 : ℕ) → Finset GaussianInt), (hr 3 =
            (P4062T1InteriorSquare P.q₂).image (fun y => y+⟨0,(P.q₁ : Int)⟩)) → (∀ (y :
            GaussianInt), (y+⟨(P.q₁ : Int),0⟩ ∈ P4062T1InteriorSquare P.q₂) → (y+⟨(P.q₁ :
            Int),(P.q₁ : Int)⟩ ∈ hr 3)) ) := by
  classical
  intro P hr hA3 y hv
  rw [hA3]
  apply Finset.mem_image.mpr
  refine ⟨y+⟨(P.q₁ : Int),0⟩, hv, ?_⟩
  ext <;> simp only [Zsqrtd.re_add, Zsqrtd.im_add,
    ] <;> ring

end OverlapDescentDetails

theorem P4062T1OverlapDescent (P P₁ P₂ : FordFareyParameter)
    (hP : 2 < P.q)
    (hp₁ : P₁.p = P.p₁) (hq₁ : P₁.q = P.q₁)
    (hp₂ : P₂.p = P.p₂) (hq₂ : P₂.q = P.q₂) :
    let A := P4062T1RecursiveInteriors P
    (P.q₂ < P.q₁ → ∃ H : FordFareyParameter,
      H.p = P.p₁-P.p₂ ∧ H.q = P.q₁-P.q₂ ∧ H.q < P.q ∧
      P₁.p₁ = P.p₁-P.p₂ ∧ P₁.q₁ = P.q₁-P.q₂ ∧
      P₁.p₂ = P.p₂ ∧ P₁.q₂ = P.q₂ ∧
      A 0 ∩ A 1 = (P4062T1InteriorSquare H.q).image
        (fun x => x+⟨(P.q₂ : Int), (P.q₂ : Int)⟩) ∧
      ∀ x ∈ A 0 ∩ A 1,
        FourNeighborLaplacian (FordOdometer P) x =
          FourNeighborLaplacian (FordOdometer H)
            (x-⟨(P.q₂ : Int), (P.q₂ : Int)⟩)) ∧
    (P.q₁ < P.q₂ → ∃ H : FordFareyParameter,
      H.p = P.p₂-P.p₁ ∧ H.q = P.q₂-P.q₁ ∧ H.q < P.q ∧
      P₂.p₁ = P.p₁ ∧ P₂.q₁ = P.q₁ ∧
      P₂.p₂ = P.p₂-P.p₁ ∧ P₂.q₂ = P.q₂-P.q₁ ∧
      A 2 ∩ A 3 = (P4062T1InteriorSquare H.q).image
        (fun x => x+⟨(P.q₁ : Int), (P.q₁ : Int)⟩) ∧
      ∀ x ∈ A 2 ∩ A 3,
        FourNeighborLaplacian (FordOdometer P) x =
          FourNeighborLaplacian (FordOdometer H)
            (x-⟨(P.q₁ : Int), (P.q₁ : Int)⟩)) := by
-- BODY
  classical
  have squareCoordinates (q : Nat) (x : GaussianInt) := FordInteriorSquareCoordinates.membership q x
  have hsum : P.q = P.q₁ + P.q₂ := P.sum_q
  have hcrossdet := OverlapDescentDetails.hcrossdet P
  have hpos₁ := OverlapDescentDetails.hpos₁ P P₁ hP hq₁ hsum
  have hpos₂ : 0 < P.q₂ := P.q₂_pos
  have hlt₁ : P.q₁ < P.q := P.q₁_lt
  have hlt₂ : P.q₂ < P.q := by omega
  have hred₁ := OverlapDescentDetails.hred₁ P hcrossdet
  obtain ⟨_, _, _, _, _, hfamilyRec⟩ :=
    (Classical.choose_spec FordOdometerFamilyExistsUnique).1
  have hrec := hfamilyRec P P₁ P₂ (by omega) hp₁ hq₁ hp₂ hq₂
  rcases hrec with ⟨hrec₀, hrec₁, hrec₂, hrec₃⟩
  have hrec₀' := OverlapDescentDetails.hrec₀' P P₁ hrec₀
  have hrec₁' := OverlapDescentDetails.hrec₁' P
              P₁ hrec₁
  have hrec₂' := OverlapDescentDetails.hrec₂' P P₂ hrec₂
  have hrec₃' := OverlapDescentDetails.hrec₃' P P₂ hrec₃
  have hlapAffine (f f' : GaussianInt → Int) (x t : GaussianInt)
      (A B C : Int)
      (h0 : f x = f' (x - t) + A * x.re + B * x.im + C)
      (hm : f (x - 1) = f' ((x - t) - 1) + A * (x - 1).re +
        B * (x - 1).im + C)
      (hp : f (x + 1) = f' ((x - t) + 1) + A * (x + 1).re +
        B * (x + 1).im + C)
      (hmi : f (x - ⟨0, 1⟩) = f' ((x - t) - ⟨0, 1⟩) +
        A * (x - ⟨0, 1⟩).re + B * (x - ⟨0, 1⟩).im + C)
      (hpi : f (x + ⟨0, 1⟩) = f' ((x - t) + ⟨0, 1⟩) +
        A * (x + ⟨0, 1⟩).re + B * (x + ⟨0, 1⟩).im + C) :=
          FourNeighborLaplacianProperties.affineTranslate f f' x t A B C h0 hm hp hmi hpi
  have hrec0Member (z : GaussianInt)
      (a : 0 ≤ z.re) (b : z.re ≤ (P.q₁ : Int))
      (c : 0 ≤ z.im) (d : z.im ≤ (P.q₁ : Int)) := OverlapDescentDetails.hrec0Member P z a b c d
  have hrec1Member (z : GaussianInt)
      (a : (P.q₂ : Int) ≤ z.re) (b : z.re ≤ (P.q : Int))
      (c : (P.q₂ : Int) ≤ z.im) (d : z.im ≤ (P.q : Int)) := OverlapDescentDetails.hrec1Member P z
          a b c d
  have hrec2Member (z : GaussianInt)
      (a : (P.q₁ : Int) ≤ z.re) (b : z.re ≤ (P.q : Int))
      (c : 0 ≤ z.im) (d : z.im ≤ (P.q₂ : Int)) := OverlapDescentDetails.hrec2Member P z a b c d
  have hrec3Member (z : GaussianInt)
      (a : 0 ≤ z.re) (b : z.re ≤ (P.q₂ : Int))
      (c : (P.q₁ : Int) ≤ z.im) (d : z.im ≤ (P.q : Int)) := OverlapDescentDetails.hrec3Member P z
          a b c d
  intro hr
  have hA0 : hr 0 = P4062T1InteriorSquare P.q₁ := by rfl
  have hA1 : hr 1 = (P4062T1InteriorSquare P.q₁).image
      (fun y => y+⟨(P.q₂ : Int),(P.q₂ : Int)⟩) := by rfl
  have hA2 : hr 2 = (P4062T1InteriorSquare P.q₂).image
      (fun y => y+⟨(P.q₁ : Int),0⟩) := by rfl
  have hA3 : hr 3 = (P4062T1InteriorSquare P.q₂).image
      (fun y => y+⟨0,(P.q₁ : Int)⟩) := by rfl
  constructor
  · intro horder
    have hdiff : 0 < P.q₁ - P.q₂ := by omega
    have hdlt : P.q₁ - P.q₂ < P.q := by omega
    have hdetdiff := OverlapDescentDetails.hdetdiffAt260 P
            hcrossdet horder
    have hcop := OverlapDescentDetails.hcopAt264 P hcrossdet horder
    obtain ⟨H, ⟨hHp,hHq⟩, _⟩ :=
      FordFareyParentsExist (P.p₁-P.p₂) (P.q₁-P.q₂) hdiff hcop
    have hredParent : Nat.Coprime P.q₁ P.p₁.natAbs := hred₁.1
    let Q : FordFareyParameter := by
      have hdet₂ : P.p₂ * (P.q₁ : Int) -
          (P.q₂ : Int) * P.p₁ = -1 := by nlinarith only [hcrossdet]
      refine FordFareyParameter.mk P.p₁ P.q₁ hpos₁ hredParent
        (P.p₁-P.p₂) (P.q₁-P.q₂) P.p₂ P.q₂ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · ring
      · omega
      · exact hdetdiff
      · exact hdet₂
      · omega
      · exact hpos₂
      · intro hu
        have : P.q₁ = 1 := by simpa using hu
        omega
    obtain ⟨R, hR, hRuniq⟩ :=
      FordFareyParentsExist P.p₁ P.q₁ hpos₁ hredParent
    have hQeq : Q = P₁ := by
      exact (hRuniq Q ⟨rfl, rfl⟩).trans (hRuniq P₁ ⟨hp₁, hq₁⟩).symm
    have hpar : Q.p₁ = P.p₁-P.p₂ ∧ Q.q₁ = P.q₁-P.q₂ ∧
        Q.p₂ = P.p₂ ∧ Q.q₂ = P.q₂ := OverlapDescentDetails.hparAt293 P hP hsum hcrossdet
            hpos₁ hpos₂ horder hdlt hdetdiff H hHq hredParent
    have hparP : P₁.p₁ = P.p₁-P.p₂ ∧ P₁.q₁ = P.q₁-P.q₂ ∧
        P₁.p₂ = P.p₂ ∧ P₁.q₂ = P.q₂ := by simpa [hQeq] using hpar
    have hchildRec := hfamilyRec P₁ H P₂ (by rw [hq₁]; omega)
      (hHp.trans hparP.1.symm) (hHq.trans hparP.2.1.symm)
      (hp₂.trans hparP.2.2.1.symm) (hq₂.trans hparP.2.2.2.symm)
    rcases hchildRec with ⟨hch₀, hch₁, _, _⟩
    have hch₀' := OverlapDescentDetails.hch₀' P₁ H hch₀
    have hch₁' := OverlapDescentDetails.hch₁' P₁ H hch₁
    have hcoords (x : GaussianInt) (hx : x ∈ hr 0 ∩ hr 1) := OverlapDescentDetails.hcoordsAt312
        P squareCoordinates hr hA0 hA1 H x hx
    have htarget := OverlapDescentDetails.htargetAt327 P P₁ hq₁
                hsum hcrossdet hpos₁ hpos₂ hrec₀' hrec₁' hlapAffine hrec0Member hrec1Member hr
                horder hdlt hdetdiff H hHq hredParent R hR hpar hparP hch₀' hch₁' hcoords
    refine ⟨H, hHp, hHq, by simpa [hHq] using hdlt, hparP.1, hparP.2.1,
      hparP.2.2.1, hparP.2.2.2, ?_, htarget⟩
    ext x
    constructor
    · intro hx
      have hc := hcoords x hx
      let y : GaussianInt := x-⟨(P.q₂ : Int),(P.q₂ : Int)⟩
      have hy : y ∈ P4062T1InteriorSquare (P.q₁-P.q₂) := by
        apply (squareCoordinates (P.q₁-P.q₂) y).mpr
        dsimp [y]
        rw [Nat.cast_sub (by omega : P.q₂ ≤ P.q₁)]
        exact ⟨by omega, by omega, by omega, by omega⟩
      refine Finset.mem_image.mpr ⟨y, ?_, ?_⟩
      · simpa [hHq] using hy
      · dsimp [y]
        exact sub_add_cancel x ⟨(P.q₂ : Int),(P.q₂ : Int)⟩
    · intro hx
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
      have hyc := (squareCoordinates H.q y).mp hy
      have hcast : (H.q : Int) = (P.q₁ : Int)-P.q₂ := by
        rw [hHq, Nat.cast_sub (by omega : P.q₂ ≤ P.q₁)]
      subst x
      apply Finset.mem_inter.mpr
      constructor
      · apply (squareCoordinates P.q₁ _).mpr
        simp only [Zsqrtd.re_add, Zsqrtd.im_add,
          ]
        exact ⟨by omega, by omega, by omega, by omega⟩
      · apply Finset.mem_image.mpr
        refine ⟨y, ?_, rfl⟩
        apply (squareCoordinates P.q₁ y).mpr
        rw [hcast] at hyc
        exact ⟨hyc.1, by omega, hyc.2.2.1, by omega⟩
  · intro horder
    have hdiff : 0 < P.q₂ - P.q₁ := by omega
    have hdlt : P.q₂ - P.q₁ < P.q := by omega
    have hdetdiff := OverlapDescentDetails.hdetdiffAt465 P
            hcrossdet horder
    have hcop := OverlapDescentDetails.hcopAt469 P hcrossdet horder
    obtain ⟨H, ⟨hHp,hHq⟩, _⟩ :=
      FordFareyParentsExist (P.p₂-P.p₁) (P.q₂-P.q₁) hdiff hcop
    have hredParent : Nat.Coprime P.q₂ P.p₂.natAbs := hred₁.2
    let Q : FordFareyParameter := by
      have hdet₁ : P.p₁ * (P.q₂ : Int) -
          (P.q₁ : Int) * P.p₂ = 1 := by nlinarith [hcrossdet]
      refine FordFareyParameter.mk P.p₂ P.q₂ hpos₂ hredParent
        P.p₁ P.q₁ (P.p₂-P.p₁) (P.q₂-P.q₁) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · ring
      · omega
      · exact hdet₁
      · exact hdetdiff
      · omega
      · omega
      · intro hu
        have : P.q₂ = 1 := by simpa using hu
        omega
    obtain ⟨R, hR, hRuniq⟩ :=
      FordFareyParentsExist P.p₂ P.q₂ hpos₂ hredParent
    have hQeq : Q = P₂ := by
      exact (hRuniq Q ⟨rfl, rfl⟩).trans (hRuniq P₂ ⟨hp₂, hq₂⟩).symm
    have hpar : P₂.p₁ = P.p₁ ∧ P₂.q₁ = P.q₁ ∧
        P₂.p₂ = P.p₂-P.p₁ ∧ P₂.q₂ = P.q₂-P.q₁ := OverlapDescentDetails.hparAt498 P P₂ hP hsum
            hcrossdet hpos₂ horder hdiff hdetdiff H hHq hredParent hQeq
    have hchildRec := hfamilyRec P₂ P₁ H (by rw [hq₂]; omega)
      (hp₁.trans hpar.1.symm) (hq₁.trans hpar.2.1.symm)
      (hHp.trans hpar.2.2.1.symm) (hHq.trans hpar.2.2.2.symm)
    rcases hchildRec with ⟨_, _, hch₂, hch₃⟩
    have hch₃' := OverlapDescentDetails.hch₃' P₂ H hch₃
    have hcoords (x : GaussianInt) (hx : x ∈ hr 2 ∩ hr 3) := OverlapDescentDetails.hcoordsAt511 P
            P₂ squareCoordinates hr hA2 hA3 R x hx
    have htarget := OverlapDescentDetails.htargetAt542 P P₂ hq₂
                hsum hlt₂ hrec₂' hlapAffine hrec2Member hr horder H R hR hpar hch₃' hcoords
    refine ⟨H, hHp, hHq, by simpa [hHq] using hdlt,
      hpar.1, hpar.2.1, hpar.2.2.1, hpar.2.2.2, ?_, htarget⟩
    ext x
    constructor
    · intro hx
      have hc := hcoords x hx
      let y : GaussianInt := x-⟨(P.q₁ : Int),(P.q₁ : Int)⟩
      have hy := OverlapDescentDetails.hyAt644 P P₂
          squareCoordinates horder R hR hpar x hc
      refine Finset.mem_image.mpr ⟨y, ?_, ?_⟩
      · simpa [hHq] using hy
      · dsimp [y]
        exact sub_add_cancel x ⟨(P.q₁ : Int),(P.q₁ : Int)⟩
    · intro hx
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
      have hyc := (squareCoordinates H.q y).mp hy
      have hcast := OverlapDescentDetails.hcastAt656 P P₂
          horder H hHq R hR hpar
      have hsmall := hyc
      rw [hcast] at hsmall
      have hu :=
        OverlapDescentDetails.hu P P₂ squareCoordinates hsum hdlt H hHq R hR hpar y hyc hcast
      have hv :=
        OverlapDescentDetails.hv P P₂ squareCoordinates hsum hdlt H hHq R hR hpar y hyc hcast
      have hmem2 := OverlapDescentDetails.hmem2 P hr hA2 y hu
      have hmem3 := OverlapDescentDetails.hmem3 P hr hA3 y hv
      exact Finset.mem_inter.mpr
        ⟨by simpa [hxy] using hmem2, by simpa [hxy] using hmem3⟩

end ApollonianSuperharmonic

end
