/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5130T5Prescription
public import LeanPool.ApollonianSuperharmonic.P5130T5ParentArithmetic
public import LeanPool.ApollonianSuperharmonic.FordFareyParentsExist
public import LeanPool.ApollonianSuperharmonic.FordDoubledBoundary
public import LeanPool.ApollonianSuperharmonic.IntegerCeilDiv
public import LeanPool.ApollonianSuperharmonic.FordRecursiveVertexDomains
public import Mathlib.LinearAlgebra.Matrix.Notation

-- [TABLET NODE: P5130T5SameParentOverlaps]

/-!
# P5130T5SameParentOverlaps

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace SameParentOverlapLemmas

private theorem hq1 :
    ∀ (P : FordFareyParameter), ∀ (P₁ : FordFareyParameter), (P₁.q = P.q₁) → P₁.q = P.q₁ := by
  classical
  intro P P₁ hq₁
  exact hq₁

private theorem hq2 :
    ∀ (P : FordFareyParameter), ∀ (P₂ : FordFareyParameter), (P₂.q = P.q₂) → P₂.q = P.q₂ := by
  classical
  intro P P₂ hq₂
  exact hq₂

private theorem hp1 :
    ∀ (P : FordFareyParameter), ∀ (P₁ : FordFareyParameter), (P₁.p = P.p₁) → P₁.p = P.p₁ := by
  classical
  intro P P₁ hp₁
  exact hp₁

private theorem hp2 :
    ∀ (P : FordFareyParameter), ∀ (P₂ : FordFareyParameter), (P₂.p = P.p₂) → P₂.p = P.p₂ := by
  classical
  intro P P₂ hp₂
  exact hp₂

private theorem hq1pos' :
    ∀ (P : FordFareyParameter),
      ∀ (P₁ : FordFareyParameter), P₁.q = P.q₁ → 0 < P.q₁ → 0 < P₁.q := by
  classical
  intro P P₁ hq₁ hq1pos
  omega

private theorem hq2pos' :
    ∀ (P : FordFareyParameter),
      ∀ (P₂ : FordFareyParameter), P₂.q = P.q₂ → 0 < P.q₂ → 0 < P₂.q := by
  classical
  intro P P₂ hq₂ hq2pos
  omega

private theorem hq1lt' :
    ∀ (P : FordFareyParameter),
      ∀ (P₁ : FordFareyParameter), P₁.q = P.q₁ → P.q₁ < P.q → P₁.q < P.q := by
  classical
  intro P P₁ hq₁ hq1lt
  omega

private theorem hq2lt' :
    ∀ (P : FordFareyParameter),
      ∀ (P₂ : FordFareyParameter), P₂.q = P.q₂ → P.q₂ < P.q → P₂.q < P.q := by
  classical
  intro P P₂ hq₂ hq2lt
  omega

end SameParentOverlapLemmas

namespace FirstParentOverlap

private theorem first_parent_overlap :
    ∀ (P : FordFareyParameter), ∀ (P₁ : FordFareyParameter), ∀ (P₂ : FordFareyParameter), (P₁.p =
        P.p₁) → (P₁.q = P.q₁) → (P₂.p = P.p₂) → (P₂.q = P.q₂) → ∀ (G : FordFareyParameter →
        IntegerLatticeFunction), (∀ R, R.q < P.q → ∀ x ∈ FordDoubledBoundary R.q, G R x =
        IntegerCeilDiv (R.p * x.re * x.im) R.q (by exact_mod_cast R.q_pos.ne')) → (∀ R A B, R.q <
        P.q → 1 < R.q → A.p = R.p₁ → A.q = R.q₁ → B.p = R.p₂ → B.q = R.q₂ → ∀ i x, x ∈
        FordRecursiveVertexDomains R i → G R x = P5130T5Prescription R (G A) (G B) i x) → ((0 :
        ℕ) < P.q₁) → ((0 : ℕ) < P.q₂) → (P.p₁ * (↑P.q₂ : ℤ) - P.p₂ * (↑P.q₁ : ℤ) = (1 : ℤ)) →
        (P₁.q = P.q₁) → (P₂.q = P.q₂) → (P₁.p = P.p₁) → (P₂.p = P.p₂) → (P₁.q < P.q) → (P₂.q <
        P.q) → ∀ x,
      x ∈ FordRecursiveVertexDomains P 0 → x ∈ FordRecursiveVertexDomains P 1 →
      P5130T5Prescription P (G P₁) (G P₂) 0 x =
        P5130T5Prescription P (G P₁) (G P₂) 1 x := by
  classical
  intro P P₁ P₂ hp₁ hq₁ hp₂ hq₂ G hB hR hq1pos hq2pos hcross hq1 hq2 hp1 hp2 hq1lt' hq2lt' x hx0 hx1
  by_cases hgt : P.q₁ > P.q₂
  · have hqdiff : P.q₂ + (P.q₁ - P.q₂) = P.q₁ := Nat.add_sub_of_le hgt.le
    let q3 : Nat := P.q₁ - P.q₂
    let p3 : Int := P.p₁ - P.p₂
    have hq3pos : 0 < q3 := by dsimp [q3]; omega
    have hq3lt : q3 < P.q₁ := by dsimp [q3]; omega
    have hq3cast : (P.q₁ : Int) = (P.q₂ : Int) + (q3 : Int) := by
      dsimp [q3]
      rw [Nat.cast_sub hgt.le]
      omega
    have hdet3a : p3 * (P.q₂ : Int) - P.p₂ * (q3 : Int) = 1 := by
      calc
        p3 * (P.q₂ : Int) - P.p₂ * (q3 : Int) =
            P.p₁ * (P.q₂ : Int) - P.p₂ * ((P.q₂ : Int) + (q3 : Int)) := by
              dsimp [p3]; ring
        _ = P.p₁ * (P.q₂ : Int) - P.p₂ * (P.q₁ : Int) := by rw [← hq3cast]
        _ = 1 := hcross
    have hdet3b : p3 * (P.q₁ : Int) - (q3 : Int) * P.p₁ = 1 := by
      calc
        p3 * (P.q₁ : Int) - (q3 : Int) * P.p₁ =
            P.p₁ * ((P.q₁ : Int) - (q3 : Int)) - P.p₂ * (P.q₁ : Int) := by
              dsimp [p3]; ring
        _ = P.p₁ * (P.q₂ : Int) - P.p₂ * (P.q₁ : Int) := by rw [hq3cast]; ring
        _ = 1 := hcross
    have hdetP1₂ : P.p₂ * (P.q₁ : Int) - (P.q₂ : Int) * P.p₁ = -1 := by
      calc
        P.p₂ * (P.q₁ : Int) - (P.q₂ : Int) * P.p₁ =
            -(P.p₁ * (P.q₂ : Int) - P.p₂ * (P.q₁ : Int)) := by ring
        _ = -1 := by rw [hcross]
    have hred3 : Nat.Coprime q3 p3.natAbs := by
      have hdvd : (Int.gcd (q3 : Int) p3 : Int) ∣ (1 : Int) := by
        have hga : (Int.gcd (q3 : Int) p3 : Int) ∣ p3 := Int.gcd_dvd_right _ _
        have hgb : (Int.gcd (q3 : Int) p3 : Int) ∣ (q3 : Int) := Int.gcd_dvd_left _ _
        have hdiv : (Int.gcd (q3 : Int) p3 : Int) ∣
            p3 * (P.q₂ : Int) - P.p₂ * (q3 : Int) :=
          dvd_sub (dvd_mul_of_dvd_left hga _) (dvd_mul_of_dvd_right hgb _)
        rw [hdet3a] at hdiv
        exact hdiv
      have hn : Int.natAbs (Int.gcd (q3 : Int) p3) = 1 :=
        Int.isUnit_iff_natAbs_eq.mp (isUnit_of_dvd_one hdvd)
      simpa [Int.gcd] using hn
    obtain ⟨P₃, hP₃, _⟩ := FordFareyParentsExist p3 q3 hq3pos hred3
    let T : FordFareyParameter := {
      p := P₁.p, q := P₁.q, q_pos := P₁.q_pos, reduced := P₁.reduced,
      p₁ := p3, q₁ := q3, p₂ := P₂.p, q₂ := P₂.q,
      sum_p := by dsimp [p3]; rw [hp1, hp2]; have hs := P.sum_p; omega,
      sum_q := by dsimp [q3]; rw [hq1, hq2]; have hs := P.sum_q; omega,
      det₁ := by dsimp [p3]; rw [hp1, hq1]; exact hdet3b,
      det₂ := by rw [hp2, hq2, hp1, hq1]; exact hdetP1₂,
      q₁_lt := by dsimp [q3]; rw [hq1]; omega,
      q₂_pos := P₂.q_pos,
      unit_case := by intro hu; have := hq3pos; have := P₂.q_pos; omega }
    obtain ⟨W, hW, huniq⟩ := FordFareyParentsExist P₁.p P₁.q P₁.q_pos P₁.reduced
    have hTP1 : T = P₁ := (huniq T ⟨rfl, rfl⟩).trans (huniq P₁ ⟨rfl, rfl⟩).symm
    have hp31 : P₁.p₁ = p3 := by
      have h := congrArg FordFareyParameter.p₁ hTP1
      simpa [T] using h.symm
    have hq31 : P₁.q₁ = q3 := by
      have h := congrArg FordFareyParameter.q₁ hTP1
      simpa [T] using h.symm
    have hp32 : P₁.p₂ = P₂.p := by
      have h := congrArg FordFareyParameter.p₂ hTP1
      simpa [T] using h.symm
    have hq32 : P₁.q₂ = P₂.q := by
      have h := congrArg FordFareyParameter.q₂ hTP1
      simpa [T] using h.symm
    simp only [FordRecursiveVertexDomains] at hx0 hx1
    rcases hx0 with ⟨hx0r, hx0r', hx0i, hx0i'⟩
    rcases hx1 with ⟨hx1r, hx1r', hx1i, hx1i'⟩
    let y : GaussianInt := x - ⟨(P.q₂ : Int), (P.q₂ : Int)⟩
    have hy0 : y ∈ FordRecursiveVertexDomains P₁ 0 := by
      simp only [FordRecursiveVertexDomains, Matrix.cons_val_zero, Set.mem_ofPred_eq]
      rw [hq31]
      constructor
      · simp [y, sub_eq_add_neg]; omega
      constructor
      · simp [y, sub_eq_add_neg]; omega
      constructor
      · simp [y, sub_eq_add_neg]; omega
      · simp [y, sub_eq_add_neg]; omega
    have hx1P : x ∈ FordRecursiveVertexDomains P₁ 1 := by
      simp only [FordRecursiveVertexDomains, Matrix.cons_val_one]
      change (P₁.q₂ : Int) ≤ x.re ∧ x.re ≤ (P₁.q : Int) ∧
        (P₁.q₂ : Int) ≤ x.im ∧ x.im ≤ (P₁.q : Int)
      exact ⟨by simpa [hq32, hq2] using hx1r, by simpa [hq1] using hx0r',
        by simpa [hq32, hq2] using hx1i, by simpa [hq1] using hx0i'⟩
    have hP1gt : 1 < P₁.q := by rw [hq1]; omega
    have hrx := hR P₁ P₃ P₂ hq1lt' hP1gt
      (by exact hP₃.1.trans hp31.symm)
      (by exact hP₃.2.trans hq31.symm)
      hp32.symm hq32.symm 1 x hx1P
    have hry := hR P₁ P₃ P₂ hq1lt' hP1gt
      (by exact hP₃.1.trans hp31.symm)
      (by exact hP₃.2.trans hq31.symm)
      hp32.symm hq32.symm 0 y hy0
    simp only [P5130T5Prescription, Matrix.cons_val_zero, Matrix.cons_val_one]
    change G P₁ x = G P₁ y + P.p₂ * x.re + P.p₂ * x.im - P.p₂ * (P.q₂ : Int) + 1
    have hrx' : G P₁ x = G P₃ y + P.p₂ * x.re + P.p₂ * x.im - P.p₂ * (P.q₂ : Int) + 1 := by
      simpa [P5130T5Prescription, y, hp32, hq32, hp2, hq2] using hrx
    have hry' : G P₁ y = G P₃ y := by simpa [P5130T5Prescription] using hry
    rw [hrx', hry']
  · by_cases hlt : P.q₂ > P.q₁
    · simp only [FordRecursiveVertexDomains] at hx0 hx1
      rcases hx0 with ⟨_, hx0r, _, hx0i⟩
      rcases hx1 with ⟨hx1r, _, hx1i, _⟩
      omega
    · have hden : P.q₁ = P.q₂ := by omega
      simp only [FordRecursiveVertexDomains] at hx0 hx1
      rcases hx0 with ⟨hx0r, hx0r', hx0i, hx0i'⟩
      rcases hx1 with ⟨hx1r, hx1r', hx1i, hx1i'⟩
      have hmul : (P.q₁ : Int) * (P.p₁ - P.p₂) = 1 := by
        have hcross' := hcross
        rw [← hden] at hcross'
        calc
          (P.q₁ : Int) * (P.p₁ - P.p₂) = P.p₁ * (P.q₁ : Int) - P.p₂ * (P.q₁ : Int) := by ring
          _ = 1 := hcross'
      have hdiv : (P.q₁ : Int) ∣ (1 : Int) := ⟨P.p₁ - P.p₂, hmul.symm⟩
      have hqle : (P.q₁ : Int) ≤ 1 := Int.le_of_dvd (by norm_num) hdiv
      have hqone : P.q₁ = 1 := by omega
      have hq2one : P.q₂ = 1 := by omega
      have hq1int : (P.q₁ : Int) = 1 := by exact_mod_cast hqone
      have hq2int : (P.q₂ : Int) = 1 := by exact_mod_cast hq2one
      have hxre : x.re = 1 := by omega
      have hxim : x.im = 1 := by omega
      let c : GaussianInt := ⟨1, 1⟩
      have hxc : x = c := by ext <;> simp [c, hxre, hxim]
      have hpone : P.p₁ = P.p₂ + 1 := by nlinarith [hmul, hqone]
      have hPq : P.q = 2 := by have hs := P.sum_q; omega
      have hP1q : P₁.q = 1 := by omega
      have hP2q : P₂.q = 1 := by omega
      let z : GaussianInt := ⟨0, 0⟩
      let u : GaussianInt := ⟨0, 1⟩
      let v : GaussianInt := ⟨1, 0⟩
      have hz1 : G P₁ z = 0 := by
        have hb := hB P₁ (by omega) z (by simp [z, FordDoubledBoundary, FordVertexDomain])
        simpa [z, IntegerCeilDiv] using hb
      have hc1 : G P₁ c = P₁.p := by
        have hb := hB P₁ (by omega) c (by simp [c, hP1q, FordDoubledBoundary, FordVertexDomain])
        simpa [c, IntegerCeilDiv, hP1q] using hb
      have hu2 : G P₂ u = 0 := by
        have hb := hB P₂ (by omega) u (by simp [u, hP2q, FordDoubledBoundary, FordVertexDomain])
        simpa [u, IntegerCeilDiv] using hb
      have hv2 : G P₂ v = 0 := by
        have hb := hB P₂ (by omega) v (by simp [v, hP2q, FordDoubledBoundary, FordVertexDomain])
        simpa [v, IntegerCeilDiv] using hb
      have hval : P₁.p = P₂.p + 1 := by omega
      rw [hxc]
      simp only [P5130T5Prescription, Matrix.cons_val_zero, Matrix.cons_val_one,
        ]
      have hshift : c - ⟨(P.q₂ : Int), (P.q₂ : Int)⟩ = z := by
        ext <;> simp [c, z, hq2int]
      rw [hshift]
      simp [c, z, hq2int,
        hval, hz1, hc1, hp2]

end FirstParentOverlap

theorem P5130T5SameParentOverlaps (P P₁ P₂ : FordFareyParameter)
    (hq : 1 < P.q) (hp₁ : P₁.p = P.p₁) (hq₁ : P₁.q = P.q₁)
    (hp₂ : P₂.p = P.p₂) (hq₂ : P₂.q = P.q₂)
    (G : FordFareyParameter → IntegerLatticeFunction)
    (hB : ∀ R, R.q < P.q → ∀ x ∈ FordDoubledBoundary R.q,
      G R x = IntegerCeilDiv (R.p * x.re * x.im) R.q (by exact_mod_cast R.q_pos.ne'))
    (hR : ∀ R A B, R.q < P.q → 1 < R.q →
      A.p = R.p₁ → A.q = R.q₁ → B.p = R.p₂ → B.q = R.q₂ →
      ∀ i x, x ∈ FordRecursiveVertexDomains R i →
        G R x = P5130T5Prescription R (G A) (G B) i x) :
    let F := P5130T5Prescription P (G P₁) (G P₂)
    (∀ x, x ∈ FordRecursiveVertexDomains P 0 → x ∈ FordRecursiveVertexDomains P 1 → F 0 x = F 1 x) ∧
    (∀ x, x ∈ FordRecursiveVertexDomains P 2 → x ∈ FordRecursiveVertexDomains P 3 → F 2 x = F 3
        x) := by
-- BODY
  dsimp
  have harith := P5130T5ParentArithmetic P hq
  rcases harith with ⟨hq1pos, hq1lt, hq2pos, hq2lt, hred1, hred2, hcross⟩
  have hq1 : P₁.q = P.q₁ := SameParentOverlapLemmas.hq1 P P₁ hq₁
  have hq2 : P₂.q = P.q₂ := SameParentOverlapLemmas.hq2 P P₂ hq₂
  have hp1 : P₁.p = P.p₁ := SameParentOverlapLemmas.hp1 P P₁ hp₁
  have hp2 : P₂.p = P.p₂ := SameParentOverlapLemmas.hp2 P P₂ hp₂
  have hq1pos' : 0 < P₁.q := SameParentOverlapLemmas.hq1pos' P P₁ hq₁ hq1pos
  have hq2pos' : 0 < P₂.q := SameParentOverlapLemmas.hq2pos' P P₂ hq₂ hq2pos
  have hq1lt' : P₁.q < P.q := SameParentOverlapLemmas.hq1lt' P P₁ hq₁ hq1lt
  have hq2lt' : P₂.q < P.q := SameParentOverlapLemmas.hq2lt' P P₂ hq₂ hq2lt
  have first_parent_overlap : ∀ x,
      x ∈ FordRecursiveVertexDomains P 0 → x ∈ FordRecursiveVertexDomains P 1 →
      P5130T5Prescription P (G P₁) (G P₂) 0 x =
        P5130T5Prescription P (G P₁) (G P₂) 1 x := FirstParentOverlap.first_parent_overlap P P₁
            P₂ hp₁ hq₁ hp₂ hq₂ G hB hR hq1pos hq2pos hcross hq1 hq2 hp1 hp2 hq1lt' hq2lt'
  refine ⟨first_parent_overlap, ?_⟩
  intro x hx2 hx3
  by_cases hlt : P.q₂ > P.q₁
  · have hqdiff : P.q₁ + (P.q₂ - P.q₁) = P.q₂ := Nat.add_sub_of_le hlt.le
    let q4 : Nat := P.q₂ - P.q₁
    let p4 : Int := P.p₂ - P.p₁
    have hq4pos : 0 < q4 := by dsimp [q4]; omega
    have hq4lt : q4 < P.q₂ := by dsimp [q4]; omega
    have hq4cast : (P.q₂ : Int) = (P.q₁ : Int) + (q4 : Int) := by
      dsimp [q4]
      rw [Nat.cast_sub hlt.le]
      omega
    have hdet4a : P.p₁ * (q4 : Int) - p4 * (P.q₁ : Int) = 1 := by
      calc
        P.p₁ * (q4 : Int) - p4 * (P.q₁ : Int) =
            P.p₁ * (q4 : Int) - (P.p₂ - P.p₁) * (P.q₁ : Int) := by rfl
        _ = P.p₁ * (P.q₂ : Int) - P.p₂ * (P.q₁ : Int) := by rw [hq4cast]; ring
        _ = 1 := hcross
    have hdet4b : p4 * (P.q₂ : Int) - (q4 : Int) * P.p₂ = -1 := by
      calc
        p4 * (P.q₂ : Int) - (q4 : Int) * P.p₂ =
            P.p₂ * ((P.q₂ : Int) - (q4 : Int)) - P.p₁ * (P.q₂ : Int) := by dsimp [p4]; ring
        _ = P.p₂ * (P.q₁ : Int) - P.p₁ * (P.q₂ : Int) := by rw [hq4cast]; ring
        _ = -(P.p₁ * (P.q₂ : Int) - P.p₂ * (P.q₁ : Int)) := by ring
        _ = -1 := by rw [hcross]
    have hred4 : Nat.Coprime q4 p4.natAbs := by
      have hdvd : (Int.gcd (q4 : Int) p4 : Int) ∣ (1 : Int) := by
        have hga : (Int.gcd (q4 : Int) p4 : Int) ∣ p4 := Int.gcd_dvd_right _ _
        have hgb : (Int.gcd (q4 : Int) p4 : Int) ∣ (q4 : Int) := Int.gcd_dvd_left _ _
        have hdiv : (Int.gcd (q4 : Int) p4 : Int) ∣
            P.p₁ * (q4 : Int) - p4 * (P.q₁ : Int) :=
          dvd_sub (dvd_mul_of_dvd_right hgb _) (dvd_mul_of_dvd_left hga _)
        rw [hdet4a] at hdiv
        exact hdiv
      have hn : Int.natAbs (Int.gcd (q4 : Int) p4) = 1 :=
        Int.isUnit_iff_natAbs_eq.mp (isUnit_of_dvd_one hdvd)
      simpa [Int.gcd] using hn
    obtain ⟨P₄, hP₄, _⟩ := FordFareyParentsExist p4 q4 hq4pos hred4
    let T : FordFareyParameter := {
      p := P₂.p, q := P₂.q, q_pos := P₂.q_pos, reduced := P₂.reduced,
      p₁ := P₁.p, q₁ := P₁.q, p₂ := p4, q₂ := q4,
      sum_p := by dsimp [p4]; rw [hp1, hp2]; have hs := P.sum_p; omega,
      sum_q := by dsimp [q4]; rw [hq1, hq2]; have hs := P.sum_q; omega,
      det₁ := by rw [hp1, hq1, hp2, hq2]; simpa [mul_comm] using hcross,
      det₂ := by dsimp [p4]; rw [hp2, hq2]; exact hdet4b,
      q₁_lt := by rw [hq1]; omega,
      q₂_pos := hq4pos,
      unit_case := by intro hu; have := hq4pos; have := P₁.q_pos; omega }
    obtain ⟨W, hW, huniq⟩ := FordFareyParentsExist P₂.p P₂.q P₂.q_pos P₂.reduced
    have hTP2 : T = P₂ := (huniq T ⟨rfl, rfl⟩).trans (huniq P₂ ⟨rfl, rfl⟩).symm
    have hp41 : P₂.p₁ = P₁.p := by
      have h := congrArg FordFareyParameter.p₁ hTP2
      simpa [T] using h.symm
    have hq41 : P₂.q₁ = P₁.q := by
      have h := congrArg FordFareyParameter.q₁ hTP2
      simpa [T] using h.symm
    have hp42 : P₂.p₂ = p4 := by
      have h := congrArg FordFareyParameter.p₂ hTP2
      simpa [T] using h.symm
    have hq42 : P₂.q₂ = q4 := by
      have h := congrArg FordFareyParameter.q₂ hTP2
      simpa [T] using h.symm
    simp only [FordRecursiveVertexDomains] at hx2 hx3
    rcases hx2 with ⟨hx2r, hx2r', hx2i, hx2i'⟩
    rcases hx3 with ⟨hx3r, hx3r', hx3i, hx3i'⟩
    let u : GaussianInt := x - ⟨(P.q₁ : Int), 0⟩
    let v : GaussianInt := x - ⟨0, (P.q₁ : Int)⟩
    let w : GaussianInt := x - ⟨(P.q₁ : Int), (P.q₁ : Int)⟩
    have hu3 : u ∈ FordRecursiveVertexDomains P₂ 3 := by
      simp only [FordRecursiveVertexDomains, Matrix.cons_val_three]
      change 0 ≤ u.re ∧ u.re ≤ (P₂.q₂ : Int) ∧
        (P₂.q₁ : Int) ≤ u.im ∧ u.im ≤ (P₂.q : Int)
      rw [hq42, hq41, hq2, hq1]
      simp [u, sub_eq_add_neg]
      omega
    have hv2 : v ∈ FordRecursiveVertexDomains P₂ 2 := by
      simp only [FordRecursiveVertexDomains, Matrix.cons_val_two]
      change (P₂.q₁ : Int) ≤ v.re ∧ v.re ≤ (P₂.q : Int) ∧
        0 ≤ v.im ∧ v.im ≤ (P₂.q₂ : Int)
      rw [hq41, hq42, hq2, hq1]
      simp [v, sub_eq_add_neg]
      omega
    have hP2gt : 1 < P₂.q := by rw [hq2]; omega
    have hru := hR P₂ P₁ P₄ hq2lt' hP2gt hp41.symm hq41.symm
      (by exact hP₄.1.trans hp42.symm) (by exact hP₄.2.trans hq42.symm) 3 u hu3
    have hrv := hR P₂ P₁ P₄ hq2lt' hP2gt hp41.symm hq41.symm
      (by exact hP₄.1.trans hp42.symm) (by exact hP₄.2.trans hq42.symm) 2 v hv2
    simp only [P5130T5Prescription, Matrix.cons_val_two, Matrix.cons_val_three]
    change G P₂ u + P.p₁ * x.im = G P₂ v + P.p₁ * x.re
    have hru' : G P₂ u = G P₄ (u - ⟨0, (P₁.q : Int)⟩) + P.p₁ * u.re := by
      simpa [P5130T5Prescription, hp41, hq41, hp1] using hru
    have hrv' : G P₂ v = G P₄ (v - ⟨(P₁.q : Int), 0⟩) + P.p₁ * v.im := by
      simpa [P5130T5Prescription, hp41, hq41, hp1] using hrv
    have hcomm : u - ⟨0, (P₁.q : Int)⟩ = v - ⟨(P₁.q : Int), 0⟩ := by
      ext <;> simp [u, v, sub_eq_add_neg, hq1]
    rw [hru', hrv']
    rw [hcomm]
    simp [u, v]
    ring
  · by_cases hgt : P.q₁ > P.q₂
    · simp only [FordRecursiveVertexDomains] at hx2 hx3
      rcases hx2 with ⟨_, hx2r, _, hx2i⟩
      rcases hx3 with ⟨hx3r, _, hx3i, _⟩
      omega
    · have hden : P.q₁ = P.q₂ := by omega
      have hmul : (P.q₁ : Int) * (P.p₁ - P.p₂) = 1 := by
        have hcross' := hcross
        rw [← hden] at hcross'
        calc
          (P.q₁ : Int) * (P.p₁ - P.p₂) = P.p₁ * (P.q₁ : Int) - P.p₂ * (P.q₁ : Int) := by ring
          _ = 1 := hcross'
      have hdiv : (P.q₁ : Int) ∣ (1 : Int) := ⟨P.p₁ - P.p₂, hmul.symm⟩
      have hqle : (P.q₁ : Int) ≤ 1 := Int.le_of_dvd (by norm_num) hdiv
      have hqone : P.q₁ = 1 := by omega
      have hq2one : P.q₂ = 1 := by omega
      simp only [FordRecursiveVertexDomains] at hx2 hx3
      rcases hx2 with ⟨hx2r, hx2r', hx2i, hx2i'⟩
      rcases hx3 with ⟨hx3r, hx3r', hx3i, hx3i'⟩
      have hq1int : (P.q₁ : Int) = 1 := by exact_mod_cast hqone
      have hq2int : (P.q₂ : Int) = 1 := by exact_mod_cast hq2one
      have hxre : x.re = 1 := by omega
      have hxim : x.im = 1 := by omega
      let c : GaussianInt := ⟨1, 1⟩
      have hxc : x = c := by ext <;> simp [c, hxre, hxim]
      have hpone : P.p₁ = P.p₂ + 1 := by nlinarith [hmul, hqone]
      have hPq : P.q = 2 := by have hs := P.sum_q; omega
      have hP1q : P₁.q = 1 := by omega
      have hP2q : P₂.q = 1 := by omega
      let u : GaussianInt := ⟨0, 1⟩
      let v : GaussianInt := ⟨1, 0⟩
      have hc1 : G P₁ c = P₁.p := by
        have hb := hB P₁ (by omega) c (by simp [c, hP1q, FordDoubledBoundary, FordVertexDomain])
        simpa [c, IntegerCeilDiv, hP1q] using hb
      have hu2 : G P₂ u = 0 := by
        have hb := hB P₂ (by omega) u (by simp [u, hP2q, FordDoubledBoundary, FordVertexDomain])
        simpa [u, IntegerCeilDiv] using hb
      have hv2 : G P₂ v = 0 := by
        have hb := hB P₂ (by omega) v (by simp [v, hP2q, FordDoubledBoundary, FordVertexDomain])
        simpa [v, IntegerCeilDiv] using hb
      have hval : P₁.p = P₂.p + 1 := by omega
      rw [hxc]
      simp only [P5130T5Prescription,
        Matrix.cons_val_two, Matrix.cons_val_three]
      change G P₂ (c - ⟨(P.q₁ : Int), 0⟩) + P.p₁ * c.im =
        G P₂ (c - ⟨0, (P.q₁ : Int)⟩) + P.p₁ * c.re
      have hshift₂ : c - ⟨(P.q₁ : Int), 0⟩ = u := by ext <;> simp [c, u, hq1int]
      have hshift₃ : c - ⟨0, (P.q₁ : Int)⟩ = v := by ext <;> simp [c, v, hq1int]
      rw [hshift₂, hshift₃]
      simp [c, u, v, hu2, hv2]

end ApollonianSuperharmonic

end
