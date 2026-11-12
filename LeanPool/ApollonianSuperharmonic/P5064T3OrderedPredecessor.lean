/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FordCoordinateConfiguration
public import LeanPool.ApollonianSuperharmonic.BandPredecessorNoCollision

-- [TABLET NODE: P5064T3OrderedPredecessor]

/-!
# P5064T3OrderedPredecessor

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5064T3OrderedPredecessor (P : FordFareyParameter)
    (r : Fin 4 → CircleCoordinates) (hr : ProperBandQuadruple r)
    (hr0 : r 0 = (FordRecursiveQuadruple P) 1)
    (hr2 : r 2 = (FordRecursiveQuadruple P) 2)
    (hr3 : r 3 = (FordRecursiveQuadruple P) 3)
    (h12 : ((FordRecursiveQuadruple P) 2).1 ≤
      ((FordRecursiveQuadruple P) 1).1)
    (h2large : 1 < ((FordRecursiveQuadruple P) 2).1) :
    2 ≤ P.q₂ ∧ P.q₂ < P.q₁ ∧ 0 < P.q₁ - P.q₂ ∧
      ∃ P₁ : FordFareyParameter,
        P₁.p = P.p₁ ∧ P₁.q = P.q₁ ∧
        P₁.p₁ = P.p₁ - P.p₂ ∧ P₁.q₁ = P.q₁ - P.q₂ ∧
        P₁.p₂ = P.p₂ ∧ P₁.q₂ = P.q₂ ∧
        r = FordRecursiveQuadruple P₁ := by
-- BODY
  have h2 : 1 < (P.q₂ : Int) * (P.q₂ : Int) := by
    simpa [FordRecursiveQuadruple, FordCircleCoordinate] using h2large
  have hs : 2 ≤ P.q₂ := by
    by_contra h
    have hz : P.q₂ = 0 ∨ P.q₂ = 1 := by omega
    rcases hz with hz | hz <;> norm_num [hz] at h2
  have hn : P.q₁ ≠ 0 := by
    intro hz
    have hh := h12
    simp [FordRecursiveQuadruple, FordCircleCoordinate, hz] at hh
    nlinarith [hh]
  have hle : P.q₂ ≤ P.q₁ := by
    have hh : (P.q₂ : Int) * (P.q₂ : Int) ≤ (P.q₁ : Int) * (P.q₁ : Int) := by
      simpa [FordRecursiveQuadruple, FordCircleCoordinate, hn] using h12
    by_contra h
    have hgt : (P.q₁ : Int) < (P.q₂ : Int) := by omega
    nlinarith [Nat.cast_nonneg (α := Int) P.q₁,
      Nat.cast_nonneg (α := Int) P.q₂]
  have cross : P.p₁ * (P.q₂ : Int) - (P.q₁ : Int) * P.p₂ = 1 := by
    have h := P.det₁
    rw [P.sum_q, P.sum_p, Nat.cast_add] at h
    nlinarith [h]
  have hrs : P.q₂ < P.q₁ := by
    by_contra h
    have he : P.q₁ = P.q₂ := by omega
    have hd : (P.q₂ : Int) ∣ 1 := ⟨P.p₁ - P.p₂, by
      rw [he] at cross
      nlinarith [cross]⟩
    have := Int.eq_one_of_dvd_one (by omega) hd
    omega
  have red : Nat.Coprime P.q₁ P.p₁.natAbs := by
    rw [Nat.coprime_iff_gcd_eq_one]
    apply Nat.dvd_one.mp
    let g := Nat.gcd P.q₁ P.p₁.natAbs
    have gb : (g : Int) ∣ (P.q₁ : Int) := by
      exact_mod_cast Nat.gcd_dvd_left P.q₁ P.p₁.natAbs
    have ga : (g : Int) ∣ P.p₁ :=
      Int.dvd_natAbs.mp (by exact_mod_cast Nat.gcd_dvd_right P.q₁ P.p₁.natAbs)
    have gd : (g : Int) ∣ 1 := by
      rw [← cross]
      exact dvd_sub (dvd_mul_of_dvd_left ga _) (dvd_mul_of_dvd_left gb _)
    have hg : (g : Int) = 1 := Int.eq_one_of_dvd_one (by omega) gd
    have hg' : g = 1 := by exact_mod_cast hg
    change g ∣ 1
    rw [hg']
  let P₁ : FordFareyParameter := {
    p := P.p₁
    q := P.q₁
    q_pos := by omega
    reduced := red
    p₁ := P.p₁ - P.p₂
    q₁ := P.q₁ - P.q₂
    p₂ := P.p₂
    q₂ := P.q₂
    sum_p := by ring
    sum_q := by omega
    det₁ := by
      rw [Nat.cast_sub hrs.le]
      nlinarith [cross]
    det₂ := by nlinarith [cross]
    q₁_lt := by omega
    q₂_pos := P.q₂_pos
    unit_case := by intro h; omega }
  have child : (FordRecursiveQuadruple P₁) 0 = (FordRecursiveQuadruple P) 1 := by
    simp [FordRecursiveQuadruple, P₁, hn]
  have hp := ((FordCoordinateConfiguration P₁).2 (by change 1 < P.q₁; omega)).1
  obtain ⟨k, hk, _⟩ := BandPredecessorNoCollision
    (FordRecursiveQuadruple P₁) r hp hr (child.trans hr0.symm)
  have hk0 : k = 0 := by
    fin_cases k
    · rfl
    · have h := hk 1
      change r 2 = (FordRecursiveQuadruple P₁) 3 at h
      rw [hr2] at h
      have hc := congrArg Prod.fst h
      simp [FordRecursiveQuadruple, FordCircleCoordinate] at hc
      nlinarith [hc]
    · have h := hk 2
      change r 3 = (FordRecursiveQuadruple P₁) 2 at h
      rw [hr3] at h
      have hc := congrArg Prod.fst h
      simp [FordRecursiveQuadruple, FordCircleCoordinate, P₁] at hc
      nlinarith [hc]
  refine ⟨hs, hrs, by omega, P₁, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  rw [hk0] at hk
  simp only [add_zero] at hk
  funext i
  fin_cases i
  · exact hr0.trans child.symm
  · exact hk 0
  · exact hk 1
  · exact hk 2

end ApollonianSuperharmonic

end
