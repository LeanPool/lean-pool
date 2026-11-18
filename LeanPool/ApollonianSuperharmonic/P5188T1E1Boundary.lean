/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5130T5ParentArithmetic
public import LeanPool.ApollonianSuperharmonic.FordDoubledBoundary
public import LeanPool.ApollonianSuperharmonic.IntegerCeilDiv
public import LeanPool.ApollonianSuperharmonic.P5188T1CeilingStability
public import LeanPool.ApollonianSuperharmonic.P5188T1CeilingBelow
public import LeanPool.ApollonianSuperharmonic.IntegerLatticeFunction

-- [TABLET NODE: P5188T1E1Boundary]

/-!
# P5188T1E1Boundary

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5188T1E1Boundary (P P₁ : FordFareyParameter)
    (hq : 1 < P.q) (hp₁ : P₁.p = P.p₁) (hq₁ : P₁.q = P.q₁)
    (g₁ : IntegerLatticeFunction)
    (h₁ : ∀ x ∈ FordDoubledBoundary P₁.q,
      g₁ x = IntegerCeilDiv (P₁.p * x.re * x.im) P₁.q (by exact_mod_cast P₁.q_pos.ne'))
    (x : GaussianInt)
    (hdom : 0 ≤ x.re ∧ x.re ≤ (P.q₁ : Int) ∧ 0 ≤ x.im ∧ x.im ≤ (P.q₁ : Int))
    (hbd : x ∈ FordDoubledBoundary P.q) :
    g₁ x =
      IntegerCeilDiv (P.p * x.re * x.im) P.q (by exact_mod_cast P.q_pos.ne') := by
-- BODY
  have hsum : (P.q : Int) = P.q₁ + P.q₂ := by exact_mod_cast P.sum_q
  have hdet₁ := P.det₁
  have hqpos : 0 < (P.q : Int) := by exact_mod_cast P.q_pos
  have ha : 0 < (P.q₁ : Int) := by have := (P5130T5ParentArithmetic P hq).1; exact_mod_cast this
  have hb : 0 < (P.q₂ : Int) := by have := P.q₂_pos; exact_mod_cast this
  have hab : (P.q₁ : Int) < P.q := by have := P.q₁_lt; exact_mod_cast this
  let a : Int := P.q₁
  let b : Int := P.q₂
  let A : Int := P.p₁
  have hAq : A * P.q - a * P.p = 1 := by simpa [a, A] using hdet₁
  have hpqa : P.p * a = A * P.q - 1 := by
    have haux : A * P.q - P.p * a = 1 := by
      rw [mul_comm P.p a]
      exact hAq
    omega
  have ceilPerturb := P5188T1CeilingStability
  have ceilBelow := P5188T1CeilingBelow
  have ceilMul (c t d : Int) (hd : d ≠ 0) :
      IntegerCeilDiv (c * d * t) d (by omega) = c * t := by
    dsimp only [IntegerCeilDiv]
    have he : -(c * d * t) = d * (-c * t) := by ring
    rw [he, Int.mul_ediv_cancel_left _ hd]
    ring
  have g₁val (u v : Int) (hu0 : 0 ≤ u) (hu : u ≤ a)
      (hv0 : 0 ≤ v) (hv : v ≤ a)
      (hs : u = 0 ∨ u = 1 ∨ u = a - 1 ∨ u = a ∨
        v = 0 ∨ v = 1 ∨ v = a - 1 ∨ v = a) :
      g₁ ⟨u, v⟩ = IntegerCeilDiv (A * u * v) a (by omega) := by
    have hbd : (⟨u, v⟩ : GaussianInt) ∈ FordDoubledBoundary P₁.q := by
      change (0 ≤ u ∧ u ≤ (P₁.q : Int) ∧ 0 ≤ v ∧ v ≤ (P₁.q : Int)) ∧ _
      refine ⟨⟨hu0, ?_, hv0, ?_⟩, ?_⟩
      · simpa [a, hq₁] using hu
      · simpa [a, hq₁] using hv
      intro hi
      simp at hi
      rcases hs with h | h | h | h | h | h | h | h <;> omega
    simpa [a, A, hp₁, hq₁] using h₁ ⟨u, v⟩ hbd
  have hbox : x ∈ FordVertexDomain P.q := hbd.1
  have hside : x.re = 0 ∨ x.re = 1 ∨ x.re = (P.q : Int) - 1 ∨ x.re = P.q ∨
      x.im = 0 ∨ x.im = 1 ∨ x.im = (P.q : Int) - 1 ∨ x.im = P.q := by
    change x ∈ FordVertexDomain P.q ∧ _ at hbd
    rcases hbd with ⟨_, hn⟩
    simp only [FordVertexDomain] at hbox
    rcases hbox with ⟨hr0, hrq, hi0, hiq⟩
    by_contra hnside
    push Not at hnside
    apply hn
    exact ⟨by omega, by omega, by omega, by omega⟩
  change (0 ≤ x.re ∧ x.re ≤ P.q₁ ∧ 0 ≤ x.im ∧ x.im ≤ P.q₁) at hdom
  change g₁ x = IntegerCeilDiv (P.p * x.re * x.im) P.q _
  have hE1side : x.re = 0 ∨ x.re = 1 ∨ x.re = P.q - 1 ∨
      x.im = 0 ∨ x.im = 1 ∨ x.im = P.q - 1 := by
    rcases hside with hr | hr | hr | hr | hi | hi | hi | hi
    · exact Or.inl hr
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr (Or.inl hr))
    · omega
    · exact Or.inr (Or.inr (Or.inr (Or.inl hi)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hi))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hi))))
    · omega
  rcases hE1side with hr0 | hr1 | hrq | hi0 | hi1 | hiq
  · have hx : x = ⟨0, x.im⟩ := by ext <;> simp [hr0]
    rw [hx]
    change g₁ ⟨0, x.im⟩ = IntegerCeilDiv (P.p * 0 * x.im) P.q _
    rw [g₁val 0 x.im (by omega) (by omega) (by omega) (by omega)
      (Or.inl rfl)]
    simp [IntegerCeilDiv]
  · have hx : x = ⟨1, x.im⟩ := by ext <;> simp [hr1]
    rw [hx]
    change g₁ ⟨1, x.im⟩ = IntegerCeilDiv (P.p * 1 * x.im) P.q _
    rw [g₁val 1 x.im (by omega) (by omega) (by omega) (by omega)
      (Or.inr (Or.inl rfl))]
    have hrel : (P.p * x.im) * a = (A * x.im) * P.q - x.im := by
      calc
        (P.p * x.im) * a = (P.p * a) * x.im := by ring
        _ = (A * P.q - 1) * x.im := by rw [hpqa]
        _ = (A * x.im) * P.q - x.im := by ring
    simpa only [mul_one] using (ceilPerturb (A * x.im) (P.p * x.im) a P.q x.im ha hab
      (by omega) (by omega) hrel).symm
  · have hb1 : b = 1 := by omega
    have hra : x.re = a := by omega
    have hx : x = ⟨a, x.im⟩ := by ext <;> simp [hra]
    rw [hx]
    change g₁ ⟨a, x.im⟩ = IntegerCeilDiv (P.p * a * x.im) P.q _
    rw [g₁val a x.im (by omega) (by omega) (by omega) (by omega)
      (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]
    have hnum : P.p * a * x.im = (A * x.im) * P.q - x.im := by
      rw [hpqa]
      ring
    rw [hnum, ceilBelow (A * x.im) x.im P.q hqpos (by omega) (by omega)]
    simpa [mul_assoc, mul_left_comm, mul_comm] using ceilMul A x.im a (by omega)
  · have hx : x = ⟨x.re, 0⟩ := by ext <;> simp [hi0]
    rw [hx]
    change g₁ ⟨x.re, 0⟩ = IntegerCeilDiv (P.p * x.re * 0) P.q _
    rw [g₁val x.re 0 (by omega) (by omega) (by omega) (by omega)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)) )))]
    simp [IntegerCeilDiv]
  · have hx : x = ⟨x.re, 1⟩ := by ext <;> simp [hi1]
    rw [hx]
    change g₁ ⟨x.re, 1⟩ = IntegerCeilDiv (P.p * x.re * 1) P.q _
    rw [g₁val x.re 1 (by omega) (by omega) (by omega) (by omega)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)) ))))]
    have hrel : (P.p * x.re) * a = (A * x.re) * P.q - x.re := by
      calc
        (P.p * x.re) * a = (P.p * a) * x.re := by ring
        _ = (A * P.q - 1) * x.re := by rw [hpqa]
        _ = (A * x.re) * P.q - x.re := by ring
    simpa only [mul_one] using (ceilPerturb (A * x.re) (P.p * x.re) a P.q x.re ha hab
      (by omega) (by omega) hrel).symm
  · have hb1 : b = 1 := by omega
    have hia : x.im = a := by omega
    have hx : x = ⟨x.re, a⟩ := by ext <;> simp [hia]
    rw [hx]
    change g₁ ⟨x.re, a⟩ = IntegerCeilDiv (P.p * x.re * a) P.q _
    rw [g₁val x.re a (by omega) (by omega) (by omega) (by omega)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))]
    have hnum : P.p * x.re * a = (A * x.re) * P.q - x.re := by
      calc
        P.p * x.re * a = (P.p * a) * x.re := by ring
        _ = (A * P.q - 1) * x.re := by rw [hpqa]
        _ = (A * x.re) * P.q - x.re := by ring
    rw [hnum]
    rw [ceilBelow (A * x.re) x.re P.q hqpos (by omega) (by omega)]
    simpa [mul_assoc, mul_left_comm, mul_comm] using ceilMul A x.re a (by omega)

end ApollonianSuperharmonic

end
