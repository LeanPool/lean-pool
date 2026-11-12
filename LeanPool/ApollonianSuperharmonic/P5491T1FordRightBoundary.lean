/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5332T1RightRows
public import LeanPool.ApollonianSuperharmonic.FordOdometer
public import LeanPool.ApollonianSuperharmonic.FordVertexDomain
public import LeanPool.ApollonianSuperharmonic.FordDoubledBoundary

-- [TABLET NODE: P5491T1FordRightBoundary]

/-!
# P5491T1FordRightBoundary

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5491T1FordRightBoundary (P : FordFareyParameter) (hq : 1 < P.q)
    (j : Fin 3) (e : Bool) :
    let R := P5332T1RightRows P j 0
    let d := if e then R.displacement else -R.displacement
    let a := if e then R.linear else -R.linear
    ∃ b : ℤ, ∀ x : GaussianInt,
      x ∈ FordVertexDomain P.q → x - d ∈ FordVertexDomain P.q →
      FordOdometer P (x-d) + a.re*x.re + a.im*x.im - FordOdometer P x = b := by
-- BODY
  have hn : (P.q : ℤ) ≠ 0 := by exact_mod_cast P.q_pos.ne'
  have boundary (x y : ℤ) (hx : 0 ≤ x) (hxq : x ≤ P.q)
      (hy : 0 ≤ y) (hyq : y ≤ P.q)
      (hb : x = 0 ∨ x = P.q ∨ y = 0 ∨ y = P.q) :
      FordOdometer P ⟨x,y⟩ = IntegerCeilDiv (P.p*x*y) P.q hn := by
    apply (Classical.choose_spec FordOdometerFamilyExistsUnique).1.2.1
    change (0 ≤ x ∧ x ≤ (P.q : ℤ) ∧ 0 ≤ y ∧ y ≤ (P.q : ℤ)) ∧
      ¬ (2 ≤ x ∧ x ≤ (P.q : ℤ)-2 ∧ 2 ≤ y ∧ y ≤ (P.q : ℤ)-2)
    omega
  have bottom (x : ℤ) (hx : 0 ≤ x) (hxq : x ≤ P.q) :
      FordOdometer P ⟨x,0⟩ = 0 := by
    rw [boundary x 0 hx hxq (by omega) (by omega) (by omega)]
    simp [IntegerCeilDiv]
  have leftEdge (y : ℤ) (hy : 0 ≤ y) (hyq : y ≤ P.q) :
      FordOdometer P ⟨0,y⟩ = 0 := by
    rw [boundary 0 y (by omega) (by omega) hy hyq (by omega)]
    simp [IntegerCeilDiv]
  have top (x : ℤ) (hx : 0 ≤ x) (hxq : x ≤ P.q) :
      FordOdometer P ⟨x,P.q⟩ = P.p*x := by
    rw [boundary x P.q hx hxq (by omega) (by omega) (by omega)]
    unfold IntegerCeilDiv
    rw [show -(P.p*x*(P.q : ℤ)) = (-(P.p*x))*(P.q : ℤ) by ring,
      Int.mul_ediv_cancel _ hn]
    ring
  have rightEdge (y : ℤ) (hy : 0 ≤ y) (hyq : y ≤ P.q) :
      FordOdometer P ⟨P.q,y⟩ = P.p*y := by
    rw [boundary P.q y (by omega) (by omega) hy hyq (by omega)]
    unfold IntegerCeilDiv
    rw [show -(P.p*(P.q : ℤ)*y) = (-(P.p*y))*(P.q : ℤ) by ring,
      Int.mul_ediv_cancel _ hn]
    ring
  have positive (j : Fin 3) :
      let R := P5332T1RightRows P j 0
      ∃ b : ℤ, ∀ x : GaussianInt,
        x ∈ FordVertexDomain P.q → x-R.displacement ∈ FordVertexDomain P.q →
        FordOdometer P (x-R.displacement) + R.linear.re*x.re +
          R.linear.im*x.im - FordOdometer P x = b := by
    fin_cases j
    · refine ⟨-P.p₁*(P.q : ℤ), ?_⟩
      rintro ⟨x,y⟩ hx hy
      change 0 ≤ x ∧ x ≤ (P.q : ℤ) ∧ 0 ≤ y ∧ y ≤ (P.q : ℤ) at hx
      change 0 ≤ x-(-(P.q₁ : ℤ)) ∧ x-(-(P.q₁ : ℤ)) ≤ (P.q : ℤ) ∧
        0 ≤ y-(P.q : ℤ) ∧ y-(P.q : ℤ) ≤ (P.q : ℤ) at hy
      have he : y = (P.q : ℤ) := by omega
      subst y
      change FordOdometer P (⟨x,P.q⟩-⟨-(P.q₁ : ℤ),P.q⟩) +
        P.p*x+(-P.p₁)*(P.q : ℤ)-FordOdometer P ⟨x,P.q⟩ = _
      rw [show (⟨x,P.q⟩-⟨-(P.q₁ : ℤ),P.q⟩ : GaussianInt) = ⟨x+P.q₁,0⟩ by ext <;> simp,
        bottom _ (by omega) (by omega), top _ hx.1 hx.2.1]
      ring
    · refine ⟨P.p*(P.q₂ : ℤ), ?_⟩
      rintro ⟨x,y⟩ hx hy
      change 0 ≤ x ∧ x ≤ (P.q : ℤ) ∧ 0 ≤ y ∧ y ≤ (P.q : ℤ) at hx
      change 0 ≤ x-(-(P.q₂ : ℤ)) ∧ x-(-(P.q₂ : ℤ)) ≤ (P.q : ℤ) ∧
        0 ≤ y-(-(P.q : ℤ)) ∧ y-(-(P.q : ℤ)) ≤ (P.q : ℤ) at hy
      have he : y = 0 := by omega
      subst y
      change FordOdometer P (⟨x,0⟩-⟨-(P.q₂ : ℤ),-(P.q : ℤ)⟩) +
        (-P.p)*x+(-P.p₂)*0-FordOdometer P ⟨x,0⟩ = _
      rw [show (⟨x,0⟩-⟨-(P.q₂ : ℤ),-(P.q : ℤ)⟩ : GaussianInt) = ⟨x+P.q₂,P.q⟩ by
          ext <;> simp,
        top _ (by omega) (by omega), bottom _ hx.1 hx.2.1]
      ring
    · refine ⟨0, ?_⟩
      rintro ⟨x,y⟩ hx hy
      change 0 ≤ x ∧ x ≤ (P.q : ℤ) ∧ 0 ≤ y ∧ y ≤ (P.q : ℤ) at hx
      change 0 ≤ x-(P.q : ℤ) ∧ x-(P.q : ℤ) ≤ (P.q : ℤ) ∧
        0 ≤ y-0 ∧ y-0 ≤ (P.q : ℤ) at hy
      have he : x = (P.q : ℤ) := by omega
      subst x
      change FordOdometer P (⟨P.q,y⟩-⟨P.q,0⟩) +
        0*(P.q : ℤ)+P.p*y-FordOdometer P ⟨P.q,y⟩ = _
      rw [show (⟨P.q,y⟩-⟨P.q,0⟩ : GaussianInt) = ⟨0,y⟩ by ext <;> simp,
        leftEdge _ hx.2.2.1 hx.2.2.2, rightEdge _ hx.2.2.1 hx.2.2.2]
      ring
  cases e
  · dsimp only [Bool.false_eq_true, ↓reduceIte]
    let R := P5332T1RightRows P j 0
    obtain ⟨b,hb⟩ := positive j
    change ∀ x : GaussianInt, x ∈ FordVertexDomain P.q →
      x-R.displacement ∈ FordVertexDomain P.q →
      FordOdometer P (x-R.displacement) + R.linear.re*x.re +
        R.linear.im*x.im - FordOdometer P x = b at hb
    refine ⟨R.linear.re*R.displacement.re+R.linear.im*R.displacement.im-b, ?_⟩
    intro x hx hy
    have he := hb (x+R.displacement) (by simpa [R] using hy) (by simpa using hx)
    simp only [add_sub_cancel_right, Zsqrtd.re_add, Zsqrtd.im_add] at he
    change FordOdometer P (x-(-R.displacement)) + (-R.linear).re*x.re +
      (-R.linear).im*x.im-FordOdometer P x = _
    simp only [sub_neg_eq_add, Zsqrtd.re_neg, Zsqrtd.im_neg]
    linear_combination -he
  · exact positive j

end ApollonianSuperharmonic

end
