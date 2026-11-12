/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FordOdometer
public import LeanPool.ApollonianSuperharmonic.FordDoubledBoundary
public import LeanPool.ApollonianSuperharmonic.FordVertexDomain
public import LeanPool.ApollonianSuperharmonic.P4217T2RectangularBoundarySlope

-- [TABLET NODE: P5491T1FordBoundarySlope]

/-!
# P5491T1FordBoundarySlope

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5491T1FordBoundarySlope (P : FordFareyParameter)
    (h : PartialOdometer)
    (hd : (h.domain : Set GaussianInt) = FordVertexDomain P.q)
    (hv : ∀ x, x ∈ h.domain → h.value x = FordOdometer P x) :
    PartialOdometerSlope h = some ((P.p : ℝ)/2, (P.p : ℝ)/2) := by
-- BODY
  have hqn : (P.q : ℤ) ≠ 0 := by exact_mod_cast P.q_pos.ne'
  have boundary (x y : ℤ) (hx : 0 ≤ x) (hxq : x ≤ P.q)
      (hy : 0 ≤ y) (hyq : y ≤ P.q)
      (hb : x = 0 ∨ x = P.q ∨ y = 0 ∨ y = P.q) :
      h.value ⟨x,y⟩ = IntegerCeilDiv (P.p*x*y) P.q hqn := by
    rw [hv _ (by change (⟨x,y⟩ : GaussianInt) ∈ (h.domain : Set GaussianInt)
                 rw [hd]; exact ⟨hx,hxq,hy,hyq⟩)]
    apply (Classical.choose_spec FordOdometerFamilyExistsUnique).1.2.1
    change (0 ≤ x ∧ x ≤ (P.q : ℤ) ∧ 0 ≤ y ∧ y ≤ (P.q : ℤ)) ∧
      ¬ (2 ≤ x ∧ x ≤ (P.q : ℤ)-2 ∧ 2 ≤ y ∧ y ≤ (P.q : ℤ)-2)
    omega
  have hz (y : ℤ) (hy : 0 ≤ y) (hyq : y ≤ P.q) : h.value ⟨0,y⟩ = 0 := by
    rw [boundary 0 y (by omega) (by omega) hy hyq (Or.inl rfl)]
    simp [IntegerCeilDiv]
  have hright (y : ℤ) (hy : 0 ≤ y) (hyq : y ≤ P.q) :
      h.value ⟨P.q,y⟩ = P.p*y := by
    rw [boundary P.q y (by omega) (by omega) hy hyq (Or.inr (Or.inl rfl))]
    unfold IntegerCeilDiv
    rw [show -(P.p*(P.q : ℤ)*y) = (-(P.p*y))*(P.q : ℤ) by ring,
      Int.mul_ediv_cancel _ hqn]
    ring
  have hbottom (x : ℤ) (hx : 0 ≤ x) (hxq : x ≤ P.q) : h.value ⟨x,0⟩ = 0 := by
    rw [boundary x 0 hx hxq (by omega) (by omega) (Or.inr (Or.inr (Or.inl rfl)))]
    simp [IntegerCeilDiv]
  have htop (x : ℤ) (hx : 0 ≤ x) (hxq : x ≤ P.q) :
      h.value ⟨x,P.q⟩ = P.p*x := by
    rw [boundary x P.q hx hxq (by omega) (by omega) (Or.inr (Or.inr (Or.inr rfl)))]
    unfold IntegerCeilDiv
    rw [show -(P.p*x*(P.q : ℤ)) = (-(P.p*x))*(P.q : ℤ) by ring,
      Int.mul_ediv_cancel _ hqn]
    ring
  have hs := P4217T2RectangularBoundarySlope h P.q P.q P.q_pos P.q_pos
    P.p P.p hd hz hright hbottom htop
  have hn : (P.q : ℝ) ≠ 0 := by exact_mod_cast P.q_pos.ne'
  convert hs using 2; field_simp

end ApollonianSuperharmonic

end
