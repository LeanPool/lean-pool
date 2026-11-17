/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5130T5Prescription
public import LeanPool.ApollonianSuperharmonic.FordDoubledBoundary
public import LeanPool.ApollonianSuperharmonic.IntegerCeilDiv
public import LeanPool.ApollonianSuperharmonic.P5188T1E1Boundary
public import LeanPool.ApollonianSuperharmonic.P5188T1E2Boundary
public import LeanPool.ApollonianSuperharmonic.P5188T1E3E4Boundary
public import LeanPool.ApollonianSuperharmonic.FordRecursiveVertexDomains

-- [TABLET NODE: P5130T5BoundaryConsistency]

/-!
# P5130T5BoundaryConsistency

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5130T5BoundaryConsistency (P P₁ P₂ : FordFareyParameter)
    (hq : 1 < P.q) (hp₁ : P₁.p = P.p₁) (hq₁ : P₁.q = P.q₁)
    (hp₂ : P₂.p = P.p₂) (hq₂ : P₂.q = P.q₂)
    (g₁ g₂ : IntegerLatticeFunction)
    (h₁ : ∀ x ∈ FordDoubledBoundary P₁.q,
      g₁ x = IntegerCeilDiv (P₁.p * x.re * x.im) P₁.q (by exact_mod_cast P₁.q_pos.ne'))
    (h₂ : ∀ x ∈ FordDoubledBoundary P₂.q,
      g₂ x = IntegerCeilDiv (P₂.p * x.re * x.im) P₂.q (by exact_mod_cast P₂.q_pos.ne')) :
    ∀ i x, x ∈ FordRecursiveVertexDomains P i → x ∈ FordDoubledBoundary P.q →
      P5130T5Prescription P g₁ g₂ i x =
        IntegerCeilDiv (P.p * x.re * x.im) P.q (by exact_mod_cast P.q_pos.ne') := by
-- BODY
  have hlast := P5188T1E3E4Boundary P P₂ hq hp₂ hq₂ g₂ h₂
  intro i x hdom hbd
  fin_cases i
  · exact P5188T1E1Boundary P P₁ hq hp₁ hq₁ g₁ h₁ x hdom hbd
  · exact P5188T1E2Boundary P P₁ hq hp₁ hq₁ g₁ h₁ x hdom hbd
  · exact hlast.1 x hdom hbd
  · exact hlast.2 x hdom hbd

end ApollonianSuperharmonic

end
