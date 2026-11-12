/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FordOdometer
public import LeanPool.ApollonianSuperharmonic.P5130T5ParentArithmetic
public import LeanPool.ApollonianSuperharmonic.P5188T1CeilingBelow

-- [TABLET NODE: P5448T1CanonicalFordBoundary]

/-!
# P5448T1CanonicalFordBoundary

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5448T1CanonicalFordBoundary (F : FordFareyParameter) (hq : 1 < F.q) :
    (∀ t : Int, 0 ≤ t → t ≤ F.q →
      FordOdometer F ⟨t, 0⟩ = 0 ∧
      FordOdometer F ⟨t, (F.q : Int)⟩ = F.p * t) ∧
    FordOdometer F ⟨(F.q₁ : Int), 1⟩ = F.p₁ ∧
    FordOdometer F ⟨(F.q₂ : Int), (F.q : Int) - 1⟩ =
      F.p * (F.q₂ : Int) - F.p₂ := by
-- BODY
  have bounds := P5130T5ParentArithmetic F hq
  have hqi : (1 : Int) < F.q := by exact_mod_cast hq
  have hb := (Classical.choose_spec FordOdometerFamilyExistsUnique).1.2.1 F
  change ∀ z, z ∈ FordDoubledBoundary F.q → FordOdometer F z = _ at hb
  have edge (t : Int) (ht : 0 ≤ t) (htq : t ≤ F.q) :
      FordOdometer F ⟨t, 0⟩ = 0 ∧
      FordOdometer F ⟨t, (F.q : Int)⟩ = F.p * t := by
    have hbot : (⟨t, 0⟩ : GaussianInt) ∈ FordDoubledBoundary F.q := by
      simp only [FordDoubledBoundary, FordVertexDomain, Set.mem_ofPred_eq]
      omega
    have htop : (⟨t, (F.q : Int)⟩ : GaussianInt) ∈ FordDoubledBoundary F.q := by
      simp only [FordDoubledBoundary, FordVertexDomain, Set.mem_ofPred_eq]
      omega
    constructor
    · rw [hb _ hbot]
      simpa using P5188T1CeilingBelow 0 0 (F.q : Int) (by omega)
        (by omega) (by omega)
    · rw [hb _ htop]
      simpa using P5188T1CeilingBelow (F.p * t) 0 (F.q : Int)
        (by omega) (by omega) (by omega)
  refine ⟨edge, ?_, ?_⟩
  · have hm : (⟨(F.q₁ : Int), 1⟩ : GaussianInt) ∈ FordDoubledBoundary F.q := by
      simp only [FordDoubledBoundary, FordVertexDomain, Set.mem_ofPred_eq]
      omega
    rw [hb _ hm]
    have he : F.p * (F.q₁ : Int) * 1 = F.p₁ * (F.q : Int) - 1 := by
      nlinarith [F.det₁]
    change IntegerCeilDiv (F.p * (F.q₁ : Int) * 1) (F.q : Int) _ = _
    rw [he]
    exact P5188T1CeilingBelow F.p₁ 1 (F.q : Int) (by omega)
      (by omega) (by omega)
  · have hm : (⟨(F.q₂ : Int), (F.q : Int) - 1⟩ : GaussianInt) ∈
        FordDoubledBoundary F.q := by
      simp only [FordDoubledBoundary, FordVertexDomain, Set.mem_ofPred_eq]
      omega
    rw [hb _ hm]
    have he : F.p * (F.q₂ : Int) * ((F.q : Int) - 1) =
        (F.p * (F.q₂ : Int) - F.p₂) * (F.q : Int) - 1 := by
      nlinarith [F.det₂]
    change IntegerCeilDiv (F.p * (F.q₂ : Int) * ((F.q : Int) - 1))
      (F.q : Int) _ = _
    rw [he]
    exact P5188T1CeilingBelow (F.p * (F.q₂ : Int) - F.p₂) 1
      (F.q : Int) (by omega) (by omega) (by omega)

end ApollonianSuperharmonic

end
