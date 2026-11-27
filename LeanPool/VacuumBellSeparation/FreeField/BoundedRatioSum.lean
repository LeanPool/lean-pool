/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.BoundedRatioOperator

/-!
# Selfadjointness of a ratio with complementary bounded denominator

For commuting selfadjoint A,B with A+B=2I, the adjoint-domain equation
Az=By is solved exactly by w=(y+z)/2. This proves maximal selfadjointness
of L(Ax)=Bx on range A even when A has no bounded inverse.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem boundedRatio_isSelfAdjoint_of_sum_eq_two (A B : E →L[ℂ] E)
    (hA : Function.Injective A) (hd : DenseRange A)
    (hAs : IsSelfAdjoint A) (hBs : IsSelfAdjoint B)
    (hc : Commute A B) (hsum : A + B = 2) :
    IsSelfAdjoint (boundedRatio A B hA) := by
  let T := boundedRatio A B hA
  have hdom : Dense (T.domain : Set E) := hd
  have hsym : T.IsFormalAdjoint T := boundedRatio_isFormalAdjoint A B hA hAs hBs hc
  have hle : T ≤ T.adjoint := LinearPMap.IsFormalAdjoint.le_adjoint hdom hsym
  have hrev : T.adjoint ≤ T := by
    have hrep (y : T.adjoint.domain) :
        ∃ w, A w = (y : E) ∧ B w = T.adjoint y := by
      let z := T.adjoint y
      have heq : A z = B y := by
        apply ext_inner_right ℂ
        intro x
        calc
          inner ℂ (A z) x = inner ℂ z (A x) := hAs.isSymmetric z x
          _ = inner ℂ (y : E) (B x) := by
            simpa only [T, boundedRatio_apply_range] using
              (LinearPMap.adjoint_isFormalAdjoint (T := T) hdom y ⟨A x, ⟨x, rfl⟩⟩)
          _ = inner ℂ (B y) x := (hBs.isSymmetric y x).symm
      have hsum' (v : E) : A v + B v = (2 : ℂ) • v := by
        simpa only [add_apply, ofNat_apply, two_smul] using
          congrArg (fun Q : E →L[ℂ] E => Q v) hsum
      refine ⟨(1 / 2 : ℂ) • ((y : E) + z), ?_, ?_⟩
      · rw [map_smul, map_add, heq, hsum']
        norm_num [smul_smul, z]
      · rw [map_smul, map_add, ← heq, hsum']
        norm_num [smul_smul, z]
    refine ⟨?_, ?_⟩
    · intro y hy
      obtain ⟨w, hw, _⟩ := hrep ⟨y, hy⟩
      exact ⟨w, hw⟩
    · intro y y' hyy'
      obtain ⟨w, hw, hz⟩ := hrep y
      have hy' : y' = (⟨A w, ⟨w, rfl⟩⟩ : T.domain) :=
        Subtype.ext (hyy'.symm.trans hw.symm)
      rw [hy']
      exact hz.symm.trans (boundedRatio_apply_range A B hA w).symm
  change T.adjoint = T
  exact le_antisymm hrev hle

end VacuumBellSeparation
