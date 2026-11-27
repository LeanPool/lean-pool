/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# A selfadjoint unbounded ratio of commuting bounded operators

The partial operator L(Ax)=Bx has its exact domain range A. The identity
A²+B²=2I closes the adjoint-domain argument algebraically: Az=By implies
(y,z)=(Aw,Bw) for w=(Ay+Bz)/2. No inverse of A is taken in the bounded
operator algebra, and the range of A need not be closed.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Linear map for the bounded ratio. -/
noncomputable def boundedRatio (A B : E →L[ℂ] E) (hA : Function.Injective A) : E →ₗ.[ℂ] E where
  domain := A.range
  toFun := B.toLinearMap.comp (LinearEquiv.ofInjective A.toLinearMap hA).symm.toLinearMap

omit [CompleteSpace E] in
@[simp] theorem boundedRatio_apply_range (A B : E →L[ℂ] E) (hA : Function.Injective A)
    (x : E) : boundedRatio A B hA ⟨A x, ⟨x, rfl⟩⟩ = B x := by
  change B ((LinearEquiv.ofInjective A.toLinearMap hA).symm
    (LinearEquiv.ofInjective A.toLinearMap hA x)) = B x
  rw [LinearEquiv.symm_apply_apply]

omit [CompleteSpace E] in
theorem boundedRatio_representation (A B : E →L[ℂ] E) (hA : Function.Injective A)
    (x : (boundedRatio A B hA).domain) :
    ∃ z, A z = (x : E) ∧ B z = boundedRatio A B hA x := by
  refine ⟨(LinearEquiv.ofInjective A.toLinearMap hA).symm x, ?_, rfl⟩
  exact LinearEquiv.ofInjective_symm_apply _ _

theorem boundedRatio_isFormalAdjoint (A B : E →L[ℂ] E) (hA : Function.Injective A)
    (hAs : IsSelfAdjoint A) (hBs : IsSelfAdjoint B) (hc : Commute A B) :
    (boundedRatio A B hA).IsFormalAdjoint (boundedRatio A B hA) := by
  intro x y
  obtain ⟨u, hu, hBu⟩ := boundedRatio_representation A B hA x
  obtain ⟨v, hv, hBv⟩ := boundedRatio_representation A B hA y
  rw [← hu, ← hv, ← hBu, ← hBv]
  calc
    inner ℂ (B u) (A v) = inner ℂ u (B (A v)) := hBs.isSymmetric u (A v)
    _ = inner ℂ u (A (B v)) := by
      rw [show B (A v) = A (B v) from congrArg (fun T : E →L[ℂ] E => T v) hc.eq.symm]
    _ = inner ℂ (A u) (B v) := (hAs.isSymmetric u (B v)).symm

/-- Exact maximal adjoint, including its domain, from a bounded algebraic identity. -/
theorem boundedRatio_isSelfAdjoint (A B : E →L[ℂ] E) (hA : Function.Injective A)
    (hd : DenseRange A) (hAs : IsSelfAdjoint A) (hBs : IsSelfAdjoint B)
    (hc : Commute A B) (hsq : A * A + B * B = 2) :
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
      have hcomm (v : E) : A (B v) = B (A v) :=
        congrArg (fun Q : E →L[ℂ] E => Q v) hc.eq
      have hsum (v : E) : A (A v) + B (B v) = (2 : ℂ) • v := by
        have hh := congrArg (fun Q : E →L[ℂ] E => Q v) hsq
        simpa only [add_apply, mul_apply_eq_comp, ofNat_apply, two_smul] using hh
      refine ⟨(1 / 2 : ℂ) • (A y + B z), ?_, ?_⟩
      · rw [map_smul, map_add, hcomm z, heq, hsum]
        norm_num [smul_smul, z]
      · rw [map_smul, map_add, ← hcomm y, ← heq, hsum]
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

theorem boundedRatio_isClosed (A B : E →L[ℂ] E) (hA : Function.Injective A)
    (hd : DenseRange A) (hAs : IsSelfAdjoint A) (hBs : IsSelfAdjoint B)
    (hc : Commute A B) (hsq : A * A + B * B = 2) :
    (boundedRatio A B hA).IsClosed :=
  (boundedRatio_isSelfAdjoint A B hA hd hAs hBs hc hsq).isClosed

end VacuumBellSeparation
