/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.BoundedRatioOperator
public import Mathlib.Algebra.GroupWithZero.Commute

/-!
# Maximal bounded ratios and their intrinsic resolvent

For commuting bounded selfadjoint A,B, injective A with dense range, and
boundedly invertible A+B, the operator L(Ax)=Bx is selfadjoint on its full
range domain. Its actual inverse (1+L)⁻¹ is A(A+B)⁻¹. Neither A nor B is
assumed to have a bounded inverse. These results support a resolvent-based
extended continuous calculus for positive unbounded operators.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem commute_ringInverse_of_isUnit (A Q : E →L[ℂ] E)
    (hc : Commute A Q) (hQ : IsUnit Q) : Commute A (Ring.inverse Q) := by
  rw [Ring.inverse_of_isUnit hQ]
  apply Commute.units_inv_right
  simpa only [IsUnit.unit_spec] using hc

omit [CompleteSpace E] in
/-- A bounded reconstruction proves that the weak graph equation is maximal. -/
theorem boundedRatio_graph_equation (A B : E →L[ℂ] E) (hA : Function.Injective A)
    (hc : Commute A B) (hQ : IsUnit (A + B)) (x y : E) :
    (∃ hx : x ∈ (boundedRatio A B hA).domain, boundedRatio A B hA ⟨x, hx⟩ = y) ↔
      A y = B x := by
  constructor
  · rintro ⟨hx, hy⟩
    obtain ⟨w, hw, hBw⟩ := boundedRatio_representation A B hA ⟨x, hx⟩
    change A w = x at hw
    rw [← hy, ← hBw, ← hw]
    exact congrArg (fun Q : E →L[ℂ] E => Q w) hc.eq
  · intro heq
    let Q := A + B
    let w := Ring.inverse Q (x + y)
    have hAi : Commute A (Ring.inverse Q) :=
      commute_ringInverse_of_isUnit A Q ((Commute.refl A).add_right hc) hQ
    have hBi : Commute B (Ring.inverse Q) :=
      commute_ringInverse_of_isUnit B Q (hc.symm.add_right (Commute.refl B)) hQ
    have hinv (v : E) : Ring.inverse Q (Q v) = v := by
      simpa only [mul_apply_eq_comp, one_apply_eq_self] using
        congrArg (fun T : E →L[ℂ] E => T v) (Ring.inverse_mul_cancel Q hQ)
    have hw : A w = x := by
      change (A * Ring.inverse Q) (x + y) = x
      rw [hAi.eq]
      change Ring.inverse Q (A (x + y)) = x
      rw [map_add, heq]
      exact hinv x
    have hBw : B w = y := by
      change (B * Ring.inverse Q) (x + y) = y
      rw [hBi.eq]
      change Ring.inverse Q (B (x + y)) = y
      rw [map_add, ← heq]
      exact hinv y
    refine ⟨⟨w, hw⟩, ?_⟩
    have hh : (⟨x, ⟨w, hw⟩⟩ : (boundedRatio A B hA).domain) =
        ⟨A w, ⟨w, rfl⟩⟩ := Subtype.ext hw.symm
    rw [hh, boundedRatio_apply_range, hBw]

theorem boundedRatio_isSelfAdjoint_of_isUnit_add (A B : E →L[ℂ] E)
    (hA : Function.Injective A) (hd : DenseRange A)
    (hAs : IsSelfAdjoint A) (hBs : IsSelfAdjoint B)
    (hc : Commute A B) (hQ : IsUnit (A + B)) :
    IsSelfAdjoint (boundedRatio A B hA) := by
  let T := boundedRatio A B hA
  have hdom : Dense (T.domain : Set E) := hd
  have hsym : T.IsFormalAdjoint T := boundedRatio_isFormalAdjoint A B hA hAs hBs hc
  have hle : T ≤ T.adjoint := LinearPMap.IsFormalAdjoint.le_adjoint hdom hsym
  have hrev : T.adjoint ≤ T := by
    have hrep (y : T.adjoint.domain) :
        ∃ hy : (y : E) ∈ T.domain, T ⟨y, hy⟩ = T.adjoint y := by
      apply (boundedRatio_graph_equation A B hA hc hQ _ _).mpr
      apply ext_inner_right ℂ
      intro x
      calc
        inner ℂ (A (T.adjoint y)) x = inner ℂ (T.adjoint y) (A x) := hAs.isSymmetric _ _
        _ = inner ℂ (y : E) (B x) := by
          simpa only [T, boundedRatio_apply_range] using
            (LinearPMap.adjoint_isFormalAdjoint (T := T) hdom y ⟨A x, ⟨x, rfl⟩⟩)
        _ = inner ℂ (B y) x := (hBs.isSymmetric y x).symm
    refine ⟨fun y hy => (hrep ⟨y, hy⟩).choose, ?_⟩
    intro y y' hyy'
    obtain ⟨hy, hh⟩ := hrep y
    have he : y' = (⟨(y : E), hy⟩ : T.domain) := Subtype.ext hyy'.symm
    rw [he]
    exact hh.symm
  change T.adjoint = T
  exact le_antisymm hrev hle

omit [CompleteSpace E] in
/-- Characterization of the actual resolvent, including its domain witness. -/
theorem boundedRatio_resolvent_iff (A B : E →L[ℂ] E) (hA : Function.Injective A)
    (hQ : IsUnit (A + B)) (x y : E) :
    (∃ hy : y ∈ (boundedRatio A B hA).domain,
      y + boundedRatio A B hA ⟨y, hy⟩ = x) ↔
        (A * Ring.inverse (A + B)) x = y := by
  have hinv (v : E) : Ring.inverse (A + B) ((A + B) v) = v := by
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using
      congrArg (fun T : E →L[ℂ] E => T v) (Ring.inverse_mul_cancel (A + B) hQ)
  have hinv' (v : E) : (A + B) (Ring.inverse (A + B) v) = v := by
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using
      congrArg (fun T : E →L[ℂ] E => T v) (Ring.mul_inverse_cancel (A + B) hQ)
  constructor
  · rintro ⟨hy, heq⟩
    obtain ⟨w, hw, hBw⟩ := boundedRatio_representation A B hA ⟨y, hy⟩
    have hx : (A + B) w = x := by simpa only [add_apply, hw, hBw] using heq
    rw [← hx, mul_apply_eq_comp, hinv, hw]
  · intro heq
    let w := Ring.inverse (A + B) x
    have hw : A w = y := heq
    refine ⟨⟨w, hw⟩, ?_⟩
    have hh : (⟨y, ⟨w, hw⟩⟩ : (boundedRatio A B hA).domain) =
        ⟨A w, ⟨w, rfl⟩⟩ := Subtype.ext hw.symm
    rw [hh, boundedRatio_apply_range, ← hw]
    exact hinv' x

end VacuumBellSeparation
