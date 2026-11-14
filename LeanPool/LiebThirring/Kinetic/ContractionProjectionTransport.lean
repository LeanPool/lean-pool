/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Transport of Hilbert-space range projections

This module records the operator algebra transporting `I I†` through linear isometric
equivalences. It also specializes the result to an operator pulled back along an equivalence.
-/

public section

open scoped InnerProduct

namespace LiebThirring

variable {E H Y X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

theorem projection_conj_eq_of_intertwining
    (C : E ≃ₗᵢ[ℂ] Y) (R : H ≃ₗᵢ[ℂ] X)
    (I : H →L[ℂ] E) (A : X →L[ℂ] Y)
    (h : (C : E →L[ℂ] Y) ∘L I = A ∘L (R : H →L[ℂ] X)) :
    (C : E →L[ℂ] Y) ∘L (I ∘L I.adjoint) ∘L (C : E →L[ℂ] Y).adjoint =
      A ∘L A.adjoint := by
  calc
    (C : E →L[ℂ] Y) ∘L (I ∘L I.adjoint) ∘L (C : E →L[ℂ] Y).adjoint =
        ((C : E →L[ℂ] Y) ∘L I) ∘L ((C : E →L[ℂ] Y) ∘L I).adjoint := by
      simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]
    _ = (A ∘L (R : H →L[ℂ] X)) ∘L (A ∘L (R : H →L[ℂ] X)).adjoint :=
      congrArg (fun T => T ∘L T.adjoint) h
    _ = A ∘L A.adjoint := by
      simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
        LinearIsometryEquiv.adjoint_eq_symm]
      rw [← ContinuousLinearMap.comp_assoc (R : H →L[ℂ] X) (R.symm : X →L[ℂ] H)]
      simp

theorem projection_transport_apply
    (C : E ≃ₗᵢ[ℂ] Y) (R : H ≃ₗᵢ[ℂ] X)
    (I : H →L[ℂ] E) (A : X →L[ℂ] Y)
    (h : (C : E →L[ℂ] Y) ∘L I = A ∘L (R : H →L[ℂ] X)) (ψ : E) :
    (C : E →L[ℂ] Y) ((I ∘L I.adjoint) ψ) =
      (A ∘L A.adjoint) ((C : E →L[ℂ] Y) ψ) := by
  have hop := projection_conj_eq_of_intertwining C R I A h
  have hψ := congrArg (fun T => T ((C : E →L[ℂ] Y) ψ)) hop
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.adjoint_eq_symm] at hψ
  rw [show (C.symm : Y →L[ℂ] E) ((C : E →L[ℂ] Y) ψ) = ψ from
    C.symm_apply_apply ψ] at hψ
  exact hψ

theorem projection_symm_comp
    (C : E ≃ₗᵢ[ℂ] Y) (D : H →L[ℂ] Y) :
    ((C.symm : Y →L[ℂ] E) ∘L D) ∘L ((C.symm : Y →L[ℂ] E) ∘L D).adjoint =
      (C.symm : Y →L[ℂ] E) ∘L (D ∘L D.adjoint) ∘L (C : E →L[ℂ] Y) := by
  simp only [ContinuousLinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm,
    LinearIsometryEquiv.symm_symm, ContinuousLinearMap.comp_assoc]

theorem projection_conj_symm_comp
    (C : E ≃ₗᵢ[ℂ] Y) (D : H →L[ℂ] Y) :
    (C : E →L[ℂ] Y) ∘L
        (((C.symm : Y →L[ℂ] E) ∘L D) ∘L
          ((C.symm : Y →L[ℂ] E) ∘L D).adjoint) ∘L
        (C : E →L[ℂ] Y).adjoint = D ∘L D.adjoint := by
  rw [projection_symm_comp]
  simp only [LinearIsometryEquiv.adjoint_eq_symm, ContinuousLinearMap.comp_assoc]
  rw [← ContinuousLinearMap.comp_assoc (C : E →L[ℂ] Y) (C.symm : Y →L[ℂ] E)]
  simp

theorem projection_pullback_apply
    (C : E ≃ₗᵢ[ℂ] Y) (D : H →L[ℂ] Y) (ψ : E) :
    (C : E →L[ℂ] Y)
        ((((C.symm : Y →L[ℂ] E) ∘L D) ∘L
          ((C.symm : Y →L[ℂ] E) ∘L D).adjoint) ψ) =
      (D ∘L D.adjoint) ((C : E →L[ℂ] Y) ψ) := by
  have hop := projection_conj_symm_comp C D
  have hψ := congrArg (fun T => T ((C : E →L[ℂ] Y) ψ)) hop
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.adjoint_eq_symm] at hψ
  rw [show (C.symm : Y →L[ℂ] E) ((C : E →L[ℂ] Y) ψ) = ψ from
    C.symm_apply_apply ψ] at hψ
  exact hψ

end LiebThirring
