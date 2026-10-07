/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Complex.Basic

/-!
# Extension of bounded bilinear maps from dense linear cores

A bilinear map bounded through two dense linear embeddings extends
uniquely to a continuous bilinear map on the complete target spaces.
-/

public section

noncomputable section

namespace CKN.Leray

variable {V W X Y Z : Type*}
  [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]

/-- A bounded bilinear map on two dense linear cores has a continuous
bilinear extension with the same norm bound. -/
theorem regularised_bilinear_dense_extension
    (eV : V →ₗ[ℂ] X) (eW : W →ₗ[ℂ] Y)
    (heV : DenseRange eV) (heW : DenseRange eW)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] Z)
    (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ v w, ‖B v w‖ ≤ C * ‖eV v‖ * ‖eW w‖) :
    ∃ F : X →L[ℂ] Y →L[ℂ] Z,
      ‖F‖ ≤ C ∧ ∀ v w, F (eV v) (eW w) = B v w := by
  let hFirst (w : W) : ∀ v, ‖B.flip w v‖ ≤
      (C * ‖eW w‖) * ‖eV v‖ := by
    intro v
    simpa only [LinearMap.flip_apply, mul_assoc, mul_comm, mul_left_comm]
      using hBound v w
  let first (w : W) : X →L[ℂ] Z :=
    (B.flip w).extendOfNorm eV
  have hFirstEq (w : W) (v : V) : first w (eV v) = B v w := by
    change (B.flip w).extendOfNorm eV (eV v) = B v w
    rw [LinearMap.extendOfNorm_eq heV ⟨C * ‖eW w‖, hFirst w⟩]
    rfl
  have hFirstNorm (w : W) : ‖first w‖ ≤ C * ‖eW w‖ := by
    exact LinearMap.opNorm_extendOfNorm_le heV
      (mul_nonneg hC (norm_nonneg _)) (hFirst w)
  let L : W →ₗ[ℂ] (X →L[ℂ] Z) := {
    toFun := first
    map_add' := by
      intro w w'
      apply ContinuousLinearMap.ext
      intro x
      change first (w + w') x = (first w + first w') x
      refine heV.induction_on (p := fun y =>
        first (w + w') y = (first w + first w') y) x ?_ ?_
      · exact isClosed_eq (first (w + w')).continuous
          (first w + first w').continuous
      · intro v
        simp only [hFirstEq, map_add, add_apply]
    map_smul' := by
      intro c w
      apply ContinuousLinearMap.ext
      intro x
      change first (c • w) x = (c • first w) x
      refine heV.induction_on (p := fun y =>
        first (c • w) y = (c • first w) y) x ?_ ?_
      · exact isClosed_eq (first (c • w)).continuous
          (c • first w).continuous
      · intro v
        simp only [hFirstEq, map_smul, smul_apply]
  }
  have hLBound (w : W) : ‖L w‖ ≤ C * ‖eW w‖ := hFirstNorm w
  let G : Y →L[ℂ] (X →L[ℂ] Z) := by
    exact LinearMap.extendOfNorm (σ₁₂ := RingHom.id ℂ) L eW
  have hGNorm : ‖G‖ ≤ C :=
    LinearMap.opNorm_extendOfNorm_le heW hC hLBound
  refine ⟨G.flip, ?_, ?_⟩
  · simpa only [ContinuousLinearMap.opNorm_flip] using hGNorm
  · intro v w
    change G (eW w) (eV v) = B v w
    rw [LinearMap.extendOfNorm_eq heW ⟨C, hLBound⟩]
    exact hFirstEq w v

end CKN.Leray

end
