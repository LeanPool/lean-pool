/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import Mathlib.Analysis.RCLike.Inner

/-! # Pairing of finite orthonormal synthesis -/

@[expose] public section

namespace LeanDirac.V2

open BigOperators
open scoped InnerProductSpace
noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜] {Site Mode : Type*}

private theorem wInner_cWeight_fintype_sum_left
    [Fintype Mode] [Fintype Site]
    (field : Mode → Site → 𝕜) (target : Site → 𝕜) :
    ⟪(fun site => ∑ mode, field mode site), target⟫ₙ_[𝕜] =
      ∑ mode, ⟪field mode, target⟫ₙ_[𝕜] := by
  simp_rw [RCLike.wInner_cWeight_eq_expect, RCLike.inner_apply, map_sum, Finset.mul_sum]
  rw [Finset.expect_sum_comm]

private theorem wInner_cWeight_fintype_sum_right
    [Fintype Mode] [Fintype Site]
    (source : Site → 𝕜) (field : Mode → Site → 𝕜) :
    ⟪source, (fun site => ∑ mode, field mode site)⟫ₙ_[𝕜] =
      ∑ mode, ⟪source, field mode⟫ₙ_[𝕜] := by
  simp_rw [RCLike.wInner_cWeight_eq_expect, RCLike.inner_apply, Finset.sum_mul]
  rw [Finset.expect_sum_comm]

/-- Synthesize a scalar field from its coefficients in a finite family of functions. -/
def finiteFrameSynthesis [Fintype Mode] (frame : Mode → Site → 𝕜) (coefficient : Mode → 𝕜) :
    Site → 𝕜 := fun site => ∑ mode, frame mode site * coefficient mode

/-- Pair two scaled members of a family orthonormal for the normalized finite pairing. -/
theorem finite_frame_scaled_pairing [Fintype Site] [DecidableEq Mode]
    (frame : Mode → Site → 𝕜)
    (orthonormal : ∀ first second, ⟪frame first, frame second⟫ₙ_[𝕜] =
      if first = second then 1 else 0)
    (first second : Mode) (a b : 𝕜) :
    ⟪(fun site => frame first site * a), (fun site => frame second site * b)⟫ₙ_[𝕜] =
      if first = second then star a * b else 0 := by
  rw [show (fun site => frame first site * a) = a • frame first by
    funext site
    exact mul_comm _ _]
  rw [show (fun site => frame second site * b) = b • frame second by
    funext site
    exact mul_comm _ _]
  rw [RCLike.wInner_smul_left, RCLike.wInner_smul_right, orthonormal]
  split <;> simp [smul_eq_mul]

/-- Synthesis in an arbitrary finite orthonormal family preserves scalar pairings. -/
theorem finite_frame_synthesis_pairing [Fintype Mode] [Fintype Site] [DecidableEq Mode]
    (frame : Mode → Site → 𝕜)
    (orthonormal : ∀ first second, ⟪frame first, frame second⟫ₙ_[𝕜] =
      if first = second then 1 else 0)
    (first second : Mode → 𝕜) :
    ⟪finiteFrameSynthesis frame first, finiteFrameSynthesis frame second⟫ₙ_[𝕜] =
      ∑ mode, star (first mode) * second mode := by
  unfold finiteFrameSynthesis
  rw [wInner_cWeight_fintype_sum_left]
  apply Finset.sum_congr rfl
  intro mode _
  rw [wInner_cWeight_fintype_sum_right]
  simp [finite_frame_scaled_pairing frame orthonormal]

end
end LeanDirac.V2
