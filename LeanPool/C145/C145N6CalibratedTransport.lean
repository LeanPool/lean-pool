/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145N6PhysicalWitness
public import LeanPool.C145.C145CoordinatePermutation

/-!
# Calibrated transport for the explicit six-vertex source.
-/

@[expose] public section
noncomputable section
namespace C145N6Frame
open scoped BigOperators
open C145CoordinatePermutation

theorem saved_response_cubic_equality (μ : ℝ) (Q : Fin 6 → Fin 6 → ℝ)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q)
    (hground : ∀ v, Q v 0 = 1 / Real.sqrt 6)
    (hresponse : C145.H2.SamePositive (C145.H2.fullRates μ C145N6.rates)
      (C145PhysicalFrame.T frame overlap) (C145PhysicalFrame.T Q overlap)) :
    C145PhysicalFrame.C frame = C145PhysicalFrame.C Q := by
  have he := (actual_tensor_saved_base).trans (saved_frame_response_unique μ Q hQ hground
    hresponse).symm
  funext i j k
  have h := congrFun (congrFun (congrFun he i) j) k
  exact (mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (overlap_nonzero i) (overlap_nonzero j))
    (overlap_nonzero k))) h

theorem saved_spectralPort : spectralPort overlap frame = port := by
  funext v
  simp only [spectralPort, overlap_frame_feature]
  fin_cases v <;> norm_num [feature, helmert, numerator, gramWeight, port, Fin.sum_univ_succ]

/-- One common vertex permutation transports all reconstructed spectral data.
The competitor's vertex port is reconstructed, not assumed equal coordinatewise. -/
theorem calibrated_response_spectral_transport (μ : ℝ) (Q : Fin 6 → Fin 6 → ℝ)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q)
    (hground : ∀ v, Q v 0 = 1 / Real.sqrt 6)
    (hresponse : C145.H2.SamePositive (C145.H2.fullRates μ C145N6.rates)
      (C145PhysicalFrame.T frame overlap) (C145PhysicalFrame.T Q overlap)) :
    ∃ π : Equiv.Perm (Fin 6),
      (∀ w v, transport frame Q w v = if w = π v then 1 else 0) ∧
      (∀ v i, Q (π v) i = frame v i) ∧
      (∀ v u, spectralGenerator (C145.H2.fullRates μ C145N6.rates) Q (π v) (π u) =
        spectralGenerator (C145.H2.fullRates μ C145N6.rates) frame v u) ∧
      (∀ v, spectralPort overlap Q (π v) = port v) ∧
      (∀ v u, decayLaplacian μ (C145.H2.fullRates μ C145N6.rates) Q (π v) (π u) =
        decayLaplacian μ (C145.H2.fullRates μ C145N6.rates) frame v u) := by
  obtain ⟨π,hπ,hrow,hgen,hport,hlap⟩ := cubic_equality_spectral_transport frame Q
    frame_orthonormal hQ
    (saved_response_cubic_equality μ Q hQ hground hresponse) (C145.H2.fullRates μ C145N6.rates)
      overlap μ
  exact ⟨π,hπ,hrow,hgen,by simpa only [saved_spectralPort] using hport,hlap⟩
end C145N6Frame

end
