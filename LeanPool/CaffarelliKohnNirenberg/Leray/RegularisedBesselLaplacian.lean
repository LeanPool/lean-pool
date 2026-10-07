/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselEmbedding
public import Mathlib.Analysis.Distribution.FourierMultiplier

/-!
# The second-order Bessel operator and the Laplacian

At integer order two, the Bessel Fourier symbol is the sum of the
identity and the quadratic frequency symbol. This identifies the
complete Sobolev weight with physical second derivatives.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap Laplacian

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The Bessel potential of order two is the identity plus the quadratic
frequency multiplier on tempered distributions. -/
theorem regularised_besselPotential_two_eq_add_frequencySq
    (D : 𝓢'(L2Vec3, ComplexVec3)) :
    TemperedDistribution.besselPotential L2Vec3 ComplexVec3 2 D =
      D + TemperedDistribution.fourierMultiplierCLM ComplexVec3
        (fun ξ : L2Vec3 => ((‖ξ‖ ^ 2 : ℝ) : ℂ)) D := by
  let q : L2Vec3 → ℂ := fun ξ => ((‖ξ‖ ^ 2 : ℝ) : ℂ)
  have hq : q.HasTemperateGrowth := by
    dsimp [q]
    fun_prop
  have hOne : (fun _ξ : L2Vec3 => (1 : ℂ)).HasTemperateGrowth := by
    fun_prop
  have hSymbol : (fun ξ : L2Vec3 =>
      (((1 + ‖ξ‖ ^ 2) ^ ((2 : ℝ) / 2) : ℝ) : ℂ)) =
      (fun ξ => (1 : ℂ) + q ξ) := by
    funext ξ
    simp [q]
  rw [TemperedDistribution.besselPotential,
    TemperedDistribution.fourierMultiplierCLM_apply, hSymbol]
  change 𝓕⁻ ((TemperedDistribution.smulLeftCLM ComplexVec3
      ((fun _ξ : L2Vec3 => (1 : ℂ)) + q)) (𝓕 D)) = _
  rw [TemperedDistribution.smulLeftCLM_add hOne hq,
    add_apply, fourierInv_add]
  simp only [TemperedDistribution.smulLeftCLM_const,
    one_smul, fourierInv_fourier_eq]
  rfl

/-- The second-order Bessel operator is the scaled identity minus the
distributional Laplacian. -/
theorem regularised_besselPotential_two_laplacian_identity
    (D : 𝓢'(L2Vec3, ComplexVec3)) :
    ((2 * Real.pi) ^ 2 : ℝ) •
      TemperedDistribution.besselPotential L2Vec3 ComplexVec3 2 D =
      ((2 * Real.pi) ^ 2 : ℝ) • D - Laplacian.laplacian D := by
  rw [regularised_besselPotential_two_eq_add_frequencySq,
    smul_add, TemperedDistribution.laplacian_eq_fourierMultiplierCLM]
  simp only [neg_smul, sub_neg_eq_add]

end CKN.Leray

end
