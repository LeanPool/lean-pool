/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueHarmonicPotential

/-!
# ExitMeanValueIdentificationCarrier

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The zero-trace carrier: Poincare inequality, ellipticity and the supremum bound

Three facts about the zero-trace value--gradient carrier are isolated here, all of them used by
the identification of the vanishing-shift limit of the Dirichlet resolvents with a weak solution.

* `ZeroTraceSobolev.exists_poincare_constant` transports the zero-trace Poincare inequality of a
  bounded convex domain from honest zero-trace Sobolev functions to the graph carrier, using the
  realization theorem of the carrier on such domains.
* `mul_norm_gradient_sq_le_coefficientPairing` is the elliptic lower bound of the coefficient
  pairing on the carrier, read off the coercivity estimate of the shifted bilinear form at the
  shift equal to the lower ellipticity constant.
* `norm_scalarL2_le_of_ae_bound` converts an essential supremum bound into an `L²` bound on a
  bounded domain.

None of this is specific to the exhaustion cubes.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ}

/-! ## The Poincare inequality on the carrier -/

namespace ZeroTraceSobolev

/-- **The zero-trace Poincare inequality on the graph carrier.**  On a bounded convex domain
every element of the carrier is realized by an honest zero-trace Sobolev function, so the
Poincare constant of the domain controls the value component by the gradient component. -/
theorem exists_poincare_constant [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ZeroTraceSobolev U, ‖toL2 z‖ ≤ C * ‖gradient z‖ := by
  obtain ⟨C0, hC0, hbound⟩ :=
    H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain (U := U) hU
  refine ⟨C0 * d, by positivity, fun z ↦ ?_⟩
  obtain ⟨u, hvalue, hgrad⟩ := exists_h10Function hU z
  have hsum : u.toH1Function.gradientCoordL2NormSum ≤
      d * ‖u.toH1Function.gradToHilbertVectorL2‖ := by
    calc
      u.toH1Function.gradientCoordL2NormSum ≤ d * ‖u.toH1Function.gradToVectorL2‖ :=
        u.toH1Function.gradientCoordL2NormSum_le
      _ ≤ d * ‖u.toH1Function.gradToHilbertVectorL2‖ :=
        mul_le_mul_of_nonneg_left
          (H1Function.norm_gradToVectorL2_le_norm_gradToHilbertVectorL2
            (U := U) u.toH1Function)
          (Nat.cast_nonneg d)
  rw [← hvalue, ← hgrad]
  calc
    ‖u.toH1Function.toScalarL2‖ ≤ C0 * u.toH1Function.gradientCoordL2NormSum := hbound u
    _ ≤ C0 * (d * ‖u.toH1Function.gradToHilbertVectorL2‖) :=
      mul_le_mul_of_nonneg_left hsum hC0
    _ = C0 * d * ‖u.toH1Function.gradToHilbertVectorL2‖ := by ring

end ZeroTraceSobolev

/-! ## Ellipticity of the coefficient pairing on the carrier -/

section Coercivity

open ZeroTraceSobolev

variable {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}

/-- The coefficient pairing of two carrier gradients is the value of the unshifted bilinear
form. -/
theorem coefficientPairing_gradient_eq_shiftedBilin
    (hEll : IsEllipticFieldOn lam Lam U a) (u w : ZeroTraceSobolev U) :
    coefficientPairing a U (gradient u) (gradient w) = shiftedBilin hEll (0 : ℝ) u w := by
  rw [shiftedBilin_apply]
  ring

/-- **The elliptic lower bound of the coefficient pairing on the carrier.** -/
theorem mul_norm_gradient_sq_le_coefficientPairing
    (hEll : IsEllipticFieldOn lam Lam U a) (u : ZeroTraceSobolev U) :
    lam * ‖gradient u‖ ^ 2 ≤ coefficientPairing a U (gradient u) (gradient u) := by
  have h := shiftedBilin_lower_bound (α := lam) hEll u
  rw [shiftedBilin_apply, min_self] at h
  have hnorm : ‖u‖ * ‖u‖ = ‖toL2 u‖ ^ 2 + ‖gradient u‖ ^ 2 := by
    rw [← pow_two, ZeroTraceSobolev.norm_sq_eq]
  rw [mul_assoc, hnorm, real_inner_self_eq_norm_sq] at h
  linarith only [h]

end Coercivity

/-! ## The supremum-to-`L²` bound -/

/-- The factor converting an essential supremum bound into an `L²` bound on a domain. -/
def scalarL2Factor (U : Set (Vec d)) : ℝ :=
  (MeasureTheory.volume U).toReal ^ (2 : ℝ)⁻¹

theorem scalarL2Factor_nonneg (U : Set (Vec d)) : 0 ≤ scalarL2Factor U :=
  Real.rpow_nonneg ENNReal.toReal_nonneg _

/-- **An essential supremum bound on a bounded domain is an `L²` bound.** -/
theorem norm_scalarL2_le_of_ae_bound {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (F : ScalarL2 U) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ᵐ x ∂volumeMeasureOn U, |F x| ≤ C) :
    ‖F‖ ≤ scalarL2Factor U * C := by
  let := hU.isFiniteMeasure_restrict_volume
  have hbound : ∀ᵐ x ∂volumeMeasureOn U, ‖F x‖ ≤ C := by
    filter_upwards [hF] with x hx
    simpa only [Real.norm_eq_abs] using hx
  have h := MeasureTheory.Lp.norm_le_of_ae_bound
    (μ := volumeMeasureOn U) (p := 2) (f := F) hC hbound
  refine h.trans (le_of_eq ?_)
  have hfactor : ((measureUnivNNReal (volumeMeasureOn U) : ℝ)) =
      (MeasureTheory.volume U).toReal := by
    rw [← ENNReal.coe_toReal, coe_measureUnivNNReal, Measure.restrict_apply_univ]
  rw [scalarL2Factor, hfactor, show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) by norm_num]

end

end DivergenceFormProcess.Form
