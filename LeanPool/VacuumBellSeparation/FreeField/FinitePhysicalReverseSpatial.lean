/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.FinitePhysicalReverseRenyi
public import LeanPool.VacuumBellSeparation.FreeField.FinitePhysicalEventBounds
public import LeanPool.VacuumBellSeparation.FreeField.JointReverseReserveFactor

/-!
# Reverse estimates on the actual finite physical source algebras

The original joint-source factor constructs the intrinsic perturbation bound
for every canonical subsystem. The final existence theorem discharges the
factor using the genuine uniform reverse reserve construction. No Gaussian
representation, inverse, or approximation hypothesis remains.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open Gaussian
open scoped ENNReal InnerProductSpace Matrix.Norms.L2Operator

variable {μ s : ℝ} (hμ : 0 < μ) (hs : 600 ≤ s)
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (V : FreeFieldVacuum μ H)
  {U W : Set (EuclideanSpace ℝ (Fin 3))}
  (hU : U ⊆ Metric.ball 0 1)
  (hW : W ⊆ Metric.ball (spatialAxisDisplacement s 0) 1)
  (hUW : Disjoint U W) (S T : Submodule ℝ TimeZeroSource)
  (hS : IsCanonicalSourceSystem U S) (hT : IsCanonicalSourceSystem W T)

include hU hW hUW hS hT in
/-- The remaining input here is the literal full-source factorization.
The next theorem constructs that factor uniformly. -/
theorem finite_physical_reverse_model_of_source_factor
    {ε : ℝ} (hε : 0 ≤ ε) (hsmall : (thermalConst aRev)⁻¹ * ε ≤ aRev / 4)
    {Y : ComplexSourceHilbert hμ (jointSourceRegion s) →L[ℂ]
      ComplexSourceHilbert hμ (jointSourceRegion s)}
    (hfactor : complexify (jointDifferenceKernelOperator hμ hs) =
      sourceReserve hμ (jointSourceRegion s) ^ aRev * Y *
        sourceReserve hμ (jointSourceRegion s) ^ aRev)
    (hcY : IsCompactOperator Y) (hY : IsSelfAdjoint Y)
    (htrace : operatorTraceNorm Y ≤ ENNReal.ofReal ε) :
    ∃ X : FiniteGaussianPairModel hμ V S T,
      sandwichedRenyiQuantity X.reference X.density rMinus ≤
        ENNReal.ofReal (Real.exp (2 * rMinus * aRev⁻¹ * ((thermalConst aRev)⁻¹ * ε))) := by
  obtain ⟨X⟩ := nonempty_finiteGaussianPairModel hμ V S T
    (Metric.isBounded_ball.subset hU) (Metric.isBounded_ball.subset hW) hUW hS hT
  have hU' : U ⊆ Metric.ball (jointCenterIndex s 0) 1
    := by simpa only [jointCenterIndex_zero] using hU
  have hW' : W ⊆ Metric.ball (jointCenterIndex s 1) 1
    := by simpa only [jointCenterIndex_one] using hW
  have hSL := hS.2.1.trans (localizedTimeZeroSources_mono hU')
  have hTR := hT.2.1.trans (localizedTimeZeroSources_mono hW')
  have hSU : S ⊔ T ≤ localizedTimeZeroSources (jointSourceRegion s) := by
    apply sup_le
    · exact hSL.trans (localizedTimeZeroSources_mono Set.subset_union_left)
    · exact hTR.trans (localizedTimeZeroSources_mono Set.subset_union_right)
  obtain ⟨hop, htr⟩ := finite_reverse_source_nuclear_bound hμ hs (S ⊔ T) X.basis hSU
    (finiteSourceLabelSubspace hμ (S ⊔ T) X.basis S)
    (finiteSourceLabelSubspace hμ (S ⊔ T) X.basis T) X.complementary
    (fun x hx => hSL hx) (fun x hx => hTR hx) X.symplectic
    X.faithful_density X.characteristic X.reference_characteristic
    aRev_pos_le.1 (show aRev ≤ 1 / 2 by linarith [aRev_pos_le.2]) hε hfactor hcY hY htrace
  obtain ⟨_, _, _, hQ⟩ := finite_reverse_order_gaussian_renyi_bound
    X.faithful_reference X.faithful_density X.reference_covariance_posDef.isHermitian
    (finiteSourceCovarianceMatrix_isHermitian hμ (S ⊔ T) X.basis)
    X.reference_characteristic X.characteristic hsmall hop htr
  exact ⟨X, hQ⟩

/-- Universal constants precede the mass, physical vacuum and every finite
canonical subsystem. Only the scalar separation smallness remains. -/
theorem exists_uniform_finite_physical_reverse :
    ∃ Sgeo A : ℝ, 600 ≤ Sgeo ∧ 0 < A ∧
      ∀ (μ : ℝ) (hμ : 0 < μ) (s : ℝ), Sgeo ≤ s →
        A * s ^ (-gammaRev) ≤ aRev / 4 →
        ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
          (V : FreeFieldVacuum μ H) (U W : Set (EuclideanSpace ℝ (Fin 3))),
          U ⊆ Metric.ball 0 1 → W ⊆ Metric.ball (spatialAxisDisplacement s 0) 1 →
          Disjoint U W → ∀ S T : Submodule ℝ TimeZeroSource,
            IsCanonicalSourceSystem U S → IsCanonicalSourceSystem W T →
            ∃ X : FiniteGaussianPairModel hμ V S T,
              sandwichedRenyiQuantity X.reference X.density rMinus ≤
                ENNReal.ofReal (Real.exp (2 * rMinus * aRev⁻¹ * (A * s ^ (-gammaRev)))) := by
  obtain ⟨Sgeo, J, hSgeo, hJ, hfactor⟩ := exists_uniform_joint_reverse_reserve_factor
  have hc : 0 < thermalConst aRev := thermalConst_pos aRev_pos_le.1 (by linarith [aRev_pos_le.2])
  refine ⟨Sgeo, (thermalConst aRev)⁻¹ * J, by linarith, mul_pos (inv_pos.mpr hc) hJ, ?_⟩
  intro μ hμ s hs hsmall H _ _ _ V U W hU hW hUW S T hS hT
  have hs600 : 600 ≤ s := by linarith
  have hs0 : 0 < s := by linarith
  obtain ⟨Y, hf, hcompact, hsa, htrace, _⟩ := hfactor μ hμ s hs600 hs
  have hsmall' : (thermalConst aRev)⁻¹ * (J * s ^ (-gammaRev)) ≤ aRev / 4 := by
    simpa only [mul_assoc] using hsmall
  obtain ⟨X, hQ⟩ := finite_physical_reverse_model_of_source_factor hμ hs600 V hU hW hUW
    S T hS hT (mul_nonneg hJ.le (Real.rpow_nonneg hs0.le _)) hsmall' hf hcompact hsa htrace
  exact ⟨X, by simpa only [mul_assoc] using hQ⟩

end VacuumBellSeparation
