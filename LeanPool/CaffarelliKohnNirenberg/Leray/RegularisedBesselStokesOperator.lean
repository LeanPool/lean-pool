/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierStokesLinearity
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselTensorQuadratic
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedDuhamelStokes

/-!
# Stokes operator on complete Bessel coordinates

The Fourier Stokes multiplier acts on the weighted L² coordinates
of complete Bessel spaces with the same integrable Abel-kernel bound.
-/

public section

open MeasureTheory FourierTransform Filter
open scoped ENNReal FourierTransform

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The complex L² Stokes operator as a bounded complex linear map. -/
@[expose]
def regularisedStokesL2CLM {t : ℝ} (ht : 0 < t) :
    ComplexTensorL2 →L[ℂ] ComplexVectorL2 := by
  let L : ComplexTensorL2 →ₗ[ℂ] ComplexVectorL2 := {
    toFun := stokesL2Operator ht
    map_add' := stokesL2Operator_add ht
    map_smul' := stokesL2Operator_smul ht
  }
  exact L.mkContinuous (1 / Real.sqrt (2 * Real.exp 1 * t))
    (fun F => stokesL2Operator_norm_le ht F)

/-- The complete H²ᵏ Stokes operator on weighted Bessel coordinates. -/
@[expose]
def regularisedBesselStokesOperator
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    BesselPotentialSpace L2Vec3 ComplexTensor3 ((2 * k : ℕ) : ℝ) 2 →L[ℂ]
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2 :=
  (BesselPotentialSpace.toLpₗᵢ L2Vec3 ComplexVec3
    ((2 * k : ℕ) : ℝ) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((regularisedStokesL2CLM ht).comp
      (BesselPotentialSpace.toLpₗᵢ L2Vec3 ComplexTensor3
        ((2 * k : ℕ) : ℝ) 2).toContinuousLinearEquiv.toContinuousLinearMap)

/-- The complete H²ᵏ Stokes operator has the same Abel-kernel
bound as the underlying L² multiplier. -/
theorem regularisedBesselStokesOperator_norm_le
    {t : ℝ} (ht : 0 < t) (k : ℕ)
    (F : BesselPotentialSpace L2Vec3 ComplexTensor3 ((2 * k : ℕ) : ℝ) 2) :
    ‖regularisedBesselStokesOperator ht k F‖ ≤
      (1 / Real.sqrt (2 * Real.exp 1 * t)) * ‖F‖ := by
  unfold regularisedBesselStokesOperator
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, BesselPotentialSpace.toLpₗᵢ_apply]
  change ‖(BesselPotentialSpace.toLpₗᵢ L2Vec3 ComplexVec3
      ((2 * k : ℕ) : ℝ) 2).symm
        (stokesL2Operator ht F.toLp)‖ ≤
      (1 / Real.sqrt (2 * Real.exp 1 * t)) * ‖F‖
  rw [LinearIsometryEquiv.norm_map, ← BesselPotentialSpace.norm_toLp_eq F]
  exact stokesL2Operator_norm_le ht F.toLp


/-- The complete Sobolev Stokes output is continuous when both the
positive elapsed time and its tensor input vary continuously. -/
theorem regularisedBesselStokesOperator_continuousAt_apply
    {t₀ : ℝ} (ht₀ : 0 < t₀) (k : ℕ)
    (F : {x : ℝ // 0 < x} →
      BesselPotentialSpace L2Vec3 ComplexTensor3 ((2 * k : ℕ) : ℝ) 2)
    (hF : ContinuousAt F ⟨t₀, ht₀⟩) :
    ContinuousAt
      (fun t : {x : ℝ // 0 < x} => regularisedBesselStokesOperator t.2 k (F t))
      ⟨t₀, ht₀⟩ := by
  let eT := BesselPotentialSpace.toLpₗᵢ L2Vec3 ComplexTensor3
    ((2 * k : ℕ) : ℝ) 2
  let eV := BesselPotentialSpace.toLpₗᵢ L2Vec3 ComplexVec3
    ((2 * k : ℕ) : ℝ) 2
  have hFp : ContinuousAt (fun t : {x : ℝ // 0 < x} => eT (F t))
      ⟨t₀, ht₀⟩ := eT.continuous.continuousAt.comp hF
  have hStokes := stokesL2Operator_continuousAt_apply ht₀
    (fun t : {x : ℝ // 0 < x} => t) tendsto_id
    (fun t => eT (F t)) hFp
  change ContinuousAt
    (fun t : {x : ℝ // 0 < x} =>
      eV.symm (stokesL2Operator t.2 (eT (F t)))) ⟨t₀, ht₀⟩
  exact eV.symm.continuous.continuousAt.tendsto.comp hStokes

end CKN.Leray

end
