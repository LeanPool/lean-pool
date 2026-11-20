/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Palomar.Statement
public import LeanPool.FastDynamo.Dynamics.Ideal.LipschitzTestFields
public import LeanPool.FastDynamo.Dynamics.MainLagrangianClauses

/-!
# The velocity is divergence free in the sense of the Challenge statement

The Challenge statement calls `u : 𝕋³ → ℝ³` divergence free when `∑ᵢ mᵢ ûᵢ(m) = 0` for every
`m ∈ ℤ³`, the Fourier coefficients being mathlib's `mFourierCoeff`
(`FastDynamoChallenge.IsDivergenceFree`).  This module proves it for the library's witness
`mainLiteralVelocity` (`isDivergenceFree_mainLiteralVelocity`).

The proof is classical and pointwise.  The periodic lift of the velocity is differentiable at
every point (`differentiable_literalVelocity_lift`) and its divergence vanishes at every point:
the axial component of the derivative vanishes because the velocity does not depend on `x₃`, and
the transverse part is `∂₁u₁ + ∂₂u₂ = 0`
(`fderiv_parameterizedFullGlobalPeriodizedRealSource_transverseDivergence`).  Integration by
parts against a character (`integral_conj_mFourier_mul_torusGradient_of_increment`), valid since
the lift is Lipschitz, gives `(∂ᵢuᵢ)^(m) = 2πi mᵢ ûᵢ(m)`; summing over `i` gives
`2πi ∑ᵢ mᵢ ûᵢ(m) = (div u)^(m) = 0`.

The only dictionary entry needed is `mFourierCoeff_eq_integral_conj_mFourier_mul`: mathlib's
`mFourierCoeff` on `UnitAddTorus (Fin 3)` (computed with the product of the normalised Haar
measures of the circles) is the integral of `conj e_m · f` against `volume`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

/-- **Mathlib's Fourier coefficient on the three-torus, against `volume`**:
`mFourierCoeff f m = ∫ conj (e_m x) · f x dx`.  `mFourierCoeff` integrates against the product of
the normalised Haar measures of the circles, which is the `volume` of `Torus 3`
(`volume_unitAddTorus_eq_haar`). -/
theorem mFourierCoeff_eq_integral_conj_mFourier_mul (f : Torus 3 → ℂ) (m : Fin 3 → ℤ) :
    UnitAddTorus.mFourierCoeff f m =
      ∫ x : Torus 3, (starRingEnd ℂ) (UnitAddTorus.mFourier m x) * f x := by
  rw [volume_unitAddTorus_eq_haar]
  simp only [UnitAddTorus.mFourierCoeff, UnitAddTorus.mFourier_neg, smul_eq_mul]
  rfl

namespace ScaleFamily.TorusCellPlacement

open FullVelocityConcrete

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-- The `i`-th coordinate of the velocity on the literal torus, as a complex-valued function. -/
abbrev literalVelocityCoord (i : Fin 3) : Torus 3 → ℂ := fun x ↦
  ((literalVelocity (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau) x i :
    ℝ) : ℂ)

/-- The `j`-th partial derivative of the `i`-th coordinate of the velocity is the `i`-th
coordinate of the derivative of the lift in the direction `eⱼ`. -/
theorem torusGradient_literalVelocityCoord (htau : 0 ≤ tau) (i j : Fin 3) (x : Torus 3) :
    torusGradient (literalVelocityCoord h P angularSpeed axialSpeed tau i) x j =
      ((fderiv ℝ (fun b : R3 ↦ literalVelocity
          (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)
          (literalTorusPoint b)) (literalIocRepresentative x) (EuclideanSpace.single j 1) i :
        ℝ) : ℂ) := by
  set U : R3 → R3 := fun b ↦ literalVelocity
    (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau) (literalTorusPoint b)
  set a := literalIocRepresentative x
  have hU : HasFDerivAt U (fderiv ℝ U a) a :=
    (differentiable_literalVelocity_lift h P angularSpeed axialSpeed tau htau a).hasFDerivAt
  have hc := Complex.ofRealCLM.hasFDerivAt.comp a
    ((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).hasFDerivAt.comp a hU)
  rw [torusGradient]
  change fderiv ℝ (Complex.ofRealCLM ∘ (EuclideanSpace.proj i : R3 →L[ℝ] ℝ) ∘ U) a
    (EuclideanSpace.single j 1) = _
  rw [hc.fderiv]
  rfl

/-- **The velocity is divergence free at every point**: `∑ᵢ ∂ᵢuᵢ = 0`. -/
theorem sum_torusGradient_literalVelocityCoord (htau : 0 ≤ tau) (x : Torus 3) :
    ∑ i, torusGradient (literalVelocityCoord h P angularSpeed axialSpeed tau i) x i = 0 := by
  simp only [torusGradient_literalVelocityCoord h P angularSpeed axialSpeed tau htau]
  set a := literalIocRepresentative x
  have hd := (differentiable_parameterizedFullGlobalPeriodizedRealSource
    h P angularSpeed axialSpeed tau htau (flowPairProjection a)).hasFDerivAt.comp a
    flowPairProjection.hasFDerivAt
  rw [literalVelocity_lift_eq h P angularSpeed axialSpeed tau, hd.fderiv]
  have e0 : flowPairProjection (EuclideanSpace.single 0 (1 : ℝ)) = pairBasis 0 := by
    simp [pairBasis]
  have e1 : flowPairProjection (EuclideanSpace.single 1 (1 : ℝ)) = pairBasis 1 := by
    simp [pairBasis]
  have e2 : flowPairProjection (EuclideanSpace.single 2 (1 : ℝ)) = 0 := by
    simp
  have hdiv := fderiv_parameterizedFullGlobalPeriodizedRealSource_transverseDivergence
    h P angularSpeed axialSpeed tau htau (flowPairProjection a)
  simp only [Fin.sum_univ_three, ContinuousLinearMap.comp_apply, e0, e1, e2, map_zero,
    PiLp.zero_apply, Complex.ofReal_zero, add_zero]
  rw [← Complex.ofReal_add, hdiv, Complex.ofReal_zero]

/-- Each partial derivative of each coordinate of the velocity is integrable on the torus: it is
measurable and bounded by the Lipschitz constant of the lift. -/
theorem integrable_torusGradient_literalVelocityCoord (htau : 0 ≤ tau) {K : NNReal}
    (hK : LipschitzWith K fun b : R3 ↦ literalVelocity
      (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)
      (literalTorusPoint b)) (m : Fin 3 → ℤ) (i j : Fin 3) :
    Integrable fun x : Torus 3 ↦ (starRingEnd ℂ) (UnitAddTorus.mFourier m x) *
      torusGradient (literalVelocityCoord h P angularSpeed axialSpeed tau i) x j := by
  simp only [torusGradient_literalVelocityCoord h P angularSpeed axialSpeed tau htau]
  refine torusIntegrable_of_bound (C := K) ?_ fun x ↦ ?_
  · refine (Complex.continuous_conj.comp (UnitAddTorus.mFourier m).continuous).measurable.mul ?_
    refine Complex.measurable_ofReal.comp ?_
    refine (measurable_pi_apply i).comp ?_
    refine (WithLp.measurable_ofLp 2 _).comp ?_
    exact (measurable_fderiv_apply_const ℝ _ _).comp measurable_literalIocRepresentative
  · rw [norm_mul, Complex.norm_conj, norm_mFourier_apply, one_mul, Complex.norm_real]
    refine (PiLp.norm_apply_le _ i).trans ?_
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    have hn : ‖(EuclideanSpace.single j (1 : ℝ) : R3)‖ = 1 := by simp
    rw [hn, mul_one]
    exact norm_fderiv_le_of_lipschitz ℝ hK

/-- **Integration by parts for the velocity**: `(∂ⱼuᵢ)^(m) = 2πi mⱼ ûᵢ(m)`, against `volume`. -/
theorem integral_conj_mFourier_mul_torusGradient_literalVelocityCoord (htau : 0 ≤ tau)
    {K : NNReal}
    (hK : LipschitzWith K fun b : R3 ↦ literalVelocity
      (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)
      (literalTorusPoint b)) (m : Fin 3 → ℤ) (i j : Fin 3) :
    (∫ x : Torus 3, (starRingEnd ℂ) (UnitAddTorus.mFourier m x) *
      torusGradient (literalVelocityCoord h P angularSpeed axialSpeed tau i) x j) =
      2 * Real.pi * Complex.I * (m j : ℂ) *
        ∫ x : Torus 3, (starRingEnd ℂ) (UnitAddTorus.mFourier m x) *
          literalVelocityCoord h P angularSpeed axialSpeed tau i x := by
  have hdiff : Differentiable ℝ
      (torusLift (literalVelocityCoord h P angularSpeed axialSpeed tau i)) :=
    Complex.ofRealCLM.differentiable.comp ((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).differentiable.comp
      (differentiable_literalVelocity_lift h P angularSpeed axialSpeed tau htau))
  refine integral_conj_mFourier_mul_torusGradient_of_increment hdiff ⟨K, fun x k t _ ↦ ?_⟩ m j
  set a := literalIocRepresentative x
  have hx : x = literalTorusPoint a := (literalTorusPoint_literalIocRepresentative x).symm
  rw [hx, ← literalTorusPoint_add_single]
  simp only [literalVelocityCoord]
  rw [← Complex.ofReal_sub, Complex.norm_real, ← PiLp.sub_apply]
  refine (PiLp.norm_apply_le _ i).trans ?_
  have := hK.norm_sub_le (a + EuclideanSpace.single k t) a
  have hn : ‖(EuclideanSpace.single k t : R3)‖ = |t| := by simp
  rwa [add_sub_cancel_left, hn] at this

/-- **The velocity is divergence free in the sense of the Challenge statement**:
`∑ᵢ mᵢ ûᵢ(m) = 0` for every `m ∈ ℤ³`, for any Lipschitz velocity of the family. -/
theorem isDivergenceFree_literalVelocity (htau : 0 ≤ tau) {K : NNReal}
    (hK : LipschitzWith K
      (literalVelocity (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))) :
    FastDynamoChallenge.IsDivergenceFree (literalVelocity
      (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) := by
  intro m
  have hlift : LipschitzWith (K * 1) fun b : R3 ↦ literalVelocity
      (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)
      (literalTorusPoint b) :=
    hK.comp lipschitzWith_literalTorusPoint
  set e : Torus 3 → ℂ := fun x ↦ (starRingEnd ℂ) (UnitAddTorus.mFourier m x)
  have hsum : (2 * Real.pi * Complex.I) *
      ∑ i, (m i : ℂ) * UnitAddTorus.mFourierCoeff
        (literalVelocityCoord h P angularSpeed axialSpeed tau i) m = 0 := by
    simp only [mFourierCoeff_eq_integral_conj_mFourier_mul, Finset.mul_sum, ← mul_assoc]
    simp only [← integral_conj_mFourier_mul_torusGradient_literalVelocityCoord
      h P angularSpeed axialSpeed tau htau hlift]
    rw [← integral_finsetSum _ fun i _ ↦
      integrable_torusGradient_literalVelocityCoord h P angularSpeed axialSpeed tau
        htau hlift m i i]
    simp only [← Finset.mul_sum, sum_torusGradient_literalVelocityCoord
      h P angularSpeed axialSpeed tau htau, mul_zero, integral_zero]
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  exact (mul_eq_zero.1 hsum).resolve_left h2pi

end ScaleFamily.TorusCellPlacement

/-- **The velocity of the theorem is divergence free in the sense of the Challenge statement**:
`∑ᵢ mᵢ ûᵢ(m) = 0` for every frequency `m ∈ ℤ³`, with mathlib's `mFourierCoeff`. -/
theorem isDivergenceFree_mainLiteralVelocity :
    FastDynamoChallenge.IsDivergenceFree mainLiteralVelocity :=
  ScaleFamily.TorusCellPlacement.isDivergenceFree_literalVelocity _ _ _ _ _
    HorizontalMode.mainParameterChoice.tau_nonneg lipschitzWith_mainLiteralVelocity

end

end FastDynamo
