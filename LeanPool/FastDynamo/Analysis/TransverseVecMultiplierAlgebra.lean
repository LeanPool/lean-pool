/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.TransverseWeightedLeibniz

/-!
# Fibre-generic multiplier algebra on the transverse torus

Multiplication of a `ℂ^ι`-valued `L²` field by a scalar `L∞` coefficient, and multiplication of
a scalar `L²` field by an `L∞` coefficient field, obey the obvious associativity and
commutation rules.  This module proves them once, generically in the fibre type `ι`, together
with the two-direction Cauchy-Schwarz step `Σ_j ‖∂_j h‖ ≤ √2 ‖∇_⊥ h‖` that converts a
coordinatewise commutator bound into the gradient-energy form in which `eq:bg-resolvent`
and `eq:local-gradient` are stated.

Nothing here mentions a cut-off, a cell, a velocity field or a spectral parameter; the
commutator calculus that consumes these facts is in `Global/HorizontalCutoffCommutator.lean`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TransverseVecMultiplierAlgebra

/-! ## Quotient-level multiplication of two `L∞` coefficients -/

/-- Pointwise multiplication of two transverse scalar `L∞` coefficients. -/
def scalarMulTransverseLInf :
    TransverseScalarLInf →L[ℂ]
      TransverseScalarLInf →L[ℂ] TransverseScalarLInf :=
  (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] ℂ →L[ℂ] ℂ).holderL
    transverseMeasure ∞ ∞ ∞

/-- The `L∞` product class `scalarMulTransverseLInf a b` is represented almost everywhere by the
pointwise product `x ↦ a x * b x`, so quotient-level multiplication may be computed on
representatives. -/
theorem scalarMulTransverseLInf_coe_ae
    (a b : TransverseScalarLInf) :
    (scalarMulTransverseLInf a b : TransverseTorus → ℂ)
      =ᵐ[transverseMeasure] fun x ↦ a x * b x := by
  change
    ((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] ℂ →L[ℂ] ℂ).holder
      ∞ a b : TransverseTorus → ℂ)
        =ᵐ[transverseMeasure] fun x ↦ a x * b x
  simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
    (ContinuousLinearMap.coeFn_holder
      (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] ℂ →L[ℂ] ℂ) a b)

/-! ## Fibre-generic multiplication algebra -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Successive multiplication of a `ℂ^ι`-valued `L²` field by two scalar `L∞` coefficients is
multiplication by their quotient-level product. -/
theorem scalarVectorMulTransverseVec_mulLInf
    (a b : TransverseScalarLInf) (f : TransverseVecL2 ι) :
    scalarVectorMulTransverseVec ι (scalarMulTransverseLInf a b) f =
      scalarVectorMulTransverseVec ι a (scalarVectorMulTransverseVec ι b f) := by
  apply Lp.ext
  filter_upwards [
    scalarVectorMulTransverseVec_coe_ae (ι := ι) (scalarMulTransverseLInf a b) f,
    scalarMulTransverseLInf_coe_ae a b,
    scalarVectorMulTransverseVec_coe_ae (ι := ι) b f,
    scalarVectorMulTransverseVec_coe_ae (ι := ι) a
      (scalarVectorMulTransverseVec ι b f)]
      with x hleft hab hbf hright
  rw [hleft, hab, hright, hbf]
  exact mul_smul _ _ _

omit [DecidableEq ι] in
/-- Two scalar `L∞` coefficients may be applied to a `ℂ^ι`-valued `L²` field in either order. -/
theorem scalarVectorMulTransverseVec_commute
    (a b : TransverseScalarLInf) (f : TransverseVecL2 ι) :
    scalarVectorMulTransverseVec ι a (scalarVectorMulTransverseVec ι b f) =
      scalarVectorMulTransverseVec ι b (scalarVectorMulTransverseVec ι a f) := by
  rw [← scalarVectorMulTransverseVec_mulLInf, ← scalarVectorMulTransverseVec_mulLInf]
  congr 2
  apply Lp.ext
  filter_upwards [scalarMulTransverseLInf_coe_ae a b,
    scalarMulTransverseLInf_coe_ae b a] with x hab hba
  rw [hab, hba, mul_comm]

omit [DecidableEq ι] in
/-- The product of a transverse `ℂ^ι`-valued `L∞` coefficient with a transverse scalar `L²`
field is represented almost everywhere by the pointwise product. -/
theorem vectorScalarMulTransverseVec_coe_ae (a : TransverseVecLInf ι) (f : TransverseScalarL2) :
    (vectorScalarMulTransverseVec ι a f : TransverseTorus → EuclideanSpace ℂ ι)
      =ᵐ[transverseMeasure] fun x ↦ f x • a x :=
  vectorScalarMulL2_coe_ae transverseMeasure a f

omit [DecidableEq ι] in
/-- A scalar `L∞` factor may be moved past a vector `L∞` coefficient. -/
theorem scalarVectorMulTransverseVec_vectorScalarMulTransverseVec
    (psi : TransverseScalarLInf) (a : TransverseVecLInf ι) (f : TransverseScalarL2) :
    scalarVectorMulTransverseVec ι psi (vectorScalarMulTransverseVec ι a f) =
      vectorScalarMulTransverseVec ι a (scalarMulTransverse psi f) := by
  apply Lp.ext
  filter_upwards [
    scalarVectorMulTransverseVec_coe_ae (ι := ι) psi
      (vectorScalarMulTransverseVec ι a f),
    vectorScalarMulTransverseVec_coe_ae (ι := ι) a f,
    vectorScalarMulTransverseVec_coe_ae (ι := ι) a (scalarMulTransverse psi f),
    scalarMulTransverse_coe_ae psi f] with x hleft haf hright hpf
  rw [hleft, haf, hright, hpf]
  rw [smul_smul, mul_comm]

/-! ## From the coordinate sum to the gradient energy -/

/-- The two-term Cauchy-Schwarz inequality `a + c ≤ √2 √(a² + c²)` for nonnegative reals. -/
private theorem add_le_sqrt_two_mul_sqrt_add_sq {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    a + c ≤ Real.sqrt 2 * Real.sqrt (a ^ 2 + c ^ 2) := by
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    a + c = Real.sqrt ((a + c) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt (2 * (a ^ 2 + c ^ 2)) := by
      apply Real.sqrt_le_sqrt
      nlinarith [sq_nonneg (a - c)]

/-- Cauchy-Schwarz in the two transverse directions: `Σ_j‖∂_jh‖ ≤ √2 ‖∇_⊥h‖`.  This is the step
that turns the commutator bound into the form in which `eq:bg-resolvent` and
`eq:local-gradient` are stated. -/
theorem sum_norm_deriv_le_sqrt_gradientEnergy (b : TransverseVecH2 ι) :
    (∑ j : Fin 2, ‖transverseVecDerivFromH2 ι j b‖) ≤
      Real.sqrt 2 * Real.sqrt (transverseGradientEnergy b) := by
  have hsum : (∑ j : Fin 2, ‖transverseVecDerivFromH2 ι j b‖) =
      ‖transverseVecDerivFromH2 ι 0 b‖ + ‖transverseVecDerivFromH2 ι 1 b‖ :=
    Fin.sum_univ_two _
  have henergy : transverseGradientEnergy b =
      ‖transverseVecDerivFromH2 ι 0 b‖ ^ 2 + ‖transverseVecDerivFromH2 ι 1 b‖ ^ 2 := by
    unfold transverseGradientEnergy
    exact Fin.sum_univ_two _
  rw [hsum, henergy]
  exact add_le_sqrt_two_mul_sqrt_add_sq (norm_nonneg _) (norm_nonneg _)

end TransverseVecMultiplierAlgebra

end

end FastDynamo
