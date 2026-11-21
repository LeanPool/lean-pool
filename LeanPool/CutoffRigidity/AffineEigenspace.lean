/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.AffineEigenfunctionOrthogonality

/-! # The actual affine pointwise eigenspace

This finite-dimensional row space is defined by the actual potential gradient.
Its members give actual affine pointwise eigenfunctions and genuine L²
orthonormal coordinates under the normalized Gibbs measure. Identifying it
with the full first L² eigenspace additionally requires analytic rigidity and
spectral attainment; the parameter here is an eigenvalue, not a definition
of the spectral gap.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Coefficient vectors satisfying the actual affine gradient equation. -/
@[expose] noncomputable def affineEigenRows (V : E → ℝ) (ρ : ℝ) : Submodule ℝ E where
  carrier := {a | ∀ x, inner ℝ a (gradient V x - gradient V 0) = ρ * inner ℝ a x}
  zero_mem' := by simp
  add_mem' := by
    intro a c ha hc x
    simp only [inner_add_left, ha x, hc x]
    ring
  smul_mem' := by
    intro r a ha x
    simp only [real_inner_smul_left, ha x]
    ring

/-- The constant term is forced by evaluating the eigenfunction equation at zero. -/
@[expose] noncomputable def affineEigenConstant (V : E → ℝ) (ρ : ℝ) (a : E) : ℝ :=
  inner ℝ a (gradient V 0) / ρ

/-- A row gives the actual affine pointwise eigenfunction precisely with its forced constant. -/
theorem affineEigenRows_iff_eigenfunction (V : E → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (a : E) (b : ℝ) :
    (∀ x, langevinDifferentialOperator V (fun y => inner ℝ a y + b) x =
      -ρ * (inner ℝ a x + b)) ↔
    a ∈ affineEigenRows V ρ ∧ b = affineEigenConstant V ρ a := by
  rw [affine_eigenfunction_iff_drift]
  constructor
  · intro h
    have h0 := h 0
    simp only [inner_zero_right, zero_add] at h0
    refine ⟨?_, ?_⟩
    · intro x
      rw [inner_sub_right, h x, h0]
      ring
    · unfold affineEigenConstant
      apply (eq_div_iff hρ.ne').mpr
      linarith
  · rintro ⟨ha, rfl⟩ x
    have hx := ha x
    change inner ℝ a (gradient V x - gradient V 0) = ρ * inner ℝ a x at hx
    rw [inner_sub_right] at hx
    unfold affineEigenConstant
    field_simp
    nlinarith [hx]

/-- All rows produce genuine affine pointwise eigenfunctions. -/
theorem affineEigenRows_eigenfunction (V : E → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (a : affineEigenRows V ρ) :
    ∀ x, langevinDifferentialOperator V
      (fun y => inner ℝ (a : E) y + affineEigenConstant V ρ a) x =
      -ρ * (inner ℝ (a : E) x + affineEigenConstant V ρ a) :=
  (affineEigenRows_iff_eigenfunction V hρ a _).mpr ⟨a.property, rfl⟩

/-- The affine pointwise row space has dimension at most the ambient dimension. -/
theorem affineEigenRows_finrank_le (V : E → ℝ) (ρ : ℝ) :
    Module.finrank ℝ (affineEigenRows V ρ) ≤ d := by
  simpa using Submodule.finrank_le (affineEigenRows V ρ)

/-- Actual L² cross moments agree with the scaled Euclidean row inner product. -/
theorem affineEigenRows_cross_moment (V : E → ℝ) (hV : Differentiable ℝ V)
    {ρ : ℝ} (hρ : 0 < ρ) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (a c : affineEigenRows V ρ) :
    ∫ x, (inner ℝ (a : E) x + affineEigenConstant V ρ a) *
      (inner ℝ (c : E) x + affineEigenConstant V ρ c) ∂gibbsMeasure volume V =
      inner ℝ (a : E) (c : E) / ρ :=
  affine_eigenfunction_cross_moment V hV a c _ _ ρ hρ
    (affineEigenRows_eigenfunction V hρ a) (affineEigenRows_eigenfunction V hρ c) hprob

/-- Choose an ordinary finite orthonormal basis of the actual row submodule. -/
@[expose] noncomputable def affineEigenRowsBasis (V : E → ℝ) (ρ : ℝ) :
    OrthonormalBasis (Fin (Module.finrank ℝ (affineEigenRows V ρ))) ℝ (affineEigenRows V ρ) :=
  stdOrthonormalBasis ℝ (affineEigenRows V ρ)

/-- The ambient unit rows supplied by the actual row-space basis. -/
@[expose] noncomputable def affineEigenBasisRows (V : E → ℝ) (ρ : ℝ) :
    Fin (Module.finrank ℝ (affineEigenRows V ρ)) → E :=
  fun i => affineEigenRowsBasis V ρ i

/-- These are genuinely orthonormal ambient Euclidean vectors. -/
theorem affineEigenBasisRows_orthonormal (V : E → ℝ) (ρ : ℝ) :
    Orthonormal ℝ (affineEigenBasisRows V ρ) := by
  rw [orthonormal_iff_ite]
  exact orthonormal_iff_ite.mp (affineEigenRowsBasis V ρ).orthonormal

/-- The scaled row basis gives unit L² eigenfunctions. -/
@[expose] noncomputable def affineEigenBasisCoefficient (V : E → ℝ) (ρ : ℝ)
    (i : Fin (Module.finrank ℝ (affineEigenRows V ρ))) : affineEigenRows V ρ :=
  Real.sqrt ρ • affineEigenRowsBasis V ρ i

/-- Actual affine eigenfunctions attached to the finite row-space basis. -/
@[expose] noncomputable def affineEigenBasisFunction (V : E → ℝ) (ρ : ℝ)
    (i : Fin (Module.finrank ℝ (affineEigenRows V ρ))) (x : E) : ℝ :=
  inner ℝ (affineEigenBasisCoefficient V ρ i : E) x +
    affineEigenConstant V ρ (affineEigenBasisCoefficient V ρ i)

/-- Every coordinate satisfies the original differential eigenfunction equation. -/
theorem affineEigenBasisFunction_eigenfunction (V : E → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (i : Fin (Module.finrank ℝ (affineEigenRows V ρ))) (x : E) :
    langevinDifferentialOperator V (affineEigenBasisFunction V ρ i) x =
      -ρ * affineEigenBasisFunction V ρ i x :=
  affineEigenRows_eigenfunction V hρ (affineEigenBasisCoefficient V ρ i) x

/-- The basis coordinates belong to the actual Gibbs L² space. -/
theorem affineEigenBasisFunction_memLp (V : E → ℝ) (hV : Differentiable ℝ V)
    {ρ : ℝ} (hρ : 0 < ρ) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (i : Fin (Module.finrank ℝ (affineEigenRows V ρ))) :
    MemLp (affineEigenBasisFunction V ρ i) 2 (gibbsMeasure volume V) :=
  affine_eigenfunction_memLp_all V hV _ _ ρ hρ
    (affineEigenRows_eigenfunction V hρ (affineEigenBasisCoefficient V ρ i)) hprob

/-- The actual Gibbs L² integrals of these coordinates form the identity matrix. -/
theorem affineEigenBasisFunction_integral_mul (V : E → ℝ) (hV : Differentiable ℝ V)
    {ρ : ℝ} (hρ : 0 < ρ) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (i j : Fin (Module.finrank ℝ (affineEigenRows V ρ))) :
    ∫ x, affineEigenBasisFunction V ρ i x * affineEigenBasisFunction V ρ j x
      ∂gibbsMeasure volume V = if i = j then 1 else 0 := by
  change (∫ x, (inner ℝ (affineEigenBasisCoefficient V ρ i : E) x + _) *
      (inner ℝ (affineEigenBasisCoefficient V ρ j : E) x + _) ∂gibbsMeasure volume V) = _
  rw [affineEigenRows_cross_moment V hV hρ hprob]
  change inner ℝ (Real.sqrt ρ • affineEigenBasisRows V ρ i)
    (Real.sqrt ρ • affineEigenBasisRows V ρ j) / ρ = _
  rw [real_inner_smul_left, inner_smul_right,
    orthonormal_iff_ite.mp (affineEigenBasisRows_orthonormal V ρ) i j]
  split_ifs <;> simp [Real.mul_self_sqrt hρ.le, hρ.ne']

/-- The concrete affine eigenmap data use precisely the unit rows and forced constants. -/
theorem affineEigenBasisFunction_representation (V : E → ℝ) (ρ : ℝ)
    (i : Fin (Module.finrank ℝ (affineEigenRows V ρ))) (x : E) :
    affineEigenBasisFunction V ρ i x =
      Real.sqrt ρ * inner ℝ (affineEigenBasisRows V ρ i) x +
        affineEigenConstant V ρ (affineEigenBasisCoefficient V ρ i) := by
  unfold affineEigenBasisFunction affineEigenBasisCoefficient affineEigenBasisRows
  rw [Submodule.coe_smul, real_inner_smul_left]

/-- The actual L² elements supplied by the finite affine pointwise eigenspace. -/
@[expose] noncomputable def affineEigenBasisL2 (V : E → ℝ) (hV : Differentiable ℝ V)
    {ρ : ℝ} (hρ : 0 < ρ) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (i : Fin (Module.finrank ℝ (affineEigenRows V ρ))) :
    E →₂[gibbsMeasure volume V] ℝ :=
  (affineEigenBasisFunction_memLp V hV hρ hprob i).toLp (affineEigenBasisFunction V ρ i)

/-- These are orthonormal in the actual Gibbs L² Hilbert space. -/
theorem affineEigenBasisL2_orthonormal (V : E → ℝ) (hV : Differentiable ℝ V)
    {ρ : ℝ} (hρ : 0 < ρ) (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    Orthonormal ℝ (affineEigenBasisL2 V hV hρ hprob) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [L2.inner_def]
  calc
    _ = ∫ x, affineEigenBasisFunction V ρ i x * affineEigenBasisFunction V ρ j x
        ∂gibbsMeasure volume V := by
      apply integral_congr_ae
      filter_upwards [(affineEigenBasisFunction_memLp V hV hρ hprob i).coeFn_toLp,
        (affineEigenBasisFunction_memLp V hV hρ hprob j).coeFn_toLp] with x hi hj
      change inner ℝ
        ((affineEigenBasisFunction_memLp V hV hρ hprob i).toLp (affineEigenBasisFunction V ρ i) x)
        ((affineEigenBasisFunction_memLp V hV hρ hprob j).toLp (affineEigenBasisFunction V ρ j) x)
          = _
      rw [hi, hj, Real.inner_apply]
    _ = _ := affineEigenBasisFunction_integral_mul V hV hρ hprob i j

end CutoffRigidity
