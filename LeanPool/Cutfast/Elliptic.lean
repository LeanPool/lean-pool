/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.Cutfast.Wasserstein
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Wasserstein distance for elliptic families (Lemma 2.2)

We compute the quadratic Wasserstein distance between two members `μ`, `ν` of the location-scale
family of a rotationally invariant law `η` (zero mean, identity covariance). The proof follows the
paper: with `R = √Σμ`, the symmetric nonnegative matrix `A = R⁻¹ √(R Σν R) R⁻¹` satisfies
`A Σμ A = Σν`, hence `Q⁻¹ A R` is orthogonal (`Q = √Σν`) and rotation invariance of `η` gives
`ν = μ ∘ (x ↦ A (x - mμ) + mν)⁻¹`. Lemma 2.1 (`wassersteinSq_map_affine'`) then gives the formula,
the trace being computed from the covariance identity of `η`.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Real
open scoped ENNReal InnerProductSpace

namespace Cutfast

local notation "𝓛" => Matrix.toEuclideanCLM (𝕜 := ℝ)

namespace Elliptic

open Matrix
open scoped MatrixOrder

variable {d : ℕ}

/-- Transposition of a matrix acting in an inner product. -/
lemma inner_toEuclideanCLM_left (D : Matrix (Fin d) (Fin d) ℝ) (x u : E d) :
    ⟪𝓛 D x, u⟫_ℝ = ⟪x, 𝓛 (star D) u⟫_ℝ := by
  rw [map_star, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

/-- Diagonal entries of a matrix as inner products. -/
lemma inner_basisFun_toEuclideanCLM (M : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    ⟪EuclideanSpace.basisFun (Fin d) ℝ i, 𝓛 M (EuclideanSpace.basisFun (Fin d) ℝ i)⟫_ℝ = M i i := by
  rw [inner_toEuclideanCLM]; simp

/-- Composition of matrices acting on `E d`. -/
lemma toEuclideanCLM_apply_apply (D D' : Matrix (Fin d) (Fin d) ℝ) (x : E d) :
    𝓛 D (𝓛 D' x) = 𝓛 (D * D') x := by
  rw [map_mul]; rfl

lemma sqrt_mul_self_of_posDef {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) :
    CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg

/-- The square root of a positive definite matrix is invertible. -/
lemma isUnit_det_sqrt {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) :
    IsUnit (CFC.sqrt S).det := by
  have : IsUnit S := hS.isUnit
  rw [← sqrt_mul_self_of_posDef hS] at this
  exact (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_of_mul_isUnit_left this)

lemma star_sqrt (S : Matrix (Fin d) (Fin d) ℝ) : star (CFC.sqrt S) = CFC.sqrt S :=
  (CFC.sqrt_nonneg S).isSelfAdjoint.star_eq

lemma star_inv_sqrt (S : Matrix (Fin d) (Fin d) ℝ) : star (CFC.sqrt S)⁻¹ = (CFC.sqrt S)⁻¹ := by
  rw [star_eq_conjTranspose, conjTranspose_nonsing_inv, ← star_eq_conjTranspose, star_sqrt]

/-- Nonnegativity of a product of commuting nonnegative real matrices. -/
lemma mul_nonneg_of_commute {R Q : Matrix (Fin d) (Fin d) ℝ} (hR : 0 ≤ R) (hQ : 0 ≤ Q)
    (h : Commute R Q) : 0 ≤ R * Q := by
  have h1 : Commute (CFC.sqrt R) Q := by
    rw [CFC.sqrt_eq_cfc]; exact h.cfc_nnreal _
  have h2 := (CFC.sqrt_nonneg R).isSelfAdjoint.conjugate_nonneg hQ
  rwa [mul_assoc, h1.eq.symm, ← mul_assoc, CFC.sqrt_mul_sqrt_self R] at h2

/-- The transport matrix `A = R⁻¹ √(R Σν R) R⁻¹`, `R = √Σμ`. -/
noncomputable def transportMatrix (Sμ Sν : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (CFC.sqrt Sμ)⁻¹ * CFC.sqrt (CFC.sqrt Sμ * Sν * CFC.sqrt Sμ) * (CFC.sqrt Sμ)⁻¹

section transport

variable {Sμ Sν : Matrix (Fin d) (Fin d) ℝ} (hSμ : Sμ.PosDef) (hSν : Sν.PosDef)
include hSμ hSν

omit hSμ hSν in
lemma transportMatrix_nonneg : 0 ≤ transportMatrix Sμ Sν := by
  have := star_left_conjugate_nonneg (CFC.sqrt_nonneg (CFC.sqrt Sμ * Sν * CFC.sqrt Sμ))
    (CFC.sqrt Sμ)⁻¹
  rwa [star_inv_sqrt] at this

/-- The transport matrix pushes `Σμ` to `Σν`: `A Σμ A = Σν`. -/
lemma transportMatrix_mul : transportMatrix Sμ Sν * Sμ * transportMatrix Sμ Sν = Sν := by
  have hM : 0 ≤ CFC.sqrt Sμ * Sν * CFC.sqrt Sμ := by
    simpa [star_sqrt] using star_left_conjugate_nonneg hSν.posSemidef.nonneg (CFC.sqrt Sμ)
  have hu := isUnit_det_sqrt hSμ
  have key := CFC.sqrt_mul_sqrt_self _ hM
  have hR := sqrt_mul_self_of_posDef hSμ
  unfold transportMatrix
  generalize CFC.sqrt (CFC.sqrt Sμ * Sν * CFC.sqrt Sμ) = N at key ⊢
  generalize CFC.sqrt Sμ = R at hR hu key ⊢
  subst hR
  simp only [mul_assoc, nonsing_inv_mul_cancel_left _ _ hu, mul_nonsing_inv_cancel_left _ _ hu]
  rw [← mul_assoc N N, key]
  simp only [mul_assoc, mul_nonsing_inv _ hu, mul_one, nonsing_inv_mul_cancel_left _ _ hu]

omit hSν in
/-- `Tr (A Σμ) = Tr √(√Σμ Σν √Σμ)`. -/
lemma trace_transportMatrix_mul : (transportMatrix Sμ Sν * Sμ).trace =
    (CFC.sqrt (CFC.sqrt Sμ * Sν * CFC.sqrt Sμ)).trace := by
  have hu := isUnit_det_sqrt hSμ
  have hR := sqrt_mul_self_of_posDef hSμ
  unfold transportMatrix
  generalize CFC.sqrt (CFC.sqrt Sμ * Sν * CFC.sqrt Sμ) = N
  generalize CFC.sqrt Sμ = R at hR hu ⊢
  subst hR
  simp only [mul_assoc, nonsing_inv_mul_cancel_left _ _ hu]
  rw [trace_mul_comm, mul_assoc, mul_nonsing_inv _ hu, mul_one]

end transport

section moments

variable {η : Measure (E d)}

lemma memLp_two_id (h2 : Integrable (fun x => ‖x‖ ^ 2) η) : MemLp (fun x : E d => x) 2 η :=
  (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).mpr h2

lemma integrable_id' [IsProbabilityMeasure η] (h2 : Integrable (fun x => ‖x‖ ^ 2) η) :
    Integrable (fun x : E d => x) η :=
  (memLp_two_id h2).integrable one_le_two

lemma integrable_sq_norm_affine [IsProbabilityMeasure η] (h2 : Integrable (fun x => ‖x‖ ^ 2) η)
    (a : E d) (T : E d →L[ℝ] E d) : Integrable (fun x => ‖a + T x‖ ^ 2) η := by
  simpa only [id, add_comm a] using Wasserstein.integrable_sq_clm aestronglyMeasurable_id h2 T a

/-- For `η` centered, `∫ ‖a + T x‖² dη = ‖a‖² + ∫ ‖T x‖² dη`. -/
lemma integral_sq_norm_affine [IsProbabilityMeasure η] (h2 : Integrable (fun x => ‖x‖ ^ 2) η)
    (hmean : ∫ x, x ∂η = 0) (a : E d) (T : E d →L[ℝ] E d) :
    ∫ x, ‖a + T x‖ ^ 2 ∂η = ‖a‖ ^ 2 + ∫ x, ‖T x‖ ^ 2 ∂η := by
  have hT : Integrable (fun x => T x) η := T.integrable_comp (integrable_id' h2)
  have hT2 : Integrable (fun x => ‖T x‖ ^ 2) η := by
    simpa using integrable_sq_norm_affine h2 0 T
  have hin : Integrable (fun x => 2 * ⟪a, T x⟫_ℝ) η := (hT.const_inner a).const_mul 2
  have h1 : Integrable (fun x => ‖a‖ ^ 2 + 2 * ⟪a, T x⟫_ℝ) η := (integrable_const _).add hin
  simp_rw [norm_add_sq_real]
  rw [integral_add h1 hT2, integral_add (integrable_const _) hin,
    integral_const_mul, integral_inner hT, T.integral_comp_comm (integrable_id' h2), hmean]
  simp

lemma integrable_inner_mul_inner (h2 : Integrable (fun x => ‖x‖ ^ 2) η) (u v : E d) :
    Integrable (fun x => ⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ) η := by
  refine (h2.const_mul (‖u‖ * ‖v‖)).mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  calc |⟪x, u⟫_ℝ| * |⟪x, v⟫_ℝ| ≤ (‖x‖ * ‖u‖) * (‖x‖ * ‖v‖) := by
        gcongr <;> exact abs_real_inner_le_norm _ _
    _ = ‖u‖ * ‖v‖ * ‖x‖ ^ 2 := by ring

/-- For `η` with identity covariance, `∫ ‖D x‖² dη = Tr (D Dᵀ)`. -/
lemma integral_sq_norm_toEuclideanCLM (h2 : Integrable (fun x => ‖x‖ ^ 2) η)
    (hcov : ∀ u v : E d, ∫ x, ⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ ∂η = ⟪u, v⟫_ℝ) (D : Matrix (Fin d) (Fin d) ℝ) :
    ∫ x, ‖𝓛 D x‖ ^ 2 ∂η = (D * star D).trace := by
  set b := EuclideanSpace.basisFun (Fin d) ℝ
  have h : ∀ x, ‖𝓛 D x‖ ^ 2 =
      ∑ i, ⟪x, 𝓛 (star D) (b i)⟫_ℝ * ⟪x, 𝓛 (star D) (b i)⟫_ℝ := by
    intro x
    rw [← b.sum_sq_inner_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_toEuclideanCLM_left, sq]
  simp_rw [h]
  rw [integral_finsetSum _ fun i _ => integrable_inner_mul_inner h2 _ _]
  simp_rw [hcov, inner_toEuclideanCLM_left, star_star, toEuclideanCLM_apply_apply]
  simp only [b, inner_basisFun_toEuclideanCLM]
  rfl

/-- Mean and covariance of the image of `η` under `x ↦ m + √S x`. -/
lemma moments_map [IsProbabilityMeasure η] (h2 : Integrable (fun x => ‖x‖ ^ 2) η)
    (hmean : ∫ x, x ∂η = 0) (hcov : ∀ u v : E d, ∫ x, ⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ ∂η = ⟪u, v⟫_ℝ)
    (m : E d) {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) :
    ∫ x, x ∂(η.map fun x => m + 𝓛 (CFC.sqrt S) x) = m ∧
      ∀ u v : E d, ∫ x, ⟪x - m, u⟫_ℝ * ⟪x - m, v⟫_ℝ ∂(η.map fun x => m + 𝓛 (CFC.sqrt S) x) =
        ⟪u, 𝓛 S v⟫_ℝ := by
  have hmeas : Measurable fun x : E d => m + 𝓛 (CFC.sqrt S) x := by fun_prop
  constructor
  · rw [integral_map hmeas.aemeasurable (by fun_prop), integral_add (integrable_const _)
      ((𝓛 _).integrable_comp (integrable_id' h2)), (𝓛 _).integral_comp_comm (integrable_id' h2),
      hmean]
    simp
  · intro u v
    rw [integral_map hmeas.aemeasurable (by fun_prop)]
    simp_rw [add_sub_cancel_left, inner_toEuclideanCLM_left, star_sqrt, hcov,
      inner_toEuclideanCLM_left, star_sqrt, toEuclideanCLM_apply_apply, sqrt_mul_self_of_posDef hS]

end moments

lemma transportMatrix_star {Sμ Sν : Matrix (Fin d) (Fin d) ℝ} :
    star (transportMatrix Sμ Sν) = transportMatrix Sμ Sν :=
  transportMatrix_nonneg.isSelfAdjoint.star_eq

/-- A nonnegative matrix gives a positive operator. -/
lemma isPositive_toEuclideanCLM {A : Matrix (Fin d) (Fin d) ℝ} (hA : 0 ≤ A) :
    (𝓛 A).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff']
  refine ⟨hA.isSelfAdjoint.map _, fun x => ?_⟩
  rw [real_inner_comm, inner_toEuclideanCLM]
  simpa using (Matrix.nonneg_iff_posSemidef.mp hA).dotProduct_mulVec_nonneg (WithLp.ofLp x)

end Elliptic

open Cutfast.Elliptic Matrix in
open scoped MatrixOrder in
/-- **Positive-definite case of Lemma 2.2.** Let `η` be a rotationally invariant probability
measure on `ℝᵈ` with finite second moment, zero mean and identity covariance. Let `μ`, `ν` be
its images under
`x ↦ m_μ + √Σ_μ x` and `x ↦ m_ν + √Σ_ν x`, with `Σ_μ`, `Σ_ν` symmetric positive definite
matrices. Then `μ`, `ν` have means `m_μ`, `m_ν` and covariances `Σ_μ`, `Σ_ν`, and
`W₂²(μ,ν) = Tr(Σ_μ + Σ_ν - 2 √(√Σ_μ Σ_ν √Σ_μ)) + |m_μ - m_ν|²`; if moreover `Σ_μ` and `Σ_ν`
commute, `W₂²(μ,ν) = Tr((√Σ_μ - √Σ_ν)²) + |m_μ - m_ν|²`. Square roots are those of the
continuous functional calculus (`CFC.sqrt`) for the order on matrices. -/
theorem wassersteinSq_elliptic' {d : ℕ} (η : Measure (E d)) [IsProbabilityMeasure η]
    (hrot : ∀ U : E d ≃ₗᵢ[ℝ] E d, η.map U = η) (h2 : Integrable (fun x => ‖x‖ ^ 2) η)
    (hmean : ∫ x, x ∂η = 0) (hcov : ∀ u v : E d, ∫ x, ⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ ∂η = ⟪u, v⟫_ℝ)
    (mμ mν : E d) (Sμ Sν : Matrix (Fin d) (Fin d) ℝ) (hSμ : Sμ.PosDef) (hSν : Sν.PosDef) :
    let μ := η.map fun x => mμ + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Sμ) x
    let ν := η.map fun x => mν + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Sν) x
    (∫ x, x ∂μ = mμ ∧ ∀ u v : E d, ∫ x, ⟪x - mμ, u⟫_ℝ * ⟪x - mμ, v⟫_ℝ ∂μ =
        ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) Sμ v⟫_ℝ) ∧
    (∫ x, x ∂ν = mν ∧ ∀ u v : E d, ∫ x, ⟪x - mν, u⟫_ℝ * ⟪x - mν, v⟫_ℝ ∂ν =
        ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) Sν v⟫_ℝ) ∧
    wassersteinSq μ ν = ENNReal.ofReal
      ((Sμ + Sν - 2 * CFC.sqrt (CFC.sqrt Sμ * Sν * CFC.sqrt Sμ)).trace + ‖mμ - mν‖ ^ 2) ∧
    (Sμ * Sν = Sν * Sμ → wassersteinSq μ ν = ENNReal.ofReal
      (((CFC.sqrt Sμ - CFC.sqrt Sν) ^ 2).trace + ‖mμ - mν‖ ^ 2)) := by
  intro μ ν
  have hμ := moments_map h2 hmean hcov mμ hSμ
  have hν := moments_map h2 hmean hcov mν hSν
  set R := CFC.sqrt Sμ with hR
  set Q := CFC.sqrt Sν with hQ
  have hRR : R * R = Sμ := sqrt_mul_self_of_posDef hSμ
  have hQQ : Q * Q = Sν := sqrt_mul_self_of_posDef hSν
  have hRu : IsUnit R.det := isUnit_det_sqrt hSμ
  have hQu : IsUnit Q.det := isUnit_det_sqrt hSν
  set A := transportMatrix Sμ Sν with hA
  set h := mν - 𝓛 A mμ with hh
  have hTμ : Measurable fun x : E d => mμ + 𝓛 R x := by fun_prop
  have hTν : Measurable fun x : E d => mν + 𝓛 Q x := by fun_prop
  have hT : Measurable fun x : E d => 𝓛 A x + h := by fun_prop
  -- the orthogonal matrix `U = Q⁻¹ A R`
  set U := Q⁻¹ * (A * R) with hU
  have hUu : U ∈ unitary (Matrix (Fin d) (Fin d) ℝ) := by
    have h1 : U * star U = 1 := by
      rw [hU, star_mul, star_mul, star_sqrt, star_inv_sqrt, transportMatrix_star]
      calc Q⁻¹ * (A * R) * (R * A * Q⁻¹) = Q⁻¹ * (A * (R * R) * A) * Q⁻¹ := by
            simp only [mul_assoc]
        _ = 1 := by
            rw [hRR, transportMatrix_mul hSμ hSν, ← hQQ]
            simp only [mul_assoc, mul_nonsing_inv _ hQu, mul_one, nonsing_inv_mul _ hQu]
    exact Unitary.mem_iff.mpr ⟨mul_eq_one_comm.mp h1, h1⟩
  set e := Unitary.linearIsometryEquiv ⟨𝓛 U, Unitary.map_mem 𝓛 hUu⟩
  have hνT : ν = μ.map fun x => 𝓛 A x + h := by
    have hcomp : ((fun x => 𝓛 A x + h) ∘ fun x => mμ + 𝓛 R x) =
        (fun x => mν + 𝓛 Q x) ∘ e := by
      funext x
      have he : e x = 𝓛 U x := rfl
      simp only [Function.comp_apply, he, hU, toEuclideanCLM_apply_apply,
        mul_nonsing_inv_cancel_left _ _ hQu, map_add, hh]
      abel
    rw [Measure.map_map hT hTμ, hcomp, ← Measure.map_map hTν e.continuous.measurable, hrot]
  have hint : Integrable (fun x => ‖x‖ ^ 2) μ := by
    rw [integrable_map_measure (by fun_prop) hTμ.aemeasurable]
    exact integrable_sq_norm_affine h2 mμ _
  have hpos : (𝓛 A).IsPositive := isPositive_toEuclideanCLM transportMatrix_nonneg
  have main : wassersteinSq μ ν = ENNReal.ofReal
      ((Sμ + Sν - 2 * CFC.sqrt (CFC.sqrt Sμ * Sν * CFC.sqrt Sμ)).trace + ‖mμ - mν‖ ^ 2) := by
    rw [hνT, wassersteinSq_map_affine' μ hint _ hpos h, hμ.1]
    congr 1
    have hB : 𝓛 A - 1 = 𝓛 (A - 1) := by rw [map_sub, map_one]
    rw [hB, integral_map hTμ.aemeasurable (by fun_prop)]
    simp_rw [map_add (𝓛 (A - 1)), toEuclideanCLM_apply_apply]
    rw [integral_sq_norm_affine h2 hmean, integral_sq_norm_toEuclideanCLM h2 hcov]
    have e1 : ‖𝓛 (A - 1) mμ‖ ^ 2 + 2 * ⟪𝓛 (A - 1) mμ, h⟫_ℝ + ‖h‖ ^ 2 = ‖mμ - mν‖ ^ 2 := by
      rw [← norm_add_sq_real, norm_sub_rev, hh, map_sub, map_one]
      congr 1
      simp only [_root_.sub_apply, one_apply_eq_self]
      abel_nf
    have e2 : ((A - 1) * R * star ((A - 1) * R)).trace =
        (Sμ + Sν - 2 * CFC.sqrt (CFC.sqrt Sμ * Sν * CFC.sqrt Sμ)).trace := by
      have h3 : (A - 1) * R * star ((A - 1) * R) = A * Sμ * A - A * Sμ - Sμ * A + Sμ := by
        rw [star_mul, star_sqrt, star_sub, star_one, transportMatrix_star,
          show (A - 1) * R * (R * (A - 1)) = (A - 1) * (R * R) * (A - 1) by simp only [mul_assoc],
          hRR]
        simp only [sub_mul, mul_sub, one_mul, mul_one]
        abel
      rw [h3, transportMatrix_mul hSμ hSν, trace_add, trace_sub, trace_sub, trace_sub, trace_add,
        trace_mul_comm Sμ A, trace_transportMatrix_mul hSμ, two_mul, trace_add]
      ring
    linarith
  refine ⟨hμ, hν, main, fun hcomm => ?_⟩
  rw [main]
  have hRν : Commute R Sν := by rw [hR, CFC.sqrt_eq_cfc]; exact Commute.cfc_nnreal hcomm _
  have hRQ : Commute R Q := by rw [hQ, CFC.sqrt_eq_cfc]; exact (Commute.cfc_nnreal hRν.symm _).symm
  have hsqrt : CFC.sqrt (R * Sν * R) = R * Q :=
    CFC.sqrt_unique
      (by rw [← hQQ, mul_assoc R Q, hRQ.eq, ← mul_assoc, mul_assoc R]; simp only [mul_assoc])
      (mul_nonneg_of_commute (CFC.sqrt_nonneg _) (CFC.sqrt_nonneg _) hRQ)
  rw [hsqrt, sq (R - Q), sub_mul, mul_sub, mul_sub, hRR, hQQ, ← hRQ.eq, two_mul]
  congr 3
  abel

/-- **Positive-definite case of Lemma 2.2.** Let `η` be a rotationally invariant probability
measure on `ℝᵈ` with finite second moment, zero mean and identity covariance. Let `μ`, `ν` be
its images under
`x ↦ m_μ + √Σ_μ x` and `x ↦ m_ν + √Σ_ν x`, with `Σ_μ`, `Σ_ν` symmetric positive definite
matrices. Then `μ`, `ν` have means `m_μ`, `m_ν` and covariances `Σ_μ`, `Σ_ν`, and
`W₂²(μ,ν) = Tr(Σ_μ + Σ_ν - 2 √(√Σ_μ Σ_ν √Σ_μ)) + |m_μ - m_ν|²`; if moreover `Σ_μ` and `Σ_ν`
commute, `W₂²(μ,ν) = Tr((√Σ_μ - √Σ_ν)²) + |m_μ - m_ν|²`. Square roots are those of the
continuous functional calculus (`CFC.sqrt`) for the order on matrices. -/
alias wassersteinSq_elliptic := wassersteinSq_elliptic'

end Cutfast
