/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Operator.FredholmIsolation

/-!
# Analytic and Fredholm bridges for bundled-domain pencils

This file supplies generic algebra around the affine pencil `z ↦ z - A` of a
`DomainOperator`.  It separates three levels which are easy to
conflate in an analytic-Fredholm argument:

* the pencil itself is an entire operator-valued function;
* the intrinsic resolvent set consists of the points at which the
  domain-to-state pencil is continuously invertible;
* the pencil factors exactly through its value at a base point and a domain
  correction, so the resolvent set is open.

It also records that normalizing a compact factor by the identity leaves it
unchanged (`CompactAffinePencil.normalized_id`).

Compact-perturbation Fredholmness and the analytic Fredholm theorem are not
available in Mathlib 4.35.0; this development proves them in `CompactAtkinson`,
`CompactAtkinsonIndexZero` and `AnalyticFredholmContinuation`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Set
open scoped LinearMap.FiniteRangeSetoid

universe u v

namespace ContinuousLinearMap

variable {E : Type u}
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- For a continuous linear endomorphism, the bundled-equivalence notion of
invertibility agrees with being a unit in the endomorphism ring. -/
theorem isInvertible_iff_isUnit {T : E →L[ℂ] E} :
    T.IsInvertible ↔ IsUnit T := by
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨ContinuousLinearEquiv.toUnit e, rfl⟩
  · rintro ⟨U, rfl⟩
    exact ⟨ContinuousLinearEquiv.ofUnit U, rfl⟩

/-- A perturbation of the identity by an operator of norm less than one is
continuously invertible. -/
theorem isInvertible_id_add_of_norm_lt_one [CompleteSpace E]
    {T : E →L[ℂ] E} (hT : ‖T‖ < 1) :
    (ContinuousLinearMap.id ℂ E + T).IsInvertible := by
  change (1 + T).IsInvertible
  rw [isInvertible_iff_isUnit]
  have hunit : IsUnit (1 - (-T)) :=
    isUnit_one_sub_of_norm_lt_one (by simpa using hT)
  simpa only [sub_neg_eq_add] using hunit

end ContinuousLinearMap

namespace DomainOperator

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]

/-! ## The affine pencil -/

/-- The affine domain pencil acts by `z • embedding d - op d`, the bundled-domain form of
`z - A`. -/
@[simp] theorem pencil_apply (A : DomainOperator X D) (z : ℂ) (d : D) :
    A.pencil z d = z • A.embedding d - A.op d :=
  rfl

/-- The derivative of the affine domain pencil is its embedding. -/
theorem pencil_hasDerivAt (A : DomainOperator X D) (z : ℂ) :
    HasDerivAt A.pencil A.embedding z := by
  change HasDerivAt (fun w : ℂ ↦ w • A.embedding - A.op) A.embedding z
  simpa only [one_smul] using
    ((hasDerivAt_id' z).smul_const A.embedding).sub_const A.op

/-- In particular, the domain pencil is norm-continuous. -/
theorem continuous_pencil (A : DomainOperator X D) :
    Continuous A.pencil :=
  continuous_iff_continuousAt.mpr fun z ↦ (A.pencil_hasDerivAt z).continuousAt

/-! ## Point resolvents and continuous invertibility -/

/-- The intrinsic resolvent set of a bundled-domain operator. -/
def resolventSet (A : DomainOperator X D) : Set ℂ :=
  {z | (A.pencil z).IsInvertible}

/-! ## Exact base-point factorizations -/

/-- The correction acting on the graph domain in the base-point
factorization of the pencil. -/
def domainCorrection (A : DomainOperator X D) (z₀ z : ℂ) : D →L[ℂ] D :=
  ContinuousLinearMap.id ℂ D +
    (z - z₀) • ((A.pencil z₀).inverse.comp A.embedding)

/-- Exact right factorization of the pencil through an invertible base
point. -/
theorem pencil_factor_domain (A : DomainOperator X D) (z₀ z : ℂ)
    (h₀ : (A.pencil z₀).IsInvertible) :
    (A.pencil z₀).comp (A.domainCorrection z₀ z) = A.pencil z := by
  ext d
  simp only [ContinuousLinearMap.comp_apply, domainCorrection,
    add_apply, ContinuousLinearMap.id_apply, smul_apply, map_add, map_smul]
  rw [h₀.self_apply_inverse]
  simp only [pencil_apply]
  module

/-- Multiplication on the left by a continuously invertible map preserves
continuous invertibility. -/
theorem isInvertible_comp_iff_of_left {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    {U : X →L[ℂ] Y} {T : D →L[ℂ] X} (hU : U.IsInvertible) :
    (U.comp T).IsInvertible ↔ T.IsInvertible := by
  rcases hU with ⟨e, rfl⟩
  exact ContinuousLinearMap.isInvertible_equiv_comp

/-- The base-point correction is invertible exactly when the pencil at the
new point is invertible. -/
theorem domainCorrection_isInvertible_iff (A : DomainOperator X D)
    (z₀ z : ℂ) (h₀ : (A.pencil z₀).IsInvertible) :
    (A.domainCorrection z₀ z).IsInvertible ↔ (A.pencil z).IsInvertible := by
  rw [← A.pencil_factor_domain z₀ z h₀]
  exact (isInvertible_comp_iff_of_left h₀).symm

/-- The intrinsic resolvent set is open.  The proof uses the exact base-point
factorization and a Neumann-series ball in the graph-domain endomorphism
algebra. -/
theorem isOpen_resolventSet [CompleteSpace D] (A : DomainOperator X D) :
    IsOpen A.resolventSet := by
  rw [isOpen_iff_mem_nhds]
  intro z₀ hz₀
  have h₀ : (A.pencil z₀).IsInvertible := hz₀
  let B : D →L[ℂ] D := (A.pencil z₀).inverse.comp A.embedding
  let ε : ℝ := (‖B‖ + 1)⁻¹
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  refine Filter.mem_of_superset (Metric.ball_mem_nhds z₀ hε) ?_
  intro z hz
  have hnorm : ‖z - z₀‖ < ε := by
    simpa only [Metric.mem_ball, dist_eq_norm_sub] using hz
  have hprod : ‖z - z₀‖ * ‖B‖ < 1 := by
    calc
      ‖z - z₀‖ * ‖B‖ ≤ ‖z - z₀‖ * (‖B‖ + 1) := by
        gcongr
        norm_num
      _ < ε * (‖B‖ + 1) := by
        exact mul_lt_mul_of_pos_right hnorm (by positivity)
      _ = 1 := by
        dsimp [ε]
        field_simp
  have hsmall : ‖(z - z₀) • B‖ < 1 := by
    simpa only [norm_smul] using hprod
  have hcorr : (A.domainCorrection z₀ z).IsInvertible := by
    change (ContinuousLinearMap.id ℂ D + (z - z₀) • B).IsInvertible
    exact ContinuousLinearMap.isInvertible_id_add_of_norm_lt_one hsmall
  exact (A.domainCorrection_isInvertible_iff z₀ z h₀).mp hcorr

end DomainOperator

/-! ## Compact scalar corrections -/

namespace CompactAffinePencil

variable {E : Type u}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Normalizing by the identity leaves an endomorphism unchanged. -/
theorem normalized_id (K : E →L[ℂ] E) :
    CompactFactor.normalized (ContinuousLinearMap.id ℂ E) K = K := by
  ext x
  simp [CompactFactor.normalized]

end CompactAffinePencil

end

end FastDynamo
