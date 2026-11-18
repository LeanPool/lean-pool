/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Support.Affine
public import LeanPool.KLS.FunctionalInequalities.Probability.Covariance.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Convex.Integral

/-!
# Ambient and intrinsic covariance

Source: Blueprint `lem:ambient-intrinsic-covariance`. For a Borel probability law `μ` with finite
second moment on a finite-dimensional Euclidean space, let `V` be the direction of its affine
support and `ν` its intrinsic law on `V`. Read the intrinsic-coordinate identities first, then
the four covariance statements.

Proved here:

1. `Covariance.operator_apply_eq_zero_of_mem_orthogonal`: the ambient covariance operator
   annihilates `Vᗮ`, because the barycenter lies in the affine support and centered samples lie
   in `V` almost surely;
2. `Covariance.operator_coe_intrinsic`: on `V` the ambient operator is the intrinsic covariance
   operator `Covariance.operator ν`, through `bilin_intrinsic`, which identifies the two
   bilinear forms by transporting the law along the translation and the orthogonal projection;
3. `Covariance.opNorm_operator_intrinsic`: both operators have the same operator norm;
4. `Covariance.intrinsic_operator_inner_self_pos`: the intrinsic covariance is positive definite,
   since a null direction would confine `ν` to a proper affine hyperplane, contradicting the
   fullness of the intrinsic affine support;
5. `Covariance.operator_eq_zero_of_direction_eq_bot`: a zero-dimensional direction gives a zero
   ambient operator.

The second-moment hypothesis is explicit; without it Mathlib's covariance form is zero by
convention and the statements would be vacuous. Nothing here assumes log-concavity, a density,
or positive dimension, and no Poincaré, whitening or KLS statement is asserted.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [FiniteDimensional ℝ E]

namespace FunctionalInequalities.Probability

omit [CompleteSpace E] [BorelSpace E] in
/-- Intrinsic coordinates are, almost everywhere, the orthogonal projection of the displacement
from the chosen support point onto the direction space. -/
theorem intrinsicMap_ae_eq_orthogonalProjection (μ : ProbabilityMeasure E) :
    intrinsicMap μ =ᵐ[(μ : Measure E)]
      fun x ↦ (affineSupport μ).direction.orthogonalProjectionOnto (x - supportPoint μ) := by
  filter_upwards [ae_mem_affineSupport μ] with x hx
  have hdir : x - supportPoint μ ∈ (affineSupport μ).direction :=
    AffineSubspace.vsub_mem_direction hx (origin μ).property
  have hret : retraction μ x = ⟨x, hx⟩ := Subtype.ext (coe_retraction_of_mem μ hx)
  rw [intrinsicMap, hret, coordinateEquiv, AffineIsometryEquiv.coe_vaddConst_symm]
  apply Subtype.ext
  rw [← Submodule.starProjection_apply, Submodule.starProjection_eq_self_iff.mpr hdir]
  rfl

omit [BorelSpace E] in
/-- The barycenter of a probability law with finite second moment lies in its affine support. -/
theorem integral_id_mem_affineSupport (μ : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) : (∫ x, x ∂(μ : Measure E)) ∈ affineSupport μ :=
  (affineSupport μ).convex.integral_mem (isClosed_affineSupport μ) (ae_mem_affineSupport μ)
    (hμ.integrable (by norm_num))

omit [CompleteSpace E] in
/-- The intrinsic law keeps a finite second moment. -/
theorem memLp_id_two_intrinsicMeasure (μ : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) :
    MemLp id 2 (intrinsicMeasure μ : Measure (affineSupport μ).direction) := by
  set P := (affineSupport μ).direction.orthogonalProjectionOnto
  have h1 : MemLp (fun x ↦ x - supportPoint μ) 2 (μ : Measure E) := hμ.sub (memLp_const _)
  have h2 : MemLp (fun x ↦ P (x - supportPoint μ)) 2 (μ : Measure E) := P.comp_memLp' h1
  have h3 : MemLp (intrinsicMap μ) 2 (μ : Measure E) :=
    h2.ae_eq (intrinsicMap_ae_eq_orthogonalProjection μ).symm
  rw [intrinsicMeasure, ProbabilityMeasure.toMeasure_map]
  exact (memLp_map_measure_iff aestronglyMeasurable_id
    (measurable_intrinsicMap μ).aemeasurable).2 h3

end FunctionalInequalities.Probability

namespace FunctionalInequalities.Covariance

open Probability

/-- The ambient covariance operator annihilates the orthogonal complement of the direction of the
affine support. -/
theorem operator_apply_eq_zero_of_mem_orthogonal (μ : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) {w : E} (hw : w ∈ (affineSupport μ).directionᗮ) :
    operator (μ : Measure E) w = 0 := by
  apply ext_inner_right ℝ
  intro y
  rw [operator_inner, inner_zero_left, covarianceBilin_apply hμ]
  have hm : (∫ x, id x ∂(μ : Measure E)) ∈ affineSupport μ := integral_id_mem_affineSupport μ hμ
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_mem_affineSupport μ] with z hz
  have hdir : z - ∫ x, id x ∂(μ : Measure E) ∈ (affineSupport μ).direction :=
    AffineSubspace.vsub_mem_direction hz hm
  change inner ℝ w (z - ∫ x, id x ∂(μ : Measure E)) * inner ℝ y (z - ∫ x, id x ∂(μ : Measure E)) = 0
  rw [Submodule.inner_left_of_mem_orthogonal hdir hw, zero_mul]

/-- The ambient covariance bilinear form restricted to the direction space is the covariance
bilinear form of the intrinsic law. -/
theorem bilin_intrinsic (μ : ProbabilityMeasure E) (hμ : MemLp id 2 (μ : Measure E))
    (v w : (affineSupport μ).direction) :
    covarianceBilin (intrinsicMeasure μ : Measure (affineSupport μ).direction) v w =
      covarianceBilin (μ : Measure E) v w := by
  set P := (affineSupport μ).direction.orthogonalProjectionOnto
  have hshift : Measurable fun x : E ↦ -supportPoint μ + x := by fun_prop
  have hmap : (intrinsicMeasure μ : Measure (affineSupport μ).direction) =
      ((μ : Measure E).map (fun x ↦ -supportPoint μ + x)).map P := by
    rw [intrinsicMeasure, ProbabilityMeasure.toMeasure_map,
      Measure.map_map P.continuous.measurable hshift]
    refine Measure.map_congr ?_
    filter_upwards [intrinsicMap_ae_eq_orthogonalProjection μ] with x hx
    rw [hx, Function.comp_apply, sub_eq_neg_add]
  have hμ' : MemLp id 2 ((μ : Measure E).map fun x ↦ -supportPoint μ + x) :=
    (measurableEmbedding_addLeft _).memLp_map_measure_iff.mpr
      ((memLp_const (-supportPoint μ)).add hμ)
  rw [hmap, covarianceBilin_map hμ' P v w, covarianceBilin_map_const_add,
    Submodule.adjoint_orthogonalProjectionOnto]
  rfl

/-- The ambient covariance operator restricts to the intrinsic covariance operator on the
direction space. -/
theorem operator_coe_intrinsic (μ : ProbabilityMeasure E) (hμ : MemLp id 2 (μ : Measure E))
    (v : (affineSupport μ).direction) :
    operator (μ : Measure E) v =
      (operator (intrinsicMeasure μ : Measure (affineSupport μ).direction) v : E) := by
  set P := (affineSupport μ).direction.orthogonalProjectionOnto
  set ν : Measure (affineSupport μ).direction := (intrinsicMeasure μ).toMeasure
  apply ext_inner_right ℝ
  intro y
  have hy : y = (P y : E) + (y - P y) := (add_sub_cancel _ _).symm
  have hperp : y - (P y : E) ∈ (affineSupport μ).directionᗮ :=
    Submodule.sub_starProjection_mem_orthogonal y
  calc
    inner ℝ (operator (μ : Measure E) v) y = covarianceBilin (μ : Measure E) v y :=
      operator_inner _ _ _
    _ = covarianceBilin (μ : Measure E) v (P y) + covarianceBilin (μ : Measure E) v (y - P y) := by
      conv_lhs => rw [hy]
      rw [map_add]
    _ = covarianceBilin (μ : Measure E) v (P y) := by
      rw [covarianceBilin_comm (v : E) (y - P y), ← operator_inner (μ : Measure E) (y - P y) v,
        operator_apply_eq_zero_of_mem_orthogonal μ hμ hperp, inner_zero_left, add_zero]
    _ = covarianceBilin ν v (P y) := (bilin_intrinsic μ hμ v (P y)).symm
    _ = inner ℝ (operator ν v) (P y) := (operator_inner _ _ _).symm
    _ = inner ℝ (operator ν v : E) (P y : E) := rfl
    _ = inner ℝ (operator ν v : E) y := by
      conv_rhs => rw [hy]
      rw [inner_add_right,
        Submodule.inner_right_of_mem_orthogonal (operator ν v).property hperp, add_zero]

/-- Ambient and intrinsic covariance operators have the same operator norm. -/
theorem opNorm_operator_intrinsic (μ : ProbabilityMeasure E) (hμ : MemLp id 2 (μ : Measure E)) :
    ‖operator (intrinsicMeasure μ : Measure (affineSupport μ).direction)‖ =
      ‖operator (μ : Measure E)‖ := by
  set P := (affineSupport μ).direction.orthogonalProjectionOnto
  set ν : Measure (affineSupport μ).direction := (intrinsicMeasure μ).toMeasure
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_
    calc
      ‖operator ν v‖ = ‖(operator ν v : E)‖ := (Submodule.norm_coe _).symm
      _ = ‖operator (μ : Measure E) v‖ := by rw [operator_coe_intrinsic μ hμ v]
      _ ≤ ‖operator (μ : Measure E)‖ * ‖(v : E)‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖operator (μ : Measure E)‖ * ‖v‖ := by rw [Submodule.norm_coe]
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y ↦ ?_
    have hy : y = (P y : E) + (y - P y) := (add_sub_cancel _ _).symm
    have hperp : y - (P y : E) ∈ (affineSupport μ).directionᗮ :=
      Submodule.sub_starProjection_mem_orthogonal y
    have h0 : operator (μ : Measure E) (y - P y) = 0 :=
      operator_apply_eq_zero_of_mem_orthogonal μ hμ hperp
    calc
      ‖operator (μ : Measure E) y‖ =
          ‖operator (μ : Measure E) (P y) + operator (μ : Measure E) (y - P y)‖ := by
        conv_lhs => rw [hy]
        rw [map_add]
      _ = ‖(operator ν (P y) : E)‖ := by rw [h0, add_zero, operator_coe_intrinsic μ hμ]
      _ = ‖operator ν (P y)‖ := Submodule.norm_coe _
      _ ≤ ‖operator ν‖ * ‖P y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖operator ν‖ * ‖y‖ :=
        mul_le_mul_of_nonneg_left
          ((affineSupport μ).direction.norm_orthogonalProjectionOnto_apply_le y) (norm_nonneg _)

omit [CompleteSpace E] in
/-- The intrinsic covariance operator is positive definite on the direction space. -/
theorem intrinsic_operator_inner_self_pos (μ : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) {v : (affineSupport μ).direction} (hv : v ≠ 0) :
    0 < inner ℝ (operator (intrinsicMeasure μ : Measure (affineSupport μ).direction) v) v := by
  set ν := intrinsicMeasure μ
  have hν : MemLp id 2 (ν : Measure (affineSupport μ).direction) :=
    memLp_id_two_intrinsicMeasure μ hμ
  rw [operator_inner, covarianceBilin_self hν]
  rcases
    (variance_nonneg (fun u ↦ inner ℝ v u)
        (ν : Measure (affineSupport μ).direction)).lt_or_eq with
    h | h
  · exact h
  exfalso
  have hX : MemLp (fun u ↦ inner ℝ v u) 2 (ν : Measure (affineSupport μ).direction) := by
    have := (innerSL ℝ v).comp_memLp' hν
    simpa [Function.comp] using this
  have hev : evariance (fun u ↦ inner ℝ v u) (ν : Measure (affineSupport μ).direction) = 0 := by
    rw [← ofReal_variance hX, ← h, ENNReal.ofReal_zero]
  have hae := (evariance_eq_zero_iff hX.aestronglyMeasurable.aemeasurable).mp hev
  set c : ℝ := ∫ u, inner ℝ v u ∂(ν : Measure (affineSupport μ).direction)
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  set H : AffineSubspace ℝ (affineSupport μ).direction :=
    AffineSubspace.mk' ((c / ‖v‖ ^ 2) • v) (Submodule.span ℝ { v })ᗮ
  have hHclosed : IsClosed (H : Set (affineSupport μ).direction) :=
    H.closed_of_finiteDimensional
  have hmem : ∀ᵐ u ∂(ν : Measure (affineSupport μ).direction), u ∈ H := by
    filter_upwards [hae] with u hu
    have hu' : inner ℝ v u = c := hu
    rw [AffineSubspace.mem_mk', Submodule.mem_orthogonal_singleton_iff_inner_right, vsub_eq_sub,
      inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hu',
      div_mul_cancel₀ c (pow_ne_zero 2 hv'), sub_self]
  have hle := affineSupport_le_of_ae_mem ν H hHclosed hmem
  rw [affineSupport_intrinsicMeasure] at hle
  have hH : H = ⊤ := top_le_iff.mp hle
  have hdir : (Submodule.span ℝ { v })ᗮ = ⊤ := by
    have := congrArg AffineSubspace.direction hH
    rwa [AffineSubspace.direction_mk', AffineSubspace.direction_top] at this
  exact hv (Submodule.span_singleton_eq_bot.mp ((Submodule.orthogonal_eq_top_iff _).mp hdir))

/-- Zero-dimensional affine support forces a zero ambient covariance operator. -/
theorem operator_eq_zero_of_direction_eq_bot (μ : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) (h : (affineSupport μ).direction = ⊥) :
    operator (μ : Measure E) = 0 := by
  ext w
  have hw : w ∈ (affineSupport μ).directionᗮ := by
    rw [h, Submodule.bot_orthogonal_eq_top]; trivial
  simpa using operator_apply_eq_zero_of_mem_orthogonal μ hμ hw

end FunctionalInequalities.Covariance
