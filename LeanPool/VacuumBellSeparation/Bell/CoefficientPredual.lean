/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.NormalityBoundedWOTEquivalence
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.Basic

/-!
The norm-closed span of the literal original-H matrix coefficients, inside
the full continuous dual of the original VNA. Its positive cone is exactly
the order-normal positive cone. The canonical evaluation into its dual is
isometric; surjectivity and the predual/ultraweak identification are separate.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open scoped Topology InnerProductSpace ComplexOrder BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance coefficient_vna_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_vonNeumannAlgebra M

/-- Continuous linear functional which evaluates a matrix coefficient on the algebra. -/
def matrixCoefficientDual (M : VonNeumannAlgebra H) (x y : H) :
    StrongDual ℂ M.toStarSubalgebra :=
  ((innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ H y)).comp
    M.toStarSubalgebra.toSubmodule.subtypeL

@[simp] theorem matrixCoefficientDual_apply (M : VonNeumannAlgebra H) (x y : H)
    (a : M.toStarSubalgebra) :
    matrixCoefficientDual M x y a = inner ℂ x ((a : H →L[ℂ] H) y) := rfl

theorem matrixCoefficientDual_norm_le (M : VonNeumannAlgebra H) (x y : H) :
    ‖matrixCoefficientDual M x y‖ ≤ ‖x‖ * ‖y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro a
  calc
    ‖matrixCoefficientDual M x y a‖ ≤ ‖x‖ * ‖(a : H →L[ℂ] H) y‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖(a : H →L[ℂ] H)‖ * ‖y‖) :=
      mul_le_mul_of_nonneg_left ((a : H →L[ℂ] H).le_opNorm y) (norm_nonneg _)
    _ = (‖x‖ * ‖y‖) * ‖a‖ := by
      change ‖x‖ * (‖a‖ * ‖y‖) = (‖x‖ * ‖y‖) * ‖a‖
      ring

/-- Matrix coefficient span given by `Submodule.span ℂ (Set.range (fun p : H × H =>
matrixCoefficientDual M p.1 p.2))`. -/
def matrixCoefficientSpan (M : VonNeumannAlgebra H) :
    Submodule ℂ (StrongDual ℂ M.toStarSubalgebra) :=
  Submodule.span ℂ (Set.range (fun p : H × H => matrixCoefficientDual M p.1 p.2))

/-- Norm closure of the span of the matrix coefficient functionals on the algebra. -/
def coefficientPredual (M : VonNeumannAlgebra H) :
    Submodule ℂ (StrongDual ℂ M.toStarSubalgebra) :=
  (matrixCoefficientSpan M).topologicalClosure

-- Cache the canonical subtype/continuous-dual norms before nested-dual headers.
instance coefficientPredualSubmoduleNormed (M : VonNeumannAlgebra H) :
    NormedAddCommGroup (coefficientPredual M) := Submodule.normedAddCommGroup _

instance coefficientPredualSubmoduleSpace (M : VonNeumannAlgebra H) :
    NormedSpace ℂ (coefficientPredual M) := Submodule.normedSpace _

instance coefficientPredualSecondDualNormed (M : VonNeumannAlgebra H) :
    NormedAddCommGroup (StrongDual ℂ (coefficientPredual M)) :=
  ContinuousLinearMap.toNormedAddCommGroup

theorem matrixCoefficientDual_mem_span (M : VonNeumannAlgebra H) (x y : H) :
    matrixCoefficientDual M x y ∈ matrixCoefficientSpan M :=
  Submodule.subset_span ⟨(x, y), rfl⟩

theorem matrixCoefficientDual_mem_predual (M : VonNeumannAlgebra H) (x y : H) :
    matrixCoefficientDual M x y ∈ coefficientPredual M :=
  (matrixCoefficientSpan M).le_topologicalClosure (matrixCoefficientDual_mem_span M x y)

theorem finiteVectorCoefficient_mem_span (M : VonNeumannAlgebra H)
    (f : StrongDual ℂ M.toStarSubalgebra) (hf : IsFiniteVectorCoefficient M f) :
    f ∈ matrixCoefficientSpan M := by
  obtain ⟨n, x, y, c, he⟩ := hf
  have heq : f = ∑ i, c i • matrixCoefficientDual M (x i) (y i) := by
    ext a
    simpa only [sum_apply, smul_apply, smul_eq_mul,
      matrixCoefficientDual_apply] using he a
  rw [heq]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (matrixCoefficientDual_mem_span M (x i) (y i))

theorem continuous_vnaWOTBall_eval_of_mem_coefficientSpan
    (M : VonNeumannAlgebra H) (R : ℝ) (f : StrongDual ℂ M.toStarSubalgebra)
    (hf : f ∈ matrixCoefficientSpan M) :
    Continuous (fun T : vnaWOTBall M R => f (vnaWOTBallElement T)) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨⟨x, y⟩, rfl⟩ := hg
      exact (ContinuousLinearMapWOT.continuous_iff.mp
        (continuous_subtype_val : Continuous (fun T : vnaWOTBall M R => T.1))) y x
  | zero => exact continuous_const
  | add g h hg hh hgc hhc => exact hgc.add hhc
  | smul c g hg hgc =>
      change Continuous (fun T : vnaWOTBall M R => c • g (vnaWOTBallElement T))
      exact (continuous_const : Continuous (fun _ : vnaWOTBall M R => c)).smul hgc

theorem continuous_vnaWOTBall_eval_of_mem_coefficientPredual
    (M : VonNeumannAlgebra H) (R : ℝ)
    (f : StrongDual ℂ M.toStarSubalgebra) (hf : f ∈ coefficientPredual M) :
    Continuous (fun T : vnaWOTBall M R => f (vnaWOTBallElement T)) := by
  apply continuous_vnaWOTBall_eval_of_norm_approximation M R f
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hf ε hε
  refine ⟨g, continuous_vnaWOTBall_eval_of_mem_coefficientSpan M R g hg, ?_⟩
  simpa only [dist_eq_norm] using hfg

theorem isNormalFunctional_iff_mem_coefficientPredual
    (M : VonNeumannAlgebra H) (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) :
    IsNormalFunctional M φ ↔
      (PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap ∈ coefficientPredual M := by
  constructor
  · intro hn
    apply closure_mono (fun f hf => finiteVectorCoefficient_mem_span M f hf)
      ((isNormalFunctional_iff_mem_closure_coefficients M φ).mp hn)
  · intro hf
    apply isNormalFunctional_of_continuous_boundedWOT M φ
    intro R _
    exact continuous_vnaWOTBall_eval_of_mem_coefficientPredual M R
      (PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap hf

/-- Evaluation of a coefficient-predual element at an operator in the algebra. -/
def coefficientPredualEvaluation (M : VonNeumannAlgebra H) (a : M.toStarSubalgebra) :
    StrongDual ℂ (coefficientPredual M) :=
  (ContinuousLinearMap.apply ℂ ℂ a).comp (coefficientPredual M).subtypeL

@[simp] theorem coefficientPredualEvaluation_apply (M : VonNeumannAlgebra H)
    (a : M.toStarSubalgebra) (f : coefficientPredual M) :
    coefficientPredualEvaluation M a f = f.1 a := rfl

theorem coefficientPredualEvaluation_norm_le (M : VonNeumannAlgebra H)
    (a : M.toStarSubalgebra) : ‖coefficientPredualEvaluation M a‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  exact (f.1.le_opNorm a).trans_eq (mul_comm _ _)

theorem coefficientPredualEvaluation_norm (M : VonNeumannAlgebra H)
    (a : M.toStarSubalgebra) : ‖coefficientPredualEvaluation M a‖ = ‖a‖ := by
  apply le_antisymm (coefficientPredualEvaluation_norm_le M a)
  change ‖(a : H →L[ℂ] H)‖ ≤ _
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (norm_nonneg _)
  intro x y hx hy
  let f : coefficientPredual M :=
    ⟨matrixCoefficientDual M y x, matrixCoefficientDual_mem_predual M y x⟩
  have hf : ‖f‖ ≤ 1 := by
    exact (matrixCoefficientDual_norm_le M y x).trans_eq (by rw [hy, hx, mul_one])
  have he : ‖inner ℂ y ((a : H →L[ℂ] H) x)‖ ≤ ‖coefficientPredualEvaluation M a‖ :=
    ((coefficientPredualEvaluation M a).le_opNorm f).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hf (norm_nonneg _))
  have hr := Complex.re_le_norm (inner ℂ y ((a : H →L[ℂ] H) x))
  change RCLike.re (inner ℂ y ((a : H →L[ℂ] H) x)) ≤ _ at hr
  rw [inner_re_symm (𝕜 := ℂ)] at hr
  exact hr.trans he

end VacuumBellSeparation.Bipartite
