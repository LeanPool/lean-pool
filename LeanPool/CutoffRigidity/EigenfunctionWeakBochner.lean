/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.EigenfunctionLocalizedBochner
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Differentiated weak eigenfunction equations at the paper's C² regularity

Coordinate integration by parts differentiates the actual eigenfunction
PDE in weak form, avoiding any assumption that its third derivatives exist.
All test functions are compactly supported, and their integration-domain
conditions are proved from continuity and compact support.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology
open scoped ENNReal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The scalar coordinate weighted-adjoint expression. -/
@[expose] noncomputable def coordinateWeightedAdjoint (i : Fin d) (V ψ : E → ℝ) (x : E) : ℝ :=
  coordinateDerivative i ψ x - ψ x * coordinateDerivative i V x

/-- Weighted directional integration by parts for a compact C¹ test, with
all three product-integrability conditions proved rather than assumed. -/
theorem compact_directional_gibbs_ibp {V ψ g : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hψ : ContDiff ℝ 1 ψ) (hg : ContDiff ℝ 1 g)
    (hψc : HasCompactSupport ψ) (i : Fin d) :
    (∫ x, ψ x * coordinateDerivative i g x ∂gibbsMeasure volume V) =
      -(∫ x, coordinateWeightedAdjoint i V ψ x * g x ∂gibbsMeasure volume V) := by
  have hcψ := continuous_coordinateDerivative_of_c1 hψ i
  have hcg := continuous_coordinateDerivative_of_c1 hg i
  have hcV := (c1_coordinateDerivative_of_c2 hV i).continuous
  have hψic : HasCompactSupport (coordinateDerivative i ψ) :=
    hψc.fderiv_apply ℝ (EuclideanSpace.single i 1)
  apply integral_mul_fderiv_gibbs_eq_neg volume (hV.differentiable (by norm_num))
    (hψ.differentiable (by norm_num)) (hg.differentiable (by norm_num)) (EuclideanSpace.single i 1)
  · exact integrable_cutoff_mul_continuous hV.continuous hψ.continuous hψc hg.continuous
  · exact integrable_cutoff_mul_continuous hV.continuous hψ.continuous hψc hcg
  · have h1 := integrable_cutoff_mul_continuous hV.continuous hcψ hψic hg.continuous
    have h2 := integrable_cutoff_mul_continuous hV.continuous hψ.continuous hψc
      (g := fun x => coordinateDerivative i V x * g x) (by fun_prop)
    convert h1.sub h2 using 1
    funext x
    simp only [Pi.sub_apply, coordinateDerivative]
    ring

/-- C² coefficients and a compact C² test give a compact C¹ weighted-adjoint test. -/
theorem c1_coordinateWeightedAdjoint {V ψ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hψ : ContDiff ℝ 2 ψ) (i : Fin d) :
    ContDiff ℝ 1 (coordinateWeightedAdjoint i V ψ) := by
  have hψi := c1_coordinateDerivative_of_c2 hψ i
  have hVi := c1_coordinateDerivative_of_c2 hV i
  exact hψi.sub ((hψ.of_le (by norm_num)).mul hVi)

theorem hasCompactSupport_coordinateWeightedAdjoint {V ψ : E → ℝ}
    (hψc : HasCompactSupport ψ) (i : Fin d) :
    HasCompactSupport (coordinateWeightedAdjoint i V ψ) := by
  have h1 : HasCompactSupport (coordinateDerivative i ψ) := hψc.fderiv_apply ℝ
    (EuclideanSpace.single i 1)
  have h2 := hψc.mul_right (f' := coordinateDerivative i V)
  unfold coordinateWeightedAdjoint
  simpa only [Pi.sub_def, Pi.mul_def] using h1.sub h2

/-- The actual derivative of the weighted-adjoint test. -/
theorem coordinateDerivative_weightedAdjoint {V ψ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hψ : ContDiff ℝ 2 ψ) (i j : Fin d) (x : E) :
    coordinateDerivative j (coordinateWeightedAdjoint i V ψ) x =
      coordinateDerivative j (coordinateDerivative i ψ) x -
        coordinateDerivative j ψ x * coordinateDerivative i V x -
          ψ x * coordinateDerivative j (coordinateDerivative i V) x := by
  have hDψ := c1_coordinateDerivative_of_c2 hψ i
  have hDV := c1_coordinateDerivative_of_c2 hV i
  have hm : DifferentiableAt ℝ (fun y => ψ y * coordinateDerivative i V y) x := by
    simpa only [Pi.mul_def] using
      ((hψ.differentiable (by norm_num)) x).mul ((hDV.differentiable (by norm_num)) x)
  unfold coordinateDerivative at ⊢
  change fderiv ℝ (fun y => coordinateDerivative i ψ y - ψ y * coordinateDerivative i V y) x
    (EuclideanSpace.single j 1) = _
  rw [fderiv_fun_sub ((hDψ.differentiable (by norm_num)) x)
    hm,
    fderiv_fun_mul ((hψ.differentiable (by norm_num)) x) ((hDV.differentiable (by norm_num)) x)]
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
  unfold coordinateDerivative
  ring

theorem continuous_coordinateWeightedAdjoint {V ψ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hψ : ContDiff ℝ 1 ψ) (i : Fin d) :
    Continuous (coordinateWeightedAdjoint i V ψ) :=
  (continuous_coordinateDerivative_of_c1 hψ i).sub
    (hψ.continuous.mul (c1_coordinateDerivative_of_c2 hV i).continuous)

/-- Testing the actual eigenfunction PDE with the coordinate weighted
adjoint shifts its derivative to the compact test without differentiating Lf. -/
theorem weightedAdjoint_test_eigenfunction {V f ψ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hψ : ContDiff ℝ 2 ψ)
    (hψc : HasCompactSupport ψ) (ρ : ℝ)
    (heigen : ∀ x, langevinDifferentialOperator V f x = -ρ * f x) (i : Fin d) :
    (∫ x, coordinateWeightedAdjoint i V ψ x * langevinDifferentialOperator V f x
      ∂gibbsMeasure volume V) =
      ρ * (∫ x, ψ x * coordinateDerivative i f x ∂gibbsMeasure volume V) := by
  have hi := compact_directional_gibbs_ibp hV (hψ.of_le (by norm_num))
    (hf.of_le (by norm_num)) hψc i
  have heq (x : E) : coordinateWeightedAdjoint i V ψ x * langevinDifferentialOperator V f x =
      -ρ * (coordinateWeightedAdjoint i V ψ x * f x) := by rw [heigen]; ring
  simp_rw [heq]
  rw [integral_const_mul]
  rw [hi]
  ring

/-- The genuine differentiated weak eigenfunction equation at C² regularity.
Only the compact C² test is differentiated twice; no third derivative of f
is assumed or used. -/
theorem c2_eigenfunction_differentiated_weak_equation {V f ψ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hψ : ContDiff ℝ 2 ψ)
    (hψc : HasCompactSupport ψ) (ρ : ℝ)
    (heigen : ∀ x, langevinDifferentialOperator V f x = -ρ * f x) (i : Fin d) :
    (∫ x, ∑ j : Fin d, coordinateDerivative j ψ x *
      coordinateDerivative j (coordinateDerivative i f) x ∂gibbsMeasure volume V) +
      (∫ x, ψ x * (∑ j : Fin d,
        coordinateDerivative i (coordinateDerivative j V) x * coordinateDerivative j f x)
          ∂gibbsMeasure volume V) =
      ρ * (∫ x, ψ x * coordinateDerivative i f x ∂gibbsMeasure volume V) := by
  let a := coordinateWeightedAdjoint i V ψ
  have ha : ContDiff ℝ 1 a := c1_coordinateWeightedAdjoint hV hψ i
  have hac : HasCompactSupport a := hasCompactSupport_coordinateWeightedAdjoint hψc i
  have hDψ (j : Fin d) := c1_coordinateDerivative_of_c2 hψ j
  have hDf (j : Fin d) := c1_coordinateDerivative_of_c2 hf j
  have hVV (j : Fin d) : Continuous (coordinateDerivative i (coordinateDerivative j V)) :=
    continuous_coordinateDerivative_of_c1 (c1_coordinateDerivative_of_c2 hV j) i
  have hff (j : Fin d) : Continuous (coordinateDerivative j (coordinateDerivative i f)) :=
    continuous_coordinateDerivative_of_c1 (hDf i) j
  have hψjc (j : Fin d) : HasCompactSupport (coordinateDerivative j ψ) :=
    hψc.fderiv_apply ℝ (EuclideanSpace.single j 1)
  have hGradInt (j : Fin d) : Integrable
      (fun x => coordinateDerivative j ψ x * coordinateDerivative j (coordinateDerivative i f) x)
      (gibbsMeasure volume V) :=
    integrable_cutoff_mul_continuous hV.continuous (hDψ j).continuous (hψjc j) (hff j)
  have hHessInt (j : Fin d) : Integrable
      (fun x => ψ x * (coordinateDerivative i (coordinateDerivative j V) x * coordinateDerivative j
        f x))
      (gibbsMeasure volume V) :=
    integrable_cutoff_mul_continuous hV.continuous hψ.continuous hψc
      ((hVV j).mul (hDf j).continuous)
  have hDerInt (j : Fin d) : Integrable
      (fun x => coordinateDerivative j a x * coordinateDerivative j f x)
      (gibbsMeasure volume V) :=
    integrable_cutoff_mul_continuous hV.continuous
      (continuous_coordinateDerivative_of_c1 ha j)
      (hac.fderiv_apply ℝ (EuclideanSpace.single j 1)) (hDf j).continuous
  have hrow (j : Fin d) :
      (∫ x, coordinateDerivative j a x * coordinateDerivative j f x ∂gibbsMeasure volume V) =
        -(∫ x, coordinateDerivative j ψ x * coordinateDerivative j (coordinateDerivative i f) x
          ∂gibbsMeasure volume V) -
        (∫ x, ψ x * (coordinateDerivative i (coordinateDerivative j V) x * coordinateDerivative j f
          x)
          ∂gibbsMeasure volume V) := by
    let b := coordinateWeightedAdjoint i V (coordinateDerivative j ψ)
    have hb : Continuous b := continuous_coordinateWeightedAdjoint hV (hDψ j) i
    have hbc : HasCompactSupport b := hasCompactSupport_coordinateWeightedAdjoint (hψjc j) i
    have hIntb : Integrable (fun x => b x * coordinateDerivative j f x) (gibbsMeasure volume V) :=
      integrable_cutoff_mul_continuous hV.continuous hb hbc (hDf j).continuous
    have hpoint (x : E) : coordinateDerivative j a x * coordinateDerivative j f x =
        b x * coordinateDerivative j f x -
          ψ x * (coordinateDerivative i (coordinateDerivative j V) x * coordinateDerivative j f x)
            := by
      dsimp only [a]
      rw [coordinateDerivative_weightedAdjoint hV hψ,
        coordinateDerivative_commute hψ j i, coordinateDerivative_commute hV j i]
      dsimp only [b, coordinateWeightedAdjoint]
      ring
    have ht := integral_congr_ae (μ := gibbsMeasure volume V) (Filter.Eventually.of_forall hpoint)
    rw [integral_sub hIntb (hHessInt j)] at ht
    have hi := compact_directional_gibbs_ibp hV (hDψ j) (hDf j) (hψjc j) i
    simp_rw [coordinateDerivative_commute hf i j] at hi
    change (∫ x, coordinateDerivative j ψ x * coordinateDerivative j (coordinateDerivative i f) x
      ∂gibbsMeasure volume V) =
      -(∫ x, b x * coordinateDerivative j f x ∂gibbsMeasure volume V) at hi
    linarith
  have henergy := compact_test_gibbs_energy hV ha hf hac
  simp_rw [inner_gradient_eq_sum_fderiv_single] at henergy
  change (∫ x, a x * langevinDifferentialOperator V f x ∂gibbsMeasure volume V) =
    -(∫ x, ∑ j : Fin d, coordinateDerivative j a x * coordinateDerivative j f x
      ∂gibbsMeasure volume V) at henergy
  rw [weightedAdjoint_test_eigenfunction hV hf hψ hψc ρ heigen i,
    integral_finsetSum _ (fun j _ => hDerInt j)] at henergy
  simp_rw [hrow] at henergy
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at henergy
  rw [integral_finsetSum _ (fun j _ => hGradInt j)]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun j _ => hHessInt j)]
  linarith

end CutoffRigidity
