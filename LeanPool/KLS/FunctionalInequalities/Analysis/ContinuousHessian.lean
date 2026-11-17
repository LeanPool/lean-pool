/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.ContinuousDerivative
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.SecondOrder.HessianRegularity
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# C² from a continuous Hessian representative

For `u : ℝⁿ → ℝ` (no convexity assumed): the coordinate identity between `hessianMatrix u` and the
derivative of the
gradient; a `C¹` function with Lipschitz gradient whose Hessian agrees a.e. with a continuous matrix
field is `C²` with that
Hessian; and, with the quantitative floor `ae_posSemidef_hessianMatrix_sub_of_log_det` of
`Convex/SecondOrder/HessianRegularity`, an a.e. positive definite log-determinant equation with cap
holds at every point
once the Hessian is continuous.
-/

@[expose] public section

/-! ## Continuous Hessians and the everywhere log-determinant equation -/

noncomputable section ContinuousHessian

open MeasureTheory Set Metric Matrix
open scoped NNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis

/-- Coordinate identity: `hessianMatrix u x i j = (D(∇u)(x) e_i)_j`, for every `u` and `x`. -/
theorem hessian_coordinate_gradient_fderiv {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    hessianMatrix u x i j =
      (fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ i)) j := by
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv
  have he : fderiv ℝ u = T ∘ gradient u :=
    funext fun y => (T.apply_symm_apply (fderiv ℝ u y)).symm
  have hd : fderiv ℝ (fderiv ℝ u) x =
      T.toContinuousLinearMap.comp (fderiv ℝ (gradient u) x) :=
    (congrArg (fun f => fderiv ℝ f x) he).trans T.comp_fderiv
  change fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j) = _
  rw [hd]
  change inner ℝ (fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ i))
    (EuclideanSpace.basisFun (Fin n) ℝ j) = _
  exact EuclideanSpace.inner_basisFun_real (Fin n)
    (fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ i)) j

private def matrixDerivative {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ∑ i : Fin n, ∑ j : Fin n, A i j •
    (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)).smulRight
      (EuclideanSpace.basisFun (Fin n) ℝ j)

private theorem matrixDerivative_basis_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) : matrixDerivative A (EuclideanSpace.basisFun (Fin n) ℝ i) j = A i j := by
  simp [matrixDerivative, EuclideanSpace.inner_single_left, Pi.single_apply]

/--
A `C¹` function with Lipschitz gradient whose Hessian agrees a.e. with a continuous matrix field `B`
is `C²`, and its
classical Hessian equals `B` everywhere. -/
theorem contDiff_two_of_continuous_ae_hessian {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {L : ℝ≥0} (hG : LipschitzWith L (gradient u))
    (B : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ) (hB : Continuous B)
    (hAE : B =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))] hessianMatrix u) :
    ContDiff ℝ 2 u ∧ hessianMatrix u = B := by
  have hDcont : Continuous (fun x => matrixDerivative (B x)) := by
    unfold matrixDerivative
    fun_prop
  have hDAE :
    fderiv ℝ (gradient u) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => matrixDerivative (B x)) := by
    filter_upwards [hAE] with x hx
    have hLin : (fderiv ℝ (gradient u) x).toLinearMap = (matrixDerivative (B x)).toLinearMap := by
      apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
      intro i
      ext j
      change
        (fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ i)) j =
          matrixDerivative (B x) (EuclideanSpace.basisFun (Fin n) ℝ i) j
      rw [← hessian_coordinate_gradient_fderiv u x i j, ← hx, matrixDerivative_basis_apply]
    apply ContinuousLinearMap.ext
    intro v
    exact DFunLike.congr_fun hLin v
  obtain ⟨hGrad, hGradC1⟩ :=
    hasFDerivAt_of_lipschitz_continuous_ae_fderiv hG (fun x => matrixDerivative (B x)) hDcont
      hDAE
  have hEvery : hessianMatrix u = B := by
    funext x
    ext i j
    rw [hessian_coordinate_gradient_fderiv u x i j, (hGrad x).fderiv,
      matrixDerivative_basis_apply]
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv
  have he : fderiv ℝ u = T ∘ gradient u :=
    funext fun y => (T.apply_symm_apply (fderiv ℝ u y)).symm
  have hdf : ContDiff ℝ 1 (fderiv ℝ u) := by
    rw [he]
    exact T.contDiff.comp hGradC1
  have hu2 : ContDiff ℝ 2 u :=
    (contDiff_succ_iff_fderiv (n := 1)).mpr ⟨hu.differentiable (by norm_num), by simp, hdf⟩
  exact ⟨hu2, hEvery⟩

/-- The real positive semidefinite cone is closed. -/
private theorem isClosed_psd_for_equation {n : ℕ} :
    IsClosed {A : Matrix (Fin n) (Fin n) ℝ | A.PosSemidef} := by
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec, Set.ofPred_and, Set.ofPred_forall]
  apply IsClosed.inter
  · change IsClosed {A : Matrix (Fin n) (Fin n) ℝ | star A = A}
    exact isClosed_eq continuous_star continuous_id
  · apply isClosed_iInter
    intro x
    exact isClosed_le continuous_const (by fun_prop)

/--
Everywhere log-determinant equation from a continuous Hessian. If the Hessian is continuous, `g` is
continuous and a.e.
the Hessian is positive definite with `log det = g` and `≤ K·I`, then all three hold at EVERY point.
The cap is a closed
condition. Positive definiteness uses the quantitative floor
`ae_posSemidef_hessianMatrix_sub_of_log_det` on a closed ball,
carried to the center by the closed PSD cone and the support of Lebesgue measure; it is not inferred
from a.e. strict
positivity. The equation then follows by continuity. -/
theorem everywhere_posDef_logdet_of_continuous_hessian_ae {n : ℕ} (hn : 0 < n)
    {u g : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ} (hK : 0 < K)
    (hH : Continuous (hessianMatrix u)) (hg : Continuous g)
    (hdata :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
          Real.log (hessianMatrix u x).det = g x ∧
            (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) :
    ∀ x,
      (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = g x ∧
          (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef := by
  let μ0 := (volume : Measure (EuclideanSpace ℝ (Fin n)))
  have hcapClosed :
    IsClosed {x | (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef} :=
    isClosed_psd_for_equation.preimage (by fun_prop)
  have hcap (x : EuclideanSpace ℝ (Fin n)) :
    (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef :=
    μ0.support_subset_of_isClosed hcapClosed (hdata.mono fun _ hx => hx.2.2)
      (by rw [Measure.support_eq_univ]; trivial)
  have hPD (x : EuclideanSpace ℝ (Fin n)) : (hessianMatrix u x).PosDef := by
    obtain ⟨δ, hδ, hfloor⟩ :=
      ae_posSemidef_hessianMatrix_sub_of_log_det hn hK hg hdata (isCompact_closedBall x (1 : ℝ))
    have hclosed :
      IsClosed {y | (hessianMatrix u y - δ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef} :=
      isClosed_psd_for_equation.preimage (by fun_prop)
    have hxs : x ∈ (μ0.restrict (closedBall x 1)).support :=
      Measure.interior_inter_support
        ⟨ball_subset_interior_closedBall (mem_ball_self zero_lt_one), by
          rw [Measure.support_eq_univ]; trivial⟩
    have hfloorx := (μ0.restrict (closedBall x 1)).support_subset_of_isClosed hclosed hfloor hxs
    have hδeq : Matrix.diagonal (fun _ : Fin n => δ) = δ • (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j
      simp [Matrix.diagonal, Matrix.one_apply]
    have hδPD : (δ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef :=
      hδeq ▸ Matrix.PosDef.diagonal (fun _ => hδ)
    have hp := hδPD.add_posSemidef hfloorx
    have he :
      δ • (1 : Matrix (Fin n) (Fin n) ℝ) +
          (hessianMatrix u x - δ • (1 : Matrix (Fin n) (Fin n) ℝ)) =
        hessianMatrix u x := by
      abel
    rwa [he] at hp
  have hlog : Continuous (fun x => Real.log (hessianMatrix u x).det) :=
    hH.matrix_det.log (fun x => (hPD x).det_pos.ne')
  have heq := μ0.eq_of_ae_eq (hdata.mono fun _ hx => hx.2.1) hlog hg
  exact fun x => ⟨hPD x, congrFun heq x, hcap x⟩

end FunctionalInequalities.Analysis

end ContinuousHessian
