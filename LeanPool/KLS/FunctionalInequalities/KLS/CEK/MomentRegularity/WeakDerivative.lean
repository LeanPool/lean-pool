/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Coordinates
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Weak
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Coercivity
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Gradient.Lipschitz
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.SecondOrder.HessianRegularity
public import LeanPool.KLS.FunctionalInequalities.Analysis.Lipschitz.Exponential
public import LeanPool.KLS.FunctionalInequalities.Analysis.Lipschitz.Gradient
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.DeterminantDerivative
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.WeakDerivative
public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.Isotropic
public import LeanPool.KLS.FunctionalInequalities.KLS.CEK.MomentRegularity.Potential

/-!
# Regular-source weak tensors and first Monge–Ampere derivatives
-/

@[expose] public section

section RegularSource

/-! Shared regular-source hypotheses for the moment-map and quadratic-variance results.
Only the source-law theorems include these hypotheses; auxiliary lemmas retain their own scope. -/

open MeasureTheory Set
open scoped ContDiff

variable {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ)

section

open MeasureTheory Set Filter
open scoped RealInnerProductSpace ContDiff Topology
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis
include hn hκ hK hKc hKint hW hstrong hμ hiso in
/-- Actual source-law tensor: both original hw and hF inputs are produced;
all original regular-class data and the weak/local-L2 tensor are retained. -/
theorem exists_regular_moment_weak_tensor :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal) (T :
      EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧
        LipschitzWith L u ∧
          (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
                (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
              ContDiff ℝ 1 u ∧
                LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
                  LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
                    (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
                      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
                          (hessianMatrix u x).PosDef ∧
                            Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
                              ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
                                  hessianMatrix u x).PosSemidef) ∧
                        ∀ k i j,
                          HasWeakDerivAlong (fun x => hessianMatrix u x i j)
                              (fun x => T x k i j) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
                            ∀ S : Set (EuclideanSpace ℝ (Fin n)),
                              IsCompact S →
                                MemLp (fun x => T x k i j) 2
                                  ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  obtain ⟨u, L, hconv, hLip, hnorm, hmap, hC1, hG, hdata⟩ :=
    exists_regular_moment_potential hn hκ hK hKc hKint hW hstrong μ hμ hiso
  have hV : ContDiff ℝ 1 W := hW.of_le (WithTop.coe_le_coe.mpr le_top)
  have hw :=
    secondDifference_le_of_map_gradient hLip hconv hnorm hK hKc hV hκ hstrong (hmap.trans hμ)
      hC1
  obtain ⟨LF, hF⟩ := exists_lipschitzWith_neg_add_comp_gradient hLip hG hV
  have hVc : ConvexOn ℝ univ W :=
    UniformConvexOn.convexOn (strongConvexOn_iff_convex.mpr hstrong) fun r => by positivity
  obtain ⟨T, hT⟩ :=
    exists_weak_third_derivative hC1 hconv hG hV hVc hF (show 0 < 16 / κ by positivity) hdata hw
  exact ⟨u, L, LF, T, hconv, hLip, hnorm, hmap, hC1, hG, hF, hw, hdata, hT⟩

open Matrix Metric
open scoped Matrix.Norms.Elementwise

/-- The actual normalized convex potential supplies an exponent upper bound.
No bound on F or minimum of u is assumed. -/
private theorem exponent_upper_of_normalized_convex {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hconv : ConvexOn ℝ univ u) (hLip : LipschitzWith L u)
    (hnorm : (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1)
    (hV : Continuous V) :
    ∃ C : ℝ, ∀ x, -u x + V (gradient u x) ≤ C := by
  have hint : Integrable (fun x => Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; exact one_ne_zero)
  obtain ⟨x₀, hx₀⟩ :=
    (exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg
      volume hconv hint).1
  obtain ⟨D, hD⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (L : ℝ)).exists_bound_of_continuousOn
      hV.continuousOn
  have hgrad (x : EuclideanSpace ℝ (Fin n)) : ‖gradient u x‖ ≤ (L : ℝ) := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      (norm_fderiv_le_of_lipschitz (x₀ := x) ℝ hLip)
  refine ⟨D - u x₀, ?_⟩
  intro x
  have hg : gradient u x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (L : ℝ) := by
    simpa only [mem_closedBall, dist_zero_right] using hgrad x
  have hv : V (gradient u x) ≤ D :=
    (le_abs_self (V (gradient u x))).trans (hD _ hg)
  linarith [hx₀ x]

/-- **First weak Monge–Ampère derivatives at a given potential** (Letwin v1 (2.4)): let `u` be a
normalized convex Lipschitz `C¹` potential with `G`-Lipschitz gradient, `W ∈ C¹`, the right side
`-u + W(∇u)` Lipschitz, the Hessian a.e. positive definite with `log det ∇²u = -u + W(∇u)`, and `T`
a
locally `L²` weak derivative of the Hessian. Then `e^{-u + W(∇u)}` is Lipschitz, the determinant has
the
locally `L²` weak derivative `det ∇²u · tr((∇²u)⁻¹ T_k)`, and the log-determinant has weak
derivative
`tr((∇²u)⁻¹ T_k)`, identified a.e. with both forms of the right-hand side. The potential is given;
no
convexity of `W` or uniform convexity is used. -/
theorem hasWeakDerivAlong_log_det_hessianMatrix_of_weak_tensor {n : ℕ}
    {u W : EuclideanSpace ℝ (Fin n) → ℝ} {L G LF : NNReal}
    {T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ} (hconv : ConvexOn ℝ univ u)
    (hLip : LipschitzWith L u)
    (hnorm : (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1)
    (hC1 : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u)) (hW : ContDiff ℝ 1 W)
    (hF : LipschitzWith LF (fun x => -u x + W (gradient u x)))
    (hdata :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧ Real.log (hessianMatrix u x).det = -u x + W (gradient u x))
    (hT :
      ∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)),
            IsCompact S →
              MemLp (fun x => T x k i j) 2
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    (∃ LE : NNReal, LipschitzWith LE (fun x => Real.exp (-u x + W (gradient u x)))) ∧
      ∀ k : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x).det)
            (fun x =>
              (hessianMatrix u x).det *
                ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          (∀ S : Set (EuclideanSpace ℝ (Fin n)),
              IsCompact S →
                MemLp
                  (fun x =>
                    (hessianMatrix u x).det *
                      ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
                  2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
            HasWeakDerivAlong (fun x => Real.log (hessianMatrix u x).det)
                (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
                (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
              (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
                  ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
                    fderiv ℝ (fun y => -u y + W (gradient u y)) x
                      (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
                (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
                  ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
                    -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
                      ∑ a : Fin n,
                        hessianMatrix u x k a *
                          fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a)) := by
  classical
  obtain ⟨C, hC⟩ := exponent_upper_of_normalized_convex hconv hLip hnorm hW.continuous
  have hmaps : MapsTo (fun x => -u x + W (gradient u x)) univ (Iic C) := by
    intro x _
    exact hC x
  have he :
    LipschitzWith (Real.toNNReal (Real.exp C) * LF)
      (fun x => Real.exp (-u x + W (gradient u x))) :=
    lipschitzOnWith_univ.mp ((lipschitzOnWith_exp_Iic C).comp hF.lipschitzOnWith hmaps)
  refine ⟨⟨_, he⟩, ?_⟩
  intro k
  have hbound (r s : Fin n) :
    MemLp (fun x => hessianMatrix u x r s) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    memLp_top_of_bound (measurable_hessianMatrix_entry u r s).aestronglyMeasurable (G : ℝ)
      (Filter.Eventually.of_forall fun x =>
        norm_hessianMatrix_entry_le_of_lipschitz_gradient hG x r s)
  have hp :=
    hasWeakDerivAlong_det_of_locally_memLp_two (A := fun x => hessianMatrix u x) (DA := fun x =>
      Matrix.of fun i j => T x k i j) (fun i j => (hT k i j).1) hbound (fun i j => (hT k i j).2)
  have hchain :
    (fun x =>
        fderiv ℝ (fun y => Real.exp (-u y + W (gradient u y))) x
          (EuclideanSpace.basisFun (Fin n) ℝ
            k)) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x =>
        Real.exp (-u x + W (gradient u x)) *
          fderiv ℝ (fun y => -u y + W (gradient u y)) x
            (EuclideanSpace.basisFun (Fin n) ℝ k)) := by
    filter_upwards [hF.ae_differentiableAt (μ := volume)] with x hx
    have h :=
      congrArg
        (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L (EuclideanSpace.basisFun (Fin n) ℝ k))
        hx.hasFDerivAt.exp.fderiv
    simpa only [_root_.smul_apply, smul_eq_mul] using h
  have hExpWeak :=
    (hasWeakDerivAlong_of_lipschitz he (EuclideanSpace.basisFun (Fin n) ℝ k)).congr_ae
      Filter.EventuallyEq.rfl hchain
  have hExpDet :
    (fun x =>
        Real.exp (-u x + W (gradient u x))) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => (hessianMatrix u x).det) := by
    filter_upwards [hdata] with x hx
    rw [← hx.2, Real.exp_log hx.1.det_pos]
  have hDetExpWeak := hExpWeak.congr_ae hExpDet Filter.EventuallyEq.rfl
  have hDensity := hp.1.ae_eq hDetExpWeak
  have hAll :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (∑ σ : Equiv.Perm (Fin n),
            ((Equiv.Perm.sign σ : ℤ) : ℝ) *
              ∑ i : Fin n,
                T x k (σ i) i *
                  ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, hessianMatrix u x (σ j) j) =
          (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace ∧
        ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            fderiv ℝ (fun y => -u y + W (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
              ∑ a : Fin n,
                hessianMatrix u x k a *
                  fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a) := by
    filter_upwards [hdata, hDensity, ae_fderiv_mongeAmpere_exponent hC1 hG hW] with x hx hd
      hRight
    have hunit : IsUnit (hessianMatrix u x).det :=
      isUnit_iff_ne_zero.mpr (ne_of_gt hx.1.det_pos)
    have hJ :
      (∑ σ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∑ i : Fin n,
              T x k (σ i) i *
                ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, hessianMatrix u x (σ j) j) =
        (hessianMatrix u x).det *
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace := by
      calc
        (∑ σ : Equiv.Perm (Fin n),
              ((Equiv.Perm.sign σ : ℤ) : ℝ) *
                ∑ i : Fin n,
                  T x k (σ i) i *
                    ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, hessianMatrix u x (σ j) j) =
            fderiv ℝ Matrix.det (hessianMatrix u x) (Matrix.of fun i j => T x k i j) :=
          (fderiv_det_eq_sum_permutation (hessianMatrix u x)
              (Matrix.of fun i j => T x k i j)).symm
        _ =
            (hessianMatrix u x).det *
              ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace :=
          fderiv_det_eq_det_mul_trace _ _ hunit
    have hExpEq : (hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)) := by
      rw [← hx.2, Real.exp_log hx.1.det_pos]
    have hTrace :
      ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
        fderiv ℝ (fun y => -u y + W (gradient u y)) x (EuclideanSpace.basisFun (Fin n) ℝ k) := by
      apply mul_left_cancel₀ (ne_of_gt hx.1.det_pos)
      calc
        (hessianMatrix u x).det *
              ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            (∑ σ : Equiv.Perm (Fin n),
              ((Equiv.Perm.sign σ : ℤ) : ℝ) *
                ∑ i : Fin n,
                  T x k (σ i) i *
                    ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, hessianMatrix u x (σ j) j) :=
          hJ.symm
        _ =
            Real.exp (-u x + W (gradient u x)) *
              fderiv ℝ (fun y => -u y + W (gradient u y)) x
                (EuclideanSpace.basisFun (Fin n) ℝ k) :=
          hd
        _ =
            (hessianMatrix u x).det *
              fderiv ℝ (fun y => -u y + W (gradient u y)) x
                (EuclideanSpace.basisFun (Fin n) ℝ k) := by
          rw [hExpEq]
    exact ⟨hJ, hTrace, hTrace.trans (hRight k)⟩
  have hJac := hAll.mono fun _ hx => hx.1
  have hTrace :
    (fun x =>
        ((hessianMatrix u x)⁻¹ *
            (Matrix.of fun i j =>
              T x k i j)).trace) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x =>
        fderiv ℝ (fun y => -u y + W (gradient u y)) x (EuclideanSpace.basisFun (Fin n) ℝ k)) :=
    hAll.mono fun _ hx => hx.2.1
  have hRight := hAll.mono fun _ hx => hx.2.2
  have hLog :
    (fun x => -u x + W (gradient u x)) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => Real.log (hessianMatrix u x).det) :=
    hdata.mono fun _ hx => hx.2.symm
  have hLogWeak :=
    (hasWeakDerivAlong_of_lipschitz hF (EuclideanSpace.basisFun (Fin n) ℝ k)).congr_ae hLog
      hTrace.symm
  exact
    ⟨hp.1.congr_ae Filter.EventuallyEq.rfl hJac, fun S hS =>
      MemLp.ae_eq (ae_restrict_of_ae hJac) (hp.2 S hS), hLogWeak, hTrace, hRight⟩

include hn hκ hK hKc hKint hW hstrong hμ hiso in
/-- The same actual-source moment potential and weak tensor retain all original
regularity data and satisfy the first weak Monge–Ampère identity (Letwin v1 (2.4)).
The determinant derivative is locally L2; the logarithmic weak derivative is
identified with the explicit source-law right-hand side. No C2 Hessian regularity
or prescribed derivative tensor is assumed. This does not prove the second
evolution identity, the integrated trace bound, or the constant-8 theorem. -/
theorem exists_regular_moment_weak_first_derivative :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
              S)) ∧
      (∃ LE : NNReal,
        LipschitzWith LE (fun x => Real.exp (-u x + W (gradient u x)))) ∧
      ∀ k : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x).det)
          (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        HasWeakDerivAlong (fun x => Real.log (hessianMatrix u x).det)
          (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            fderiv ℝ (fun y => -u y + W (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
              ∑ a : Fin n, hessianMatrix u x k a *
                fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a)) := by
  obtain ⟨u, L, LF, T, hconv, hLip, hnorm, hmap, hC1, hG,
      hF, hw, hdata, hT⟩ :=
    exists_regular_moment_weak_tensor hn hκ hK hKc hKint hW hstrong μ hμ hiso
  obtain ⟨he, hfirst⟩ := hasWeakDerivAlong_log_det_hessianMatrix_of_weak_tensor hconv hLip hnorm
    hC1 hG (hW.of_le (WithTop.coe_le_coe.mpr le_top)) hF (hdata.mono fun _ hx => ⟨hx.1, hx.2.1⟩) hT
  exact ⟨u, L, LF, T, hconv, hLip, hnorm, hmap, hC1, hG, hF, hw, hdata, hT, he, hfirst⟩

end FunctionalInequalities.Analysis

end

end RegularSource
