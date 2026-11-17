/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Moments
public import LeanPool.KLS.FunctionalInequalities.Probability.Gaussian.Moments
public import LeanPool.KLS.FunctionalInequalities.Analysis.Operator.HilbertSchmidt
public import LeanPool.KLS.FunctionalInequalities.KLS.CEK.MomentRegularity.TraceStein
public import LeanPool.KLS.FunctionalInequalities.KLS.IsotropicSupport
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.QuadraticVariance
public import LeanPool.KLS.FunctionalInequalities.Probability.Stein.QuadraticAction
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Calculus
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.Sign
public import LeanPool.KLS.FunctionalInequalities.Analysis.Operator.Coordinates
public import LeanPool.KLS.FunctionalInequalities.Probability.Stein.Kernel
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Coordinates
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Weak
public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Basic
public import LeanPool.KLS.FunctionalInequalities.Probability.LogConcave
public import LeanPool.KLS.FunctionalInequalities.KLS.Isotropic
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.Tilted
public import LeanPool.KLS.FunctionalInequalities.Probability.Support.Affine
public import LeanPool.KLS.FunctionalInequalities.Probability.Variance.Quadratic
public import LeanPool.KLS.FunctionalInequalities.Probability.Transport

/-!
# Letwin's constant 8 for the regular class

Letwin (arXiv:2607.24164v1), Theorem 1.2, proof assembly for the actual regular class: an isotropic
law `1_K e^{-W} dx` with `K`
compact convex with nonempty interior and `W` smooth and `κ`-uniformly convex, `n > 0`.
- `regularClass_matrix_variance_le_eight`: for every symmetric `M`, `Var (Σᵢⱼ Mᵢⱼ xᵢ xⱼ) ≤ 8 tr
  (M²)`. The proof chooses one regular
  moment witness through `exists_regular_moment_hessian_trace_bound` (the flat view of
  `exists_regular_moment_weak_stein_coupling`)
  and uses its trace bound, the Gaussian product `H⁻¹` route, the spectral noise energy, the noise
  limit and the singular extension.
- `letwinQuadraticBound_of_matrix_variance_bound`: the matrix form of the bound for a measure gives
  `LetwinQuadraticBound`.
- `regularClass_letwinQuadraticBound`: `LetwinQuadraticBound` for every regular-class law.

Exact original hypotheses; no desired-bound, `C²`, global-inverse or kernel premise. This is the
compact regular-class counterpart; the
paper's general theorem is not stated here.
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
open MeasureTheory Set Filter ProbabilityTheory
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein
open FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open scoped ContDiff RealInnerProductSpace Topology MatrixOrder

namespace FunctionalInequalities.KLS.LogConcave

include hn hκ hK hKc hKint hW hstrong hμ hiso in
theorem regularClass_matrix_variance_le_eight :
    ∀ M : Matrix (Fin n) (Fin n) ℝ,
      M.IsSymm →
        variance (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, ∑ j, M i j * x i * x j)
            (μ : Measure _) ≤
          8 * Matrix.trace (M * M) := by
  obtain ⟨u, L, _hconv, hl, hnrm, hm, hC1, hG, hdata, hmean, hT25⟩ :=
    Analysis.exists_regular_moment_hessian_trace_bound hn hκ hK hKc hKint hW hstrong μ hμ hiso
  let E := EuclideanSpace ℝ (Fin n)
  let ρ : Measure E := volume.tilted (-u)
  have hexp : Integrable (fun y : E => Real.exp (-u y)) volume :=
    Integrable.of_integral_ne_zero (by rw [hnrm]; norm_num)
  let : IsProbabilityMeasure ρ := isProbabilityMeasure_tilted hexp
  have hgnorm (x : E) : ‖gradient u x‖ ≤ (L : ℝ) := by
    calc
      _ = ‖fderiv ℝ u x‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map _
      _ ≤ _ := norm_fderiv_le_of_lipschitz ℝ hl
  have hu4 : MemLp (gradient u) 4 ρ :=
    MemLp.of_bound (continuous_gradient hC1).aestronglyMeasurable (L : ℝ) (ae_of_all _ hgnorm)
  have hLC : KLS.LogConcave μ :=
    KLS.LogConcave.logConcave_of_eq_regularClass μ hK.isClosed hKc hW.continuous hκ hstrong hμ
  have hfull : Probability.affineSupport μ = ⊤ := hiso.affineSupport_eq_top
  have hSmooth (e : E ≃L[ℝ] E) (Q : E →L[ℝ] E) (hQ : IsSelfAdjoint Q) (s : ℝ) (hs : 0 < s) :=
    gaussian_smoothed_quadratic_variance_le_latent_energy μ hLC hfull hC1 hl hG hnrm hm e Q hQ
      hs
  have hμ4 : MemLp id 4 (μ : Measure E) := by
    rw [← hm]
    exact
      (memLp_map_measure_iff continuous_id.aestronglyMeasurable
            (continuous_gradient hC1).measurable.aemeasurable).2
        hu4
  apply Probability.symmetric_matrix_variance_bound_of_isUnit μ hμ4 8
  intro M hM hunit
  let B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt (M * M)
  let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt B
  let Q : Matrix (Fin n) (Fin n) ℝ := cfc (fun x : ℝ => (SignType.sign x : ℝ)) M
  obtain ⟨_, hSp, _, _, _, hSQS, _, _, hQL, e, he, hSelf⟩ :=
    Analysis.symmetric_matrix_spectral_geometry M hM hunit
  have hS : S.IsSymm := Matrix.isHermitian_iff_isSymm.mp hSp.isHermitian
  let QL : E →L[ℝ] E := (Matrix.toEuclideanLin Q).toContinuousLinearMap
  let μe := Probability.mapContinuousLinearEquiv μ e
  have hμe4 : MemLp id 4 (μe : Measure E) :=
    Probability.memLp_four_map_linear (μ : Measure E) e.toContinuousLinearMap hμ4
  have hvarmap :
    variance (fun x : E => ⟪QL x, x⟫) (μe : Measure E) =
      variance (fun x : E => ∑ i, ∑ j, M i j * x i * x j) (μ : Measure E) := by
    change variance (fun x => ⟪action Q x, x⟫) ((μ : Measure E).map e.toContinuousLinearMap) = _
    rw [he, variance_quadratic_map_sandwich _ S Q hS, hSQS]
    exact variance_congr (ae_of_all _ fun x => (quadratic_matrix_sum_eq_inner_action M x).symm)
  apply
    le_of_forall_inverse_noise_quadratic_error
      (variance (fun x : E => ∑ i, ∑ j, M i j * x i * x j) (μ : Measure E))
      (8 * Matrix.trace (M * M)) (8 * Matrix.trace B) (4 * (n : ℝ))
  intro s hs
  let γ : Measure E := Probability.Gaussian.law s
  let : IsProbabilityMeasure γ := Probability.Gaussian.law_probability hs
  let P := ρ.prod γ
  have hHsym : ∀ᵐ y ∂ρ, (hessianMatrix u y).IsSymm := by
    filter_upwards [(tilted_absolutelyContinuous (volume : Measure E) (-u)).ae_le hdata] with y
      hy
    exact Matrix.isHermitian_iff_isSymm.mp hy.1.isHermitian
  have hEn :=
    sum_integral_spectral_noise_energy_le ρ γ (hessianMatrix u)
      (fun i j => measurable_hessianMatrix_entry u i j) hHsym (fun i j => (hmean i j).1)
      (fun i j => (hmean i j).2) hT25 M hM hunit ((2 * s)⁻¹)
  have hEnergy :
    (∑ i : Fin n,
        ∫ p : E × E,
          ‖e
                  (action (hessianMatrix u p.1)
                    (e.toContinuousLinearMap.adjoint (QL (EuclideanSpace.single i 1)))) +
                (2 * s)⁻¹ • QL (EuclideanSpace.single i 1)‖ ^
            2 ∂P) ≤
      2 * Matrix.trace (M * M) + 2 * (2 * s)⁻¹ * Matrix.trace B + (n : ℝ) * ((2 * s)⁻¹) ^ 2 := by
    calc
      _ =
          ∑ i : Fin n,
            ∫ p : E × E,
              ‖action (S * hessianMatrix u p.1 * S + (2 * s)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ))
                    (action Q (EuclideanSpace.single i 1))‖ ^
                2 ∂P := by
        apply Finset.sum_congr rfl
        intro i _
        apply integral_congr_ae
        exact
          ae_of_all _ fun p =>
            congrArg (fun v : E => ‖v‖ ^ 2)
              (latent_field_eq_action_conjugation S (hessianMatrix u p.1) e he hSelf ((2 * s)⁻¹)
                (action Q (EuclideanSpace.single i 1)))
      _ ≤ _ := hEn.2
  have hSM := hSmooth e QL hQL s hs
  calc
    _ = variance (fun x : E => ⟪QL x, x⟫) (μe : Measure E) := hvarmap.symm
    _ ≤ variance (fun x : E => ⟪QL x, x⟫) (smoothedLaw (μe : Measure E) s) :=
      variance_quadratic_le_smoothedLaw μe hμe4 QL hs
    _ ≤
        4 *
          ∑ i : Fin n,
            ∫ p : E × E,
              ‖e
                      (action (hessianMatrix u p.1)
                        (e.toContinuousLinearMap.adjoint (QL (EuclideanSpace.single i 1)))) +
                    (2 * s)⁻¹ • QL (EuclideanSpace.single i 1)‖ ^
                2 ∂P :=
      hSM
    _ ≤
        4 *
          (2 * Matrix.trace (M * M) + 2 * (2 * s)⁻¹ * Matrix.trace B +
            (n : ℝ) * ((2 * s)⁻¹) ^ 2) :=
      mul_le_mul_of_nonneg_left hEnergy (by norm_num)
    _ = _ := by ring

end FunctionalInequalities.KLS.LogConcave

end

section
open MeasureTheory ProbabilityTheory
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave

theorem letwinQuadraticBound_of_matrix_variance_bound {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (h :
      ∀ M : Matrix (Fin n) (Fin n) ℝ,
        M.IsSymm →
          variance (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, ∑ j, M i j * x i * x j) μ ≤
            8 * Matrix.trace (M * M)) :
    LetwinQuadraticBound μ := by
  let E := EuclideanSpace ℝ (Fin n)
  intro A hA
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let M : Matrix (Fin n) (Fin n) ℝ := Analysis.operatorMatrix b A
  have hMA : (Matrix.toEuclideanLin M).toContinuousLinearMap = A :=
    Analysis.operatorOfMatrix_operatorMatrix b A
  have hSym : (Matrix.toEuclideanLin M).IsSymmetric := by
    change ((Matrix.toEuclideanLin M).toContinuousLinearMap : E →ₗ[ℝ] E).IsSymmetric
    rw [hMA]
    exact hA.isSymmetric
  have hM : M.IsSymm :=
    Matrix.isHermitian_iff_isSymm.mp (Matrix.isSymmetric_toEuclideanLin_iff.mp hSym)
  have hcoord (x : E) : (∑ i, ∑ j, M i j * x i * x j) = ⟪A x, x⟫ := by
    rw [quadratic_matrix_sum_eq_inner_action]
    change ⟪(Matrix.toEuclideanLin M).toContinuousLinearMap x, x⟫ = _
    rw [hMA]
  have hv : variance (fun x : E => ⟪A x, x⟫) μ ≤ 8 * Matrix.trace (M * M) := by
    simpa only [hcoord] using h M hM
  have htrace : LinearMap.trace ℝ E (A.toLinearMap * A.toLinearMap) = Matrix.trace (M * M) := by
    rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis, LinearMap.toMatrix_mul]
    rfl
  have hHS :
    (∑ i, ∑ j, ⟪A (stdOrthonormalBasis ℝ E i), stdOrthonormalBasis ℝ E j⟫ ^ 2) =
      Matrix.trace (M * M) :=
    (Analysis.sum_inner_apply_sq_eq_trace_comp_of_isSymmetric A hA.isSymmetric
          (stdOrthonormalBasis ℝ E)).trans
      htrace
  calc
    _ = variance (fun x : E => ⟪A x, x⟫) μ :=
      (variance_eq_integral (A.continuous.inner continuous_id).measurable.aemeasurable).symm
    _ ≤ 8 * Matrix.trace (M * M) := hv
    _ = _ := by rw [hHS]

end FunctionalInequalities.KLS.LogConcave

end

section
open MeasureTheory Set
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave

include hn hκ hK hKc hKint hW hstrong hμ hiso in
theorem regularClass_letwinQuadraticBound :
    LetwinQuadraticBound (μ : Measure (EuclideanSpace ℝ (Fin n))) := by
  apply letwinQuadraticBound_of_matrix_variance_bound
  exact regularClass_matrix_variance_le_eight hn hκ hK hKc hKint hW hstrong μ hμ hiso

end FunctionalInequalities.KLS.LogConcave

end

end RegularSource
