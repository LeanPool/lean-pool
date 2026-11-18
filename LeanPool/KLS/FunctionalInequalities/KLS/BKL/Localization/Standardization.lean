/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Posterior.Covariance
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.CompactReduction
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Posterior.Standardization
/-!
# Standardized posteriors inherit the compact cumulant bound

BKL arXiv:2610.05474v1, (77): for a compactly supported isotropic log-concave prior and symmetric
positive
semidefinite `Q`, the standardized posterior `(A^{-1/2}(· − a))_* μ_{c,Q}` is compactly supported,
isotropic and
log-concave, so a bound `CumulantBoundCompact d b` transfers to `‖κ_{d+1}(t)(v)‖²_t ≤ b ⟨A v, v⟩`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS

/-- The standardized-posterior transfer only needs the cumulant bound in its own dimension. -/
theorem compactPosterior_cumulant_bound_of_fixed_dimension {n : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support) (hiso : KLS.Isotropic μ)
    (hLC : KLS.LogConcave μ) (c : EuclideanSpace ℝ (Fin n))
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hSym : IsSelfAdjoint Q)
    (hQ : ∀ x, 0 ≤ ⟪Q x, x⟫) {d : ℕ} (hd : 1 ≤ d) {b : ℝ}
    (h :
      ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
        KLS.LogConcave ν →
          KLS.Isotropic ν →
            IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support →
              ∀ u : EuclideanSpace ℝ (Fin n),
                ∑ J : Fin d → Fin n,
                    cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
                        (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^
                      2 ≤
                  b * ‖u‖ ^ 2)
    (v : EuclideanSpace ℝ (Fin n)) :
    ∑ J : Fin d → Fin n,
        cumulant (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
            (Fin.cons v fun k =>
              inverseSqrt
                (Covariance.operator
                  (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))))
                (EuclideanSpace.basisFun (Fin n) ℝ (J k))) ^
          2 ≤
      b *
        ⟪Covariance.operator (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))) v,
          v⟫ := by
  let π : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) := compactPosterior μ hc c Q
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    Covariance.operator (π : Measure (EuclideanSpace ℝ (Fin n)))
  let σ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := inverseSqrt A
  let a : EuclideanSpace ℝ (Fin n) := posteriorMean μ c Q
  let η : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) := Probability.translateLaw π (-a)
  obtain ⟨W, hW, hνiso⟩ :=
    Isotropic.exists_inverseSqrt_equiv_isotropic_standardized μ hc hiso c Q
  let ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) :=
    Probability.mapContinuousLinearEquiv η W
  have hW' : (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = σ := by
    simpa [π, A, σ] using hW
  have hpos : A.IsPositive := by
    simpa [π, A] using Isotropic.compactPosterior_covariance_isPositive μ hc hiso c Q
  have hunit : IsUnit A := by
    simpa [π, A] using Isotropic.compactPosterior_covariance_isUnit μ hc hiso c Q
  have hself : ContinuousLinearMap.adjoint σ = σ := by
    change ContinuousLinearMap.adjoint (inverseSqrt A) = inverseSqrt A
    exact (inverseSqrt_spec A hpos hunit).2.1
  have halg : (σ.comp A).comp σ = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    change σ (A (σ x)) = x
    simpa [σ] using
      congrArg (fun T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => T x)
        (inverseSqrt_mul_mul_inverseSqrt A hpos hunit)
  have hνcoe :
    (ν : Measure (EuclideanSpace ℝ (Fin n))) =
      Measure.map (fun x => W (x - a)) (π : Measure (EuclideanSpace ℝ (Fin n))) := by
    change
      (Probability.mapContinuousLinearEquiv η W : Measure (EuclideanSpace ℝ (Fin n))) =
        Measure.map (fun x => W (x - a)) (π : Measure (EuclideanSpace ℝ (Fin n)))
    rw [Probability.coe_mapContinuousLinearEquiv, Probability.coe_translateLaw,
      Measure.map_map W.continuous.measurable (measurable_const_add _)]
    congr 1
    funext x
    simp [sub_eq_add_neg, add_comm]
  have hπLC : KLS.LogConcave π := by
    simpa [π] using compactPosterior_logConcave μ hc hLC c Q hSym hQ
  have hηLC : KLS.LogConcave η := by simpa [η] using hπLC.translateLaw (-a)
  have hmapback :
    Measure.map (W.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (ν : Measure (EuclideanSpace ℝ (Fin n))) =
      (η : Measure (EuclideanSpace ℝ (Fin n))) :=
    (Probability.measurePreserving_mapContinuousLinearEquiv_symm η W).map_eq
  have hνLC : KLS.LogConcave ν := LogConcave.of_continuousLinearEquiv_map hηLC ν W.symm hmapback
  have hπcompact : IsCompact (π : Measure (EuclideanSpace ℝ (Fin n))).support := by
    change IsCompact (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))).support
    rw [compactPosterior_support μ hc c Q]
    exact hc
  let K : Set (EuclideanSpace ℝ (Fin n)) :=
    (fun x => W (x - a)) '' (π : Measure (EuclideanSpace ℝ (Fin n))).support
  have hKcompact : IsCompact K := by
    apply hπcompact.image
    exact W.continuous.comp (continuous_id.sub continuous_const)
  have hKae : K ∈ ae (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [hνcoe]
    apply
      (ae_map_iff (W.continuous.comp (continuous_id.sub continuous_const)).aemeasurable
          hKcompact.measurableSet).2
    filter_upwards [Measure.support_mem_ae (μ := (π : Measure (EuclideanSpace ℝ (Fin n))))] with
      x hx
    exact ⟨x, hx, rfl⟩
  have hνcompact : IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support := by
    apply IsCompact.of_isClosed_subset hKcompact
    · exact Measure.isClosed_support
    · exact Measure.support_subset_of_isClosed hKcompact.isClosed hKae
  have hexp (r : ℝ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (r * ‖x‖))
      (π : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply integrable_exp_of_compact π hπcompact
    fun_prop
  have hk : 2 ≤ d + 1 := by omega
  have hcum (J : Fin d → Fin n) :
    cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
        (Fin.cons (W.symm v) fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) =
      cumulant (π : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
        (Fin.cons v fun k => σ (EuclideanSpace.basisFun (Fin n) ℝ (J k))) := by
    rw [hνcoe, cumulant_map_affine W a (π : Measure (EuclideanSpace ℝ (Fin n))) hexp hk]
    have hWadj :
      ContinuousLinearMap.adjoint
          (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) =
        σ := by
      rw [hW', hself]
    congr 1
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [Fin.cons_zero, hWadj]
      rw [← hW']
      exact W.apply_symm_apply v
    · simp only [Fin.cons_succ, hWadj]
  have hsum :
    ∑ J : Fin d → Fin n,
        cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
            (Fin.cons (W.symm v) fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^
          2 =
      ∑ J : Fin d → Fin n,
        cumulant (π : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
            (Fin.cons v fun k => σ (EuclideanSpace.basisFun (Fin n) ℝ (J k))) ^
          2 := by
    apply Finset.sum_congr rfl
    intro J hJ
    rw [hcum]
  have hnorm : ‖W.symm v‖ ^ 2 = ⟪A v, v⟫ := by
    let u := W.symm v
    have hv : v = σ u := by
      dsimp [u]
      rw [← hW']
      exact (W.apply_symm_apply v).symm
    have hu : σ (A (σ u)) = u := by
      simpa [ContinuousLinearMap.comp_apply] using
        congrArg (fun T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => T u) halg
    calc
      ‖u‖ ^ 2 = ⟪u, u⟫ := (real_inner_self_eq_norm_sq u).symm
      _ = ⟪σ (A (σ u)), u⟫ := by rw [hu]
      _ = ⟪A (σ u), (ContinuousLinearMap.adjoint σ) u⟫ :=
        (ContinuousLinearMap.adjoint_inner_right σ (A (σ u)) u).symm
      _ = ⟪A (σ u), σ u⟫ := by rw [hself]
      _ = ⟪A v, v⟫ := by rw [← hv]
  have hbound := h ν hνLC hνiso hνcompact (W.symm v)
  calc
    ∑ J : Fin d → Fin n,
          cumulant (π : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
              (Fin.cons v fun k => σ (EuclideanSpace.basisFun (Fin n) ℝ (J k))) ^
            2 =
        ∑ J : Fin d → Fin n,
          cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
              (Fin.cons (W.symm v) fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^
            2 :=
      hsum.symm
    _ ≤ b * ‖W.symm v‖ ^ 2 := hbound
    _ = b * ⟪A v, v⟫ := by rw [hnorm]
    _ =
        b *
          ⟪Covariance.operator (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n)))
              v,
            v⟫ := by
      rfl


/--
**Standardized posterior cumulant bound** (BKL arXiv:2610.05474v1, (77)): for a compactly supported
isotropic log-concave prior and a posterior with symmetric positive semidefinite `Q`, a cumulant
bound
`CumulantBoundCompact d b` (`d ≥ 1`) applied to the standardized posterior
`ν = (A^{-1/2}(· − a))_* μ_{c,Q}` gives, with `σ = A^{-1/2}`,
`Σ_J κ_{d+1}(μ_{c,Q})(v, σ e_{J_1}, …, σ e_{J_d})² ≤ b ⟪A v, v⟫`, i.e. `‖κ_{d+1}(t)(v)‖²_t ≤ b ⟨A_t
v, v⟩`. -/
theorem compactPosterior_cumulant_bound {n : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support) (hiso : KLS.Isotropic μ)
    (hLC : KLS.LogConcave μ) (c : EuclideanSpace ℝ (Fin n))
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hSym : IsSelfAdjoint Q)
    (hQ : ∀ x, 0 ≤ ⟪Q x, x⟫) {d : ℕ} (hd : 1 ≤ d) {b : ℝ}
    (h : LogConcave.Suspension.CumulantBoundCompact d b) (v : EuclideanSpace ℝ (Fin n)) :
    ∑ J : Fin d → Fin n,
        cumulant (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
            (Fin.cons v fun k =>
              inverseSqrt
                (Covariance.operator
                  (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))))
                (EuclideanSpace.basisFun (Fin n) ℝ (J k))) ^
          2 ≤
      b *
        ⟪Covariance.operator (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))) v,
          v⟫ := by
  exact
    compactPosterior_cumulant_bound_of_fixed_dimension μ hc hiso hLC c Q hSym hQ hd
      (fun ν hνLC hνiso hνcompact u => h n ν hνiso hνLC hνcompact u) v
end FunctionalInequalities.KLS
