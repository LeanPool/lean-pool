/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.ExponentialMoments.Norm
public import LeanPool.KLS.FunctionalInequalities.Probability.Stein.DualBound
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.AbsoluteContinuity
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Isotropic
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Moments

/-!
# Stein kernels of log-concave laws: Letwin A.7 and Lemma 2.9

Letwin, arXiv:2607.24164v1, Appendix A.7 and Lemma 2.9, for a centered log-concave law `μ` on `ℝⁿ`
of full affine dimension (hence `μ ≪ volume` with finite second moment): the Stein identity extends
to all locally Lipschitz `f` with `f, ∇f ∈ L²(μ)`, and the `H^{-1}(μ)` norm of `⟪·, v⟫` is bounded
by `∫ ‖τ(x) v‖² dμ`. No isotropy, regularity or Stein-kernel construction is assumed or provided.
This
module neither uses nor constructs the moment-map kernel of the paper: smooth moment potentials
(Lemma 2.2) are produced in `KLS/Letwin/MomentMap.lean`, the `C²` form of the `H^{-1}` variance
inequality (Proposition 2.8) is in `KLS/LogConcave/HminusOne.lean`, and Theorem 1.2 is in
`KLS/Letwin/QuadraticBound.lean`.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave

/--
A log-concave law of full affine dimension is absolutely continuous with finite second moment. -/
theorem absolutelyContinuous_and_memLp_two_of_affineSupport_eq_top {n : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hLC : KLS.LogConcave μ)
    (hfull : Probability.affineSupport μ = ⊤) :
    (μ : Measure (EuclideanSpace ℝ (Fin n))) ≪ volume ∧
      MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2
        (μ : Measure (EuclideanSpace ℝ (Fin n))) := by
  refine
    ⟨hLC.absolutelyContinuous_of_interior_support_nonempty volume
        (hLC.interior_support_nonempty_of_affineSupport_eq_top hfull),
      ?_⟩
  obtain ⟨r, hr, hexp, _⟩ := hLC.exists_integrable_exp_norm_contDiffOn_logLaplace
  apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).mpr
  exact Probability.integrable_norm_pow_of_exp _ hr hexp 2

/--
**Letwin A.7** for a full-dimensional log-concave law: the Stein identity and its Cauchy–Schwarz
bound hold for every locally Lipschitz `f` with `f, ∇f ∈ L²(μ)`. -/
theorem stein_identity_of_affineSupport_eq_top {n : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (τ : EuclideanSpace ℝ (Fin n) → Probability.Stein.KernelMatrix n)
    (hK : Probability.Stein.IsSteinKernel μ τ) (hLC : KLS.LogConcave μ)
    (hfull : Probability.affineSupport μ = ⊤) (hSym : Probability.Stein.SymmetricAE μ τ)
    (hHS :
      MemLp (fun x => Probability.Stein.hsNorm (τ x)) 2
        (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LocallyLipschitz f)
    (hf2 : MemLp f 2 (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hgrad : MemLp (gradient f) 2 (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (v : EuclideanSpace ℝ (Fin n)) :
    (∫ x, ⟪x, v⟫ * f x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) =
        (∫ x,
          ⟪Probability.Stein.action (τ x) v,
            gradient f x⟫ ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      |∫ x, ⟪x, v⟫ * f x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))| ≤
        Real.sqrt
            (∫ x,
              ‖Probability.Stein.action (τ x) v‖ ^
                2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) *
          Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) := by
  obtain ⟨hac, hμ2⟩ := absolutelyContinuous_and_memLp_two_of_affineSupport_eq_top μ hLC hfull
  exact
    ⟨Probability.Stein.extended_identity_of_ac μ τ hK hac hμ2 hSym hHS f hf hf2 hgrad v,
      Probability.Stein.extended_abs_bound_of_ac μ τ hK hac hμ2 hSym hHS f hf hf2 hgrad v⟩

/-- A.7 with the hypothesis written as `∫ |τ|_HS² dμ < ∞`. -/
theorem stein_identity_of_affineSupport_eq_top' {n : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (τ : EuclideanSpace ℝ (Fin n) → Probability.Stein.KernelMatrix n)
    (hK : Probability.Stein.IsSteinKernel μ τ) (hLC : KLS.LogConcave μ)
    (hfull : Probability.affineSupport μ = ⊤) (hSym : Probability.Stein.SymmetricAE μ τ)
    (hHS :
      Integrable (fun x => Probability.Stein.hsNorm (τ x) ^ 2)
        (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LocallyLipschitz f)
    (hf2 : MemLp f 2 (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hgrad : MemLp (gradient f) 2 (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (v : EuclideanSpace ℝ (Fin n)) :
    (∫ x, ⟪x, v⟫ * f x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) =
        (∫ x,
          ⟪Probability.Stein.action (τ x) v,
            gradient f x⟫ ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      |∫ x, ⟪x, v⟫ * f x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))| ≤
        Real.sqrt
            (∫ x,
              ‖Probability.Stein.action (τ x) v‖ ^
                2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) *
          Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) := by
  exact
    stein_identity_of_affineSupport_eq_top μ τ hK hLC hfull hSym
      ((Probability.Stein.memLp_hsNorm_iff_integrable_sq hK.measurable_entries).mpr hHS) f hf
      hf2 hgrad v

/--
**Letwin Lemma 2.9**: for a full-dimensional log-concave law with an a.e. symmetric Stein kernel
`τ`, `|τ|_HS ∈ L²`, the linear function `⟪·, v⟫` is centered with finite `H^{-1}` norm and
`‖⟪·, v⟫‖²_{H^{-1}} ≤ ∫ ‖τ(x) v‖² dμ`. -/
theorem dualNorm_linear_sq_le_of_affineSupport_eq_top {n : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (τ : EuclideanSpace ℝ (Fin n) → Probability.Stein.KernelMatrix n)
    (hK : Probability.Stein.IsSteinKernel μ τ) (hLC : KLS.LogConcave μ)
    (hfull : Probability.affineSupport μ = ⊤) (hSym : Probability.Stein.SymmetricAE μ τ)
    (hHS :
      MemLp (fun x => Probability.Stein.hsNorm (τ x)) 2
        (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (v : EuclideanSpace ℝ (Fin n)) :
    let hμ2 := (absolutelyContinuous_and_memLp_two_of_affineSupport_eq_top μ hLC hfull).2
    let q := Probability.Stein.linearLp μ hμ2 v
    (∫ x, q x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) = 0 ∧
      Energy.Dual.dualNorm μ q ≠ ⊤ ∧
        (Energy.Dual.dualNorm μ q).toReal = sSup (Energy.Dual.signedPairings μ q) ∧
          (Energy.Dual.dualNorm μ q).toReal ^ 2 ≤
            ∫ x,
              ‖Probability.Stein.action (τ x) v‖ ^
                2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) := by
  dsimp only
  exact
    Probability.Stein.linear_dual_bound_of_ac μ τ hK
      (absolutelyContinuous_and_memLp_two_of_affineSupport_eq_top μ hLC hfull).1
      (absolutelyContinuous_and_memLp_two_of_affineSupport_eq_top μ hLC hfull).2 hSym hHS v

/-- Lemma 2.9 with the hypothesis written as `∫ |τ|_HS² dμ < ∞`. -/
theorem dualNorm_linear_sq_le_of_affineSupport_eq_top' {n : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (τ : EuclideanSpace ℝ (Fin n) → Probability.Stein.KernelMatrix n)
    (hK : Probability.Stein.IsSteinKernel μ τ) (hLC : KLS.LogConcave μ)
    (hfull : Probability.affineSupport μ = ⊤) (hSym : Probability.Stein.SymmetricAE μ τ)
    (hHS :
      Integrable (fun x => Probability.Stein.hsNorm (τ x) ^ 2)
        (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (v : EuclideanSpace ℝ (Fin n)) :
    let hμ2 := (absolutelyContinuous_and_memLp_two_of_affineSupport_eq_top μ hLC hfull).2
    let q := Probability.Stein.linearLp μ hμ2 v
    (∫ x, q x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) = 0 ∧
      Energy.Dual.dualNorm μ q ≠ ⊤ ∧
        (Energy.Dual.dualNorm μ q).toReal = sSup (Energy.Dual.signedPairings μ q) ∧
          (Energy.Dual.dualNorm μ q).toReal ^ 2 ≤
            ∫ x,
              ‖Probability.Stein.action (τ x) v‖ ^
                2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) := by
  exact
    dualNorm_linear_sq_le_of_affineSupport_eq_top μ τ hK hLC hfull hSym
      ((Probability.Stein.memLp_hsNorm_iff_integrable_sq hK.measurable_entries).mpr hHS) v

end FunctionalInequalities.KLS.LogConcave
