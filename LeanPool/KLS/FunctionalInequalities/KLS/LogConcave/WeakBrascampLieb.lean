/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.BrascampLieb
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakLaplacian
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Bochner.Lipschitz
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Coordinates
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Weak
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.Positivity

/-!
# Weak finite-energy scalar Brascamp–Lieb at C^{1,1}

Letwin arXiv:2607.24164v1 Lemma A.6 for a normalized C1 globally Lipschitz potential with Lipschitz
gradient and
a.e. positive definite coordinate Hessian, for globally bounded weak tests with finite
inverse-Hessian energy. Weak
sibling of `KLS/LogConcave/BrascampLieb.lean`, reusing its Hilbert-closure helpers; the
finite-coordinate Hessian
identification uses `Probability/Stein/HessianKernel`.
-/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology Set InnerProductSpace Matrix
open FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein
open FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open scoped ContDiff RealInnerProductSpace
namespace FunctionalInequalities.KLS.LogConcave

private theorem hessian_pairing_eq_coordinate_quadratic {n : ℕ}
    {U : EuclideanSpace ℝ (Fin n) → ℝ} (hU : ContDiff ℝ 1 U)
    {x : EuclideanSpace ℝ (Fin n)} (hx : DifferentiableAt ℝ (gradient U) x)
    (v : EuclideanSpace ℝ (Fin n)) :
    ⟪fderiv ℝ (gradient U) x v, v⟫ =
      (fun i => v i) ⬝ᵥ (hessianMatrix U x *ᵥ (fun i => v i)) := by
  have he := congrArg (fun A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n) => A v)
    (hessianMatrix_toEuclideanLin_of_differentiableAt_gradient hU hx)
  change Matrix.toEuclideanLin (hessianMatrix U x) v = fderiv ℝ (gradient U) x v at he
  rw [← he, EuclideanSpace.inner_eq_star_dotProduct]
  change (fun i => v i) ⬝ᵥ star (hessianMatrix U x *ᵥ (fun i => v i)) = _
  simp only [star_trivial]

/--
Weak compact variational estimate: the C1,1 sibling of `compact_variational_estimate` for a globally
bounded
locally integrable weak test with compact-local L2 coordinate derivatives and finite inverse-Hessian
energy. -/
theorem compact_weak_variational_estimate {n : ℕ}
    {nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
    {U eta v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hnuU :
      (nu : Measure (EuclideanSpace ℝ (Fin n))) =
        (volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U))
    (hU : ContDiff ℝ 1 U) {G : NNReal} (hG : LipschitzWith G (gradient U)) {L : NNReal}
    (hL : LipschitzWith L U)
    (hnorm : (∫ x, Real.exp (-U x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1)
    (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (hessianMatrix U x).PosDef)
    (a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (C : ℝ)
    (heta : LocallyIntegrable eta (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖eta x‖ ≤ C)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong eta (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 :
      ∀ i : Fin n,
        ∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (henergy :
      Integrable (fun x => (fun i => a i x) ⬝ᵥ ((hessianMatrix U x)⁻¹ *ᵥ (fun i => a i x)))
        (nu : Measure (EuclideanSpace ℝ (Fin n))))
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    Integrable (fun x => eta x * (-weightedLaplacian U v x))
        (nu : Measure (EuclideanSpace ℝ (Fin n))) ∧
      Integrable (fun x => weightedLaplacian U v x ^ 2)
          (nu : Measure (EuclideanSpace ℝ (Fin n))) ∧
        2 *
              (∫ x,
                eta x * (-weightedLaplacian U v x) ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))) -
            (∫ x, weightedLaplacian U v x ^ 2 ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))) ≤
          ∫ x,
            (fun i => a i x) ⬝ᵥ
              ((hessianMatrix U x)⁻¹ *ᵥ
                (fun i => a i x)) ∂(nu : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  let dv := fun x i => fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i)
  obtain ⟨hpair0, hgrad, hpair⟩ :=
    integral_bounded_weak_mul_weightedLaplacian_of_contDiff_one hU hv hvc hnorm a C heta hbound
      hweak ha2
  rw [← hnuU] at hpair0 hgrad hpair
  have hpairInt :
    Integrable (fun x => eta x * (-weightedLaplacian U v x))
      (nu : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply hpair0.neg.congr
    exact Filter.Eventually.of_forall fun x => by simp only [Pi.neg_apply, mul_neg]
  have hpair' :
    (∫ x, eta x * (-weightedLaplacian U v x) ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ x, (fun i => a i x) ⬝ᵥ dv x ∂(nu : Measure (EuclideanSpace ℝ (Fin n))) := by
    simp only [mul_neg, integral_neg]
    change
      -(∫ x, eta x * weightedLaplacian U v x ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))) = _
    rw [hpair, neg_neg]
    rfl
  have hexp : Integrable (fun x => Real.exp (-U x)) volume :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  obtain ⟨hQ, hLap, hcoer⟩ :=
    compact_ordinary_diffusion_coercivity_of_lipschitz_gradient hU hG hL hexp hv hvc
  rw [← hnuU] at hQ hLap hcoer
  have hac :
    (nu : Measure (EuclideanSpace ℝ (Fin n))) ≪ (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [hnuU]
    exact tilted_absolutelyContinuous _ _
  have hEqual :
    (fun x =>
        ⟪fderiv ℝ (gradient U) x (gradient v x),
          gradient v x⟫) =ᵐ[(nu : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => dv x ⬝ᵥ (hessianMatrix U x *ᵥ dv x)) := by
    filter_upwards [hac.ae_le (hG.ae_differentiableAt (μ := volume))] with x hx
    have hdv : dv x = (fun i => gradient v x i) := by
      funext i
      dsimp only [dv]
      rw [← inner_gradient_left, EuclideanSpace.inner_basisFun_real]
    rw [hdv]
    exact hessian_pairing_eq_coordinate_quadratic hU hx (gradient v x)
  have hH := hQ.congr hEqual
  rw [integral_congr_ae hEqual] at hcoer
  have hyoung :=
    integral_mono_ae (hgrad.const_mul 2) (henergy.add hH)
      (by
        filter_upwards [hac.ae_le hPD] with x hx
        exact inverse_quadratic_young (hessianMatrix U x) hx (fun i => a i x) (dv x))
  simp only [Pi.add_apply] at hyoung
  rw [integral_const_mul, integral_add henergy hH] at hyoung
  refine ⟨hpairInt, hLap, ?_⟩
  rw [hpair']
  dsimp only [dv, dotProduct] at hyoung hcoer ⊢
  linarith only [hyoung, hcoer]

/--
Weak finite-energy scalar Brascamp–Lieb inequality (Letwin arXiv:2607.24164v1 Lemma A.6 at C^{1,1}):
for a
log-concave probability `ν = e^{-U} dx` with `U` C1, globally Lipschitz, with Lipschitz gradient and
a.e. positive
definite coordinate Hessian, and a globally bounded weak test `η` with integrable inverse-Hessian
energy,
`Var_ν η ≤ ∫ ⟪a, (∇²U)⁻¹ a⟫ dν`. -/
theorem scalar_brascamp_lieb_weak_finite_energy {n : ℕ}
    {nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hnu : KLS.LogConcave nu)
    {U eta : EuclideanSpace ℝ (Fin n) → ℝ}
    (hnuU :
      (nu : Measure (EuclideanSpace ℝ (Fin n))) =
        (volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U))
    (hU : ContDiff ℝ 1 U) {G : NNReal} (hG : LipschitzWith G (gradient U)) {L : NNReal}
    (hL : LipschitzWith L U)
    (hnorm : (∫ x, Real.exp (-U x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1)
    (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (hessianMatrix U x).PosDef)
    (a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (C : ℝ)
    (heta : LocallyIntegrable eta (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖eta x‖ ≤ C)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong eta (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 :
      ∀ i : Fin n,
        ∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (henergy :
      Integrable (fun x => (fun i => a i x) ⬝ᵥ ((hessianMatrix U x)⁻¹ *ᵥ (fun i => a i x)))
        (nu : Measure (EuclideanSpace ℝ (Fin n)))) :
    ProbabilityTheory.variance eta (nu : Measure (EuclideanSpace ℝ (Fin n))) ≤
      ∫ x,
        (fun i => a i x) ⬝ᵥ
          ((hessianMatrix U x)⁻¹ *ᵥ
            (fun i => a i x)) ∂(nu : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hac :
    (nu : Measure (EuclideanSpace ℝ (Fin n))) ≪ (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [hnuU]
    exact tilted_absolutelyContinuous _ _
  have heta2 : MemLp eta 2 (nu : Measure (EuclideanSpace ℝ (Fin n))) :=
    MemLp.of_bound (heta.aestronglyMeasurable.mono_ac hac) C
      (Filter.Eventually.of_forall hbound)
  let F : Lp ℝ 2 (nu : Measure (EuclideanSpace ℝ (Fin n))) := heta2.toLp eta
  let D : ℝ :=
    ∫ x,
      (fun i => a i x) ⬝ᵥ
        ((hessianMatrix U x)⁻¹ *ᵥ (fun i => a i x)) ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))
  have hQ :
    ∀ w ∈ compactSmoothDiffusionImage (ν := nu) hU,
      2 * ⟪FunctionalInequalities.L2.center nu F, w⟫ - ‖w‖ ^ 2 ≤ D := by
    rintro w ⟨v, hv, hvc, rfl⟩
    let hLap :
      MemLp (fun x => -weightedLaplacian U v x) 2 (nu : Measure (EuclideanSpace ℝ (Fin n))) :=
      memLp_neg_weightedLaplacian (ν := nu) hU hv hvc
    let V : Lp ℝ 2 (nu : Measure (EuclideanSpace ℝ (Fin n))) :=
      hLap.toLp (fun x => -weightedLaplacian U v x)
    change 2 * ⟪FunctionalInequalities.L2.center nu F, V⟫ - ‖V‖ ^ 2 ≤ D
    have hmean : FunctionalInequalities.L2.mean nu V = 0 :=
      compact_diffusion_toLp_mean_zero volume hnuU hU hv hvc
    have hinner :
      ⟪F, V⟫ =
        ∫ x, eta x * (-weightedLaplacian U v x) ∂(nu : Measure (EuclideanSpace ℝ (Fin n))) :=
      real_inner_toLp heta2 hLap
    have hnormV :
      ‖V‖ ^ 2 = ∫ x, weightedLaplacian U v x ^ 2 ∂(nu : Measure (EuclideanSpace ℝ (Fin n))) := by
      simpa only [V, Real.norm_eq_abs, abs_neg, sq_abs] using
        FunctionalInequalities.L2.norm_toLp_sq hLap
    rw [inner_center_left_of_mean_zero nu F V hmean, hinner, hnormV]
    exact
      (compact_weak_variational_estimate hnuU hU hG hL hnorm hPD a C heta hbound hweak ha2
            henergy hv hvc).2.2
  have hclosure :
    FunctionalInequalities.L2.center nu F ∈
      closure (compactSmoothDiffusionImage (ν := nu) hU) :=
    center_mem_closure_compactSmoothDiffusionImage volume hnu hnuU hU F
  have hnormF : ‖FunctionalInequalities.L2.center nu F‖ ^ 2 ≤ D :=
    norm_sq_le_of_mem_closure_quadratic_bound (FunctionalInequalities.L2.center nu F) hclosure
      hQ
  have hvariance :
    (FunctionalInequalities.L2.variance nu F : ℝ) =
      ProbabilityTheory.variance eta (nu : Measure (EuclideanSpace ℝ (Fin n))) :=
    (FunctionalInequalities.L2.coe_variance_eq_pointwise nu F).trans
      (ProbabilityTheory.variance_congr heta2.coeFn_toLp)
  rw [← hvariance, FunctionalInequalities.L2.coe_variance]
  exact hnormF

end FunctionalInequalities.KLS.LogConcave
