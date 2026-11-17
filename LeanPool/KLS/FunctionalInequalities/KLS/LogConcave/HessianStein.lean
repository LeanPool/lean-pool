/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Operator.Coordinates
public import LeanPool.KLS.FunctionalInequalities.Probability.Stein.Kernel
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Coordinates
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Weak
public import LeanPool.KLS.FunctionalInequalities.Probability.Stein.HessianKernel
public import LeanPool.KLS.FunctionalInequalities.KLS.Isotropic
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Stein
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.LipschitzHessian
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Calculus

/-!
# The Hessian–Stein kernel of a normalized convex potential

Letwin, arXiv:2607.24164v1, Lemma 2.7, analytic part for a given potential. Let `φ` be smooth and
convex on `ℝⁿ` with `e^{-φ}` a probability density, `ν = e^{-φ}dx`, and `(∇φ)_* ν = μ` isotropic.
Then the entries of the Hessian matrix of `φ` are `ν`-integrable, and for a measurable left inverse
`Ψ`
of `∇φ` the Hessian kernel `τ = ∇²φ ∘ Ψ` is a Stein kernel of `μ` (Definition 2.6) with integrable
entries, a.e. symmetry,
positive semidefiniteness and mean `Id`; gradient injectivity (an explicit geometric prerequisite)
produces such a `Ψ`. The existence of the moment-map potential for an arbitrary law, strict positive
definiteness and the Hilbert–Schmidt `L²` bound (the rest of Lemma 2.7 and Theorem 2.5) are not
proved here.

At `C^{1,1}` regularity (`weak_hessianKernel_isSteinKernel`) the same kernel is a Stein kernel for a
`C¹` potential with
Lipschitz gradient and an a.e. left inverse, through the weak source Stein identity; the strong
regular-class producer with
a.e. positive definiteness and the Hilbert–Schmidt bound is
`Analysis.exists_regular_moment_target_stein_kernel`
(`KLS/CEK/MomentRegularity/TraceStein.lean`).
-/

@[expose] public section

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.KLS.LogConcave

section HessianKernel

/-! Shared context of the six Hessian-kernel results: a smooth convex normalized potential `φ`,
`ν = e^{-φ}dx` and the isotropic image law `μ = (∇φ)_* ν`. The hypotheses are included in every
theorem of the section in this order. -/

variable {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : ContDiff ℝ ∞ φ)
  (hcv : ConvexOn ℝ Set.univ φ)
  (hnorm : ∫ y, Real.exp (-φ y) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
  (ν μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hν : (ν : Measure (EuclideanSpace ℝ (Fin n))) = volume.tilted (-φ))
  (hmap :
    (ν : Measure (EuclideanSpace ℝ (Fin n))).map (gradient φ) =
      (μ : Measure (EuclideanSpace ℝ (Fin n))))
  (hiso : KLS.Isotropic μ)

include hφ hcv hnorm hν hmap hiso

/--
For a smooth convex normalized `φ` with `(∇φ)_* ν = μ` isotropic, the Hessian entries are
`ν`-integrable. -/
theorem integrable_hessianMatrix_of_isotropic_map (i j : Fin n) :
    Integrable (fun y => Probability.Stein.hessianMatrix φ y i j)
      (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hexp :
    Integrable (fun y => Real.exp (-φ y)) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  have hgrad :=
    Probability.Stein.memLp_two_gradient_of_map_eq (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) ν
      μ hmap hiso.memLp_two
  rw [hν] at hgrad ⊢
  exact Analysis.BakryEmery.integrable_hessian_tilted_of_convexOn φ hφ hcv hexp hnorm hgrad _ _

section LeftInverse

/-! A measurable left inverse `Ψ` of `∇φ` on a `ν`-full set; this context belongs only to the four
kernel results below. -/

variable (Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hΨ : Measurable Ψ)
    (hInv : ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin n))), Ψ (gradient φ y) = y)

include hΨ hInv

/-- The entries `τ_{ij} = (∇²φ ∘ Ψ)_{ij}` of the Hessian kernel are `μ`-integrable. -/
theorem integrable_hessianKernel_of_isotropic_map (i j : Fin n) :
    Integrable (fun x => Probability.Stein.hessianKernel φ Ψ x i j)
      (μ : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hg : Measurable (gradient φ) :=
    (continuous_gradient (hφ.of_le (WithTop.coe_le_coe.mpr le_top))).measurable
  have hk :=
    Probability.Stein.hessianKernel_entries_measurable
      (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) hΨ i j
  rw [← hmap]
  apply (integrable_map_measure hk.aestronglyMeasurable hg.aemeasurable).mpr
  have hH := integrable_hessianMatrix_of_isotropic_map φ hφ hcv hnorm ν μ hν hmap hiso i j
  apply hH.congr
  filter_upwards [Probability.Stein.hessianKernel_comp_gradient φ Ψ ν hInv] with y hy
  exact (congrArg (fun T => T i j) hy).symm

/--
**Compact-test Stein identity for the Hessian kernel**: `∫ x_i f dμ = ∫ (τ ∇f)_i dμ` for `f ∈ C_c^∞`
(A.3 applied to the bounded pullback `f ∘ ∇φ`, whose compact support is not assumed). -/
theorem hessianKernel_compact_identity (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (i : Fin n) :
    (∫ x, x i * f x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ x,
        Probability.Stein.action (Probability.Stein.hessianKernel φ Ψ x) (gradient f x)
          i ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have hgsmooth : ContDiff ℝ ∞ (gradient φ) := contDiff_gradient hφ (by simp)
  have hg := (continuous_gradient hφ1).measurable
  let F : EuclideanSpace ℝ (Fin n) → ℝ := f ∘ gradient φ
  have hF : ContDiff ℝ ∞ F := hf.comp hgsmooth
  obtain ⟨M0, hM0⟩ := hf.continuous.bounded_above_of_compact_support hfc
  obtain ⟨M1, hM1⟩ :=
    (continuous_gradient hf1).bounded_above_of_compact_support (hasCompactSupport_gradient hfc)
  have hgradν := Probability.Stein.memLp_two_gradient_of_map_eq hφ1 ν μ hmap hiso.memLp_two
  have hφi :
    Integrable (fun y => fderiv ℝ φ y (EuclideanSpace.basisFun (Fin n) ℝ i))
      (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hh := hgradν.inner_const (𝕜 := ℝ) (EuclideanSpace.basisFun (Fin n) ℝ i)
    simpa only [inner_gradient_left] using hh.integrable one_le_two
  have hFbd : ∀ y, ‖F y‖ ≤ M0 := fun y => hM0 (gradient φ y)
  have hFi :
    Integrable (fun y => F y * fderiv ℝ φ y (EuclideanSpace.basisFun (Fin n) ℝ i))
      (ν : Measure (EuclideanSpace ℝ (Fin n))) :=
    hφi.bdd_mul hF.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hFbd)
  have hFint : Integrable F (ν : Measure (EuclideanSpace ℝ (Fin n))) :=
    (integrable_const M0).mono' hF.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hFbd)
  have hdfF :
    Integrable (fun y => fderiv ℝ F y (EuclideanSpace.basisFun (Fin n) ℝ i))
      (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hterms (j : Fin n) :
      Integrable
        (fun y => Probability.Stein.hessianMatrix φ y i j * gradient f (gradient φ y) j)
        (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
      have hh := integrable_hessianMatrix_of_isotropic_map φ hφ hcv hnorm ν μ hν hmap hiso i j
      have hb : ∀ y, ‖gradient f (gradient φ y) j‖ ≤ M1 := fun y =>
        (PiLp.norm_apply_le _ j).trans (hM1 (gradient φ y))
      have hcont : Continuous (fun y => gradient f (gradient φ y) j) :=
        (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp
          ((continuous_gradient hf1).comp (continuous_gradient hφ1))
      exact hh.mul_bdd hcont.aestronglyMeasurable (Filter.Eventually.of_forall hb)
    have hh := integrable_finsetSum (s := (Finset.univ : Finset (Fin n))) (fun j _ => hterms j)
    apply hh.congr
    exact
      Filter.Eventually.of_forall fun y => (Probability.Stein.chain_coordinate hφ2 hf1 y i).symm
  have hexp :
    Integrable (fun y => Real.exp (-φ y)) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  have hdfLaw :
    Integrable (fun y => fderiv ℝ F y (EuclideanSpace.basisFun (Fin n) ℝ i) * (1 : ℝ))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-φ)) := by
    rw [← hν]; simpa only [mul_one] using hdfF
  have hprodLaw :
    Integrable (fun y => F y * (1 : ℝ) * fderiv ℝ φ y (EuclideanSpace.basisFun (Fin n) ℝ i))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-φ)) := by
    rw [← hν]; simpa only [mul_one] using hFi
  have hFLaw :
    Integrable (fun y => F y * (1 : ℝ))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-φ)) := by
    rw [← hν]; simpa only [mul_one] using hFint
  have hA3 :=
    integral_fderiv_mul_tilted_eq (volume : Measure (EuclideanSpace ℝ (Fin n))) φ F (fun _ => 1)
      (EuclideanSpace.basisFun (Fin n) ℝ i) hφ hF contDiff_const hexp hnorm hdfLaw (by simp)
      hprodLaw hFLaw
  rw [← hν] at hA3
  have hDir (y : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ φ y (EuclideanSpace.basisFun (Fin n) ℝ i) = gradient φ y i := by
    rw [← inner_gradient_left]
    exact EuclideanSpace.inner_basisFun_real (Fin n) _ i
  have hA3' :
    (∫ y,
        fderiv ℝ F y
          (EuclideanSpace.basisFun (Fin n) ℝ i) ∂(ν : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ y, gradient φ y i * f (gradient φ y) ∂(ν : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [mul_one, one_mul, fderiv_const_apply, zero_apply, sub_zero, F,
      Function.comp_def, hDir, mul_comm] using hA3
  have hLmeas : Measurable (fun x : EuclideanSpace ℝ (Fin n) => x i * f x) :=
    (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).measurable.mul hf.continuous.measurable
  have hRmeas :
    Measurable
      (fun x =>
        Probability.Stein.action (Probability.Stein.hessianKernel φ Ψ x) (gradient f x) i) := by
    change Measurable (fun x => ∑ j, Probability.Stein.hessianKernel φ Ψ x i j * gradient f x j)
    exact
      Finset.measurable_sum _
        (fun j _ =>
          (Probability.Stein.hessianKernel_entries_measurable hφ2 hΨ i j).mul
            ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp
                (continuous_gradient hf1)).measurable)
  rw [← hmap, integral_map hg.aemeasurable hLmeas.aestronglyMeasurable,
    integral_map hg.aemeasurable hRmeas.aestronglyMeasurable]
  have hR :
    (fun y =>
        Probability.Stein.action (Probability.Stein.hessianKernel φ Ψ (gradient φ y))
          (gradient f (gradient φ y)) i) =ᵐ[(ν : Measure (EuclideanSpace ℝ (Fin n)))]
      fun y => fderiv ℝ F y (EuclideanSpace.basisFun (Fin n) ℝ i) := by
    filter_upwards [Probability.Stein.hessianKernel_comp_gradient φ Ψ ν hInv] with y hy
    rw [hy]
    exact (Probability.Stein.chain_coordinate hφ2 hf1 y i).symm
  rw [integral_congr_ae hR]
  exact hA3'.symm

/-- `τ = ∇²φ ∘ Ψ` is a Stein kernel of `μ` (Definition 2.6). -/
theorem hessianKernel_isSteinKernel :
    Probability.Stein.IsSteinKernel μ (Probability.Stein.hessianKernel φ Ψ)
    where
  integrable_id := hiso.memLp_two.integrable one_le_two
  mean_zero := hiso.mean_zero
  measurable_entries :=
    Probability.Stein.hessianKernel_entries_measurable
      (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) hΨ
  local_entries := fun i j =>
    (integrable_hessianKernel_of_isotropic_map φ hφ hcv hnorm ν μ hν hmap hiso Ψ hΨ hInv i
        j).locallyIntegrable
  compact_identity := hessianKernel_compact_identity φ hφ hcv hnorm ν μ hν hmap hiso Ψ hΨ hInv

/-- `∫ τ dμ = Id` (mean Hessian identity). -/
theorem integral_hessianKernel_eq_one (i j : Fin n) :
    (∫ x, Probability.Stein.hessianKernel φ Ψ x i j ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) =
      (1 : Probability.Stein.KernelMatrix n) i j := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg := (continuous_gradient hφ1).measurable
  have hk :=
    Probability.Stein.hessianKernel_entries_measurable
      (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) hΨ i j
  rw [← hmap, integral_map hg.aemeasurable hk.aestronglyMeasurable]
  have hcoup :
    (fun y =>
        Probability.Stein.hessianKernel φ Ψ (gradient φ y) i
          j) =ᵐ[(ν : Measure (EuclideanSpace ℝ (Fin n)))]
      fun y => Probability.Stein.hessianMatrix φ y i j := by
    filter_upwards [Probability.Stein.hessianKernel_comp_gradient φ Ψ ν hInv] with y hy
    exact congrArg (fun T => T i j) hy
  rw [integral_congr_ae hcoup]
  have hEq : ν.map (gradient φ) = μ := by
    apply ProbabilityMeasure.toMeasure_injective
    simpa only [ProbabilityMeasure.toMeasure_map] using hmap
  have hI : KLS.Isotropic (ν.map (gradient φ)) := by rw [hEq]; exact hiso
  have h :=
    integral_hessian_eq_inner_of_isotropic_map φ hφ hcv hnorm ν hν hI
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)
  have he :
    ⟪EuclideanSpace.basisFun (Fin n) ℝ i, EuclideanSpace.basisFun (Fin n) ℝ j⟫ =
      (1 : Probability.Stein.KernelMatrix n) i j := by
    rw [EuclideanSpace.basisFun_inner]
    change (EuclideanSpace.basisFun (Fin n) ℝ j) i = (if i = j then (1 : ℝ) else 0)
    rw [EuclideanSpace.basisFun_apply]
    change (PiLp.single 2 j (1 : ℝ) : EuclideanSpace ℝ (Fin n)) i = _
    simp only [PiLp.single_apply]
  rw [he] at h
  exact h

end LeftInverse

/--
**Letwin Lemma 2.7, analytic part for a given potential**: if `φ` is smooth, convex, normalized,
`ν = e^{-φ}dx`, `(∇φ)_* ν = μ` is isotropic and `∇φ` is injective (explicit prerequisite), then with
a
measurable left inverse `Ψ` the Hessian kernel `∇²φ ∘ Ψ` is a symmetric, positive semidefinite,
integrable
Stein kernel of `μ` with mean `Id` and coupling `τ(∇φ y) = ∇²φ(y)`. The moment map `φ` for an
arbitrary law, strict
positive definiteness and `|τ|_HS ∈ L²` are not provided. -/
theorem exists_hessianSteinKernel_of_injective_gradient
    (hInj : Function.Injective (gradient φ)) :
    ∃ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      Measurable Ψ ∧
        Function.LeftInverse Ψ (gradient φ) ∧
          Probability.Stein.IsSteinKernel μ (Probability.Stein.hessianKernel φ Ψ) ∧
            Probability.Stein.SymmetricAE μ (Probability.Stein.hessianKernel φ Ψ) ∧
              (∀ i j,
                  Integrable (fun x => Probability.Stein.hessianKernel φ Ψ x i j)
                    (μ : Measure (EuclideanSpace ℝ (Fin n)))) ∧
                (∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin n))),
                    Probability.Stein.hessianKernel φ Ψ (gradient φ y) =
                      Probability.Stein.hessianMatrix φ y) ∧
                  (∀ x v,
                      0 ≤
                        ⟪v,
                          Probability.Stein.action (Probability.Stein.hessianKernel φ Ψ x) v⟫) ∧
                    (∀ i j,
                      (∫ x,
                          Probability.Stein.hessianKernel φ Ψ x i
                            j ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) =
                        (1 : Probability.Stein.KernelMatrix n) i j) := by
  obtain ⟨Ψ, hΨ, hi⟩ :=
    Probability.Stein.exists_measurable_leftInverse_gradient_of_injective
      (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) hInj
  have hiAE : ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin n))), Ψ (gradient φ y) = y :=
    Filter.Eventually.of_forall hi
  refine
    ⟨Ψ, hΨ, hi, hessianKernel_isSteinKernel φ hφ hcv hnorm ν μ hν hmap hiso Ψ hΨ hiAE,
      Probability.Stein.hessianKernel_symmetricAE (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) Ψ
        μ,
      fun i j =>
      integrable_hessianKernel_of_isotropic_map φ hφ hcv hnorm ν μ hν hmap hiso Ψ hΨ hiAE i j,
      Probability.Stein.hessianKernel_comp_gradient φ Ψ ν hiAE, fun x v =>
      Probability.Stein.hessianKernel_quadratic_nonneg
        (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) hcv Ψ x v,
      fun i j => integral_hessianKernel_eq_one φ hφ hcv hnorm ν μ hν hmap hiso Ψ hΨ hiAE i j⟩

end HessianKernel

end FunctionalInequalities.KLS.LogConcave

section WeakSourceSteinIdentity

open MeasureTheory Filter
open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.Stein
open scoped ContDiff Topology RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave

/--
Weak source Stein identity at a C1 potential with Lipschitz gradient and mass-one exponential
weight: for every C1 bounded
globally Lipschitz test `f` the coordinate pairing `∫ ∂ᵢu · f(∇u)` equals `∫ ∑ⱼ (∇²u)ᵢⱼ ∂ⱼf(∇u)`
(both integrable);
no C2, global inverse or kernel premise. -/
theorem source_stein_identity_of_bounded_lipschitz_test {n : ℕ}
    {u f : EuclideanSpace ℝ (Fin n) → ℝ} {L G Lf : NNReal} (hu : ContDiff ℝ 1 u)
    (hL : LipschitzWith L u) (hG : LipschitzWith G (gradient u))
    (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1) (hf : ContDiff ℝ 1 f)
    (hfLip : LipschitzWith Lf f) (C : ℝ) (hbound : ∀ x, ‖f x‖ ≤ C) (i : Fin n) :
    Integrable (fun y => gradient u y i * f (gradient u y))
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
      Integrable (fun y => ∑ j, hessianMatrix u y i j * gradient f (gradient u y) j)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ y,
            gradient u y i *
              f (gradient u y) ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          ∫ y,
            (∑ j,
              hessianMatrix u y i j *
                gradient f (gradient u y)
                  j) ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) := by
  let eta := f ∘ gradient u
  let mu : Measure (EuclideanSpace ℝ (Fin n)) := volume.tilted (-u)
  have hpair :=
    integral_fderiv_tilted_eq_integral_mul_fderiv_of_bounded_lipschitz hL (hfLip.comp hG) C
      (fun y => hbound (gradient u y)) hnorm (EuclideanSpace.basisFun (Fin n) ℝ i)
  have hleft :
    (fun y => eta y * fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ i)) =ᵐ[mu]
      (fun y => gradient u y i * f (gradient u y)) := by
    filter_upwards [] with y
    have hdu : fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ i) = gradient u y i := by
      rw [← inner_gradient_left, EuclideanSpace.inner_basisFun_real]
    dsimp only [eta, Function.comp_apply]
    rw [hdu, mul_comm]
  have hchain :
    (fun y => fderiv ℝ eta y (EuclideanSpace.basisFun (Fin n) ℝ i)) =ᵐ[mu]
      (fun y => ∑ j, hessianMatrix u y i j * gradient f (gradient u y) j) := by
    have hac : mu ≪ (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      tilted_absolutelyContinuous _ _
    filter_upwards [hac.ae_le (hG.ae_differentiableAt (μ := volume))] with y hy
    exact chain_coordinate_of_differentiableAt_gradient hu hf hy i
  refine ⟨hpair.2.1.congr hleft, hpair.1.congr hchain, ?_⟩
  calc
    _ = ∫ y, eta y * fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ i) ∂mu :=
      (integral_congr_ae hleft).symm
    _ = ∫ y, fderiv ℝ eta y (EuclideanSpace.basisFun (Fin n) ℝ i) ∂mu := hpair.2.2.symm
    _ = _ := integral_congr_ae hchain

end FunctionalInequalities.KLS.LogConcave

end WeakSourceSteinIdentity

/-! ### Directional and affine source Stein identities

For `C¹` globally Lipschitz `u` with Lipschitz gradient and `∫ e^{-u} = 1`, the coordinate source
Stein identity in a direction `v`, and its form for tests `h (S x + z)` with a continuous linear
`S`. -/

section
open MeasureTheory
open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave

theorem source_directional_stein_identity_of_bounded_lipschitz_test {n : ℕ}
    {u f : EuclideanSpace ℝ (Fin n) → ℝ} {L G Lf : NNReal} (hu : ContDiff ℝ 1 u)
    (hL : LipschitzWith L u) (hG : LipschitzWith G (gradient u))
    (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1) (hf : ContDiff ℝ 1 f)
    (hfLip : LipschitzWith Lf f) (C : ℝ) (hbound : ∀ x, ‖f x‖ ≤ C)
    (v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y => ⟪gradient u y, v⟫ * f (gradient u y))
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
      Integrable (fun y => ⟪v, action (hessianMatrix u y) (gradient f (gradient u y))⟫)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ y,
            ⟪gradient u y, v⟫ *
              f (gradient u y) ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          ∫ y,
            ⟪v,
              action (hessianMatrix u y)
                (gradient f
                  (gradient u
                    y))⟫ ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) := by
  classical
  let mu : Measure (EuclideanSpace ℝ (Fin n)) := volume.tilted (-u)
  let A (i : Fin n) (y : EuclideanSpace ℝ (Fin n)) := gradient u y i * f (gradient u y)
  let B (i : Fin n) (y : EuclideanSpace ℝ (Fin n)) :=
    ∑ j, hessianMatrix u y i j * gradient f (gradient u y) j
  have hp (i : Fin n) :=
    source_stein_identity_of_bounded_lipschitz_test hu hL hG hnorm hf hfLip C hbound i
  have hA : Integrable (fun y => ∑ i, v i * A i y) mu :=
    integrable_finsetSum Finset.univ fun i _ => (hp i).1.const_mul (v i)
  have hB : Integrable (fun y => ∑ i, v i * B i y) mu :=
    integrable_finsetSum Finset.univ fun i _ => (hp i).2.1.const_mul (v i)
  have heqA (y : EuclideanSpace ℝ (Fin n)) :
    (∑ i, v i * A i y) = ⟪gradient u y, v⟫ * f (gradient u y) := by
    simp only [PiLp.inner_apply, Real.inner_apply, Finset.sum_mul, A]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have heqB (y : EuclideanSpace ℝ (Fin n)) :
    (∑ i, v i * B i y) = ⟪v, action (hessianMatrix u y) (gradient f (gradient u y))⟫ := by
    simp only [PiLp.inner_apply, Real.inner_apply, action, Matrix.mulVec, dotProduct, B]
  refine ⟨hA.congr (ae_of_all _ heqA), hB.congr (ae_of_all _ heqB), ?_⟩
  calc
    _ = ∫ y, ∑ i, v i * A i y ∂mu := (integral_congr_ae (ae_of_all _ heqA)).symm
    _ = ∑ i, v i * ∫ y, A i y ∂mu := by
      rw [integral_finsetSum Finset.univ (fun i _ => (hp i).1.const_mul (v i))]
      simp only [integral_const_mul, A, mu]
    _ = ∑ i, v i * ∫ y, B i y ∂mu := by
      apply Finset.sum_congr rfl
      intro i _
      rw [(hp i).2.2]
    _ = ∫ y, ∑ i, v i * B i y ∂mu := by
      rw [integral_finsetSum Finset.univ (fun i _ => (hp i).2.1.const_mul (v i))]
      simp only [integral_const_mul, B, mu]
    _ = _ := integral_congr_ae (ae_of_all _ heqB)

end FunctionalInequalities.KLS.LogConcave

end

section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave

theorem source_affine_stein_identity_of_bounded_lipschitz_test {n : ℕ}
    {u h : EuclideanSpace ℝ (Fin n) → ℝ} {L G Lh : NNReal} (hu : ContDiff ℝ 1 u)
    (hL : LipschitzWith L u) (hG : LipschitzWith G (gradient u))
    (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1) (hh : ContDiff ℝ 1 h)
    (hhLip : LipschitzWith Lh h) (C : ℝ) (hbound : ∀ x, ‖h x‖ ≤ C)
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (z v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y => ⟪S (gradient u y), v⟫ * h (S (gradient u y) + z))
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
      Integrable
          (fun y =>
            ⟪S.adjoint v,
              action (hessianMatrix u y) (S.adjoint (gradient h (S (gradient u y) + z)))⟫)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ y,
            ⟪S (gradient u y), v⟫ *
              h
                (S (gradient u y) +
                  z) ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          ∫ y,
            ⟪S.adjoint v,
              action (hessianMatrix u y)
                (S.adjoint
                  (gradient h
                    (S (gradient u y) +
                      z)))⟫ ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) := by
  have hf : ContDiff ℝ 1 (fun x => h (S x + z)) := hh.comp (S.contDiff.add contDiff_const)
  have hp :=
    source_directional_stein_identity_of_bounded_lipschitz_test hu hL hG hnorm hf
      (hhLip.comp (S.lipschitzWith.add (LipschitzWith.const z))) C (fun x => hbound (S x + z))
      (S.adjoint v)
  have hleft (y : EuclideanSpace ℝ (Fin n)) :
    ⟪gradient u y, S.adjoint v⟫ * h (S (gradient u y) + z) =
      ⟪S (gradient u y), v⟫ * h (S (gradient u y) + z) := by
    rw [S.adjoint_inner_right]
  have hright (y : EuclideanSpace ℝ (Fin n)) :
    ⟪S.adjoint v, action (hessianMatrix u y) (gradient (fun x => h (S x + z)) (gradient u y))⟫ =
      ⟪S.adjoint v,
        action (hessianMatrix u y) (S.adjoint (gradient h (S (gradient u y) + z)))⟫ := by
    rw [gradient_comp_affine S z (hh.differentiable one_ne_zero _)]
  refine ⟨hp.1.congr (ae_of_all _ hleft), hp.2.1.congr (ae_of_all _ hright), ?_⟩
  exact
    (integral_congr_ae (ae_of_all _ hleft)).symm.trans
      (hp.2.2.trans (integral_congr_ae (ae_of_all _ hright)))

end FunctionalInequalities.KLS.LogConcave

end

/-! ### Weak Hessian–Stein kernel at `C^{1,1}` regularity -/

section
open MeasureTheory Filter
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave

/--
**Weak Hessian–Stein kernel for a given `C^{1,1}` potential**: if `u` is `C¹`, Lipschitz, with
Lipschitz gradient and
`∫ e^{-u} = 1`, `(∇u)_*(e^{-u} dx) = μ` is isotropic and `Ψ` is a measurable `e^{-u} dx`-a.e. left
inverse of `∇u`, then
`∇²u ∘ Ψ` is a Stein kernel of `μ` (Definition 2.6), from the weak source identity
`source_stein_identity_of_bounded_lipschitz_test`. No `C²` or convexity hypothesis. -/
theorem weak_hessianKernel_isSteinKernel {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {L G : NNReal} (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u))
    (hnorm : ∫ y, Real.exp (-u y) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hmap :
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hiso : KLS.Isotropic μ) {Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hΨ : Measurable Ψ)
    (hInv :
      ∀ᵐ y ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)), Ψ (gradient u y) = y) :
    IsSteinKernel μ (hessianKernel u Ψ) := by
  have hmeas (i j : Fin n) : Measurable (fun x => hessianKernel u Ψ x i j) :=
    (measurable_hessianMatrix_entry u i j).comp hΨ
  refine ⟨hiso.memLp_two.integrable one_le_two, hiso.mean_zero, hmeas, ?_, ?_⟩
  · intro i j
    have hmem : MemLp (fun x => hessianKernel u Ψ x i j) 2 (μ : Measure _) :=
      MemLp.of_bound (hmeas i j).aestronglyMeasurable (G : ℝ)
        (ae_of_all _ fun x => norm_hessianMatrix_entry_le_of_lipschitz_gradient hG (Ψ x) i j)
    exact (hmem.integrable one_le_two).locallyIntegrable
  · intro f hf hfc i
    have hf1 : ContDiff ℝ 1 f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
    obtain ⟨Lf, hfLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hfc hf1 one_ne_zero
    obtain ⟨C, hC⟩ := hf.continuous.bounded_above_of_compact_support hfc
    have hid := source_stein_identity_of_bounded_lipschitz_test hu hL hG hnorm hf1 hfLip C hC i
    have hg := (continuous_gradient hu).measurable
    have hLm : Measurable (fun x : EuclideanSpace ℝ (Fin n) => x i * f x) :=
      (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).measurable.mul hf.continuous.measurable
    have hRm : Measurable (fun x => action (hessianKernel u Ψ x) (gradient f x) i) := by
      change Measurable (fun x => ∑ j, hessianKernel u Ψ x i j * gradient f x j)
      exact
        Finset.measurable_sum _ fun j _ =>
          (hmeas i j).mul
            ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp
                (continuous_gradient hf1)).measurable
    rw [← hmap, integral_map hg.aemeasurable hLm.aestronglyMeasurable,
      integral_map hg.aemeasurable hRm.aestronglyMeasurable]
    rw [hid.2.2]
    apply integral_congr_ae
    filter_upwards [hInv] with y hy
    simp only [hessianKernel, hy, action, Matrix.mulVec, dotProduct]

end FunctionalInequalities.KLS.LogConcave

end
