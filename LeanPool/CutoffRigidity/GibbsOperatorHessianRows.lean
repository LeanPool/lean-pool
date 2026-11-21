/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsOperatorWeakHessian
public import LeanPool.CutoffRigidity.WeakH1Mollification

/-! # Actual selected symmetric local Hessian rows

Every selected coordinate is a genuine Riesz L² representative of the
second distributional derivative of the actual cutoff eigenfunction.
Dense compact tests prove symmetry independently of representative choices.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual local weak Hessian coordinate, selected from the proved existence theorem. -/
@[expose] noncomputable def gibbsOperatorLocalizedHessian {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (i j : Fin d) : E →₂[volume] ℝ :=
  Classical.choose (exists_gibbsOperatorEigen_local_weak_hessian hV hprob rate u hχ hχc i j)

theorem gibbsOperatorLocalizedHessian_spec {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (i j : Fin d) :
    ‖gibbsOperatorLocalizedHessian hV hprob rate u hχ hχc i j‖ ≤
      ‖(localizedOperatorEigenLaplacian_memLp hV hprob rate u hχ hχc).toLp
        (localizedOperatorEigenLaplacian hV hprob rate u χ)‖ ∧
    ∀ ψ : E → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∫ x, (χ x * (u : E →₂[gibbsMeasure volume V] ℝ) x) *
        coordinateDerivative j (coordinateDerivative i ψ) x) =
          ∫ x, gibbsOperatorLocalizedHessian hV hprob rate u hχ hχc i j x * ψ x :=
  Classical.choose_spec (exists_gibbsOperatorEigen_local_weak_hessian hV hprob rate u hχ hχc i j)

/-- The selected Hessian row is the actual weak derivative of the actual
localized weak-gradient coordinate. -/
theorem gibbsOperatorLocalizedHessian_weak_derivative {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (i j : Fin d) (ψ : E → ℝ) (hψ : ContDiff ℝ 3 ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, localizedOperatorEigenGradient hV hprob rate u χ i x * coordinateDerivative j ψ x) =
      -(∫ x, gibbsOperatorLocalizedHessian hV hprob rate u hχ hχc i j x * ψ x) := by
  rw [localizedOperatorEigenGradient_second_test hV hprob rate u hχ hχc hψ i j,
    (gibbsOperatorLocalizedHessian_spec hV hprob rate u hχ hχc i j).2 ψ hψ hψc]

/-- Actual compact-test L² pairing uniqueness. -/
theorem L2_eq_of_compact_C3_test_pairings (H K : E →₂[volume] ℝ)
    (heq : ∀ ψ : E → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∫ x, H x * ψ x) = ∫ x, K x * ψ x) : H = K := by
  apply compactEuclideanTestSpace_dense.eq_of_inner_left ℝ
  intro v hv
  let t : compactEuclideanTestSpace (d := d) := ⟨v, hv⟩
  have hs := compactEuclideanTestRep_spec t
  have hIH : inner ℝ H v = ∫ x, H x * compactEuclideanTestRep t x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hs.2.2] with x hx
    rw [← hx, Real.inner_apply]
  have hIK : inner ℝ K v = ∫ x, K x * compactEuclideanTestRep t x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hs.2.2] with x hx
    rw [← hx, Real.inner_apply]
  exact hIH.trans ((heq _ hs.1 hs.2.1).trans hIK.symm)

/-- The actual selected local Hessian is symmetric in L², proved from
commutation on smooth tests and density, not postulated as a tensor premise. -/
theorem gibbsOperatorLocalizedHessian_symmetric {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (i j : Fin d) :
    gibbsOperatorLocalizedHessian hV hprob rate u hχ hχc i j =
      gibbsOperatorLocalizedHessian hV hprob rate u hχ hχc j i := by
  apply L2_eq_of_compact_C3_test_pairings
  intro ψ hψ hψc
  have hi := (gibbsOperatorLocalizedHessian_spec hV hprob rate u hχ hχc i j).2 ψ hψ hψc
  have hj := (gibbsOperatorLocalizedHessian_spec hV hprob rate u hχ hχc j i).2 ψ hψ hψc
  simp_rw [coordinateDerivative_commute (hψ.of_le (by norm_num) : ContDiff ℝ 2 ψ) i j] at hj
  exact hi.symm.trans hj

/-- The actual vector L² Hessian row used in strong weak-H¹ approximation. -/
@[expose] noncomputable def gibbsOperatorLocalizedHessianRow {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (i : Fin d) : E →₂[volume] E :=
  euclideanL2Assemble (fun j => gibbsOperatorLocalizedHessian hV hprob rate u hχ hχc i j)

/-- The localized weak-gradient representative is genuinely measurable. -/
theorem localizedOperatorEigenGradient_measurable {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) (hχ : ContDiff ℝ 3 χ) (i : Fin d) :
    Measurable (localizedOperatorEigenGradient hV hprob rate u χ i) := by
  have hU := (Lp.stronglyMeasurable (u : E →₂[gibbsMeasure volume V] ℝ)).measurable
  have hG := (Lp.stronglyMeasurable (gibbsSobolevDerivative hV hprob
    (gibbsOperatorEigenSobolevLift hV hprob rate u))).measurable
  have hGi := (EuclideanSpace.proj i : E →L[ℝ] ℝ).continuous.measurable.comp hG
  have hDχ := (c1_coordinateDerivative_of_c2 (hχ.of_le (by norm_num)) i).continuous.measurable
  unfold localizedOperatorEigenGradient
  exact (hχ.continuous.measurable.mul hGi).add (hU.mul hDχ)

/-- The actual localized weak-gradient representative has actual compact support. -/
theorem localizedOperatorEigenGradient_hasCompactSupport {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) (hχc : HasCompactSupport χ) (i : Fin d) :
    HasCompactSupport (localizedOperatorEigenGradient hV hprob rate u χ i) := by
  have ha := hχc.mul_right (f' := fun x =>
    (gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u) x) i)
  have hb := (hχc.fderiv_apply ℝ (EuclideanSpace.single i 1)).mul_left
    (f := fun x => (u : E →₂[gibbsMeasure volume V] ℝ) x)
  unfold localizedOperatorEigenGradient
  simpa only [coordinateDerivative, Pi.add_def, Pi.mul_def] using ha.add hb

/-- Compact smooth mollifications of the actual localized first gradient
converge strongly together with their actual vector gradients. -/
theorem gibbsOperatorLocalizedHessianRow_mollified_gradient_tendsto {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (i : Fin d) (φ : ℕ → ContDiffBump (0 : E))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) :
    Tendsto (fun n => mollifiedGradientLp (φ n) (localizedOperatorEigenGradient hV hprob rate u χ i)
      ((localizedOperatorEigenGradient_memLp hV hprob rate u hχ hχc i).locallyIntegrable
        (by norm_num))
      (localizedOperatorEigenGradient_hasCompactSupport hV hprob rate u hχc i))
      atTop (𝓝 (gibbsOperatorLocalizedHessianRow hV hprob rate u hχ hχc i)) := by
  apply mollifiedGradientLp_tendsto_of_weak_derivatives φ hφ
  intro j ψ hψ hψc
  exact gibbsOperatorLocalizedHessian_weak_derivative hV hprob rate u hχ hχc i j ψ hψ hψc

/-- The actual localized first-gradient function also converges strongly
under the same smoothings, independently of a translation modulus. -/
theorem localizedOperatorEigenGradient_mollified_tendsto {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (i : Fin d) (φ : ℕ → ContDiffBump (0 : E))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) :
    Tendsto (fun n => bumpMollificationLp (φ n) (localizedOperatorEigenGradient hV hprob rate u χ i)
      (localizedOperatorEigenGradient_measurable hV hprob rate u hχ i)
      (localizedOperatorEigenGradient_memLp hV hprob rate u hχ hχc i)) atTop
      (𝓝 ((localizedOperatorEigenGradient_memLp hV hprob rate u hχ hχc i).toLp
        (localizedOperatorEigenGradient hV hprob rate u χ i))) :=
  bumpMollificationLp_tendsto φ hφ _ _ _

end CutoffRigidity
