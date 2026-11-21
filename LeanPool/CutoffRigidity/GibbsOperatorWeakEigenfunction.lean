/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsSelfAdjointEigenfunctions
public import LeanPool.CutoffRigidity.GibbsWeakDerivative

/-!
# Actual operator eigenvectors satisfy the genuine weak eigenfunction PDE

The actual self-adjoint graph determines the variational resolvent and
hence a canonical closed-form-domain lift. No classical representative,
weak H² regularity or pointwise eigenfunction equation is assumed.
-/

public section

namespace CutoffRigidity

open MeasureTheory
open scoped LinearPMap ENNReal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual operator eigenvectors satisfy the shifted resolvent identity,
directly from the actual inverse-resolvent graph. -/
theorem gibbsOperatorEigen_resolvent {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) :
    gibbsL2Resolvent hV hprob ((1 + rate) • (u : E →₂[gibbsMeasure volume V] ℝ)) =
      (u : E →₂[gibbsMeasure volume V] ℝ) := by
  have hu := u.property
  change ((u : E →₂[gibbsMeasure volume V] ℝ), rate • (u : E →₂[gibbsMeasure volume V] ℝ)) ∈
    (positiveResolventOperator (gibbsL2Resolvent hV hprob)).graph at hu
  rw [positiveResolventOperator_graph _ (gibbsL2Resolvent_injective hV hprob),
    mem_positiveResolventGraph] at hu
  obtain ⟨f, hf, hAf⟩ := hu
  have hshift : f = (1 + rate) • (u : E →₂[gibbsMeasure volume V] ℝ) := by
    rw [hf] at hAf
    calc
      f = (u : E →₂[gibbsMeasure volume V] ℝ) + rate • (u : E →₂[gibbsMeasure volume V] ℝ) := by
        exact sub_eq_iff_eq_add.mp hAf |>.trans (add_comm _ _)
      _ = _ := by module
  rwa [hshift] at hf

/-- The canonical H¹ lift of an actual operator eigenclass is constructed
from the actual variational resolvent. -/
@[expose] noncomputable def gibbsOperatorEigenSobolevLift {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) : gibbsSobolevGraph hV hprob :=
  gibbsWeakResolvent hV hprob ((1 + rate) • (u : E →₂[gibbsMeasure volume V] ℝ))

/-- The lift's actual L² value is the original operator eigenclass. -/
theorem gibbsOperatorEigenSobolevLift_inclusion {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) :
    gibbsSobolevInclusion hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u) =
      (u : E →₂[gibbsMeasure volume V] ℝ) := gibbsOperatorEigen_resolvent hV hprob rate u

/-- The full genuine variational eigenfunction equation, for every actual
closed Sobolev test. No regularity assumption on the eigenvector is imposed. -/
theorem gibbsOperatorEigenSobolevLift_weak_eigenfunction {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) (v : gibbsSobolevGraph hV hprob) :
    gibbsDirichletEnergy hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u) v =
      rate * inner ℝ (u : E →₂[gibbsMeasure volume V] ℝ) (gibbsSobolevInclusion hV hprob v) := by
  have hh := gibbsWeakResolvent_equation hV hprob
    ((1 + rate) • (u : E →₂[gibbsMeasure volume V] ℝ)) v
  change inner ℝ (gibbsSobolevInclusion hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u))
      (gibbsSobolevInclusion hV hprob v) +
    gibbsDirichletEnergy hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u) v = _ at hh
  rw [gibbsOperatorEigenSobolevLift_inclusion, real_inner_smul_left] at hh
  linarith

/-- The exact actual global weak-gradient energy identity for operator eigenvectors. -/
theorem gibbsOperatorEigen_energy {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) :
    ‖gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u)‖ ^ 2 =
      rate * ‖(u : E →₂[gibbsMeasure volume V] ℝ)‖ ^ 2 := by
  have hh := gibbsOperatorEigenSobolevLift_weak_eigenfunction hV hprob rate u
    (gibbsOperatorEigenSobolevLift hV hprob rate u)
  rw [gibbsOperatorEigenSobolevLift_inclusion, gibbsDirichletEnergy,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hh
  exact hh

/-- Nonzero actual operator eigenvectors have nonnegative eigenvalue,
proved from the actual weak-gradient energy. -/
theorem gibbsOperatorEigen_eigenvalue_nonneg {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) (hu : (u : E →₂[gibbsMeasure volume V] ℝ) ≠ 0) :
    0 ≤ rate := by
  have hh := gibbsOperatorEigen_energy hV hprob rate u
  have hp : 0 < ‖(u : E →₂[gibbsMeasure volume V] ℝ)‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  nlinarith [sq_nonneg ‖gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob
    rate u)‖]

/-- Actual operator eigenvectors satisfy the original weighted weak PDE
against every compact C² test, with their genuine closed weak gradient. -/
theorem gibbsOperatorEigen_compact_test_equation {V φ : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    (∫ x, inner ℝ
      (gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u) x)
      (gradient φ x) ∂gibbsMeasure volume V) =
      rate * (∫ x, (u : E →₂[gibbsMeasure volume V] ℝ) x * φ x ∂gibbsMeasure volume V) := by
  let := hprob
  have hφLp : MemLp φ 2 (gibbsMeasure volume V) := hφ.continuous.memLp_of_hasCompactSupport hφc
  have hgradc : HasCompactSupport (gradient φ) :=
    (hφc.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ E).symm) (by simp)
  have hgLp : MemLp (gradient φ) 2 (gibbsMeasure volume V) :=
    (continuous_gradient_of_c1 (hφ.of_le (by norm_num))).memLp_of_hasCompactSupport hgradc
  let v := c2GibbsSobolevLift hV hprob hφ hφLp hgLp
  have he := gibbsOperatorEigenSobolevLift_weak_eigenfunction hV hprob rate u v
  have hleft : gibbsDirichletEnergy hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u) v =
      ∫ x, inner ℝ
        (gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u) x)
        (gradient φ x) ∂gibbsMeasure volume V := by
    rw [gibbsDirichletEnergy, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hgLp.coeFn_toLp] with x hx
    change inner ℝ _ (hgLp.toLp (gradient φ) x) = _
    rw [hx]
  have hright : inner ℝ (u : E →₂[gibbsMeasure volume V] ℝ) (gibbsSobolevInclusion hV hprob v) =
      ∫ x, (u : E →₂[gibbsMeasure volume V] ℝ) x * φ x ∂gibbsMeasure volume V := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hφLp.coeFn_toLp] with x hx
    change inner ℝ _ (hφLp.toLp φ x) = _
    rw [hx, Real.inner_apply]
  rwa [hleft, hright] at he

/-- Actual gradient product rule for an inverse-density test. -/
theorem gradient_exp_potential_mul_test {V φ : E → ℝ}
    (hV : Differentiable ℝ V) (hφ : Differentiable ℝ φ) (x : E) :
    gradient (fun y => Real.exp (V y) * φ y) x =
      Real.exp (V x) • (gradient φ x + φ x • gradient V x) := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left, fderiv_fun_mul ((hV x).exp) (hφ x), fderiv_exp (hV x)]
  simp only [add_apply, smul_apply, smul_eq_mul, inner_add_left, inner_smul_left,
    inner_gradient_left]
  simp only [RCLike.conj_to_real]
  ring

/-- The genuine ordinary-volume distributional elliptic equation for every
actual operator eigenvector. Its only derivatives are the actual closed weak
gradient; no representative regularity is postulated. -/
theorem gibbsOperatorEigen_volume_test_equation {V φ : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    (∫ x, inner ℝ
      (gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u) x)
      (gradient φ x + φ x • gradient V x) ∂volume) =
      rate * (∫ x, (u : E →₂[gibbsMeasure volume V] ℝ) x * φ x ∂volume) := by
  let ψ (x : E) := Real.exp (V x) * φ x
  have hψ : ContDiff ℝ 2 ψ := hV.exp.mul hφ
  have hψc : HasCompactSupport ψ := by
    simpa only [ψ, Pi.mul_def] using hφc.mul_left (f := fun x => Real.exp (V x))
  have he := gibbsOperatorEigen_compact_test_equation hV hprob rate u hψ hψc
  have hleft : (∫ x, inner ℝ
      (gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u) x)
      (gradient ψ x) ∂gibbsMeasure volume V) =
      ∫ x, inner ℝ
        (gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u) x)
        (gradient φ x + φ x • gradient V x) ∂volume := by
    rw [← integral_exp_potential_mul_gibbs_eq_volume hV.continuous.measurable]
    apply integral_congr_ae
    filter_upwards with x
    rw [gradient_exp_potential_mul_test (hV.differentiable (by norm_num)) (hφ.differentiable
      (by norm_num)),
      inner_smul_right]
  have hright : (∫ x, (u : E →₂[gibbsMeasure volume V] ℝ) x * ψ x ∂gibbsMeasure volume V) =
      ∫ x, (u : E →₂[gibbsMeasure volume V] ℝ) x * φ x ∂volume := by
    rw [← integral_exp_potential_mul_gibbs_eq_volume hV.continuous.measurable]
    apply integral_congr_ae
    filter_upwards with x
    dsimp [ψ]
    ring
  rwa [hleft, hright] at he

/-- Actual Gibbs L² vector coordinates admit compact localization in actual
Lebesgue L², by the proved positive-density measure comparison. -/
theorem compact_cutoff_gibbsVector_coordinate_memLp_volume {V χ : E → ℝ}
    (hV : Continuous V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (w : E →₂[gibbsMeasure volume V] E) (i : Fin d) :
    MemLp (fun x => χ x * (w x) i) 2 volume := by
  have hi : MemLp (fun x => (w x) i) 2 (gibbsMeasure volume V) := by
    apply (Lp.memLp w).of_le_mul (c := 1) (by fun_prop)
    filter_upwards with x
    simpa only [one_mul] using (PiLp.norm_apply_le (w x) i)
  have hh := compact_cutoff_gibbsLp_memLp_volume hV hprob hχ hχc (hi.toLp (fun x => (w x) i))
  have hae := (gibbsMeasure_ae_eq_iff volume hV.measurable).mp hi.coeFn_toLp
  refine (memLp_congr_ae ?_).mp hh
  filter_upwards [hae] with x hx
  rw [hx]

/-- The lower-order elliptic right-hand side is genuinely locally L² for
every actual operator eigenvector, without any regularity hypothesis. -/
theorem gibbsOperatorEigen_local_rhs_memLp {V χ : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    MemLp (fun x => χ x *
      (inner ℝ (gradient V x)
        (gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u) x) -
          rate * (u : E →₂[gibbsMeasure volume V] ℝ) x)) 2 volume := by
  let G := gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u)
  have hGV : Continuous (gradient V) := continuous_gradient_of_c1 (hV.of_le (by norm_num))
  have hi (i : Fin d) : MemLp (fun x => (χ x * (gradient V x) i) * (G x) i) 2 volume := by
    have hc : Continuous (fun x => χ x * (gradient V x) i) :=
      hχ.mul ((EuclideanSpace.proj i : E →L[ℝ] ℝ).continuous.comp hGV)
    have hs : HasCompactSupport (fun x => χ x * (gradient V x) i) := by
      simpa only [Pi.mul_def] using hχc.mul_right (f' := fun x => (gradient V x) i)
    exact compact_cutoff_gibbsVector_coordinate_memLp_volume hV.continuous hprob hc hs G i
  have hsum : MemLp (fun x => ∑ i : Fin d, (χ x * (gradient V x) i) * (G x) i) 2 volume :=
    by
      convert memLp_finsetSum' Finset.univ (fun i _ => hi i) using 1
      funext x
      simp
  have hu := (compact_cutoff_gibbsLp_memLp_volume hV.continuous hprob hχ hχc
    (u : E →₂[gibbsMeasure volume V] ℝ)).const_mul rate
  convert hsum.sub hu using 1
  funext x
  dsimp only [G]
  simp only [Pi.sub_apply, PiLp.inner_apply, Real.inner_apply, mul_sub, Finset.mul_sum, mul_assoc]
  ring

end CutoffRigidity
