/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.EigenfunctionLocalizedBochner

/-! # Genuine compact-test infinitesimal Gibbs stationarity

The identities below concern the actual differential Langevin generator and
actual exponential Gibbs density. Compact support discharges every analytic
integrability condition. In particular the Gibbs measure annihilates the
generator on C² compact tests.

This is infinitesimal invariance, not yet invariance of the constructed
transition kernel. The latter additionally needs a connection between the
stochastic transition kernel and its differential generator, together with a
uniqueness or generator-core argument. Neither is assumed in these theorems.
-/

public section

namespace CutoffRigidity

open MeasureTheory

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The differential generator has compact support whenever its test does. -/
theorem hasCompactSupport_langevinDifferentialOperator
    (V : E → ℝ) {g : E → ℝ} (hgc : HasCompactSupport g) :
    HasCompactSupport (langevinDifferentialOperator V g) := by
  have hd (i : Fin d) : HasCompactSupport (coordinateDerivative i g) :=
    hgc.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hdd (i : Fin d) : HasCompactSupport (coordinateDerivative i (coordinateDerivative i g)) :=
    (hd i).fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hLap : HasCompactSupport (euclideanLaplacian g) := by
    classical
    have hsum (s : Finset (Fin d)) : HasCompactSupport
        (fun x => ∑ i ∈ s, coordinateDerivative i (coordinateDerivative i g) x) := by
      induction s using Finset.induction with
      | empty => simp [HasCompactSupport]
      | @insert i s his ih =>
        have heq : (fun x : E => ∑ j ∈ insert i s, coordinateDerivative j (coordinateDerivative j
          g) x) =
            coordinateDerivative i (coordinateDerivative i g) +
              (fun x => ∑ j ∈ s, coordinateDerivative j (coordinateDerivative j g) x) := by
          funext x
          rw [Finset.sum_insert his]
          rfl
        rw [heq]
        exact (hdd i).add ih
    exact hsum Finset.univ
  have hG : HasCompactSupport (gradient g) :=
    (hgc.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ E).symm) (by simp)
  have hinner : HasCompactSupport (fun x => inner ℝ (gradient V x) (gradient g x)) := by
    apply hG.mono
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro hz
    apply hx
    rw [hz, inner_zero_right]
  exact hLap.sub hinner

/-- Compact C² tests have an integrable actual differential generator. -/
theorem integrable_langevinDifferentialOperator_compact
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    Integrable (langevinDifferentialOperator V g) (gibbsMeasure volume V) :=
  integrable_gibbs_of_continuous_hasCompactSupport hV.continuous
    (continuous_langevinDifferentialOperator hV hg)
    (hasCompactSupport_langevinDifferentialOperator V hgc)

/-- Dirichlet integration by parts with a compact differentiated test; the
multiplier need not have compact support, and all products are integrable. -/
theorem gibbs_energy_compact_differentiated_test
    {V f g : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    (∫ x, f x * langevinDifferentialOperator V g x ∂gibbsMeasure volume V) =
      -(∫ x, inner ℝ (gradient f x) (gradient g x) ∂gibbsMeasure volume V) := by
  have hD (q : E → ℝ) (hq : ContDiff ℝ 2 q) (i : Fin d) :
      ContDiff ℝ 1 (coordinateDerivative i q) := by
    apply contDiff_coordinateDerivative
    convert hq using 1
    norm_num
  have hDD (i : Fin d) : Continuous (coordinateDerivative i (coordinateDerivative i g)) := by
    have h : ContDiff ℝ 0 (coordinateDerivative i (coordinateDerivative i g)) := by
      apply contDiff_coordinateDerivative
      convert hD g hg i using 1
      norm_num
    exact h.continuous
  have hDc (i : Fin d) : HasCompactSupport (coordinateDerivative i g) :=
    hgc.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hDDc (i : Fin d) : HasCompactSupport (coordinateDerivative i (coordinateDerivative i g)) :=
    (hDc i).fderiv_apply ℝ (EuclideanSpace.single i 1)
  apply integral_mul_langevin_eq_neg_gradient_inner (hV.differentiable (by norm_num))
    (hf.differentiable (by norm_num)) hg
  · intro i
    change Integrable (fun x => f x * coordinateDerivative i g x) _
    apply integrable_gibbs_of_continuous_hasCompactSupport hV.continuous
      (hf.continuous.mul (hD g hg i).continuous)
    simpa only [Pi.mul_def] using (hDc i).mul_left (f := f)
  · intro i
    change Integrable (fun x => f x * coordinateDerivative i (coordinateDerivative i g) x) _
    apply integrable_gibbs_of_continuous_hasCompactSupport hV.continuous (hf.continuous.mul (hDD i))
    simpa only [Pi.mul_def] using (hDDc i).mul_left (f := f)
  · intro i
    change Integrable (fun x => coordinateDerivative i f x * coordinateDerivative i g x) _
    apply integrable_gibbs_of_continuous_hasCompactSupport hV.continuous
      ((hD f hf i).continuous.mul (hD g hg i).continuous)
    simpa only [Pi.mul_def] using (hDc i).mul_left (f := coordinateDerivative i f)
  · intro i
    change Integrable (fun x => f x * coordinateDerivative i V x * coordinateDerivative i g x) _
    apply integrable_gibbs_of_continuous_hasCompactSupport hV.continuous
      ((hf.continuous.mul (hD V hV i).continuous).mul (hD g hg i).continuous)
    simpa only [Pi.mul_def] using (hDc i).mul_left (f := fun x => f x * coordinateDerivative i V x)

/-- Genuine weak stationarity of Gibbs density on compact C² tests. -/
theorem integral_langevinDifferentialOperator_compact_eq_zero
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    (∫ x, langevinDifferentialOperator V g x ∂gibbsMeasure volume V) = 0 := by
  have h := gibbs_energy_compact_differentiated_test hV
    (contDiff_const (c := (1 : ℝ))) hg hgc
  simpa only [one_mul, gradient_fun_const, inner_zero_left, integral_zero, neg_zero] using h

/-- The actual compact-test differential generator is Gibbs symmetric. -/
theorem integral_langevinDifferentialOperator_compact_symmetric
    {V f g : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    (∫ x, f x * langevinDifferentialOperator V g x ∂gibbsMeasure volume V) =
      ∫ x, g x * langevinDifferentialOperator V f x ∂gibbsMeasure volume V := by
  rw [gibbs_energy_compact_differentiated_test hV hf hg hgc,
    gibbs_energy_compact_differentiated_test hV hg hf hfc]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => real_inner_comm _ _)

/-- The actual compact-test generator is dissipative in Gibbs L², as forced
by the derived Dirichlet identity rather than by an assumed stationary flow. -/
theorem integral_mul_langevinDifferentialOperator_compact_nonpos
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (∫ x, f x * langevinDifferentialOperator V f x ∂gibbsMeasure volume V) ≤ 0 := by
  rw [gibbs_energy_compact_differentiated_test hV hf hf hfc]
  apply neg_nonpos.mpr
  apply integral_nonneg
  intro x
  exact real_inner_self_nonneg

end CutoffRigidity
