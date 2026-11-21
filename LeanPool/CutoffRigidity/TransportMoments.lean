/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.Transport
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Moment lower bounds for quadratic coupling costs

The estimates apply to actual square-integrable random variables. They supply
the moment lower bounds needed for the Gaussian distance formula used in the
paper's proof of the main Wasserstein estimate.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {π : Measure Ω}

/-- The real L² inner product is the integral of the product of representatives. -/
theorem real_inner_toLp {X Y : Ω → ℝ} (hX : MemLp X 2 π) (hY : MemLp Y 2 π) :
    inner ℝ (hX.toLp X) (hY.toLp Y) = ∫ ω, X ω * Y ω ∂π := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hX.coeFn_toLp, hY.coeFn_toLp] with ω hx hy
  simp [hx, hy, RCLike.inner_apply, mul_comm]

/-- The squared L² norm is the actual second moment. -/
theorem norm_toLp_sq {X : Ω → ℝ} (hX : MemLp X 2 π) :
    ‖hX.toLp X‖ ^ 2 = ∫ ω, X ω ^ 2 ∂π := by
  rw [← real_inner_self_eq_norm_sq, real_inner_toLp]
  simp only [pow_two]

/-- Cauchy--Schwarz for real random variables in second-moment form. -/
theorem integral_mul_le_second_moments {X Y : Ω → ℝ}
    (hX : MemLp X 2 π) (hY : MemLp Y 2 π) :
    (∫ ω, X ω * Y ω ∂π) ≤
      Real.sqrt (∫ ω, X ω ^ 2 ∂π) * Real.sqrt (∫ ω, Y ω ^ 2 ∂π) := by
  have h := real_inner_le_norm (hX.toLp X) (hY.toLp Y)
  rw [real_inner_toLp] at h
  simpa only [← norm_toLp_sq hX, ← norm_toLp_sq hY,
    Real.sqrt_sq (norm_nonneg _)] using h

/-- On a probability space the second moment dominates the squared mean. -/
theorem integral_sq_ge_sq_integral [IsProbabilityMeasure π] {X : Ω → ℝ}
    (hX : MemLp X 2 π) :
    (∫ ω, X ω ∂π) ^ 2 ≤ ∫ ω, X ω ^ 2 ∂π := by
  have h := variance_nonneg X π
  rw [variance_eq_sub hX] at h
  exact sub_nonneg.mp h

/-- Covariance is bounded above by the product of standard deviations. -/
theorem covariance_le_sqrt_variances [IsProbabilityMeasure π] {X Y : Ω → ℝ}
    (hX : MemLp X 2 π) (hY : MemLp Y 2 π) :
    covariance X Y π ≤ Real.sqrt (variance X π) * Real.sqrt (variance Y π) := by
  have hxc : MemLp (fun ω => X ω - ∫ a, X a ∂π) 2 π := hX.sub (memLp_const _)
  have hyc : MemLp (fun ω => Y ω - ∫ a, Y a ∂π) 2 π := hY.sub (memLp_const _)
  have h := integral_mul_le_second_moments hxc hyc
  rw [← variance_eq_integral hX.aemeasurable, ← variance_eq_integral hY.aemeasurable] at h
  exact h

/-- Any scalar coupling pays at least the squared difference of its means and
of its standard deviations. No independence assumption is used. -/
theorem integral_sq_sub_ge_mean_variance [IsProbabilityMeasure π] {X Y : Ω → ℝ}
    (hX : MemLp X 2 π) (hY : MemLp Y 2 π) :
    (∫ ω, X ω ∂π - ∫ ω, Y ω ∂π) ^ 2 +
        (Real.sqrt (variance X π) - Real.sqrt (variance Y π)) ^ 2 ≤
      ∫ ω, (X ω - Y ω) ^ 2 ∂π := by
  have hc := covariance_le_sqrt_variances hX hY
  have hv := variance_sub hX hY
  rw [variance_eq_sub (hX.sub hY)] at hv
  simp only [Pi.sub_apply, Pi.pow_apply] at hv
  rw [integral_sub (hX.integrable (by norm_num)) (hY.integrable (by norm_num))] at hv
  have hsX := Real.sq_sqrt (variance_nonneg X π)
  have hsY := Real.sq_sqrt (variance_nonneg Y π)
  nlinarith

/-- The same coupling estimate with explicit means and standard deviations. -/
theorem integral_sq_sub_ge_of_moments [IsProbabilityMeasure π] {X Y : Ω → ℝ}
    (hX : MemLp X 2 π) (hY : MemLp Y 2 π) {a b s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hmeanX : (∫ ω, X ω ∂π) = a) (hmeanY : (∫ ω, Y ω ∂π) = b)
    (hvarX : variance X π = s ^ 2) (hvarY : variance Y π = t ^ 2) :
    (a - b) ^ 2 + (s - t) ^ 2 ≤ ∫ ω, (X ω - Y ω) ^ 2 ∂π := by
  simpa only [hmeanX, hmeanY, hvarX, hvarY, Real.sqrt_sq hs, Real.sqrt_sq ht]
    using integral_sq_sub_ge_mean_variance hX hY

section EuclideanCouplings

variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Coordinate second moments give a lower bound for any actual Euclidean
coupling, and hence for their infimum. -/
theorem squaredWasserstein_ge_coordinate_moments (μ ν : Measure E)
    [IsProbabilityMeasure μ]
    (hμ : ∀ i : ι, MemLp (fun x : E => x i) 2 μ)
    (hν : ∀ i : ι, MemLp (fun y : E => y i) 2 ν)
    (a b s t : ι → ℝ) (hs : ∀ i, 0 ≤ s i) (ht : ∀ i, 0 ≤ t i)
    (hmμ : ∀ i, (∫ x : E, x i ∂μ) = a i)
    (hmν : ∀ i, (∫ y : E, y i ∂ν) = b i)
    (hvμ : ∀ i, variance (fun x : E => x i) μ = s i ^ 2)
    (hvν : ∀ i, variance (fun y : E => y i) ν = t i ^ 2) :
    ENNReal.ofReal (∑ i, ((a i - b i) ^ 2 + (s i - t i) ^ 2)) ≤
      squaredWasserstein μ ν := by
  unfold squaredWasserstein
  apply le_iInf
  intro γ
  have : IsProbabilityMeasure γ.val := γ.isProbabilityMeasure
  have hfst : MeasurePreserving Prod.fst γ.val μ := ⟨measurable_fst, γ.property.1⟩
  have hsnd : MeasurePreserving Prod.snd γ.val ν := ⟨measurable_snd, γ.property.2⟩
  have hX (i : ι) : MemLp (fun z : E × E => z.1 i) 2 γ.val :=
    (hμ i).comp_measurePreserving hfst
  have hY (i : ι) : MemLp (fun z : E × E => z.2 i) 2 γ.val :=
    (hν i).comp_measurePreserving hsnd
  have hint (i : ι) : Integrable (fun z : E × E => (z.1 i - z.2 i) ^ 2) γ.val :=
    ((hX i).sub (hY i)).integrable_sq
  have hcoord (i : ι) : (a i - b i) ^ 2 + (s i - t i) ^ 2 ≤
      ∫ z : E × E, (z.1 i - z.2 i) ^ 2 ∂γ.val := by
    apply integral_sq_sub_ge_of_moments (hX i) (hY i) (hs i) (ht i)
    · have h := integral_map (μ := γ.val) (φ := Prod.fst)
        (f := fun x : E => x i) measurable_fst.aemeasurable (by fun_prop)
      rw [γ.property.1] at h
      exact h.symm.trans (hmμ i)
    · have h := integral_map (μ := γ.val) (φ := Prod.snd)
        (f := fun x : E => x i) measurable_snd.aemeasurable (by fun_prop)
      rw [γ.property.2] at h
      exact h.symm.trans (hmν i)
    · have h := variance_map (μ := γ.val) (Y := Prod.fst)
        (X := fun x : E => x i) (by fun_prop) measurable_fst.aemeasurable
      rw [γ.property.1] at h
      exact h.symm.trans (hvμ i)
    · have h := variance_map (μ := γ.val) (Y := Prod.snd)
        (X := fun x : E => x i) (by fun_prop) measurable_snd.aemeasurable
      rw [γ.property.2] at h
      exact h.symm.trans (hvν i)
  have hreal : (∑ i, ((a i - b i) ^ 2 + (s i - t i) ^ 2)) ≤
      ∫ z : E × E, ‖z.1 - z.2‖ ^ 2 ∂γ.val := by
    calc
      _ ≤ ∑ i, ∫ z : E × E, (z.1 i - z.2 i) ^ 2 ∂γ.val :=
        Finset.sum_le_sum (fun i _ => hcoord i)
      _ = ∫ z : E × E, ∑ i, (z.1 i - z.2 i) ^ 2 ∂γ.val := by
        rw [integral_finsetSum _ (fun i _ => hint i)]
      _ = _ := by
        congr 1
        funext z
        exact (EuclideanSpace.real_norm_sq_eq (z.1 - z.2)).symm
  have hcost : Integrable (fun z : E × E => ‖z.1 - z.2‖ ^ 2) γ.val := by
    simp_rw [EuclideanSpace.real_norm_sq_eq]
    exact integrable_finsetSum _ (fun i _ => hint i)
  calc
    _ ≤ ENNReal.ofReal (∫ z : E × E, ‖z.1 - z.2‖ ^ 2 ∂γ.val) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ∫⁻ z : E × E, ENNReal.ofReal (‖z.1 - z.2‖ ^ 2) ∂γ.val :=
      ofReal_integral_eq_lintegral_ofReal hcost (Filter.Eventually.of_forall fun z => sq_nonneg _)
    _ = _ := by
      apply lintegral_congr
      intro z
      rw [edist_dist, dist_eq_norm, ENNReal.ofReal_pow (norm_nonneg _) 2]

end EuclideanCouplings

end CutoffRigidity
