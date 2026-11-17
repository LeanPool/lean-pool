/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Exp
public import LeanPool.KLS.FunctionalInequalities.Probability.Covariance.Basic
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Small quadratic tilts of a probability measure

For a probability measure `μ` on a normed additive group, the normalized tilts `e^{-δ‖x‖²/2} μ /
Z_δ`
converge to `μ` as `δ → 0⁺`, weakly and against integrable Banach-valued observables.
Moment and covariance corollaries retain their stated additional structure. This is the second
regular approximation step in Bizeul–Klartag–Lehec (arXiv:2610.05474v1, Section 2, p. 5); the
Gaussian smoothing step and the joint limit are separate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set

namespace FunctionalInequalities.Probability

/-- **Normalized small quadratic tilts converge**: for a probability measure `μ` and an integrable
`f`, `∫ f d(μ tilted by e^{-δ‖x‖²/2}) → ∫ f dμ` as `δ → 0⁺`. -/
theorem integral_quadraticTilt_tendsto {E F : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure E) [IsProbabilityMeasure μ] (f : E → F) (hf : Integrable f μ) :
    Tendsto
      (fun δ : ℝ => ∫ x, f x ∂(μ.tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, f x ∂μ)) := by
  let w : ℝ → E → ℝ := fun δ x => Real.exp (-(δ / 2) * ‖x‖ ^ 2)
  let Z : ℝ → ℝ := fun δ => ∫ x, w δ x ∂μ
  let I : ℝ → F := fun δ => ∫ x, w δ x • f x ∂μ
  have hw_cont (δ : ℝ) : Continuous (w δ) := by
    dsimp [w]
    fun_prop
  have hw_nonneg (δ : ℝ) (x : E) : 0 ≤ w δ x :=
    (Real.exp_pos _).le
  have hw_le (δ : ℝ) (hδ : 0 ≤ δ) (x : E) : w δ x ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (div_nonneg hδ (by norm_num))) (sq_nonneg _)
  have hw_lim (x : E) : Tendsto (fun δ : ℝ => w δ x) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hc : Continuous (fun δ : ℝ => w δ x) := by
      dsimp [w]
      fun_prop
    have ht : Tendsto (fun δ : ℝ => w δ x) (𝓝 (0 : ℝ)) (𝓝 (w 0 x)) :=
      hc.tendsto 0
    simpa [w] using ht.mono_left nhdsWithin_le_nhds
  have hZ : Tendsto Z (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (l := 𝓝[>] (0 : ℝ))
      (F := w) (f := fun _ : E => (1 : ℝ)) (fun _ : E => (1 : ℝ))
      (Filter.Eventually.of_forall fun δ => (hw_cont δ).aestronglyMeasurable) ?_
      (integrable_const 1) (Filter.Eventually.of_forall hw_lim)
    · simpa [Z] using h
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      change 0 < δ at hδ
      exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hw_nonneg δ x)]
        exact hw_le δ hδ.le x
  have hI : Tendsto I (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, f x ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (l := 𝓝[>] (0 : ℝ))
      (F := fun δ x => w δ x • f x) (f := f) (fun x => ‖f x‖)
    · exact Filter.Eventually.of_forall fun δ =>
        (hw_cont δ).aestronglyMeasurable.smul hf.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      change 0 < δ at hδ
      exact Filter.Eventually.of_forall fun x => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw_nonneg δ x)]
        simpa using mul_le_mul_of_nonneg_right (hw_le δ hδ.le x) (norm_nonneg (f x))
    · exact hf.norm
    · exact Filter.Eventually.of_forall fun x => by
        simpa using (hw_lim x).smul (tendsto_const_nhds (x := f x))
  have hnormalized : Tendsto (fun δ => (Z δ)⁻¹ • I δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, f x ∂μ)) := by
    simpa using (hZ.inv₀ (by norm_num : (1 : ℝ) ≠ 0)).smul hI
  have heq (δ : ℝ) :
      (∫ x, f x ∂(μ.tilted (fun x => -(δ / 2) * ‖x‖ ^ 2))) =
        (Z δ)⁻¹ • I δ := by
    rw [MeasureTheory.integral_tilted]
    change (∫ x, (w δ x / Z δ) • f x ∂μ) = (Z δ)⁻¹ • I δ
    simp_rw [div_eq_mul_inv, mul_comm (w δ _) ((Z δ)⁻¹), mul_smul]
    exact integral_smul (Z δ)⁻¹ (fun x => w δ x • f x)
  simpa only [heq] using hnormalized

section Laws

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section QuadraticTiltLaws

omit [NormedSpace ℝ E]
/-- The quadratic tilt of a probability measure is a probability measure for `δ ≥ 0`. -/
theorem isProbabilityMeasure_quadraticTilt (μ : Measure E) [IsProbabilityMeasure μ]
    (δ : ℝ) (hδ : 0 ≤ δ) :
    IsProbabilityMeasure (μ.tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)) := by
  apply MeasureTheory.isProbabilityMeasure_tilted
  refine (integrable_const (1 : ℝ)).mono' ?_ ?_
  · exact (show Continuous (fun x : E => Real.exp (-(δ / 2) * ‖x‖ ^ 2)) by
      fun_prop).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (div_nonneg hδ (by norm_num))) (sq_nonneg _))

/-- The normalized quadratic tilt `e^{-δ‖x‖²/2} μ / Z_δ` as a probability law. -/
def quadraticTiltLaw (μ : ProbabilityMeasure E) (δ : ℝ) (hδ : 0 ≤ δ) :
    ProbabilityMeasure E :=
  ⟨(μ : Measure E).tilted (fun x => -(δ / 2) * ‖x‖ ^ 2),
    isProbabilityMeasure_quadraticTilt (μ : Measure E) δ hδ⟩

/-- The quadratic tilts converge weakly to `μ` along any positive rate sequence `δ_j → 0`. -/
theorem quadraticTiltLaw_tendsto (μ : ProbabilityMeasure E) (δseq : ℕ → ℝ)
    (hδ : ∀ j, 0 < δseq j) (hlim : Tendsto δseq atTop (𝓝 0)) :
    Tendsto (fun j => quadraticTiltLaw μ (δseq j) (hδ j).le) atTop (𝓝 μ) := by
  have hwithin : Tendsto δseq atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Filter.Eventually.of_forall hδ⟩
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro g
  have hg : Integrable (fun x : E => g x) (μ : Measure E) :=
    (integrable_const ‖g‖).mono' g.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall g.norm_coe_le_norm)
  exact (integral_quadraticTilt_tendsto (μ : Measure E) (fun x => g x) hg).comp hwithin

end QuadraticTiltLaws

/-- Means converge when `μ` has a first moment. -/
theorem integral_id_quadraticTilt_tendsto (μ : Measure E) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : E => x) μ) :
    Tendsto (fun δ : ℝ => ∫ x : E, x ∂(μ.tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x : E, x ∂μ)) :=
  integral_quadraticTilt_tendsto μ (fun x => x) hint

omit [NormedSpace ℝ E] in
/-- Second moments converge when `μ` has a second moment. -/
theorem integral_norm_sq_quadraticTilt_tendsto (μ : Measure E) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : E => ‖x‖ ^ 2) μ) :
    Tendsto (fun δ : ℝ => ∫ x : E, ‖x‖ ^ 2
      ∂(μ.tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x : E, ‖x‖ ^ 2 ∂μ)) :=
  integral_quadraticTilt_tendsto μ (fun x => ‖x‖ ^ 2) hint

end Laws


section Covariance

open ProbabilityTheory
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
private theorem weight_le_one {δ : ℝ} (hδ : 0 ≤ δ) (x : E) :
    Real.exp (-(δ / 2) * ‖x‖ ^ 2) ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (div_nonneg hδ (by norm_num))) (sq_nonneg _)

section QuadraticTiltMoments

omit [CompleteSpace E]
private theorem weight_integrable (μ : ProbabilityMeasure E) {δ : ℝ} (hδ : 0 ≤ δ) :
    Integrable (fun x : E => Real.exp (-(δ / 2) * ‖x‖ ^ 2)) (μ : Measure E) := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact weight_le_one hδ x

/-- The quadratic tilt of a law with finite second moment has finite second moment. -/
theorem memLp_id_two_quadraticTilt (μ : ProbabilityMeasure E)
    (hμ2 : MemLp (id : E → E) 2 (μ : Measure E)) {δ : ℝ} (hδ : 0 ≤ δ) :
    MemLp (id : E → E) 2 ((μ : Measure E).tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)) := by
  have hi : Integrable (fun x : E => ‖x‖ ^ 2) (μ : Measure E) := by
    simpa only [id_eq] using (memLp_two_iff_integrable_sq_norm hμ2.aestronglyMeasurable).mp hμ2
  apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).mpr
  apply (integrable_tilted_iff (weight_integrable μ hδ) (fun x : E => ‖x‖ ^ 2)).mpr
  refine hi.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact
      (by fun_prop :
          Continuous
            (fun x : E => Real.exp (-(δ / 2) * ‖x‖ ^ 2) * ‖x‖ ^ 2)).aestronglyMeasurable
  · change ‖Real.exp (-(δ / 2) * ‖x‖ ^ 2) * ‖x‖ ^ 2‖ ≤ ‖x‖ ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    exact (mul_le_mul_of_nonneg_right (weight_le_one hδ x) (sq_nonneg _)).trans_eq (one_mul _)

end QuadraticTiltMoments

/--
`⟪Cov(μ_δ) u, v⟫ → ⟪Cov(μ) u, v⟫` as `δ → 0⁺` for the quadratic tilts `μ_δ = μ.tilted (−δ‖·‖²/2)`.
-/
theorem inner_covariance_quadraticTilt_tendsto (μ : ProbabilityMeasure E)
    (hμ2 : MemLp (id : E → E) 2 (μ : Measure E)) (u v : E) :
    Tendsto
      (fun δ : ℝ =>
        ⟪Covariance.operator ((μ : Measure E).tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)) u, v⟫)
      (𝓝[>] (0 : ℝ)) (𝓝 ⟪Covariance.operator (μ : Measure E) u, v⟫) := by
  let X : E → ℝ := fun x => ⟪u, x⟫
  let Y : E → ℝ := fun x => ⟪v, x⟫
  have hX : MemLp X 2 (μ : Measure E) := by
    simpa only [X, id_eq] using hμ2.const_inner (𝕜 := ℝ) u
  have hY : MemLp Y 2 (μ : Measure E) := by
    simpa only [Y, id_eq] using hμ2.const_inner (𝕜 := ℝ) v
  have hp :=
    Probability.integral_quadraticTilt_tendsto (μ : Measure E) (X * Y) (hX.integrable_mul hY)
  have hx :=
    Probability.integral_quadraticTilt_tendsto (μ : Measure E) X (hX.integrable one_le_two)
  have hy :=
    Probability.integral_quadraticTilt_tendsto (μ : Measure E) Y (hY.integrable one_le_two)
  have hlim := hp.sub (hx.mul hy)
  have hmean :
    ⟪Covariance.operator (μ : Measure E) u, v⟫ =
      (∫ x, (X * Y) x ∂(μ : Measure E)) -
        (∫ x, X x ∂(μ : Measure E)) * ∫ x, Y x ∂(μ : Measure E) := by
    rw [Covariance.operator_inner, covarianceBilin_apply_eq_cov hμ2, covariance_eq_sub hX hY]
  rw [hmean]
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hd : 0 ≤ δ := (show 0 < δ from hδ).le
  let _ := Probability.isProbabilityMeasure_quadraticTilt (μ : Measure E) δ hd
  have hδ2 := memLp_id_two_quadraticTilt μ hμ2 hd
  have hδX : MemLp X 2 ((μ : Measure E).tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)) := by
    simpa only [X, id_eq] using hδ2.const_inner (𝕜 := ℝ) u
  have hδY : MemLp Y 2 ((μ : Measure E).tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)) := by
    simpa only [Y, id_eq] using hδ2.const_inner (𝕜 := ℝ) v
  rw [Covariance.operator_inner, covarianceBilin_apply_eq_cov hδ2, covariance_eq_sub hδX hδY]

/--
**Covariance of the quadratic tilt converges** in operator norm as `δ → 0⁺` (BKL Section 2, p. 5).
-/
theorem covariance_quadraticTilt_tendsto (μ : ProbabilityMeasure E)
    (hμ2 : MemLp (id : E → E) 2 (μ : Measure E)) :
    Tendsto
      (fun δ : ℝ => Covariance.operator ((μ : Measure E).tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)))
      (𝓝[>] (0 : ℝ)) (𝓝 (Covariance.operator (μ : Measure E))) := by
  let A : ℝ → E →L[ℝ] E := fun δ =>
    Covariance.operator ((μ : Measure E).tilted (fun x => -(δ / 2) * ‖x‖ ^ 2))
  have h0 : A 0 = Covariance.operator (μ : Measure E) := by
    dsimp only [A]
    have hw : (fun x : E => -((0 : ℝ) / 2) * ‖x‖ ^ 2) = 0 := by funext x; simp
    rw [hw, tilted_zero]
  have hscalar (u v : E) : ContinuousWithinAt (fun δ => ⟪A δ u, v⟫) (Set.Ioi (0 : ℝ)) 0 := by
    change Tendsto (fun δ => ⟪A δ u, v⟫) (𝓝[>] (0 : ℝ)) (𝓝 ⟪A 0 u, v⟫)
    rw [h0]
    exact inner_covariance_quadraticTilt_tendsto μ hμ2 u v
  have hA : ContinuousWithinAt A (Set.Ioi (0 : ℝ)) 0 := by
    apply continuousWithinAt_clm_apply.mpr
    intro u
    let b := stdOrthonormalBasis ℝ E
    rw [b.toBasis.equivFunL.toHomeomorph.isInducing.continuousWithinAt_iff]
    apply continuousWithinAt_pi.mpr
    intro i
    change ContinuousWithinAt (fun δ => b.toBasis.equivFun (A δ u) i) (Set.Ioi (0 : ℝ)) 0
    simpa only [Module.Basis.equivFun_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply, real_inner_comm] using hscalar u (b i)
  change Tendsto A (𝓝[>] (0 : ℝ)) (𝓝 _)
  change Tendsto A (𝓝[>] (0 : ℝ)) (𝓝 (A 0)) at hA
  rw [h0] at hA
  exact hA

end Covariance

end FunctionalInequalities.Probability
