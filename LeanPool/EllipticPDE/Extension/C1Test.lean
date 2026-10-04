/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Embedding.Convolution
public import LeanPool.EllipticPDE.Embedding.WeakGradient
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution


/-!
# Integration by parts against a `C¹` test function

`HasWeakGradOn` asks for the integration-by-parts identity against smooth test functions. The
extension operator needs it against a `C¹` one: a boundary chart of a `C¹` domain is `C¹`, so a
smooth test function pulled back through it is `C¹` and no better.

Mollification supplies the smooth test functions. The mollification of a `C¹` class of compact
support is smooth, its support sits in a closed thickening of the original, its partial
derivatives are the mollified partial derivatives, and both stay bounded by the suprema of the
originals while converging pointwise. Dominated convergence passes the identity.

## Main declarations

* `EllipticPdes.Extension.partialD_convolution_normed`: the partial derivative of a
  mollification is the mollification of the partial derivative.
* `EllipticPdes.Extension.norm_convolution_normed_le`: a mollification is bounded by the
  supremum of what it mollifies.
* `EllipticPdes.Extension.hasWeakGradOn_contDiffOne`: the identity of a weak gradient, against
  a `C¹` test function.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal Convolution Pointwise

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Embedding (HasWeakGradOn)
open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

local notation "Lsm" => ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)

/-- **Partial derivative of a mollification.** For `ψ` of class `C¹` with compact support,
`ρ ⋆ ψ` is differentiable and its partial derivatives are the mollified partial derivatives. -/
theorem partialD_convolution_normed (ρ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ)
    (k : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    partialD k (ρ.normed volume ⋆[Lsm, volume] ψ) x
      = (ρ.normed volume ⋆[Lsm, volume] (partialD k ψ)) x := by
  have hρc : Continuous (ρ.normed volume) :=
    (ρ.contDiff_normed : ContDiff ℝ (⊤ : ℕ∞) _).continuous
  have hρli : LocallyIntegrable (ρ.normed volume) volume := hρc.locallyIntegrable
  have hfd := hψcs.hasFDerivAt_convolution_right (L := Lsm) hρli hψ x
  rw [partialD, hfd.fderiv,
    convolution_precompR_apply Lsm hρli (hψcs.fderiv ℝ) (hψ.continuous_fderiv one_ne_zero) x
      (EuclideanSpace.single k (1 : ℝ))]
  rfl

/-- **Bound on a mollification by what it mollifies.** The normed bump is a probability
density, so the convolution is an average and inherits the bound. -/
theorem norm_convolution_normed_le (ρ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    {h : EuclideanSpace ℝ (Fin d) → ℝ} (hc : Continuous h) (hcs : HasCompactSupport h)
    {M : ℝ} (hM : ∀ y, ‖h y‖ ≤ M) (x : EuclideanSpace ℝ (Fin d)) :
    ‖(ρ.normed volume ⋆[Lsm, volume] h) x‖ ≤ M := by
  have hρc : Continuous (ρ.normed volume) :=
    (ρ.contDiff_normed : ContDiff ℝ (⊤ : ℕ∞) _).continuous
  have hρli : LocallyIntegrable (ρ.normed volume) volume := hρc.locallyIntegrable
  have hρint : Integrable (ρ.normed volume) volume := ρ.integrable_normed
  have hex := hcs.convolutionExists_right (L := Lsm) (f := ρ.normed volume) hρli hc x
  rw [convolution_def]
  calc ‖∫ t, (Lsm (ρ.normed volume t)) (h (x - t))‖
      ≤ ∫ t, ‖(Lsm (ρ.normed volume t)) (h (x - t))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, ρ.normed volume t * M := by
        refine integral_mono hex.norm (hρint.mul_const M) fun t => ?_
        simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs,
          abs_of_nonneg (ρ.nonneg_normed t)]
        exact mul_le_mul_of_nonneg_left (hM _) (ρ.nonneg_normed t)
    _ = M := by rw [integral_mul_const, ρ.integral_normed, one_mul]

/-- The partial derivatives of a `C¹` class of compact support are continuous with compact
support. -/
private theorem hasCompactSupport_partialD {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψcs : HasCompactSupport ψ) (j : Fin d) : HasCompactSupport (partialD j ψ) :=
  (hψcs.fderiv ℝ).comp_left (g := fun T : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ =>
    T (EuclideanSpace.single j (1 : ℝ))) (by simp)

private theorem continuous_partialD {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (j : Fin d) : Continuous (partialD j ψ) :=
  (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- **Integration by parts against a `C¹` test function.** A weak gradient on an open set
satisfies its defining identity against every `C¹` function of compact support inside the set,
and not only against the smooth ones the definition names. -/
theorem hasWeakGradOn_contDiffOne {B : Set (EuclideanSpace ℝ (Fin d))} (hBopen : IsOpen B)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u B volume) (hgi : ∀ k, IntegrableOn (g k) B volume)
    (hwg : HasWeakGradOn B u g)
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ B) (k : Fin d) :
    ∫ x in B, u x * partialD k ψ x = - ∫ x in B, g k x * ψ x := by
  classical
  obtain ⟨ε, hε, hsub⟩ := hψcs.isCompact.exists_cthickening_subset_open hBopen hψs
  have hψc : Continuous ψ := hψ.continuous
  have hdcs : HasCompactSupport (partialD k ψ) := hasCompactSupport_partialD hψcs k
  have hdc : Continuous (partialD k ψ) := continuous_partialD hψ k
  obtain ⟨M, hM⟩ := hψcs.exists_bound_of_continuous hψc
  obtain ⟨N, hN⟩ := hdcs.exists_bound_of_continuous hdc
  -- The mollifier family, with outer radius `ε / (n + 1)`.
  set ρ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := fun n =>
    { rIn := ε / (n + 1) / 2
      rOut := ε / (n + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := half_lt_self (by positivity) } with hρdef
  have hrOutle : ∀ n : ℕ, (ρ n).rOut ≤ ε := by
    intro n
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
    calc (ρ n).rOut = ε / ((n : ℝ) + 1) := rfl
      _ ≤ ε / 1 := by
          refine div_le_div_of_nonneg_left hε.le one_pos h1
      _ = ε := by ring
  have hrOut : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => ε * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ε
    refine h.congr fun n => ?_
    change ε * (1 / ((n : ℝ) + 1)) = ε / ((n : ℝ) + 1)
    ring
  set ψn : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun n => (ρ n).normed volume ⋆[Lsm, volume] ψ with hψndef
  have hψnsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψn n) := fun n =>
    (ρ n).hasCompactSupport_normed.contDiff_convolution_left (L := Lsm) (ρ n).contDiff_normed
      hψc.locallyIntegrable
  have hψncs : ∀ n, HasCompactSupport (ψn n) := fun n =>
    HasCompactSupport.convolution (L := Lsm) (ρ n).hasCompactSupport_normed hψcs
  -- The mollified test function is still supported inside `B`.
  have hψns : ∀ n, tsupport (ψn n) ⊆ B := by
    intro n
    have h1 : Function.support (ψn n)
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (ρ n).rOut + tsupport ψ := by
      refine (support_convolution_subset Lsm).trans (Set.add_subset_add ?_ ?_)
      · rw [(ρ n).support_normed_eq]; exact ball_subset_closedBall
      · exact subset_tsupport ψ
    have h2 : IsClosed
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (ρ n).rOut + tsupport ψ) :=
      ((isCompact_closedBall _ _).add hψcs.isCompact).isClosed
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := closure_minimal h1 h2 hx
    refine hsub (mem_cthickening_of_dist_le _ b _ _ hb ?_)
    have : dist (a + b) b = ‖a‖ := by
      rw [dist_eq_norm]; simp
    rw [this]
    exact le_trans (mem_closedBall_zero_iff.mp ha) (hrOutle n)
  -- Pointwise convergence of the mollifications and of their partial derivatives.
  have hconvψ : ∀ x, Tendsto (fun n => ψn n x) atTop (𝓝 (ψ x)) := fun x =>
    ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hrOut hψc x
  have hconvd : ∀ x, Tendsto (fun n => partialD k (ψn n) x) atTop (𝓝 (partialD k ψ x)) := by
    intro x
    have h := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) (φ := ρ)
      hrOut hdc x
    refine h.congr fun n => ?_
    exact (partialD_convolution_normed (ρ n) hψ hψcs k x).symm
  -- Uniform bounds, from the same suprema.
  have hboundψ : ∀ n x, ‖ψn n x‖ ≤ M := fun n x =>
    norm_convolution_normed_le (ρ n) hψc hψcs hM x
  have hboundd : ∀ n x, ‖partialD k (ψn n) x‖ ≤ N := by
    intro n x
    rw [partialD_convolution_normed (ρ n) hψ hψcs k x]
    exact norm_convolution_normed_le (ρ n) hdc hdcs hN x
  have hψnd : ∀ n, Continuous (partialD k (ψn n)) := fun n =>
    continuous_partialD ((hψnsmooth n).of_le (by exact_mod_cast le_top)) k
  -- The identity holds for every mollification.
  have hid : ∀ n, ∫ x in B, u x * partialD k (ψn n) x = - ∫ x in B, g k x * ψn n x := fun n =>
    hwg (ψn n) (hψnsmooth n) (hψncs n) (hψns n) k
  -- Both sides converge, by dominated convergence on `B`.
  have hL : Tendsto (fun n => ∫ x in B, u x * partialD k (ψn n) x) atTop
      (𝓝 (∫ x in B, u x * partialD k ψ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => N * ‖u x‖) ?_ ?_ ?_ ?_
    · exact fun n => hu.1.mul (hψnd n).aestronglyMeasurable
    · exact hu.norm.const_mul N
    · intro n
      filter_upwards with x
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hboundd n x) (norm_nonneg _)
    · filter_upwards with x using (hconvd x).const_mul (u x)
  have hR : Tendsto (fun n => ∫ x in B, g k x * ψn n x) atTop
      (𝓝 (∫ x in B, g k x * ψ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => M * ‖g k x‖) ?_ ?_ ?_ ?_
    · exact fun n => (hgi k).1.mul (hψnsmooth n).continuous.aestronglyMeasurable
    · exact (hgi k).norm.const_mul M
    · intro n
      filter_upwards with x
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hboundψ n x) (norm_nonneg _)
    · filter_upwards with x using (hconvψ x).const_mul (g k x)
  exact tendsto_nhds_unique hL (by simpa only [hid] using hR.neg)

end EllipticPdes.Extension
