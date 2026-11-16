/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.SmoothGradient.Basic
public import LeanPool.KLS.FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.Kernel

/-!
# Weighted smooth approximation of locally Lipschitz tests

Source: Blueprint Appendix A, `lem:covariance-test-core-density`, first statement and proof.
Read `exists_smooth_weighted_L2` for the main contract, then the two preceding
intermediate statements for the cutoff / mollification / diagonal proof order. The final theorem
is the bounded L1 variant, preserving an arbitrary closed interval and the Lipschitz constant.
All four statements are proved; no proof placeholder remains in this module.

The space is finite-dimensional real Hilbert, including dimension zero. `m` is an additive Haar
measure: in finite dimension it is a Lebesgue reference measure, with arbitrary positive
normalization. The probability law `ν` is absolutely continuous with respect to `m`.
No log-concavity, density lower bound, translated-density estimate or second moment is required.
`B` is any continuous linear endomorphism, including zero or singular maps. Only `B ∘ gradient g`
must be square-integrable; integrability of the full gradient is not imposed in the main result.

`gradient` is Mathlib's canonical Hilbert gradient, zero at nondifferentiability points.
Rademacher's theorem (`LipschitzWith.ae_differentiableAt`, extended here to locally Lipschitz
functions through compact exhaustion and McShane extension) makes it meaningful `m`-almost
everywhere, hence `ν`-almost everywhere. Convergence is expressed by extended `eLpNorm` of
differences, with membership conditions explicit.

## Proof architecture

* A fixed smooth bump `bump`, rescaled to `scaled R`, provides both the cutoffs `scaled R` (one on
  the ball of radius `R`, zero outside radius `2 * R`) and the normalized mollifiers `kernel m R`
  (supported in radius `2 * R`, total mass one for the actual reference measure `m`).
* `mollify m R g = g ⋆ kernel m R` is smooth, preserves the global Lipschitz constant, preserves
  bounds and compact support, and is uniformly `2 K R`-close to `g`.
* At every differentiability point `x` of `g`, `fderiv (mollify m R g) x → fderiv g x` as `R → 0`.
  The argument compares the convolution derivative with the affine model `g x + L (· - x)`, using
  `integral_affine_smul_fderiv_kernel` and the scale-free derivative mass `kernelDerivativeMass m`
  of the kernel.
  No weak derivative or Lebesgue differentiation argument is needed.
* Dominated convergence in `L^p(ν)` (`tendsto_eLpNorm_zero_of_dominated`) transfers pointwise
  convergence to the weighted norms; the cutoff step uses the `L²` data `g` and `B ∘ gradient g`
  as dominating functions, and the diagonal selection in the main theorem combines both steps.

These statements do not identify local slope with gradient, compare Poincaré constants,
establish a closed gradient operator, or prove KLS.


The implementation is organized by responsibility: Basic, Measurable, Kernel, Approximation.
Import the earliest layer containing the required interface.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff Convolution ENNReal

namespace FunctionalInequalities.Energy.Euclidean.LipschitzApproximation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Main

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  (ν : ProbabilityMeasure E) (m : Measure E) [Measure.IsAddHaarMeasure m]

/-- Step 1 (cutoff): approximate in the weighted graph norm by globally Lipschitz tests
with compact support. Suggested witnesses are smooth cutoffs times g; their Lipschitz constants
may grow with j. This conclusion does not assert smoothness of the approximants. -/
theorem exists_compactSupport_weighted_L2 (hν : (ν : Measure E) ≪ m) (B : E →L[ℝ] E) (g : E → ℝ)
    (hg : LocallyLipschitz g) (hg_L2 : MemLp g 2 (ν : Measure E))
    (hBg_L2 : MemLp (fun x ↦ B (gradient g x)) 2 (ν : Measure E)) :
    ∃ gSeq : ℕ → E → ℝ,
      (∀ j,
          HasCompactSupport (gSeq j) ∧
            (∃ K : NNReal, LipschitzWith K (gSeq j)) ∧
              MemLp (gSeq j) 2 (ν : Measure E) ∧
                MemLp (fun x ↦ B (gradient (gSeq j) x)) 2 (ν : Measure E)) ∧
        Tendsto (fun j ↦ eLpNorm (fun x ↦ gSeq j x - g x) 2 (ν : Measure E)) atTop (𝓝 0) ∧
          Tendsto
            (fun j ↦
              eLpNorm (fun x ↦ B (gradient (gSeq j) x) - B (gradient g x)) 2 (ν : Measure E))
            atTop (𝓝 0) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_fderiv_bump (E := E)
  obtain ⟨Rs, hRs⟩ : ∃ Rs : ℕ → ℝ, ∀ j, Rs j = (j : ℝ) + 1 := ⟨_, fun j => rfl⟩
  have hRpos : ∀ j, 0 < Rs j := fun j => by rw [hRs]; positivity
  have hR1 : ∀ j, 1 ≤ Rs j := fun j => by
    rw [hRs]
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hout : ∀ j (x : E), x ∉ Metric.closedBall (0 : E) (2 * Rs j) → scaled (Rs j) x = 0 := by
    intro j x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    exact scaled_eq_zero (hRpos j) (le_of_lt (not_le.mp hx))
  choose K hK using fun j =>
    lipschitzOnWith_of_locallyLipschitz_of_isCompact hg
      (isCompact_closedBall (0 : E) (2 * Rs j))
  choose C hC using fun j =>
    (isCompact_closedBall (0 : E) (2 * Rs j)).exists_bound_of_continuousOn
      hg.continuous.continuousOn
  have hC' : ∀ j (x : E), x ∈ Metric.closedBall (0 : E) (2 * Rs j) → |g x| ≤ max (C j) 0 := by
    intro j x hx
    have := hC j x hx
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hχlip : ∀ j, LipschitzWith ((Rs j)⁻¹ * M).toNNReal (scaled (E := E) (Rs j)) := fun j =>
    lipschitzWith_scaled (hRpos j) hM0 hM
  have hgrad_bound : ∀ j (x : E), ‖gradient (scaled (E := E) (Rs j)) x‖ ≤ M := fun j x => by
    rw [norm_gradient_eq_norm_fderiv]
    calc
      ‖fderiv ℝ (scaled (Rs j)) x‖ ≤ (Rs j)⁻¹ * M := norm_fderiv_scaled_le (hRpos j) hM x
      _ ≤ 1 * M := by gcongr; exact inv_le_one_of_one_le₀ (hR1 j)
      _ = M := one_mul M
  have hgrad_zero : ∀ j (x : E), ‖x‖ < Rs j → gradient (scaled (E := E) (Rs j)) x = 0 :=
    fun j x hx => by
    change (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (scaled (Rs j)) x) = 0
    rw [fderiv_scaled_eq_zero (hRpos j) hx, map_zero]
  have hprod :
    ∀ j,
      LipschitzWith (((Rs j)⁻¹ * M) * max (C j) 0 + K j).toNNReal
        (fun x => scaled (Rs j) x * g x) := by
    intro j
    have hRj := hRpos j
    have key :
      ∀ x y,
        x ∈ Metric.closedBall (0 : E) (2 * Rs j) →
          dist (scaled (Rs j) x * g x) (scaled (Rs j) y * g y) ≤
            (((Rs j)⁻¹ * M) * max (C j) 0 + K j) * dist x y := by
      intro x y hx
      have e :
        scaled (Rs j) x * g x - scaled (Rs j) y * g y =
          (scaled (Rs j) x - scaled (Rs j) y) * g x + scaled (Rs j) y * (g x - g y) := by
        ring
      rw [Real.dist_eq, e]
      have h1 :
        |(scaled (Rs j) x - scaled (Rs j) y) * g x| ≤ ((Rs j)⁻¹ * M) * max (C j) 0 * dist x y := by
        rw [abs_mul]
        calc
          |scaled (Rs j) x - scaled (Rs j) y| * |g x| ≤
              ((Rs j)⁻¹ * M * dist x y) * max (C j) 0 := by
            gcongr
            · rw [← Real.dist_eq]
              have := (hχlip j).dist_le_mul x y
              rwa [Real.coe_toNNReal _ (by positivity)] at this
            · exact hC' j x hx
          _ = ((Rs j)⁻¹ * M) * max (C j) 0 * dist x y := by ring
      have h2 : |scaled (Rs j) y * (g x - g y)| ≤ K j * dist x y := by
        by_cases hy : y ∈ Metric.closedBall (0 : E) (2 * Rs j)
        · rw [abs_mul, abs_of_nonneg (scaled_nonneg _ _)]
          calc
            scaled (Rs j) y * |g x - g y| ≤ 1 * |g x - g y| := by
              gcongr
              exact scaled_le_one _ _
            _ = dist (g x) (g y) := by rw [one_mul, Real.dist_eq]
            _ ≤ K j * dist x y := (hK j).dist_le_mul x hx y hy
        · rw [hout j y hy, zero_mul, abs_zero]
          positivity
      calc
        |(scaled (Rs j) x - scaled (Rs j) y) * g x + scaled (Rs j) y * (g x - g y)| ≤
            |(scaled (Rs j) x - scaled (Rs j) y) * g x| + |scaled (Rs j) y * (g x - g y)| :=
          abs_add_le _ _
        _ ≤ ((Rs j)⁻¹ * M) * max (C j) 0 * dist x y + K j * dist x y := add_le_add h1 h2
        _ = (((Rs j)⁻¹ * M) * max (C j) 0 + K j) * dist x y := by ring
    refine LipschitzWith.of_dist_le' fun x y => ?_
    by_cases hx : x ∈ Metric.closedBall (0 : E) (2 * Rs j)
    · exact key x y hx
    by_cases hy : y ∈ Metric.closedBall (0 : E) (2 * Rs j)
    · rw [dist_comm, dist_comm x y]
      exact key y x hy
    · rw [hout j x hx, hout j y hy, zero_mul, zero_mul, dist_self]
      positivity
  refine ⟨fun j x => scaled (Rs j) x * g x, fun j => ⟨?_, ⟨_, hprod j⟩, ?_, ?_⟩, ?_, ?_⟩
  · exact
      HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * Rs j)) fun x hx => by
        beta_reduce
        rw [hout j x hx, zero_mul]
  · refine
      MemLp.of_bound ((continuous_scaled _).mul hg.continuous).aestronglyMeasurable
        (max (C j) 0) (ae_of_all _ fun x => ?_)
    beta_reduce
    by_cases hx : x ∈ Metric.closedBall (0 : E) (2 * Rs j)
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (scaled_nonneg _ _)]
      calc
        scaled (Rs j) x * |g x| ≤ 1 * max (C j) 0 := by
          gcongr
          · exact scaled_le_one _ _
          · exact hC' j x hx
        _ = max (C j) 0 := one_mul _
    · rw [hout j x hx, zero_mul, norm_zero]
      exact le_max_right _ _
  · have hRj := hRpos j
    refine
      MemLp.of_bound (B.continuous.measurable.comp (measurable_gradient _)).aestronglyMeasurable
        (‖B‖ * (((Rs j)⁻¹ * M) * max (C j) 0 + K j)) (ae_of_all _ fun x => ?_)
    beta_reduce
    calc
      ‖B (gradient (fun x => scaled (Rs j) x * g x) x)‖ ≤
          ‖B‖ * ‖gradient (fun x => scaled (Rs j) x * g x) x‖ :=
        B.le_opNorm _
      _ ≤ ‖B‖ * (((Rs j)⁻¹ * M) * max (C j) 0 + K j) := by
        gcongr
        have := norm_gradient_le_of_lipschitz (hprod j) x
        rwa [Real.coe_toNNReal _ (by positivity)] at this
  · refine
      tendsto_eLpNorm_zero_of_dominated (ν : Measure E) (by norm_num) (by norm_num)
        (fun j =>
          (((continuous_scaled _).mul hg.continuous).sub hg.continuous).aestronglyMeasurable)
        (bound := fun x => ‖g x‖) hg_L2.norm (fun j => ae_of_all _ fun x => ?_)
        (ae_of_all _ fun x => ?_)
    · beta_reduce
      have e : scaled (Rs j) x * g x - g x = (scaled (Rs j) x - 1) * g x := by ring
      rw [e, norm_mul]
      calc
        ‖scaled (Rs j) x - 1‖ * ‖g x‖ ≤ 1 * ‖g x‖ := by
          gcongr
          rw [Real.norm_eq_abs, abs_le]
          constructor <;> linarith [scaled_nonneg (Rs j) x, scaled_le_one (Rs j) x]
        _ = ‖g x‖ := one_mul _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with j hj
      have hxR : ‖x‖ ≤ Rs j := by
        rw [hRs j]
        calc
          ‖x‖ ≤ ⌈‖x‖⌉₊ := Nat.le_ceil _
          _ ≤ (j : ℝ) := by exact_mod_cast hj
          _ ≤ j + 1 := by linarith
      rw [scaled_eq_one (hRpos j) hxR, one_mul, sub_self]
  · have hdiff := hν.ae_le (ae_differentiableAt_of_locallyLipschitz hg m)
    refine
      tendsto_eLpNorm_zero_of_dominated (ν : Measure E) (by norm_num) (by norm_num)
        (fun j =>
          ((B.continuous.measurable.comp (measurable_gradient _)).aestronglyMeasurable).sub
            (B.continuous.measurable.comp (measurable_gradient _)).aestronglyMeasurable)
        (bound := fun x => ‖B (gradient g x)‖ + ‖B‖ * M * ‖g x‖)
        (hBg_L2.norm.add (hg_L2.norm.const_mul _)) (fun j => ?_) ?_
    · filter_upwards [hdiff] with x hx
      rw [gradient_scaled_mul hx, map_add, map_smul, map_smul]
      have e :
        scaled (Rs j) x • B (gradient g x) + g x • B (gradient (scaled (Rs j)) x) -
            B (gradient g x) =
          (scaled (Rs j) x - 1) • B (gradient g x) + g x • B (gradient (scaled (Rs j)) x) := by
        rw [sub_smul, one_smul]
        abel
      rw [e]
      calc
        ‖(scaled (Rs j) x - 1) • B (gradient g x) + g x • B (gradient (scaled (Rs j)) x)‖ ≤
            ‖(scaled (Rs j) x - 1) • B (gradient g x)‖ +
              ‖g x • B (gradient (scaled (Rs j)) x)‖ :=
          norm_add_le _ _
        _ ≤ 1 * ‖B (gradient g x)‖ + ‖g x‖ * (‖B‖ * M) := by
          rw [norm_smul, norm_smul]
          gcongr
          · rw [Real.norm_eq_abs, abs_le]
            constructor <;> linarith [scaled_nonneg (Rs j) x, scaled_le_one (Rs j) x]
          · calc
              ‖B (gradient (scaled (Rs j)) x)‖ ≤ ‖B‖ * ‖gradient (scaled (Rs j)) x‖ :=
                B.le_opNorm _
              _ ≤ ‖B‖ * M := by gcongr; exact hgrad_bound j x
        _ = ‖B (gradient g x)‖ + ‖B‖ * M * ‖g x‖ := by ring
    · filter_upwards [hdiff] with x hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with j hj
      have hxR : ‖x‖ < Rs j := by
        rw [hRs j]
        calc
          ‖x‖ ≤ ⌈‖x‖⌉₊ := Nat.le_ceil _
          _ ≤ (j : ℝ) := by exact_mod_cast hj
          _ < j + 1 := by linarith
      rw [gradient_scaled_mul hx, scaled_eq_one (hRpos j) hxR.le, hgrad_zero j x hxR, one_smul,
        smul_zero, add_zero, sub_self]

/-- Step 2 (mollification): smooth a compactly supported globally Lipschitz test.
The original global Lipschitz constant is retained, and the *full* gradient converges in L2.
Its source and approximant membership is part of the conclusion, not an extra hypothesis. -/
theorem exists_smooth_compactSupport_L2
    (hν : (ν : Measure E) ≪ m) (g : E → ℝ) (K : NNReal)
    (hg : LipschitzWith K g) (hcompact : HasCompactSupport g) :
    MemLp g 2 (ν : Measure E) ∧ MemLp (gradient g) 2 (ν : Measure E) ∧
      ∃ gSeq : ℕ → E → ℝ,
        (∀ j, ContDiff ℝ ∞ (gSeq j) ∧ HasCompactSupport (gSeq j) ∧
          LipschitzWith K (gSeq j) ∧ MemLp (gSeq j) 2 (ν : Measure E) ∧
          MemLp (gradient (gSeq j)) 2 (ν : Measure E)) ∧
        Tendsto (fun j ↦ eLpNorm (fun x ↦ gSeq j x - g x) 2 (ν : Measure E))
          atTop (𝓝 0) ∧
        Tendsto (fun j ↦ eLpNorm (fun x ↦ gradient (gSeq j) x - gradient g x)
          2 (ν : Measure E)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hcompact
  have hgL2 : MemLp g 2 (ν : Measure E) :=
    MemLp.of_bound hg.continuous.aestronglyMeasurable C (ae_of_all _ hC)
  have hgradL2 : MemLp (gradient g) 2 (ν : Measure E) :=
    MemLp.of_bound (aestronglyMeasurable_gradient g _) K
      (ae_of_all _ (norm_gradient_le_of_lipschitz hg))
  refine ⟨hgL2, hgradL2, fun j => mollify m (radius j) g, fun j => ?_, ?_, ?_⟩
  · have hR := radius_pos j
    refine ⟨contDiff_mollify m hR hg.continuous, hasCompactSupport_mollify m hR hcompact,
      lipschitzWith_mollify m hR hg, ?_, ?_⟩
    · refine MemLp.of_bound (continuous_mollify m hR hg.continuous).aestronglyMeasurable C
        (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs]
      exact abs_mollify_le m hR hg.continuous (fun x => by rw [← Real.norm_eq_abs]; exact hC x) x
    · exact MemLp.of_bound (aestronglyMeasurable_gradient _ _) K
        (ae_of_all _ (norm_gradient_le_of_lipschitz (lipschitzWith_mollify m hR hg)))
  · have hbound : ∀ j, eLpNorm (fun x => mollify m (radius j) g x - g x) 2 (ν : Measure E) ≤
        ENNReal.ofReal (K * (2 * radius j)) := by
      intro j
      have := eLpNorm_le_of_ae_bound (μ := (ν : Measure E)) (p := 2)
        (f := fun x => mollify m (radius j) g x - g x) ((continuous_mollify m (radius_pos j) hg.continuous).sub
          hg.continuous).aestronglyMeasurable
        (ae_of_all _ (norm_mollify_sub_le m (radius_pos j) hg))
      simpa [measure_univ] using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ => zero_le) hbound
    have h : Tendsto (fun j => (K : ℝ) * (2 * radius j)) atTop (𝓝 0) := by
      simpa using (tendsto_radius.const_mul 2).const_mul (K : ℝ)
    simpa using ENNReal.tendsto_ofReal h
  · refine tendsto_eLpNorm_zero_of_dominated (ν : Measure E) (by norm_num) (by norm_num)
      (fun j => (aestronglyMeasurable_gradient _ _).sub (aestronglyMeasurable_gradient _ _))
      (bound := fun _ => (K : ℝ) + K) (memLp_const _) (fun j => ae_of_all _ fun x => ?_) ?_
    · calc ‖gradient (mollify m (radius j) g) x - gradient g x‖
          ≤ ‖gradient (mollify m (radius j) g) x‖ + ‖gradient g x‖ := norm_sub_le _ _
        _ ≤ K + K := add_le_add
          (norm_gradient_le_of_lipschitz (lipschitzWith_mollify m (radius_pos j) hg) x)
          (norm_gradient_le_of_lipschitz hg x)
    · filter_upwards [hν.ae_le (hg.ae_differentiableAt (μ := m))] with x hx
      have := (tendsto_gradient_mollify m hg.continuous hx radius_pos tendsto_radius).sub_const
        (gradient g x)
      simpa using this

/-- Main L2 statement of `lem:covariance-test-core-density`.
Choose compactly supported smooth approximants with simultaneous value and B-gradient convergence.
For fixed B, continuity transports step 2 to the weighted norm; a diagonal choice combines steps
1 and 2. This statement has no hypothesis asserting either intermediate approximation theorem. -/
theorem exists_smooth_weighted_L2
    (hν : (ν : Measure E) ≪ m) (B : E →L[ℝ] E) (g : E → ℝ)
    (hg : LocallyLipschitz g) (hg_L2 : MemLp g 2 (ν : Measure E))
    (hBg_L2 : MemLp (fun x ↦ B (gradient g x)) 2 (ν : Measure E)) :
    ∃ gSeq : ℕ → E → ℝ,
      (∀ j, ContDiff ℝ ∞ (gSeq j) ∧ HasCompactSupport (gSeq j) ∧
        MemLp (gSeq j) 2 (ν : Measure E) ∧
        MemLp (fun x ↦ B (gradient (gSeq j) x)) 2 (ν : Measure E)) ∧
      Tendsto (fun j ↦ eLpNorm (fun x ↦ gSeq j x - g x) 2 (ν : Measure E))
        atTop (𝓝 0) ∧
      Tendsto (fun j ↦ eLpNorm
        (fun x ↦ B (gradient (gSeq j) x) - B (gradient g x)) 2 (ν : Measure E))
        atTop (𝓝 0) := by
  obtain ⟨u, hu, hu1, hu2⟩ :=
    exists_compactSupport_weighted_L2 ν m hν B g hg hg_L2 hBg_L2
  choose K hK using fun j => (hu j).2.1
  choose v hv hv1 hv2 using fun j =>
    (exists_smooth_compactSupport_L2 ν m hν (u j) (K j) (hK j) (hu j).1).2.2
  have hpick : ∀ j, ∃ k,
      eLpNorm (fun x => v j k x - u j x) 2 (ν : Measure E) ≤ ENNReal.ofReal (radius j) ∧
      eLpNorm (fun x => gradient (v j k) x - gradient (u j) x) 2 (ν : Measure E) ≤
        ENNReal.ofReal (radius j) := by
    intro j
    have hε : (0 : ℝ≥0∞) < ENNReal.ofReal (radius j) := ENNReal.ofReal_pos.mpr (radius_pos j)
    exact ((ENNReal.tendsto_nhds_zero.mp (hv1 j) _ hε).and
      (ENNReal.tendsto_nhds_zero.mp (hv2 j) _ hε)).exists
  choose k hk1 hk2 using hpick
  have hmB : ∀ f : E → ℝ, AEStronglyMeasurable (fun x => B (gradient f x)) (ν : Measure E) :=
    fun f => (B.continuous.measurable.comp (measurable_gradient _)).aestronglyMeasurable
  refine ⟨fun j => v j (k j), fun j => ⟨(hv j (k j)).1, (hv j (k j)).2.1, (hv j (k j)).2.2.2.1, ?_⟩,
    ?_, ?_⟩
  · refine MemLp.of_le ((hv j (k j)).2.2.2.2.norm.const_mul ‖B‖) (hmB _) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact B.le_opNorm _
  · have hle : ∀ j, eLpNorm (fun x => v j (k j) x - g x) 2 (ν : Measure E) ≤
        ENNReal.ofReal (radius j) + eLpNorm (fun x => u j x - g x) 2 (ν : Measure E) := by
      intro j
      calc eLpNorm (fun x => v j (k j) x - g x) 2 (ν : Measure E)
          = eLpNorm ((fun x => v j (k j) x - u j x) + fun x => u j x - g x) 2 (ν : Measure E) := by
            congr 1
            funext x
            simp
        _ ≤ eLpNorm (fun x => v j (k j) x - u j x) 2 (ν : Measure E) +
            eLpNorm (fun x => u j x - g x) 2 (ν : Measure E) :=
            eLpNorm_add_le one_le_two
        _ ≤ ENNReal.ofReal (radius j) + eLpNorm (fun x => u j x - g x) 2 (ν : Measure E) := by
            gcongr
            exact hk1 j
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le) hle
    have h1 : Tendsto (fun j => ENNReal.ofReal (radius j)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal tendsto_radius
    simpa using h1.add hu1
  · have hle : ∀ j, eLpNorm (fun x => B (gradient (v j (k j)) x) - B (gradient g x)) 2
        (ν : Measure E) ≤
        ‖B‖ₑ * ENNReal.ofReal (radius j) +
          eLpNorm (fun x => B (gradient (u j) x) - B (gradient g x)) 2 (ν : Measure E) := by
      intro j
      calc eLpNorm (fun x => B (gradient (v j (k j)) x) - B (gradient g x)) 2 (ν : Measure E)
          = eLpNorm ((fun x => B (gradient (v j (k j)) x) - B (gradient (u j) x)) +
              fun x => B (gradient (u j) x) - B (gradient g x)) 2 (ν : Measure E) := by
            congr 1
            funext x
            simp
        _ ≤ eLpNorm (fun x => B (gradient (v j (k j)) x) - B (gradient (u j) x)) 2 (ν : Measure E)
            + eLpNorm (fun x => B (gradient (u j) x) - B (gradient g x)) 2 (ν : Measure E) :=
            eLpNorm_add_le one_le_two
        _ ≤ ‖B‖ₑ * ENNReal.ofReal (radius j) +
            eLpNorm (fun x => B (gradient (u j) x) - B (gradient g x)) 2 (ν : Measure E) := by
            gcongr
            calc eLpNorm (fun x => B (gradient (v j (k j)) x) - B (gradient (u j) x)) 2
                  (ν : Measure E)
                ≤ eLpNorm (‖B‖ • fun x => ‖gradient (v j (k j)) x - gradient (u j) x‖) 2
                  (ν : Measure E) := by
                  refine eLpNorm_mono_ae_real ((hmB _).sub (hmB _)) (ae_of_all _ fun x => ?_)
                  rw [← map_sub]
                  exact B.le_opNorm _
              _ = ‖B‖ₑ * eLpNorm (fun x => gradient (v j (k j)) x - gradient (u j) x) 2
                  (ν : Measure E) := by
                  rw [eLpNorm_const_smul, enorm_norm, eLpNorm_norm
                    (fun x => gradient (v j (k j)) x - gradient (u j) x)
                    ((aestronglyMeasurable_gradient _ _).sub (aestronglyMeasurable_gradient _ _))]
              _ ≤ ‖B‖ₑ * ENNReal.ofReal (radius j) := by
                  gcongr
                  exact hk2 j
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le) hle
    have h1 : Tendsto (fun j => ‖B‖ₑ * ENNReal.ofReal (radius j)) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal tendsto_radius) (a := ‖B‖ₑ)
        (Or.inr enorm_ne_top)
      simpa using this
    simpa using h1.add hu2

/-- Bounded L1 variant of the same Blueprint lemma. A closed interval [a,b] is preserved;
setting a=0 and b=1 gives the stated range-preserving case. No compact support is required here.
The smoothing also preserves the supplied global Lipschitz bound. -/
theorem exists_smooth_bounded_L1
    (hν : (ν : Measure E) ≪ m) (g : E → ℝ) (K : NNReal)
    (hg : LipschitzWith K g) (a b : ℝ) (hbounds : ∀ x, a ≤ g x ∧ g x ≤ b) :
    MemLp g 1 (ν : Measure E) ∧ MemLp (gradient g) 1 (ν : Measure E) ∧
      ∃ gSeq : ℕ → E → ℝ,
        (∀ j, ContDiff ℝ ∞ (gSeq j) ∧ LipschitzWith K (gSeq j) ∧
          (∀ x, a ≤ gSeq j x ∧ gSeq j x ≤ b) ∧
          MemLp (gSeq j) 1 (ν : Measure E) ∧
          MemLp (gradient (gSeq j)) 1 (ν : Measure E)) ∧
        Tendsto (fun j ↦ eLpNorm (fun x ↦ gSeq j x - g x) 1 (ν : Measure E))
          atTop (𝓝 0) ∧
        Tendsto (fun j ↦ eLpNorm (fun x ↦ gradient (gSeq j) x - gradient g x)
          1 (ν : Measure E)) atTop (𝓝 0) := by
  have hC : ∀ x, ‖g x‖ ≤ max |a| |b| := fun x => by
    rw [Real.norm_eq_abs]
    exact abs_le_max_abs_abs (hbounds x).1 (hbounds x).2
  have hgL1 : MemLp g 1 (ν : Measure E) :=
    MemLp.of_bound hg.continuous.aestronglyMeasurable _ (ae_of_all _ hC)
  have hgradL1 : MemLp (gradient g) 1 (ν : Measure E) :=
    MemLp.of_bound (aestronglyMeasurable_gradient g _) K
      (ae_of_all _ (norm_gradient_le_of_lipschitz hg))
  refine ⟨hgL1, hgradL1, fun j => mollify m (radius j) g, fun j => ?_, ?_, ?_⟩
  · have hR := radius_pos j
    refine ⟨contDiff_mollify m hR hg.continuous, lipschitzWith_mollify m hR hg,
      fun x => ⟨le_mollify m hR hg.continuous (fun x => (hbounds x).1) x,
        mollify_le m hR hg.continuous (fun x => (hbounds x).2) x⟩, ?_, ?_⟩
    · refine MemLp.of_bound (continuous_mollify m hR hg.continuous).aestronglyMeasurable
        (max |a| |b|) (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs]
      exact abs_mollify_le m hR hg.continuous (fun x => by rw [← Real.norm_eq_abs]; exact hC x) x
    · exact MemLp.of_bound (aestronglyMeasurable_gradient _ _) K
        (ae_of_all _ (norm_gradient_le_of_lipschitz (lipschitzWith_mollify m hR hg)))
  · have hbound : ∀ j, eLpNorm (fun x => mollify m (radius j) g x - g x) 1 (ν : Measure E) ≤
        ENNReal.ofReal (K * (2 * radius j)) := by
      intro j
      have := eLpNorm_le_of_ae_bound (μ := (ν : Measure E)) (p := 1)
        (f := fun x => mollify m (radius j) g x - g x) ((continuous_mollify m (radius_pos j) hg.continuous).sub
          hg.continuous).aestronglyMeasurable
        (ae_of_all _ (norm_mollify_sub_le m (radius_pos j) hg))
      simpa [measure_univ] using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ => zero_le) hbound
    have h : Tendsto (fun j => (K : ℝ) * (2 * radius j)) atTop (𝓝 0) := by
      simpa using (tendsto_radius.const_mul 2).const_mul (K : ℝ)
    simpa using ENNReal.tendsto_ofReal h
  · refine tendsto_eLpNorm_zero_of_dominated (ν : Measure E) (by norm_num) (by norm_num)
      (fun j => (aestronglyMeasurable_gradient _ _).sub (aestronglyMeasurable_gradient _ _))
      (bound := fun _ => (K : ℝ) + K) (memLp_const _) (fun j => ae_of_all _ fun x => ?_) ?_
    · calc ‖gradient (mollify m (radius j) g) x - gradient g x‖
          ≤ ‖gradient (mollify m (radius j) g) x‖ + ‖gradient g x‖ := norm_sub_le _ _
        _ ≤ K + K := add_le_add
          (norm_gradient_le_of_lipschitz (lipschitzWith_mollify m (radius_pos j) hg) x)
          (norm_gradient_le_of_lipschitz hg x)
    · filter_upwards [hν.ae_le (hg.ae_differentiableAt (μ := m))] with x hx
      have := (tendsto_gradient_mollify m hg.continuous hx radius_pos tendsto_radius).sub_const
        (gradient g x)
      simpa using this

end Main

end FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
