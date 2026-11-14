/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.MarkovProcess.MarkovProcess.Kernel.KolmogorovMoments
public import LeanPool.Superdiffusion.Algsuperdiff.Process.Kernel.ResolventTail

/-!
# ResolventTailMoments

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Kolmogorov moments from resolvent tail decay

The displacement tail of `Kernel/ResolventTail.lean` is integrated here against the cubic weight
of the layer-cake formula, which turns it into the intrinsic fourth-moment criterion
`SubMarkovKernelSemigroup.HasKolmogorovMoments 4 2 M` and hence, through `Main.lean`, into the
continuous-path process.

The layer cake is applied to the displacement rescaled by `4 sqrt t`, so that the tail estimate
enters in the scale-free variable and the time dependence `t ^ 2` is produced by the Jacobian
alone.  Below the cutting radius the transition mass is bounded by one, which contributes
`(4 a) ^ 4 t ^ 2`; above it the tail estimate contributes `8 e 4 ^ 4` times the cubic budget
`I` of the profile.  The resulting constant is explicit in the statement.

The budget is a hypothesis, as the tail decay is: nothing here asserts an analytic estimate for
a particular generator.

On a state space of finite diameter only the shifts at least one are needed, because only the
times at most one enter the local criterion.  That is the form the one-point compactification of
a live space uses: with an exhaustion function bounded by one, tail decay in the metric it
determines produces the regularity data from which the continuous-path process of the
compactified semigroup is formed.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace Algsuperdiff.Process.OnePoint

open _root_.OnePoint

variable {X : Type*} [MetricSpace X]

/-- An exhaustion function bounded by one gives the compactification diameter at most two. -/
theorem exhaustionDist_le_two {rho : X → ℝ} (hrho_le : ∀ x, rho x ≤ 1) (z w : OnePoint X) :
    exhaustionDist rho z w ≤ 2 := by
  induction z using OnePoint.rec with
  | infty =>
      induction w using OnePoint.rec with
      | infty => rw [exhaustionDist_infty_infty]; norm_num
      | coe y => rw [exhaustionDist_infty_coe]; linarith only [hrho_le y]
  | coe x =>
      induction w using OnePoint.rec with
      | infty => rw [exhaustionDist_coe_infty]; linarith only [hrho_le x]
      | coe y =>
          rw [exhaustionDist_coe_coe]
          exact le_trans (min_le_right _ _) (by linarith only [hrho_le x, hrho_le y])

/-- **The compactification displacement bound.**  In the metric determined by an exhaustion
function bounded by one, the fourth power of the distance on the compactification is at most
sixteen.  This is the uniform displacement bound the local moment criterion consumes. -/
theorem exhaustionMetricSpace_edist_pow_le (rho : X → ℝ) (hrho_cont : Continuous rho)
    (hrho_pos : ∀ x, 0 < rho x) (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x})
    (hrho_le : ∀ x, rho x ≤ 1) :
    letI := exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    ∀ z w : OnePoint X, edist w z ^ (4 : ℝ) ≤ ((16 : ℝ≥0) : ℝ≥0∞) := by
  let := exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  intro z w
  have hd : dist w z ≤ 2 := exhaustionDist_le_two hrho_le w z
  calc edist w z ^ (4 : ℝ) ≤ (2 : ℝ≥0∞) ^ (4 : ℝ) := by
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        rw [edist_dist]
        calc ENNReal.ofReal (dist w z) ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hd
          _ = 2 := by
              rw [show (2 : ℝ) = ((2 : ℝ≥0) : ℝ) by norm_num, ENNReal.ofReal_coe_nnreal]
              rfl
    _ = ((16 : ℝ≥0) : ℝ≥0∞) := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
        norm_num

end Algsuperdiff.Process.OnePoint

open MarkovProcess

namespace Algsuperdiff.Process

/-- The weighted layer-cake budget of a cubic weight on a bounded interval. -/
theorem lintegral_Ioc_ofReal_cube {a : ℝ} (ha : 0 ≤ a) :
    ∫⁻ s in Set.Ioc (0 : ℝ) a, ENNReal.ofReal (s ^ 3) = ENNReal.ofReal (a ^ 4 / 4) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← intervalIntegral.integral_of_le ha, integral_pow]
    norm_num
  · exact (continuous_pow 3).integrableOn_Ioc
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with s hs
    exact pow_nonneg hs.1.le 3


namespace PositiveC0ContractiveResolvent

open Semigroup SubMarkovKernelSemigroup
open MarkovProcess.PositiveC0ContractiveResolvent

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]


/-- **The fourth displacement moment at one time from resolvent tail decay.**  The layer-cake
formula in the parabolic variable turns the displacement tail into a fourth moment of order
`t ^ 2`, with the trivial bound below the cutting radius and the tail estimate above it. -/
theorem lintegral_edist_pow_le_of_hasResolventTail
    (R : PositiveC0ContractiveResolvent X) (hcons : R.kernelSemigroup.IsConservative)
    {phi : ℝ → ℝ} (hphi : ∀ s, 0 ≤ phi s)
    {mu : PositiveShift} (htail : SubMarkovKernelSemigroup.HasResolventTail R.kernelSemigroup (mu
      : ℝ) phi)
    {t : ℝ≥0} (htmu : (mu : ℝ) * (t : ℝ) = 1) {a I : ℝ} (ha : 0 ≤ a) (hI : 0 ≤ I)
    (hint : ∫⁻ s in Set.Ioi a, ENNReal.ofReal (phi s * s ^ 3) ≤ ENNReal.ofReal I) (x : X) :
    ∫⁻ z, edist z x ^ (4 : ℝ) ∂(R.kernelSemigroup t x) ≤
      ENNReal.ofReal (256 * (a ^ 4 + 8 * Real.exp 1 * I)) * ENNReal.ofReal ((t : ℝ) ^ 2) := by
  have hmu : (0 : ℝ) < (mu : ℝ) := mu.property
  have ht : (0 : ℝ) < (t : ℝ) := by
    rcases lt_or_ge (0 : ℝ) (t : ℝ) with h | h
    · exact h
    · exfalso
      have : (mu : ℝ) * (t : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hmu.le h
      rw [htmu] at this
      linarith only [this]
  set c : ℝ := 4 * Real.sqrt (t : ℝ) with hc_def
  have hsqrt_t : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr ht
  have hc : 0 < c := by rw [hc_def]; linarith only [hsqrt_t]
  have hsqrt : Real.sqrt (mu : ℝ) * Real.sqrt (t : ℝ) = 1 := by
    rw [← Real.sqrt_mul hmu.le, htmu, Real.sqrt_one]
  set nu := R.kernelSemigroup t x with hnu
  -- the measure of the level set of the rescaled distance
  have hlevel : ∀ s : ℝ, 0 < s →
      nu {z | s < dist z x / c} ≤ ENNReal.ofReal (2 * Real.exp 1 * phi s) := by
    intro s hs
    have hsub : {z | s < dist z x / c} ⊆ (Metric.ball x (4 * (Real.sqrt (t : ℝ) * s)))ᶜ := by
      intro z hz
      have hz' : c * s < dist z x := by
        rw [Set.mem_ofPred_eq, lt_div_iff₀ hc] at hz
        linarith only [hz]
      simp only [Set.mem_compl_iff, Metric.mem_ball, not_lt]
      rw [hc_def] at hz'
      linarith only [hz']
    refine le_trans (measure_mono hsub) ?_
    have hkey := measure_compl_ball_le_of_hasResolventTail R hcons hphi htail htmu x
      (r := Real.sqrt (t : ℝ) * s) (by positivity)
    rw [show Real.sqrt (mu : ℝ) * (Real.sqrt (t : ℝ) * s) = s by
      rw [← mul_assoc, hsqrt, one_mul]] at hkey
    exact hkey
  -- the layer-cake formula in the rescaled variable
  have hdistmeas : Measurable fun z : X ↦ dist z x / c :=
    (measurable_dist.comp (measurable_id.prodMk measurable_const)).div_const _
  have hrescale : ∀ z : X, dist z x ^ (4 : ℝ) = c ^ (4 : ℝ) * (dist z x / c) ^ (4 : ℝ) := by
    intro z
    rw [← Real.mul_rpow hc.le (by positivity), mul_div_cancel₀ _ hc.ne']
  have hcake : ∫⁻ z, edist z x ^ (4 : ℝ) ∂nu =
      ENNReal.ofReal (c ^ (4 : ℝ)) *
        (ENNReal.ofReal 4 * ∫⁻ s in Set.Ioi (0 : ℝ),
          nu {z | s < dist z x / c} * ENNReal.ofReal (s ^ ((4 : ℝ) - 1))) := by
    rw [show (∫⁻ z, edist z x ^ (4 : ℝ) ∂nu) =
        ∫⁻ z, ENNReal.ofReal (c ^ (4 : ℝ)) *
          ENNReal.ofReal ((dist z x / c) ^ (4 : ℝ)) ∂nu by
      refine lintegral_congr fun z ↦ ?_
      rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num), hrescale z,
        ENNReal.ofReal_mul (Real.rpow_nonneg hc.le 4)]]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    exact lintegral_rpow_eq_lintegral_meas_lt_mul nu
      (Eventually.of_forall fun z ↦ by positivity) hdistmeas.aemeasurable (by norm_num)
  -- constants
  have h2e : (0 : ℝ) ≤ 2 * Real.exp 1 := by positivity
  have h2eI : (0 : ℝ) ≤ 2 * Real.exp 1 * I := mul_nonneg h2e hI
  have ha4 : (0 : ℝ) ≤ a ^ 4 / 4 := by positivity
  have hexp3 : ∀ s : ℝ, s ^ ((4 : ℝ) - 1) = s ^ (3 : ℕ) := by
    intro s
    rw [show (4 : ℝ) - 1 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hc4 : c ^ (4 : ℝ) = 256 * (t : ℝ) ^ 2 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hc_def, mul_pow,
      show Real.sqrt (t : ℝ) ^ (4 : ℕ) = (Real.sqrt (t : ℝ) ^ 2) ^ 2 by ring,
      Real.sq_sqrt ht.le]
    norm_num
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) a) (Set.Ioi a) := by
    rw [Set.disjoint_left]
    intro s hs hs'
    exact absurd hs.2 (not_le.mpr hs')
  have hbound : ∫⁻ s in Set.Ioi (0 : ℝ),
      nu {z | s < dist z x / c} * ENNReal.ofReal (s ^ ((4 : ℝ) - 1)) ≤
      ENNReal.ofReal (a ^ 4 / 4) + ENNReal.ofReal (2 * Real.exp 1) * ENNReal.ofReal I := by
    simp only [hexp3]
    rw [← Set.Ioc_union_Ioi_eq_Ioi ha, lintegral_union measurableSet_Ioi hdisj]
    refine add_le_add ?_ ?_
    · calc ∫⁻ s in Set.Ioc (0 : ℝ) a,
            nu {z | s < dist z x / c} * ENNReal.ofReal (s ^ (3 : ℕ))
          ≤ ∫⁻ s in Set.Ioc (0 : ℝ) a, ENNReal.ofReal (s ^ (3 : ℕ)) := by
            refine setLIntegral_mono' measurableSet_Ioc fun s _ ↦ ?_
            calc nu {z | s < dist z x / c} * ENNReal.ofReal (s ^ (3 : ℕ))
                ≤ 1 * ENNReal.ofReal (s ^ (3 : ℕ)) := by
                  gcongr
                  exact R.kernelSemigroup.measure_le_one t x _
              _ = ENNReal.ofReal (s ^ (3 : ℕ)) := one_mul _
        _ = ENNReal.ofReal (a ^ 4 / 4) := lintegral_Ioc_ofReal_cube ha
    · calc ∫⁻ s in Set.Ioi a, nu {z | s < dist z x / c} * ENNReal.ofReal (s ^ (3 : ℕ))
          ≤ ∫⁻ s in Set.Ioi a, ENNReal.ofReal (2 * Real.exp 1) *
              ENNReal.ofReal (phi s * s ^ (3 : ℕ)) := by
            refine setLIntegral_mono' measurableSet_Ioi fun s hs ↦ ?_
            have hs0 : 0 < s := lt_of_le_of_lt ha hs
            calc nu {z | s < dist z x / c} * ENNReal.ofReal (s ^ (3 : ℕ))
                ≤ ENNReal.ofReal (2 * Real.exp 1 * phi s) *
                    ENNReal.ofReal (s ^ (3 : ℕ)) := by
                  gcongr
                  exact hlevel s hs0
              _ = ENNReal.ofReal (2 * Real.exp 1) *
                    ENNReal.ofReal (phi s * s ^ (3 : ℕ)) := by
                  rw [← ENNReal.ofReal_mul (mul_nonneg h2e (hphi s)),
                    ← ENNReal.ofReal_mul h2e]
                  congr 1
                  ring
        _ = ENNReal.ofReal (2 * Real.exp 1) *
              ∫⁻ s in Set.Ioi a, ENNReal.ofReal (phi s * s ^ (3 : ℕ)) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (2 * Real.exp 1) * ENNReal.ofReal I := by gcongr
  rw [hcake]
  calc ENNReal.ofReal (c ^ (4 : ℝ)) *
        (ENNReal.ofReal 4 * ∫⁻ s in Set.Ioi (0 : ℝ),
          nu {z | s < dist z x / c} * ENNReal.ofReal (s ^ ((4 : ℝ) - 1)))
      ≤ ENNReal.ofReal (c ^ (4 : ℝ)) * (ENNReal.ofReal 4 *
          (ENNReal.ofReal (a ^ 4 / 4) +
            ENNReal.ofReal (2 * Real.exp 1) * ENNReal.ofReal I)) := by
        gcongr
    _ = ENNReal.ofReal (256 * (a ^ 4 + 8 * Real.exp 1 * I)) * ENNReal.ofReal ((t : ℝ) ^ 2) := by
        rw [← ENNReal.ofReal_mul h2e, ← ENNReal.ofReal_add ha4 h2eI,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
          ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le 4),
          ← ENNReal.ofReal_mul (by
            have h1 : (0 : ℝ) ≤ a ^ 4 := by positivity
            have h2 : (0 : ℝ) ≤ 8 * Real.exp 1 * I := by
              exact mul_nonneg (by positivity) hI
            linarith only [h1, h2] : (0 : ℝ) ≤ 256 * (a ^ 4 + 8 * Real.exp 1 * I)), hc4]
        congr 1
        ring

/-- The fourth displacement moment of a transition law vanishes at the time zero. -/
theorem lintegral_edist_pow_zero (R : PositiveC0ContractiveResolvent X) (y : X) :
    ∫⁻ z, edist z y ^ (4 : ℝ) ∂(R.kernelSemigroup 0 y) = 0 := by
  have hmeas : Measurable fun z : X ↦ edist z y ^ (4 : ℝ) :=
    (measurable_edist_left (x := y)).pow_const _
  have hzero : R.kernelSemigroup 0 y = Measure.dirac y := by
    rw [R.kernelSemigroup.zero]
    rfl
  rw [hzero, lintegral_dirac' _ hmeas, edist_self, ENNReal.zero_rpow_of_pos (by norm_num)]

/-- **Regularity data of a compactified process from a local moment estimate.**  An exhaustion
function and a local fourth-moment estimate for the compactified semigroup in the metric that
function determines give the data from which the continuous-path process of the compactified
semigroup is formed.  This is the common core of the tail criteria below: they differ only in
how the local moment estimate is produced. -/
def OnePointRegular.ofHasLocalKolmogorovMoments (R : PositiveC0ContractiveResolvent X)
    (rho : X → ℝ) (hrho_cont : Continuous rho) (hrho_pos : ∀ x, 0 < rho x)
    (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x})
    {q : ℝ} {M B : ℝ≥0}
    (hmom :
      letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
      R.onePointKernelSemigroup.HasLocalKolmogorovMoments 4 q M B) :
    R.OnePointRegular where
  rho := rho
  continuous_rho := hrho_cont
  rho_pos := hrho_pos
  lipschitz_rho := hrho_lipschitz
  isCompact_superlevel := hrho_compact
  kolmogorovRegular := by
    let := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    let : CompleteSpace (OnePoint X) :=
      completeSpace_of_isComplete_univ isCompact_univ.isComplete
    exact SubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments _
      R.isConservative_onePointKernelSemigroup
      (hmom.toHasKolmogorovMoments R.isConservative_onePointKernelSemigroup)

end PositiveC0ContractiveResolvent

end Algsuperdiff.Process
