/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Wiener.WienerIntegralL2
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The Wiener integral of a deterministic integrand is Gaussian

The Wiener integral `wienerIntegralLp B hB T : L²([0,T]) →L[ℝ] L²(μ)`
(`Probability/Brownian/Wiener/WienerIntegralL2.lean`) was built as an isometry — its *norm* is
pinned (`wienerIntegralLp_norm`, `wienerIntegralLp_integral_sq`) but its *law*
was not. This file proves the missing distributional fact:

  for a **deterministic** integrand `f ∈ L²([0,T])`, the random variable
  `ω ↦ (wienerIntegralLp B hB T f) ω` is **Gaussian**, centred, with variance
  `‖f‖²₂ = ∫₀ᵀ f²`:

  `μ.map (wienerIntegralLp B hB T f) = gaussianReal 0 ‖f‖²`.

This is the structural fact behind every linear-SDE terminal law (Vasicek /
Ornstein–Uhlenbeck / Hull–White): the diffusion term `σ ∫₀ᵗ e^{−κ(t−s)} dB_s`
is a deterministic-integrand Itô integral, hence Gaussian, with variance fixed
by the isometry. See `Models/Rates/VasicekSDEGaussian.lean`.

## Proof

The Wiener integral is the `extendOfNorm` closure of the elementary integral
`wienerAssembly` on simple (step) processes, along the dense embedding
`stepAssembly` of step indicators in `L²([0,T])` (`stepAssembly_denseRange`).

1. **Simple processes are Gaussian.** `wienerAssembly B hB T x =
   ∑ᵢ xᵢ (B_{tᵢ} − B_{sᵢ})` is a finite linear combination of the Gaussian
   process `B`. The scaled-increment family is a Gaussian process
   (`IsGaussianProcess.of_isGaussianProcess`), so its finite sum is Gaussian
   (`hasGaussianLaw_fun_sum`). `map_eq_gaussianReal` then pins the law to
   `gaussianReal 0 ‖stepAssembly x‖²` — mean `0` (Brownian increments are
   centred) and variance `‖wienerAssembly x‖² = ‖stepAssembly x‖²` (the Itô
   isometry, `wiener_assembly_isometry`).

2. **Pass to the L²-limit by characteristic functions.** For each frequency
   `t`, the map `g ↦ charFun (μ.map (wienerIntegralLp g)) t` is continuous
   (charFun is `|t|`-Lipschitz in the `L²` random variable) and equals
   `exp(−‖g‖² t²/2)` on the dense simple processes; both sides are continuous,
   so they agree on all of `L²([0,T])` (`DenseRange.induction_on`). Two finite
   measures on `ℝ` with equal characteristic functions coincide
   (`Measure.ext_of_charFun`), giving the law.

## Main results

* `wienerIntegralLp_map_eq_gaussianReal`: `μ.map (wienerIntegralLp B hB T f) =
  gaussianReal 0 (‖f‖²).toNNReal`.
* `wienerIntegralLp_hasLaw_gaussian`: the `HasLaw` form with the variance in
  integral shape `(∫₀ᵀ f²).toNNReal`.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Ch 6/7

## Tags

Wiener integral, Gaussian law, deterministic integrand, Ornstein–Uhlenbeck, Vasicek model,
characteristic function, MSC 60H05, MSC 60G15, MSC 60J65
-/

@[expose] public section

namespace MathFin
namespace WienerIntegralL2

open MeasureTheory ProbabilityTheory Finset Complex
open scoped NNReal ENNReal Topology InnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-! ### The Wiener integral agrees with the elementary integral on step processes -/

/-- On the range of `stepAssembly`, the extended Wiener integral is the
elementary integral `wienerAssembly` (this is `LinearMap.extendOfNorm_eq`). -/
lemma wienerIntegralLp_stepAssembly (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (x : StepIndex T →₀ ℝ) :
    wienerIntegralLp B hB T (stepAssembly T x) = wienerAssembly B hB T x := by
  rw [wienerIntegralLp,
    LinearMap.extendOfNorm_eq (stepAssembly_denseRange T)
      ⟨1, fun y ↦ by rw [one_mul]; exact (wiener_assembly_isometry hB T y).le⟩]

/-! ### Simple processes are Gaussian -/

omit [IsProbabilityMeasure μ] in
/-- Explicit a.e. form of the elementary integral: `wienerAssembly B hB T x`
agrees a.e. with the finite sum of scaled Brownian increments. -/
lemma wienerAssembly_coeFn (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (x : StepIndex T →₀ ℝ) :
    (wienerAssembly B hB T x : Ω → ℝ) =ᵐ[μ]
      fun ω ↦ ∑ i ∈ x.support, x i • (B i.1.2 ω - B i.1.1 ω) := by
  have hExpand : wienerAssembly B hB T x
      = ∑ i ∈ x.support, x i • wienerIncrementLp B hB i := by
    rw [wienerAssembly, Finsupp.linearCombination_apply, Finsupp.sum]
  have hterm : ∀ i ∈ x.support,
      (↑(x i • wienerIncrementLp B hB i) : Ω → ℝ)
        =ᵐ[μ] fun ω ↦ x i • (B i.1.2 ω - B i.1.1 ω) := by
    intro i _
    filter_upwards [Lp.coeFn_smul (x i) (wienerIncrementLp B hB i),
      MemLp.coeFn_toLp (memLp_increment hB i.1.1 i.1.2)] with ω hsmul htoLp
    rw [hsmul]
    simp only [Pi.smul_apply]
    rw [show (wienerIncrementLp B hB i : Ω → ℝ) ω = B i.1.2 ω - B i.1.1 ω from htoLp]
  rw [hExpand]
  refine (Lp.coeFn_finsetSum x.support (fun i ↦ x i • wienerIncrementLp B hB i)).trans ?_
  filter_upwards [(Filter.eventually_all_finset x.support).2 hterm] with ω hω
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i hi ↦ hω i hi)

omit [IsProbabilityMeasure μ] in
/-- The scaled-increment family `i ↦ xᵢ (B_{hiᵢ} − B_{loᵢ})` is a Gaussian
process: each value is a (continuous-linear) combination of finitely many
values of the Gaussian process `B`. -/
lemma isGaussianProcess_scaledIncrement (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (x : StepIndex T →₀ ℝ) :
    IsGaussianProcess (fun (i : StepIndex T) ω ↦ x i • (B i.1.2 ω - B i.1.1 ω)) μ := by
  refine hB.isGaussianProcess.of_isGaussianProcess (fun i ↦ ⟨{i.1.1, i.1.2},
    LinearMap.toContinuousLinearMap
      { toFun := fun v ↦ x i • (v ⟨i.1.2, by simp⟩ - v ⟨i.1.1, by simp⟩)
        map_add' := fun v w ↦ by simp only [Pi.add_apply]; module
        map_smul' := fun c v ↦ by simp only [Pi.smul_apply, RingHom.id_apply]; module }, ?_⟩)
  intro ω
  simp [Finset.restrict]

omit [IsProbabilityMeasure μ] in
/-- A simple (step-process) Wiener integral has a Gaussian law. -/
lemma wienerAssembly_hasGaussianLaw (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (x : StepIndex T →₀ ℝ) :
    HasGaussianLaw (fun ω ↦ (wienerAssembly B hB T x) ω) μ := by
  have hsum : HasGaussianLaw
      (fun ω ↦ ∑ i ∈ x.support, x i • (B i.1.2 ω - B i.1.1 ω)) μ :=
    (isGaussianProcess_scaledIncrement hB T x).hasGaussianLaw_fun_sum (I := x.support)
  exact hsum.congr (wienerAssembly_coeFn hB T x).symm

/-- The elementary integral is centred: `∫ wienerAssembly B hB T x ∂μ = 0`. -/
lemma wienerAssembly_integral_zero (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (x : StepIndex T →₀ ℝ) :
    ∫ ω, (wienerAssembly B hB T x) ω ∂μ = 0 := by
  rw [integral_congr_ae (wienerAssembly_coeFn hB T x)]
  have hsum : ∫ ω, ∑ i ∈ x.support, x i • (B i.1.2 ω - B i.1.1 ω) ∂μ
      = ∑ i ∈ x.support, ∫ ω, x i • (B i.1.2 ω - B i.1.1 ω) ∂μ :=
    integral_finsetSum x.support
      (fun i _ ↦ Integrable.smul (x i) ((memLp_increment hB i.1.1 i.1.2).integrable one_le_two))
  rw [hsum]
  refine Finset.sum_eq_zero (fun i _ ↦ ?_)
  rw [integral_smul,
    integral_sub ((hB.isGaussianProcess.hasGaussianLaw_eval i.1.2).memLp_two.integrable one_le_two)
      ((hB.isGaussianProcess.hasGaussianLaw_eval i.1.1).memLp_two.integrable one_le_two),
    hB.integral_eval i.1.2, hB.integral_eval i.1.1, sub_zero, smul_zero]

/-- The law of a simple-process Wiener integral: `gaussianReal 0 ‖stepAssembly x‖²`. -/
lemma wienerAssembly_map_eq_gaussianReal (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (x : StepIndex T →₀ ℝ) :
    μ.map (fun ω ↦ (wienerAssembly B hB T x) ω)
      = gaussianReal 0 (‖stepAssembly T x‖ ^ 2).toNNReal := by
  rw [(wienerAssembly_hasGaussianLaw hB T x).map_eq_gaussianReal]
  have hmean : μ[fun ω ↦ (wienerAssembly B hB T x) ω] = 0 :=
    wienerAssembly_integral_zero hB T x
  have hvar : Var[fun ω ↦ (wienerAssembly B hB T x) ω; μ] = ‖stepAssembly T x‖ ^ 2 := by
    rw [variance_eq_integral
      ((Lp.aestronglyMeasurable (wienerAssembly B hB T x)).aemeasurable), hmean]
    simp only [sub_zero]
    rw [← lp_two_norm_sq (wienerAssembly B hB T x), ← wiener_assembly_isometry hB T x]
  rw [hmean, hvar]

/-! ### Pass to the L²-limit by characteristic functions -/

/-- Auxiliary: on a probability measure, `∫ ‖g‖ ≤ ‖g‖₂` for `g ∈ L²`. -/
lemma L1_norm_le_L2_norm_prob (g : Lp ℝ 2 μ) :
    ∫ ω, ‖g ω‖ ∂μ ≤ ‖g‖ := by
  rw [show (∫ ω, ‖g ω‖ ∂μ) = (eLpNorm (g : Ω → ℝ) 1 μ).toReal by
    rw [eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable g),
        ← integral_norm_eq_lintegral_eNorm (Lp.aestronglyMeasurable g)],
    Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top g)
    (eLpNorm_le_eLpNorm_of_exponent_le one_le_two)

/-- The characteristic function of `μ.map h` is `|t|`-Lipschitz in `h : L²(μ)`. -/
lemma charFun_map_lp_dist_le (t : ℝ) (h₁ h₂ : Lp ℝ 2 μ) :
    ‖charFun (μ.map (h₁ : Ω → ℝ)) t - charFun (μ.map (h₂ : Ω → ℝ)) t‖
      ≤ |t| * ‖h₁ - h₂‖ := by
  have hInt : ∀ h : Lp ℝ 2 μ, Integrable (fun ω ↦ cexp (↑t * ↑(h ω) * I)) μ := fun h ↦
    (memLp_top_of_bound (by fun_prop) 1
      (ae_of_all _ fun ω ↦ by rw [Complex.norm_exp]; simp)).integrable le_top
  have hcf : ∀ h : Lp ℝ 2 μ, charFun (μ.map (h : Ω → ℝ)) t
      = ∫ ω, cexp (↑t * ↑(h ω) * I) ∂μ := by
    intro h
    rw [charFun_apply_real, integral_map (Lp.aestronglyMeasurable h).aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop))]
  have hbound : ∀ ω, ‖cexp (↑t * ↑(h₁ ω) * I) - cexp (↑t * ↑(h₂ ω) * I)‖
      ≤ |t| * |h₁ ω - h₂ ω| := by
    intro ω
    have hfac : cexp (↑t * ↑(h₁ ω) * I) - cexp (↑t * ↑(h₂ ω) * I)
        = cexp (↑t * ↑(h₂ ω) * I) * (cexp (I * ((t * (h₁ ω - h₂ ω) : ℝ) : ℂ)) - 1) := by
      rw [mul_sub, mul_one, ← Complex.exp_add,
        show (↑t * ↑(h₂ ω) * I + I * ((t * (h₁ ω - h₂ ω) : ℝ) : ℂ)) = ↑t * ↑(h₁ ω) * I by
          push_cast; ring]
    rw [hfac, norm_mul, show ‖cexp (↑t * ↑(h₂ ω) * I)‖ = 1 by
      rw [show (↑t * ↑(h₂ ω) * I : ℂ) = ↑(t * h₂ ω) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I], one_mul]
    calc ‖cexp (I * ((t * (h₁ ω - h₂ ω) : ℝ) : ℂ)) - 1‖
        ≤ ‖(t * (h₁ ω - h₂ ω) : ℝ)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
      _ = |t| * |h₁ ω - h₂ ω| := by rw [Real.norm_eq_abs, abs_mul]
  have hint_bound : Integrable (fun ω ↦ |t| * |h₁ ω - h₂ ω|) μ := by
    refine Integrable.const_mul ?_ _
    have hi : Integrable (fun ω ↦ (h₁ - h₂) ω) μ := (Lp.memLp (h₁ - h₂)).integrable one_le_two
    refine hi.abs.congr ?_
    filter_upwards [Lp.coeFn_sub h₁ h₂] with ω hω; rw [hω, Pi.sub_apply]
  rw [hcf, hcf]
  calc ‖(∫ ω, cexp (↑t * ↑(h₁ ω) * I) ∂μ) - ∫ ω, cexp (↑t * ↑(h₂ ω) * I) ∂μ‖
      = ‖∫ ω, (cexp (↑t * ↑(h₁ ω) * I) - cexp (↑t * ↑(h₂ ω) * I)) ∂μ‖ := by
        rw [integral_sub (hInt h₁) (hInt h₂)]
    _ ≤ ∫ ω, ‖cexp (↑t * ↑(h₁ ω) * I) - cexp (↑t * ↑(h₂ ω) * I)‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ ω, |t| * |h₁ ω - h₂ ω| ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun ω ↦ norm_nonneg _) hint_bound
          (ae_of_all _ hbound)
    _ = |t| * ∫ ω, |h₁ ω - h₂ ω| ∂μ := by rw [integral_const_mul]
    _ ≤ |t| * ‖h₁ - h₂‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg t)
        have hcongr : ∫ ω, |h₁ ω - h₂ ω| ∂μ = ∫ ω, ‖(h₁ - h₂) ω‖ ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [Lp.coeFn_sub h₁ h₂] with ω hω
          rw [hω, Real.norm_eq_abs, Pi.sub_apply]
        rw [hcongr]
        exact L1_norm_le_L2_norm_prob _

/-- **The Wiener integral of a deterministic integrand is Gaussian.** For every
`f ∈ L²([0,T])`, `μ.map (wienerIntegralLp B hB T f) = gaussianReal 0 ‖f‖²`. -/
theorem wienerIntegralLp_map_eq_gaussianReal (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) :
    μ.map (fun ω ↦ (wienerIntegralLp B hB T f) ω)
      = gaussianReal 0 (‖f‖ ^ 2).toNNReal := by
  refine Measure.ext_of_charFun (funext fun t ↦ ?_)
  have hcont1 : Continuous (fun g : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) ↦
      charFun (μ.map (fun ω ↦ (wienerIntegralLp B hB T g) ω)) t) := by
    have hL : LipschitzWith |t|.toNNReal
        (fun h : Lp ℝ 2 μ ↦ charFun (μ.map (h : Ω → ℝ)) t) :=
      LipschitzWith.of_dist_le_mul fun h₁ h₂ ↦ by
        rw [Complex.dist_eq]
        refine (charFun_map_lp_dist_le t h₁ h₂).trans (le_of_eq ?_)
        rw [Real.coe_toNNReal _ (abs_nonneg t), dist_eq_norm]
    exact hL.continuous.comp (wienerIntegralLp B hB T).continuous
  have hcont2 : Continuous (fun g : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) ↦
      cexp (-(((‖g‖ ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2))) := by
    apply Continuous.cexp; fun_prop
  have hbase : ∀ x : StepIndex T →₀ ℝ,
      charFun (μ.map (fun ω ↦ (wienerIntegralLp B hB T (stepAssembly T x)) ω)) t
        = cexp (-(((‖stepAssembly T x‖ ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2)) := by
    intro x
    rw [wienerIntegralLp_stepAssembly hB T x, wienerAssembly_map_eq_gaussianReal hB T x,
      charFun_gaussianReal]
    congr 1
    rw [show (((‖stepAssembly T x‖ ^ 2).toNNReal : ℝ)) = ‖stepAssembly T x‖ ^ 2 from
      Real.coe_toNNReal _ (by positivity)]
    push_cast; ring
  have hf_eq : charFun (μ.map (fun ω ↦ (wienerIntegralLp B hB T f) ω)) t
      = cexp (-(((‖f‖ ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2)) :=
    (stepAssembly_denseRange T).induction_on
      (p := fun g ↦ charFun (μ.map (fun ω ↦ (wienerIntegralLp B hB T g) ω)) t
        = cexp (-(((‖g‖ ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2)))
      f (isClosed_eq hcont1 hcont2) hbase
  rw [hf_eq, charFun_gaussianReal]
  congr 1
  rw [show (((‖f‖ ^ 2).toNNReal : ℝ)) = ‖f‖ ^ 2 from Real.coe_toNNReal _ (by positivity)]
  push_cast; ring

/-- **`HasLaw` form**, with the variance in integral shape `∫₀ᵀ f²`. -/
theorem wienerIntegralLp_hasLaw_gaussian (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) :
    HasLaw (fun ω ↦ (wienerIntegralLp B hB T f) ω)
      (gaussianReal 0 (∫ s in Set.Ioc (0 : ℝ) (T : ℝ), (f s) ^ 2 ∂volume).toNNReal) μ where
  aemeasurable := (Lp.aestronglyMeasurable _).aemeasurable
  map_eq := by
    rw [wienerIntegralLp_map_eq_gaussianReal hB T f]
    congr 2
    exact lp_two_norm_sq f

/-- The `L²` representative of an `L²` function has the same squared integral. -/
theorem _root_.MeasureTheory.MemLp.integral_sq_toLp {α : Type*} {mα : MeasurableSpace α}
    {ν : Measure α} {f : α → ℝ} (hf : MemLp f 2 ν) :
    ∫ x, (hf.toLp f x) ^ 2 ∂ν = ∫ x, f x ^ 2 ∂ν :=
  integral_congr_ae <| hf.coeFn_toLp.mono fun _ hx ↦ by simp only [hx]

/-- **`HasLaw` form with the variance given**: when `∫₀ᵀ f² = v`, the Wiener integral of `f` is
`N(0, v)`. -/
theorem wienerIntegralLp_hasLaw_gaussian_of_integral_sq (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) {v : ℝ}
    (hv : ∫ s in Set.Ioc (0 : ℝ) (T : ℝ), (f s) ^ 2 ∂volume = v) :
    HasLaw (fun ω ↦ (wienerIntegralLp B hB T f) ω) (gaussianReal 0 v.toNNReal) μ :=
  hv ▸ wienerIntegralLp_hasLaw_gaussian hB T f

end WienerIntegralL2
end MathFin
