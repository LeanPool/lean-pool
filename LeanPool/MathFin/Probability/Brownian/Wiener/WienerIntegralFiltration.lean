/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Wiener.WienerIntegralExpMoment
public import LeanPool.MathFin.Probability.Brownian.BrownianMarkov

/-!
# The Wiener integral given the past

The Wiener integral `∫₀ᵀ f dB` of a deterministic kernel splits at a time `t ≤ T` into the part
the past `𝓕_t = σ(B_s : s ≤ t)` has seen and a remainder independent of the past:

  `∫₀ᵀ f dB = ∫₀ᵗ f dB + N`,   `N ⟂ 𝓕_t`,   `𝔼[e^{−cN}] = e^{c²∫_t^T f²/2}`,

the exponential moments of a centred Gaussian of variance `∫_t^T f²` (the Gaussian law of `N`
itself is not stated). The past part is `wienerIntegralLp B hB t (kernelRestrict htT f)`, the
Wiener integral over `(0, t]` of the restricted kernel, and the remainder is the difference. Both
measurability statements are
closed conditions on the kernel `f` (the Wiener integral is continuous, `lpMeas` is closed), so
they are checked on step indicators, where the integral is a Brownian increment: the past
increments `B_{s∧t}` are `𝓕_t`-measurable, and the remainders `B_{s∨t} − B_t` are increments of
the post-`t` process, independent of `𝓕_t` (`shift_indep_natural`).

## Main definitions

* `kernelRestrict`: the continuous linear restriction of a kernel `f ∈ L²((0, T])` to `(0, t]`.
* `stepClip`: the step `(s ∧ t, u ∧ t]` of a step `(s, u]`, the part seen by time `t`.
* `postσ`: the σ-algebra of the post-`t` increments `ω ↦ (B_{t+s} − B_t)_s`.

## Main results

* `mem_lpMeas_of_stepIndicator` — a continuous linear image of kernels is `m`-measurable as soon
  as the images of the step indicators are.
* `wienerIntegralLp_past_mem_lpMeas`, `wienerIntegralLp_future_mem_lpMeas` — the past part is
  `𝓕_t`-measurable and the remainder is measurable for the post-`t` increments (`postσ`), hence
  independent of `𝓕_t`.
* `condExp_exp_wienerIntegralLp` — the conditional Laplace transform
  `𝔼[e^{a + b∫₀ᵗ h dB − c∫₀ᵀ f dB} | 𝓕_t] = e^{a + b∫₀ᵗ h dB − c∫₀ᵗ f dB}·e^{c²∫_t^T f²/2}`.

## References

* [I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991],
  section 3.2
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], Theorem
  4.4.9

## Tags

Wiener integral, conditional Laplace transform, independent of the past, deterministic kernel,
Gaussian short rate, conditional exponential moment, MSC 60H05, MSC 60G15, MSC 91G30
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal
open WienerIntegralL2

variable {t T : ℝ≥0}

/-! ### Restricting a kernel to the past -/

lemma volume_restrict_Ioc_mono (htT : t ≤ T) :
    volume.restrict (Set.Ioc (0 : ℝ) t) ≤ volume.restrict (Set.Ioc (0 : ℝ) T) :=
  Measure.restrict_mono (Set.Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 htT)) le_rfl

/-- **Restriction of a kernel to the past.** The kernel `f ∈ L²((0, T])`, seen on `(0, t]`. -/
noncomputable def kernelRestrict (htT : t ≤ T) :
    Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) T)) →L[ℝ]
      Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) t)) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ((Lp.memLp f).mono_measure (volume_restrict_Ioc_mono htT)).toLp f
      map_add' := fun f g ↦ by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (f + g)).mono_measure
            (volume_restrict_Ioc_mono htT)),
          MemLp.coeFn_toLp ((Lp.memLp f).mono_measure (volume_restrict_Ioc_mono htT)),
          MemLp.coeFn_toLp ((Lp.memLp g).mono_measure (volume_restrict_Ioc_mono htT)),
          (Lp.coeFn_add f g).filter_mono (ae_mono (volume_restrict_Ioc_mono htT)),
          Lp.coeFn_add (((Lp.memLp f).mono_measure (volume_restrict_Ioc_mono htT)).toLp f)
            (((Lp.memLp g).mono_measure (volume_restrict_Ioc_mono htT)).toLp g)]
          with x h1 h2 h3 h4 h5
        rw [h5, Pi.add_apply, h2, h3, h1, h4, Pi.add_apply]
      map_smul' := fun c f ↦ by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (c • f)).mono_measure
            (volume_restrict_Ioc_mono htT)),
          MemLp.coeFn_toLp ((Lp.memLp f).mono_measure (volume_restrict_Ioc_mono htT)),
          (Lp.coeFn_smul c f).filter_mono (ae_mono (volume_restrict_Ioc_mono htT)),
          Lp.coeFn_smul c (((Lp.memLp f).mono_measure (volume_restrict_Ioc_mono htT)).toLp f)]
          with x h1 h2 h3 h4
        rw [RingHom.id_apply, h4, Pi.smul_apply, h2, h1, h3, Pi.smul_apply] }
    1 fun f ↦ by
      rw [one_mul, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
        (eLpNorm_mono_measure _ (volume_restrict_Ioc_mono htT))

lemma kernelRestrict_coeFn (htT : t ≤ T) (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) T))) :
    kernelRestrict htT f =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) t)] f :=
  MemLp.coeFn_toLp ((Lp.memLp f).mono_measure (volume_restrict_Ioc_mono htT))


/-! ### Step indicators: past and future -/

/-- The step `(s ∧ t, u ∧ t]` of a step `(s, u]`: the part of the step seen by time `t`. -/
def stepClip (t : ℝ≥0) (i : StepIndex T) : StepIndex t :=
  ⟨(min i.1.1 t, min i.1.2 t), min_le_min_right _ i.2.1, min_le_right _ _⟩

lemma kernelRestrict_stepIndicatorLp (htT : t ≤ T) (i : StepIndex T) :
    kernelRestrict htT (stepIndicatorLp T i) = stepIndicatorLp t (stepClip t i) := by
  refine Lp.ext ?_
  have h2 : (stepIndicatorLp T i : ℝ → ℝ) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) T)]
      (i.interval).indicator fun _ ↦ (1 : ℝ) := indicatorConstLp_coeFn
  have h3 : (stepIndicatorLp t (stepClip t i) : ℝ → ℝ) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) t)]
      ((stepClip t i).interval).indicator fun _ ↦ (1 : ℝ) := indicatorConstLp_coeFn
  filter_upwards [kernelRestrict_coeFn htT (stepIndicatorLp T i),
    h2.filter_mono (ae_mono (volume_restrict_Ioc_mono htT)), h3,
    ae_restrict_mem measurableSet_Ioc] with x h1 h2 h3 hx
  rw [h1, h2, h3]
  simp only [Set.indicator_apply, StepIndex.interval, StepIndex.lo, StepIndex.hi, stepClip,
    Set.mem_Ioc, NNReal.coe_min]
  have hxt := not_lt.2 (Set.mem_Ioc.1 hx).2
  have hxt' := (Set.mem_Ioc.1 hx).2
  congr 1
  refine propext ?_
  simp only [min_lt_iff, le_min_iff]
  tauto

/-! ### Measurability is a closed condition on the kernel -/

section Closure

-- `m` precedes `mΩ`, so that `mΩ` is the instance the `Lp` spaces are built on.
variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- A continuous linear image of kernels is `m`-measurable as soon as the images of the step
indicators are: `lpMeas` is closed and the step indicators span a dense subspace. -/
lemma mem_lpMeas_of_stepIndicator (hm : m ≤ mΩ)
    (Φ : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) T)) →L[ℝ] Lp ℝ 2 μ)
    (h : ∀ i : StepIndex T, Φ (stepIndicatorLp T i) ∈ lpMeas ℝ ℝ m 2 μ)
    (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) T))) : Φ f ∈ lpMeas ℝ ℝ m 2 μ := by
  have : Fact (m ≤ mΩ) := ⟨hm⟩
  have hclosed : IsClosed (lpMeas ℝ ℝ m 2 μ : Set (Lp ℝ 2 μ)) :=
    (completeSpace_coe_iff_isComplete.1 (inferInstance : CompleteSpace (lpMeas ℝ ℝ m 2 μ))).isClosed
  refine (stepAssembly_denseRange T).induction_on (p := fun f ↦ Φ f ∈ lpMeas ℝ ℝ m 2 μ) f
    (hclosed.preimage Φ.continuous) fun x ↦ ?_
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
  | single i a =>
    rw [stepAssembly, Finsupp.linearCombination_single, map_smul]
    exact Submodule.smul_mem _ _ (h i)

/-- The Brownian increment, as an element of `Lp`, is `m`-measurable when its endpoints are. -/
lemma wienerIncrementLp_mem_lpMeas (hB : IsPreBrownianReal B μ)
    (i : StepIndex T) (h1 : StronglyMeasurable[m] (B i.1.1))
    (h2 : StronglyMeasurable[m] (B i.1.2)) :
    wienerIncrementLp B hB i ∈ lpMeas ℝ ℝ m 2 μ := by
  rw [mem_lpMeas_iff_aestronglyMeasurable]
  exact (h2.sub h1).aestronglyMeasurable.congr
    (MemLp.coeFn_toLp (memLp_increment hB i.1.1 i.1.2)).symm

variable [IsProbabilityMeasure μ]

/-- The Wiener integral of the kernel restricted to `(0, t]` is `𝓕_t`-measurable. -/
lemma wienerIntegralLp_past_mem_lpMeas (hB : IsPreBrownianReal B μ)
    (hBm : ∀ s, Measurable (B s)) (htT : t ≤ T)
    (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) T))) :
    wienerIntegralLp B hB t (kernelRestrict htT f)
      ∈ lpMeas ℝ ℝ (Filtration.natural B (fun s ↦ (hBm s).stronglyMeasurable) t) 2 μ := by
  have hF := Filtration.stronglyAdapted_natural (fun s ↦ (hBm s).stronglyMeasurable)
  refine mem_lpMeas_of_stepIndicator ((Filtration.natural B _).le t)
    ((wienerIntegralLp B hB t).comp (kernelRestrict htT)) (fun i ↦ ?_) f
  simp only [ContinuousLinearMap.comp_apply, kernelRestrict_stepIndicatorLp,
    wienerIntegralLp_stepIndicator]
  exact wienerIncrementLp_mem_lpMeas hB _
    ((hF _).mono ((Filtration.natural B _).mono (min_le_right _ _)))
    ((hF _).mono ((Filtration.natural B _).mono (min_le_right _ _)))

/-- The σ-algebra of the post-`t` increments `ω ↦ (B_{t+s} − B_t)_s`. -/
abbrev postσ (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (s : ℝ≥0) ↦ B (t + s) ω - B t ω) inferInstance

lemma postσ_le (hBm : ∀ s, Measurable (B s)) (t : ℝ≥0) : postσ B t ≤ mΩ :=
  Measurable.comap_le (.of_eval fun _ ↦ (hBm _).sub (hBm _))

lemma stronglyMeasurable_postσ (s : ℝ≥0) :
    StronglyMeasurable[postσ B t] fun ω ↦ B (t + s) ω - B t ω :=
  ((measurable_pi_apply s).comp
    (comap_measurable fun ω (s : ℝ≥0) ↦ B (t + s) ω - B t ω)).stronglyMeasurable

/-- The remainder `∫₀ᵀ f dB − ∫₀ᵗ f dB` of a step indicator is `postσ`-measurable: it is the
increment of the post-`t` process over `((s − t)⁺, (u − t)⁺]`. -/
lemma wienerIntegralLp_future_step_mem_lpMeas (hB : IsPreBrownianReal B μ) (htT : t ≤ T)
    (i : StepIndex T) :
    wienerIntegralLp B hB T (stepIndicatorLp T i)
        - wienerIntegralLp B hB t (kernelRestrict htT (stepIndicatorLp T i))
      ∈ lpMeas ℝ ℝ (postσ B t) 2 μ := by
  rw [mem_lpMeas_iff_aestronglyMeasurable, kernelRestrict_stepIndicatorLp,
    wienerIntegralLp_stepIndicator, wienerIntegralLp_stepIndicator]
  refine ((stronglyMeasurable_postσ (B := B) (t := t) (i.1.2 - t)).sub
    (stronglyMeasurable_postσ (B := B) (t := t) (i.1.1 - t))).aestronglyMeasurable.congr ?_
  filter_upwards [Lp.coeFn_sub (wienerIncrementLp B hB i) (wienerIncrementLp B hB (stepClip t i)),
    MemLp.coeFn_toLp (memLp_increment hB i.1.1 i.1.2),
    MemLp.coeFn_toLp (memLp_increment hB (stepClip t i).1.1 (stepClip t i).1.2)] with ω h1 h2 h3
  rw [h1, Pi.sub_apply]
  change _ = (wienerIncrementLp B hB i : Ω → ℝ) ω - _
  rw [show (wienerIncrementLp B hB i : Ω → ℝ) ω = B i.1.2 ω - B i.1.1 ω from h2,
    show (wienerIncrementLp B hB (stepClip t i) : Ω → ℝ) ω
      = B (min i.1.2 t) ω - B (min i.1.1 t) ω from h3]
  rcases le_total i.1.2 t with h | h <;> rcases le_total i.1.1 t with h' | h' <;>
    simp [tsub_eq_zero_of_le, add_tsub_cancel_of_le, *]

/-- The remainder `∫₀ᵀ f dB − ∫₀ᵗ f dB` of any kernel is `postσ`-measurable, hence independent of
the past. -/
lemma wienerIntegralLp_future_mem_lpMeas (hB : IsPreBrownianReal B μ)
    (hBm : ∀ s, Measurable (B s)) (htT : t ≤ T)
    (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) T))) :
    wienerIntegralLp B hB T f - wienerIntegralLp B hB t (kernelRestrict htT f)
      ∈ lpMeas ℝ ℝ (postσ B t) 2 μ :=
  mem_lpMeas_of_stepIndicator (postσ_le hBm t)
    (wienerIntegralLp B hB T - (wienerIntegralLp B hB t).comp (kernelRestrict htT))
    (fun i ↦ wienerIntegralLp_future_step_mem_lpMeas hB htT i) f

lemma integral_sq_Ioc_split (htT : t ≤ T) (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) T))) :
    ∫ s in Set.Ioc (0 : ℝ) T, f s ^ 2
      = (∫ s in Set.Ioc (0 : ℝ) t, f s ^ 2) + ∫ s in Set.Ioc (t : ℝ) T, f s ^ 2 := by
  have hsq : Integrable (fun s ↦ f s ^ 2) (volume.restrict (Set.Ioc (0 : ℝ) T)) :=
    (Lp.memLp f).integrable_sq
  have ht : (t : ℝ) ≤ T := NNReal.coe_le_coe.2 htT
  have h := setIntegral_union (μ := volume) (f := fun s ↦ f s ^ 2)
    (Set.disjoint_left.2 fun x (hx : x ∈ Set.Ioc (0 : ℝ) t) (hy : x ∈ Set.Ioc (t : ℝ) T) ↦
      absurd hx.2 (not_le.2 hy.1)) measurableSet_Ioc
    (hsq.mono_measure (Measure.restrict_mono (Set.Ioc_subset_Ioc_right ht) le_rfl))
    (hsq.mono_measure (Measure.restrict_mono (Set.Ioc_subset_Ioc_left t.coe_nonneg) le_rfl))
  rw [Set.Ioc_union_Ioc_eq_Ioc t.coe_nonneg ht] at h
  exact h

/-- The Wiener integral over `(0, t]` is `𝓕_t`-measurable. -/
lemma wienerIntegralLp_mem_lpMeas (hB : IsPreBrownianReal B μ) (hBm : ∀ s, Measurable (B s))
    (h : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) t))) :
    wienerIntegralLp B hB t h
      ∈ lpMeas ℝ ℝ (Filtration.natural B (fun s ↦ (hBm s).stronglyMeasurable) t) 2 μ := by
  have hF := Filtration.stronglyAdapted_natural (fun s ↦ (hBm s).stronglyMeasurable)
  refine mem_lpMeas_of_stepIndicator ((Filtration.natural B _).le t) (wienerIntegralLp B hB t)
    (fun i ↦ ?_) h
  rw [wienerIntegralLp_stepIndicator]
  exact wienerIncrementLp_mem_lpMeas hB _
    ((hF _).mono ((Filtration.natural B _).mono (i.2.1.trans i.2.2)))
    ((hF _).mono ((Filtration.natural B _).mono i.2.2))

/-- **The remainder factor.** For a `postσ`-measurable representative `N'` of the remainder
`∫₀ᵀ f dB − ∫₀ᵗ f dB`, the factor `e^{−cN'}` is integrable with mean `e^{c²∫_t^T f²/2}`: the
remainder is independent of the past part, and the product of the two factors is the Gaussian
exponential moment of `∫₀ᵀ f dB`. -/
lemma integral_exp_neg_future (hB : IsPreBrownianReal B μ) (hBm : ∀ s, Measurable (B s))
    (htT : t ≤ T) (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) T))) (c : ℝ) {N' : Ω → ℝ}
    (hN'm : StronglyMeasurable[postσ B t] N')
    (hNN' : ((wienerIntegralLp B hB T f
        - wienerIntegralLp B hB t (kernelRestrict htT f) : Lp ℝ 2 μ) : Ω → ℝ) =ᵐ[μ] N') :
    Integrable (fun ω ↦ Real.exp (-(c * N' ω))) μ ∧
      ∫ ω, Real.exp (-(c * N' ω)) ∂μ
        = Real.exp (c ^ 2 * (∫ s in Set.Ioc (t : ℝ) T, f s ^ 2) / 2) := by
  have hle := (Filtration.natural B (fun s ↦ (hBm s).stronglyMeasurable)).le t
  obtain ⟨P', hP'm, hPP'⟩ := mem_lpMeas_iff_aestronglyMeasurable.1
    (wienerIntegralLp_past_mem_lpMeas hB hBm htT f)
  have hW : (wienerIntegralLp B hB T f : Ω → ℝ) =ᵐ[μ] P' + N' := by
    filter_upwards [Lp.coeFn_sub (wienerIntegralLp B hB T f)
      (wienerIntegralLp B hB t (kernelRestrict htT f)), hPP', hNN'] with ω h1 h2 h3
    rw [Pi.add_apply, ← h2]
    rw [Pi.sub_apply] at h1
    linarith
  set E1 : Ω → ℝ := fun ω ↦ Real.exp (-(c * P' ω)) with hE1def
  set E2 : Ω → ℝ := fun ω ↦ Real.exp (-(c * N' ω)) with hE2def
  have hE1 : StronglyMeasurable[Filtration.natural B (fun s ↦ (hBm s).stronglyMeasurable) t] E1 :=
    Real.continuous_exp.comp_stronglyMeasurable (hP'm.const_mul c).neg
  have hE2 : StronglyMeasurable[postσ B t] E2 :=
    Real.continuous_exp.comp_stronglyMeasurable (hN'm.const_mul c).neg
  have hprod : (fun ω ↦ Real.exp (-(c * wienerIntegralLp B hB T f ω))) =ᵐ[μ] E1 * E2 := by
    filter_upwards [hW] with ω h
    rw [Pi.mul_apply, hE1def, hE2def]
    simp only
    rw [← Real.exp_add, h, Pi.add_apply]
    congr 1
    ring
  have hWint : Integrable (fun ω ↦ Real.exp (-(c * wienerIntegralLp B hB T f ω))) μ :=
    ((wienerIntegralLp_hasLaw_gaussian hB T f).integrable_fun_comp
      (integrable_exp_mul_gaussianReal (-c))).congr
      (ae_of_all _ fun ω ↦ by simp only [neg_mul])
  have hint : Integrable (E1 * E2) μ := hWint.congr hprod
  have hindep : Indep (postσ B t)
      (Filtration.natural B (fun s ↦ (hBm s).stronglyMeasurable) t) μ :=
    shift_indep_natural hB hBm t
  have hIndFun : IndepFun E1 E2 μ :=
    (IndepFun_iff_Indep _ _ _).2
      (indep_of_indep_of_le_right (indep_of_indep_of_le_left hindep.symm hE1.measurable.comap_le)
        hE2.measurable.comap_le)
  have hE1ae : AEStronglyMeasurable E1 μ := (hE1.mono hle).aestronglyMeasurable
  have hE2ae : AEStronglyMeasurable E2 μ := (hE2.mono (postσ_le hBm t)).aestronglyMeasurable
  have hE2int : Integrable E2 μ :=
    hIndFun.integrable_right_of_integrable_op (fun x y ↦ x * y) 1 one_ne_zero
      (fun x y ↦ by simp [eNorm_mul]) hint hE1ae hE2ae
      fun h ↦ by obtain ⟨ω, hω⟩ := h.exists; exact (Real.exp_pos _).ne' hω
  refine ⟨hE2int, ?_⟩
  have hI_W : ∫ ω, (E1 * E2) ω ∂μ = Real.exp (c ^ 2 * ‖f‖ ^ 2 / 2) := by
    rw [← integral_congr_ae hprod]
    have := integral_exp_mul_wienerIntegralLp hB T f (-c)
    simpa only [neg_mul, neg_sq] using this
  have hI_P : ∫ ω, E1 ω ∂μ
      = Real.exp (c ^ 2 * ‖kernelRestrict htT f‖ ^ 2 / 2) := by
    rw [show ∫ ω, E1 ω ∂μ = ∫ ω, Real.exp
        (-(c * wienerIntegralLp B hB t (kernelRestrict htT f) ω)) ∂μ from
      integral_congr_ae (hPP'.mono fun ω h ↦ by simp only [hE1def, h])]
    have := integral_exp_mul_wienerIntegralLp hB t (kernelRestrict htT f) (-c)
    simpa only [neg_mul, neg_sq] using this
  have hmul := hIndFun.integral_mul_eq_mul_integral hE1ae hE2ae
  rw [hI_W, hI_P] at hmul
  have hnorm : ‖f‖ ^ 2 = ‖kernelRestrict htT f‖ ^ 2 + ∫ s in Set.Ioc (t : ℝ) T, f s ^ 2 := by
    rw [lp_two_norm_sq, lp_two_norm_sq, integral_sq_Ioc_split htT f]
    congr 1
    exact integral_congr_ae ((kernelRestrict_coeFn htT f).mono fun x hx ↦ by simp only [hx])
  have hpos := Real.exp_pos (c ^ 2 * ‖kernelRestrict htT f‖ ^ 2 / 2)
  refine mul_left_cancel₀ hpos.ne' ?_
  rw [← hmul, ← Real.exp_add, hnorm]
  congr 1
  ring

/-- **The conditional Laplace transform of a Wiener integral.** Given the past `𝓕_t`, the
integral `∫₀ᵀ f dB` is its past part `∫₀ᵗ f dB` (the Wiener integral of the restricted kernel)
plus an independent centred Gaussian of variance `∫_t^T f²`; so, with a further past Wiener
integral `∫₀ᵗ h dB` carried along,

  `𝔼[e^{a + b∫₀ᵗ h dB − c∫₀ᵀ f dB} | 𝓕_t] = e^{a + b∫₀ᵗ h dB − c∫₀ᵗ f dB}·e^{c²∫_t^T f²/2}`

almost surely. -/
theorem condExp_exp_wienerIntegralLp (hB : IsPreBrownianReal B μ)
    (hBm : ∀ s, Measurable (B s)) (htT : t ≤ T)
    (h : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) t)))
    (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) T))) (a b c : ℝ) :
    μ[fun ω ↦ Real.exp (a + b * wienerIntegralLp B hB t h ω - c * wienerIntegralLp B hB T f ω)
        | Filtration.natural B (fun s ↦ (hBm s).stronglyMeasurable) t]
      =ᵐ[μ] fun ω ↦ Real.exp (a + b * wienerIntegralLp B hB t h ω
          - c * wienerIntegralLp B hB t (kernelRestrict htT f) ω)
        * Real.exp (c ^ 2 * (∫ s in Set.Ioc (t : ℝ) T, f s ^ 2) / 2) := by
  set 𝓕t := Filtration.natural B (fun s ↦ (hBm s).stronglyMeasurable) t
  have hle : 𝓕t ≤ mΩ := (Filtration.natural B _).le t
  obtain ⟨P', hP'm, hPP'⟩ := mem_lpMeas_iff_aestronglyMeasurable.1
    (wienerIntegralLp_past_mem_lpMeas hB hBm htT f)
  obtain ⟨H', hH'm, hHH'⟩ := mem_lpMeas_iff_aestronglyMeasurable.1
    (wienerIntegralLp_mem_lpMeas hB hBm h)
  obtain ⟨N', hN'm, hNN'⟩ := mem_lpMeas_iff_aestronglyMeasurable.1
    (wienerIntegralLp_future_mem_lpMeas hB hBm htT f)
  obtain ⟨hE2int, hI_N⟩ := integral_exp_neg_future hB hBm htT f c hN'm hNN'
  have hW : (wienerIntegralLp B hB T f : Ω → ℝ) =ᵐ[μ] P' + N' := by
    filter_upwards [Lp.coeFn_sub (wienerIntegralLp B hB T f)
      (wienerIntegralLp B hB t (kernelRestrict htT f)), hPP', hNN'] with ω h1 h2 h3
    rw [Pi.add_apply, ← h2]
    rw [Pi.sub_apply] at h1
    linarith
  set E1 : Ω → ℝ := fun ω ↦ Real.exp (a + b * H' ω - c * P' ω)
  set E2 : Ω → ℝ := fun ω ↦ Real.exp (-(c * N' ω))
  have hE1 : StronglyMeasurable[𝓕t] E1 :=
    Real.continuous_exp.comp_stronglyMeasurable
      ((stronglyMeasurable_const.add (hH'm.const_mul b)).sub (hP'm.const_mul c))
  have hE2 : StronglyMeasurable[postσ B t] E2 :=
    Real.continuous_exp.comp_stronglyMeasurable (hN'm.const_mul c).neg
  have hprod : (fun ω ↦ Real.exp (a + b * wienerIntegralLp B hB t h ω
      - c * wienerIntegralLp B hB T f ω)) =ᵐ[μ] E1 * E2 := by
    filter_upwards [hW, hHH'] with ω hw hh
    dsimp only [E1, E2, Pi.mul_apply]
    rw [← Real.exp_add, hw, hh, Pi.add_apply]
    congr 1
    ring
  -- `E1` is integrable: a Gaussian exponential moment
  have hlin : (wienerIntegralLp B hB t (b • h - c • kernelRestrict htT f) : Ω → ℝ)
      =ᵐ[μ] fun ω ↦ b * wienerIntegralLp B hB t h ω
        - c * wienerIntegralLp B hB t (kernelRestrict htT f) ω := by
    rw [map_sub, map_smul, map_smul]
    filter_upwards [Lp.coeFn_sub (b • wienerIntegralLp B hB t h)
      (c • wienerIntegralLp B hB t (kernelRestrict htT f)),
      Lp.coeFn_smul b (wienerIntegralLp B hB t h),
      Lp.coeFn_smul c (wienerIntegralLp B hB t (kernelRestrict htT f))] with ω h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
    rfl
  have hE1int : Integrable E1 μ :=
    (((wienerIntegralLp_hasLaw_gaussian hB t
      (b • h - c • kernelRestrict htT f)).integrable_fun_comp
        (integrable_exp_mul_gaussianReal 1)).const_mul (Real.exp a)).congr <| by
      filter_upwards [hlin, hPP', hHH'] with ω h1 h2 h3
      dsimp only [E1]
      rw [← Real.exp_add, one_mul, h1, ← h2, ← h3]
      congr 1
      ring
  refine (condExp_congr_ae hprod).trans
    ((condExp_mul_of_indep hle (postσ_le hBm t) (shift_indep_natural hB hBm t) hE1 hE2 hE1int
      hE2int).trans ?_)
  filter_upwards [hPP', hHH'] with ω hP hH
  rw [hI_N]
  simp only [E1, hP, hH]

end Closure

end MathFin
