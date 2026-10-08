/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Jointly measurable representatives of `L²`-valued curves

The regularized construction of `lem:regularised-forced` works with curves of
square-integrable fields. To compute with them pointwise, a strongly
measurable curve `s ↦ γ s ∈ L²(μ)` is represented by one jointly measurable
function `Γ(x, s)` whose slices are the classes `γ s`. The Bochner integral of
such a curve is then computed pointwise almost everywhere by integrating the
representative in the curve variable.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace CKN.Leray

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
  [NormedAddCommGroup E]

/-- The pointwise values of a simple curve of `L²` classes, written as a
finite sum of indicator functions of its fibers. -/
private theorem simpleCurve_eval_eq_sum (φ : SimpleFunc β (Lp E 2 μ)) (x : α) (s : β) :
    (φ s : α → E) x =
      ∑ c ∈ φ.range, ({t : β | φ t = c}.indicator (fun _ => (c : α → E) x) s) := by
  rw [Finset.sum_eq_single (φ s)]
  · simp
  · intro c _ hc
    have hs : s ∉ {t : β | φ t = c} := fun h => hc h.symm
    simp [Set.indicator_of_notMem hs]
  · intro h
    exact absurd (φ.mem_range_self s) h

/-- The pointwise evaluation of a simple curve of `L²` classes is jointly
strongly measurable. -/
private theorem simpleCurve_eval_stronglyMeasurable (φ : SimpleFunc β (Lp E 2 μ)) :
    StronglyMeasurable (fun p : α × β => (φ p.2 : α → E) p.1) := by
  have heq : (fun p : α × β => (φ p.2 : α → E) p.1) = fun p =>
      ∑ c ∈ φ.range, ((Set.univ ×ˢ {t : β | φ t = c}).indicator
        (fun q : α × β => (c : α → E) q.1) p) := by
    funext p
    rw [simpleCurve_eval_eq_sum φ p.1 p.2]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : φ p.2 = c
    · have h1 : p.2 ∈ {t : β | φ t = c} := h
      have h2 : p ∈ Set.univ ×ˢ {t : β | φ t = c} := ⟨Set.mem_univ _, h⟩
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
    · have h1 : p.2 ∉ {t : β | φ t = c} := h
      have h2 : p ∉ Set.univ ×ˢ {t : β | φ t = c} := fun hp => h hp.2
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
  rw [heq]
  refine Finset.stronglyMeasurable_fun_sum (f := fun (c : Lp E 2 μ) (p : α × β) =>
    (Set.univ ×ˢ {t : β | φ t = c}).indicator (fun q : α × β => (c : α → E) q.1) p)
    _ fun c _ => ?_
  exact ((Lp.stronglyMeasurable c).comp_measurable measurable_fst).indicator
    (MeasurableSet.univ.prod (φ.measurableSet_fiber c))

/-- Chebyshev and Borel-Cantelli: functions whose `L²` distances to a fixed
function are bounded by `4⁻ᵏ` converge to it almost everywhere. -/
private theorem ae_tendsto_of_eLpNorm_le_four_pow (g : ℕ → α → E) (h : α → E)
    (hbound : ∀ k, eLpNorm (g k - h) 2 μ ≤ ENNReal.ofReal ((1 / 4 : ℝ) ^ k)) :
    ∀ᵐ x ∂μ, Tendsto (fun k => g k x) atTop (𝓝 (h x)) := by
  let S : ℕ → Set α := fun k => {x | ENNReal.ofReal ((1 / 4 : ℝ) ^ k) ≤
    ‖(g k - h) x‖ₑ ^ (2 : ℝ≥0∞).toReal}
  have hS (k : ℕ) : μ (S k) ≤ ENNReal.ofReal ((1 / 4 : ℝ) ^ k) := by
    have hcheb := mul_meas_ge_le_pow_eLpNorm μ (p := 2) (by norm_num) (by norm_num)
      (f := g k - h) (ENNReal.ofReal ((1 / 4 : ℝ) ^ k))
    have hpow : eLpNorm (g k - h) 2 μ ^ (2 : ℝ≥0∞).toReal ≤
        ENNReal.ofReal ((1 / 4 : ℝ) ^ k) ^ (2 : ℝ≥0∞).toReal :=
      ENNReal.rpow_le_rpow (hbound k) (by norm_num)
    have hq : (0 : ℝ) < (1 / 4 : ℝ) ^ k := by positivity
    have hsq : ENNReal.ofReal ((1 / 4 : ℝ) ^ k) ^ (2 : ℝ≥0∞).toReal =
        ENNReal.ofReal ((1 / 4 : ℝ) ^ k) * ENNReal.ofReal ((1 / 4 : ℝ) ^ k) := by
      rw [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num, ENNReal.rpow_two, sq]
    have hne : ENNReal.ofReal ((1 / 4 : ℝ) ^ k) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]; exact hq
    have hmul : ENNReal.ofReal ((1 / 4 : ℝ) ^ k) * μ (S k) ≤
        ENNReal.ofReal ((1 / 4 : ℝ) ^ k) * ENNReal.ofReal ((1 / 4 : ℝ) ^ k) :=
      (hcheb.trans hpow).trans_eq hsq
    exact (ENNReal.mul_le_mul_iff_right hne ENNReal.ofReal_ne_top).1 hmul
  have hsum : ∑' k, μ (S k) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hS)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))]
    exact ENNReal.ofReal_ne_top
  have hnull := measure_setOfPred_frequently_eq_zero (μ := μ)
    (p := fun k x => x ∈ S k) hsum
  have hev : ∀ᵐ x ∂μ, ∀ᶠ k in atTop, x ∉ S k := by
    rw [ae_iff]
    have hset : {a | ¬ ∀ᶠ k in atTop, a ∉ S k} = {x | ∃ᶠ n in atTop, x ∈ S n} := by
      ext a
      simp only [Set.mem_ofPred_eq, Filter.not_eventually, not_not]
    rw [hset]
    exact hnull
  filter_upwards [hev] with x hx
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ hlim
  filter_upwards [hx] with k hk
  have hlt : ‖(g k - h) x‖ₑ ^ (2 : ℝ≥0∞).toReal < ENNReal.ofReal ((1 / 4 : ℝ) ^ k) :=
    lt_of_not_ge hk
  rw [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num, ← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)] at hlt
  have hlt' : ‖(g k - h) x‖ ^ (2 : ℝ) < (1 / 4 : ℝ) ^ k :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hlt
  have hsq : ‖g k x - h x‖ ^ 2 < ((1 / 2 : ℝ) ^ k) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
    simpa [Real.rpow_two] using hlt'
  exact (abs_lt_of_sq_lt_sq' hsq (by positivity)).2.le

/-- A strongly measurable curve of `L²` classes has a jointly strongly
measurable representative whose every slice is the class of the curve. -/
theorem exists_jointRep_of_stronglyMeasurable [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E] [Nonempty E]
    (γ : β → Lp E 2 μ) (hγ : StronglyMeasurable γ) :
    ∃ Γ : α × β → E, StronglyMeasurable Γ ∧
      ∀ s, (fun x => Γ (x, s)) =ᵐ[μ] γ s := by
  classical
  let φ : ℕ → SimpleFunc β (Lp E 2 μ) := hγ.approx
  have hφ : ∀ s, Tendsto (fun n => φ n s) atTop (𝓝 (γ s)) := hγ.tendsto_approx
  have hex : ∀ (k : ℕ) (s : β), ∃ n, dist (φ n s) (γ s) < (1 / 4 : ℝ) ^ k := by
    intro k s
    have hpos : (0 : ℝ) < (1 / 4 : ℝ) ^ k := by positivity
    obtain ⟨n, hn⟩ := (Metric.tendsto_atTop.1 (hφ s)) _ hpos
    exact ⟨n, hn n le_rfl⟩
  let N : ℕ → β → ℕ := fun k s => Nat.find (hex k s)
  have hNmeas : ∀ k, Measurable (N k) := by
    intro k
    refine measurable_find (hex k) fun n => ?_
    exact measurableSet_lt
      (((φ n).stronglyMeasurable.dist hγ).measurable) measurable_const
  have hNspec : ∀ k s, dist (φ (N k s) s) (γ s) < (1 / 4 : ℝ) ^ k :=
    fun k s => Nat.find_spec (hex k s)
  let A : (α × β) × ℕ → E := fun q => (φ q.2 q.1.2 : α → E) q.1.1
  have hA : Measurable A := by
    refine measurable_from_prod_countable_left fun n => ?_
    exact (simpleCurve_eval_stronglyMeasurable (φ n)).measurable
  let G : ℕ → α × β → E := fun k p => A (p, N k p.2)
  have hG : ∀ k, StronglyMeasurable (G k) := by
    intro k
    exact (hA.comp (measurable_id.prodMk ((hNmeas k).comp measurable_snd))).stronglyMeasurable
  refine ⟨fun p => limUnder atTop (fun k => G k p),
    StronglyMeasurable.limUnder hG, fun s => ?_⟩
  have hconv : ∀ᵐ x ∂μ, Tendsto (fun k => G k (x, s)) atTop (𝓝 ((γ s : α → E) x)) := by
    refine ae_tendsto_of_eLpNorm_le_four_pow (fun k x => G k (x, s)) (γ s) fun k => ?_
    have hdist := hNspec k s
    rw [Lp.dist_def] at hdist
    have hfin : eLpNorm ((φ (N k s) s : α → E) - (γ s : α → E)) 2 μ ≠ ⊤ :=
      ((Lp.memLp _).sub (Lp.memLp _)).eLpNorm_ne_top
    have hle : eLpNorm ((φ (N k s) s : α → E) - (γ s : α → E)) 2 μ ≤
        ENNReal.ofReal ((1 / 4 : ℝ) ^ k) := by
      rw [← ENNReal.ofReal_toReal hfin]
      exact ENNReal.ofReal_le_ofReal hdist.le
    exact hle
  filter_upwards [hconv] with x hx
  exact hx.limUnder_eq

/-- An almost everywhere strongly measurable curve of `L²` classes has a
jointly strongly measurable representative whose slices are the classes of
the curve for almost every value of the curve variable. -/
theorem exists_jointRep_of_aestronglyMeasurable [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E] [Nonempty E]
    {ν : Measure β} (γ : β → Lp E 2 μ) (hγ : AEStronglyMeasurable γ ν) :
    ∃ Γ : α × β → E, StronglyMeasurable Γ ∧
      ∀ᵐ s ∂ν, (fun x => Γ (x, s)) =ᵐ[μ] γ s := by
  obtain ⟨Γ, hΓ, hrep⟩ := exists_jointRep_of_stronglyMeasurable hγ.mk hγ.stronglyMeasurable_mk
  refine ⟨Γ, hΓ, ?_⟩
  filter_upwards [hγ.ae_eq_mk] with s hs
  rw [hs]
  exact hrep s

/-- On a set of finite measure, the integral of the norm of an `L²` class is
bounded by the square root of the measure times its `L²` norm. -/
theorem setIntegral_norm_le_sqrt_measure_mul_norm (f : Lp E 2 μ) {B : Set α}
    (hμB : μ B < ⊤) :
    ∫ x in B, ‖(f : α → E) x‖ ∂μ ≤ (μ B).toReal ^ (1 / 2 : ℝ) * ‖f‖ := by
  have hmeas : AEStronglyMeasurable (f : α → E) (μ.restrict B) :=
    (Lp.aestronglyMeasurable f).restrict
  have h12 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict B)
    (p := 1) (q := 2) (by norm_num) hmeas
  have hmono : eLpNorm (f : α → E) 2 (μ.restrict B) ≤ eLpNorm (f : α → E) 2 μ :=
    eLpNorm_mono_measure _ Measure.restrict_le_self
  rw [Measure.restrict_apply_univ] at h12
  have hexp : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by
    norm_num
  rw [hexp] at h12
  have hfin2 : eLpNorm (f : α → E) 2 μ ≠ ⊤ := (Lp.memLp f).eLpNorm_ne_top
  have hB : μ B ≠ ⊤ := hμB.ne
  have hle : eLpNorm (f : α → E) 1 (μ.restrict B) ≤
      eLpNorm (f : α → E) 2 μ * μ B ^ (1 / 2 : ℝ) :=
    h12.trans (mul_le_mul_left hmono _)
  have hfinR : eLpNorm (f : α → E) 2 μ * μ B ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top hfin2 (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hB)
  rw [integral_norm_eq_lintegral_enorm hmeas, ← eLpNorm_one_eq_lintegral_enorm hmeas]
  calc (eLpNorm (f : α → E) 1 (μ.restrict B)).toReal
      ≤ (eLpNorm (f : α → E) 2 μ * μ B ^ (1 / 2 : ℝ)).toReal :=
        ENNReal.toReal_mono hfinR hle
    _ = (μ B).toReal ^ (1 / 2 : ℝ) * ‖f‖ := by
        rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, Lp.norm_def, mul_comm]

/-- The representative of an integrable curve is integrable on the product of
a finite-measure set with the curve measure. -/
theorem integrable_jointRep_restrict_prod [SFinite μ] {ν : Measure β} [SFinite ν]
    (γ : β → Lp E 2 μ) (hγ : Integrable γ ν) (Γ : α × β → E)
    (hΓ : StronglyMeasurable Γ) (hrep : ∀ᵐ s ∂ν, (fun x => Γ (x, s)) =ᵐ[μ] γ s)
    {B : Set α} (hμB : μ B < ⊤) :
    Integrable Γ ((μ.restrict B).prod ν) := by
  have : IsFiniteMeasure (μ.restrict B) := ⟨by rw [Measure.restrict_apply_univ]; exact hμB⟩
  rw [integrable_prod_iff' hΓ.aestronglyMeasurable]
  constructor
  · filter_upwards [hrep] with s hs
    have hint : Integrable (γ s : α → E) (μ.restrict B) :=
      ((Lp.memLp (γ s)).restrict B).integrable (by norm_num)
    exact hint.congr (ae_restrict_of_ae hs.symm)
  · refine Integrable.mono' (hγ.norm.const_mul ((μ B).toReal ^ (1 / 2 : ℝ))) ?_ ?_
    · exact (StronglyMeasurable.integral_prod_left
        (f := fun x s => ‖Γ (x, s)‖) hΓ.norm).aestronglyMeasurable
    · filter_upwards [hrep] with s hs
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      have heq : ∫ x in B, ‖Γ (x, s)‖ ∂μ = ∫ x in B, ‖(γ s : α → E) x‖ ∂μ :=
        integral_congr_ae (ae_restrict_of_ae (by
          filter_upwards [hs] with x hx
          exact congrArg norm hx))
      rw [heq]
      exact setIntegral_norm_le_sqrt_measure_mul_norm (γ s) hμB

variable [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The Bochner integral of an integrable curve of `L²` classes is computed
almost everywhere by integrating a jointly measurable representative in the
curve variable. -/
theorem integral_ae_eq_integral_jointRep [SigmaFinite μ] {ν : Measure β} [SFinite ν]
    (γ : β → Lp E 2 μ) (hγ : Integrable γ ν) (Γ : α × β → E)
    (hΓ : StronglyMeasurable Γ) (hrep : ∀ᵐ s ∂ν, (fun x => Γ (x, s)) =ᵐ[μ] γ s) :
    ((∫ s, γ s ∂ν : Lp E 2 μ) : α → E) =ᵐ[μ] fun x => ∫ s, Γ (x, s) ∂ν := by
  let I : Lp E 2 μ := ∫ s, γ s ∂ν
  let H : α → E := fun x => ∫ s, Γ (x, s) ∂ν
  have hHint : ∀ B : Set α, μ B < ⊤ → IntegrableOn H B μ := fun B hμB =>
    (integrable_jointRep_restrict_prod γ hγ Γ hΓ hrep hμB).integral_prod_left
  have hIint : ∀ B : Set α, μ B < ⊤ → IntegrableOn (I : α → E) B μ := fun B hμB => by
    have : IsFiniteMeasure (μ.restrict B) := ⟨by rw [Measure.restrict_apply_univ]; exact hμB⟩
    exact ((Lp.memLp I).restrict B).integrable (by norm_num)
  have hkey : ∀ (c : E) (B : Set α), MeasurableSet B → μ B < ⊤ →
      ∫ x in B, inner ℂ c ((I : α → E) x) ∂μ = ∫ x in B, inner ℂ c (H x) ∂μ := by
    intro c B hB hμB
    have hprod := integrable_jointRep_restrict_prod γ hγ Γ hΓ hrep hμB
    rw [← L2.inner_indicatorConstLp_eq_setIntegral_inner ℂ I hB c hμB.ne]
    rw [← integral_inner hγ]
    have hstep : ∀ᵐ s ∂ν, inner ℂ (indicatorConstLp 2 hB hμB.ne c) (γ s) =
        ∫ x in B, inner ℂ c (Γ (x, s)) ∂μ := by
      filter_upwards [hrep] with s hs
      rw [L2.inner_indicatorConstLp_eq_setIntegral_inner ℂ (γ s) hB c hμB.ne]
      exact integral_congr_ae (ae_restrict_of_ae (by
        filter_upwards [hs] with x hx
        exact congrArg (inner ℂ c) hx.symm))
    rw [integral_congr_ae hstep]
    have hswap := integral_integral_swap (μ := μ.restrict B) (ν := ν)
      (f := fun x s => inner ℂ c (Γ (x, s))) (hprod.const_inner c)
    rw [← hswap]
    apply integral_congr_ae
    filter_upwards [hprod.prod_right_ae] with x hx
    exact integral_inner hx c
  have hzero : ∀ c : E, (fun x => inner ℂ c ((I : α → E) x - H x)) =ᵐ[μ] 0 := by
    intro c
    refine ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite (fun B _ hμB => ?_)
      (fun B hB hμB => ?_)
    · simp_rw [inner_sub_right]
      exact ((hIint B hμB).const_inner c).sub ((hHint B hμB).const_inner c)
    · simp_rw [inner_sub_right]
      rw [integral_sub ((hIint B hμB).const_inner c) ((hHint B hμB).const_inner c),
        hkey c B hB hμB, sub_self]
  let b := stdOrthonormalBasis ℂ E
  have hall : ∀ᵐ x ∂μ, ∀ i, inner ℂ (b i) ((I : α → E) x - H x) = 0 := by
    rw [ae_all_iff]
    intro i
    exact hzero (b i)
  filter_upwards [hall] with x hx
  have hsum := b.sum_repr' ((I : α → E) x - H x)
  simp only [hx, zero_smul, Finset.sum_const_zero] at hsum
  exact sub_eq_zero.1 hsum.symm

end CKN.Leray

end
