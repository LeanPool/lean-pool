/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.IsAdmissibleDrift
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Passing the extracted drift to the limit

Given drift fields `b n`, `divb n` on `Vec m × ℝ` satisfying the hypotheses of the generic drift
extraction (eventual continuity and per-slice bounds on compacts of `Vec m × (-∞, T]`, and the
per-slice weak divergence identity), and a subsequence `φ` along which the `T`-clamped time
primitives `∫_{T-1}^{min(τ, T)} b_{φ n}(x, s) ds` converge locally uniformly to limits `a`,
`adiv` whose a.e. time derivatives are `B`, `divB` (the time-primitive route to
`eq:aniso:comparison:drift`), this file proves:

* `CIV.tendsto_integral_mul_of_tendstoUniformlyOn_primitive`: `b_{φ n} → B` and
  `divb_{φ n} → divB` weakly against integrable compactly supported test functions on
  `Vec m × (-∞, T)`;
* `CIV.ae_weakDiv_of_tendstoUniformlyOn_primitive`: for a.e. `τ` in every compact
  `J ⊆ (-∞, T)`, `divB(·, τ)` is the weak divergence of `B(·, τ)`.
-/

public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open CKN

noncomputable section
namespace CIV

/-- The increment of a `T`-clamped primitive based at `T - 1` between two times is the integral
between the clamped times. -/
theorem primitive_sub_eq_of_continuousOn {g : ℝ → ℝ} {c T τ₁ τ₂ : ℝ} (hc : c ≤ T - 1)
    (hg : ContinuousOn g (Icc c T)) (h1 : c ≤ τ₁) (h2 : c ≤ τ₂) :
    (∫ s in (T - 1)..(min τ₂ T), g s) - ∫ s in (T - 1)..(min τ₁ T), g s =
      ∫ s in (min τ₁ T)..(min τ₂ T), g s := by
  have hmem : ∀ τ, c ≤ τ → min τ T ∈ Icc c T := fun τ hτ =>
    ⟨le_min hτ (by linarith only [hc]), min_le_right _ _⟩
  have hT : T - 1 ∈ Icc c T := ⟨hc, by linarith only []⟩
  have hii : ∀ u ∈ Icc c T, ∀ v ∈ Icc c T, IntervalIntegrable g volume u v :=
    fun u hu v hv => (hg.mono (uIcc_subset_Icc hu hv)).intervalIntegrable
  exact intervalIntegral.integral_interval_sub_left (hii _ hT _ (hmem _ h2))
    (hii _ hT _ (hmem _ h1))

/-- A `T`-clamped primitive of a function bounded by `M` on `[c, T]` is `M`-Lipschitz on `[c,
∞)`. -/
theorem abs_primitive_sub_le {g : ℝ → ℝ} {c T τ₁ τ₂ M : ℝ} (hc : c ≤ T - 1)
    (hg : ContinuousOn g (Icc c T)) (hM : ∀ s ∈ Icc c T, |g s| ≤ M) (h1 : c ≤ τ₁)
    (h2 : c ≤ τ₂) :
    |(∫ s in (T - 1)..(min τ₂ T), g s) - ∫ s in (T - 1)..(min τ₁ T), g s| ≤ M * |τ₂ - τ₁| := by
  rw [primitive_sub_eq_of_continuousOn hc hg h1 h2]
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM T ⟨by linarith only [hc], le_rfl⟩)
  have hmem : ∀ τ, c ≤ τ → min τ T ∈ Icc c T := fun τ hτ =>
    ⟨le_min hτ (by linarith only [hc]), min_le_right _ _⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := min τ₁ T) (b := min τ₂ T)
    (f := g) (C := M) (fun s hs => by
      rw [Real.norm_eq_abs]
      exact hM s (uIcc_subset_Icc (hmem _ h1) (hmem _ h2) (uIoc_subset_uIcc hs)))
  rw [Real.norm_eq_abs] at h
  have hmin : |min τ₂ T - min τ₁ T| ≤ |τ₂ - τ₁| := by
    have := abs_min_sub_min_le_max τ₂ T τ₁ T
    rwa [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at this
  exact h.trans (mul_le_mul_of_nonneg_left hmin hM0)

variable {m : ℕ} {T : ℝ}

/-- A locally uniform limit `p` of `T`-clamped time primitives of locally bounded, continuous
fields is Lipschitz in time, uniformly for `x` in a ball, on every half-line `[c, ∞)`. -/
theorem exists_lipschitz_time_of_tendstoUniformlyOn_primitive (f : ℕ → Vec m × ℝ → ℝ)
    (p : Vec m × ℝ → ℝ)
    (hcontS : ∀ K : Set (Vec m × ℝ), IsCompact K → K ⊆ univ ×ˢ Iic T →
      ∀ᶠ n in atTop, ContinuousOn (f n) K)
    (hbdS : ∀ K : Set (Vec m × ℝ), IsCompact K → K ⊆ univ ×ˢ Iic T →
      ∃ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, |f n z| ≤ M)
    (hconvS : ∀ K : Set (Vec m × ℝ), IsCompact K → TendstoUniformlyOn
      (fun n z => ∫ s in (T - 1)..(min z.2 T), f n (z.1, s)) p atTop K)
    (R c : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ Metric.closedBall (0 : Vec m) R, ∀ τ₁ τ₂ : ℝ, c ≤ τ₁ → c ≤ τ₂ →
      |p (x, τ₂) - p (x, τ₁)| ≤ L * |τ₂ - τ₁| := by
  set c' := min c (T - 1) with hc'
  have hc'T : c' ≤ T - 1 := min_le_right _ _
  set K : Set (Vec m × ℝ) := Metric.closedBall (0 : Vec m) R ×ˢ Icc c' T with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  have hKs : K ⊆ univ ×ˢ Iic T := fun z hz => ⟨mem_univ _, hz.2.2⟩
  obtain ⟨M, hM⟩ := hbdS K hKc hKs
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro x hx τ₁ τ₂ h1 h2
  have hlim : ∀ τ : ℝ, Tendsto (fun n => ∫ s in (T - 1)..(min τ T), f n (x, s)) atTop
      (nhds (p (x, τ))) := fun τ =>
    (hconvS {(x, τ)} isCompact_singleton).tendsto_at (mem_singleton _)
  have hlim2 := ((hlim τ₂).sub (hlim τ₁)).abs
  refine le_of_tendsto hlim2 ?_
  filter_upwards [hM, hcontS K hKc hKs] with n hn hcn
  have hgc : ContinuousOn (fun s => f n (x, s)) (Icc c' T) :=
    hcn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hx, hs⟩)
  exact abs_primitive_sub_le hc'T hgc
    (fun s hs => (hn (x, s) ⟨hx, hs⟩).trans (le_max_left _ _))
    ((min_le_left _ _).trans h1) ((min_le_left _ _).trans h2)

/-- Fundamental theorem of calculus for the limit primitive: if `G(x, ·)` is a.e. the time
derivative of `p(x, ·)`, then `∫_s^t G(x, τ) dτ = p(x, t) - p(x, s)` (the limit is Lipschitz in
time, hence absolutely continuous). -/
theorem integral_eq_sub_of_tendstoUniformlyOn_primitive (f : ℕ → Vec m × ℝ → ℝ)
    (p G : Vec m × ℝ → ℝ)
    (hcontS : ∀ K : Set (Vec m × ℝ), IsCompact K → K ⊆ univ ×ˢ Iic T →
      ∀ᶠ n in atTop, ContinuousOn (f n) K)
    (hbdS : ∀ K : Set (Vec m × ℝ), IsCompact K → K ⊆ univ ×ˢ Iic T →
      ∃ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, |f n z| ≤ M)
    (hconvS : ∀ K : Set (Vec m × ℝ), IsCompact K → TendstoUniformlyOn
      (fun n z => ∫ s in (T - 1)..(min z.2 T), f n (z.1, s)) p atTop K)
    (hGd : ∀ c d : ℝ, c ≤ d → ∀ᵐ τ ∂(volume.restrict (Icc c d)),
      ∀ x, HasDerivAt (fun τ' => p (x, τ')) (G (x, τ)) τ)
    (x : Vec m) {s t : ℝ} (hst : s ≤ t) :
    ∫ τ in s..t, G (x, τ) = p (x, t) - p (x, s) := by
  obtain ⟨L, hL0, hL⟩ := exists_lipschitz_time_of_tendstoUniformlyOn_primitive f p hcontS hbdS
    hconvS ‖x‖ s
  have hx : x ∈ Metric.closedBall (0 : Vec m) ‖x‖ := by simp
  have hlip : LipschitzOnWith L.toNNReal (fun τ => p (x, τ)) (uIcc s t) := by
    refine LipschitzOnWith.of_dist_le_mul fun τ₁ h1 τ₂ h2 => ?_
    rw [uIcc_of_le hst] at h1 h2
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hL0]
    exact hL x hx τ₂ τ₁ h2.1 h1.1
  rw [← hlip.absolutelyContinuousOnInterval.integral_deriv_eq_sub]
  refine intervalIntegral.integral_congr_ae ?_
  have h := hGd s t hst
  rw [ae_restrict_iff' measurableSet_Icc] at h
  filter_upwards [h] with τ hτ hτmem
  rw [uIoc_of_le hst] at hτmem
  exact ((hτ (Ioc_subset_Icc_self hτmem)) x).deriv.symm

/-- A property holding for a.e. time in `[c, d]` holds for a.e. point of `Vec m × [c, d]`. -/
theorem ae_restrict_univ_prod_of_ae {Q : ℝ → Prop} {c d : ℝ}
    (h : ∀ᵐ τ ∂(volume.restrict (Icc c d)), Q τ) :
    ∀ᵐ z ∂((volume : Measure (Vec m × ℝ)).restrict (univ ×ˢ Icc c d)), Q z.2 := by
  have heq : (volume : Measure (Vec m × ℝ)).restrict (univ ×ˢ Icc c d) =
      (volume : Measure (Vec m)).prod (volume.restrict (Icc c d)) := by
    show (volume.prod volume).restrict (univ ×ˢ Icc c d) = _
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [heq]
  exact (Measure.quasiMeasurePreserving_snd).ae h

/-- A measurable field bounded for a.e. time in `[s, t]` is integrable on `A × (s, t]` for every
`A` of finite measure. -/
theorem integrableOn_prod_Ioc_of_ae_bound {G : Vec m × ℝ → ℝ} (hGm : Measurable G)
    {s t Λ : ℝ} (hΛ : ∀ᵐ τ ∂(volume.restrict (Icc s t)), ∀ x, |G (x, τ)| ≤ Λ)
    {A : Set (Vec m)} (hvolA : volume A < ∞) :
    IntegrableOn G (A ×ˢ Ioc s t) := by
  have hvol : (volume : Measure (Vec m × ℝ)) (A ×ˢ Ioc s t) ≠ ∞ := by
    show (volume.prod volume) (A ×ˢ Ioc s t) ≠ ∞
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hvolA.ne measure_Ioc_lt_top.ne
  have hrect : A ×ˢ Ioc s t ⊆ univ ×ˢ Icc s t :=
    prod_mono (subset_univ _) Ioc_subset_Icc_self
  refine Measure.integrableOn_of_bounded hvol hGm.aestronglyMeasurable (M := Λ) ?_
  have h := ae_restrict_univ_prod_of_ae (m := m) hΛ
  filter_upwards [ae_mono (Measure.restrict_mono hrect le_rfl) h] with z hz
  rw [Real.norm_eq_abs]
  exact hz z.1

/-- Convergence of the integrals of the fields over a bounded space-time rectangle `A × (s, t]`
with `t ≤ T`: by Fubini both sides are `∫_A` of primitive increments, which converge uniformly. -/
theorem tendsto_setIntegral_prod_Ioc_of_primitive (f : ℕ → Vec m × ℝ → ℝ)
    (p G : Vec m × ℝ → ℝ)
    (hcontS : ∀ K : Set (Vec m × ℝ), IsCompact K → K ⊆ univ ×ˢ Iic T →
      ∀ᶠ n in atTop, ContinuousOn (f n) K)
    (hbdS : ∀ K : Set (Vec m × ℝ), IsCompact K → K ⊆ univ ×ˢ Iic T →
      ∃ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, |f n z| ≤ M)
    (hconvS : ∀ K : Set (Vec m × ℝ), IsCompact K → TendstoUniformlyOn
      (fun n z => ∫ s in (T - 1)..(min z.2 T), f n (z.1, s)) p atTop K)
    (hpc : Continuous p) (hGm : Measurable G)
    (hGd : ∀ c d : ℝ, c ≤ d → ∀ᵐ τ ∂(volume.restrict (Icc c d)),
      ∀ x, HasDerivAt (fun τ' => p (x, τ')) (G (x, τ)) τ)
    (hGb : ∀ c d : ℝ, c ≤ d → ∃ Λ : ℝ, ∀ᵐ τ ∂(volume.restrict (Icc c d)), ∀ x, |G (x, τ)| ≤ Λ)
    {R s t : ℝ} (hst : s ≤ t) (htT : t ≤ T) {A : Set (Vec m)} (hA : MeasurableSet A)
    (hAR : A ⊆ Metric.closedBall (0 : Vec m) R) :
    Tendsto (fun n => ∫ z in A ×ˢ Ioc s t, f n z) atTop (nhds (∫ z in A ×ˢ Ioc s t, G z)) := by
  have hvolA : volume A < ∞ := (measure_mono hAR).trans_lt measure_closedBall_lt_top
  obtain ⟨Λ, hΛ⟩ := hGb s t hst
  have hGint : IntegrableOn G (A ×ˢ Ioc s t) := integrableOn_prod_Ioc_of_ae_bound hGm hΛ hvolA
  have hGeq : ∫ z in A ×ˢ Ioc s t, G z = ∫ x in A, (p (x, t) - p (x, s)) := by
    rw [show (volume : Measure (Vec m × ℝ)) = volume.prod volume from rfl] at hGint ⊢
    rw [setIntegral_prod _ hGint]
    refine setIntegral_congr_fun hA fun x _ => ?_
    rw [← intervalIntegral.integral_of_le hst]
    exact integral_eq_sub_of_tendstoUniformlyOn_primitive f p G hcontS hbdS hconvS hGd x hst
  rw [hGeq]
  -- the finite side
  set c' := min s (T - 1) with hc'
  have hc'T : c' ≤ T - 1 := min_le_right _ _
  set K : Set (Vec m × ℝ) := Metric.closedBall (0 : Vec m) R ×ˢ Icc c' T with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  have hKs : K ⊆ univ ×ˢ Iic T := fun z hz => ⟨mem_univ _, hz.2.2⟩
  have hrK : A ×ˢ Ioc s t ⊆ K := prod_mono hAR fun τ hτ =>
    ⟨(min_le_left _ _).trans hτ.1.le, hτ.2.trans htT⟩
  have hsT : s ≤ T := hst.trans htT
  have hfeq : ∀ᶠ n in atTop, IntegrableOn (fun x => ∫ τ in Ioc s t, f n (x, τ)) A ∧
      ∫ z in A ×ˢ Ioc s t, f n z = ∫ x in A, ∫ τ in Ioc s t, f n (x, τ) ∧
      ∀ x ∈ A, ∫ τ in Ioc s t, f n (x, τ) =
        (∫ σ in (T - 1)..(min t T), f n (x, σ)) - ∫ σ in (T - 1)..(min s T), f n (x, σ) := by
    filter_upwards [hcontS K hKc hKs] with n hn
    have hint : IntegrableOn (f n) (A ×ˢ Ioc s t) := (hn.integrableOn_compact hKc).mono_set hrK
    refine ⟨?_, ?_, ?_⟩
    · have h1 : Integrable (f n) ((volume.restrict A).prod (volume.restrict (Ioc s t))) := by
        rw [Measure.prod_restrict]; exact hint
      exact h1.integral_prod_left
    · exact setIntegral_prod _ hint
    · intro x hx
      have hg : ContinuousOn (fun σ => f n (x, σ)) (Icc c' T) :=
        hn.comp (continuous_const.prodMk continuous_id).continuousOn (fun σ hσ => ⟨hAR hx, hσ⟩)
      rw [primitive_sub_eq_of_continuousOn hc'T hg (min_le_left _ _) ((min_le_left _ _).trans hst),
        min_eq_left hsT, min_eq_left htT, intervalIntegral.integral_of_le hst]
  have hpint : IntegrableOn (fun x => p (x, t) - p (x, s)) A :=
    ((((hpc.comp (continuous_id.prodMk continuous_const)).sub
      (hpc.comp (continuous_id.prodMk continuous_const))).continuousOn).integrableOn_compact
      (isCompact_closedBall (0 : Vec m) R)).mono_set hAR
  set K2 : Set (Vec m × ℝ) := Metric.closedBall (0 : Vec m) R ×ˢ {s, t} with hK2
  have hK2c : IsCompact K2 := (isCompact_closedBall _ _).prod (Set.toFinite _).isCompact
  have hunif := Metric.tendstoUniformlyOn_iff.mp (hconvS K2 hK2c)
  rw [Metric.tendsto_nhds]
  intro ε hε
  set V := volume.real A + 1 with hV
  have hV0 : 0 < V := by positivity
  filter_upwards [hfeq, hunif (ε / (4 * V)) (by positivity)] with n hn hu
  obtain ⟨hDint, hint_eq, hDeq⟩ := hn
  rw [hint_eq, Real.dist_eq, ← integral_sub hDint hpint]
  have hbound : ∀ x ∈ A, ‖(∫ τ in Ioc s t, f n (x, τ)) - (p (x, t) - p (x, s))‖ ≤
      ε / (2 * V) := by
    intro x hx
    rw [hDeq x hx, Real.norm_eq_abs]
    have h1 := hu (x, t) ⟨hAR hx, by simp⟩
    have h2 := hu (x, s) ⟨hAR hx, by simp⟩
    rw [Real.dist_eq] at h1 h2
    simp only at h1 h2
    have e : ε / (2 * V) = ε / (4 * V) + ε / (4 * V) := by field_simp; ring
    rw [e, abs_le]
    constructor <;>
    · have := abs_lt.mp h1; have := abs_lt.mp h2
      linarith only [(abs_lt.mp h1).1, (abs_lt.mp h1).2, (abs_lt.mp h2).1, (abs_lt.mp h2).2]
  have := norm_setIntegral_le_of_norm_le_const hvolA hbound
  rw [Real.norm_eq_abs] at this
  refine lt_of_le_of_lt this ?_
  have hVA : volume.real A < V := by rw [hV]; linarith only []
  have hA0 : 0 ≤ volume.real A := measureReal_nonneg
  calc ε / (2 * V) * volume.real A ≤ ε / (2 * V) * V := by gcongr
    _ = ε / 2 := by field_simp
    _ < ε := by linarith only [hε]

/-- Convergence of the integrals of the fields over `E ∩ (B_R × (a₀, b₀])` for every measurable
`E`, by the π-λ theorem from the rectangles `A × (l, u]`; the countable disjoint unions pass to
the limit by dominated convergence of series, using the uniform bound on the fields. -/
theorem tendsto_setIntegral_inter_box_of_primitive (f : ℕ → Vec m × ℝ → ℝ)
    (p G : Vec m × ℝ → ℝ)
    (hcontS : ∀ K : Set (Vec m × ℝ), IsCompact K → K ⊆ univ ×ˢ Iic T →
      ∀ᶠ n in atTop, ContinuousOn (f n) K)
    (hbdS : ∀ K : Set (Vec m × ℝ), IsCompact K → K ⊆ univ ×ˢ Iic T →
      ∃ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, |f n z| ≤ M)
    (hconvS : ∀ K : Set (Vec m × ℝ), IsCompact K → TendstoUniformlyOn
      (fun n z => ∫ s in (T - 1)..(min z.2 T), f n (z.1, s)) p atTop K)
    (hpc : Continuous p) (hGm : Measurable G)
    (hGd : ∀ c d : ℝ, c ≤ d → ∀ᵐ τ ∂(volume.restrict (Icc c d)),
      ∀ x, HasDerivAt (fun τ' => p (x, τ')) (G (x, τ)) τ)
    (hGb : ∀ c d : ℝ, c ≤ d → ∃ Λ : ℝ, ∀ᵐ τ ∂(volume.restrict (Icc c d)), ∀ x, |G (x, τ)| ≤ Λ)
    {R a₀ b₀ : ℝ} (hab : a₀ ≤ b₀) (hbT : b₀ ≤ T) (E : Set (Vec m × ℝ)) (hE : MeasurableSet E) :
    Tendsto (fun n => ∫ z in E ∩ (Metric.closedBall (0 : Vec m) R ×ˢ Ioc a₀ b₀), f n z) atTop
      (nhds (∫ z in E ∩ (Metric.closedBall (0 : Vec m) R ×ˢ Ioc a₀ b₀), G z)) := by
  set Q : Set (Vec m × ℝ) := Metric.closedBall (0 : Vec m) R ×ˢ Ioc a₀ b₀ with hQ
  have hQm : MeasurableSet Q := measurableSet_closedBall.prod measurableSet_Ioc
  have hvolB : volume (Metric.closedBall (0 : Vec m) R) < ∞ := measure_closedBall_lt_top
  have hvolQ : volume Q < ∞ := by
    show (volume.prod volume) Q < ∞
    rw [hQ, Measure.prod_prod]
    exact ENNReal.mul_lt_top hvolB measure_Ioc_lt_top
  set c' := min a₀ (T - 1) with hc'
  set K : Set (Vec m × ℝ) := Metric.closedBall (0 : Vec m) R ×ˢ Icc c' T with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  have hKs : K ⊆ univ ×ˢ Iic T := fun z hz => ⟨mem_univ _, hz.2.2⟩
  have hQK : Q ⊆ K := prod_mono subset_rfl fun τ hτ =>
    ⟨(min_le_left _ _).trans hτ.1.le, hτ.2.trans hbT⟩
  obtain ⟨M, hM⟩ := hbdS K hKc hKs
  obtain ⟨Λ, hΛ⟩ := hGb a₀ b₀ hab
  have hGQ : IntegrableOn G Q := integrableOn_prod_Ioc_of_ae_bound hGm hΛ hvolB
  have hfQ : ∀ᶠ n in atTop, IntegrableOn (f n) Q ∧ ∀ z ∈ Q, |f n z| ≤ M := by
    filter_upwards [hcontS K hKc hKs, hM] with n hn hMn
    exact ⟨(hn.integrableOn_compact hKc).mono_set hQK, fun z hz => hMn z (hQK hz)⟩
  have hempty : ∀ S : Set (Vec m × ℝ), S = ∅ →
      Tendsto (fun n => ∫ z in S, f n z) atTop (nhds (∫ z in S, G z)) := by
    rintro S rfl
    simp only [Measure.restrict_empty, integral_zero_measure]
    exact tendsto_const_nhds
  have hPQ : Tendsto (fun n => ∫ z in Q, f n z) atTop (nhds (∫ z in Q, G z)) :=
    tendsto_setIntegral_prod_Ioc_of_primitive f p G hcontS hbdS hconvS hpc hGm hGd hGb hab hbT
      measurableSet_closedBall subset_rfl
  -- the generating π-system of rectangles `A × (l, u]`
  set D : Set (Set ℝ) := {S | ∃ l u, l < u ∧ Ioc l u = S} with hD
  have hDgen : MeasurableSpace.generateFrom D = (inferInstance : MeasurableSpace ℝ) :=
    (borel_eq_generateFrom_Ioc ℝ).symm.trans BorelSpace.measurable_eq.symm
  have hDspan : IsCountablySpanning D := by
    refine ⟨fun n : ℕ => Ioc (-(n : ℝ) - 1) n, fun n => ⟨_, _, by linarith only [], rfl⟩, ?_⟩
    refine eq_univ_of_forall fun x => mem_iUnion.2 ⟨⌈|x|⌉₊, ?_⟩
    have h1 := Nat.le_ceil |x|
    exact ⟨by linarith only [h1, neg_abs_le x], (le_abs_self x).trans h1⟩
  have hDpi : IsPiSystem D := isPiSystem_Ioc id id
  have hgen := (generateFrom_eq_prod (α := Vec m) MeasurableSpace.generateFrom_measurableSet hDgen
    isCountablySpanning_measurableSet hDspan).symm
  refine MeasurableSpace.induction_on_inter (C := fun E _ => Tendsto
      (fun n => ∫ z in E ∩ Q, f n z) atTop (nhds (∫ z in E ∩ Q, G z)))
    hgen ((MeasurableSpace.isPiSystem_measurableSet (α := Vec m)).prod hDpi) ?_ ?_ ?_ ?_ E hE
  · exact hempty _ (empty_inter _)
  · rintro _ ⟨A, hA, _, ⟨l, u, -, rfl⟩, rfl⟩
    have hrw : A ×ˢ Ioc l u ∩ Q =
        (A ∩ Metric.closedBall (0 : Vec m) R) ×ˢ Ioc (max l a₀) (min u b₀) := by
      rw [hQ, prod_inter_prod, Ioc_inter_Ioc]
    rw [hrw]
    by_cases hlt : max l a₀ ≤ min u b₀
    · exact tendsto_setIntegral_prod_Ioc_of_primitive f p G hcontS hbdS hconvS hpc hGm hGd hGb
        hlt ((min_le_right _ _).trans hbT) ((show MeasurableSet A from hA).inter
          measurableSet_closedBall)
        inter_subset_right
    · refine hempty _ ?_
      rw [Ioc_eq_empty (fun h => hlt h.le), prod_empty]
  · intro E' hE' hP
    have hrw : E'ᶜ ∩ Q = Q \ (E' ∩ Q) := by
      ext z; simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff]; tauto
    rw [hrw, setIntegral_sdiff (hE'.inter hQm) hGQ inter_subset_right]
    refine Tendsto.congr' ?_ (hPQ.sub hP)
    filter_upwards [hfQ] with n hn
    rw [setIntegral_sdiff (hE'.inter hQm) hn.1 inter_subset_right]
  · intro F hFd hFm hP
    have hrw : (⋃ i, F i) ∩ Q = ⋃ i, (F i ∩ Q) := iUnion_inter _ _
    have hdisj : Pairwise (Function.onFun Disjoint fun i => F i ∩ Q) :=
      fun i j hij => (hFd hij).mono inter_subset_left inter_subset_left
    have hmeas : ∀ i, MeasurableSet (F i ∩ Q) := fun i => (hFm i).inter hQm
    have hsub : (⋃ i, (F i ∩ Q)) ⊆ Q := iUnion_subset fun i => inter_subset_right
    rw [hrw, integral_iUnion hmeas hdisj (hGQ.mono_set hsub)]
    have hsum : Summable fun i => M * volume.real (F i ∩ Q) := by
      refine Summable.mul_left _ (ENNReal.summable_toReal ?_)
      rw [← measure_iUnion hdisj hmeas]
      exact (lt_of_le_of_lt (measure_mono hsub) hvolQ).ne
    have hlim := tendsto_tsum_of_dominated_convergence (f := fun n i => ∫ z in F i ∩ Q, f n z)
      hsum hP (by
        filter_upwards [hfQ] with n hn i
        have hfin : volume (F i ∩ Q) < ∞ := lt_of_le_of_lt (measure_mono inter_subset_right) hvolQ
        exact norm_setIntegral_le_of_norm_le_const hfin fun z hz => by
          rw [Real.norm_eq_abs]; exact hn.2 z hz.2)
    refine Tendsto.congr' ?_ hlim
    filter_upwards [hfQ] with n hn
    rw [integral_iUnion hmeas hdisj (hn.1.mono_set hsub)]

/-- Testing a weight bounded by `C` against two integrable functions: the difference of the two
pairings is at most `C` times the `L¹` distance. -/
theorem abs_integral_mul_sub_integral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F H w : α → ℝ} {C : ℝ} (hF : Integrable F μ) (hH : Integrable H μ)
    (hw : AEStronglyMeasurable w μ) (hwb : ∀ᵐ z ∂μ, ‖w z‖ ≤ C) :
    |(∫ z, F z * w z ∂μ) - ∫ z, H z * w z ∂μ| ≤ C * ∫ z, ‖F z - H z‖ ∂μ := by
  rw [← integral_sub (hF.mul_bdd hw hwb) (hH.mul_bdd hw hwb), ← integral_const_mul,
    ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le ((hF.sub hH).norm.const_mul C) ?_
  filter_upwards [hwb] with z hz
  rw [← sub_mul, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)

/-- A sequence uniformly bounded by `M` (eventually) whose integrals over every measurable set of
finite measure converge to those of a limit bounded by `M` converges weakly against every
integrable function. -/
theorem tendsto_integral_mul_of_forall_setIntegral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f : ℕ → α → ℝ) (G : α → ℝ) {M : ℝ}
    (hf : ∀ᶠ n in atTop, AEStronglyMeasurable (f n) μ ∧ ∀ᵐ z ∂μ, ‖f n z‖ ≤ M)
    (hG : AEStronglyMeasurable G μ) (hGb : ∀ᵐ z ∂μ, ‖G z‖ ≤ M)
    (hset : ∀ E : Set α, MeasurableSet E → μ E < ∞ →
      Tendsto (fun n => ∫ z in E, f n z ∂μ) atTop (nhds (∫ z in E, G z ∂μ)))
    {g : α → ℝ} (hg : Integrable g μ) :
    Tendsto (fun n => ∫ z, g z * f n z ∂μ) atTop (nhds (∫ z, g z * G z ∂μ)) := by
  refine Integrable.induction (P := fun h => Tendsto (fun n => ∫ z, h z * f n z ∂μ) atTop
    (nhds (∫ z, h z * G z ∂μ))) ?_ ?_ ?_ ?_ hg
  · intro c E hE hEμ
    have key : ∀ w : α → ℝ, ∫ z, E.indicator (fun _ => c) z * w z ∂μ = c * ∫ z in E, w z ∂μ := by
      intro w
      simp_rw [← indicator_mul_left]
      rw [integral_indicator hE, integral_const_mul]
    simp_rw [key]
    exact (hset E hE hEμ).const_mul c
  · intro h₁ h₂ _ hi₁ hi₂ hP₁ hP₂
    have hG' : ∫ z, (h₁ + h₂) z * G z ∂μ = ∫ z, h₁ z * G z ∂μ + ∫ z, h₂ z * G z ∂μ := by
      simp only [Pi.add_apply, add_mul]
      exact integral_add (hi₁.mul_bdd hG hGb) (hi₂.mul_bdd hG hGb)
    rw [hG']
    refine Tendsto.congr' ?_ (hP₁.add hP₂)
    filter_upwards [hf] with n hn
    simp only [Pi.add_apply, add_mul]
    exact (integral_add (hi₁.mul_bdd hn.1 hn.2) (hi₂.mul_bdd hn.1 hn.2)).symm
  · refine isClosed_of_closure_subset fun F hF => ?_
    rw [Metric.mem_closure_iff] at hF
    show Tendsto _ _ _
    rw [Metric.tendsto_nhds]
    intro ε hε
    set C := |M| + 1 with hC
    have hC0 : 0 < C := by positivity
    have hMC : M ≤ C := by rw [hC]; linarith only [le_abs_self M]
    obtain ⟨H, hH, hdist⟩ := hF (ε / (3 * C)) (by positivity)
    have hH' : Tendsto (fun n => ∫ z, H z * f n z ∂μ) atTop (nhds (∫ z, H z * G z ∂μ)) := hH
    rw [L1.dist_eq_integral_dist] at hdist
    simp_rw [dist_eq_norm] at hdist
    filter_upwards [hf, Metric.tendsto_nhds.mp hH' (ε / 3) (by positivity)] with n hn hHn
    rw [Real.dist_eq] at hHn ⊢
    have h1 := abs_integral_mul_sub_integral_mul_le (L1.integrable_coeFn F)
      (L1.integrable_coeFn H) hn.1 (hn.2.mono fun z hz => hz.trans hMC)
    have h2 := abs_integral_mul_sub_integral_mul_le (L1.integrable_coeFn F)
      (L1.integrable_coeFn H) hG (hGb.mono fun z hz => hz.trans hMC)
    have h3 : C * ∫ z, ‖F z - H z‖ ∂μ ≤ ε / 3 := by
      have := mul_lt_mul_of_pos_left hdist hC0
      rw [show C * (ε / (3 * C)) = ε / 3 by field_simp] at this
      exact this.le
    rw [abs_le] at h1 h2
    rw [abs_lt] at hHn ⊢
    constructor
    · linarith only [h1.1, h1.2, h2.1, h2.2, h3, hHn.1, hHn.2]
    · linarith only [h1.1, h1.2, h2.1, h2.2, h3, hHn.1, hHn.2]
  · intro h₁ h₂ heq _ hP
    have e : ∀ w : α → ℝ, ∫ z, h₁ z * w z ∂μ = ∫ z, h₂ z * w z ∂μ := fun w =>
      integral_congr_ae (heq.mono fun z hz => by simp only [hz])
    simp_rw [← e]
    exact hP

/-- Scalar weak convergence: fields with locally bounded, eventually continuous restrictions to
`Vec m × (-∞, T]` whose `T`-clamped time primitives converge locally uniformly to `p` converge
weakly, against every integrable compactly supported `g` with support in `Vec m × (-∞, T]`, to
the a.e. time derivative `G` of `p`. -/
theorem tendsto_integral_mul_of_tendstoUniformlyOn_primitive_scalar (f : ℕ → Vec m × ℝ → ℝ)
    (p G : Vec m × ℝ → ℝ)
    (hcontS : ∀ K : Set (Vec m × ℝ), IsCompact K → K ⊆ univ ×ˢ Iic T →
      ∀ᶠ n in atTop, ContinuousOn (f n) K)
    (hbdS : ∀ K : Set (Vec m × ℝ), IsCompact K → K ⊆ univ ×ˢ Iic T →
      ∃ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, |f n z| ≤ M)
    (hconvS : ∀ K : Set (Vec m × ℝ), IsCompact K → TendstoUniformlyOn
      (fun n z => ∫ s in (T - 1)..(min z.2 T), f n (z.1, s)) p atTop K)
    (hpc : Continuous p) (hGm : Measurable G)
    (hGd : ∀ c d : ℝ, c ≤ d → ∀ᵐ τ ∂(volume.restrict (Icc c d)),
      ∀ x, HasDerivAt (fun τ' => p (x, τ')) (G (x, τ)) τ)
    (hGb : ∀ c d : ℝ, c ≤ d → ∃ Λ : ℝ, ∀ᵐ τ ∂(volume.restrict (Icc c d)), ∀ x, |G (x, τ)| ≤ Λ)
    {g : Vec m × ℝ → ℝ} (hg : Integrable g) (hgc : HasCompactSupport g)
    (hgs : tsupport g ⊆ univ ×ˢ Iic T) :
    Tendsto (fun n => ∫ z, g z * f n z) atTop (nhds (∫ z, g z * G z)) := by
  obtain ⟨R, hR⟩ := (hgc.isCompact.image continuous_fst).isBounded.subset_closedBall
    (0 : Vec m)
  obtain ⟨a, ha⟩ := (hgc.isCompact.image continuous_snd).bddBelow
  set a₀ := min (a - 1) (T - 1) with ha₀
  have ha₀T : a₀ ≤ T := (min_le_right _ _).trans (by linarith only [])
  set Q : Set (Vec m × ℝ) := Metric.closedBall (0 : Vec m) R ×ˢ Ioc a₀ T with hQ
  have hQm : MeasurableSet Q := measurableSet_closedBall.prod measurableSet_Ioc
  have hgQ : tsupport g ⊆ Q := fun z hz =>
    ⟨hR (mem_image_of_mem _ hz),
      lt_of_lt_of_le (by linarith only [min_le_left (a - 1) (T - 1)])
        (ha (mem_image_of_mem _ hz)), (hgs hz).2⟩
  have hcompl : ∀ w : Vec m × ℝ → ℝ, ∫ z in Q, g z * w z = ∫ z, g z * w z := fun w =>
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hgQ h)), zero_mul]
  simp_rw [← hcompl]
  set c' := min a₀ (T - 1) with hc'
  set K : Set (Vec m × ℝ) := Metric.closedBall (0 : Vec m) R ×ˢ Icc c' T with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  have hKs : K ⊆ univ ×ˢ Iic T := fun z hz => ⟨mem_univ _, hz.2.2⟩
  have hQK : Q ⊆ K := prod_mono subset_rfl fun τ hτ =>
    ⟨(min_le_left _ _).trans hτ.1.le, hτ.2⟩
  obtain ⟨M, hM⟩ := hbdS K hKc hKs
  obtain ⟨Λ, hΛ⟩ := hGb a₀ T ha₀T
  have hQI : Q ⊆ univ ×ˢ Icc a₀ T := prod_mono (subset_univ _) Ioc_subset_Icc_self
  refine tendsto_integral_mul_of_forall_setIntegral (μ := volume.restrict Q) (fun n => f n) G
    (M := max M Λ) ?_ hGm.aestronglyMeasurable ?_ ?_ hg.integrableOn
  · filter_upwards [hcontS K hKc hKs, hM] with n hn hMn
    refine ⟨(hn.mono hQK).aestronglyMeasurable hQm, ?_⟩
    refine ae_restrict_of_forall_mem hQm fun z hz => ?_
    rw [Real.norm_eq_abs]
    exact (hMn z (hQK hz)).trans (le_max_left _ _)
  · have h := ae_mono (Measure.restrict_mono hQI le_rfl) (ae_restrict_univ_prod_of_ae (m := m) hΛ)
    filter_upwards [h] with z hz
    rw [Real.norm_eq_abs]
    exact (hz z.1).trans (le_max_right _ _)
  · intro E hE _
    simp_rw [Measure.restrict_restrict hE]
    exact tendsto_setIntegral_inter_box_of_primitive f p G hcontS hbdS hconvS hpc hGm hGd hGb
      ha₀T le_rfl E hE

/-- The per-slice bounds of `eq:aniso:comparison:drift` on balls give eventual bounds on every
compact subset of `Vec m × (-∞, T]`. -/
theorem exists_bound_on_compact_of_slice_bounds (b : ℕ → Vec m × ℝ → Vec m)
    (divb : ℕ → Vec m × ℝ → ℝ)
    (hbd : ∀ J : Set ℝ, IsCompact J → J ⊆ Iic T → ∃ Λ : ℝ, ∀ r : ℝ, ∀ᶠ n in atTop,
      ∀ τ ∈ J, ∀ x ∈ Metric.closedBall (0 : Vec m) r, ∀ y ∈ Metric.closedBall (0 : Vec m) r,
        ‖b n (x, τ)‖ ≤ Λ ∧ |divb n (x, τ)| ≤ Λ ∧
        ‖b n (x, τ) - b n (y, τ)‖ ≤ Λ * ‖x - y‖ ∧
        |divb n (x, τ) - divb n (y, τ)| ≤ Λ * ‖x - y‖)
    (K : Set (Vec m × ℝ)) (hK : IsCompact K) (hKs : K ⊆ univ ×ˢ Iic T) :
    ∃ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, ‖b n z‖ ≤ M ∧ |divb n z| ≤ M := by
  obtain ⟨r, hr⟩ := (hK.image continuous_fst).isBounded.subset_closedBall (0 : Vec m)
  obtain ⟨Λ, hΛ⟩ := hbd (Prod.snd '' K) (hK.image continuous_snd)
    (by rintro _ ⟨z, hz, rfl⟩; exact (hKs hz).2)
  refine ⟨Λ, (hΛ r).mono fun n hn z hz => ?_⟩
  have h := hn z.2 (mem_image_of_mem _ hz) z.1 (hr (mem_image_of_mem _ hz)) z.1
    (hr (mem_image_of_mem _ hz))
  exact ⟨h.1, h.2.1⟩

/-- Weak convergence of the drift and its divergence along the extracted subsequence: the
`T`-clamped time primitives of `b ∘ φ` and `divb ∘ φ` converge locally uniformly to `a`,
`adiv`, whose a.e. time derivatives are `B` and `divB`; then `∫ g b_{φ n,i} → ∫ g B_i` and
`∫ g divb_{φ n} → ∫ g divB` for every integrable compactly supported `g` supported in
`Vec m × (-∞, T)`. -/
theorem tendsto_integral_mul_of_tendstoUniformlyOn_primitive
    (b : ℕ → Vec m × ℝ → Vec m) (divb : ℕ → Vec m × ℝ → ℝ)
    (hcont : ∀ K : Set (Vec m × ℝ), IsCompact K → K ⊆ univ ×ˢ Iic T →
      ∀ᶠ n in atTop, ContinuousOn (b n) K ∧ ContinuousOn (divb n) K)
    (hbd : ∀ J : Set ℝ, IsCompact J → J ⊆ Iic T → ∃ Λ : ℝ, ∀ r : ℝ, ∀ᶠ n in atTop,
      ∀ τ ∈ J, ∀ x ∈ Metric.closedBall (0 : Vec m) r, ∀ y ∈ Metric.closedBall (0 : Vec m) r,
        ‖b n (x, τ)‖ ≤ Λ ∧ |divb n (x, τ)| ≤ Λ ∧
        ‖b n (x, τ) - b n (y, τ)‖ ≤ Λ * ‖x - y‖ ∧
        |divb n (x, τ) - divb n (y, τ)| ≤ Λ * ‖x - y‖)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (a : Vec m × ℝ → Vec m) (adiv : Vec m × ℝ → ℝ)
    (ha : ∀ i, Continuous (fun z => a z i)) (hadiv : Continuous adiv)
    (hconv : ∀ K : Set (Vec m × ℝ), IsCompact K → ∀ i, TendstoUniformlyOn
      (fun n z => ∫ s in (T - 1)..(min z.2 T), b (φ n) (z.1, s) i) (fun z => a z i) atTop K)
    (hconvd : ∀ K : Set (Vec m × ℝ), IsCompact K → TendstoUniformlyOn
      (fun n z => ∫ s in (T - 1)..(min z.2 T), divb (φ n) (z.1, s)) adiv atTop K)
    (B : Vec m × ℝ → Vec m) (divB : Vec m × ℝ → ℝ) (hBm : Measurable B)
    (hdivBm : Measurable divB)
    (hB : ∀ i, ∀ c d : ℝ, c ≤ d → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ᵐ τ ∂(volume.restrict (Icc c d)),
      (∀ x, HasDerivAt (fun τ' => a (x, τ') i) (B (x, τ) i) τ) ∧ (∀ x, |B (x, τ) i| ≤ Λ) ∧
        LipschitzWith Λ.toNNReal (fun x => B (x, τ) i))
    (hdivB : ∀ c d : ℝ, c ≤ d → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ᵐ τ ∂(volume.restrict (Icc c d)),
      (∀ x, HasDerivAt (fun τ' => adiv (x, τ')) (divB (x, τ)) τ) ∧ (∀ x, |divB (x, τ)| ≤ Λ) ∧
        LipschitzWith Λ.toNNReal (fun x => divB (x, τ))) :
    ∀ g : Vec m × ℝ → ℝ, Integrable g → HasCompactSupport g → tsupport g ⊆ univ ×ˢ Iio T →
      (∀ i, Tendsto (fun n => ∫ z, g z * b (φ n) z i) atTop (nhds (∫ z, g z * B z i))) ∧
        Tendsto (fun n => ∫ z, g z * divb (φ n) z) atTop (nhds (∫ z, g z * divB z)) := by
  intro g hg hgc hgs
  have hgs' : tsupport g ⊆ univ ×ˢ Iic T := hgs.trans (prod_mono subset_rfl Iio_subset_Iic_self)
  have hφt := hφ.tendsto_atTop
  have hbdK := exists_bound_on_compact_of_slice_bounds b divb hbd
  refine ⟨fun i => ?_, ?_⟩
  · refine tendsto_integral_mul_of_tendstoUniformlyOn_primitive_scalar
      (fun n z => b (φ n) z i) (fun z => a z i) (fun z => B z i) ?_ ?_ (hconv · · i) (ha i)
      (measurable_pi_iff.mp hBm i) ?_ ?_ hg hgc hgs'
    · intro K hK hKs
      exact (hφt.eventually (hcont K hK hKs)).mono fun n hn =>
        (continuous_apply i).comp_continuousOn hn.1
    · intro K hK hKs
      obtain ⟨M, hM⟩ := hbdK K hK hKs
      exact ⟨M, (hφt.eventually hM).mono fun n hn z hz =>
        (norm_le_pi_norm (b (φ n) z) i).trans (hn z hz).1⟩
    · intro c d hcd
      obtain ⟨Λ, -, h⟩ := hB i c d hcd
      exact h.mono fun τ hτ => hτ.1
    · intro c d hcd
      obtain ⟨Λ, -, h⟩ := hB i c d hcd
      exact ⟨Λ, h.mono fun τ hτ => hτ.2.1⟩
  · refine tendsto_integral_mul_of_tendstoUniformlyOn_primitive_scalar
      (fun n => divb (φ n)) adiv divB ?_ ?_ hconvd hadiv hdivBm ?_ ?_ hg hgc hgs'
    · intro K hK hKs
      exact (hφt.eventually (hcont K hK hKs)).mono fun n hn => hn.2
    · intro K hK hKs
      obtain ⟨M, hM⟩ := hbdK K hK hKs
      exact ⟨M, (hφt.eventually hM).mono fun n hn z hz => (hn z hz).2⟩
    · intro c d hcd
      obtain ⟨Λ, -, h⟩ := hdivB c d hcd
      exact h.mono fun τ hτ => hτ.1
    · intro c d hcd
      obtain ⟨Λ, -, h⟩ := hdivB c d hcd
      exact ⟨Λ, h.mono fun τ hτ => hτ.2.1⟩

/-- If the fields `q j n` satisfy `∫ Σ_j q_j(x, s) W_j(x) dx = 0` for every time `s ≤ T` (eventually
in `n`, locally uniformly in `s`), then so do the limits `A j` of their `T`-clamped time primitives,
at every time: integrate the identity in time, exchange the integrals, and pass to the limit. -/
theorem integral_sum_mul_eq_zero_of_primitive {ι : Type*} [Fintype ι]
    (q : ι → ℕ → Vec m × ℝ → ℝ) (A : ι → Vec m × ℝ → ℝ) (W : ι → Vec m → ℝ) {R : ℝ}
    (hWc : ∀ j, Continuous (W j))
    (hWs : ∀ j, ∀ x, x ∉ Metric.closedBall (0 : Vec m) R → W j x = 0)
    (hcontS : ∀ j, ∀ K : Set (Vec m × ℝ), IsCompact K → K ⊆ univ ×ˢ Iic T →
      ∀ᶠ n in atTop, ContinuousOn (q j n) K)
    (hconvS : ∀ j, ∀ K : Set (Vec m × ℝ), IsCompact K → TendstoUniformlyOn
      (fun n z => ∫ s in (T - 1)..(min z.2 T), q j n (z.1, s)) (A j) atTop K)
    (hAc : ∀ j, Continuous (A j))
    (hzero : ∀ J : Set ℝ, IsCompact J → J ⊆ Iic T → ∀ᶠ n in atTop, ∀ s ∈ J,
      ∫ x, ∑ j, q j n (x, s) * W j x = 0)
    (τ' : ℝ) : ∫ x, ∑ j, A j (x, τ') * W j x = 0 := by
  set u := min τ' T with hu
  set J' : Set ℝ := uIcc (T - 1) u with hJ'
  have hJ'c : IsCompact J' := isCompact_uIcc
  have hJ'I : J' ⊆ Icc (min (T - 1) u) T := uIcc_subset_Icc
    ⟨min_le_left _ _, by linarith only []⟩ ⟨min_le_right _ _, min_le_right _ _⟩
  have hJ's : J' ⊆ Iic T := fun s hs => (hJ'I hs).2
  set K' : Set (Vec m × ℝ) := Metric.closedBall (0 : Vec m) R ×ˢ J' with hK'
  have hK'c : IsCompact K' := (isCompact_closedBall _ _).prod hJ'c
  have hK's : K' ⊆ univ ×ˢ Iic T := fun z hz => ⟨mem_univ _, hJ's hz.2⟩
  have hWcs : ∀ j, HasCompactSupport (W j) :=
    fun j => HasCompactSupport.intro (isCompact_closedBall _ _) (hWs j)
  -- the finite-`n` identity for the primitives
  set Φ : ℕ → Vec m → ℝ := fun n x => ∑ j, (∫ s in (T - 1)..u, q j n (x, s)) * W j x with hΦ
  have hfin : ∀ᶠ n in atTop, Integrable (Φ n) ∧ ∫ x, Φ n x = 0 := by
    filter_upwards [eventually_all.2 fun j => hcontS j K' hK'c hK's, hzero J' hJ'c hJ's]
      with n hc hz
    set H : ℝ × Vec m → ℝ := fun y => ∑ j, q j n (y.2, y.1) * W j y.2 with hH
    have hHc : ContinuousOn H (J' ×ˢ Metric.closedBall (0 : Vec m) R) := by
      refine continuousOn_finsetSum _ fun j _ => ContinuousOn.mul ?_
        ((hWc j).comp continuous_snd).continuousOn
      exact (hc j).comp (continuous_snd.prodMk continuous_fst).continuousOn
        (fun y hy => ⟨hy.2, hy.1⟩)
    have hHint : Integrable H ((volume.restrict (uIoc (T - 1) u)).prod volume) := by
      rw [← Measure.restrict_univ (μ := (volume : Measure (Vec m))), Measure.prod_restrict]
      refine (hHc.integrableOn_compact (hJ'c.prod (isCompact_closedBall _
        _))).of_forall_sdiff_eq_zero
        (measurableSet_uIoc.prod MeasurableSet.univ) fun y hy => ?_
      have hy2 : y.2 ∉ Metric.closedBall (0 : Vec m) R := fun h =>
        hy.2 ⟨uIoc_subset_uIcc hy.1.1, h⟩
      simp only [hH, hWs _ _ hy2, mul_zero, Finset.sum_const_zero]
    have hinner : ∀ x, ∫ s in (T - 1)..u, H (s, x) = Φ n x := by
      intro x
      by_cases hx : x ∈ Metric.closedBall (0 : Vec m) R
      · simp only [hH, hΦ]
        rw [intervalIntegral.integral_finsetSum fun j _ => ?_]
        · exact Finset.sum_congr rfl fun j _ => intervalIntegral.integral_mul_const _ _
        · refine ContinuousOn.intervalIntegrable ?_
          exact ((hc j).comp (continuous_const.prodMk continuous_id).continuousOn
            (fun s hs => ⟨hx, hs⟩)).mul continuousOn_const
      · simp only [hH, hΦ, hWs _ _ hx, mul_zero, Finset.sum_const_zero,
          intervalIntegral.integral_zero]
    have hswap := intervalIntegral_integral_swap (f := fun s x => H (s, x)) hHint
    simp only [hinner] at hswap
    refine ⟨?_, ?_⟩
    · have h1 := hHint.integral_prod_right
      have : Φ n = fun x => (if T - 1 ≤ u then 1 else -1 : ℝ) • ∫ s in uIoc (T - 1) u, H (s, x) :=
        funext fun x => by rw [← hinner x, intervalIntegral.intervalIntegral_eq_integral_uIoc]
      rw [this]
      exact h1.smul (if T - 1 ≤ u then (1 : ℝ) else -1)
    · rw [← hswap]
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => hz s hs]
      exact intervalIntegral.integral_zero
  -- passing to the limit
  set CW : ℝ := ∫ x, ∑ j, |W j x| with hCW
  have hWint : Integrable (fun x => ∑ j, |W j x|) :=
    integrable_finsetSum _ fun j _ => ((hWc j).integrable_of_hasCompactSupport (hWcs j)).abs
  have hlimint : Integrable (fun x => ∑ j, A j (x, τ') * W j x) :=
    integrable_finsetSum _ fun j _ =>
      (((hAc j).comp (continuous_id.prodMk continuous_const)).mul (hWc
        j)).integrable_of_hasCompactSupport
        (hWcs j).mul_left
  have hK2 : IsCompact (Metric.closedBall (0 : Vec m) R ×ˢ ({τ'} : Set ℝ)) :=
    (isCompact_closedBall _ _).prod isCompact_singleton
  refine eq_of_forall_dist_le fun ε hε => ?_
  set δ := ε / (CW + 1) with hδ
  have hCW0 : 0 ≤ CW := integral_nonneg fun x => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hδ0 : 0 < δ := by positivity
  obtain ⟨n, hn, hun⟩ := (hfin.and (eventually_all.2 fun j =>
    Metric.tendstoUniformlyOn_iff.mp (hconvS j _ hK2) δ hδ0)).exists
  rw [Real.dist_eq, sub_zero, ← sub_zero (∫ x, ∑ j, A j (x, τ') * W j x), ← hn.2,
    ← integral_sub hlimint hn.1]
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hWint.const_mul δ) (Eventually.of_forall fun x =>
    ?_)).trans ?_
  · rw [Real.norm_eq_abs, hΦ, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [← sub_mul, abs_mul]
    by_cases hx : x ∈ Metric.closedBall (0 : Vec m) R
    · have h := hun j (x, τ') ⟨hx, rfl⟩
      rw [Real.dist_eq] at h
      exact mul_le_mul_of_nonneg_right h.le (abs_nonneg _)
    · rw [hWs j x hx, abs_zero, mul_zero, mul_zero]
  · rw [integral_const_mul, ← hCW]
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith only [hε.le, hCW0]

/-- Differentiation under the spatial integral of `Σ_j A_j(x, τ) W_j(x)`, for continuous compactly
supported weights `W_j` and fields `A_j` Lipschitz in time uniformly on the support. -/
theorem hasDerivAt_integral_sum_mul_of_lipschitz_time {ι : Type*} [Fintype ι]
    (A : ι → Vec m × ℝ → ℝ) (D : ι → Vec m → ℝ) (W : ι → Vec m → ℝ) {R τ : ℝ}
    (hWc : ∀ j, Continuous (W j))
    (hWs : ∀ j, ∀ x, x ∉ Metric.closedBall (0 : Vec m) R → W j x = 0)
    (hAc : ∀ j, Continuous (A j))
    (hlip : ∀ j, ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ Metric.closedBall (0 : Vec m) R, ∀ τ₁ τ₂ : ℝ,
      τ - 1 ≤ τ₁ → τ - 1 ≤ τ₂ → |A j (x, τ₂) - A j (x, τ₁)| ≤ L * |τ₂ - τ₁|)
    (hder : ∀ j x, HasDerivAt (fun τ' => A j (x, τ')) (D j x) τ)
    (hDm : ∀ j, AEStronglyMeasurable (D j)) :
    HasDerivAt (fun τ' => ∫ x, ∑ j, A j (x, τ') * W j x) (∫ x, ∑ j, D j x * W j x) τ := by
  choose L hL0 hL using hlip
  have hWcs : ∀ j, HasCompactSupport (W j) :=
    fun j => HasCompactSupport.intro (isCompact_closedBall _ _) (hWs j)
  have hFc : ∀ τ' : ℝ, Continuous (fun x => ∑ j, A j (x, τ') * W j x) := fun τ' =>
    continuous_finsetSum _ fun j _ => ((hAc j).comp (continuous_id.prodMk continuous_const)).mul
      (hWc j)
  have hbnn : ∀ x, 0 ≤ ∑ j, L j * |W j x| :=
    fun x => Finset.sum_nonneg fun j _ => mul_nonneg (hL0 j) (abs_nonneg _)
  refine (hasDerivAt_integral_of_dominated_loc_of_lip (s := Metric.ball τ 1)
    (bound := fun x => ∑ j, L j * |W j x|) (Metric.ball_mem_nhds τ one_pos)
    (Eventually.of_forall fun τ' => (hFc τ').aestronglyMeasurable)
    ((hFc τ).integrable_of_hasCompactSupport ?_)
    (Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hDm j).mul (hWc j).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
    (integrable_finsetSum _ fun j _ =>
      (((hWc j).integrable_of_hasCompactSupport (hWcs j)).abs.const_mul (L j)))
    (Eventually.of_forall fun x => ?_)).2
  · have h : HasCompactSupport (fun x => ∑ j, A j (x, τ) * W j x) :=
      HasCompactSupport.intro (isCompact_closedBall (0 : Vec m) R) fun x hx => by
        simp only [hWs _ _ hx, mul_zero, Finset.sum_const_zero]
    exact h
  · refine LipschitzOnWith.of_dist_le_mul fun τ₂ h2 τ₁ h1 => ?_
    rw [Real.coe_nnabs, abs_of_nonneg (hbnn x), Real.dist_eq, Real.dist_eq,
      ← Finset.sum_sub_distrib, Finset.sum_mul]
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at h1 h2
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [← sub_mul, abs_mul]
    by_cases hx : x ∈ Metric.closedBall (0 : Vec m) R
    · have := hL j x hx τ₁ τ₂ (by linarith only [h1.1]) (by linarith only [h2.1])
      calc |A j (x, τ₂) - A j (x, τ₁)| * |W j x| ≤ L j * |τ₂ - τ₁| * |W j x| :=
            mul_le_mul_of_nonneg_right this (abs_nonneg _)
        _ = L j * |W j x| * |τ₂ - τ₁| := by ring
    · rw [hWs j x hx, abs_zero, mul_zero, mul_zero, zero_mul]
  · exact HasDerivAt.fun_sum fun j _ => (hder j x).mul_const (W j x)

/-- The weak-divergence identity at one time `τ` at which the limit primitives are differentiable in
time at every `x`, with bounded derivatives `B(·, τ)` and `divB(·, τ)`: the primitive identity
holds at all times, and its time derivative at `τ` is the claim. -/
theorem weakDiv_of_hasDerivAt_slice (b : ℕ → Vec m × ℝ → Vec m) (divb : ℕ → Vec m × ℝ → ℝ)
    (hcont : ∀ K : Set (Vec m × ℝ), IsCompact K → K ⊆ univ ×ˢ Iic T →
      ∀ᶠ n in atTop, ContinuousOn (b n) K ∧ ContinuousOn (divb n) K)
    (hbd : ∀ J : Set ℝ, IsCompact J → J ⊆ Iic T → ∃ Λ : ℝ, ∀ r : ℝ, ∀ᶠ n in atTop,
      ∀ τ ∈ J, ∀ x ∈ Metric.closedBall (0 : Vec m) r, ∀ y ∈ Metric.closedBall (0 : Vec m) r,
        ‖b n (x, τ)‖ ≤ Λ ∧ |divb n (x, τ)| ≤ Λ ∧
        ‖b n (x, τ) - b n (y, τ)‖ ≤ Λ * ‖x - y‖ ∧
        |divb n (x, τ) - divb n (y, τ)| ≤ Λ * ‖x - y‖)
    (hdiv : ∀ ψ : Vec m → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∀ J : Set ℝ, IsCompact J → J ⊆ Iic T → ∀ᶠ n in atTop, ∀ τ ∈ J,
        ∫ x, divb n (x, τ) * ψ x = -∫ x, ∑ i, b n (x, τ) i * fderiv ℝ ψ x (basisVec i))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (a : Vec m × ℝ → Vec m) (adiv : Vec m × ℝ → ℝ)
    (ha : ∀ i, Continuous (fun z => a z i)) (hadiv : Continuous adiv)
    (hconv : ∀ K : Set (Vec m × ℝ), IsCompact K → ∀ i, TendstoUniformlyOn
      (fun n z => ∫ s in (T - 1)..(min z.2 T), b (φ n) (z.1, s) i) (fun z => a z i) atTop K)
    (hconvd : ∀ K : Set (Vec m × ℝ), IsCompact K → TendstoUniformlyOn
      (fun n z => ∫ s in (T - 1)..(min z.2 T), divb (φ n) (z.1, s)) adiv atTop K)
    (B : Vec m × ℝ → Vec m) (divB : Vec m × ℝ → ℝ) (hBm : Measurable B)
    (hdivBm : Measurable divB) {τ : ℝ}
    (hderB : ∀ i x, HasDerivAt (fun τ' => a (x, τ') i) (B (x, τ) i) τ)
    (hbB : ∀ i, ∃ C : ℝ, ∀ x, |B (x, τ) i| ≤ C)
    (hderD : ∀ x, HasDerivAt (fun τ' => adiv (x, τ')) (divB (x, τ)) τ)
    (hbD : ∃ C : ℝ, ∀ x, |divB (x, τ)| ≤ C)
    (ψ : Vec m → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, divB (x, τ) * ψ x = -∫ x, ∑ i, B (x, τ) i * fderiv ℝ ψ x (basisVec i) := by
  have hφt := hφ.tendsto_atTop
  obtain ⟨R, hR⟩ := hψc.isCompact.isBounded.subset_closedBall (0 : Vec m)
  set q : Option (Fin m) → ℕ → Vec m × ℝ → ℝ :=
    fun j n z => Option.elim j (divb (φ n) z) (fun i => b (φ n) z i) with hq
  set A : Option (Fin m) → Vec m × ℝ → ℝ :=
    fun j z => Option.elim j (adiv z) (fun i => a z i) with hA
  set D : Option (Fin m) → Vec m → ℝ :=
    fun j x => Option.elim j (divB (x, τ)) (fun i => B (x, τ) i) with hD
  set W : Option (Fin m) → Vec m → ℝ :=
    fun j x => Option.elim j (ψ x) (fun i => fderiv ℝ ψ x (basisVec i)) with hW
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
  have hWc : ∀ j, Continuous (W j) := by
    rintro (_ | i)
    · exact hψ.continuous
    · exact (hψ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hWs : ∀ j, ∀ x, x ∉ Metric.closedBall (0 : Vec m) R → W j x = 0 := by
    rintro (_ | i) x hx
    · exact image_eq_zero_of_notMem_tsupport (fun h => hx (hR h))
    · show fderiv ℝ ψ x (basisVec i) = 0
      rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hR h))]
      rfl
  have hbdK := exists_bound_on_compact_of_slice_bounds b divb hbd
  have hcontS : ∀ j, ∀ K : Set (Vec m × ℝ), IsCompact K → K ⊆ univ ×ˢ Iic T →
      ∀ᶠ n in atTop, ContinuousOn (q j n) K := by
    rintro (_ | i) K hK hKs
    · exact (hφt.eventually (hcont K hK hKs)).mono fun n hn => hn.2
    · exact (hφt.eventually (hcont K hK hKs)).mono fun n hn =>
        (continuous_apply i).comp_continuousOn hn.1
  have hbdS : ∀ j, ∀ K : Set (Vec m × ℝ), IsCompact K → K ⊆ univ ×ˢ Iic T →
      ∃ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, |q j n z| ≤ M := by
    rintro (_ | i) K hK hKs
    · obtain ⟨M, hM⟩ := hbdK K hK hKs
      exact ⟨M, (hφt.eventually hM).mono fun n hn z hz => (hn z hz).2⟩
    · obtain ⟨M, hM⟩ := hbdK K hK hKs
      exact ⟨M, (hφt.eventually hM).mono fun n hn z hz =>
        (norm_le_pi_norm (b (φ n) z) i).trans (hn z hz).1⟩
  have hconvS : ∀ j, ∀ K : Set (Vec m × ℝ), IsCompact K → TendstoUniformlyOn
      (fun n z => ∫ s in (T - 1)..(min z.2 T), q j n (z.1, s)) (A j) atTop K := by
    rintro (_ | i) K hK
    · exact hconvd K hK
    · exact hconv K hK i
  have hAc : ∀ j, Continuous (A j) := by
    rintro (_ | i)
    · exact hadiv
    · exact ha i
  have hint_of : ∀ f : Vec m → ℝ, ContinuousOn f (Metric.closedBall (0 : Vec m) R) →
      (∀ x, x ∉ Metric.closedBall (0 : Vec m) R → f x = 0) → Integrable f := fun f hf h0 =>
    (hf.integrableOn_compact (isCompact_closedBall _ _)).integrable_of_forall_notMem_eq_zero h0
  have hzero : ∀ J : Set ℝ, IsCompact J → J ⊆ Iic T → ∀ᶠ n in atTop, ∀ s ∈ J,
      ∫ x, ∑ j, q j n (x, s) * W j x = 0 := by
    intro J hJ hJs
    have hK : IsCompact (Metric.closedBall (0 : Vec m) R ×ˢ J) :=
      (isCompact_closedBall _ _).prod hJ
    have hKs : Metric.closedBall (0 : Vec m) R ×ˢ J ⊆ univ ×ˢ Iic T :=
      prod_mono (subset_univ _) hJs
    filter_upwards [hφt.eventually (hdiv ψ hψ hψc J hJ hJs), eventually_all.2 fun j =>
      hcontS j _ hK hKs] with n hn hc s hs
    have hcj : ∀ j, ContinuousOn (fun x => q j n (x, s) * W j x)
        (Metric.closedBall (0 : Vec m) R) := fun j =>
      ((hc j).comp (continuous_id.prodMk continuous_const).continuousOn
        (fun x hx => ⟨hx, hs⟩)).mul (hWc j).continuousOn
    have hij : ∀ j, Integrable (fun x => q j n (x, s) * W j x) := fun j =>
      hint_of _ (hcj j) fun x hx => by simp only [hWs j x hx, mul_zero]
    simp only [Fintype.sum_option]
    rw [integral_add (hij none) (integrable_finsetSum _ fun i _ => hij (some i))]
    have h := hn s hs
    simp only [hq, hW, Option.elim]
    linarith only [h]
  have hstep1 := integral_sum_mul_eq_zero_of_primitive q A W hWc hWs hcontS hconvS hAc hzero
  have hlip : ∀ j, ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ Metric.closedBall (0 : Vec m) R, ∀ τ₁ τ₂ : ℝ,
      τ - 1 ≤ τ₁ → τ - 1 ≤ τ₂ → |A j (x, τ₂) - A j (x, τ₁)| ≤ L * |τ₂ - τ₁| := fun j =>
    exists_lipschitz_time_of_tendstoUniformlyOn_primitive (q j) (A j) (hcontS j) (hbdS j)
      (hconvS j) R (τ - 1)
  have hder : ∀ j x, HasDerivAt (fun τ' => A j (x, τ')) (D j x) τ := by
    rintro (_ | i) x
    · exact hderD x
    · exact hderB i x
  have hDm : ∀ j, AEStronglyMeasurable (D j) := by
    rintro (_ | i)
    · exact (hdivBm.comp measurable_prodMk_right).aestronglyMeasurable
    · exact ((measurable_pi_iff.mp hBm i).comp measurable_prodMk_right).aestronglyMeasurable
  have hderiv := hasDerivAt_integral_sum_mul_of_lipschitz_time A D W hWc hWs hAc hlip hder hDm
  have hconst : (fun τ' => ∫ x, ∑ j, A j (x, τ') * W j x) = fun _ => (0 : ℝ) :=
    funext hstep1
  rw [hconst] at hderiv
  have hzero' := hderiv.unique (hasDerivAt_const τ (0 : ℝ))
  have hWint : ∀ j, Integrable (W j) := fun j =>
    (hWc j).integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_closedBall _ _)
      (hWs j))
  have hDW : ∀ j, Integrable (fun x => D j x * W j x) := by
    intro j
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x, |D j x| ≤ C := by
      rcases j with _ | i
      · exact hbD
      · exact hbB i
    exact (hWint j).bdd_mul (hDm j) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hC x)
  simp only [Fintype.sum_option] at hzero'
  rw [integral_add (hDW none) (integrable_finsetSum _ fun i _ => hDW (some i))] at hzero'
  simp only [hD, hW, Option.elim] at hzero'
  linarith only [hzero']

/-- The weak-divergence clause of `eq:aniso:comparison:drift` in the limit: for a.e. `τ` in every
compact `J ⊆ (-∞, T)`, `divB(·, τ)` is the weak divergence of `B(·, τ)`. -/
theorem ae_weakDiv_of_tendstoUniformlyOn_primitive
    (b : ℕ → Vec m × ℝ → Vec m) (divb : ℕ → Vec m × ℝ → ℝ)
    (hcont : ∀ K : Set (Vec m × ℝ), IsCompact K → K ⊆ univ ×ˢ Iic T →
      ∀ᶠ n in atTop, ContinuousOn (b n) K ∧ ContinuousOn (divb n) K)
    (hbd : ∀ J : Set ℝ, IsCompact J → J ⊆ Iic T → ∃ Λ : ℝ, ∀ r : ℝ, ∀ᶠ n in atTop,
      ∀ τ ∈ J, ∀ x ∈ Metric.closedBall (0 : Vec m) r, ∀ y ∈ Metric.closedBall (0 : Vec m) r,
        ‖b n (x, τ)‖ ≤ Λ ∧ |divb n (x, τ)| ≤ Λ ∧
        ‖b n (x, τ) - b n (y, τ)‖ ≤ Λ * ‖x - y‖ ∧
        |divb n (x, τ) - divb n (y, τ)| ≤ Λ * ‖x - y‖)
    (hdiv : ∀ ψ : Vec m → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∀ J : Set ℝ, IsCompact J → J ⊆ Iic T → ∀ᶠ n in atTop, ∀ τ ∈ J,
        ∫ x, divb n (x, τ) * ψ x = -∫ x, ∑ i, b n (x, τ) i * fderiv ℝ ψ x (basisVec i))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (a : Vec m × ℝ → Vec m) (adiv : Vec m × ℝ → ℝ)
    (ha : ∀ i, Continuous (fun z => a z i)) (hadiv : Continuous adiv)
    (hconv : ∀ K : Set (Vec m × ℝ), IsCompact K → ∀ i, TendstoUniformlyOn
      (fun n z => ∫ s in (T - 1)..(min z.2 T), b (φ n) (z.1, s) i) (fun z => a z i) atTop K)
    (hconvd : ∀ K : Set (Vec m × ℝ), IsCompact K → TendstoUniformlyOn
      (fun n z => ∫ s in (T - 1)..(min z.2 T), divb (φ n) (z.1, s)) adiv atTop K)
    (B : Vec m × ℝ → Vec m) (divB : Vec m × ℝ → ℝ) (hBm : Measurable B)
    (hdivBm : Measurable divB)
    (hB : ∀ i, ∀ c d : ℝ, c ≤ d → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ᵐ τ ∂(volume.restrict (Icc c d)),
      (∀ x, HasDerivAt (fun τ' => a (x, τ') i) (B (x, τ) i) τ) ∧ (∀ x, |B (x, τ) i| ≤ Λ) ∧
        LipschitzWith Λ.toNNReal (fun x => B (x, τ) i))
    (hdivB : ∀ c d : ℝ, c ≤ d → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ᵐ τ ∂(volume.restrict (Icc c d)),
      (∀ x, HasDerivAt (fun τ' => adiv (x, τ')) (divB (x, τ)) τ) ∧ (∀ x, |divB (x, τ)| ≤ Λ) ∧
        LipschitzWith Λ.toNNReal (fun x => divB (x, τ))) :
    ∀ J : Set ℝ, IsCompact J → J ⊆ Iio T → ∀ᵐ τ ∂(volume.restrict J),
      ∀ ψ : Vec m → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        ∫ x, divB (x, τ) * ψ x = -∫ x, ∑ i, B (x, τ) i * fderiv ℝ ψ x (basisVec i) := by
  intro J hJ _
  obtain ⟨c, hc⟩ := hJ.bddBelow
  obtain ⟨d, hd⟩ := hJ.bddAbove
  have hcd : c ≤ max c d := le_max_left _ _
  have hJI : J ⊆ Icc c (max c d) := fun τ hτ => ⟨hc hτ, (hd hτ).trans (le_max_right _ _)⟩
  have hmono : volume.restrict J ≤ volume.restrict (Icc c (max c d)) :=
    Measure.restrict_mono hJI le_rfl
  have hgB : ∀ i, ∀ᵐ τ ∂(volume.restrict J),
      (∀ x, HasDerivAt (fun τ' => a (x, τ') i) (B (x, τ) i) τ) ∧
        ∃ C : ℝ, ∀ x, |B (x, τ) i| ≤ C := by
    intro i
    obtain ⟨Λ, -, h⟩ := hB i c (max c d) hcd
    exact Eventually.mono (ae_mono hmono h) fun τ hτ => ⟨hτ.1, Λ, hτ.2.1⟩
  have hgD : ∀ᵐ τ ∂(volume.restrict J),
      (∀ x, HasDerivAt (fun τ' => adiv (x, τ')) (divB (x, τ)) τ) ∧
        ∃ C : ℝ, ∀ x, |divB (x, τ)| ≤ C := by
    obtain ⟨Λ, -, h⟩ := hdivB c (max c d) hcd
    exact Eventually.mono (ae_mono hmono h) fun τ hτ => ⟨hτ.1, Λ, hτ.2.1⟩
  filter_upwards [ae_all_iff.2 hgB, hgD] with τ hτB hτD ψ hψ hψc
  exact weakDiv_of_hasDerivAt_slice b divb hcont hbd hdiv φ hφ a adiv ha hadiv hconv hconvd
    B divB hBm hdivBm (fun i => (hτB i).1) (fun i => (hτB i).2) hτD.1 hτD.2 ψ hψ hψc

end CIV
