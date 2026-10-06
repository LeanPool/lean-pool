/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingJointCurve
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingTransportPairing
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Pointwise time derivatives of the smooth slice representatives

`lem:lps-Bochner-joint-smooth`: if the weak pairings of the slices with spatial
tests are differentiable in time with continuous derivative given by the next
slice, the pointwise values of the smooth representatives are differentiable in
time with the corresponding derivative.
-/

public section

open MeasureTheory Set Filter Topology Convolution
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- If a real function is a primitive of a function continuous on `[a,b]` on all
subintervals, it is differentiable within `[a,b]` with that derivative
(`lem:lps-Bochner-joint-smooth`). -/
theorem lps_hasDerivWithinAt_Icc_of_integral {a b : ℝ} (hab : a < b) {f g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b))
    (hid : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → f t - f s = ∫ τ in s..t, g τ) :
    ∀ t ∈ Icc a b, HasDerivWithinAt f (g t) (Icc a b) t := by
  intro t ht
  let G : ℝ → ℝ := fun τ => g (Set.projIcc a b hab.le τ : ℝ)
  have hGc : Continuous G :=
    hg.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun τ => (Set.projIcc a b hab.le τ).2)
  have hGg : ∀ τ ∈ Icc a b, G τ = g τ := by
    intro τ hτ
    simp only [G, Set.projIcc_of_mem hab.le hτ]
  let F : ℝ → ℝ := fun u => f a + ∫ τ in a..u, G τ
  have hF : ∀ u, HasDerivAt F (G u) u := fun u =>
    ((hGc.integral_hasStrictDerivAt a u).hasDerivAt).const_add (f a)
  have hfF : ∀ u ∈ Icc a b, f u = F u := by
    intro u hu
    have h1 := hid a ⟨le_rfl, hab.le⟩ u hu hu.1
    have h2 : ∫ τ in a..u, G τ = ∫ τ in a..u, g τ := by
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [Set.uIcc_of_le hu.1] at hτ
      exact hGg τ ⟨hτ.1, hτ.2.trans hu.2⟩
    simp only [F, h2]
    linarith only [h1]
  have := (hF t).hasDerivWithinAt (s := Icc a b)
  rw [hGg t ht] at this
  exact this.congr (fun y hy => hfF y hy) (hfF t ht)

/-- The absolute value of an `L²` pairing is at most the product of the norms
(`lem:lps-Bochner-joint-smooth`). -/
theorem lps_abs_integral_pairing_le (f g : Vec3 → ℝ) (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) :
    |∫ x, f x * g x| ≤ Real.sqrt (∫ x, f x ^ 2) * Real.sqrt (∫ x, g x ^ 2) := by
  have h1 := lps_integral_pairing_le f g hf hg
  have h2 := lps_integral_pairing_le (fun x => -f x) g hf.neg hg
  have h3 : (∫ x, -f x * g x) = -∫ x, f x * g x := by
    rw [← integral_neg]
    simp only [neg_mul]
  have h4 : (∫ x, (-f x) ^ 2) = ∫ x, f x ^ 2 := by simp only [neg_sq]
  rw [h3, h4] at h2
  exact abs_le.mpr ⟨by linarith only [h2], h1⟩

/-- A curve of `L²` fields that is `L²`-continuous has continuous spatial pairings
with any `L²` test (`lem:lps-Bochner-joint-smooth`). -/
theorem lps_pairing_continuousOn {a b : ℝ} {Z : ℝ → Vec3 → ℝ}
    (hmem : ∀ t ∈ Icc a b, MemLp (Z t) 2 volume)
    (hcont : ∀ t ∈ Icc a b,
      Tendsto (fun s => eLpNorm (Z s - Z t) 2 volume) (𝓝[Icc a b] t) (𝓝 0))
    {ψ : Vec3 → ℝ} (hψ : MemLp ψ 2 volume) :
    ContinuousOn (fun s => ∫ x, Z s x * ψ x) (Icc a b) := by
  intro t ht
  have hreal : Tendsto (fun s => (eLpNorm (Z s - Z t) 2 volume).toReal)
      (𝓝[Icc a b] t) (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hcont t ht)
    simpa only [Function.comp_def, ENNReal.toReal_zero] using this
  have hbound : Tendsto (fun s => (eLpNorm (Z s - Z t) 2 volume).toReal *
      Real.sqrt (∫ x, ψ x ^ 2)) (𝓝[Icc a b] t) (𝓝 0) := by
    simpa using hreal.mul_const (Real.sqrt (∫ x, ψ x ^ 2))
  have hdiff : Tendsto (fun s => (∫ x, Z s x * ψ x) - ∫ x, Z t x * ψ x)
      (𝓝[Icc a b] t) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hm : MemLp (fun x => Z s x - Z t x) 2 volume := (hmem s hs).sub (hmem t ht)
    have hI : (∫ x, Z s x * ψ x) - ∫ x, Z t x * ψ x = ∫ x, (Z s x - Z t x) * ψ x := by
      have h1 : Integrable (fun x => Z s x * ψ x) volume := (hmem s hs).integrable_mul hψ
      have h2 : Integrable (fun x => Z t x * ψ x) volume := (hmem t ht).integrable_mul hψ
      rw [← integral_sub h1 h2]
      simp only [sub_mul]
    rw [Real.norm_eq_abs, hI]
    refine (lps_abs_integral_pairing_le _ _ hm hψ).trans (le_of_eq ?_)
    rw [vl_integral_sq_eq hm]
    rw [Real.sqrt_sq ENNReal.toReal_nonneg]
    rfl
  have := hdiff.add_const (∫ x, Z t x * ψ x)
  simp only [zero_add, sub_add_cancel] at this
  exact this

/-- Fundamental theorem of calculus for the spatial pairings of a slice curve
(`lem:lps-Bochner-joint-smooth`). -/
theorem lps_pairing_integral_identity {a b : ℝ} {Z Z' : ℝ → Vec3 → ℝ}
    (hmem' : ∀ t ∈ Icc a b, MemLp (Z' t) 2 volume)
    (hcont' : ∀ t ∈ Icc a b,
      Tendsto (fun s => eLpNorm (Z' s - Z' t) 2 volume) (𝓝[Icc a b] t) (𝓝 0))
    {ψ : Vec3 → ℝ} (hψ : MemLp ψ 2 volume)
    (hderiv : ∀ t ∈ Icc a b, HasDerivWithinAt (fun s => ∫ x, Z s x * ψ x)
      (∫ x, Z' t x * ψ x) (Icc a b) t) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      (∫ x, Z t x * ψ x) - ∫ x, Z s x * ψ x = ∫ τ in s..t, ∫ x, Z' τ x * ψ x := by
  intro s hs t ht hst
  have hq := lps_pairing_continuousOn hmem' hcont' hψ
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  have hcontP : ContinuousOn (fun u => ∫ x, Z u x * ψ x) (Icc s t) :=
    fun u hu => (hderiv u (hsub hu)).continuousWithinAt.mono hsub
  have hd : ∀ u ∈ Ioo s t, HasDerivWithinAt (fun u => ∫ x, Z u x * ψ x)
      (∫ x, Z' u x * ψ x) (Ioi u) u := by
    intro u hu
    have hu' : u ∈ Icc a b := hsub (Ioo_subset_Icc_self hu)
    refine (hderiv u hu').mono_of_mem_nhdsWithin ?_
    have : Icc u t ∈ 𝓝[Ioi u] u := Icc_mem_nhdsGT hu.2
    exact mem_of_superset this (fun y hy => ⟨hu'.1.trans hy.1, hy.2.trans ht.2⟩)
  have hint : IntervalIntegrable (fun u => ∫ x, Z' u x * ψ x) volume s t :=
    (hq.mono hsub).intervalIntegrable_of_Icc hst
  exact (intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hst hcontP hd hint).symm

/-- The bump function of outer radius `r` used to build approximate identities. -/
@[expose] def lpsBump (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : Vec3) where
  rIn := r / 2
  rOut := r
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith only [hr]

/-- The normalized bump of radius `r` centred at `x₀`, as a test function. -/
@[expose] def lpsBumpTest (x₀ : Vec3) (r : ℝ) (hr : 0 < r) : Vec3 → ℝ :=
  fun y => (lpsBump r hr).normed volume (x₀ - y)

theorem lpsBumpTest_contDiff (x₀ : Vec3) (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (lpsBumpTest x₀ r hr) :=
  ((lpsBump r hr).contDiff_normed (n := (⊤ : ℕ∞))).comp (contDiff_const.sub contDiff_id)

theorem lpsBumpTest_hasCompactSupport (x₀ : Vec3) (r : ℝ) (hr : 0 < r) :
    HasCompactSupport (lpsBumpTest x₀ r hr) :=
  (lpsBump r hr).hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x₀)

/-- Pairing with the normalized bump at `x₀` is convolution with the bump at `x₀`. -/
theorem lpsBumpTest_pairing (x₀ : Vec3) (r : ℝ) (hr : 0 < r) (h : Vec3 → ℝ) :
    ∫ y, h y * lpsBumpTest x₀ r hr y =
      (((lpsBump r hr).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) x₀ := by
  rw [convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← integral_sub_left_eq_self (fun t => (lpsBump r hr).normed volume t * h (x₀ - t))
    volume x₀]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [lpsBumpTest, sub_sub_cancel]
  ring

/-- The pointwise values of the smooth slice representatives satisfy the integral
form of the time equation (`lem:lps-Bochner-joint-smooth`). -/
theorem lps_pointwise_time_identity {a b : ℝ} {Z Z' : ℝ → Vec3 → ℝ} {B B' : ℝ → Vec3 → ℝ}
    (hBs : ∀ t ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (B t) ∧ B t =ᵐ[volume] Z t)
    (hBs' : ∀ t ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (B' t) ∧ B' t =ᵐ[volume] Z' t)
    (hmem' : ∀ t ∈ Icc a b, MemLp (Z' t) 2 volume)
    (hcont' : ∀ t ∈ Icc a b,
      Tendsto (fun s => eLpNorm (Z' s - Z' t) 2 volume) (𝓝[Icc a b] t) (𝓝 0))
    (hderiv : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∀ t ∈ Icc a b, HasDerivWithinAt (fun s => ∫ x, Z s x * ψ x)
        (∫ x, Z' t x * ψ x) (Icc a b) t)
    (hW' : ContinuousOn (fun z : Vec3 × ℝ => B' z.2 z.1) ((univ : Set Vec3) ×ˢ Icc a b))
    (x₀ : Vec3) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      B t x₀ - B s x₀ = ∫ τ in s..t, B' τ x₀ := by
  intro s hs t ht hst
  let φ : ℕ → ContDiffBump (0 : Vec3) := fun n => lpsBump (1 / ((n : ℝ) + 1)) (by positivity)
  have hr : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let ψ : ℕ → Vec3 → ℝ := fun n => lpsBumpTest x₀ (1 / ((n : ℝ) + 1)) (by positivity)
  have hψc : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n) := fun n => lpsBumpTest_contDiff _ _ _
  have hψs : ∀ n, HasCompactSupport (ψ n) := fun n => lpsBumpTest_hasCompactSupport _ _ _
  have hψm : ∀ n, MemLp (ψ n) 2 volume := fun n =>
    (hψc n).continuous.memLp_of_hasCompactSupport (hψs n)
  have hpair : ∀ n (h : Vec3 → ℝ), ∫ y, h y * ψ n y =
      (((φ n).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) x₀ :=
    fun n h => lpsBumpTest_pairing x₀ _ _ h
  have hid := fun n => lps_pairing_integral_identity hmem' hcont' (hψm n)
    (hderiv (ψ n) (hψc n) (hψs n)) s hs t ht hst
  -- convergence of the left-hand sides
  have hlhs : ∀ u ∈ Icc a b, Tendsto (fun n => ∫ x, Z u x * ψ n x) atTop (𝓝 (B u x₀)) := by
    intro u hu
    have hae : ∀ n, ∫ x, Z u x * ψ n x = ∫ x, B u x * ψ n x := fun n =>
      integral_congr_ae ((hBs u hu).2.symm.mono fun x hx => by simp only [hx])
    simp only [hae, hpair]
    exact ContDiffBump.convolution_tendsto_right_of_continuous hr
      (hBs u hu).1.continuous x₀
  -- uniform convergence of the derivative pairings
  have hq : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ τ ∈ Icc a b,
      dist (∫ x, Z' τ x * ψ n x) (B' τ x₀) ≤ ε := by
    intro ε hε
    have hKc : IsCompact (Metric.closedBall x₀ 1 ×ˢ Icc a b : Set (Vec3 × ℝ)) :=
      (isCompact_closedBall x₀ 1).prod isCompact_Icc
    have hKs : (Metric.closedBall x₀ 1 ×ˢ Icc a b : Set (Vec3 × ℝ)) ⊆
        (univ : Set Vec3) ×ˢ Icc a b := fun z hz => ⟨mem_univ _, hz.2⟩
    have huc := hKc.uniformContinuousOn_of_continuous (hW'.mono hKs)
    obtain ⟨δ, hδ, hδK⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))) (min δ 1) (by positivity)
    refine ⟨N, fun n hn τ hτ => ?_⟩
    have hrn : 1 / ((n : ℝ) + 1) < min δ 1 := by
      have := hN n hn
      rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)] at this
      exact this
    have hae : ∫ x, Z' τ x * ψ n x = ∫ x, B' τ x * ψ n x :=
      integral_congr_ae ((hBs' τ hτ).2.symm.mono fun x hx => by simp only [hx])
    rw [hae, hpair]
    refine ContDiffBump.dist_normed_convolution_le (hBs' τ hτ).1.continuous.aestronglyMeasurable ?_
    intro y hy
    have hy1 : dist y x₀ < min δ 1 := by
      have : dist y x₀ < (φ n).rOut := hy
      exact lt_of_lt_of_le this hrn.le
    have := hδK (y, τ) ⟨Metric.mem_closedBall.mpr (hy1.trans_le (min_le_right _ _)).le, hτ⟩
      (x₀, τ) ⟨Metric.mem_closedBall.mpr (by simp), hτ⟩ (by
        rw [Prod.dist_eq]
        simp only [dist_self]
        exact max_lt (hy1.trans_le (min_le_left _ _)) hδ)
    exact this.le
  -- the limit of the right-hand sides
  have hcs : ∀ u ∈ Icc a b, ContinuousOn (fun τ => B' τ x₀) (Icc a b) := by
    intro u _
    have := hW'.comp (f := fun τ : ℝ => (x₀, τ)) (continuous_const.prodMk continuous_id).continuousOn
      (fun τ hτ => ⟨mem_univ _, hτ⟩)
    exact this
  have hqc := fun n => lps_pairing_continuousOn hmem' hcont' (hψm n)
  have hrhs : Tendsto (fun n => ∫ τ in s..t, ∫ x, Z' τ x * ψ n x) atTop
      (𝓝 (∫ τ in s..t, B' τ x₀)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hq (ε / (t - s + 1)) (by
      have : 0 ≤ t - s := sub_nonneg.mpr hst
      positivity)
    refine ⟨N, fun n hn => ?_⟩
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
    have hi1 : IntervalIntegrable (fun τ => ∫ x, Z' τ x * ψ n x) volume s t :=
      ((hqc n).mono hsub).intervalIntegrable_of_Icc hst
    have hi2 : IntervalIntegrable (fun τ => B' τ x₀) volume s t :=
      ((hcs s hs).mono hsub).intervalIntegrable_of_Icc hst
    rw [Real.dist_eq, ← intervalIntegral.integral_sub hi1 hi2]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := s) (b := t) (C := ε / (t - s + 1))
      (f := fun τ => (∫ x, Z' τ x * ψ n x) - B' τ x₀) (fun τ hτ => by
        rw [Set.uIoc_of_le hst] at hτ
        have := hN n hn τ (hsub ⟨hτ.1.le, hτ.2⟩)
        rwa [Real.dist_eq, ← Real.norm_eq_abs] at this)
    have h0 : 0 ≤ t - s := sub_nonneg.mpr hst
    rw [abs_of_nonneg h0] at hb
    calc |∫ τ in s..t, ((∫ x, Z' τ x * ψ n x) - B' τ x₀)|
        = ‖∫ τ in s..t, ((∫ x, Z' τ x * ψ n x) - B' τ x₀)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ε / (t - s + 1) * (t - s) := hb
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith only [hε, h0]
  -- combine
  have hL := (hlhs t ht).sub (hlhs s hs)
  have heq : Tendsto (fun n => ∫ τ in s..t, ∫ x, Z' τ x * ψ n x) atTop (𝓝 (B t x₀ - B s x₀)) :=
    hL.congr fun n => hid n
  exact tendsto_nhds_unique heq hrhs

/-- The pointwise values of the smooth slice representatives are differentiable in
time within `[a,b]`, with derivative the value of the next slice representative
(`lem:lps-Bochner-joint-smooth`). -/
theorem lps_pointwise_time_hasDerivWithinAt {a b : ℝ} (hab : a < b)
    {Z Z' : ℝ → Vec3 → ℝ} {B B' : ℝ → Vec3 → ℝ}
    (hBs : ∀ t ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (B t) ∧ B t =ᵐ[volume] Z t)
    (hBs' : ∀ t ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (B' t) ∧ B' t =ᵐ[volume] Z' t)
    (hmem' : ∀ t ∈ Icc a b, MemLp (Z' t) 2 volume)
    (hcont' : ∀ t ∈ Icc a b,
      Tendsto (fun s => eLpNorm (Z' s - Z' t) 2 volume) (𝓝[Icc a b] t) (𝓝 0))
    (hderiv : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∀ t ∈ Icc a b, HasDerivWithinAt (fun s => ∫ x, Z s x * ψ x)
        (∫ x, Z' t x * ψ x) (Icc a b) t)
    (hW' : ContinuousOn (fun z : Vec3 × ℝ => B' z.2 z.1) ((univ : Set Vec3) ×ˢ Icc a b))
    (x₀ : Vec3) :
    ∀ t ∈ Icc a b, HasDerivWithinAt (fun s => B s x₀) (B' t x₀) (Icc a b) t := by
  have hcs : ContinuousOn (fun τ => B' τ x₀) (Icc a b) := by
    have := hW'.comp (f := fun τ : ℝ => (x₀, τ))
      (continuous_const.prodMk continuous_id).continuousOn (fun τ hτ => ⟨mem_univ _, hτ⟩)
    exact this
  exact lps_hasDerivWithinAt_Icc_of_integral hab hcs
    (lps_pointwise_time_identity hBs hBs' hmem' hcont' hderiv hW' x₀)

end ESS
