/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.HeatCriticalMain
public import LeanPool.EscauriazaSereginSverak.PartV.HeatEntropyH1
public import LeanPool.EscauriazaSereginSverak.PartV.HeatPDE
public import LeanPool.EscauriazaSereginSverak.PartV.HeatOrbitSolutionKernel
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpConvolution

/-!
# Strong continuity of the heat flow in `Lᵖ`

For `2 ≤ p < ∞` and `b ∈ Lᵖ`, the Gaussian convolution `S(t)b` is an `Lᵖ`
contraction, converges to `b` in `Lᵖ` as `t ↓ 0`, and is `Lᵖ`-continuous at every
positive time. These are the heat-flow facts behind the strong `L²` and `L³`
traces in `prop:pv-local-solution`. Smooth compactly supported data are handled
by dominated convergence with the uniform tail bound of their heat orbits; the
general case follows by density and the contraction.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Dominated convergence for `Lᵖ` norms along a countably generated filter. -/
theorem heatStrong_eLpNorm_tendsto_zero {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → Vec3 → ℝ} {g : Vec3 → ℝ} {p : ℝ} (hp : 0 < p)
    (hmeas : ∀ᶠ n in l, AEStronglyMeasurable (F n) volume)
    (hdom : ∀ᶠ n in l, ∀ x, |F n x| ≤ g x)
    (hg : Integrable (fun x => g x ^ p) volume)
    (hlim : ∀ x, Tendsto (fun n => F n x) l (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) (ENNReal.ofReal p) volume) l (𝓝 0) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by simpa using hp
  have hlint : Tendsto (fun n => ∫⁻ x, ‖F n x‖ₑ ^ p) l (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence' (μ := volume) (l := l)
      (F := fun n x => ‖F n x‖ₑ ^ p) (f := fun _ => 0)
      (fun x => ENNReal.ofReal (g x ^ p)) ?_ ?_ hg.lintegral_lt_top.ne ?_
    · simpa using h
    · filter_upwards [hmeas] with n hn
      exact hn.enorm.pow_const p
    · filter_upwards [hdom] with n hn
      refine Eventually.of_forall fun x => ?_
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]
      refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) ?_ hp.le)
      rw [Real.norm_eq_abs]
      exact hn x
    · refine Eventually.of_forall fun x => ?_
      have h1 : Tendsto (fun n => ‖F n x‖ₑ) l (𝓝 0) := by
        simpa using (hlim x).enorm
      have h2 := ((ENNReal.continuous_rpow_const (y := p)).tendsto 0).comp h1
      rwa [ENNReal.zero_rpow_of_pos hp] at h2
  have hroot := ((ENNReal.continuous_rpow_const (y := 1 / p)).tendsto 0).comp hlint
  rw [ENNReal.zero_rpow_of_pos (by positivity)] at hroot
  refine hroot.congr' ?_
  filter_upwards [hmeas] with n hn
  rw [Function.comp_apply, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hn,
    ENNReal.toReal_ofReal hp.le]

/-- The `p`-th power of a cubic tail is integrable for `2 ≤ p`. -/
theorem heatStrong_decay_rpow_integrable {C p : ℝ} (hC : 0 ≤ C) (hp : 2 ≤ p) :
    Integrable (fun x : Vec3 => (C / (1 + vec3EuclideanNorm x) ^ 3) ^ p) volume := by
  refine (heat_decay_six_integrable (C ^ p) (Real.rpow_nonneg hC p)).mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    refine Continuous.rpow_const ?_ fun _ => Or.inr (by linarith only [hp])
    refine continuous_const.div ((continuous_const.add ?_).pow 3) fun x => ?_
    · exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
        (continuous_apply i).pow 2)
    · exact pow_ne_zero 3 (by linarith only [vec3EuclideanNorm_nonneg x])
  · refine Eventually.of_forall fun x => ?_
    have hr : 1 ≤ 1 + vec3EuclideanNorm x := by linarith only [vec3EuclideanNorm_nonneg x]
    have hr0 : 0 < 1 + vec3EuclideanNorm x := by linarith only [hr]
    have hpow0 : 0 < (1 + vec3EuclideanNorm x) ^ 3 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) p),
      Real.div_rpow hC hpow0.le]
    refine div_le_div_of_nonneg_left (Real.rpow_nonneg hC p) (by positivity) ?_
    have e1 : ((1 + vec3EuclideanNorm x) ^ 3) ^ p = (1 + vec3EuclideanNorm x) ^ (3 * p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
      norm_num
    have e2 : (1 + vec3EuclideanNorm x) ^ 6 = (1 + vec3EuclideanNorm x) ^ (6 : ℝ) := by
      rw [← Real.rpow_natCast]
      norm_num
    rw [e1, e2]
    exact Real.rpow_le_rpow_of_exponent_le hr (by linarith only [hp])

/-- Heat convolution is linear on `Lᵖ` data at positive times. -/
theorem heatConv_sub_apply {p q : ℝ} (hpq : p.HolderConjugate q) {t : ℝ} (ht : 0 < t)
    {f g : Vec3 → ℝ} (hf : MemLp f (ENNReal.ofReal p) volume)
    (hg : MemLp g (ENNReal.ofReal p) volume) (x : Vec3) :
    heatConv t f x - heatConv t g x = heatConv t (f - g) x := by
  rw [heatConv_eq_integral, heatConv_eq_integral, heatConv_eq_integral,
    ← integral_sub (heatConv_integrable_enorm_le hpq ht hf x).1
      (heatConv_integrable_enorm_le hpq ht hg x).1]
  congr 1
  funext y
  simp only [Pi.sub_apply]
  ring

/-- Heat convolution is an `Lᵖ` contraction at positive times. -/
theorem heatConv_eLpNorm_le {p : ℝ} (hp : 1 ≤ p) {t : ℝ} (ht : 0 < t) {f : Vec3 → ℝ}
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm (heatConv t f) (ENNReal.ofReal p) volume ≤ eLpNorm f (ENNReal.ofReal p) volume :=
  CKN.young_convolution_nonneg_integral_one_of_aemeasurable (ENNReal.one_le_ofReal.2 hp)
    ENNReal.ofReal_ne_top (fun y => heatKernel_nonneg y t) (heatKernel_integrable ht)
    (heatKernel_integral t ht)
    (heatKernel_vecTime_measurable.comp (measurable_id.prodMk measurable_const))
    hf.aemeasurable

/-- Heat convolution maps `Lᵖ` to `Lᵖ` at positive times. -/
theorem heatConv_memLp {p : ℝ} (hp : 1 ≤ p) {t : ℝ} (ht : 0 < t) {f : Vec3 → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    MemLp (heatConv t f) (ENNReal.ofReal p) volume :=
  (heatConv_eLpNorm_le hp ht hf.aestronglyMeasurable).trans_lt hf

/-- Smooth compactly supported data: the heat orbit converges in `Lᵖ` to the datum. -/
theorem heatConv_smooth_tendsto_self {f : Vec3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) {p : ℝ} (hp : 2 ≤ p) :
    Tendsto (fun t => eLpNorm (fun x => heatConv t f x - f x) (ENNReal.ofReal p) volume)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC, hdec⟩ := heatConv_abs_le_spatial_decay hf hfc
  have hf0 (x : Vec3) : |f x| ≤ C / (1 + vec3EuclideanNorm x) ^ 3 :=
    le_of_tendsto ((heatConv_tendsto_self_nhdsWithin_zero_smooth hf hfc x).abs)
      (eventually_nhdsWithin_of_forall fun t ht => hdec ht x)
  refine heatStrong_eLpNorm_tendsto_zero (by linarith only [hp]) ?_ ?_
    (heatStrong_decay_rpow_integrable (C := 2 * C) (by positivity) hp) fun x => ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact ((heatConv_smooth_input hf hfc ht).continuous.sub hf.continuous).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with t ht x
    calc
      |heatConv t f x - f x| ≤ |heatConv t f x| + |f x| := abs_sub _ _
      _ ≤ C / (1 + vec3EuclideanNorm x) ^ 3 + C / (1 + vec3EuclideanNorm x) ^ 3 :=
        add_le_add (hdec ht x) (hf0 x)
      _ = 2 * C / (1 + vec3EuclideanNorm x) ^ 3 := by ring
  · simpa using (heatConv_tendsto_self_nhdsWithin_zero_smooth hf hfc x).sub_const (f x)

/-- Smooth compactly supported data: the heat orbit is `Lᵖ`-continuous at every
positive time. -/
theorem heatConv_smooth_tendsto_pos {f : Vec3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) {p : ℝ} (hp : 2 ≤ p) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    Tendsto (fun t => eLpNorm (fun x => heatConv t f x - heatConv t₀ f x)
      (ENNReal.ofReal p) volume) (𝓝 t₀) (𝓝 0) := by
  obtain ⟨C, hC, hdec⟩ := heatConv_abs_le_spatial_decay hf hfc
  have hpos : ∀ᶠ t in 𝓝 t₀, 0 < t := lt_mem_nhds ht₀
  refine heatStrong_eLpNorm_tendsto_zero (by linarith only [hp]) ?_ ?_
    (heatStrong_decay_rpow_integrable (C := 2 * C) (by positivity) hp) fun x => ?_
  · filter_upwards [hpos] with t ht
    exact ((heatConv_smooth_input hf hfc ht).continuous.sub
      (heatConv_smooth_input hf hfc ht₀).continuous).aestronglyMeasurable
  · filter_upwards [hpos] with t ht x
    calc
      |heatConv t f x - heatConv t₀ f x| ≤ |heatConv t f x| + |heatConv t₀ f x| := abs_sub _ _
      _ ≤ C / (1 + vec3EuclideanNorm x) ^ 3 + C / (1 + vec3EuclideanNorm x) ^ 3 :=
        add_le_add (hdec ht x) (hdec ht₀ x)
      _ = 2 * C / (1 + vec3EuclideanNorm x) ^ 3 := by ring
  · have h := (heatConv_hasDerivAt_laplacianInput hf hfc ht₀ x).continuousAt.tendsto
    simpa using h.sub_const (heatConv t₀ f x)

/-- The density step: `Lᵖ` convergence of `S(t)f - R f` for smooth compact data
extends to every `Lᵖ` datum when `R` is linear and an `Lᵖ` contraction. -/
theorem heatStrong_density {p : ℝ} (hp : 2 ≤ p) {l : Filter ℝ} (hl : ∀ᶠ t in l, 0 < t)
    (R : (Vec3 → ℝ) → Vec3 → ℝ)
    (hRsub : ∀ f g : Vec3 → ℝ, MemLp f (ENNReal.ofReal p) volume →
      MemLp g (ENNReal.ofReal p) volume → ∀ x, R f x - R g x = R (f - g) x)
    (hRmem : ∀ h : Vec3 → ℝ, MemLp h (ENNReal.ofReal p) volume →
      MemLp (R h) (ENNReal.ofReal p) volume ∧
        eLpNorm (R h) (ENNReal.ofReal p) volume ≤ eLpNorm h (ENNReal.ofReal p) volume)
    (hsmooth : ∀ g : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      Tendsto (fun t => eLpNorm (fun x => heatConv t g x - R g x) (ENNReal.ofReal p) volume)
        l (𝓝 0))
    {f : Vec3 → ℝ} (hf : MemLp f (ENNReal.ofReal p) volume) :
    Tendsto (fun t => eLpNorm (fun x => heatConv t f x - R f x) (ENNReal.ofReal p) volume)
      l (𝓝 0) := by
  have hp1 : (1 : ℝ) ≤ p := by linarith only [hp]
  have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp1
  have hpq : p.HolderConjugate (Real.conjExponent p) :=
    Real.HolderConjugate.conjExponent (by linarith only [hp])
  obtain ⟨gs, hgs, hglim⟩ := exists_smooth_compact_tendsto_eLpNorm hP1 ENNReal.ofReal_ne_top hf
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεtop : ε = ⊤
  · exact Eventually.of_forall fun _ => by simp only [hεtop, le_top]
  have hε2 : 0 < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
  have hε4 : 0 < ε / 2 / 2 := ENNReal.div_pos hε2.ne' (by norm_num)
  obtain ⟨n, hn⟩ := ((ENNReal.tendsto_nhds_zero.1 hglim) _ hε4).exists
  set g := gs n
  have hgmem : MemLp g (ENNReal.ofReal p) volume :=
    (hgs n).1.continuous.memLp_of_hasCompactSupport (hgs n).2
  have hfg : eLpNorm (f - g) (ENNReal.ofReal p) volume ≤ ε / 2 / 2 := by
    rw [← eLpNorm_neg, neg_sub]
    exact hn
  filter_upwards [hl, (ENNReal.tendsto_nhds_zero.1 (hsmooth g (hgs n).1 (hgs n).2)) _ hε2]
    with t ht hsm
  have hfgmem : MemLp (f - g) (ENNReal.ofReal p) volume := hf.sub hgmem
  have hgfmem : MemLp (g - f) (ENNReal.ofReal p) volume := hgmem.sub hf
  have hsplit : (fun x => heatConv t f x - R f x) =
      heatConv t (f - g) + (fun x => heatConv t g x - R g x) + R (g - f) := by
    funext x
    rw [Pi.add_apply, Pi.add_apply, ← heatConv_sub_apply hpq ht hf hgmem,
      ← hRsub g f hgmem hf]
    ring
  have hA : AEStronglyMeasurable (heatConv t (f - g)) volume :=
    (heatConv_memLp hp1 ht hfgmem).aestronglyMeasurable
  have hB : AEStronglyMeasurable (fun x => heatConv t g x - R g x) volume :=
    (heatConv_memLp hp1 ht hgmem).aestronglyMeasurable.sub
      (hRmem g hgmem).1.aestronglyMeasurable
  have hC : AEStronglyMeasurable (R (g - f)) volume := (hRmem _ hgfmem).1.aestronglyMeasurable
  rw [hsplit]
  calc
    eLpNorm (heatConv t (f - g) + (fun x => heatConv t g x - R g x) + R (g - f))
        (ENNReal.ofReal p) volume ≤
        eLpNorm (heatConv t (f - g)) (ENNReal.ofReal p) volume +
          eLpNorm (fun x => heatConv t g x - R g x) (ENNReal.ofReal p) volume +
          eLpNorm (R (g - f)) (ENNReal.ofReal p) volume :=
      (eLpNorm_add_le hP1).trans (add_le_add_left (eLpNorm_add_le hP1) _)
    _ ≤ ε / 2 / 2 + ε / 2 + ε / 2 / 2 := by
      gcongr
      · exact (heatConv_eLpNorm_le hp1 ht hfgmem.aestronglyMeasurable).trans hfg
      · exact (hRmem _ hgfmem).2.trans hn
    _ = ε := by
      rw [add_right_comm, ENNReal.add_halves, ENNReal.add_halves]

/-- `Lᵖ` convergence of the scalar heat orbit to its datum as `t ↓ 0`. -/
theorem heatConv_tendsto_self {p : ℝ} (hp : 2 ≤ p) {f : Vec3 → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    Tendsto (fun t => eLpNorm (fun x => heatConv t f x - f x) (ENNReal.ofReal p) volume)
      (𝓝[>] 0) (𝓝 0) :=
  heatStrong_density hp self_mem_nhdsWithin id (fun _ _ _ _ _ => rfl)
    (fun _ h => ⟨h, le_rfl⟩) (fun _ hg hgc => heatConv_smooth_tendsto_self hg hgc hp) hf

/-- `Lᵖ` continuity of the scalar heat orbit at a positive time. -/
theorem heatConv_tendsto_pos {p : ℝ} (hp : 2 ≤ p) {f : Vec3 → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    Tendsto (fun t => eLpNorm (fun x => heatConv t f x - heatConv t₀ f x)
      (ENNReal.ofReal p) volume) (𝓝 t₀) (𝓝 0) := by
  have hp1 : (1 : ℝ) ≤ p := by linarith only [hp]
  have hpq : p.HolderConjugate (Real.conjExponent p) :=
    Real.HolderConjugate.conjExponent (by linarith only [hp])
  exact heatStrong_density hp (lt_mem_nhds ht₀) (heatConv t₀)
    (fun f g hf hg x => heatConv_sub_apply hpq ht₀ hf hg x)
    (fun h hh => ⟨heatConv_memLp hp1 ht₀ hh, heatConv_eLpNorm_le hp1 ht₀ hh.aestronglyMeasurable⟩)
    (fun _ hg hgc => heatConv_smooth_tendsto_pos hg hgc hp ht₀) hf

/-- A vector field's `Lᵖ` norm is at most the sum of its components' norms. -/
theorem heatStrong_vec_eLpNorm_le {p : ℝ≥0∞} (hp : 1 ≤ p) {F : Vec3 → Vec3}
    (hF : AEStronglyMeasurable F volume) :
    eLpNorm F p volume ≤ ∑ i : Fin 3, eLpNorm (fun x => F x i) p volume := by
  have hFi (i : Fin 3) : AEStronglyMeasurable (fun x => F x i) volume :=
    (continuous_apply i).comp_aestronglyMeasurable hF
  calc
    eLpNorm F p volume ≤ eLpNorm (∑ i : Fin 3, fun x => |F x i|) p volume := by
      refine eLpNorm_mono_ae hF (Eventually.of_forall fun x => ?_)
      rw [Finset.sum_apply, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)]
      refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)).2 fun i => ?_
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun k => |F x k|) (fun k _ => abs_nonneg _)
        (Finset.mem_univ i)
    _ ≤ ∑ i : Fin 3, eLpNorm (fun x => |F x i|) p volume := eLpNorm_sum_le hp
    _ = ∑ i : Fin 3, eLpNorm (fun x => F x i) p volume := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simpa only [Real.norm_eq_abs] using eLpNorm_norm (p := p) (μ := volume) _ (hFi i)

/-- The vector heat orbit of an `Lᵖ` field lies in `Lᵖ` at positive times. -/
theorem heatConvVec3_memLp {p : ℝ} (hp : 1 ≤ p) {t : ℝ} (ht : 0 < t) {b : Vec3 → Vec3}
    (hb : MemLp b (ENNReal.ofReal p) volume) :
    MemLp (heatConvVec3 t b) (ENNReal.ofReal p) volume :=
  memLp_pi_iff.2 fun i => heatConv_memLp hp ht (memLp_pi_iff.1 hb i)

/-- `Lᵖ` convergence of the vector heat orbit to its datum as `t ↓ 0`. -/
theorem heatConvVec3_tendsto_self {p : ℝ} (hp : 2 ≤ p) {b : Vec3 → Vec3}
    (hb : MemLp b (ENNReal.ofReal p) volume) :
    Tendsto (fun t => eLpNorm (fun x => heatConvVec3 t b x - b x) (ENNReal.ofReal p) volume)
      (𝓝[>] 0) (𝓝 0) := by
  have hp1 : (1 : ℝ) ≤ p := by linarith only [hp]
  have hsum : Tendsto (fun t => ∑ i : Fin 3, eLpNorm (fun x => heatConv t (fun y => b y i) x -
      b x i) (ENNReal.ofReal p) volume) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_finsetSum (s := Finset.univ) fun i _ =>
      heatConv_tendsto_self hp (memLp_pi_iff.1 hb i)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact heatStrong_vec_eLpNorm_le (ENNReal.one_le_ofReal.2 hp1)
    ((heatConvVec3_memLp hp1 ht hb).aestronglyMeasurable.sub hb.aestronglyMeasurable)

/-- `Lᵖ` continuity of the vector heat orbit at a positive time. -/
theorem heatConvVec3_tendsto_pos {p : ℝ} (hp : 2 ≤ p) {b : Vec3 → Vec3}
    (hb : MemLp b (ENNReal.ofReal p) volume) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    Tendsto (fun t => eLpNorm (fun x => heatConvVec3 t b x - heatConvVec3 t₀ b x)
      (ENNReal.ofReal p) volume) (𝓝 t₀) (𝓝 0) := by
  have hp1 : (1 : ℝ) ≤ p := by linarith only [hp]
  have hsum : Tendsto (fun t => ∑ i : Fin 3, eLpNorm (fun x => heatConv t (fun y => b y i) x -
      heatConv t₀ (fun y => b y i) x) (ENNReal.ofReal p) volume) (𝓝 t₀) (𝓝 0) := by
    simpa using tendsto_finsetSum (s := Finset.univ) fun i _ =>
      heatConv_tendsto_pos hp (memLp_pi_iff.1 hb i) ht₀
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [lt_mem_nhds ht₀] with t ht
  exact heatStrong_vec_eLpNorm_le (ENNReal.one_le_ofReal.2 hp1)
    ((heatConvVec3_memLp hp1 ht hb).aestronglyMeasurable.sub
      (heatConvVec3_memLp hp1 ht₀ hb).aestronglyMeasurable)

end ESS

end
