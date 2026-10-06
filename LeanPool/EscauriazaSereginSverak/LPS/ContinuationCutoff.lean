/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSlab

/-!
# Smooth time cutoffs at a slab endpoint

A monotone smooth cutoff equal to one before `b - 2ε` and to zero after `b - ε`.
Testing a weak formulation against such cutoffs exhibits the boundary term at the
slab endpoint (`lem:lps-continuation`).
-/

public section

open MeasureTheory Set Filter
open scoped Topology Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The smooth cutoff `1` on `(-∞, b - 2ε]` and `0` on `[b - ε, ∞)`. -/
@[expose] def lpsCutoffRight (b ε : ℝ) (t : ℝ) : ℝ :=
  1 - Real.smoothTransition ((t - b + 2 * ε) / ε)

theorem lpsCutoffRight_contDiff (b ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (lpsCutoffRight b ε) := by
  unfold lpsCutoffRight
  refine contDiff_const.sub (Real.smoothTransition.contDiff.comp ?_)
  exact ((contDiff_id.sub contDiff_const).add contDiff_const).div_const ε

theorem lpsCutoffRight_eq_one {b ε t : ℝ} (hε : 0 < ε) (ht : t ≤ b - 2 * ε) :
    lpsCutoffRight b ε t = 1 := by
  unfold lpsCutoffRight
  rw [Real.smoothTransition.zero_of_nonpos, sub_zero]
  rw [div_nonpos_iff]
  right
  exact ⟨by linarith only [ht], hε.le⟩

theorem lpsCutoffRight_eq_zero {b ε t : ℝ} (hε : 0 < ε) (ht : b - ε ≤ t) :
    lpsCutoffRight b ε t = 0 := by
  unfold lpsCutoffRight
  rw [Real.smoothTransition.one_of_one_le, sub_self]
  rw [le_div_iff₀ hε]
  linarith only [ht]

theorem lpsCutoffRight_nonneg (b ε t : ℝ) : 0 ≤ lpsCutoffRight b ε t := by
  unfold lpsCutoffRight
  linarith only [Real.smoothTransition.le_one ((t - b + 2 * ε) / ε)]

theorem lpsCutoffRight_le_one (b ε t : ℝ) : lpsCutoffRight b ε t ≤ 1 := by
  unfold lpsCutoffRight
  linarith only [Real.smoothTransition.nonneg ((t - b + 2 * ε) / ε)]

theorem lpsCutoffRight_antitone {b ε : ℝ} (hε : 0 < ε) : Antitone (lpsCutoffRight b ε) := by
  intro s t hst
  unfold lpsCutoffRight
  have : (s - b + 2 * ε) / ε ≤ (t - b + 2 * ε) / ε := by
    gcongr
  have := Real.smoothTransition.monotone this
  linarith only [this]

theorem deriv_lpsCutoffRight_nonpos {b ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    deriv (lpsCutoffRight b ε) t ≤ 0 :=
  (lpsCutoffRight_antitone hε).deriv_nonpos

theorem deriv_lpsCutoffRight_eq_zero_of_le {b ε t : ℝ} (hε : 0 < ε) (ht : t < b - 2 * ε) :
    deriv (lpsCutoffRight b ε) t = 0 := by
  have h : lpsCutoffRight b ε =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact lpsCutoffRight_eq_one hε hs.le
  rw [h.deriv_eq]
  simp

theorem deriv_lpsCutoffRight_eq_zero_of_ge {b ε t : ℝ} (hε : 0 < ε) (ht : b - ε < t) :
    deriv (lpsCutoffRight b ε) t = 0 := by
  have h : lpsCutoffRight b ε =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact lpsCutoffRight_eq_zero hε hs.le
  rw [h.deriv_eq]
  simp

private theorem lps_cutoffRight_integral_deriv {a b ε : ℝ} (hε : 0 < ε) (ha : a ≤ b - 2 * ε) :
    ∫ t in a..b, deriv (lpsCutoffRight b ε) t = -1 := by
  have hd : ∀ t ∈ uIcc a b, HasDerivAt (lpsCutoffRight b ε) (deriv (lpsCutoffRight b ε) t) t :=
    fun t _ => ((lpsCutoffRight_contDiff b ε).differentiable (by simp) t).hasDerivAt
  have hcont : Continuous (deriv (lpsCutoffRight b ε)) :=
    (lpsCutoffRight_contDiff b ε).continuous_deriv (by simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _),
    lpsCutoffRight_eq_zero hε (show b - ε ≤ b by linarith only [hε]),
    lpsCutoffRight_eq_one hε ha]
  norm_num

private theorem lps_cutoffRight_deriv_bounded {b ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (deriv (lpsCutoffRight b ε)) ∧ Continuous (deriv (lpsCutoffRight b ε)) := by
  refine ⟨?_, (lpsCutoffRight_contDiff b ε).continuous_deriv (by simp)⟩
  refine HasCompactSupport.intro (isCompact_Icc (a := b - 2 * ε) (b := b - ε)) ?_
  intro t ht
  by_cases h1 : t < b - 2 * ε
  · exact deriv_lpsCutoffRight_eq_zero_of_le hε h1
  · by_cases h2 : b - ε < t
    · exact deriv_lpsCutoffRight_eq_zero_of_ge hε h2
    · exact absurd ⟨not_lt.mp h1, not_lt.mp h2⟩ ht

private theorem lps_cutoff_deriv_integral_estimate {a b ℓ δ η ε : ℝ} (hab : a < b)
    {G : ℝ → ℝ} (hGint : IntegrableOn G (Ioo a b))
    (hG : ∀ᵐ t ∂(volume.restrict (Ioo a b)), b - η < t → |G t - ℓ| < δ)
    (hε : 0 < ε) (hε1 : 2 * ε ≤ b - a) (hε2 : 2 * ε < η) :
    |(∫ t in Ioo a b, deriv (lpsCutoffRight b ε) t * G t) + ℓ| ≤ δ := by
  obtain ⟨hcs, hcont⟩ := lps_cutoffRight_deriv_bounded (b := b) hε
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcs
  have hdInt : IntegrableOn (deriv (lpsCutoffRight b ε)) (Ioo a b) :=
    (hcont.integrableOn_Icc (a := a) (b := b)).mono_set Ioo_subset_Icc_self
  have hI : ∫ t in Ioo a b, deriv (lpsCutoffRight b ε) t = -1 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le]
    exact lps_cutoffRight_integral_deriv hε (by linarith only [hε1])
  have hprod : IntegrableOn (fun t => deriv (lpsCutoffRight b ε) t * G t) (Ioo a b) :=
    hGint.bdd_mul (f := deriv (lpsCutoffRight b ε)) (c := C) hcont.aestronglyMeasurable
      (Eventually.of_forall hC)
  have hprod2 : IntegrableOn (fun t => deriv (lpsCutoffRight b ε) t * (G t - ℓ)) (Ioo a b) := by
    have : IntegrableOn (fun t => deriv (lpsCutoffRight b ε) t * ℓ) (Ioo a b) :=
      hdInt.mul_const ℓ
    refine (hprod.sub this).congr (Eventually.of_forall fun t => ?_)
    simp [mul_sub]
  have hkey : (∫ t in Ioo a b, deriv (lpsCutoffRight b ε) t * G t) + ℓ =
      ∫ t in Ioo a b, deriv (lpsCutoffRight b ε) t * (G t - ℓ) := by
    have h1 : (∫ t in Ioo a b, deriv (lpsCutoffRight b ε) t * (G t - ℓ)) =
        (∫ t in Ioo a b, deriv (lpsCutoffRight b ε) t * G t) -
          ∫ t in Ioo a b, deriv (lpsCutoffRight b ε) t * ℓ := by
      rw [← integral_sub hprod (hdInt.mul_const ℓ)]
      congr 1
      funext t
      ring
    rw [h1, integral_mul_const, hI]
    ring
  rw [hkey]
  have hbound : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      ‖deriv (lpsCutoffRight b ε) t * (G t - ℓ)‖ ≤ -deriv (lpsCutoffRight b ε) t * δ := by
    filter_upwards [hG] with t ht
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases h0 : deriv (lpsCutoffRight b ε) t = 0
    · simp [h0]
    · have hnt : t ≥ b - 2 * ε := by
        by_contra hlt
        exact h0 (deriv_lpsCutoffRight_eq_zero_of_le hε (not_le.mp hlt))
      have hdlt := ht (by linarith only [hnt, hε2])
      have hnp := deriv_lpsCutoffRight_nonpos (b := b) hε t
      rw [abs_of_nonpos hnp]
      exact mul_le_mul_of_nonneg_left hdlt.le (by linarith only [hnp])
  have hgInt : IntegrableOn (fun t => -deriv (lpsCutoffRight b ε) t * δ) (Ioo a b) :=
    (hdInt.neg).mul_const δ
  calc |∫ t in Ioo a b, deriv (lpsCutoffRight b ε) t * (G t - ℓ)|
      = ‖∫ t in Ioo a b, deriv (lpsCutoffRight b ε) t * (G t - ℓ)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t in Ioo a b, -deriv (lpsCutoffRight b ε) t * δ :=
        norm_integral_le_of_norm_le hgInt hbound
    _ = δ := by
        rw [integral_mul_const, integral_neg, hI]
        ring

/-- Boundary term at the right end of a slab: if the cutoff-tested identity
`∫ η_ε F₁ - ∫ η_ε' F₂ = 0` holds for all small `ε` and the time profile
`t ↦ ∫ F₂(·, t)` tends to `ℓ` at `b` from the left, then `∫ F₁ = -ℓ`
(`lem:lps-continuation`). -/
theorem lps_endpoint_boundary_right {a b ℓ : ℝ} (hab : a < b)
    {F1 F2 : Vec3 × ℝ → ℝ}
    (hF1 : Integrable F1 ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))))
    (hF2 : Integrable F2 ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))))
    (hid : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∫ q : Vec3 × ℝ,
      (lpsCutoffRight b ε q.2 * F1 q - deriv (lpsCutoffRight b ε) q.2 * F2 q)
      ∂((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) = 0)
    (hG : ∀ δ > 0, ∃ η > 0, ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      b - η < t → |(∫ x : Vec3, F2 (x, t)) - ℓ| < δ) :
    ∫ q : Vec3 × ℝ, F1 q ∂((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) = -ℓ := by
  set ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod (volume.restrict (Ioo a b))
    with hν
  have hae_t : ∀ᵐ q ∂ν, q.2 ∈ Ioo a b := by
    have : ∀ᵐ t ∂(volume.restrict (Ioo a b)), t ∈ Ioo a b := ae_restrict_mem measurableSet_Ioo
    exact (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure Vec3))
      (ν := volume.restrict (Ioo a b))).ae this
  -- limit of the first term
  have h1 : Tendsto (fun ε : ℝ => ∫ q : Vec3 × ℝ, lpsCutoffRight b ε q.2 * F1 q ∂ν)
      (𝓝[>] 0) (𝓝 (∫ q : Vec3 × ℝ, F1 q ∂ν)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun q => ‖F1 q‖) ?_ ?_
      hF1.norm ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (((lpsCutoffRight_contDiff b ε).continuous.comp continuous_snd).aestronglyMeasurable).mul
        hF1.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine Eventually.of_forall fun q => ?_
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (lpsCutoffRight_nonneg _ _ _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (lpsCutoffRight_le_one _ _ _)
    · filter_upwards [hae_t] with q hq
      refine tendsto_const_nhds.congr' ?_
      have hpos : 0 < (b - q.2) / 2 := by linarith only [hq.2]
      filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
      rw [lpsCutoffRight_eq_one hε.1 (by linarith only [hε.2]), one_mul]
  have hGint : IntegrableOn (fun t : ℝ => ∫ x : Vec3, F2 (x, t)) (Ioo a b) :=
    hF2.integral_prod_right
  have hint2 (ε : ℝ) (hε : 0 < ε) : Integrable (fun q : Vec3 × ℝ =>
      deriv (lpsCutoffRight b ε) q.2 * F2 q) ν := by
    obtain ⟨hcs, hcont⟩ := lps_cutoffRight_deriv_bounded (b := b) hε
    obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcs
    exact hF2.bdd_mul (f := fun q : Vec3 × ℝ => deriv (lpsCutoffRight b ε) q.2) (c := C)
      ((hcont.comp continuous_snd).aestronglyMeasurable)
      (Eventually.of_forall fun q => hC q.2)
  have h2 : Tendsto (fun ε : ℝ => ∫ q : Vec3 × ℝ, deriv (lpsCutoffRight b ε) q.2 * F2 q ∂ν)
      (𝓝[>] 0) (𝓝 (-ℓ)) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    obtain ⟨η, hη, hGη⟩ := hG (δ / 2) (by positivity)
    have hε₀ : 0 < min ((b - a) / 2) (η / 2) := lt_min (by linarith only [hab]) (by positivity)
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 (min ((b - a) / 2) (η / 2)) :=
      Ioo_mem_nhdsGT hε₀
    filter_upwards [hev] with ε hε
    have hε0 : 0 < ε := hε.1
    have hεa : ε < (b - a) / 2 := lt_of_lt_of_le hε.2 (min_le_left _ _)
    have hεη : ε < η / 2 := lt_of_lt_of_le hε.2 (min_le_right _ _)
    have hFub : (∫ q : Vec3 × ℝ, deriv (lpsCutoffRight b ε) q.2 * F2 q ∂ν) =
        ∫ t in Ioo a b, deriv (lpsCutoffRight b ε) t * ∫ x : Vec3, F2 (x, t) := by
      rw [integral_prod_symm _ (hint2 ε hε0)]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [integral_const_mul]
    rw [Real.dist_eq, hFub]
    have hest := lps_cutoff_deriv_integral_estimate hab hGint hGη hε0
      (by linarith only [hεa]) (by linarith only [hεη])
    have : (∫ t in Ioo a b, deriv (lpsCutoffRight b ε) t * ∫ x : Vec3, F2 (x, t)) - -ℓ =
        (∫ t in Ioo a b, deriv (lpsCutoffRight b ε) t * ∫ x : Vec3, F2 (x, t)) + ℓ := by ring
    rw [this]
    linarith only [hest, hδ]
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ q : Vec3 × ℝ, lpsCutoffRight b ε q.2 * F1 q ∂ν) =
        ∫ q : Vec3 × ℝ, deriv (lpsCutoffRight b ε) q.2 * F2 q ∂ν := by
    filter_upwards [hid, self_mem_nhdsWithin] with ε hε hε0
    have hint1 : Integrable (fun q : Vec3 × ℝ => lpsCutoffRight b ε q.2 * F1 q) ν := by
      refine hF1.bdd_mul (f := fun q : Vec3 × ℝ => lpsCutoffRight b ε q.2) (c := 1)
        (((lpsCutoffRight_contDiff b ε).continuous.comp continuous_snd).aestronglyMeasurable)
        (Eventually.of_forall fun q => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (lpsCutoffRight_nonneg _ _ _)]
      exact lpsCutoffRight_le_one _ _ _
    rw [integral_sub hint1 (hint2 ε hε0)] at hε
    linarith only [hε]
  exact tendsto_nhds_unique h1 (Tendsto.congr' (heq.mono fun ε h => h.symm) h2)

/-- The smooth cutoff `0` on `(-∞, a + ε]` and `1` on `[a + 2ε, ∞)`, obtained by
reflecting the right-end cutoff. -/
@[expose] def lpsCutoffLeft (a ε : ℝ) (t : ℝ) : ℝ := lpsCutoffRight (-a) ε (-t)

theorem lpsCutoffLeft_contDiff (a ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (lpsCutoffLeft a ε) :=
  (lpsCutoffRight_contDiff (-a) ε).comp contDiff_neg

theorem lpsCutoffLeft_eq_zero {a ε t : ℝ} (hε : 0 < ε) (ht : t ≤ a + ε) :
    lpsCutoffLeft a ε t = 0 :=
  lpsCutoffRight_eq_zero hε (by linarith only [ht])

theorem lpsCutoffLeft_eq_one {a ε t : ℝ} (hε : 0 < ε) (ht : a + 2 * ε ≤ t) :
    lpsCutoffLeft a ε t = 1 :=
  lpsCutoffRight_eq_one hε (by linarith only [ht])

theorem lpsCutoffLeft_nonneg (a ε t : ℝ) : 0 ≤ lpsCutoffLeft a ε t := lpsCutoffRight_nonneg _ _ _

theorem lpsCutoffLeft_le_one (a ε t : ℝ) : lpsCutoffLeft a ε t ≤ 1 := lpsCutoffRight_le_one _ _ _

theorem deriv_lpsCutoffLeft_eq_zero_of_le {a ε t : ℝ} (hε : 0 < ε) (ht : t < a + ε) :
    deriv (lpsCutoffLeft a ε) t = 0 := by
  have h : lpsCutoffLeft a ε =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact lpsCutoffLeft_eq_zero hε hs.le
  rw [h.deriv_eq]
  simp

theorem deriv_lpsCutoffLeft_eq_zero_of_ge {a ε t : ℝ} (hε : 0 < ε) (ht : a + 2 * ε < t) :
    deriv (lpsCutoffLeft a ε) t = 0 := by
  have h : lpsCutoffLeft a ε =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact lpsCutoffLeft_eq_one hε hs.le
  rw [h.deriv_eq]
  simp

private theorem lps_reflect_measurePreserving (a b : ℝ) :
    MeasurePreserving (fun q : Vec3 × ℝ => (q.1, -q.2))
      ((volume : Measure Vec3).prod (volume.restrict (Ioo (-b) (-a))))
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) := by
  have hneg : MeasurePreserving (fun t : ℝ => -t) (volume.restrict (Ioo (-b) (-a)))
      (volume.restrict (Ioo a b)) := by
    have hset : (fun t : ℝ => -t) ⁻¹' Ioo a b = Ioo (-b) (-a) := by
      ext t
      simp only [mem_preimage, mem_Ioo]
      constructor <;> intro h <;> constructor <;> linarith only [h.1, h.2]
    have := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
      (measurableSet_Ioo (a := a) (b := b))
    rwa [hset] at this
  exact (MeasurePreserving.id (volume : Measure Vec3)).prod hneg

/-- Boundary term at the left end of a slab: if the cutoff-tested identity
`∫ η_ε F₁ - ∫ η_ε' F₂ = 0` holds for all small `ε` with the left cutoffs and the
time profile `t ↦ ∫ F₂(·, t)` tends to `ℓ` at `a` from the right, then
`∫ F₁ = ℓ` (`lem:lps-continuation`). -/
theorem lps_endpoint_boundary_left {a b ℓ : ℝ} (hab : a < b)
    {F1 F2 : Vec3 × ℝ → ℝ}
    (hF1 : Integrable F1 ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))))
    (hF2 : Integrable F2 ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))))
    (hid : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∫ q : Vec3 × ℝ,
      (lpsCutoffLeft a ε q.2 * F1 q - deriv (lpsCutoffLeft a ε) q.2 * F2 q)
      ∂((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) = 0)
    (hG : ∀ δ > 0, ∃ η > 0, ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      t < a + η → |(∫ x : Vec3, F2 (x, t)) - ℓ| < δ) :
    ∫ q : Vec3 × ℝ, F1 q ∂((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) = ℓ := by
  have hρ := lps_reflect_measurePreserving a b
  have hρm : MeasurableEmbedding (fun q : Vec3 × ℝ => (q.1, -q.2)) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Vec3)
      (MeasurableEquiv.neg ℝ)).measurableEmbedding
  have hab' : -b < -a := by linarith only [hab]
  have hF1' : Integrable (fun q : Vec3 × ℝ => F1 (q.1, -q.2))
      ((volume : Measure Vec3).prod (volume.restrict (Ioo (-b) (-a)))) :=
    (hρ.integrable_comp_emb hρm).mpr hF1
  have hF2' : Integrable (fun q : Vec3 × ℝ => -F2 (q.1, -q.2))
      ((volume : Measure Vec3).prod (volume.restrict (Ioo (-b) (-a)))) :=
    ((hρ.integrable_comp_emb hρm).mpr hF2).neg
  have hderiv (ε t : ℝ) : deriv (lpsCutoffLeft a ε) t = - deriv (lpsCutoffRight (-a) ε) (-t) := by
    unfold lpsCutoffLeft
    exact deriv_comp_neg (lpsCutoffRight (-a) ε) t
  have hid' : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∫ q : Vec3 × ℝ,
      (lpsCutoffRight (-a) ε q.2 * (F1 (q.1, -q.2)) -
        deriv (lpsCutoffRight (-a) ε) q.2 * (-F2 (q.1, -q.2)))
      ∂((volume : Measure Vec3).prod (volume.restrict (Ioo (-b) (-a)))) = 0 := by
    filter_upwards [hid] with ε hε
    rw [← hε]
    have := hρ.integral_comp hρm
      (fun q : Vec3 × ℝ => lpsCutoffLeft a ε q.2 * F1 q - deriv (lpsCutoffLeft a ε) q.2 * F2 q)
    rw [← this]
    congr 1
    funext q
    simp only [lpsCutoffLeft, hderiv, neg_neg]
    ring
  have hG' : ∀ δ > 0, ∃ η > 0, ∀ᵐ s ∂(volume.restrict (Ioo (-b) (-a))),
      -a - η < s → |(∫ x : Vec3, -F2 (x, -s)) - -ℓ| < δ := by
    intro δ hδ
    obtain ⟨η, hη, hGη⟩ := hG δ hδ
    refine ⟨η, hη, ?_⟩
    have hneg : MeasurePreserving (fun t : ℝ => -t) (volume.restrict (Ioo (-b) (-a)))
        (volume.restrict (Ioo a b)) := by
      have hset : (fun t : ℝ => -t) ⁻¹' Ioo a b = Ioo (-b) (-a) := by
        ext t
        simp only [mem_preimage, mem_Ioo]
        constructor <;> intro h <;> constructor <;> linarith only [h.1, h.2]
      have := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
        (measurableSet_Ioo (a := a) (b := b))
      rwa [hset] at this
    filter_upwards [hneg.quasiMeasurePreserving.ae hGη] with s hs hsη
    have := hs (by linarith only [hsη])
    have h2 : (∫ x : Vec3, -F2 (x, -s)) - -ℓ = -((∫ x : Vec3, F2 (x, -s)) - ℓ) := by
      rw [integral_neg]
      ring
    rw [h2, abs_neg]
    exact this
  have hres := lps_endpoint_boundary_right hab' hF1' hF2' hid' hG'
  have hint : (∫ q : Vec3 × ℝ, F1 (q.1, -q.2)
      ∂((volume : Measure Vec3).prod (volume.restrict (Ioo (-b) (-a))))) =
      ∫ q : Vec3 × ℝ, F1 q ∂((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) :=
    hρ.integral_comp hρm F1
  linarith only [hres, hint]

end ESS
