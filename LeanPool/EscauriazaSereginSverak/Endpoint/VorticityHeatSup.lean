/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityPerTime

/-!
# Uniform-in-time bounds for backward mollifications of heat solutions

For a square-integrable weak solution of the heat equation with square-integrable divergence-form
source on a box, the backward mollifications satisfy, for all small radii, a bound of their
spatial `L²` norm at every time up to the top, and are uniformly Cauchy in this norm (the
energy part of `lem:localized-vorticity-energy` and `lem:local-heat-gain`).
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Uniform-in-time bounds and the uniform Cauchy property for backward mollifications of a weak
heat solution. -/
theorem vorticity_heatSup_bm {r R κ : ℝ} (hr : 0 < r) (hrR : r < R) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Vec3) (a t₀ : ℝ) (w : Vec3 × ℝ → ℝ) (F : Fin 3 → Vec3 × ℝ → ℝ),
      a + κ < t₀ → t₀ ≤ a + 1 →
      MemLp w 2 (volume.restrict (vec3Ball x₀ R ×ˢ Ioo a t₀)) →
      (∀ j, MemLp (F j) 2 (volume.restrict (vec3Ball x₀ R ×ˢ Ioo a t₀))) →
      (∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ vec3Ball x₀ R ×ˢ Ioo a t₀ →
        ∫ y in vec3Ball x₀ R ×ˢ Ioo a t₀,
            w y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
          -∫ y in vec3Ball x₀ R ×ˢ Ioo a t₀, ∑ j : Fin 3, F j y * spatialPartial ψ j y) →
      ∀ (ε : ℕ → ℝ) (hεpos : ∀ n, 0 < ε n), Tendsto ε atTop (𝓝 0) →
      (∀ᶠ n in atTop, ∀ t ∈ Icc (a + κ) t₀,
        ∫ x in vec3Ball x₀ r,
            vorticityBackMollify (vec3Ball x₀ R ×ˢ Ioo a t₀) w (ε n) (hεpos n) (x, t) ^ 2 ≤
          C * (∫ y in vec3Ball x₀ R ×ˢ Ioo a t₀, (w y ^ 2 + ∑ j : Fin 3, F j y ^ 2)) + 1) ∧
      (∀ δ : ℝ, 0 < δ → ∀ᶠ p in (atTop : Filter (ℕ × ℕ)), ∀ t ∈ Icc (a + κ) t₀,
        ∫ x in vec3Ball x₀ r,
            (vorticityBackMollify (vec3Ball x₀ R ×ˢ Ioo a t₀) w (ε p.1) (hεpos p.1) (x, t) -
              vorticityBackMollify (vec3Ball x₀ R ×ˢ Ioo a t₀) w (ε p.2) (hεpos p.2) (x, t)) ^ 2 ≤
            δ) := by
  set R₁ : ℝ := (r + R) / 2 with hR₁def
  have hrR₁ : r < R₁ := by rw [hR₁def]; linarith only [hrR]
  have hR₁R : R₁ < R := by rw [hR₁def]; linarith only [hrR]
  obtain ⟨C₀, hC₀, hsmooth⟩ := vorticityHeatSmooth_localEnergy hr hrR₁ (half_pos hκ)
  refine ⟨C₀, hC₀, ?_⟩
  intro x₀ a t₀ w F hat hta hw hF hweak ε hεpos hεlim
  set W := (vec3Ball x₀ R ×ˢ Ioo a t₀ : Set (Vec3 × ℝ)) with hWdef
  set W₁ := (vec3Ball x₀ R₁ ×ˢ Ioo (a + κ / 2) t₀ : Set (Vec3 × ℝ)) with hW₁def
  have hWo : IsOpen W := vorticityBox_isOpen x₀ R a t₀
  have hWm : MeasurableSet W := hWo.measurableSet
  have hWb : Bornology.IsBounded W := vorticityBox_isBounded x₀ R _ (Metric.isBounded_Ioo a t₀)
  have hW₁W : W₁ ⊆ W := by
    rintro ⟨x, t⟩ ⟨hx, ht1, ht2⟩
    refine ⟨show vec3EuclideanNorm (x - x₀) < R from
      lt_trans (show vec3EuclideanNorm (x - x₀) < R₁ from hx) hR₁R, ?_, ht2⟩
    change a < t
    change a + κ / 2 < t at ht1
    linarith only [ht1, hκ]
  have hW₁m : MeasurableSet W₁ := (vorticityBox_isOpen x₀ R₁ _ t₀).measurableSet
  have hW₁b : Bornology.IsBounded W₁ := hWb.subset hW₁W
  have hfin : IsFiniteMeasure (volume.restrict W) :=
    isFiniteMeasure_restrict.2 hWb.measure_lt_top.ne
  have hwi : IntegrableOn w W := hw.integrable (by norm_num)
  have hFi : ∀ j, IntegrableOn (F j) W := fun j => (hF j).integrable (by norm_num)
  have hloc : ∀ f : Vec3 × ℝ → ℝ, IntegrableOn f W →
      LocallyIntegrable (W.indicator f) (volume : Measure (Vec3 × ℝ)) := fun f hf =>
    ((integrable_indicator_iff hWm).2 hf).locallyIntegrable
  set wn : ℕ → Vec3 × ℝ → ℝ := fun n => vorticityBackMollify W w (ε n) (hεpos n) with hwndef
  set Fn : ℕ → Fin 3 → Vec3 × ℝ → ℝ :=
    fun n j => vorticityBackMollify W (F j) (ε n) (hεpos n) with hFndef
  have hwn : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (wn n) := fun n =>
    vorticityBackMollify_contDiff (hεpos n) (hloc _ hwi)
  have hFn : ∀ n j, ContDiff ℝ (⊤ : ℕ∞) (Fn n j) := fun n j =>
    vorticityBackMollify_contDiff (hεpos n) (hloc _ (hFi j))
  -- small radii
  set ε₀ : ℝ := min ((R - R₁) / 2) (κ / 12) with hε₀def
  have hε₀ : 0 < ε₀ := lt_min (by linarith only [hR₁R]) (by linarith only [hκ])
  have hsmall : ∀ᶠ n in atTop, ε n < ε₀ := hεlim.eventually (gt_mem_nhds hε₀)
  have heqn : ∀ n, ε n < ε₀ → ∀ z ∈ vec3Ball x₀ R₁ ×ˢ Ioo (a + κ / 2) t₀,
      timePartial (wn n) z - ∑ j : Fin 3, spatialSecondPartial (wn n) j j z =
        ∑ j : Fin 3, spatialPartial (Fn n j) j z := by
    intro n hn z hz
    have hball := vorticityBackBall_subset (x₀ := x₀) (ρ := R₁) (R := R) (a := a) (b := t₀)
      (κ := κ / 2) (hεpos n)
      (by have := min_le_left ((R - R₁) / 2) (κ / 12); linarith only [this, hn])
      (by have := min_le_right ((R - R₁) / 2) (κ / 12); linarith only [this, hn])
      ⟨hz.1, hz.2.1, le_of_lt hz.2.2⟩
    exact vorticityBackMollify_heat_of_weak hWo hwi hFi hweak (hεpos n) hball
  have hκsplit : a + κ / 2 + κ / 2 = a + κ := by ring
  -- square integrability and convergence on the box
  have hwnW : ∀ n, MemLp (wn n) 2 (volume.restrict W) := fun n =>
    vorticity_memLp_two_of_continuous_bounded (hwn n).continuous hWb
  have hFnW : ∀ n j, MemLp (Fn n j) 2 (volume.restrict W) := fun n j =>
    vorticity_memLp_two_of_continuous_bounded (hFn n j).continuous hWb
  have hwconv : Tendsto (fun n => eLpNorm (wn n - w) 2 (volume.restrict W)) atTop (𝓝 0) :=
    vorticityBackMollify_tendsto_restrict hWm hWm subset_rfl hw hεlim hεpos
  have hFconv : ∀ j, Tendsto (fun n => eLpNorm (Fn n j - F j) 2 (volume.restrict W)) atTop
      (𝓝 0) := fun j => vorticityBackMollify_tendsto_restrict hWm hWm subset_rfl (hF j) hεlim hεpos
  have hsqi : ∀ (f : Vec3 × ℝ → ℝ), MemLp f 2 (volume.restrict W) →
      IntegrableOn (fun y => f y ^ 2) W := fun f hf =>
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf
  have hmonoW : ∀ (f : Vec3 × ℝ → ℝ), IntegrableOn f W → (∀ y, 0 ≤ f y) →
      ∫ y in W₁, f y ≤ ∫ y in W, f y := fun f hf h0 =>
    setIntegral_mono_set hf (Eventually.of_forall h0) (Eventually.of_forall hW₁W)
  have hsplitW : ∀ (f : Vec3 × ℝ → ℝ) (g : Fin 3 → Vec3 × ℝ → ℝ),
      MemLp f 2 (volume.restrict W) → (∀ j, MemLp (g j) 2 (volume.restrict W)) →
      ∫ y in W, (f y ^ 2 + ∑ j : Fin 3, g j y ^ 2) =
        (∫ y in W, f y ^ 2) + ∑ j : Fin 3, ∫ y in W, g j y ^ 2 := fun f g hf hg => by
    rw [integral_add (hsqi f hf) (integrable_finsetSum _ fun j _ => hsqi _ (hg j)),
      integral_finsetSum _ fun j _ => hsqi _ (hg j)]
  refine ⟨?_, ?_⟩
  · -- the uniform bound
    have hlim : Tendsto (fun n => C₀ * ∫ y in W, (wn n y ^ 2 + ∑ j : Fin 3, Fn n j y ^ 2))
        atTop (𝓝 (C₀ * ∫ y in W, (w y ^ 2 + ∑ j : Fin 3, F j y ^ 2))) := by
      apply Tendsto.const_mul
      rw [hsplitW w F hw hF]
      refine (Tendsto.add (vorticity_tendsto_integral_sq hwnW hw hwconv)
        (tendsto_finsetSum _ fun j _ =>
          vorticity_tendsto_integral_sq (fun n => hFnW n j) (hF j) (hFconv j))).congr
        fun n => ?_
      exact (hsplitW _ _ (hwnW n) (hFnW n)).symm
    filter_upwards [hsmall, hlim.eventually (gt_mem_nhds (lt_add_one _))] with n hn hlt
    intro t ht
    have hest := (hsmooth x₀ (a + κ / 2) t₀ (wn n) (Fn n) (by linarith only [hat])
      (by linarith only [hta, hκ]) (hwn n) (hFn n) (heqn n hn)).1 t (by rw [hκsplit]; exact ht)
    refine hest.trans ?_
    refine le_trans ?_ (le_of_lt hlt)
    apply mul_le_mul_of_nonneg_left _ hC₀
    exact hmonoW _ ((hsqi _ (hwnW n)).add (integrable_finsetSum _ fun j _ => hsqi _ (hFnW n j)))
      (fun y => by positivity)
  · -- the uniform Cauchy property
    intro δ hδ
    have hdw : Tendsto (fun n => ∫ y in W, (wn n y - w y) ^ 2) atTop (𝓝 0) :=
      vorticity_integral_sq_tendsto_zero (f := fun n => wn n - w)
        (fun n => (hwnW n).sub hw) hwconv
    have hdF : ∀ j, Tendsto (fun n => ∫ y in W, (Fn n j y - F j y) ^ 2) atTop (𝓝 0) := fun j =>
      vorticity_integral_sq_tendsto_zero (f := fun n => Fn n j - F j)
        (fun n => (hFnW n j).sub (hF j)) (hFconv j)
    have hbound : Tendsto (fun p : ℕ × ℕ => C₀ *
        ((2 * (∫ y in W, (wn p.1 y - w y) ^ 2) + 2 * (∫ y in W, (wn p.2 y - w y) ^ 2)) +
          ∑ j : Fin 3, (2 * (∫ y in W, (Fn p.1 j y - F j y) ^ 2) +
            2 * (∫ y in W, (Fn p.2 j y - F j y) ^ 2)))) atTop (𝓝 0) := by
      have h2w : Tendsto (fun n => 2 * (∫ y in W, (wn n y - w y) ^ 2)) atTop (𝓝 0) := by
        simpa using hdw.const_mul 2
      have h2F : ∀ j : Fin 3, Tendsto (fun n => 2 * (∫ y in W, (Fn n j y - F j y) ^ 2))
          atTop (𝓝 0) := fun j => by simpa using (hdF j).const_mul 2
      have h1 := vorticity_tendsto_prod_add h2w h2w
      have h3 := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun j _ =>
        vorticity_tendsto_prod_add (h2F j) (h2F j)
      simp only [Finset.sum_const_zero] at h3
      simpa using (h1.add h3).const_mul C₀
    have hsmall2 : ∀ᶠ p in (atTop : Filter (ℕ × ℕ)), ε p.1 < ε₀ ∧ ε p.2 < ε₀ := by
      rw [← prod_atTop_atTop_eq]
      exact (hsmall.prod_mk hsmall).mono fun p hp => hp
    filter_upwards [hsmall2, hbound.eventually (ge_mem_nhds hδ)] with p hp hle
    intro t ht
    have hD : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => wn p.1 z - wn p.2 z) :=
      (hwn p.1).sub (hwn p.2)
    have hFD : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => Fn p.1 j z - Fn p.2 j z) :=
      fun j => (hFn p.1 j).sub (hFn p.2 j)
    have heqD : ∀ z ∈ vec3Ball x₀ R₁ ×ˢ Ioo (a + κ / 2) t₀,
        timePartial (fun z : Vec3 × ℝ => wn p.1 z - wn p.2 z) z -
            ∑ j : Fin 3, spatialSecondPartial (fun z : Vec3 × ℝ => wn p.1 z - wn p.2 z) j j z =
          ∑ j : Fin 3, spatialPartial (fun z : Vec3 × ℝ => Fn p.1 j z - Fn p.2 j z) j z := by
      intro z hz
      rw [vorticity_timePartial_sub (hwn p.1) (hwn p.2) z]
      simp only [vorticity_spatialSecondPartial_sub (hwn p.1) (hwn p.2),
        vorticity_spatialPartial_sub (hFn p.1 _) (hFn p.2 _), Finset.sum_sub_distrib]
      have h1 := heqn p.1 hp.1 z hz
      have h2 := heqn p.2 hp.2 z hz
      linarith only [h1, h2]
    have hest := (hsmooth x₀ (a + κ / 2) t₀ (fun z : Vec3 × ℝ => wn p.1 z - wn p.2 z)
      (fun j (z : Vec3 × ℝ) => Fn p.1 j z - Fn p.2 j z) (by linarith only [hat])
      (by linarith only [hta, hκ]) hD hFD heqD).1 t (by rw [hκsplit]; exact ht)
    refine hest.trans (le_trans ?_ hle)
    apply mul_le_mul_of_nonneg_left _ hC₀
    have hDi : IntegrableOn (fun y => (wn p.1 y - wn p.2 y) ^ 2) W :=
      hsqi _ ((hwnW p.1).sub (hwnW p.2))
    have hFDi : ∀ j, IntegrableOn (fun y => (Fn p.1 j y - Fn p.2 j y) ^ 2) W := fun j =>
      hsqi _ ((hFnW p.1 j).sub (hFnW p.2 j))
    calc
      ∫ z in W₁, ((wn p.1 z - wn p.2 z) ^ 2 + ∑ j : Fin 3, (Fn p.1 j z - Fn p.2 j z) ^ 2) ≤
          ∫ z in W, ((wn p.1 z - wn p.2 z) ^ 2 + ∑ j : Fin 3, (Fn p.1 j z - Fn p.2 j z) ^ 2) :=
        hmonoW _ (hDi.add (integrable_finsetSum _ fun j _ => hFDi j)) (fun y => by positivity)
      _ = (∫ z in W, (wn p.1 z - wn p.2 z) ^ 2) +
          ∑ j : Fin 3, ∫ z in W, (Fn p.1 j z - Fn p.2 j z) ^ 2 := by
        rw [integral_add hDi (integrable_finsetSum _ fun j _ => hFDi j),
          integral_finsetSum _ fun j _ => hFDi j]
      _ ≤ _ := by
        apply add_le_add
        · exact vorticity_integral_sq_sub_le (hwnW p.1) (hwnW p.2) hw
        · exact Finset.sum_le_sum fun j _ =>
            vorticity_integral_sq_sub_le (hFnW p.1 j) (hFnW p.2 j) (hF j)

end ESS
