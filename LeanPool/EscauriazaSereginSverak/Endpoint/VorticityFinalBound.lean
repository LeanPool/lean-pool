/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityLevelThree

/-!
# The bound of the velocity gradient

At every time the smooth approximations of the velocity gradient are bounded pointwise, by the
`H²` embedding, the div–curl chain and the uniform-in-time bounds of the vorticity and its first
and second derivatives; the bound passes to the weak gradient (the gradient bound
`eq:vorticity-regularity-gradient` of `thm:vorticity-regularity`).
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The pointwise bound of the velocity gradient on a smaller box. -/
theorem vorticityFinal_gradBound (M Kw K1 K2' : ℝ) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x₀ : Vec3) (a t₀ : ℝ) (U : Fin 3 → Vec3 × ℝ → ℝ)
      (G Ω1 F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
      (D2 Ω2 F' : Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
      (F'' : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ),
    a + 1 / 32 < t₀ → t₀ ≤ a + 1 →
    (∀ i, MemLp (U i) 2 (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀))) →
    (∀ᵐ z ∂(volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀)), ∀ i, |U i z| ≤ M) →
    (∀ i j, MemLp (G i j) 2 (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀))) →
    (∀ i j k, MemLp (D2 i j k) 2 (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀))) →
    (∀ i j, MemLp (Ω1 i j) 2 (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀))) →
    (∀ i j k, MemLp (Ω2 i j k) 2 (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀))) →
    (∀ i j, MemLp (F i j) 2 (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀))) →
    (∀ i j m, MemLp (F' i j m) 2 (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀))) →
    (∀ i j m k, MemLp (F'' i j m k) 2 (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀))) →
    (∀ i j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀, U i y * spatialPartial ψ j y =
        -∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀, G i j y * ψ y) →
    (∀ i j k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀, G i j y * spatialPartial ψ k y =
        -∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀, D2 i j k y * ψ y) →
    (∀ i j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀, vorticityCurl G i y * spatialPartial ψ j y =
        -∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀, Ω1 i j y * ψ y) →
    (∀ i j k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀, Ω1 i j y * spatialPartial ψ k y =
        -∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀, Ω2 i j k y * ψ y) →
    (∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀, ∑ i : Fin 3, U i y * spatialPartial ψ i y = 0) →
    (∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀,
          vorticityCurl G i y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
        -∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀, ∑ j : Fin 3, F i j y * spatialPartial ψ j y) →
    (∀ i m : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀,
          Ω1 i m y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
        -∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀,
          ∑ j : Fin 3, F' i j m y * spatialPartial ψ j y) →
    (∀ i m k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀,
          Ω2 i m k y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
        -∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀,
          ∑ j : Fin 3, F'' i j m k y * spatialPartial ψ j y) →
    (∀ i, ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀,
      (vorticityCurl G i y ^ 2 + ∑ j : Fin 3, F i j y ^ 2) ≤ Kw) →
    (∀ i m, ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀,
      (Ω1 i m y ^ 2 + ∑ j : Fin 3, F' i j m y ^ 2) ≤ K1) →
    (∀ i m k, ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀,
      (Ω2 i m k y ^ 2 + ∑ j : Fin 3, F'' i j m k y ^ 2) ≤ K2') →
    ∀ᵐ z ∂(volume.restrict (vec3Ball x₀ (38 / 64) ×ˢ Ioo (a + 1 / 64) t₀)),
      ∀ i j, |G i j z| ≤ K := by
  obtain ⟨Ch, hCh, hsup⟩ := vorticity_heatSup_bm (r := 42 / 64) (R := 43 / 64) (κ := 1 / 64)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Cc, hCc, hchain⟩ := vorticityChain (ρ := 42 / 64) (by norm_num)
  set AU : ℝ := 3 * (M ^ 2 * (volume (vec3Ball (0 : Vec3) (42 / 64))).toReal) with hAUdef
  have hAU : 0 ≤ AU := by positivity
  set H4 : ℝ := Cc * (3 * (Ch * |Kw| + 1) + AU) with hH4def
  set H5 : ℝ := Cc * (9 * (Ch * |K1| + 1) + H4) with hH5def
  set H6 : ℝ := Cc * (27 * (Ch * |K2'| + 1) + H5) with hH6def
  have hH4 : 0 ≤ H4 := by positivity
  have hH5 : 0 ≤ H5 := by positivity
  have hH6 : 0 ≤ H6 := by positivity
  refine ⟨Real.sqrt (Cc * (H4 + H5 + H6)), Real.sqrt_nonneg _, ?_⟩
  intro x₀ a t₀ U G Ω1 F D2 Ω2 F' F'' hat hta hU hUb hG hD2 hΩ1 hΩ2 hF hF' hF'' hdU hdG hdw
    hdΩ1 hdiv hheatw hheatΩ hheatΩ2 hKw hK1 hK2'
  set W := (vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀ : Set (Vec3 × ℝ)) with hWdef
  have hWo : IsOpen W := vorticityBox_isOpen x₀ _ a t₀
  have hWm : MeasurableSet W := hWo.measurableSet
  have hWb : Bornology.IsBounded W := vorticityBox_isBounded x₀ _ _ (Metric.isBounded_Ioo a t₀)
  have hfin : IsFiniteMeasure (volume.restrict W) :=
    isFiniteMeasure_restrict.2 hWb.measure_lt_top.ne
  have hint : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W) → IntegrableOn f W :=
    fun f hf => hf.integrable (by norm_num)
  have hloc : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W) →
      LocallyIntegrable (W.indicator f) (volume : Measure (Vec3 × ℝ)) := fun f hf =>
    ((integrable_indicator_iff hWm).2 (hint f hf)).locallyIntegrable
  have hw := vorticityCurl_memLp hG
  obtain ⟨ε, hεpos, hεlim, hεle⟩ := vorticity_engine_radii (show (0 : ℝ) < 1 / 768 by norm_num)
  set bm : (Vec3 × ℝ → ℝ) → ℕ → Vec3 × ℝ → ℝ :=
    fun f n => vorticityBackMollify W f (ε n) (hεpos n) with hbmdef
  have hbmS : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W) → ∀ n,
      ContDiff ℝ (⊤ : ℕ∞) (bm f n) := fun f hf n =>
    vorticityBackMollify_contDiff (hεpos n) (hloc f hf)
  have hc : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W) → ∀ n,
      Continuous (bm f n) := fun f hf n => (hbmS f hf n).continuous
  have hball : ∀ n, ∀ z ∈ vec3Ball x₀ (42 / 64) ×ˢ Ioc (a + 1 / 128) t₀,
      Metric.closedBall (z - vorticityBackShift (ε n)) (ε n) ⊆ W := fun n z hz =>
    vorticityBackBall_subset (hεpos n) (by have := hεle n; linarith only [this])
      (by have := hεle n; linarith only [this]) hz
  have hrel := fun n z hz => vorticitySmoothRelations hWo hWb hU hG hD2 hΩ1 hΩ2 hdU hdG hdw hdΩ1
    hdiv (hεpos n) (hball n z hz)
  have hUn : ∀ n i z, |bm (U i) n z| ≤ M := fun n i z =>
    vorticityBackMollify_abs_le (hεpos n)
      (vorticity_indicator_bound hWm hM (by filter_upwards [hUb] with z hz using hz i)) z
  have hsw : ∀ᶠ n in atTop, ∀ i : Fin 3, ∀ t ∈ Icc (a + 1 / 64) t₀,
      ∫ x in vec3Ball x₀ (42 / 64), bm (vorticityCurl G i) n (x, t) ^ 2 ≤ Ch * |Kw| + 1 := by
    rw [eventually_all]
    intro i
    filter_upwards [(hsup x₀ a t₀ (vorticityCurl G i) (F i) (by linarith only [hat]) hta (hw i)
      (hF i) (hheatw i) ε hεpos hεlim).1] with n hn t ht
    refine (hn t ht).trans ?_
    gcongr
    exact (hKw i).trans (le_abs_self Kw)
  have hsΩ : ∀ᶠ n in atTop, ∀ i m : Fin 3, ∀ t ∈ Icc (a + 1 / 64) t₀,
      ∫ x in vec3Ball x₀ (42 / 64), bm (Ω1 i m) n (x, t) ^ 2 ≤ Ch * |K1| + 1 := by
    rw [eventually_all]
    intro i
    rw [eventually_all]
    intro m
    filter_upwards [(hsup x₀ a t₀ (Ω1 i m) (fun j => F' i j m) (by linarith only [hat]) hta
      (hΩ1 i m) (fun j => hF' i j m) (hheatΩ i m) ε hεpos hεlim).1] with n hn t ht
    refine (hn t ht).trans ?_
    gcongr
    exact (hK1 i m).trans (le_abs_self K1)
  have hsΩ2 : ∀ᶠ n in atTop, ∀ i m k : Fin 3, ∀ t ∈ Icc (a + 1 / 64) t₀,
      ∫ x in vec3Ball x₀ (42 / 64), bm (Ω2 i m k) n (x, t) ^ 2 ≤ Ch * |K2'| + 1 := by
    rw [eventually_all]
    intro i
    rw [eventually_all]
    intro m
    rw [eventually_all]
    intro k
    filter_upwards [(hsup x₀ a t₀ (Ω2 i m k) (fun j => F'' i j m k) (by linarith only [hat]) hta
      (hΩ2 i m k) (fun j => hF'' i j m k) (hheatΩ2 i m k) ε hεpos hεlim).1] with n hn t ht
    refine (hn t ht).trans ?_
    gcongr
    exact (hK2' i m k).trans (le_abs_self K2')
  have hsl : ∀ h : Vec3 × ℝ → ℝ, Continuous h → ∀ t : ℝ, Continuous (fun x : Vec3 => h (x, t)) :=
    fun h hh t => hh.comp (continuous_id.prodMk continuous_const)
  have hib : ∀ (h : Vec3 → ℝ) (r : ℝ), Continuous h → IntegrableOn h (vec3Ball x₀ r) :=
    fun h r hh => vorticityHeatSmooth_integrableOn_ball hh x₀ r
  have hmonoB : ∀ (h : Vec3 → ℝ) {r₁ r₂ : ℝ}, Continuous h → (∀ x, 0 ≤ h x) → r₁ ≤ r₂ →
      ∫ x in vec3Ball x₀ r₁, h x ≤ ∫ x in vec3Ball x₀ r₂, h x := fun h r₁ r₂ hh h0 hr =>
    setIntegral_mono_set (hib h r₂ hh) (Eventually.of_forall h0)
      (Eventually.of_forall (vec3Ball_mono hr))
  have hper : ∀ᶠ n in atTop, ∀ t ∈ Icc (a + 1 / 64) t₀, ∀ x,
      vec3EuclideanNorm (x - x₀) ≤ 38 / 64 → ∀ i j : Fin 3,
        bm (G i j) n (x, t) ^ 2 ≤ Cc * (H4 + H5 + H6) := by
    filter_upwards [hsw, hsΩ, hsΩ2] with n hn1 hn2 hn3 t ht x hx i j
    have hreg : ∀ x ∈ vec3Ball x₀ (42 / 64),
        (x, t) ∈ vec3Ball x₀ (42 / 64) ×ˢ Ioc (a + 1 / 128) t₀ := fun x hx =>
      ⟨hx, by linarith only [ht.1], ht.2⟩
    obtain ⟨c1, c2, c3, c4⟩ := hchain x₀ t (fun i => bm (U i) n)
      (fun i => bm (vorticityCurl G i) n) (fun i j => bm (G i j) n) (fun i j => bm (Ω1 i j) n)
      (fun i j k => bm (D2 i j k) n) (fun i j k => bm (Ω2 i j k) n)
      (fun i => hbmS _ (hU i) n) (fun i j => hbmS _ (hG i j) n)
      (fun i j k => hbmS _ (hD2 i j k) n) (fun i => hc _ (hw i) n) (fun i j => hc _ (hΩ1 i j) n)
      (fun i j k => hc _ (hΩ2 i j k) n)
      (fun x hx => (hrel n _ (hreg x hx)).1) (fun x hx => (hrel n _ (hreg x hx)).2.1)
      (fun x hx => (hrel n _ (hreg x hx)).2.2.1) (fun x hx => (hrel n _ (hreg x hx)).2.2.2.1)
      (fun x hx => (hrel n _ (hreg x hx)).2.2.2.2.1)
      (fun x hx => (hrel n _ (hreg x hx)).2.2.2.2.2.1)
      (fun x hx => (hrel n _ (hreg x hx)).2.2.2.2.2.2.1)
      (fun x hx => (hrel n _ (hreg x hx)).2.2.2.2.2.2.2.1)
    have e1 : (42 / 64 : ℝ) - 1 / 64 = 41 / 64 := by norm_num
    have e2 : (42 / 64 : ℝ) - 2 / 64 = 40 / 64 := by norm_num
    have e3 : (42 / 64 : ℝ) - 3 / 64 = 39 / 64 := by norm_num
    have e4 : (42 / 64 : ℝ) - 4 / 64 = 38 / 64 := by norm_num
    rw [e1] at c1 c2
    rw [e2] at c2 c3
    rw [e3] at c3 c4
    rw [e4] at c4
    have cw : ∀ l, Continuous (fun x : Vec3 => bm (vorticityCurl G l) n (x, t) ^ 2) := fun l =>
      (hsl _ (hc _ (hw l) n) t).pow 2
    have cU : ∀ i, Continuous (fun x : Vec3 => bm (U i) n (x, t) ^ 2) := fun i =>
      (hsl _ (hc _ (hU i) n) t).pow 2
    have cG : ∀ i j, Continuous (fun x : Vec3 => bm (G i j) n (x, t) ^ 2) := fun i j =>
      (hsl _ (hc _ (hG i j) n) t).pow 2
    have cΩ : ∀ i j, Continuous (fun x : Vec3 => bm (Ω1 i j) n (x, t) ^ 2) := fun i j =>
      (hsl _ (hc _ (hΩ1 i j) n) t).pow 2
    have cΩ2 : ∀ i j k, Continuous (fun x : Vec3 => bm (Ω2 i j k) n (x, t) ^ 2) :=
      fun i j k => (hsl _ (hc _ (hΩ2 i j k) n) t).pow 2
    have cD : ∀ i j k, Continuous (fun x : Vec3 => bm (D2 i j k) n (x, t) ^ 2) := fun i j k =>
      (hsl _ (hc _ (hD2 i j k) n) t).pow 2
    have cE : ∀ i j k c, Continuous (fun x : Vec3 =>
        spatialPartial (bm (D2 i j k) n) c (x, t) ^ 2) := fun i j k c =>
      (hsl _ (CKN.spatialPartial_contDiff (hbmS _ (hD2 i j k) n) c).continuous t).pow 2
    have sG : Continuous (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3, bm (G i j) n (x, t) ^ 2) :=
      continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => cG i j
    have sΩ : Continuous (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3, bm (Ω1 i j) n (x, t) ^ 2) :=
      continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => cΩ i j
    have sD : Continuous (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        bm (D2 i j k) n (x, t) ^ 2) :=
      continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        continuous_finsetSum _ fun k _ => cD i j k
    have sΩ2 : Continuous (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        bm (Ω2 i j k) n (x, t) ^ 2) :=
      continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        continuous_finsetSum _ fun k _ => cΩ2 i j k
    have sE : Continuous (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ c : Fin 3,
        spatialPartial (bm (D2 i j k) n) c (x, t) ^ 2) :=
      continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun c _ => cE i j k c
    have A1 : ∫ x in vec3Ball x₀ (42 / 64), (∑ l : Fin 3, bm (vorticityCurl G l) n (x, t) ^ 2 +
        ∑ i : Fin 3, bm (U i) n (x, t) ^ 2) ≤ 3 * (Ch * |Kw| + 1) + AU := by
      rw [integral_add (integrable_finsetSum _ fun l _ => hib _ _ (cw l))
          (integrable_finsetSum _ fun i _ => hib _ _ (cU i)),
        integral_finsetSum _ fun l _ => hib _ _ (cw l),
        integral_finsetSum _ fun i _ => hib _ _ (cU i)]
      apply add_le_add
      · calc
          _ ≤ ∑ _l : Fin 3, (Ch * |Kw| + 1) := Finset.sum_le_sum fun l _ => hn1 l t ht
          _ = 3 * (Ch * |Kw| + 1) := by simp; ring
      · calc
          _ ≤ ∑ _i : Fin 3, M ^ 2 * (volume (vec3Ball (0 : Vec3) (42 / 64))).toReal :=
            Finset.sum_le_sum fun i _ => vorticity_setIntegral_sq_le_of_bound
              (hsl _ (hc _ (hU i) n) t) (fun x => hUn n i (x, t))
          _ = AU := by simp [hAUdef]
    have A2 : ∫ x in vec3Ball x₀ (41 / 64), ∑ i : Fin 3, ∑ j : Fin 3,
        bm (G i j) n (x, t) ^ 2 ≤ H4 :=
      c1.trans (mul_le_mul_of_nonneg_left A1 hCc)
    have A3 : ∫ x in vec3Ball x₀ (41 / 64), (∑ l : Fin 3, ∑ m : Fin 3,
        bm (Ω1 l m) n (x, t) ^ 2 + ∑ i : Fin 3, ∑ j : Fin 3, bm (G i j) n (x, t) ^ 2) ≤
        9 * (Ch * |K1| + 1) + H4 := by
      rw [integral_add (hib _ _ sΩ) (hib _ _ sG)]
      apply add_le_add _ A2
      rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun m _ => hib _ _ (cΩ l m)]
      calc
        _ ≤ ∑ _l : Fin 3, ∑ _m : Fin 3, (Ch * |K1| + 1) := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [integral_finsetSum _ fun m _ => hib _ _ (cΩ l m)]
          exact Finset.sum_le_sum fun m _ =>
            (hmonoB _ (cΩ l m) (fun x => sq_nonneg _) (by norm_num)).trans (hn2 l m t ht)
        _ = 9 * (Ch * |K1| + 1) := by simp; ring
    have A4 : ∫ x in vec3Ball x₀ (40 / 64), ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        bm (D2 i j k) n (x, t) ^ 2 ≤ H5 :=
      c2.trans (mul_le_mul_of_nonneg_left A3 hCc)
    have A5 : ∫ x in vec3Ball x₀ (40 / 64), (∑ l : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        bm (Ω2 l j k) n (x, t) ^ 2 + ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          bm (D2 i j k) n (x, t) ^ 2) ≤ 27 * (Ch * |K2'| + 1) + H5 := by
      rw [integral_add (hib _ _ sΩ2) (hib _ _ sD)]
      apply add_le_add _ A4
      rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun m _ =>
        integrable_finsetSum _ fun k _ => hib _ _ (cΩ2 l m k)]
      calc
        _ ≤ ∑ _l : Fin 3, ∑ _m : Fin 3, ∑ _k : Fin 3, (Ch * |K2'| + 1) := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun k _ =>
            hib _ _ (cΩ2 l m k)]
          refine Finset.sum_le_sum fun m _ => ?_
          rw [integral_finsetSum _ fun k _ => hib _ _ (cΩ2 l m k)]
          exact Finset.sum_le_sum fun k _ =>
            (hmonoB _ (cΩ2 l m k) (fun x => sq_nonneg _) (by norm_num)).trans (hn3 l m k t ht)
        _ = 27 * (Ch * |K2'| + 1) := by simp; ring
    have A6 : ∫ x in vec3Ball x₀ (39 / 64), ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ c : Fin 3,
        spatialPartial (bm (D2 i j k) n) c (x, t) ^ 2 ≤ H6 :=
      c3.trans (mul_le_mul_of_nonneg_left A5 hCc)
    refine (c4 x hx i j).trans (mul_le_mul_of_nonneg_left ?_ hCc)
    have hsingle : ∀ (f : Fin 3 → Fin 3 → ℝ) (a b : Fin 3), (∀ a b, 0 ≤ f a b) →
        f a b ≤ ∑ a : Fin 3, ∑ b : Fin 3, f a b := fun f a b h0 =>
      (Finset.single_le_sum (f := fun b => f a b) (fun b _ => h0 a b)
        (Finset.mem_univ b)).trans (Finset.single_le_sum (f := fun a => ∑ b : Fin 3, f a b)
          (fun a _ => Finset.sum_nonneg fun b _ => h0 a b) (Finset.mem_univ a))
    have iG : IntegrableOn (fun y : Vec3 => bm (G i j) n (y, t) ^ 2) (vec3Ball x₀ (39 / 64)) :=
      hib _ _ (cG i j)
    have iD : IntegrableOn (fun y : Vec3 => ∑ k : Fin 3, bm (D2 i j k) n (y, t) ^ 2)
        (vec3Ball x₀ (39 / 64)) := hib _ _ (continuous_finsetSum _ fun k _ => cD i j k)
    have iE : IntegrableOn (fun y : Vec3 => ∑ k : Fin 3, ∑ c : Fin 3,
        spatialPartial (bm (D2 i j k) n) c (y, t) ^ 2) (vec3Ball x₀ (39 / 64)) :=
      hib _ _ (continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun c _ => cE i j k c)
    refine le_of_eq_of_le ((integral_add (iG.add iD) iE).trans (congrArg (fun r => r +
      ∫ y in vec3Ball x₀ (39 / 64), ∑ k : Fin 3, ∑ c : Fin 3,
        spatialPartial (bm (D2 i j k) n) c (y, t) ^ 2) (integral_add iG iD))) ?_
    refine add_le_add (add_le_add ?_ ?_) ?_
    · refine (setIntegral_mono_on (hib _ _ (cG i j)) (hib _ _ sG)
        (isOpen_vec3Ball x₀ _).measurableSet fun y _ =>
          hsingle (fun a b => bm (G a b) n (y, t) ^ 2) i j (fun _ _ => sq_nonneg _)).trans ?_
      exact (hmonoB _ sG (fun y => by positivity) (by norm_num)).trans A2
    · refine (setIntegral_mono_on (hib _ _ (continuous_finsetSum _ fun k _ => cD i j k))
        (hib _ _ sD) (isOpen_vec3Ball x₀ _).measurableSet fun y _ =>
          hsingle (fun a b => ∑ k : Fin 3, bm (D2 a b k) n (y, t) ^ 2) i j
            (fun _ _ => by positivity)).trans ?_
      exact (hmonoB _ sD (fun y => by positivity) (by norm_num)).trans A4
    · refine (setIntegral_mono_on (hib _ _ (continuous_finsetSum _ fun k _ =>
        continuous_finsetSum _ fun c _ => cE i j k c)) (hib _ _ sE)
        (isOpen_vec3Ball x₀ _).measurableSet fun y _ =>
          hsingle (fun a b => ∑ k : Fin 3, ∑ c : Fin 3,
            spatialPartial (bm (D2 a b k) n) c (y, t) ^ 2) i j
            (fun _ _ => by positivity)).trans A6
  -- pass to the limit along an almost everywhere convergent subsequence
  set B := (vec3Ball x₀ (38 / 64) ×ˢ Ioo (a + 1 / 64) t₀ : Set (Vec3 × ℝ)) with hBdef
  have hBW : B ⊆ W := by
    rintro ⟨x, t⟩ ⟨hx, ht1, ht2⟩
    refine ⟨vec3Ball_mono (by norm_num) hx, ?_, ht2⟩
    change a < t
    change a + 1 / 64 < t at ht1
    linarith only [ht1]
  have hBm : MeasurableSet B := (vorticityBox_isOpen x₀ _ _ t₀).measurableSet
  have hBb : Bornology.IsBounded B := hWb.subset hBW
  obtain ⟨φ, hφ, hae⟩ := vorticity_exists_subseq_ae (μ := volume.restrict B)
    (ι := Fin 3 × Fin 3) (f := fun p n => bm (G p.1 p.2) n) (F := fun p => G p.1 p.2)
    (fun p n => vorticity_memLp_two_of_continuous_bounded (hc _ (hG p.1 p.2) n) hBb)
    (fun p => (hG p.1 p.2).mono_measure (Measure.restrict_mono hBW le_rfl))
    (fun p => vorticityBackMollify_tendsto_restrict hWm hBm hBW (hG p.1 p.2) hεlim hεpos)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hper
  filter_upwards [hae, ae_restrict_mem hBm] with z hz hzB i j
  obtain ⟨x, t⟩ := z
  have hx : vec3EuclideanNorm (x - x₀) ≤ 38 / 64 := le_of_lt hzB.1
  have ht : t ∈ Icc (a + 1 / 64) t₀ := ⟨le_of_lt hzB.2.1, le_of_lt hzB.2.2⟩
  have hlim := hz (i, j)
  have hsq := ((continuous_pow 2).tendsto _).comp hlim
  have hbd : ∀ n, bm (G i j) (φ (n + N)) (x, t) ^ 2 ≤ Cc * (H4 + H5 + H6) := fun n =>
    hN (φ (n + N)) (le_trans (Nat.le_add_left N n) (hφ.id_le (n + N))) t ht x hx i j
  have hsq' : Tendsto (fun n => bm (G i j) (φ (n + N)) (x, t) ^ 2) atTop
      (𝓝 (G i j (x, t) ^ 2)) :=
    hsq.comp ((tendsto_add_atTop_iff_nat N).2 tendsto_id)
  have hG2 : G i j (x, t) ^ 2 ≤ Cc * (H4 + H5 + H6) := le_of_tendsto' hsq' hbd
  exact Real.abs_le_sqrt hG2

end ESS
