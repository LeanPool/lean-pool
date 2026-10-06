/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityHeatEngine
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityDivCurlSmooth

/-!
# The weak local div–curl recovery

A square-integrable space-time vector field which is weakly divergence free and whose weak
antisymmetric derivatives are square integrable has a square-integrable weak spatial gradient on
every smaller box with the same top, bounded by the data (`lem:local-div-curl`, integrated in
time). The gradient is the `L²` limit of the gradients of backward mollifications, to which the
smooth estimate applies at every time.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Integrating a time-sliced inequality over a time interval. -/
theorem vorticity_setIntegral_prod_time_mono {B B' : Set Vec3} {I : Set ℝ}
    (hI : MeasurableSet I) {f g : Vec3 × ℝ → ℝ} (hf : IntegrableOn f (B ×ˢ I))
    (hg : IntegrableOn g (B' ×ˢ I))
    (h : ∀ t ∈ I, ∫ x in B, f (x, t) ≤ ∫ x in B', g (x, t)) :
    ∫ z in B ×ˢ I, f z ≤ ∫ z in B' ×ˢ I, g z := by
  rw [vorticity_setIntegral_prod_time hf, vorticity_setIntegral_prod_time hg]
  have hf' : Integrable f ((volume.restrict B).prod (volume.restrict I)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hf
  have hg' : Integrable g ((volume.restrict B').prod (volume.restrict I)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hg
  exact setIntegral_mono_on hf'.integral_prod_right hg'.integral_prod_right hI h

/-- The smooth div–curl estimate integrated over a time interval, for smooth fields whose
divergence vanishes and whose antisymmetric derivatives are prescribed on the outer box. -/
theorem vorticityDivCurl_integrated {r R₁ C₀ : ℝ}
    (hsmooth : ∀ (x₀ : Vec3) (V : Fin 3 → Vec3 → ℝ), (∀ b, ContDiff ℝ (⊤ : ℕ∞) (V b)) →
      ∫ x in vec3Ball x₀ r, ∑ a : Fin 3, ∑ b : Fin 3, spatialDeriv (V b) a x ^ 2 ≤
        C₀ * ∫ x in vec3Ball x₀ R₁,
          ((∑ a : Fin 3, spatialDeriv (V a) a x) ^ 2 +
            ∑ a : Fin 3, ∑ b : Fin 3, (spatialDeriv (V b) a x - spatialDeriv (V a) b x) ^ 2 +
            ∑ b : Fin 3, V b x ^ 2))
    (x₀ : Vec3) (t₁ t₂ : ℝ)
    {V : Fin 3 → Vec3 × ℝ → ℝ} (hV : ∀ c, ContDiff ℝ (⊤ : ℕ∞) (V c))
    {Φ : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ} (hΦ : ∀ a c, Continuous (Φ a c))
    (hdiv : ∀ z ∈ vec3Ball x₀ R₁ ×ˢ Ioo t₁ t₂, ∑ a : Fin 3, spatialPartial (V a) a z = 0)
    (hcurl : ∀ z ∈ vec3Ball x₀ R₁ ×ˢ Ioo t₁ t₂, ∀ a c : Fin 3,
      spatialPartial (V c) a z - spatialPartial (V a) c z = Φ a c z) :
    ∫ z in vec3Ball x₀ r ×ˢ Ioo t₁ t₂, ∑ a : Fin 3, ∑ c : Fin 3, spatialPartial (V c) a z ^ 2 ≤
      C₀ * ∫ z in vec3Ball x₀ R₁ ×ˢ Ioo t₁ t₂,
        (∑ a : Fin 3, ∑ c : Fin 3, Φ a c z ^ 2 + ∑ c : Fin 3, V c z ^ 2) := by
  have hbr : Bornology.IsBounded (vec3Ball x₀ r ×ˢ Ioo t₁ t₂) :=
    vorticityBox_isBounded x₀ r _ (Metric.isBounded_Ioo t₁ t₂)
  have hbR : Bornology.IsBounded (vec3Ball x₀ R₁ ×ˢ Ioo t₁ t₂) :=
    vorticityBox_isBounded x₀ R₁ _ (Metric.isBounded_Ioo t₁ t₂)
  have hcontL : Continuous (fun z : Vec3 × ℝ =>
      ∑ a : Fin 3, ∑ c : Fin 3, spatialPartial (V c) a z ^ 2) := by
    refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun c _ => ?_
    exact (CKN.spatialPartial_contDiff (hV c) a).continuous.pow 2
  have hcontR : Continuous (fun z : Vec3 × ℝ =>
      C₀ * (∑ a : Fin 3, ∑ c : Fin 3, Φ a c z ^ 2 + ∑ c : Fin 3, V c z ^ 2)) := by
    refine continuous_const.mul (Continuous.add ?_ ?_)
    · exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun c _ =>
        (hΦ a c).pow 2
    · exact continuous_finsetSum _ fun c _ => (hV c).continuous.pow 2
  rw [← integral_const_mul]
  apply vorticity_setIntegral_prod_time_mono measurableSet_Ioo
    (vorticity_integrableOn_of_continuous_bounded hcontL hbr)
    (vorticity_integrableOn_of_continuous_bounded hcontR hbR)
  intro t ht
  let Vt : Fin 3 → Vec3 → ℝ := fun c x => V c (x, t)
  have hVt : ∀ c, ContDiff ℝ (⊤ : ℕ∞) (Vt c) := fun c =>
    (hV c).comp (contDiff_id.prodMk contDiff_const)
  have hest := hsmooth x₀ Vt hVt
  have hderiv : ∀ c a x, spatialDeriv (Vt c) a x = spatialPartial (V c) a (x, t) :=
    fun c a x => rfl
  simp only [hderiv] at hest
  refine le_trans hest ?_
  rw [← integral_const_mul]
  apply le_of_eq
  apply setIntegral_congr_fun (isOpen_vec3Ball x₀ R₁).measurableSet
  intro x hx
  have hz : (x, t) ∈ vec3Ball x₀ R₁ ×ˢ Ioo t₁ t₂ := ⟨hx, ht⟩
  simp only [hdiv (x, t) hz, hcurl (x, t) hz]
  ring

private theorem vorticityDivCurlEngine_core {r R₁ R κ C₀ : ℝ} (hrR₁ : r < R₁)
    (hR₁R : R₁ < R) (hκ : 0 < κ) (hC₀ : 0 ≤ C₀)
    (hsmooth : ∀ (x₀ : Vec3) (V : Fin 3 → Vec3 → ℝ), (∀ b, ContDiff ℝ (⊤ : ℕ∞) (V b)) →
      ∫ x in vec3Ball x₀ r, ∑ a : Fin 3, ∑ b : Fin 3, spatialDeriv (V b) a x ^ 2 ≤
        C₀ * ∫ x in vec3Ball x₀ R₁,
          ((∑ a : Fin 3, spatialDeriv (V a) a x) ^ 2 +
            ∑ a : Fin 3, ∑ b : Fin 3, (spatialDeriv (V b) a x - spatialDeriv (V a) b x) ^ 2 +
            ∑ b : Fin 3, V b x ^ 2))
    (x₀ : Vec3) (a b : ℝ) (Y : Fin 3 → Vec3 × ℝ → ℝ) (Ω : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hY : ∀ i, MemLp (Y i) 2 (volume.restrict (vec3Ball x₀ R ×ˢ Ioo a b)))
    (hΩ : ∀ i k, MemLp (Ω i k) 2 (volume.restrict (vec3Ball x₀ R ×ˢ Ioo a b)))
    (hdivw : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ R ×ˢ Ioo a b →
      ∫ y in vec3Ball x₀ R ×ˢ Ioo a b, ∑ i : Fin 3, Y i y * spatialPartial ψ i y = 0)
    (hcurlw : ∀ i k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ vec3Ball x₀ R ×ˢ Ioo a b →
      ∫ y in vec3Ball x₀ R ×ˢ Ioo a b,
          (Y k y * spatialPartial ψ i y - Y i y * spatialPartial ψ k y) =
        -∫ y in vec3Ball x₀ R ×ˢ Ioo a b, Ω i k y * ψ y) :
    ∃ G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ,
      (∀ i j, MemLp (G i j) 2 (volume.restrict (vec3Ball x₀ r ×ˢ Ioo (a + κ) b))) ∧
      (∀ i j, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ vec3Ball x₀ r ×ˢ Ioo (a + κ) b →
        ∫ y in vec3Ball x₀ r ×ˢ Ioo (a + κ) b, Y i y * spatialPartial ψ j y =
          -∫ y in vec3Ball x₀ r ×ˢ Ioo (a + κ) b, G i j y * ψ y) ∧
      ∫ y in vec3Ball x₀ r ×ˢ Ioo (a + κ) b, ∑ i : Fin 3, ∑ j : Fin 3, G i j y ^ 2 ≤
        C₀ * ∫ y in vec3Ball x₀ R ×ˢ Ioo a b,
          (∑ i : Fin 3, ∑ k : Fin 3, Ω i k y ^ 2 + ∑ i : Fin 3, Y i y ^ 2) := by
  set W := vec3Ball x₀ R ×ˢ Ioo a b with hWdef
  set W₁ := vec3Ball x₀ R₁ ×ˢ Ioo (a + κ) b with hW₁def
  set W' := vec3Ball x₀ r ×ˢ Ioo (a + κ) b with hW'def
  have hWo : IsOpen W := vorticityBox_isOpen x₀ R a b
  have hWm : MeasurableSet W := hWo.measurableSet
  have hW₁m : MeasurableSet W₁ := (vorticityBox_isOpen x₀ R₁ _ b).measurableSet
  have hW'm : MeasurableSet W' := (vorticityBox_isOpen x₀ r _ b).measurableSet
  have hW₁W : W₁ ⊆ W := by
    intro z hz
    refine ⟨lt_trans hz.1 hR₁R, ?_, hz.2.2⟩
    have := hz.2.1
    linarith only [this, hκ]
  have hW'W₁ : W' ⊆ W₁ := fun z hz => ⟨lt_trans hz.1 hrR₁, hz.2⟩
  have hW'W : W' ⊆ W := hW'W₁.trans hW₁W
  have hWb : Bornology.IsBounded W := vorticityBox_isBounded x₀ R _ (Metric.isBounded_Ioo a b)
  have hW₁b : Bornology.IsBounded W₁ := hWb.subset hW₁W
  have hW'b : Bornology.IsBounded W' := hWb.subset hW'W
  set ε₀ : ℝ := min ((R - R₁) / 2) (κ / 6) with hε₀def
  have hε₀ : 0 < ε₀ := lt_min (by linarith only [hR₁R]) (by linarith only [hκ])
  obtain ⟨ε, hεpos, hεlim, hεle⟩ := vorticity_engine_radii hε₀
  have hYi : ∀ i, IntegrableOn (Y i) W := fun i => vorticity_integrableOn_of_memLp_box (hY i)
  have hΩi : ∀ i k, IntegrableOn (Ω i k) W := fun i k =>
    vorticity_integrableOn_of_memLp_box (hΩ i k)
  have hYloc : ∀ i, LocallyIntegrable (W.indicator (Y i)) (volume : Measure (Vec3 × ℝ)) :=
    fun i => ((integrable_indicator_iff hWm).2 (hYi i)).locallyIntegrable
  have hΩloc : ∀ i k, LocallyIntegrable (W.indicator (Ω i k)) (volume : Measure (Vec3 × ℝ)) :=
    fun i k => ((integrable_indicator_iff hWm).2 (hΩi i k)).locallyIntegrable
  set Yn : ℕ → Fin 3 → Vec3 × ℝ → ℝ :=
    fun n i => vorticityBackMollify W (Y i) (ε n) (hεpos n) with hYndef
  set Ωn : ℕ → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ :=
    fun n i k => vorticityBackMollify W (Ω i k) (ε n) (hεpos n) with hΩndef
  have hYn : ∀ n i, ContDiff ℝ (⊤ : ℕ∞) (Yn n i) := fun n i =>
    vorticityBackMollify_contDiff (hεpos n) (hYloc i)
  have hΩn : ∀ n i k, ContDiff ℝ (⊤ : ℕ∞) (Ωn n i k) := fun n i k =>
    vorticityBackMollify_contDiff (hεpos n) (hΩloc i k)
  have hball : ∀ n, ∀ z ∈ W₁, Metric.closedBall (z - vorticityBackShift (ε n)) (ε n) ⊆ W :=
    fun n z hz => vorticityBackBall_subset (x₀ := x₀) (ρ := R₁) (R := R) (a := a) (b := b)
      (κ := κ) (hεpos n)
      (by linarith only [hεle n, min_le_left ((R - R₁) / 2) (κ / 6)])
      (by linarith only [hεle n, min_le_right ((R - R₁) / 2) (κ / 6)])
      ⟨hz.1, hz.2.1, le_of_lt hz.2.2⟩
  have hdivn : ∀ n, ∀ z ∈ W₁, ∑ i : Fin 3, spatialPartial (Yn n i) i z = 0 := fun n z hz =>
    vorticityBackMollify_div_of_weak hWo hYi hdivw (hεpos n) (hball n z hz)
  have hcurln : ∀ n, ∀ z ∈ W₁, ∀ i k : Fin 3,
      spatialPartial (Yn n k) i z - spatialPartial (Yn n i) k z = Ωn n i k z :=
    fun n z hz i k => vorticityBackMollify_curl_of_weak hWo (hYi i) (hYi k)
      (hcurlw i k) (hεpos n) (hball n z hz)
  -- square integrability and convergence
  have hYS : ∀ i S, S ⊆ W → MemLp (Y i) 2 (volume.restrict S) := fun i S hS =>
    (hY i).mono_measure (Measure.restrict_mono hS le_rfl)
  have hΩS : ∀ i k S, S ⊆ W → MemLp (Ω i k) 2 (volume.restrict S) := fun i k S hS =>
    (hΩ i k).mono_measure (Measure.restrict_mono hS le_rfl)
  have hYnS : ∀ n i S, Bornology.IsBounded S → MemLp (Yn n i) 2 (volume.restrict S) :=
    fun n i S hS => vorticity_memLp_two_of_continuous_bounded (hYn n i).continuous hS
  have hΩnS : ∀ n i k S, Bornology.IsBounded S → MemLp (Ωn n i k) 2 (volume.restrict S) :=
    fun n i k S hS => vorticity_memLp_two_of_continuous_bounded (hΩn n i k).continuous hS
  have hdYnS : ∀ n i j S, Bornology.IsBounded S →
      MemLp (fun z : Vec3 × ℝ => spatialPartial (Yn n i) j z) 2 (volume.restrict S) :=
    fun n i j S hS => vorticity_memLp_two_of_continuous_bounded
      (CKN.spatialPartial_contDiff (hYn n i) j).continuous hS
  have hYconv : ∀ i S, MeasurableSet S → S ⊆ W →
      Tendsto (fun n => eLpNorm (Yn n i - Y i) 2 (volume.restrict S)) atTop (𝓝 0) :=
    fun i S hS hSW => vorticityBackMollify_tendsto_restrict hWm hS hSW (hY i) hεlim hεpos
  have hΩconv : ∀ i k S, MeasurableSet S → S ⊆ W →
      Tendsto (fun n => eLpNorm (Ωn n i k - Ω i k) 2 (volume.restrict S)) atTop (𝓝 0) :=
    fun i k S hS hSW => vorticityBackMollify_tendsto_restrict hWm hS hSW (hΩ i k) hεlim hεpos
  have hYsq : ∀ i, Tendsto (fun n => ∫ z in W₁, (Yn n i z - Y i z) ^ 2) atTop (𝓝 0) :=
    fun i => vorticity_integral_sq_tendsto_zero (f := fun n => Yn n i - Y i)
      (fun n => (hYnS n i W₁ hW₁b).sub (hYS i W₁ hW₁W)) (hYconv i W₁ hW₁m hW₁W)
  have hΩsq : ∀ i k, Tendsto (fun n => ∫ z in W₁, (Ωn n i k z - Ω i k z) ^ 2) atTop (𝓝 0) :=
    fun i k => vorticity_integral_sq_tendsto_zero (f := fun n => Ωn n i k - Ω i k)
      (fun n => (hΩnS n i k W₁ hW₁b).sub (hΩS i k W₁ hW₁W)) (hΩconv i k W₁ hW₁m hW₁W)
  -- the estimate for differences
  have hdiff : ∀ n m : ℕ,
      ∫ z in W', ∑ j : Fin 3, ∑ i : Fin 3,
          (spatialPartial (Yn n i) j z - spatialPartial (Yn m i) j z) ^ 2 ≤
        C₀ * ((∑ j : Fin 3, ∑ i : Fin 3, ∫ z in W₁, (Ωn n j i z - Ωn m j i z) ^ 2) +
          ∑ i : Fin 3, ∫ z in W₁, (Yn n i z - Yn m i z) ^ 2) := by
    intro n m
    have hD : ∀ c, ContDiff ℝ (⊤ : ℕ∞) (fun z => Yn n c z - Yn m c z) := fun c =>
      (hYn n c).sub (hYn m c)
    have hΦ : ∀ a c, Continuous (fun z => Ωn n a c z - Ωn m a c z) := fun a c =>
      (hΩn n a c).continuous.sub (hΩn m a c).continuous
    have hest := vorticityDivCurl_integrated hsmooth x₀ (a + κ) b hD hΦ
      (fun z hz => by
        simp only [vorticity_spatialPartial_sub (hYn n _) (hYn m _), Finset.sum_sub_distrib,
          hdivn n z hz, hdivn m z hz, sub_zero])
      (fun z hz i k => by
        rw [vorticity_spatialPartial_sub (hYn n k) (hYn m k),
          vorticity_spatialPartial_sub (hYn n i) (hYn m i)]
        have h1 := hcurln n z hz i k
        have h2 := hcurln m z hz i k
        linarith only [h1, h2])
    have hlhs : ∀ z, ∑ j : Fin 3, ∑ i : Fin 3,
        spatialPartial (fun z : Vec3 × ℝ => Yn n i z - Yn m i z) j z ^ 2 =
        ∑ j : Fin 3, ∑ i : Fin 3,
          (spatialPartial (Yn n i) j z - spatialPartial (Yn m i) j z) ^ 2 := by
      intro z
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
        rw [vorticity_spatialPartial_sub (hYn n i) (hYn m i) j z]
    have hint1 : ∀ j i, IntegrableOn (fun z => (Ωn n j i z - Ωn m j i z) ^ 2) W₁ :=
      fun j i => vorticity_integrableOn_of_continuous_bounded ((hΦ j i).pow 2) hW₁b
    have hint2 : ∀ i, IntegrableOn (fun z => (Yn n i z - Yn m i z) ^ 2) W₁ := fun i =>
      vorticity_integrableOn_of_continuous_bounded ((hD i).continuous.pow 2) hW₁b
    have hsplitR : ∫ z in W₁, (∑ j : Fin 3, ∑ i : Fin 3, (Ωn n j i z - Ωn m j i z) ^ 2 +
        ∑ i : Fin 3, (Yn n i z - Yn m i z) ^ 2) =
        (∑ j : Fin 3, ∑ i : Fin 3, ∫ z in W₁, (Ωn n j i z - Ωn m j i z) ^ 2) +
          ∑ i : Fin 3, ∫ z in W₁, (Yn n i z - Yn m i z) ^ 2 := by
      rw [integral_add (integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ =>
          hint1 j i) (integrable_finsetSum _ fun i _ => hint2 i),
        integral_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ => hint1 j i,
        integral_finsetSum _ fun i _ => hint2 i]
      rw [Finset.sum_congr rfl fun j _ => integral_finsetSum _ fun i _ => hint1 j i]
    calc
      _ = ∫ z in W', ∑ j : Fin 3, ∑ i : Fin 3,
          spatialPartial (fun z : Vec3 × ℝ => Yn n i z - Yn m i z) j z ^ 2 :=
        integral_congr_ae (Eventually.of_forall fun z => (hlhs z).symm)
      _ ≤ _ := hest
      _ = _ := by rw [hsplitR]
  have hrhs : Tendsto (fun p : ℕ × ℕ => C₀ *
      ((∑ j : Fin 3, ∑ i : Fin 3, ∫ z in W₁, (Ωn p.1 j i z - Ωn p.2 j i z) ^ 2) +
        ∑ i : Fin 3, ∫ z in W₁, (Yn p.1 i z - Yn p.2 i z) ^ 2)) atTop (𝓝 0) := by
    have hY2 : ∀ i : Fin 3, Tendsto (fun n => 2 * (∫ z in W₁, (Yn n i z - Y i z) ^ 2))
        atTop (𝓝 0) := fun i => by simpa using (hYsq i).const_mul 2
    have hΩ2 : ∀ j i : Fin 3, Tendsto (fun n => 2 * (∫ z in W₁, (Ωn n j i z - Ω j i z) ^ 2))
        atTop (𝓝 0) := fun j i => by simpa using (hΩsq j i).const_mul 2
    have hbound : Tendsto (fun p : ℕ × ℕ => C₀ *
        ((∑ j : Fin 3, ∑ i : Fin 3, (2 * (∫ z in W₁, (Ωn p.1 j i z - Ω j i z) ^ 2) +
          2 * (∫ z in W₁, (Ωn p.2 j i z - Ω j i z) ^ 2))) +
        ∑ i : Fin 3, (2 * (∫ z in W₁, (Yn p.1 i z - Y i z) ^ 2) +
          2 * (∫ z in W₁, (Yn p.2 i z - Y i z) ^ 2)))) atTop (𝓝 0) := by
      have h1 := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun j _ =>
        tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun i _ =>
          vorticity_tendsto_prod_add (hΩ2 j i) (hΩ2 j i)
      have h2 := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun i _ =>
        vorticity_tendsto_prod_add (hY2 i) (hY2 i)
      simp only [Finset.sum_const_zero] at h1 h2
      simpa using (h1.add h2).const_mul C₀
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
      (fun p => ?_) (fun p => ?_)
    · exact mul_nonneg hC₀ (add_nonneg
        (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ =>
          integral_nonneg fun z => sq_nonneg _)
        (Finset.sum_nonneg fun i _ => integral_nonneg fun z => sq_nonneg _))
    · apply mul_le_mul_of_nonneg_left _ hC₀
      apply add_le_add
      · exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ =>
          vorticity_integral_sq_sub_le (hΩnS p.1 j i W₁ hW₁b) (hΩnS p.2 j i W₁ hW₁b)
            (hΩS j i W₁ hW₁W)
      · exact Finset.sum_le_sum fun i _ => vorticity_integral_sq_sub_le
          (hYnS p.1 i W₁ hW₁b) (hYnS p.2 i W₁ hW₁b) (hYS i W₁ hW₁W)
  have hcauchy : ∀ i j : Fin 3, Tendsto (fun p : ℕ × ℕ =>
      eLpNorm ((fun z : Vec3 × ℝ => spatialPartial (Yn p.1 i) j z) -
        (fun z : Vec3 × ℝ => spatialPartial (Yn p.2 i) j z)) 2 (volume.restrict W'))
      atTop (𝓝 0) := by
    intro i j
    have hsq : Tendsto (fun p : ℕ × ℕ => ∫ z in W', (spatialPartial (Yn p.1 i) j z -
        spatialPartial (Yn p.2 i) j z) ^ 2) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrhs
        (fun p => integral_nonneg fun z => sq_nonneg _) (fun p => ?_)
      refine le_trans ?_ (hdiff p.1 p.2)
      have hint : ∀ k l : Fin 3, IntegrableOn (fun z => (spatialPartial (Yn p.1 l) k z -
          spatialPartial (Yn p.2 l) k z) ^ 2) W' := fun k l =>
        vorticity_integrableOn_of_continuous_bounded
          (((CKN.spatialPartial_contDiff (hYn p.1 l) k).continuous.sub
            (CKN.spatialPartial_contDiff (hYn p.2 l) k).continuous).pow 2) hW'b
      apply integral_mono (hint j i)
        (integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l)
      intro z
      have h1 : (spatialPartial (Yn p.1 i) j z - spatialPartial (Yn p.2 i) j z) ^ 2 ≤
          ∑ l : Fin 3, (spatialPartial (Yn p.1 l) j z - spatialPartial (Yn p.2 l) j z) ^ 2 :=
        Finset.single_le_sum (f := fun l : Fin 3 => (spatialPartial (Yn p.1 l) j z -
          spatialPartial (Yn p.2 l) j z) ^ 2) (fun l _ => sq_nonneg _) (Finset.mem_univ i)
      have h2 : ∑ l : Fin 3, (spatialPartial (Yn p.1 l) j z -
          spatialPartial (Yn p.2 l) j z) ^ 2 ≤ ∑ k : Fin 3, ∑ l : Fin 3,
            (spatialPartial (Yn p.1 l) k z - spatialPartial (Yn p.2 l) k z) ^ 2 :=
        Finset.single_le_sum (f := fun k : Fin 3 => ∑ l : Fin 3,
          (spatialPartial (Yn p.1 l) k z - spatialPartial (Yn p.2 l) k z) ^ 2)
          (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _) (Finset.mem_univ j)
      exact h1.trans h2
    exact vorticity_tendsto_eLpNorm_of_integral_sq
      (fun p => (hdYnS p.1 i j W' hW'b).sub (hdYnS p.2 i j W' hW'b)) hsq
  have hlim : ∀ i j : Fin 3, ∃ g : Vec3 × ℝ → ℝ, MemLp g 2 (volume.restrict W') ∧
      Tendsto (fun n => eLpNorm ((fun z : Vec3 × ℝ => spatialPartial (Yn n i) j z) - g) 2
        (volume.restrict W')) atTop (𝓝 0) := fun i j =>
    vorticityL2_exists_limit (fun n => hdYnS n i j W' hW'b) (hcauchy i j)
  choose G hGmem hGlim using hlim
  refine ⟨G, hGmem, ?_, ?_⟩
  · intro i j
    exact vorticity_weakPartial_of_tendsto (fun n => hYn n i) (fun n => hYnS n i W' hW'b)
      (fun n => hdYnS n i j W' hW'b) (hYS i W' hW'W) (hGmem i j) (hYconv i W' hW'm hW'W)
      (hGlim i j)
  · have hG2 : ∀ i j, IntegrableOn (fun y => G i j y ^ 2) W' := fun i j =>
      (memLp_two_iff_integrable_sq (hGmem i j).aestronglyMeasurable).1 (hGmem i j)
    have hY2W : ∀ i, IntegrableOn (fun y => Y i y ^ 2) W := fun i =>
      (memLp_two_iff_integrable_sq (hY i).aestronglyMeasurable).1 (hY i)
    have hΩ2W : ∀ i k, IntegrableOn (fun y => Ω i k y ^ 2) W := fun i k =>
      (memLp_two_iff_integrable_sq (hΩ i k).aestronglyMeasurable).1 (hΩ i k)
    have happrox : ∀ n, ∑ i : Fin 3, ∑ j : Fin 3, ∫ z in W', spatialPartial (Yn n i) j z ^ 2 ≤
        C₀ * ((∑ j : Fin 3, ∑ i : Fin 3, ∫ z in W₁, Ωn n j i z ^ 2) +
          ∑ i : Fin 3, ∫ z in W₁, Yn n i z ^ 2) := by
      intro n
      have hest := vorticityDivCurl_integrated hsmooth x₀ (a + κ) b (hYn n)
        (fun j i => (hΩn n j i).continuous) (hdivn n) (hcurln n)
      have hint : ∀ k l : Fin 3, IntegrableOn (fun z => spatialPartial (Yn n l) k z ^ 2) W' :=
        fun k l => vorticity_integrableOn_of_continuous_bounded
          ((CKN.spatialPartial_contDiff (hYn n l) k).continuous.pow 2) hW'b
      have hint1 : ∀ j i, IntegrableOn (fun z => Ωn n j i z ^ 2) W₁ := fun j i =>
        vorticity_integrableOn_of_continuous_bounded ((hΩn n j i).continuous.pow 2) hW₁b
      have hint2 : ∀ i, IntegrableOn (fun z => Yn n i z ^ 2) W₁ := fun i =>
        vorticity_integrableOn_of_continuous_bounded ((hYn n i).continuous.pow 2) hW₁b
      calc
        _ = ∫ z in W', ∑ j : Fin 3, ∑ i : Fin 3, spatialPartial (Yn n i) j z ^ 2 := by
          symm
          calc
            _ = ∑ j : Fin 3, ∫ z in W', ∑ i : Fin 3, spatialPartial (Yn n i) j z ^ 2 :=
              integral_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ => hint j i
            _ = ∑ j : Fin 3, ∑ i : Fin 3, ∫ z in W', spatialPartial (Yn n i) j z ^ 2 :=
              Finset.sum_congr rfl fun j _ => integral_finsetSum _ fun i _ => hint j i
            _ = _ := Finset.sum_comm
        _ ≤ _ := hest
        _ = _ := by
          rw [integral_add (integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ =>
              hint1 j i) (integrable_finsetSum _ fun i _ => hint2 i),
            integral_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ => hint1 j i,
            integral_finsetSum _ fun i _ => hint2 i,
            Finset.sum_congr rfl fun j _ => integral_finsetSum _ fun i _ => hint1 j i]
    have hL : Tendsto (fun n => ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z in W', spatialPartial (Yn n i) j z ^ 2) atTop
        (𝓝 (∑ i : Fin 3, ∑ j : Fin 3, ∫ z in W', G i j z ^ 2)) :=
      tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
        vorticity_tendsto_integral_sq (fun n => hdYnS n i j W' hW'b) (hGmem i j) (hGlim i j)
    have hR : Tendsto (fun n => C₀ * ((∑ j : Fin 3, ∑ i : Fin 3, ∫ z in W₁, Ωn n j i z ^ 2) +
          ∑ i : Fin 3, ∫ z in W₁, Yn n i z ^ 2)) atTop
        (𝓝 (C₀ * ((∑ j : Fin 3, ∑ i : Fin 3, ∫ z in W₁, Ω j i z ^ 2) +
          ∑ i : Fin 3, ∫ z in W₁, Y i z ^ 2))) := by
      apply Tendsto.const_mul
      apply Tendsto.add
      · exact tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun i _ =>
          vorticity_tendsto_integral_sq (fun n => hΩnS n j i W₁ hW₁b) (hΩS j i W₁ hW₁W)
            (hΩconv j i W₁ hW₁m hW₁W)
      · exact tendsto_finsetSum _ fun i _ => vorticity_tendsto_integral_sq
          (fun n => hYnS n i W₁ hW₁b) (hYS i W₁ hW₁W) (hYconv i W₁ hW₁m hW₁W)
    have hlimle := le_of_tendsto_of_tendsto' hL hR happrox
    have hmono : (∑ j : Fin 3, ∑ i : Fin 3, ∫ z in W₁, Ω j i z ^ 2) +
        ∑ i : Fin 3, ∫ z in W₁, Y i z ^ 2 ≤
        ∫ y in W, (∑ i : Fin 3, ∑ k : Fin 3, Ω i k y ^ 2 + ∑ i : Fin 3, Y i y ^ 2) := by
      have hintW : IntegrableOn (fun y => ∑ i : Fin 3, ∑ k : Fin 3, Ω i k y ^ 2 +
          ∑ i : Fin 3, Y i y ^ 2) W :=
        (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hΩ2W i k).add
          (integrable_finsetSum _ fun i _ => hY2W i)
      calc
        _ = ∫ y in W₁, (∑ i : Fin 3, ∑ k : Fin 3, Ω i k y ^ 2 + ∑ i : Fin 3, Y i y ^ 2) := by
          rw [integral_add (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
              (hΩ2W i k).mono_set hW₁W)
              (integrable_finsetSum _ fun i _ => (hY2W i).mono_set hW₁W),
            integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
              (hΩ2W i k).mono_set hW₁W,
            integral_finsetSum _ fun i _ => (hY2W i).mono_set hW₁W,
            Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun k _ =>
              (hΩ2W i k).mono_set hW₁W]
        _ ≤ _ := setIntegral_mono_set hintW
          (Eventually.of_forall fun y => add_nonneg
            (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _)
            (Finset.sum_nonneg fun i _ => sq_nonneg _))
          (Eventually.of_forall hW₁W)
    calc
      ∫ y in W', ∑ i : Fin 3, ∑ j : Fin 3, G i j y ^ 2 =
          ∑ i : Fin 3, ∑ j : Fin 3, ∫ y in W', G i j y ^ 2 := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hG2 i j]
        exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hG2 i j
      _ ≤ _ := hlimle
      _ ≤ _ := mul_le_mul_of_nonneg_left hmono hC₀

/-- The weak local div–curl recovery on boxes (`lem:local-div-curl`, integrated in time). -/
theorem vorticityDivCurlEngine {r R κ : ℝ} (hr : 0 < r) (hrR : r < R) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Vec3) (a b : ℝ) (Y : Fin 3 → Vec3 × ℝ → ℝ)
      (Ω : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ),
      (∀ i, MemLp (Y i) 2 (volume.restrict (vec3Ball x₀ R ×ˢ Ioo a b))) →
      (∀ i k, MemLp (Ω i k) 2 (volume.restrict (vec3Ball x₀ R ×ˢ Ioo a b))) →
      (∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ vec3Ball x₀ R ×ˢ Ioo a b →
        ∫ y in vec3Ball x₀ R ×ˢ Ioo a b, ∑ i : Fin 3, Y i y * spatialPartial ψ i y = 0) →
      (∀ i k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ → tsupport ψ ⊆ vec3Ball x₀ R ×ˢ Ioo a b →
        ∫ y in vec3Ball x₀ R ×ˢ Ioo a b,
            (Y k y * spatialPartial ψ i y - Y i y * spatialPartial ψ k y) =
          -∫ y in vec3Ball x₀ R ×ˢ Ioo a b, Ω i k y * ψ y) →
      ∃ G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ,
        (∀ i j, MemLp (G i j) 2 (volume.restrict (vec3Ball x₀ r ×ˢ Ioo (a + κ) b))) ∧
        (∀ i j, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ vec3Ball x₀ r ×ˢ Ioo (a + κ) b →
          ∫ y in vec3Ball x₀ r ×ˢ Ioo (a + κ) b, Y i y * spatialPartial ψ j y =
            -∫ y in vec3Ball x₀ r ×ˢ Ioo (a + κ) b, G i j y * ψ y) ∧
        ∫ y in vec3Ball x₀ r ×ˢ Ioo (a + κ) b, ∑ i : Fin 3, ∑ j : Fin 3, G i j y ^ 2 ≤
          C * ∫ y in vec3Ball x₀ R ×ˢ Ioo a b,
            (∑ i : Fin 3, ∑ k : Fin 3, Ω i k y ^ 2 + ∑ i : Fin 3, Y i y ^ 2) := by
  have hrR₁ : r < (r + R) / 2 := by linarith only [hrR]
  have hR₁R : (r + R) / 2 < R := by linarith only [hrR]
  obtain ⟨C₀, hC₀, hsmooth⟩ := vorticityDivCurlSmooth_local hr hrR₁
  exact ⟨C₀, hC₀, fun x₀ a b Y Ω hY hΩ hdivw hcurlw =>
    vorticityDivCurlEngine_core hrR₁ hR₁R hκ hC₀ hsmooth x₀ a b Y Ω hY hΩ hdivw hcurlw⟩

end ESS
