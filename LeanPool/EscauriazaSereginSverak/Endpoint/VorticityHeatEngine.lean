/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityL2Tools
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityHeatSmooth

/-!
# The weak local heat gain

A square-integrable distributional solution of the heat equation with a square-integrable
divergence-form source on a space-time box has a square-integrable weak spatial gradient on every
smaller box with the same top, with a bound by the data (the gradient part of
`lem:localized-vorticity-energy` and `lem:local-heat-gain`). The gradient is the `L²` limit of
the gradients of backward mollifications, which solve the equation pointwise up to the top.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Space-time boxes over Euclidean balls are bounded. -/
theorem vorticityBox_isBounded (x₀ : Vec3) (R : ℝ) (I : Set ℝ) (hI : Bornology.IsBounded I) :
    Bornology.IsBounded (vec3Ball x₀ R ×ˢ I) :=
  (Metric.isBounded_closedBall.subset (vorticityHeatSmooth_vec3Ball_subset x₀ R)).prod hI

/-- Space-time boxes over Euclidean balls with open time intervals are open. -/
theorem vorticityBox_isOpen (x₀ : Vec3) (R a b : ℝ) :
    IsOpen (vec3Ball x₀ R ×ˢ Ioo a b) := by
  have hball : IsOpen (vec3Ball x₀ R) := by
    have : vec3Ball x₀ R = (fun y => vec3EuclideanNorm (y - x₀)) ⁻¹' Iio R := rfl
    rw [this]
    refine isOpen_Iio.preimage ?_
    unfold vec3EuclideanNorm
    fun_prop
  exact hball.prod isOpen_Ioo

/-- A square-integrable function on a bounded box is integrable there. -/
theorem vorticity_integrableOn_of_memLp_box {x₀ : Vec3} {R a b : ℝ} {f : Vec3 × ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (vec3Ball x₀ R ×ˢ Ioo a b))) :
    IntegrableOn f (vec3Ball x₀ R ×ˢ Ioo a b) := by
  have hfin : volume (vec3Ball x₀ R ×ˢ Ioo a b) < ∞ :=
    (vorticityBox_isBounded x₀ R (Ioo a b) (Metric.isBounded_Ioo a b)).measure_lt_top
  have : IsFiniteMeasure (volume.restrict (vec3Ball x₀ R ×ˢ Ioo a b)) :=
    isFiniteMeasure_restrict.2 hfin.ne
  exact hf.integrable (by norm_num)

/-- The shrinking radii of the backward mollifications used in the engines. -/
theorem vorticity_engine_radii {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧ ∀ n, ε n ≤ ε₀ := by
  refine ⟨fun n => ε₀ / ((n : ℝ) + 2), fun n => by positivity, ?_, fun n => ?_⟩
  · have h : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    simpa [div_eq_mul_inv] using h.inv_tendsto_atTop.const_mul ε₀
  · rw [div_le_iff₀ (by positivity)]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith only [hε₀, hn]

/-- A double sequence of sums of null sequences is null along the product filter. -/
theorem vorticity_tendsto_prod_add {a b : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0)) :
    Tendsto (fun p : ℕ × ℕ => a p.1 + b p.2) atTop (𝓝 0) := by
  have h1 : Tendsto (fun p : ℕ × ℕ => a p.1) atTop (𝓝 0) := by
    rw [← prod_atTop_atTop_eq]
    exact ha.comp tendsto_fst
  have h2 : Tendsto (fun p : ℕ × ℕ => b p.2) atTop (𝓝 0) := by
    rw [← prod_atTop_atTop_eq]
    exact hb.comp tendsto_snd
  simpa using h1.add h2

private theorem vorticityHeatEngine_core {r R₁ R κ C₀ : ℝ} (hrR₁ : r < R₁)
    (hR₁R : R₁ < R) (hκ : 0 < κ) (hC₀ : 0 ≤ C₀)
    (hsmooth : ∀ (x₀ : Vec3) (a b : ℝ) (w : Vec3 × ℝ → ℝ) (F : Fin 3 → Vec3 × ℝ → ℝ),
      a + κ / 2 ≤ b → b ≤ a + 1 → ContDiff ℝ (⊤ : ℕ∞) w → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (F j)) →
      (∀ z ∈ vec3Ball x₀ R₁ ×ˢ Ioo a b,
        timePartial w z - ∑ j : Fin 3, spatialSecondPartial w j j z =
          ∑ j : Fin 3, spatialPartial (F j) j z) →
      (∀ t ∈ Icc (a + κ / 2) b,
        ∫ x in vec3Ball x₀ r, w (x, t) ^ 2 ≤
          C₀ * ∫ z in vec3Ball x₀ R₁ ×ˢ Ioo a b, (w z ^ 2 + ∑ j : Fin 3, F j z ^ 2)) ∧
      ∫ z in vec3Ball x₀ r ×ˢ Ioo (a + κ / 2) b, ∑ j : Fin 3, spatialPartial w j z ^ 2 ≤
        C₀ * ∫ z in vec3Ball x₀ R₁ ×ˢ Ioo a b, (w z ^ 2 + ∑ j : Fin 3, F j z ^ 2))
    (x₀ : Vec3) (a b : ℝ) (w : Vec3 × ℝ → ℝ) (F : Fin 3 → Vec3 × ℝ → ℝ)
    (hab : a + κ < b) (hba : b ≤ a + 1)
    (hw : MemLp w 2 (volume.restrict (vec3Ball x₀ R ×ˢ Ioo a b)))
    (hF : ∀ j, MemLp (F j) 2 (volume.restrict (vec3Ball x₀ R ×ˢ Ioo a b)))
    (hweak : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ R ×ˢ Ioo a b →
      ∫ y in vec3Ball x₀ R ×ˢ Ioo a b,
          w y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
        -∫ y in vec3Ball x₀ R ×ˢ Ioo a b, ∑ j : Fin 3, F j y * spatialPartial ψ j y) :
    ∃ G : Fin 3 → Vec3 × ℝ → ℝ,
      (∀ j, MemLp (G j) 2 (volume.restrict (vec3Ball x₀ r ×ˢ Ioo (a + κ) b))) ∧
      (∀ j, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ vec3Ball x₀ r ×ˢ Ioo (a + κ) b →
        ∫ y in vec3Ball x₀ r ×ˢ Ioo (a + κ) b, w y * spatialPartial ψ j y =
          -∫ y in vec3Ball x₀ r ×ˢ Ioo (a + κ) b, G j y * ψ y) ∧
      ∫ y in vec3Ball x₀ r ×ˢ Ioo (a + κ) b, ∑ j : Fin 3, G j y ^ 2 ≤
        C₀ * ∫ y in vec3Ball x₀ R ×ˢ Ioo a b, (w y ^ 2 + ∑ j : Fin 3, F j y ^ 2) := by
  set W := vec3Ball x₀ R ×ˢ Ioo a b with hWdef
  set W₁ := vec3Ball x₀ R₁ ×ˢ Ioo (a + κ / 2) b with hW₁def
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
  have hW'W₁ : W' ⊆ W₁ := by
    intro z hz
    refine ⟨lt_trans hz.1 hrR₁, ?_, hz.2.2⟩
    have := hz.2.1
    linarith only [this, hκ]
  have hW'W : W' ⊆ W := hW'W₁.trans hW₁W
  have hWb : Bornology.IsBounded W := vorticityBox_isBounded x₀ R _ (Metric.isBounded_Ioo a b)
  have hW₁b : Bornology.IsBounded W₁ := hWb.subset hW₁W
  have hW'b : Bornology.IsBounded W' := hWb.subset hW'W
  -- the mollification radii
  set ε₀ : ℝ := min ((R - R₁) / 2) (κ / 12) with hε₀def
  have hε₀ : 0 < ε₀ := lt_min (by linarith only [hR₁R]) (by linarith only [hκ])
  obtain ⟨ε, hεpos, hεlim, hεle⟩ := vorticity_engine_radii hε₀
  have hwi : IntegrableOn w W := vorticity_integrableOn_of_memLp_box hw
  have hFi : ∀ j, IntegrableOn (F j) W := fun j => vorticity_integrableOn_of_memLp_box (hF j)
  have hwloc : LocallyIntegrable (W.indicator w) (volume : Measure (Vec3 × ℝ)) :=
    ((integrable_indicator_iff hWm).2 hwi).locallyIntegrable
  have hFloc : ∀ j, LocallyIntegrable (W.indicator (F j)) (volume : Measure (Vec3 × ℝ)) :=
    fun j => ((integrable_indicator_iff hWm).2 (hFi j)).locallyIntegrable
  set wn : ℕ → Vec3 × ℝ → ℝ := fun n => vorticityBackMollify W w (ε n) (hεpos n) with hwndef
  set Fn : ℕ → Fin 3 → Vec3 × ℝ → ℝ :=
    fun n j => vorticityBackMollify W (F j) (ε n) (hεpos n) with hFndef
  have hwn : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (wn n) := fun n =>
    vorticityBackMollify_contDiff (hεpos n) hwloc
  have hFn : ∀ n j, ContDiff ℝ (⊤ : ℕ∞) (Fn n j) := fun n j =>
    vorticityBackMollify_contDiff (hεpos n) (hFloc j)
  -- the pointwise equation below the top
  have heqn : ∀ n, ∀ z ∈ vec3Ball x₀ R₁ ×ˢ Ioo (a + κ / 2) b,
      timePartial (wn n) z - ∑ j : Fin 3, spatialSecondPartial (wn n) j j z =
        ∑ j : Fin 3, spatialPartial (Fn n j) j z := by
    intro n z hz
    have hball := vorticityBackBall_subset (x₀ := x₀) (ρ := R₁) (R := R) (a := a) (b := b)
      (κ := κ / 2) (hεpos n)
      (by linarith only [hεle n, min_le_left ((R - R₁) / 2) (κ / 12)])
      (by linarith only [hεle n, min_le_right ((R - R₁) / 2) (κ / 12)])
      ⟨hz.1, hz.2.1, le_of_lt hz.2.2⟩
    exact vorticityBackMollify_heat_of_weak hWo hwi hFi hweak (hεpos n) hball
  -- square integrability and convergence of the approximations
  have hwS : ∀ S, S ⊆ W → MemLp w 2 (volume.restrict S) := fun S hS =>
    hw.mono_measure (Measure.restrict_mono hS le_rfl)
  have hFS : ∀ j S, S ⊆ W → MemLp (F j) 2 (volume.restrict S) := fun j S hS =>
    (hF j).mono_measure (Measure.restrict_mono hS le_rfl)
  have hwnS : ∀ n S, Bornology.IsBounded S → MemLp (wn n) 2 (volume.restrict S) :=
    fun n S hS => vorticity_memLp_two_of_continuous_bounded (hwn n).continuous hS
  have hFnS : ∀ n j S, Bornology.IsBounded S → MemLp (Fn n j) 2 (volume.restrict S) :=
    fun n j S hS => vorticity_memLp_two_of_continuous_bounded (hFn n j).continuous hS
  have hdwnS : ∀ n j S, Bornology.IsBounded S →
      MemLp (fun z : Vec3 × ℝ => spatialPartial (wn n) j z) 2 (volume.restrict S) :=
    fun n j S hS => vorticity_memLp_two_of_continuous_bounded
      (CKN.spatialPartial_contDiff (hwn n) j).continuous hS
  have hwconv : ∀ S, MeasurableSet S → S ⊆ W →
      Tendsto (fun n => eLpNorm (wn n - w) 2 (volume.restrict S)) atTop (𝓝 0) :=
    fun S hS hSW => vorticityBackMollify_tendsto_restrict hWm hS hSW hw hεlim hεpos
  have hFconv : ∀ j S, MeasurableSet S → S ⊆ W →
      Tendsto (fun n => eLpNorm (Fn n j - F j) 2 (volume.restrict S)) atTop (𝓝 0) :=
    fun j S hS hSW => vorticityBackMollify_tendsto_restrict hWm hS hSW (hF j) hεlim hεpos
  have hwsq : Tendsto (fun n => ∫ z in W₁, (wn n z - w z) ^ 2) atTop (𝓝 0) :=
    vorticity_integral_sq_tendsto_zero (f := fun n => wn n - w)
      (fun n => (hwnS n W₁ hW₁b).sub (hwS W₁ hW₁W)) (hwconv W₁ hW₁m hW₁W)
  have hFsq : ∀ j, Tendsto (fun n => ∫ z in W₁, (Fn n j z - F j z) ^ 2) atTop (𝓝 0) :=
    fun j => vorticity_integral_sq_tendsto_zero (f := fun n => Fn n j - F j)
      (fun n => (hFnS n j W₁ hW₁b).sub (hFS j W₁ hW₁W)) (hFconv j W₁ hW₁m hW₁W)
  have hκsplit : a + κ / 2 + κ / 2 = a + κ := by ring
  -- the energy estimate for differences
  have hdiff : ∀ n m : ℕ,
      ∫ z in W', ∑ j : Fin 3, (spatialPartial (wn n) j z - spatialPartial (wn m) j z) ^ 2 ≤
        C₀ * ((∫ z in W₁, (wn n z - wn m z) ^ 2) +
          ∑ j : Fin 3, ∫ z in W₁, (Fn n j z - Fn m j z) ^ 2) := by
    intro n m
    have hD : ContDiff ℝ (⊤ : ℕ∞) (fun z => wn n z - wn m z) := (hwn n).sub (hwn m)
    have hFD : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun z => Fn n j z - Fn m j z) :=
      fun j => (hFn n j).sub (hFn m j)
    have heqD : ∀ z ∈ vec3Ball x₀ R₁ ×ˢ Ioo (a + κ / 2) b,
        timePartial (fun z : Vec3 × ℝ => wn n z - wn m z) z -
            ∑ j : Fin 3, spatialSecondPartial (fun z : Vec3 × ℝ => wn n z - wn m z) j j z =
          ∑ j : Fin 3, spatialPartial (fun z : Vec3 × ℝ => Fn n j z - Fn m j z) j z := by
      intro z hz
      rw [vorticity_timePartial_sub (hwn n) (hwn m) z]
      simp only [vorticity_spatialSecondPartial_sub (hwn n) (hwn m),
        vorticity_spatialPartial_sub (hFn n _) (hFn m _), Finset.sum_sub_distrib]
      have h1 := heqn n z hz
      have h2 := heqn m z hz
      linarith only [h1, h2]
    have hest := (hsmooth x₀ (a + κ / 2) b (fun z : Vec3 × ℝ => wn n z - wn m z)
      (fun j (z : Vec3 × ℝ) => Fn n j z - Fn m j z) (by linarith only [hab])
      (by linarith only [hba, hκ])
      hD hFD heqD).2
    rw [hκsplit] at hest
    have hint1 : IntegrableOn (fun z => (wn n z - wn m z) ^ 2) W₁ :=
      vorticity_integrableOn_of_continuous_bounded (hD.continuous.pow 2) hW₁b
    have hint2 : ∀ j, IntegrableOn (fun z => (Fn n j z - Fn m j z) ^ 2) W₁ := fun j =>
      vorticity_integrableOn_of_continuous_bounded ((hFD j).continuous.pow 2) hW₁b
    have hsplitR : ∫ z in W₁, ((wn n z - wn m z) ^ 2 +
        ∑ j : Fin 3, (Fn n j z - Fn m j z) ^ 2) =
        (∫ z in W₁, (wn n z - wn m z) ^ 2) +
          ∑ j : Fin 3, ∫ z in W₁, (Fn n j z - Fn m j z) ^ 2 := by
      rw [integral_add hint1 (integrable_finsetSum _ fun j _ => hint2 j),
        integral_finsetSum _ fun j _ => hint2 j]
    have hlhs : ∀ z, ∑ j : Fin 3, spatialPartial (fun z : Vec3 × ℝ => wn n z - wn m z) j z ^ 2 =
        ∑ j : Fin 3, (spatialPartial (wn n) j z - spatialPartial (wn m) j z) ^ 2 := by
      intro z
      exact Finset.sum_congr rfl fun j _ => by
        rw [vorticity_spatialPartial_sub (hwn n) (hwn m) j z]
    calc
      _ = ∫ z in W', ∑ j : Fin 3,
          spatialPartial (fun z : Vec3 × ℝ => wn n z - wn m z) j z ^ 2 :=
        integral_congr_ae (Eventually.of_forall fun z => (hlhs z).symm)
      _ ≤ _ := hest
      _ = _ := by rw [hsplitR]
  -- the right side of the difference estimate tends to zero
  have hrhs : Tendsto (fun p : ℕ × ℕ => C₀ * ((∫ z in W₁, (wn p.1 z - wn p.2 z) ^ 2) +
      ∑ j : Fin 3, ∫ z in W₁, (Fn p.1 j z - Fn p.2 j z) ^ 2)) atTop (𝓝 0) := by
    have hw2 : Tendsto (fun n => 2 * (∫ z in W₁, (wn n z - w z) ^ 2)) atTop (𝓝 0) := by
      simpa using hwsq.const_mul 2
    have hF2 : ∀ j : Fin 3, Tendsto (fun n => 2 * (∫ z in W₁, (Fn n j z - F j z) ^ 2))
        atTop (𝓝 0) := fun j => by simpa using (hFsq j).const_mul 2
    have hbound : Tendsto (fun p : ℕ × ℕ => C₀ * ((2 * (∫ z in W₁, (wn p.1 z - w z) ^ 2) +
        2 * (∫ z in W₁, (wn p.2 z - w z) ^ 2)) + ∑ j : Fin 3,
          (2 * (∫ z in W₁, (Fn p.1 j z - F j z) ^ 2) +
            2 * (∫ z in W₁, (Fn p.2 j z - F j z) ^ 2)))) atTop (𝓝 0) := by
      have h1 := vorticity_tendsto_prod_add hw2 hw2
      have h3 := tendsto_finsetSum (Finset.univ : Finset (Fin 3))
        fun j _ => vorticity_tendsto_prod_add (hF2 j) (hF2 j)
      simp only [Finset.sum_const_zero] at h3
      simpa using (h1.add h3).const_mul C₀
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
      (fun p => ?_) (fun p => ?_)
    · have h0 : 0 ≤ (∫ z in W₁, (wn p.1 z - wn p.2 z) ^ 2) +
          ∑ j : Fin 3, ∫ z in W₁, (Fn p.1 j z - Fn p.2 j z) ^ 2 :=
        add_nonneg (integral_nonneg fun z => sq_nonneg _)
          (Finset.sum_nonneg fun j _ => integral_nonneg fun z => sq_nonneg _)
      exact mul_nonneg hC₀ h0
    · apply mul_le_mul_of_nonneg_left _ hC₀
      apply add_le_add
      · exact vorticity_integral_sq_sub_le (hwnS p.1 W₁ hW₁b) (hwnS p.2 W₁ hW₁b)
          (hwS W₁ hW₁W)
      · exact Finset.sum_le_sum fun j _ => vorticity_integral_sq_sub_le
          (hFnS p.1 j W₁ hW₁b) (hFnS p.2 j W₁ hW₁b) (hFS j W₁ hW₁W)
  -- Cauchy property of each derivative and its limit
  have hcauchy : ∀ j : Fin 3, Tendsto (fun p : ℕ × ℕ =>
      eLpNorm ((fun z : Vec3 × ℝ => spatialPartial (wn p.1) j z) -
        (fun z : Vec3 × ℝ => spatialPartial (wn p.2) j z)) 2 (volume.restrict W'))
      atTop (𝓝 0) := by
    intro j
    have hsq : Tendsto (fun p : ℕ × ℕ => ∫ z in W', (spatialPartial (wn p.1) j z -
        spatialPartial (wn p.2) j z) ^ 2) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrhs
        (fun p => integral_nonneg fun z => sq_nonneg _) (fun p => ?_)
      refine le_trans ?_ (hdiff p.1 p.2)
      have hint : ∀ k : Fin 3, IntegrableOn (fun z => (spatialPartial (wn p.1) k z -
          spatialPartial (wn p.2) k z) ^ 2) W' := fun k =>
        vorticity_integrableOn_of_continuous_bounded
          (((CKN.spatialPartial_contDiff (hwn p.1) k).continuous.sub
            (CKN.spatialPartial_contDiff (hwn p.2) k).continuous).pow 2) hW'b
      apply integral_mono (hint j) (integrable_finsetSum _ fun k _ => hint k)
      intro z
      exact Finset.single_le_sum (f := fun k : Fin 3 => (spatialPartial (wn p.1) k z -
        spatialPartial (wn p.2) k z) ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    exact vorticity_tendsto_eLpNorm_of_integral_sq
      (fun p => (hdwnS p.1 j W' hW'b).sub (hdwnS p.2 j W' hW'b)) hsq
  have hlim : ∀ j : Fin 3, ∃ g : Vec3 × ℝ → ℝ, MemLp g 2 (volume.restrict W') ∧
      Tendsto (fun n => eLpNorm ((fun z : Vec3 × ℝ => spatialPartial (wn n) j z) - g) 2
        (volume.restrict W')) atTop (𝓝 0) := fun j =>
    vorticityL2_exists_limit (fun n => hdwnS n j W' hW'b) (hcauchy j)
  choose G hGmem hGlim using hlim
  refine ⟨G, hGmem, ?_, ?_⟩
  · intro j
    exact vorticity_weakPartial_of_tendsto hwn (fun n => hwnS n W' hW'b)
      (fun n => hdwnS n j W' hW'b) (hwS W' hW'W) (hGmem j) (hwconv W' hW'm hW'W) (hGlim j)
  · have hG2 : ∀ j, IntegrableOn (fun y => G j y ^ 2) W' := fun j =>
      (memLp_two_iff_integrable_sq (hGmem j).aestronglyMeasurable).1 (hGmem j)
    have hw2W : IntegrableOn (fun y => w y ^ 2) W :=
      (memLp_two_iff_integrable_sq hw.aestronglyMeasurable).1 hw
    have hF2W : ∀ j, IntegrableOn (fun y => F j y ^ 2) W := fun j =>
      (memLp_two_iff_integrable_sq (hF j).aestronglyMeasurable).1 (hF j)
    -- the estimate for each approximation
    have happrox : ∀ n, ∑ j : Fin 3, ∫ z in W', spatialPartial (wn n) j z ^ 2 ≤
        C₀ * ((∫ z in W₁, wn n z ^ 2) + ∑ j : Fin 3, ∫ z in W₁, Fn n j z ^ 2) := by
      intro n
      have hest := (hsmooth x₀ (a + κ / 2) b (wn n) (Fn n) (by linarith only [hab])
        (by linarith only [hba, hκ]) (hwn n) (hFn n) (heqn n)).2
      rw [hκsplit] at hest
      have hint : ∀ k : Fin 3, IntegrableOn (fun z => spatialPartial (wn n) k z ^ 2) W' :=
        fun k => vorticity_integrableOn_of_continuous_bounded
          ((CKN.spatialPartial_contDiff (hwn n) k).continuous.pow 2) hW'b
      have hint1 : IntegrableOn (fun z => wn n z ^ 2) W₁ :=
        vorticity_integrableOn_of_continuous_bounded ((hwn n).continuous.pow 2) hW₁b
      have hint2 : ∀ k : Fin 3, IntegrableOn (fun z => Fn n k z ^ 2) W₁ := fun k =>
        vorticity_integrableOn_of_continuous_bounded ((hFn n k).continuous.pow 2) hW₁b
      calc
        _ = ∫ z in W', ∑ j : Fin 3, spatialPartial (wn n) j z ^ 2 :=
          (integral_finsetSum _ fun k _ => hint k).symm
        _ ≤ _ := hest
        _ = _ := by
          rw [integral_add hint1 (integrable_finsetSum _ fun k _ => hint2 k),
            integral_finsetSum _ fun k _ => hint2 k]
    have hL : Tendsto (fun n => ∑ j : Fin 3, ∫ z in W', spatialPartial (wn n) j z ^ 2) atTop
        (𝓝 (∑ j : Fin 3, ∫ z in W', G j z ^ 2)) :=
      tendsto_finsetSum _ fun j _ =>
        vorticity_tendsto_integral_sq (fun n => hdwnS n j W' hW'b) (hGmem j) (hGlim j)
    have hR : Tendsto (fun n => C₀ * ((∫ z in W₁, wn n z ^ 2) +
        ∑ j : Fin 3, ∫ z in W₁, Fn n j z ^ 2)) atTop
        (𝓝 (C₀ * ((∫ z in W₁, w z ^ 2) + ∑ j : Fin 3, ∫ z in W₁, F j z ^ 2))) := by
      apply Tendsto.const_mul
      apply Tendsto.add
      · exact vorticity_tendsto_integral_sq (fun n => hwnS n W₁ hW₁b) (hwS W₁ hW₁W)
          (hwconv W₁ hW₁m hW₁W)
      · exact tendsto_finsetSum _ fun j _ => vorticity_tendsto_integral_sq
          (fun n => hFnS n j W₁ hW₁b) (hFS j W₁ hW₁W) (hFconv j W₁ hW₁m hW₁W)
    have hlimle := le_of_tendsto_of_tendsto' hL hR happrox
    have hmono : (∫ z in W₁, w z ^ 2) + ∑ j : Fin 3, ∫ z in W₁, F j z ^ 2 ≤
        ∫ y in W, (w y ^ 2 + ∑ j : Fin 3, F j y ^ 2) := by
      have hintW : IntegrableOn (fun y => w y ^ 2 + ∑ j : Fin 3, F j y ^ 2) W :=
        hw2W.add (integrable_finsetSum _ fun j _ => hF2W j)
      calc
        _ = ∫ y in W₁, (w y ^ 2 + ∑ j : Fin 3, F j y ^ 2) := by
          rw [integral_add (hw2W.mono_set hW₁W)
            (integrable_finsetSum _ fun j _ => (hF2W j).mono_set hW₁W),
            integral_finsetSum _ fun j _ => (hF2W j).mono_set hW₁W]
        _ ≤ _ := setIntegral_mono_set hintW
          (Eventually.of_forall fun y => add_nonneg (sq_nonneg _)
            (Finset.sum_nonneg fun j _ => sq_nonneg _))
          (Eventually.of_forall hW₁W)
    calc
      ∫ y in W', ∑ j : Fin 3, G j y ^ 2 = ∑ j : Fin 3, ∫ y in W', G j y ^ 2 :=
        integral_finsetSum _ fun j _ => hG2 j
      _ ≤ _ := hlimle
      _ ≤ _ := mul_le_mul_of_nonneg_left hmono hC₀

/-- The weak local heat gain: a square-integrable distributional solution of
`∂ₜ w - Δ w = div F` with square-integrable `F` on a box has a square-integrable weak spatial
gradient on every smaller box with the same top, bounded by the data
(`lem:localized-vorticity-energy`, `lem:local-heat-gain`). -/
theorem vorticityHeatEngine {r R κ : ℝ} (hr : 0 < r) (hrR : r < R) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Vec3) (a b : ℝ) (w : Vec3 × ℝ → ℝ)
      (F : Fin 3 → Vec3 × ℝ → ℝ), a + κ < b → b ≤ a + 1 →
      MemLp w 2 (volume.restrict (vec3Ball x₀ R ×ˢ Ioo a b)) →
      (∀ j, MemLp (F j) 2 (volume.restrict (vec3Ball x₀ R ×ˢ Ioo a b))) →
      (∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ vec3Ball x₀ R ×ˢ Ioo a b →
        ∫ y in vec3Ball x₀ R ×ˢ Ioo a b,
            w y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
          -∫ y in vec3Ball x₀ R ×ˢ Ioo a b, ∑ j : Fin 3, F j y * spatialPartial ψ j y) →
      ∃ G : Fin 3 → Vec3 × ℝ → ℝ,
        (∀ j, MemLp (G j) 2 (volume.restrict (vec3Ball x₀ r ×ˢ Ioo (a + κ) b))) ∧
        (∀ j, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ vec3Ball x₀ r ×ˢ Ioo (a + κ) b →
          ∫ y in vec3Ball x₀ r ×ˢ Ioo (a + κ) b, w y * spatialPartial ψ j y =
            -∫ y in vec3Ball x₀ r ×ˢ Ioo (a + κ) b, G j y * ψ y) ∧
        ∫ y in vec3Ball x₀ r ×ˢ Ioo (a + κ) b, ∑ j : Fin 3, G j y ^ 2 ≤
          C * ∫ y in vec3Ball x₀ R ×ˢ Ioo a b, (w y ^ 2 + ∑ j : Fin 3, F j y ^ 2) := by
  have hrR₁ : r < (r + R) / 2 := by linarith only [hrR]
  have hR₁R : (r + R) / 2 < R := by linarith only [hrR]
  obtain ⟨C₀, hC₀, hsmooth⟩ := vorticityHeatSmooth_localEnergy hr hrR₁ (half_pos hκ)
  exact ⟨C₀, hC₀, fun x₀ a b w F hab hba hw hF hweak =>
    vorticityHeatEngine_core hrR₁ hR₁R hκ hC₀ hsmooth x₀ a b w F hab hba hw hF hweak⟩

end ESS
