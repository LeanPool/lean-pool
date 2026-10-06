/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationCutoff
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateTestField
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateStrongFormAE

/-!
# Time-cutoff test fields and their `L²` time continuity

Multiplying a space-time test field by a smooth cutoff in time gives a test
field on a shorter slab; its time derivative splits by the product rule. A
compactly supported continuous field is continuous in time with values in `L²`
(`lem:lps-continuation`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A test field on `(a, c)` multiplied by a smooth time cutoff supported before
`β < b` is a test field on `(a, b)`. -/
theorem lps_cutoff_test_mem_right {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b c β : ℝ} {η : ℝ → ℝ} {φ : Vec3 × ℝ → V}
    (hφ : φ ∈ spaceTimeTestFunction (V := V) (Set.univ : Set Vec3) (Ioo a c))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : tsupport η ⊆ Iic β) (hβ : β < b) :
    (fun z : Vec3 × ℝ => η z.2 • φ z) ∈
      spaceTimeTestFunction (V := V) (Set.univ : Set Vec3) (Ioo a b) := by
  obtain ⟨hφs, hφc, hφt⟩ := hφ
  have hsub : tsupport (fun z : Vec3 × ℝ => η z.2 • φ z) ⊆ tsupport φ ∩ {z | z.2 ∈ tsupport η} := by
    refine closure_minimal ?_ ((isClosed_tsupport φ).inter
      ((isClosed_tsupport η).preimage continuous_snd))
    intro z hz
    have hz' : η z.2 • φ z ≠ 0 := hz
    exact ⟨subset_tsupport _ (right_ne_zero_of_smul hz'),
      subset_tsupport _ (left_ne_zero_of_smul hz')⟩
  refine ⟨(hη.comp contDiff_snd).smul hφs, ?_, ?_⟩
  · exact IsCompact.of_isClosed_subset hφc (isClosed_tsupport _) (hsub.trans inter_subset_left)
  · intro z hz
    have h1 := hsub hz
    have h2 := hφt h1.1
    exact ⟨mem_univ _, h2.2.1, lt_of_le_of_lt (hηs h1.2) hβ⟩

/-- A test field on `(a, c)` multiplied by a smooth time cutoff supported after
`α > b` is a test field on `(b, c)`. -/
theorem lps_cutoff_test_mem_left {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b c α : ℝ} {η : ℝ → ℝ} {φ : Vec3 × ℝ → V}
    (hφ : φ ∈ spaceTimeTestFunction (V := V) (Set.univ : Set Vec3) (Ioo a c))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : tsupport η ⊆ Ici α) (hα : b < α) :
    (fun z : Vec3 × ℝ => η z.2 • φ z) ∈
      spaceTimeTestFunction (V := V) (Set.univ : Set Vec3) (Ioo b c) := by
  obtain ⟨hφs, hφc, hφt⟩ := hφ
  have hsub : tsupport (fun z : Vec3 × ℝ => η z.2 • φ z) ⊆ tsupport φ ∩ {z | z.2 ∈ tsupport η} := by
    refine closure_minimal ?_ ((isClosed_tsupport φ).inter
      ((isClosed_tsupport η).preimage continuous_snd))
    intro z hz
    have hz' : η z.2 • φ z ≠ 0 := hz
    exact ⟨subset_tsupport _ (right_ne_zero_of_smul hz'),
      subset_tsupport _ (left_ne_zero_of_smul hz')⟩
  refine ⟨(hη.comp contDiff_snd).smul hφs, ?_, ?_⟩
  · exact IsCompact.of_isClosed_subset hφc (isClosed_tsupport _) (hsub.trans inter_subset_left)
  · intro z hz
    have h1 := hsub hz
    have h2 := hφt h1.1
    exact ⟨mem_univ _, lt_of_lt_of_le hα (hηs h1.2), h2.2.2⟩

/-- Product rule for the time derivative of a cutoff test field. -/
theorem lps_cutoff_timePartial {η : ℝ → ℝ} {φ : Vec3 × ℝ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (z : ParabolicPoint) :
    timePartial (fun y : ParabolicPoint => η y.2 * φ y) z =
      deriv η z.2 * φ z + η z.2 * timePartial φ z := by
  unfold timePartial
  have hd1 : DifferentiableAt ℝ η z.2 := hη.differentiable (by simp) z.2
  have hd2 : DifferentiableAt ℝ (fun s : ℝ => φ (z.1, s)) z.2 :=
    DifferentiableAt.comp z.2 (hφ.differentiable (by simp) (z.1, z.2))
      ((differentiableAt_const z.1).prodMk differentiableAt_id)
  change (fderiv ℝ (fun s : ℝ => η s * φ (z.1, s)) z.2) 1 = _
  rw [fderiv_fun_mul hd1 hd2]
  have hz : φ (z.1, z.2) = φ z := rfl
  simp [mul_comm, hz]
  ring

/-- Spatial derivatives commute with the time cutoff. -/
theorem lps_cutoff_spatialPartial {η : ℝ → ℝ} {φ : Vec3 × ℝ → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (j : Fin 3) (z : ParabolicPoint) :
    spatialPartial (fun y : ParabolicPoint => η y.2 * φ y) j z =
      η z.2 * spatialPartial φ j z := by
  unfold spatialPartial
  have hd : DifferentiableAt ℝ (fun x : Vec3 => φ (x, z.2)) z.1 :=
    DifferentiableAt.comp z.1 (hφ.differentiable (by simp) (z.1, z.2))
      (differentiableAt_id.prodMk (differentiableAt_const z.2))
  change (fderiv ℝ (fun x : Vec3 => η z.2 * φ (x, z.2)) z.1) (basisVec j) = _
  rw [fderiv_const_mul hd]
  simp

/-- A continuous compactly supported field is continuous in time with values
in `L²`. -/
theorem lps_test_slice_l2_tendsto {φ : Vec3 × ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (b : ℝ) :
    Tendsto (fun t : ℝ => eLpNorm (fun x : Vec3 => φ (x, t) - φ (x, b)) 2 volume)
      (𝓝 b) (𝓝 0) := by
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
  have hK : IsCompact (Prod.fst '' tsupport φ) := hφc.image continuous_fst
  have hKmeas : MeasurableSet (Prod.fst '' tsupport φ) := hK.isClosed.measurableSet
  have hvol : volume (Prod.fst '' tsupport φ) < ⊤ := hK.measure_lt_top
  let bound : Vec3 → ℝ≥0∞ := fun x =>
    (Prod.fst '' tsupport φ).indicator (fun _ => ENNReal.ofReal (2 * C) ^ (2 : ℝ)) x
  have hcont : ∀ t : ℝ, Continuous fun x : Vec3 => φ (x, t) := fun t =>
    hφ.comp (continuous_id.prodMk continuous_const)
  have hlim : Tendsto (fun t : ℝ => ∫⁻ x : Vec3, ‖φ (x, t) - φ (x, b)‖ₑ ^ (2 : ℝ)) (𝓝 b)
      (𝓝 (∫⁻ x : Vec3, (0 : ℝ≥0∞))) := by
    refine tendsto_lintegral_filter_of_dominated_convergence bound ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun t =>
        (((hcont t).sub (hcont b)).measurable.enorm.pow_const _)
    · refine Eventually.of_forall fun t => Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ Prod.fst '' tsupport φ
      · simp only [bound, indicator_of_mem hx]
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        rw [Real.enorm_eq_ofReal_abs]
        refine ENNReal.ofReal_le_ofReal ?_
        calc |φ (x, t) - φ (x, b)| ≤ |φ (x, t)| + |φ (x, b)| := abs_sub _ _
          _ ≤ C + C := add_le_add (by simpa using hC (x, t)) (by simpa using hC (x, b))
          _ = 2 * C := by ring
      · have h1 : φ (x, t) = 0 := by
          by_contra h
          exact hx ⟨(x, t), subset_tsupport _ h, rfl⟩
        have h2 : φ (x, b) = 0 := by
          by_contra h
          exact hx ⟨(x, b), subset_tsupport _ h, rfl⟩
        simp [h1, h2, bound, indicator_of_notMem hx]
    · simp only [bound]
      rw [lintegral_indicator hKmeas, setLIntegral_const]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
        hvol.ne
    · refine Eventually.of_forall fun x => ?_
      have hx : Tendsto (fun t : ℝ => φ (x, t) - φ (x, b)) (𝓝 b) (𝓝 0) := by
        have hc : Continuous fun t : ℝ => φ (x, t) := hφ.comp (continuous_const.prodMk continuous_id)
        have := (hc.tendsto b).sub_const (φ (x, b))
        simpa using this
      have hx' : Tendsto (fun t : ℝ => ‖φ (x, t) - φ (x, b)‖ₑ) (𝓝 b) (𝓝 0) := by
        simpa using hx.enorm
      have := (ENNReal.continuous_rpow_const (y := (2 : ℝ)) |>.tendsto 0).comp hx'
      simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] using this
  simp only [lintegral_zero] at hlim
  have hform (t : ℝ) : eLpNorm (fun x : Vec3 => φ (x, t) - φ (x, b)) 2 volume =
      (∫⁻ x : Vec3, ‖φ (x, t) - φ (x, b)‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    have hm : AEStronglyMeasurable (fun x : Vec3 => φ (x, t) - φ (x, b)) volume :=
      ((hcont t).sub (hcont b)).aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hm]
    norm_num
  simp_rw [hform]
  have := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0 |>.comp hlim
  simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using this

/-- Cauchy–Schwarz for scalar `L²` functions. -/
theorem lps_abs_integral_mul_le {f g : Vec3 → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    |∫ x : Vec3, f x * g x| ≤
      (eLpNorm f 2 volume).toReal * (eLpNorm g 2 volume).toReal := by
  have hint : Integrable (fun x => f x * g x) volume := hf.integrable_mul hg
  have h3 : (∫⁻ x : Vec3, ‖f x‖ₑ * ‖g x‖ₑ) ≤ eLpNorm f 2 volume * eLpNorm g 2 volume :=
    lps_lintegral_mul_le_two hf.aestronglyMeasurable hg.aestronglyMeasurable
  have hfin : eLpNorm f 2 volume * eLpNorm g 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top
  have h4 : (∫⁻ x : Vec3, ‖f x * g x‖ₑ) ≤ eLpNorm f 2 volume * eLpNorm g 2 volume := by
    refine le_trans (le_of_eq ?_) h3
    refine lintegral_congr fun x => ?_
    rw [enorm_mul]
  have h5 := ENNReal.toReal_mono hfin h4
  rw [ENNReal.toReal_mul] at h5
  have hI : ∫ x : Vec3, ‖f x * g x‖ = (∫⁻ x : Vec3, ‖f x * g x‖ₑ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => norm_nonneg _)
      hint.aestronglyMeasurable.norm]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [Real.enorm_eq_ofReal_abs]
    simp
  calc |∫ x : Vec3, f x * g x| = ‖∫ x : Vec3, f x * g x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x : Vec3, ‖f x * g x‖ := norm_integral_le_integral_norm _
    _ = (∫⁻ x : Vec3, ‖f x * g x‖ₑ).toReal := hI
    _ ≤ _ := h5

/-- The `L²` pairing is continuous along families that converge in `L²`. -/
theorem lps_pairing_tendsto {ι : Type} {l : Filter ι} {f g : ι → Vec3 → ℝ} {f₀ g₀ : Vec3 → ℝ}
    (hf₀ : MemLp f₀ 2 volume) (hg₀ : MemLp g₀ 2 volume)
    (hf : ∀ᶠ i in l, MemLp (f i) 2 volume) (hg : ∀ᶠ i in l, MemLp (g i) 2 volume)
    (hfl : Tendsto (fun i => eLpNorm (fun x => f i x - f₀ x) 2 volume) l (𝓝 0))
    (hgl : Tendsto (fun i => eLpNorm (fun x => g i x - g₀ x) 2 volume) l (𝓝 0)) :
    Tendsto (fun i => ∫ x : Vec3, f i x * g i x) l (𝓝 (∫ x : Vec3, f₀ x * g₀ x)) := by
  set a : ι → ℝ := fun i => (eLpNorm (fun x => f i x - f₀ x) 2 volume).toReal with ha
  set c : ι → ℝ := fun i => (eLpNorm (fun x => g i x - g₀ x) 2 volume).toReal with hc
  have ha0 : Tendsto a l (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hfl
    simpa [ha, Function.comp_def] using this
  have hc0 : Tendsto c l (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hgl
    simpa [hc, Function.comp_def] using this
  set A : ℝ := (eLpNorm f₀ 2 volume).toReal
  set B : ℝ := (eLpNorm g₀ 2 volume).toReal
  have hbound : ∀ᶠ i in l, |(∫ x : Vec3, f i x * g i x) - ∫ x : Vec3, f₀ x * g₀ x| ≤
      a i * (c i + B) + A * c i := by
    filter_upwards [hf, hg] with i hfi hgi
    have hI1 : Integrable (fun x => (f i x - f₀ x) * g i x) volume :=
      (hfi.sub hf₀).integrable_mul hgi
    have hI2 : Integrable (fun x => f₀ x * (g i x - g₀ x)) volume :=
      hf₀.integrable_mul (hgi.sub hg₀)
    have hI3 : Integrable (fun x => f i x * g i x) volume := hfi.integrable_mul hgi
    have hI4 : Integrable (fun x => f₀ x * g₀ x) volume := hf₀.integrable_mul hg₀
    have hsplit : (∫ x : Vec3, f i x * g i x) - ∫ x : Vec3, f₀ x * g₀ x =
        (∫ x : Vec3, (f i x - f₀ x) * g i x) + ∫ x : Vec3, f₀ x * (g i x - g₀ x) := by
      rw [← integral_add hI1 hI2, ← integral_sub hI3 hI4]
      congr 1
      funext x
      ring
    rw [hsplit]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (lps_abs_integral_mul_le (hfi.sub hf₀) hgi).trans ?_
      have hgn : (eLpNorm (g i) 2 volume).toReal ≤ c i + B := by
        have h1 : eLpNorm (g i) 2 volume ≤ eLpNorm (fun x => g i x - g₀ x) 2 volume +
            eLpNorm g₀ 2 volume := by
          have := eLpNorm_add_le (f := fun x => g i x - g₀ x) (g := g₀) (μ := volume) (p := 2)
            (by norm_num)
          have heq : eLpNorm (g i) 2 volume =
              eLpNorm ((fun x => g i x - g₀ x) + g₀) 2 volume := by
            congr 1
            funext x
            simp
          rw [heq]
          exact this
        have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
          ⟨(hgi.sub hg₀).eLpNorm_ne_top, hg₀.eLpNorm_ne_top⟩) h1
        rwa [ENNReal.toReal_add (hgi.sub hg₀).eLpNorm_ne_top hg₀.eLpNorm_ne_top] at h2
      exact mul_le_mul_of_nonneg_left hgn ENNReal.toReal_nonneg
    · refine (lps_abs_integral_mul_le hf₀ (hgi.sub hg₀)).trans ?_
      exact le_of_eq rfl
  have hlim : Tendsto (fun i => a i * (c i + B) + A * c i) l (𝓝 0) := by
    have h1 : Tendsto (fun i => a i * (c i + B)) l (𝓝 (0 * (0 + B))) :=
      ha0.mul (hc0.add_const B)
    have h2 : Tendsto (fun i => A * c i) l (𝓝 (A * 0)) := hc0.const_mul A
    simpa using h1.add h2
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) ?_ hlim
  filter_upwards [hbound] with i hi
  simpa [Real.norm_eq_abs] using hi

end ESS

end
