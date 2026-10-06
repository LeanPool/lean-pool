/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.HeatCriticalSpaceTime
public import LeanPool.EscauriazaSereginSverak.PartV.HeatCriticalTenThirds

/-!
# The critical `L⁵` bound for smooth heat data

For smooth compactly supported data the regularized profile
`g_η = (|h|² + η²)^{3/4} - η^{3/2}` satisfies, by the entropy identity,
`sup_t ‖g_η(t)‖₂² + ∫∫ |∇g_η|² ≤ C ∫ E_η(b)`.  The Gagliardo–Nirenberg
inequality `eq:gn-ten-thirds` of the CKN manuscript at each time then bounds `∫∫ g_η^{10/3}`, and
Fatou's lemma as `η → 0` gives the estimate `eq:pv-heat-l5` of
`lem:pv-heat-critical` for smooth compact data.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat


noncomputable section

namespace ESS

/-- The Gagliardo–Nirenberg inequality `eq:gn-ten-thirds` of the CKN manuscript in power form for a
whole-space `H¹` function. -/
theorem h1_tenThirds_lintegral_le (H : CKN.H1Function (Set.univ : Set Vec3)) :
    ∫⁻ x : Vec3, ‖H.toFun x‖ₑ ^ (10 / 3 : ℝ) ≤
      gagliardoNirenbergSobolevConstant ^ (2 : ℝ) *
        (eLpNorm H.toFun 2 volume ^ (2 : ℝ)) ^ (2 / 3 : ℝ) *
        eLpNorm (fun x => vec3EuclideanNorm (H.grad x)) 2 volume ^ (2 : ℝ) := by
  have hGN := h1_gagliardoNirenberg_tenThirds H
  have hmem : MemLp H.toFun 2 volume := by
    simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using H.memL2
  rw [lintegral_enorm_rpow_eq_eLpNorm_rpow (by norm_num) hmem.aestronglyMeasurable]
  set S := gagliardoNirenbergSobolevConstant
  set A := eLpNorm H.toFun 2 volume
  set B := eLpNorm (fun x => vec3EuclideanNorm (H.grad x)) 2 volume
  calc
    eLpNorm H.toFun (ENNReal.ofReal (10 / 3 : ℝ)) volume ^ (10 / 3 : ℝ) ≤
        (S ^ (3 / 5 : ℝ) * A ^ (2 / 5 : ℝ) * B ^ (3 / 5 : ℝ)) ^ (10 / 3 : ℝ) :=
      ENNReal.rpow_le_rpow hGN (by norm_num)
    _ = S ^ (2 : ℝ) * (A ^ (2 : ℝ)) ^ (2 / 3 : ℝ) * B ^ (2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
        ← ENNReal.rpow_mul]
      norm_num

/-- The regularized critical profile is nonnegative. -/
theorem heatRegG_nonneg {η : ℝ} (hη : 0 < η) (v : Vec3) : 0 ≤ heatRegG η v := by
  unfold heatRegG
  have hle : η ^ 2 ≤ heatRegSq η v := by
    unfold heatRegSq
    have hsum : 0 ≤ ∑ i : Fin 3, v i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith only [hsum]
  have hmono := Real.rpow_le_rpow (by positivity) hle (by norm_num : (0 : ℝ) ≤ 3 / 4)
  have heq : (η ^ 2) ^ (3 / 4 : ℝ) = η ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hη.le]
    norm_num
  rw [heq] at hmono
  linarith only [hmono]

/-- One time slice of the regularized profile: the Gagliardo–Nirenberg
inequality combined with the entropy bound and the pointwise gradient bound. -/
theorem heatRegG_tenThirds_slice {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    ∫⁻ x : Vec3, ‖heatRegG η (heatConvVec3 t b x)‖ₑ ^ (10 / 3 : ℝ) ≤
      gagliardoNirenbergSobolevConstant ^ (2 : ℝ) *
        ENNReal.ofReal (27 * ∫ x : Vec3, heatRegEnergy η (b x)) ^ (2 / 3 : ℝ) *
        ENNReal.ofReal ((9 / 2 : ℝ) * ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3,
          CKN.spatialDeriv
            (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
          CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x) := by
  let H := heatRegG_heatConv_h1 hb hbc ht hη
  have hmain := h1_tenThirds_lintegral_le H
  have hmem : MemLp H.toFun 2 volume := by
    simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using H.memL2
  have hprofile : ContDiff ℝ (⊤ : ℕ∞) (heatConvVec3 t b) := by
    rw [contDiff_pi]
    intro i
    simpa [heatConvVec3] using heatConv_smooth_input (hb i) (hbc i) ht
  have hGsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => heatRegG η (heatConvVec3 t b x)) :=
    (heatRegG_contDiff hη).comp hprofile
  have hgradCont (j : Fin 3) : Continuous (fun x => H.grad x j) :=
    (CKN.contDiff_spatialDeriv_smooth hGsmooth j).continuous
  have hgradInt := heatRegG_heatConv_spatial_grad_sq_integrable hb hbc ht hη
  have heuclMem : MemLp (fun x => vec3EuclideanNorm (H.grad x)) 2 volume := by
    have hcont : Continuous (fun x => vec3EuclideanNorm (H.grad x)) :=
      continuous_vec3EuclideanNorm.comp (continuous_pi hgradCont)
    refine (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 ?_
    refine hgradInt.congr (Filter.Eventually.of_forall fun x => ?_)
    change ∑ j : Fin 3, (H.grad x j) ^ 2 = vec3EuclideanNorm (H.grad x) ^ 2
    rw [vec3EuclideanNorm_sq]
  have hGsq : eLpNorm H.toFun 2 volume ^ (2 : ℝ) ≤
      ENNReal.ofReal (27 * ∫ x : Vec3, heatRegEnergy η (b x)) := by
    rw [eLpNorm_two_rpow_two_eq_ofReal_integral hmem]
    apply ENNReal.ofReal_le_ofReal
    have hEint := heatRegEnergy_heatConv_integrable hb hbc ht hη
    have hGint : Integrable (fun x => (H.toFun x) ^ 2) volume :=
      (memLp_two_iff_integrable_sq hmem.aestronglyMeasurable).1 hmem
    calc
      (∫ x : Vec3, (H.toFun x) ^ 2) ≤
          ∫ x : Vec3, 27 * heatRegEnergy η (heatConvVec3 t b x) :=
        integral_mono hGint (hEint.const_mul 27) fun x =>
          heatRegG_sq_le_energy hη (heatConvVec3 t b x)
      _ = 27 * ∫ x : Vec3, heatRegEnergy η (heatConvVec3 t b x) :=
        integral_const_mul _ _
      _ ≤ 27 * ∫ x : Vec3, heatRegEnergy η (b x) :=
        mul_le_mul_of_nonneg_left (heatRegEnergy_integral_le_initial hb hbc ht hη)
          (by norm_num)
  have hgradSq : eLpNorm (fun x => vec3EuclideanNorm (H.grad x)) 2 volume ^ (2 : ℝ) ≤
      ENNReal.ofReal ((9 / 2 : ℝ) * ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3,
          CKN.spatialDeriv
            (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
          CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x) := by
    rw [eLpNorm_two_rpow_two_eq_ofReal_integral heuclMem]
    apply ENNReal.ofReal_le_ofReal
    refine le_trans (le_of_eq ?_)
      (heatRegG_heatConv_spatial_grad_sq_integral_le_dissipation hb hbc ht hη)
    apply integral_congr_ae
    filter_upwards [] with x
    rw [vec3EuclideanNorm_sq]
    rfl
  refine hmain.trans ?_
  gcongr

/-- The space-time `L^{10/3}` integral of the regularized profile over
`ℝ³ × (0, τ)` is bounded by its initial entropy, uniformly in `τ`. -/
theorem heatRegG_tenThirds_lintegral_le {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η) :
    ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
        ‖heatRegG η (heatOrbit b z)‖ₑ ^ (10 / 3 : ℝ) ≤
      gagliardoNirenbergSobolevConstant ^ (2 : ℝ) *
        ENNReal.ofReal (27 * ∫ x : Vec3, heatRegEnergy η (b x)) ^ (2 / 3 : ℝ) *
        ENNReal.ofReal ((9 / 2 : ℝ) * ∫ x : Vec3, heatRegEnergy η (b x)) := by
  set S := gagliardoNirenbergSobolevConstant
  set E₀ := ∫ x : Vec3, heatRegEnergy η (b x)
  let D : ℝ → ℝ := fun t => ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3,
    CKN.spatialDeriv (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
    CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x
  have hS : S ≠ ∞ := (Classical.choose_spec CKN.sobolev_L6_global).1
  have hm := heatOrbit_aestronglyMeasurable_smooth hb hbc τ
  have hmeas : AEMeasurable (fun z => ‖heatRegG η (heatOrbit b z)‖ₑ ^ (10 / 3 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) :=
    ((heatRegG_contDiff hη).continuous.comp_aestronglyMeasurable hm).aemeasurable.enorm.pow_const _
  have hDnonneg {t : ℝ} (ht : 0 < t) : 0 ≤ D t := by
    have h := heatRegG_heatConv_spatial_grad_sq_integral_le_dissipation hb hbc ht hη
    have hnn : 0 ≤ ∫ x : Vec3, ∑ j : Fin 3,
        (CKN.spatialDeriv (fun y => heatRegG η (heatConvVec3 t b y)) j x) ^ 2 :=
      integral_nonneg fun x => Finset.sum_nonneg fun j _ => sq_nonneg _
    have h' : 0 ≤ (9 / 2 : ℝ) * D t := hnn.trans h
    linarith only [h']
  obtain ⟨hDint, hDle⟩ := heatRegEnergy_time_dissipation_le_initial hb hbc hτ hη
  have hDintOn : IntegrableOn D (Ioo 0 τ) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.le).1 hDint).mono_set
      Ioo_subset_Ioc_self
  rw [lintegral_spaceTimeSet_univ_eq hmeas]
  calc
    (∫⁻ t in Ioo 0 τ, ∫⁻ x : Vec3, ‖heatRegG η (heatOrbit b (x, t))‖ₑ ^ (10 / 3 : ℝ)) ≤
        ∫⁻ t in Ioo 0 τ, S ^ (2 : ℝ) * ENNReal.ofReal (27 * E₀) ^ (2 / 3 : ℝ) *
          ENNReal.ofReal ((9 / 2 : ℝ) * D t) := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro t ht
      exact heatRegG_tenThirds_slice hb hbc ht.1 hη
    _ = S ^ (2 : ℝ) * ENNReal.ofReal (27 * E₀) ^ (2 / 3 : ℝ) *
          ∫⁻ t in Ioo 0 τ, ENNReal.ofReal ((9 / 2 : ℝ) * D t) :=
      lintegral_const_mul' _ _ (by
        apply ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hS)
        exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
    _ ≤ S ^ (2 : ℝ) * ENNReal.ofReal (27 * E₀) ^ (2 / 3 : ℝ) *
          ENNReal.ofReal ((9 / 2 : ℝ) * E₀) := by
      gcongr
      rw [← ofReal_integral_eq_lintegral_ofReal (hDintOn.const_mul (9 / 2 : ℝ))
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
          exact mul_nonneg (by norm_num) (hDnonneg ht.1))]
      apply ENNReal.ofReal_le_ofReal
      rw [integral_const_mul]
      have hsame : (∫ t in Ioo 0 τ, D t) = ∫ t in (0 : ℝ)..τ, D t := by
        rw [intervalIntegral.integral_of_le hτ.le, integral_Ioc_eq_integral_Ioo]
      rw [hsame]
      gcongr

private theorem heatRegG_tendsto_zero (v : Vec3) :
    Tendsto (fun η : ℝ => heatRegG η v) (nhds 0)
      (nhds (vec3EuclideanNorm v ^ (3 / 2 : ℝ))) := by
  have hq : ContinuousAt (fun η : ℝ => heatRegSq η v) 0 := by
    unfold heatRegSq
    fun_prop
  have hpow : ContinuousAt (fun η : ℝ => heatRegSq η v ^ (3 / 4 : ℝ)) 0 :=
    (Real.continuous_rpow_const (by norm_num)).continuousAt.comp hq
  have hη : ContinuousAt (fun η : ℝ => η ^ (3 / 2 : ℝ)) 0 :=
    (Real.continuous_rpow_const (by norm_num)).continuousAt
  have h : Tendsto (fun η : ℝ => heatRegSq η v ^ (3 / 4 : ℝ) - η ^ (3 / 2 : ℝ))
      (nhds 0) (nhds (heatRegSq 0 v ^ (3 / 4 : ℝ) - (0 : ℝ) ^ (3 / 2 : ℝ))) :=
    (hpow.sub hη).tendsto
  have hval : heatRegSq 0 v ^ (3 / 4 : ℝ) - (0 : ℝ) ^ (3 / 2 : ℝ) =
      vec3EuclideanNorm v ^ (3 / 2 : ℝ) := by
    have hsq : heatRegSq 0 v = vec3EuclideanNorm v ^ 2 := by
      simp [heatRegSq, vec3EuclideanNorm_sq]
    rw [hsq, Real.zero_rpow (by norm_num), sub_zero, ← Real.rpow_natCast,
      ← Real.rpow_mul (vec3EuclideanNorm_nonneg v)]
    norm_num
  rw [hval] at h
  exact h

private theorem smooth_compact_euclidean_cube_integrable {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i)) :
    Integrable (fun x => vec3EuclideanNorm (b x) ^ 3) volume := by
  have hcont : Continuous (fun x => vec3EuclideanNorm (b x) ^ 3) :=
    (continuous_vec3EuclideanNorm.comp (continuous_pi fun i => (hb i).continuous)).pow 3
  apply hcont.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (isCompact_iUnion fun i => hbc i)
  intro x hx
  have hzero : b x = 0 := by
    funext i
    exact image_eq_zero_of_notMem_tsupport (f := fun y => b y i) (x := x)
      fun h => hx (mem_iUnion.2 ⟨i, h⟩)
  simp [hzero, vec3EuclideanNorm_zero]

/-- The cubic Euclidean integral of smooth compact data is bounded by the cube
of its `L³` norm, up to the norm-comparison constant. -/
theorem ofReal_integral_euclidean_cube_le {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i)) :
    ENNReal.ofReal (∫ x : Vec3, vec3EuclideanNorm (b x) ^ 3) ≤
      ENNReal.ofReal (Real.sqrt 3 ^ 3) * eLpNorm b 3 volume ^ (3 : ℝ) := by
  have hcont : Continuous b := continuous_pi fun i => (hb i).continuous
  rw [ofReal_integral_eq_lintegral_ofReal (smooth_compact_euclidean_cube_integrable hb hbc)
      (Filter.Eventually.of_forall fun x => pow_nonneg (vec3EuclideanNorm_nonneg _) 3),
    show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num,
    ← lintegral_enorm_rpow_eq_eLpNorm_rpow (by norm_num) hcont.aestronglyMeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro x
  have hle := vec3EuclideanNorm_le_sqrt_three_mul_norm (b x)
  calc
    ENNReal.ofReal (vec3EuclideanNorm (b x) ^ 3) ≤
        ENNReal.ofReal ((Real.sqrt 3 * ‖b x‖) ^ 3) :=
      ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (vec3EuclideanNorm_nonneg _) hle 3)
    _ = ENNReal.ofReal (Real.sqrt 3 ^ 3) * ‖b x‖ₑ ^ (3 : ℝ) := by
      rw [mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
        ofReal_norm, ← ENNReal.rpow_natCast]
      norm_num

/-- Fatou's lemma as the regularization vanishes: the space-time quintic
integral of a smooth compact heat orbit is bounded by the limit of the
regularized bounds. -/
theorem heatOrbit_five_lintegral_smooth {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {τ : ℝ} (hτ : 0 < τ) :
    ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
        ENNReal.ofReal (vec3EuclideanNorm (heatOrbit b z)) ^ (5 : ℝ) ≤
      gagliardoNirenbergSobolevConstant ^ (2 : ℝ) *
        ENNReal.ofReal (27 * ((1 / 3 : ℝ) *
          ∫ x : Vec3, vec3EuclideanNorm (b x) ^ 3)) ^ (2 / 3 : ℝ) *
        ENNReal.ofReal ((9 / 2 : ℝ) * ((1 / 3 : ℝ) *
          ∫ x : Vec3, vec3EuclideanNorm (b x) ^ 3)) := by
  set Q := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)
  set S := gagliardoNirenbergSobolevConstant
  set L := (1 / 3 : ℝ) * ∫ x : Vec3, vec3EuclideanNorm (b x) ^ 3
  have hS : S ≠ ∞ := (Classical.choose_spec CKN.sobolev_L6_global).1
  let η : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hηpos (n : ℕ) : 0 < η n := by dsimp [η]; positivity
  have hη0 : Tendsto η atTop (nhds 0) := by
    simpa only [η] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let f : ℕ → ParabolicPoint → ℝ≥0∞ := fun n z =>
    ‖heatRegG (η n) (heatOrbit b z)‖ₑ ^ (10 / 3 : ℝ)
  have hlim (z : ParabolicPoint) : Tendsto (fun n => f n z) atTop
      (nhds (ENNReal.ofReal (vec3EuclideanNorm (heatOrbit b z)) ^ (5 : ℝ))) := by
    have h1 := (heatRegG_tendsto_zero (heatOrbit b z)).comp hη0
    have h2 := (ENNReal.continuous_rpow_const (y := (10 / 3 : ℝ))).tendsto _ |>.comp
      ((continuous_enorm.tendsto _).comp h1)
    have hval : ‖vec3EuclideanNorm (heatOrbit b z) ^ (3 / 2 : ℝ)‖ₑ ^ (10 / 3 : ℝ) =
        ENNReal.ofReal (vec3EuclideanNorm (heatOrbit b z)) ^ (5 : ℝ) := by
      have hn := vec3EuclideanNorm_nonneg (heatOrbit b z)
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.rpow_nonneg hn _),
        ← ENNReal.ofReal_rpow_of_nonneg hn (by norm_num), ← ENNReal.rpow_mul]
      norm_num
    rw [← hval]
    exact h2
  have hm := heatOrbit_aestronglyMeasurable_smooth hb hbc τ
  have hmeas (n : ℕ) : AEMeasurable (f n) (volume.restrict Q) :=
    ((heatRegG_contDiff (hηpos n)).continuous.comp_aestronglyMeasurable
      hm).aemeasurable.enorm.pow_const _
  let E : ℕ → ℝ := fun n => ∫ x : Vec3, heatRegEnergy (η n) (b x)
  have hE : Tendsto E atTop (nhds L) := heatRegEnergy_initial_tendsto_l3 hb hbc
  let R : ℕ → ℝ≥0∞ := fun n => S ^ (2 : ℝ) * ENNReal.ofReal (27 * E n) ^ (2 / 3 : ℝ) *
    ENNReal.ofReal ((9 / 2 : ℝ) * E n)
  have hR : Tendsto R atTop (nhds (S ^ (2 : ℝ) * ENNReal.ofReal (27 * L) ^ (2 / 3 : ℝ) *
      ENNReal.ofReal ((9 / 2 : ℝ) * L))) := by
    have h27 : Tendsto (fun n => ENNReal.ofReal (27 * E n) ^ (2 / 3 : ℝ)) atTop
        (nhds (ENNReal.ofReal (27 * L) ^ (2 / 3 : ℝ))) :=
      (ENNReal.continuous_rpow_const.tendsto _).comp
        (ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := (27 : ℝ))).mul hE))
    have h92 : Tendsto (fun n => ENNReal.ofReal ((9 / 2 : ℝ) * E n)) atTop
        (nhds (ENNReal.ofReal ((9 / 2 : ℝ) * L))) :=
      ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := (9 / 2 : ℝ))).mul hE)
    have hS2 : S ^ (2 : ℝ) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hS
    have hL27 : ENNReal.ofReal (27 * L) ^ (2 / 3 : ℝ) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    have hprod := ENNReal.Tendsto.mul (ENNReal.Tendsto.const_mul h27 (Or.inr hS2))
      (Or.inr ENNReal.ofReal_ne_top) h92 (Or.inr (ENNReal.mul_ne_top hS2 hL27))
    exact hprod
  calc
    ∫⁻ z in Q, ENNReal.ofReal (vec3EuclideanNorm (heatOrbit b z)) ^ (5 : ℝ) =
        ∫⁻ z in Q, Filter.liminf (fun n => f n z) atTop :=
      lintegral_congr fun z => ((hlim z).liminf_eq).symm
    _ ≤ Filter.liminf (fun n => ∫⁻ z in Q, f n z) atTop := lintegral_liminf_le' hmeas
    _ ≤ Filter.liminf R atTop :=
      Filter.liminf_le_liminf (Filter.Eventually.of_forall fun n =>
        heatRegG_tenThirds_lintegral_le hb hbc hτ (hηpos n))
    _ = _ := hR.liminf_eq

/-- The critical estimate `eq:pv-heat-l5` for smooth compact data:
`‖S(·)b‖_{L⁵(Q_τ)} ≤ C‖b‖₃` with `C` independent of `τ`. -/
theorem heatOrbit_five_smooth :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : Vec3 → Vec3),
      (∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i)) →
      (∀ i : Fin 3, HasCompactSupport (fun x => b x i)) → ∀ τ : ℝ, 0 < τ →
      eLpNorm (heatOrbit b) 5
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
        ENNReal.ofReal C * eLpNorm b 3 volume := by
  set S := gagliardoNirenbergSobolevConstant
  have hS : S ≠ ∞ := (Classical.choose_spec CKN.sobolev_L6_global).1
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt 3 ^ 3)
  set K : ℝ≥0∞ := S ^ (2 : ℝ) * (ENNReal.ofReal 9 * c) ^ (2 / 3 : ℝ) *
    (ENNReal.ofReal (3 / 2) * c)
  have hK : K ≠ ∞ := by
    apply ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hS)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)))
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hKp : K ^ (1 / (5 : ℝ)) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK
  refine ⟨(K ^ (1 / (5 : ℝ))).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro b hb hbc τ hτ
  rw [ENNReal.ofReal_toReal hKp, show (5 : ℝ≥0∞) = ENNReal.ofReal 5 by norm_num]
  apply eLpNorm_ofReal_le_of_lintegral_le (by norm_num)
    (heatOrbit_aestronglyMeasurable_smooth hb hbc τ)
  set B := ∫ x : Vec3, vec3EuclideanNorm (b x) ^ 3
  set X := eLpNorm b 3 volume
  have hB : 0 ≤ B := integral_nonneg fun x => pow_nonneg (vec3EuclideanNorm_nonneg _) 3
  have hY : ENNReal.ofReal B ≤ c * X ^ (3 : ℝ) := ofReal_integral_euclidean_cube_le hb hbc
  calc
    ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ), ‖heatOrbit b z‖ₑ ^ (5 : ℝ) ≤
        ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
          ENNReal.ofReal (vec3EuclideanNorm (heatOrbit b z)) ^ (5 : ℝ) := by
      apply lintegral_mono
      intro z
      change ‖heatOrbit b z‖ₑ ^ (5 : ℝ) ≤ _
      rw [← ofReal_norm]
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal
        (norm_le_vec3EuclideanNorm _)) (by norm_num)
    _ ≤ _ := heatOrbit_five_lintegral_smooth hb hbc hτ
    _ = S ^ (2 : ℝ) * (ENNReal.ofReal 9 * ENNReal.ofReal B) ^ (2 / 3 : ℝ) *
          (ENNReal.ofReal (3 / 2) * ENNReal.ofReal B) := by
      have h1 (y : ℝ) : (27 : ℝ) * ((1 / 3 : ℝ) * y) = 9 * y := by ring
      have h2 (y : ℝ) : (9 / 2 : ℝ) * ((1 / 3 : ℝ) * y) = (3 / 2) * y := by ring
      rw [h1, h2, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
    _ ≤ S ^ (2 : ℝ) * (ENNReal.ofReal 9 * (c * X ^ (3 : ℝ))) ^ (2 / 3 : ℝ) *
          (ENNReal.ofReal (3 / 2) * (c * X ^ (3 : ℝ))) := by gcongr
    _ = K * X ^ (5 : ℝ) := by
      rw [← mul_assoc (ENNReal.ofReal 9), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        ← ENNReal.rpow_mul, show (5 : ℝ) = 3 * (2 / 3) + 3 by norm_num,
        ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      simp only [K]
      ring

end ESS

end
