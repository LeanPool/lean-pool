/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.HeatCriticalSmooth
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Heat Critical Estimate

The regularized entropy density of a smooth heat orbit is integrable at
each positive time, as used in `lem:pv-heat-critical`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat


noncomputable section

namespace ESS

/-- The regularized entropy density of a smooth heat orbit is integrable at
each positive time, as used in `lem:pv-heat-critical`. -/
theorem heatRegEnergy_heatConv_integrable {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    Integrable (fun x : Vec3 => heatRegEnergy η (heatConvVec3 t b x)) volume := by
  obtain ⟨M, hM, hMtail⟩ := heatConvVec3_norm_decay hb hbc
  let K : ℝ := (3 * η + 2 * M) / 6
  let C : ℝ := K * M ^ 2
  have hC : 0 ≤ C := by dsimp [C, K]; positivity
  have hden (x : Vec3) : 1 ≤ 1 + vec3EuclideanNorm x := by
    linarith only [vec3EuclideanNorm_nonneg x]
  have hdenpow (x : Vec3) (k : ℕ) :
      1 ≤ (1 + vec3EuclideanNorm x) ^ k := one_le_pow₀ (hden x)
  have huniform (x : Vec3) : vec3EuclideanNorm (heatConvVec3 t b x) ≤ M := by
    have htail := hMtail ht x
    have hquot : M / (1 + vec3EuclideanNorm x) ^ 3 ≤ M := by
      apply (div_le_iff₀
        (lt_of_lt_of_le zero_lt_one (hdenpow x 3))).2
      calc
        M = M * 1 := by ring
        _ ≤ M * (1 + vec3EuclideanNorm x) ^ 3 :=
          mul_le_mul_of_nonneg_left (hdenpow x 3) hM
    exact htail.trans hquot
  have hsum (x : Vec3) :
      (∑ i : Fin 3, (heatConvVec3 t b x i) ^ 2) =
        (vec3EuclideanNorm (heatConvVec3 t b x)) ^ 2 := by
    unfold vec3EuclideanNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  have hbound (x : Vec3) :
      |heatRegEnergy η (heatConvVec3 t b x)| ≤
        C / (1 + vec3EuclideanNorm x) ^ 6 := by
    have henergy := heatRegEnergy_le_mul_sum_sq hη hM
      (heatConvVec3 t b x) (huniform x)
    have hnormSq : (vec3EuclideanNorm (heatConvVec3 t b x)) ^ 2 ≤
        (M / (1 + vec3EuclideanNorm x) ^ 3) ^ 2 :=
      pow_le_pow_left₀ (vec3EuclideanNorm_nonneg _) (hMtail ht x) 2
    have hpoint : heatRegEnergy η (heatConvVec3 t b x) ≤
        C / (1 + vec3EuclideanNorm x) ^ 6 := by
      calc
        heatRegEnergy η (heatConvVec3 t b x) ≤
            K * (∑ i : Fin 3, (heatConvVec3 t b x i) ^ 2) := by
              simpa [K] using henergy
        _ = K * (vec3EuclideanNorm (heatConvVec3 t b x)) ^ 2 := by rw [hsum]
        _ ≤ K * (M / (1 + vec3EuclideanNorm x) ^ 3) ^ 2 :=
          mul_le_mul_of_nonneg_left hnormSq (by dsimp [K]; positivity)
        _ = C / (1 + vec3EuclideanNorm x) ^ 6 := by
          dsimp [C, K]
          rw [div_pow, ← pow_mul]
          ring
    rw [abs_of_nonneg (heatRegEnergy_nonneg hη _)]
    exact hpoint
  have hcont : Continuous (fun x : Vec3 =>
      heatRegEnergy η (heatConvVec3 t b x)) := by
    have hprofile : ContDiff ℝ (⊤ : ℕ∞) (heatConvVec3 t b) := by
      rw [contDiff_pi]
      intro i
      simpa [heatConvVec3] using heatConv_smooth_input (hb i) (hbc i) ht
    exact ((heatRegEnergy_contDiff hη).comp hprofile).continuous
  apply (heat_decay_six_integrable C hC).mono' hcont.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  exact hbound x

/-- The regularized critical profile's directional gradient is controlled by
the entropy-test dissipation, pointwise in space and time. -/
theorem heatRegG_heatConv_spatial_grad_sq_le_dissipation
    {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {t η : ℝ} (ht : 0 < t) (hη : 0 < η)
    (x : Vec3) (j : Fin 3) :
    (CKN.spatialDeriv
      (fun y => heatRegG η (heatConvVec3 t b y)) j x) ^ 2 ≤
      (9 / 2 : ℝ) * ∑ i : Fin 3,
        CKN.spatialDeriv
          (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
        CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x := by
  have hprofile : ContDiff ℝ (⊤ : ℕ∞) (heatConvVec3 t b) := by
    rw [contDiff_pi]
    intro i
    simpa [heatConvVec3] using heatConv_smooth_input (hb i) (hbc i) ht
  have hh : DifferentiableAt ℝ (heatConvVec3 t b) x :=
    (hprofile.differentiable (by norm_num)).differentiableAt
  let w : Vec3 := fderiv ℝ (heatConvVec3 t b) x (CKN.basisVec j)
  have hGcomp : CKN.spatialDeriv
      (fun y => heatRegG η (heatConvVec3 t b y)) j x =
        fderiv ℝ (heatRegG η) (heatConvVec3 t b x) w := by
    rw [CKN.spatialDeriv, heatRegG_comp_fderiv hη hh,
      ← heatRegG_fderiv hη]
  have hpair :
      (∑ i : Fin 3,
        CKN.spatialDeriv
          (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
        CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x) =
      ∑ i : Fin 3,
        fderiv ℝ (fun z : Vec3 => heatRegTest η z i)
          (heatConvVec3 t b x) w * w i := by
    apply Finset.sum_congr rfl
    intro i hi
    change (fderiv ℝ (fun y : Vec3 =>
      heatRegTest η (heatConvVec3 t b y) i) x (CKN.basisVec j)) *
        CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x = _
    rw [heatRegTest_comp_fderiv hη hh i, ← heatRegTest_fderiv hη,
      ← heatConvVec3_fderiv_basis_apply hb hbc ht x i j]
  have hpoint := heatReg_gradient_bound hη (heatConvVec3 t b x) w
  have htest := heatRegTest_dissipation_lower hη (heatConvVec3 t b x) w
  rw [hGcomp, hpair]
  calc
    (fderiv ℝ (heatRegG η) (heatConvVec3 t b x) w) ^ 2 ≤
        (9 / 2 : ℝ) *
          (heatRegSq η (heatConvVec3 t b x) ^ (1 / 2 : ℝ) - η) *
            ∑ i : Fin 3, w i ^ 2 := hpoint
    _ ≤ (9 / 2 : ℝ) *
        ∑ i : Fin 3,
          fderiv ℝ (fun z : Vec3 => heatRegTest η z i)
            (heatConvVec3 t b x) w * w i := by
      calc
        _ = (9 / 2 : ℝ) *
            ((heatRegSq η (heatConvVec3 t b x) ^ (1 / 2 : ℝ) - η) *
              ∑ i : Fin 3, w i ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left htest (by norm_num)

/-- The entropy-integral derivative equals minus the integrated spatial test
dissipation for smooth compact data. -/
theorem heatRegEnergy_integral_deriv_eq_neg_dissipation
    {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    deriv (fun s : ℝ => ∫ x : Vec3,
      heatRegEnergy η (heatConvVec3 s b x)) t =
      -∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3,
        CKN.spatialDeriv
          (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
        CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x := by
  have hderiv := heatRegEnergy_integral_hasDerivAt hb hbc ht hη
  have hibp := heatRegEnergy_integral_derivative_eq_neg_gradient hb hbc ht hη
  rw [hderiv.deriv]
  exact hibp

/-- The spatial gradient of the regularized critical profile is square
integrable for each positive time. -/
theorem heatRegG_heatConv_spatial_grad_sq_integrable
    {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    Integrable (fun x : Vec3 => ∑ j : Fin 3,
      (CKN.spatialDeriv
        (fun y => heatRegG η (heatConvVec3 t b y)) j x) ^ 2) volume := by
  let H := heatRegG_heatConv_h1 hb hbc ht hη
  have hgrad (j : Fin 3) : MemLp (fun x : Vec3 => H.grad x j) 2 volume := by
    simpa [H, CKN.GradMemL2On, CKN.MemL2On, CKN.MemLpOn,
      CKN.volumeOn, Measure.restrict_univ] using H.gradMemL2 j
  have hsq (j : Fin 3) : Integrable (fun x : Vec3 =>
      (CKN.spatialDeriv
        (fun y => heatRegG η (heatConvVec3 t b y)) j x) ^ 2) volume := by
    have hmem := hgrad j
    have hmemSq := (memLp_two_iff_integrable_sq
      hmem.aestronglyMeasurable).1 hmem
    have heq : (fun x : Vec3 => H.grad x j) = fun x =>
        CKN.spatialDeriv
          (fun y => heatRegG η (heatConvVec3 t b y)) j x := by
      rfl
    exact hmemSq.congr (Filter.Eventually.of_forall fun x => by
      change (H.grad x j) ^ 2 = _
      have hpoint := congrFun heq x
      rw [hpoint])
  exact integrable_finsetSum Finset.univ (fun j hj => hsq j)

/-- Spatial integration of the gradient inequality compares its square
integral with the integrated entropy-test dissipation. -/
theorem heatRegG_heatConv_spatial_grad_sq_integral_le_dissipation
    {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    (∫ x : Vec3, ∑ j : Fin 3,
      (CKN.spatialDeriv
        (fun y => heatRegG η (heatConvVec3 t b y)) j x) ^ 2) ≤
      (9 / 2 : ℝ) * ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3,
        CKN.spatialDeriv
          (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
        CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x := by
  have hleft := heatRegG_heatConv_spatial_grad_sq_integrable hb hbc ht hη
  have hdiss := heatRegTest_heatConv_dissipation_integrable hb hbc ht hη
  have hterm := hdiss.1
  have hright := hdiss.2
  have hpoint (x : Vec3) :
      ∑ j : Fin 3,
        (CKN.spatialDeriv
          (fun y => heatRegG η (heatConvVec3 t b y)) j x) ^ 2 ≤
        (9 / 2 : ℝ) * ∑ i : Fin 3, ∑ j : Fin 3,
          CKN.spatialDeriv
            (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
          CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x := by
    calc
      _ = ∑ j : Fin 3,
          (CKN.spatialDeriv
            (fun y => heatRegG η (heatConvVec3 t b y)) j x) ^ 2 := rfl
      _ ≤ ∑ j : Fin 3,
          (9 / 2 : ℝ) * ∑ i : Fin 3,
            CKN.spatialDeriv
              (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
            CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x := by
        apply Finset.sum_le_sum
        intro j hj
        exact heatRegG_heatConv_spatial_grad_sq_le_dissipation hb hbc ht hη x j
      _ = (9 / 2 : ℝ) * ∑ i : Fin 3, ∑ j : Fin 3,
          CKN.spatialDeriv
            (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
          CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x := by
        rw [← Finset.mul_sum, Finset.sum_comm]
  have hright' : Integrable (fun x : Vec3 => (9 / 2 : ℝ) *
      ∑ i : Fin 3, ∑ j : Fin 3,
        CKN.spatialDeriv
          (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
        CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x) volume := by
    simpa only [smul_eq_mul] using hright.const_mul (9 / 2 : ℝ)
  have hrows (i : Fin 3) : Integrable (fun x : Vec3 => ∑ j : Fin 3,
      CKN.spatialDeriv
        (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
      CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x) volume :=
    integrable_finsetSum Finset.univ (fun j hj => hterm i j)
  have hsumIntegral :
      (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
        CKN.spatialDeriv
          (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
        CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3,
        CKN.spatialDeriv
          (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
        CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x := by
    rw [integral_finsetSum Finset.univ (fun i hi => hrows i)]
    congr 1
    funext i
    exact integral_finsetSum Finset.univ (fun j hj => hterm i j)
  calc
    _ ≤ ∫ x : Vec3, (9 / 2 : ℝ) * ∑ i : Fin 3, ∑ j : Fin 3,
          CKN.spatialDeriv
            (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
          CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x :=
        integral_mono_ae hleft hright' (Filter.Eventually.of_forall hpoint)
    _ = (9 / 2 : ℝ) * (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
          CKN.spatialDeriv
            (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
          CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x) :=
        integral_const_mul _ _
    _ = _ := by rw [hsumIntegral]

/-- Time integration of entropy dissipation is bounded by the initial
regularized entropy, uniformly in the terminal time. -/
theorem heatRegEnergy_time_dissipation_le_initial {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η) :
    IntervalIntegrable (fun t : ℝ => ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3,
      CKN.spatialDeriv
        (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
      CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x) volume 0 τ ∧
    (∫ t in (0 : ℝ)..τ, ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3,
      CKN.spatialDeriv
        (fun y => heatRegTest η (heatConvVec3 t b y) i) j x *
      CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x) ≤
      ∫ x : Vec3, heatRegEnergy η (b x) := by
  let E : ℝ → ℝ := fun s => ∫ x : Vec3,
    heatRegEnergy η (heatConvVec3 s b x)
  let E₀ : ℝ := ∫ x : Vec3, heatRegEnergy η (b x)
  let F : ℝ → ℝ := fun s => -(if s = 0 then E₀ else E s)
  let D : ℝ → ℝ := fun s => ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3,
    CKN.spatialDeriv
      (fun y => heatRegTest η (heatConvVec3 s b y) i) j x *
    CKN.spatialDeriv (fun y => heatConvVec3 s b y i) j x
  have hanti := heatRegEnergy_integral_antitoneOn hb hbc η hη
  change AntitoneOn E (Ioi 0) at hanti
  have hFanti : AntitoneOn (fun s : ℝ => if s = 0 then E₀ else E s)
      (Icc 0 τ) := by
    intro s hs r hr hsr
    by_cases hs0 : s = 0
    · subst s
      by_cases hr0 : r = 0
      · simp [hr0]
      · have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
        have hle := heatRegEnergy_integral_le_initial hb hbc hrpos hη
        simpa [E₀, E, hr0] using hle
    · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
      have hrpos : 0 < r := lt_of_lt_of_le hspos hsr
      have hle := hanti hspos hrpos hsr
      simpa [E, hs0, ne_of_gt hrpos] using hle
  have hFmono : MonotoneOn F (Icc 0 τ) := by
    intro s hs r hr hsr
    dsimp [F]
    exact neg_le_neg (hFanti hs hr hsr)
  have hFmonoU : MonotoneOn F (uIcc 0 τ) := by
    simpa [uIcc_of_le hτ.le] using hFmono
  have hint : IntervalIntegrable (deriv F) volume 0 τ :=
    hFmonoU.intervalIntegrable_deriv
  have hFderiv : ∀ s ∈ Ioo 0 τ, HasDerivAt F (deriv F s) s := by
    intro s hs
    have hEderiv := heatRegEnergy_integral_hasDerivAt hb hbc hs.1 hη
    have hlocal : F =ᶠ[nhds s] (fun r => -E r) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
      simp [F, E, ne_of_gt hr.1]
    have hderiv := hEderiv.neg.congr_of_eventuallyEq hlocal
    simpa only [hderiv.deriv] using hderiv
  have hlim0 : Tendsto F (nhdsWithin 0 (Ioi 0)) (nhds (-E₀)) := by
    have hE := heatRegEnergy_integral_tendsto_initial hb hbc η hη
    have hEneg := hE.neg
    have heq : F =ᶠ[nhdsWithin 0 (Ioi 0)] (fun s => -E s) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      change 0 < s at hs
      simp [F, E, hs.ne']
    exact (tendsto_congr' heq).2 hEneg
  have hlocalτ : F =ᶠ[nhds τ] (fun s => -E s) := by
    filter_upwards [eventually_ne_nhds (ne_of_gt hτ)] with s hs
    simp [F, E, hs]
  have hEderivτ := heatRegEnergy_integral_hasDerivAt hb hbc hτ hη
  have hFderivτ := hEderivτ.neg.congr_of_eventuallyEq hlocalτ
  have hlimτ : Tendsto F (nhdsWithin τ (Iio τ)) (nhds (F τ)) :=
    hFderivτ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    hτ hFderiv hint hlim0 hlimτ
  have hD_eq_deriv (s : ℝ) (hs : s ∈ Ioo 0 τ) : D s = deriv F s := by
    have hEderiv := heatRegEnergy_integral_deriv_eq_neg_dissipation
      hb hbc hs.1 hη
    have hEderivAt := heatRegEnergy_integral_hasDerivAt hb hbc hs.1 hη
    have hlocal : F =ᶠ[nhds s] (fun r => -E r) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
      simp [F, E, ne_of_gt hr.1]
    have hFderiv' := hEderivAt.neg.congr_of_eventuallyEq hlocal
    have hFderivEq : deriv F s = -deriv E s := by
      rw [hEderivAt.deriv]
      exact hFderiv'.deriv
    calc
      D s = -deriv E s := by
        have hEd : deriv E s = -D s := by
          simpa only [E, D] using hEderiv
        rw [hEd]
        ring
      _ = deriv F s := by
        exact hFderivEq.symm
  have hEqOn : (uIoo 0 τ).EqOn D (deriv F) := by
    intro s hs
    have hs' : s ∈ Ioo 0 τ := by simpa [uIoo_of_le hτ.le] using hs
    exact hD_eq_deriv s hs'
  have hrewrite : (∫ t in (0 : ℝ)..τ, D t) =
      ∫ t in (0 : ℝ)..τ, deriv F t :=
    intervalIntegral.integral_congr_uIoo (μ := volume) hEqOn
  have hEτnonneg : 0 ≤ E τ := by
    dsimp [E]
    exact integral_nonneg fun x => heatRegEnergy_nonneg hη (heatConvVec3 τ b x)
  have hresult : (∫ t in (0 : ℝ)..τ, D t) = E₀ - E τ := by
    calc
      (∫ t in (0 : ℝ)..τ, D t) = ∫ t in (0 : ℝ)..τ, deriv F t := hrewrite
      _ = F τ - -E₀ := by simpa [F] using hFTC
      _ = E₀ - E τ := by simp [F, E₀, E, hτ.ne']; ring
  have hbound : (∫ t in (0 : ℝ)..τ, D t) ≤ E₀ := by
    calc
      (∫ t in (0 : ℝ)..τ, D t) = E₀ - E τ := hresult
      _ ≤ E₀ := sub_le_self _ hEτnonneg
  have hDcongr : IntervalIntegrable D volume 0 τ ↔
      IntervalIntegrable (deriv F) volume 0 τ :=
    intervalIntegrable_congr_uIoo (f := D) (g := deriv F)
      (μ := (volume : Measure ℝ)) (a := 0) (b := τ) hEqOn
  have hintD : IntervalIntegrable D volume 0 τ := hDcongr.mpr hint
  refine ⟨?_, ?_⟩
  · simpa [D] using hintD
  · simpa [D, E₀] using hbound

end ESS

end
