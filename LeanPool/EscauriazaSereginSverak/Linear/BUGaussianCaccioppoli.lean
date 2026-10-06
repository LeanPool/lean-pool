/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCRestriction
public import LeanPool.EscauriazaSereginSverak.Linear.Caccioppoli
public import LeanPool.EscauriazaSereginSverak.Linear.UCWeightBound
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianCellWeight

/-!
# Caccioppoli estimates on Gaussian collar cells

The local energy inequality applies to each enlarged cell of the rescaled
Gaussian collar.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

private theorem buGaussian_memLp_of_local_l2
    {E : Type*} [NormedAddCommGroup E]
    {U : Set ParabolicPoint} {f : ParabolicPoint → E}
    (hlocal : LocallyIntegrableOn f U volume)
    (hfin : (∫⁻ z in U, ‖f z‖ₑ ^ (2 : ℝ)) < ⊤) :
    MemLp f 2 (volume.restrict U) := by
  have hrestrict : MemLp f 2 (volume.restrict U) := by
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (μ := volume.restrict U) (by norm_num) (by norm_num)
      hlocal.aestronglyMeasurable).2
    simpa using hfin
  exact hrestrict

/-- Finite quadratic data imply integrability of the scalar velocity and
gradient energies on the cylinder (`lem:bu-gaussian#caccioppoli`). -/
theorem buGaussian_local_energy_integrable
    {Ω : Set Vec3} {I : Set ℝ}
    {v : ParabolicPoint → Vec3}
    {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtv : ParabolicPoint → Vec3}
    (hweak : HasSpaceTimeWeakDerivs Ω I v Dv D2v Dtv)
    (hL2 : (∫⁻ z in spaceTimeSet Ω I,
      ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤) :
    Integrable (fun z => vec3EuclideanNorm (v z) ^ 2)
        (volume.restrict (spaceTimeSet Ω I)) ∧
      Integrable (fun z => spatialGradientSq v Dv z)
        (volume.restrict (spaceTimeSet Ω I)) := by
  let U : Set ParabolicPoint := spaceTimeSet Ω I
  have hVfin : (∫⁻ z in U, ‖v z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    apply (lintegral_mono ?_).trans_lt hL2
    intro z
    exact le_add_of_nonneg_right (by positivity) |>.trans
      (le_add_of_nonneg_right (by positivity) |>.trans
        (le_add_of_nonneg_right (by positivity)))
  have hDvfin : (∫⁻ z in U, ‖Dv z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    apply (lintegral_mono ?_).trans_lt hL2
    intro z
    exact le_add_of_nonneg_left (by positivity) |>.trans
      (le_add_of_nonneg_right (by positivity) |>.trans
        (le_add_of_nonneg_right (by positivity)))
  have hVmem : MemLp v 2 (volume.restrict U) :=
    buGaussian_memLp_of_local_l2 hweak.1 (by simpa [U] using hVfin)
  have hDvMem : MemLp Dv 2 (volume.restrict U) :=
    buGaussian_memLp_of_local_l2 hweak.2.1 (by simpa [U] using hDvfin)
  have hVnorm : MemLp (fun z => vec3EuclideanNorm (v z)) 2
      (volume.restrict U) := by
    apply hVmem.of_nnnorm_le_mul (c := 2)
      (continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
        hVmem.aestronglyMeasurable)
    filter_upwards [] with z
    have hsqrt : Real.sqrt 3 ≤ 2 := (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
    have hreal : vec3EuclideanNorm (v z) ≤ 2 * ‖v z‖ := by
      calc
        vec3EuclideanNorm (v z) ≤ Real.sqrt 3 * ‖v z‖ :=
          vec3EuclideanNorm_le_sqrt_three_mul_norm _
        _ ≤ 2 * ‖v z‖ := mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)
    have hreal' : (‖vec3EuclideanNorm (v z)‖₊ : ℝ) ≤
        2 * (‖‖v z‖‖₊ : ℝ) := by
      simpa only [coe_nnnorm, Real.norm_eq_abs,
        abs_of_nonneg (vec3EuclideanNorm_nonneg _),
        abs_of_nonneg (norm_nonneg _)] using hreal
    have hreal'' : (‖vec3EuclideanNorm (v z)‖₊ : ℝ) ≤
        2 * (‖v z‖₊ : ℝ) := by
      simpa only [coe_nnnorm, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)] using hreal'
    exact_mod_cast hreal''
  have hVint : Integrable (fun z => vec3EuclideanNorm (v z) ^ 2)
      (volume.restrict U) := by
    have h := hVnorm.integrable_norm_pow (p := 2) (by norm_num)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)] using h
  have hDvcomp (i j : Fin 3) : MemLp (fun z => Dv z i j) 2
      (volume.restrict U) :=
    memLp_pi_component (memLp_pi_component hDvMem i) j
  have hGint : Integrable (fun z => spatialGradientSq v Dv z)
      (volume.restrict U) := by
    change Integrable (fun z => ∑ i : Fin 3, ∑ j : Fin 3, (Dv z i j) ^ 2)
      (volume.restrict U)
    exact integrable_finsetSum Finset.univ fun i hi =>
      integrable_finsetSum Finset.univ fun j hj =>
        (hDvcomp i j).integrable_sq
  exact ⟨hVint, hGint⟩

/-- Apply `lem:caccioppoli` to one space-time cell inside the rescaled
Gaussian cylinder. -/
theorem buGaussian_cell_caccioppoli
    (ρ : ℝ) (x : Vec3) (σ t r c : ℝ) (hr : 0 < r)
    (hc : 0 ≤ c)
    {v : ParabolicPoint → Vec3}
    {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtv : ParabolicPoint → Vec3}
    (hcont : ContinuousOn v (vec3Ball 0 ρ ×ˢ Ico σ 2))
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo σ 2) v Dv D2v Dtv)
    (hL2 : (∫⁻ z in spaceTimeSet (vec3Ball 0 ρ) (Ioo σ 2),
      ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet (vec3Ball 0 ρ) (Ioo σ 2))),
      vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) ≤
        c * (vec3EuclideanNorm (v z) + Real.sqrt (spatialGradientSq v Dv z)))
    (hspace : vec3Ball x (2 * r) ⊆ vec3Ball 0 ρ)
    (htime : Ioo t (t + 4 * r ^ 2) ⊆ Ioo σ 2) :
    (∫ z in spaceTimeSet (vec3Ball x r) (Ioo t (t + r ^ 2)),
      spatialGradientSq v Dv z ∂(volume : Measure ParabolicPoint)) ≤
      256 * (1 + c ^ 2 + 1 / r ^ 2) *
        (∫ z in spaceTimeSet (vec3Ball x (2 * r))
          (Ioo t (t + 4 * r ^ 2)), vec3EuclideanNorm (v z) ^ 2
          ∂(volume : Measure ParabolicPoint)) := by
  let Ω : Set Vec3 := vec3Ball x (2 * r)
  let I : Set ℝ := Ioo t (t + 4 * r ^ 2)
  have hBopen : IsOpen (vec3Ball 0 ρ) := isOpen_vec3Ball 0 ρ
  have hcont' : ContinuousOn v
      (vec3Ball 0 ρ ×ˢ Ioo σ 2) :=
    hcont.mono (Set.prod_mono (subset_refl _) (Ioo_subset_Ico_self))
  have hrestricted := uc_restrict_data c Ω (vec3Ball 0 ρ) I (Ioo σ 2)
    v Dv D2v Dtv hBopen isOpen_Ioo hspace htime hcont' hweak hL2 hineq
  have hcacc := caccioppoli x t r c hr hc hrestricted.2.1
    hrestricted.2.2.1 hrestricted.2.2.2
  simpa [Ω, I] using hcacc

private theorem weighted_cell_integral_comparison
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (W G V : X → ℝ) (z₀ K C : ℝ)
    (hWG : Integrable (fun z => W z * G z) (μ.restrict A))
    (hG : Integrable G (μ.restrict A))
    (hV : Integrable V (μ.restrict B))
    (hWV : Integrable (fun z => W z * V z) (μ.restrict B))
    (hWin : ∀ z ∈ A, W z ≤ K * z₀)
    (hWout : ∀ z ∈ B, z₀ ≤ K * W z)
    (hGnonneg : ∀ z, 0 ≤ G z) (hVnonneg : ∀ z, 0 ≤ V z)
    (hK : 0 ≤ K) (hz₀ : 0 ≤ z₀) (hC : 0 ≤ C)
    (hacc : (∫ z in A, G z ∂μ) ≤ C * (∫ z in B, V z ∂μ)) :
    (∫ z in A, W z * G z ∂μ) ≤ K ^ 2 * C * (∫ z in B, W z * V z ∂μ) := by
  have hAref : Integrable (fun z => (K * z₀) * G z) (μ.restrict A) :=
    hG.const_mul (K * z₀)
  have hAmono : ∀ᵐ z ∂(μ.restrict A),
      W z * G z ≤ (K * z₀) * G z := by
    filter_upwards [ae_restrict_mem hA] with z hz
    exact mul_le_mul_of_nonneg_right (hWin z hz) (hGnonneg z)
  have hAint : (∫ z in A, W z * G z ∂μ) ≤
      (K * z₀) * (∫ z in A, G z ∂μ) := by
    calc
      _ ≤ ∫ z, (K * z₀) * G z ∂(μ.restrict A) :=
        integral_mono_ae hWG hAref hAmono
      _ = (K * z₀) * ∫ z in A, G z ∂μ := by rw [integral_const_mul]
  have hBref : Integrable (fun z => z₀ * V z) (μ.restrict B) :=
    hV.const_mul z₀
  have hBmono : ∀ᵐ z ∂(μ.restrict B),
      z₀ * V z ≤ K * (W z * V z) := by
    filter_upwards [ae_restrict_mem hB] with z hz
    calc
      z₀ * V z ≤ (K * W z) * V z :=
        mul_le_mul_of_nonneg_right (hWout z hz) (hVnonneg z)
      _ = K * (W z * V z) := by ring
  have hBint : z₀ * (∫ z in B, V z ∂μ) ≤
      K * (∫ z in B, W z * V z ∂μ) := by
    calc
      _ = ∫ z, z₀ * V z ∂(μ.restrict B) := by rw [integral_const_mul]
      _ ≤ ∫ z, K * (W z * V z) ∂(μ.restrict B) :=
        integral_mono_ae hBref (hWV.const_mul K) hBmono
      _ = K * ∫ z in B, W z * V z ∂μ := by rw [integral_const_mul]
  have hleft : 0 ≤ K * z₀ := mul_nonneg hK hz₀
  calc
    _ ≤ (K * z₀) * (C * (∫ z in B, V z ∂μ)) :=
      hAint.trans (mul_le_mul_of_nonneg_left hacc hleft)
    _ = (K * C) * (z₀ * ∫ z in B, V z ∂μ) := by ring
    _ ≤ (K * C) * (K * ∫ z in B, W z * V z ∂μ) :=
      mul_le_mul_of_nonneg_left hBint (mul_nonneg hK hC)
    _ = K ^ 2 * C * (∫ z in B, W z * V z ∂μ) := by ring

private theorem gaussian_cell_nested_in_domain
    {ρ r t : ℝ} {x : Vec3} (hr : 0 < r)
    (hspace : vec3Ball x r ⊆ vec3Ball 0 ρ)
    (htime : Ioo t (t + r ^ 2) ⊆ Ioo (1 / 6) 2) :
    spaceTimeSet (vec3Ball x (r / 2)) (Ioo t (t + (r / 2) ^ 2)) ⊆
        spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2) ∧
      spaceTimeSet (vec3Ball x r) (Ioo t (t + r ^ 2)) ⊆
        spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2) := by
  constructor
  · intro z hz
    refine ⟨hspace (vec3Ball_mono
      (div_le_self hr.le (by norm_num : 1 ≤ (2 : ℝ))) hz.1), ?_⟩
    have hztime : z.2 ∈ Ioo t (t + r ^ 2) := by
      refine ⟨hz.2.1, ?_⟩
      have hhalf : 0 ≤ r / 2 := by positivity
      have hle : r / 2 ≤ r := by linarith only [hr]
      have hsquare : (r / 2) ^ 2 ≤ r ^ 2 :=
        (sq_le_sq₀ hhalf hr.le).2 hle
      exact lt_of_lt_of_le hz.2.2 (add_le_add_right hsquare t)
    exact htime hztime
  · intro z hz
    exact ⟨hspace hz.1, htime hz.2⟩

/-- The Gaussian weight lets the Caccioppoli estimate be compared on one
enlarged collar cell. -/
theorem buGaussian_weighted_caccioppoli_cell
    {ρ a r c t : ℝ} {x : Vec3}
    (hρ : 0 < ρ) (ha : 0 < a) (hr : 0 < r)
    (hcenter : vec3EuclideanNorm x ≤ ρ - 1 / 2)
    (hspace : vec3Ball x r ⊆ vec3Ball 0 ρ)
    (htime : Ioo t (t + r ^ 2) ⊆ Ioo (1 / 6) 2)
    {v : ParabolicPoint → Vec3}
    {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtv : ParabolicPoint → Vec3}
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo (1 / 6) 2)
      v Dv D2v Dtv)
    (hcont : ContinuousOn v (vec3Ball 0 ρ ×ˢ Ico (1 / 6) 2))
    (hc : 0 ≤ c)
    (hL2 : (∫⁻ z in spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2),
      ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2))),
      vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) ≤
        c * (vec3EuclideanNorm (v z) + Real.sqrt (spatialGradientSq v Dv z))) :
    (∫ z in spaceTimeSet (vec3Ball x (r / 2))
        (Ioo t (t + (r / 2) ^ 2)),
      ucGaussianWeight a z * spatialGradientSq v Dv z) ≤
      Real.exp (2 * (56 * a * r ^ 2 + 12 * ρ * r + 36 * ρ ^ 2 * r ^ 2)) *
        (256 * (1 + c ^ 2 + 1 / (r / 2) ^ 2)) *
        (∫ z in spaceTimeSet (vec3Ball x r) (Ioo t (t + r ^ 2)),
          ucGaussianWeight a z * vec3EuclideanNorm (v z) ^ 2) := by
  let U : Set ParabolicPoint := spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2)
  let Uinner : Set ParabolicPoint :=
    spaceTimeSet (vec3Ball x (r / 2)) (Ioo t (t + (r / 2) ^ 2))
  let Uouter : Set ParabolicPoint :=
    spaceTimeSet (vec3Ball x r) (Ioo t (t + r ^ 2))
  let W : ParabolicPoint → ℝ := ucGaussianWeight a
  let V : ParabolicPoint → ℝ := fun z => vec3EuclideanNorm (v z) ^ 2
  let G : ParabolicPoint → ℝ := fun z => spatialGradientSq v Dv z
  let K : ℝ := Real.exp (56 * a * r ^ 2 + 12 * ρ * r + 36 * ρ ^ 2 * r ^ 2)
  have hUopen : IsOpen (vec3Ball 0 ρ) := isOpen_vec3Ball 0 ρ
  have hIopen : IsOpen (Ioo (1 / 6 : ℝ) 2) := isOpen_Ioo
  have hEint := buGaussian_local_energy_integrable hweak hL2
  have hWmeas : AEStronglyMeasurable W (volume.restrict U) :=
    ucGaussianWeight_measurable a |>.aestronglyMeasurable
      |>.mono_measure Measure.restrict_le_self
  have hWbound : ∀ᵐ z ∂(volume.restrict U), W z ≤
      ((1 / 6 : ℝ) * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a) := by
    filter_upwards [ae_restrict_mem (isOpen_spaceTimeSet _ _ hUopen hIopen).measurableSet]
      with z hz
    exact ucGaussianWeight_le_after (by norm_num) (le_of_lt ha) hz.2.1.le hz.2.2.le
  have hWnormbound : ∀ᵐ z ∂(volume.restrict U),
      ‖W z‖ ≤ ((1 / 6 : ℝ) * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a) := by
    filter_upwards [hWbound, ae_restrict_mem
      (isOpen_spaceTimeSet _ _ hUopen hIopen).measurableSet] with z hz hzmem
    rw [Real.norm_eq_abs, abs_of_nonneg
      (ucGaussianWeight_nonneg a (by linarith only [hzmem.2.1]))]
    exact hz
  have hWVint : Integrable (fun z => W z * V z) (volume.restrict U) := by
    have h := hEint.1.bdd_mul hWmeas hWnormbound
    simpa [U, W, V, mul_comm] using h
  have hWGint : Integrable (fun z => W z * G z) (volume.restrict U) := by
    have h := hEint.2.bdd_mul hWmeas hWnormbound
    simpa [U, W, G, mul_comm] using h
  have hnested := gaussian_cell_nested_in_domain hr hspace htime
  have hUinner : Uinner ⊆ U := by simpa [Uinner, U] using hnested.1
  have hUouter : Uouter ⊆ U := by simpa [Uouter, U] using hnested.2
  have hUinnermeas : MeasurableSet Uinner := by
    exact (vec3Ball_measurable x (r / 2)).prod measurableSet_Ioo
  have hUoutermeas : MeasurableSet Uouter := by
    exact (vec3Ball_measurable x r).prod measurableSet_Ioo
  let tmid : ℝ := t + r ^ 2 / 2
  let z₀ : ParabolicPoint := (x, tmid)
  have hmid : tmid ∈ Ioo t (t + r ^ 2) := by
    dsimp [tmid]
    constructor
    · exact lt_add_of_pos_right _ (div_pos (sq_pos_of_pos hr) (by norm_num))
    · have hsq : 0 < r ^ 2 := sq_pos_of_pos hr
      have hdiv : r ^ 2 / 2 < r ^ 2 := by
        apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).2
        calc
          r ^ 2 < 2 * r ^ 2 := by nlinarith only [hsq]
          _ = r ^ 2 * 2 := by ring
      exact add_lt_add_right hdiv t
  have hmidRange := htime hmid
  have htreflo : (1 / 6 : ℝ) ≤ tmid := hmidRange.1.le
  have htrefhi : tmid ≤ 2 := hmidRange.2.le
  have hxρ : vec3EuclideanNorm x ≤ ρ :=
    hcenter.trans (sub_le_self ρ (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have hWeightRefNonneg : 0 ≤ W z₀ :=
    ucGaussianWeight_nonneg a
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 6) htreflo)
  have hWinnerBound (z : ParabolicPoint) (hz : z ∈ Uinner) :
      W z ≤ K * W z₀ := by
    have hsp : vec3EuclideanNorm (z.1 - x) < 2 * r := by
      exact (vec3Ball_mono
        (div_le_self hr.le (by norm_num : 1 ≤ (2 : ℝ))) hz.1).trans
          (by nlinarith only [hr])
    have hyρ : vec3EuclideanNorm z.1 ≤ ρ := by
      have := hspace (vec3Ball_mono
        (div_le_self hr.le (by norm_num : 1 ≤ (2 : ℝ))) hz.1)
      have hnorm : vec3EuclideanNorm (z.1 - 0) < ρ := by
        simpa only [mem_vec3Ball] using this
      simpa only [sub_zero] using hnorm.le
    have hztime : z.2 ∈ Ioo t (t + r ^ 2) := by
      rcases hz with ⟨_, hs⟩
      refine ⟨hs.1, ?_⟩
      have hhalf : 0 ≤ r / 2 := by positivity
      have hle : r / 2 ≤ r := by
        exact div_le_self hr.le (by norm_num : 1 ≤ (2 : ℝ))
      have hsquare : (r / 2) ^ 2 ≤ r ^ 2 :=
        (sq_le_sq₀ hhalf hr.le).2 hle
      exact lt_of_lt_of_le hs.2 (add_le_add_right hsquare t)
    have hzRange := htime hztime
    have hs : (1 / 6 : ℝ) ≤ z.2 := hzRange.1.le
    have ht : (1 / 6 : ℝ) ≤ tmid := htreflo
    have hdt : |z.2 - tmid| ≤ 4 * r ^ 2 := by
      have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
      rcases hz.2 with ⟨hl, hu⟩
      dsimp [tmid]
      rw [abs_le]
      constructor <;> nlinarith only [hl, hu, hr2]
    have hcompare := buGaussian_weight_cell_comparison
      hρ ha hr rfl rfl hsp hyρ hxρ hs ht hdt
    have hη : (z.1, z.2) = z := by cases z; rfl
    rw [← hη]
    simpa [W, K, z₀] using hcompare
  have hWouterBound (z : ParabolicPoint) (hz : z ∈ Uouter) :
      W z₀ ≤ K * W z := by
    have hsp : vec3EuclideanNorm (x - z.1) < 2 * r := by
      have h := hz.1
      have hn : vec3EuclideanNorm (z.1 - x) < r := h
      have hnorm : vec3EuclideanNorm (x - z.1) = vec3EuclideanNorm (z.1 - x) := by
        rw [show x - z.1 = -(z.1 - x) by abel, vec3EuclideanNorm_neg]
      rw [hnorm]
      linarith only [hn, hr]
    have houterρ : vec3EuclideanNorm z.1 ≤ ρ := by
      have hn := hspace hz.1
      have hnorm : vec3EuclideanNorm (z.1 - 0) < ρ := by
        simpa only [mem_vec3Ball] using hn
      simpa only [sub_zero] using hnorm.le
    have hs : (1 / 6 : ℝ) ≤ tmid := htreflo
    have ht : (1 / 6 : ℝ) ≤ z.2 := by
      exact (htime hz.2).1.le
    have hdt : |tmid - z.2| ≤ 4 * r ^ 2 := by
      rcases hz.2 with ⟨hl, hu⟩
      dsimp [tmid]
      rw [abs_le]
      constructor <;> nlinarith only [hl, hu, sq_nonneg r]
    have hcompare := buGaussian_weight_cell_comparison
      hρ ha hr rfl rfl hsp hxρ houterρ hs ht hdt
    have hη : (z.1, z.2) = z := by cases z; rfl
    rw [← hη]
    simpa [W, K, z₀] using hcompare
  have hInnerGInt : Integrable G (volume.restrict Uinner) :=
    hEint.2.mono_measure (Measure.restrict_mono hUinner le_rfl)
  have hOuterVInt : Integrable V (volume.restrict Uouter) :=
    hEint.1.mono_measure (Measure.restrict_mono hUouter le_rfl)
  have hInnerWGInt : Integrable (fun z => W z * G z)
      (volume.restrict Uinner) :=
    hWGint.mono_measure (Measure.restrict_mono hUinner le_rfl)
  have hOuterWVInt : Integrable (fun z => W z * V z)
      (volume.restrict Uouter) :=
    hWVint.mono_measure (Measure.restrict_mono hUouter le_rfl)
  have hacc := buGaussian_cell_caccioppoli ρ x (1 / 6) t (r / 2) c
    (div_pos hr (by norm_num)) hc hcont hweak hL2 hineq (by
      have hrad : 2 * (r / 2) = r := by ring
      rw [hrad]
      exact hspace) (by
      have hpow : 4 * (r / 2) ^ 2 = r ^ 2 := by ring
      simpa [hpow] using htime)
  have hacc' : (∫ z in Uinner, G z ∂(volume : Measure ParabolicPoint)) ≤
      256 * (1 + c ^ 2 + 1 / (r / 2) ^ 2) *
        ∫ z in Uouter, V z ∂(volume : Measure ParabolicPoint) := by
    have hrad : 2 * (r / 2) = r := by ring
    have htime' : 4 * (r / 2) ^ 2 = r ^ 2 := by ring
    rw [hrad, htime'] at hacc
    simpa [Uinner, Uouter, G, V] using hacc
  have hGnonneg (z : ParabolicPoint) : 0 ≤ G z := by
    unfold G spatialGradientSq
    positivity
  have hVnonneg (z : ParabolicPoint) : 0 ≤ V z := by positivity
  have hKnonneg : 0 ≤ K := by dsimp [K]; exact Real.exp_nonneg _
  have hCnonneg : 0 ≤ 256 * (1 + c ^ 2 + 1 / (r / 2) ^ 2) := by positivity
  have hfinal := weighted_cell_integral_comparison Uinner Uouter
    hUinnermeas hUoutermeas W G V (W z₀) K
    (256 * (1 + c ^ 2 + 1 / (r / 2) ^ 2)) hInnerWGInt hInnerGInt
    hOuterVInt hOuterWVInt hWinnerBound hWouterBound hGnonneg hVnonneg
    hKnonneg hWeightRefNonneg hCnonneg hacc'
  have hexp : K ^ 2 = Real.exp
      (2 * (56 * a * r ^ 2 + 12 * ρ * r + 36 * ρ ^ 2 * r ^ 2)) := by
    dsimp [K]
    rw [show 2 * (56 * a * r ^ 2 + 12 * ρ * r + 36 * ρ ^ 2 * r ^ 2) =
      (56 * a * r ^ 2 + 12 * ρ * r + 36 * ρ ^ 2 * r ^ 2) +
        (56 * a * r ^ 2 + 12 * ρ * r + 36 * ρ ^ 2 * r ^ 2) by ring]
    rw [pow_two, ← Real.exp_add]
  simpa [Uinner, Uouter, W, G, V, hexp] using hfinal

end ESS

end
