/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.CrossEndpointConvolution
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinCutoff
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceGradientBumps
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpConvolution
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Fixed-time endpoint pairing limits

At a fixed time, the product of two cutoff-weighted spatial mollifications
converges in `L¹` to the product of the two slices when the slices lie in
`L∞ × L¹` or in `L² × L²`. These are the fixed-time estimates behind the
endpoint density passage in `lem:lps-comparison`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem lps_serrinRadius_eq (n : ℕ) : serrinRadius n = CKN.sliceRadius n := by
  unfold serrinRadius CKN.sliceRadius
  push_cast
  rfl

private theorem lps_mollify_radius_congr (g : Vec3 → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a = b) : CKN.mollify g a ha = CKN.mollify g b hb := by
  subst h
  rfl

private theorem lps_ae_tendsto_serrin_mollify {g : Vec3 → ℝ}
    (hg : LocallyIntegrable g volume) :
    ∀ᵐ x ∂(volume : Measure Vec3), Tendsto
      (fun n : ℕ => CKN.mollify g (serrinRadius n) (serrinRadius_pos n) x) atTop
      (𝓝 (g x)) := by
  filter_upwards [CKN.ae_tendsto_mollify_sliceRadius hg] with x hx
  refine hx.congr fun n => ?_
  rw [lps_mollify_radius_congr g (CKN.sliceRadius_pos n) (serrinRadius_pos n)
    (lps_serrinRadius_eq n).symm]

private theorem lps_eLpNorm_mollify_le {p : ℝ≥0∞} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    {g : Vec3 → ℝ} (hg : AEStronglyMeasurable g volume) (n : ℕ) :
    eLpNorm (CKN.mollify g (serrinRadius n) (serrinRadius_pos n)) p volume ≤
      eLpNorm g p volume := by
  have hmol := CKN.young_convolution_nonneg_integral_one_of_aemeasurable
    (d := 3) (p := p) hp hptop (CKN.mollifier_nonneg (serrinRadius_pos n))
    ((CKN.mollifier_contDiff (d := 3) (serrinRadius_pos n) (n := 0)).continuous
      |>.integrable_of_hasCompactSupport (CKN.mollifier_hasCompactSupport _))
    (CKN.mollifier_integral_one (serrinRadius_pos n))
    (CKN.mollifier_contDiff (d := 3) (serrinRadius_pos n) (n := 0)).continuous.measurable
    hg.aemeasurable
  simpa [CKN.mollify, CKN.mollifier] using hmol

private theorem lps_mollify_tendsto_norm {p : ℝ≥0∞} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    {g : Vec3 → ℝ} (hg : MemLp g p volume) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun x => CKN.mollify g (serrinRadius n) (serrinRadius_pos n) x - g x) p volume)
      atTop (𝓝 0) :=
  CKN.tendsto_eLpNorm_sub_zero_mollify hp hptop hg serrinRadius_tendsto serrinRadius_pos

/-- Cauchy–Schwarz for the spatial `L¹` norm of a product. -/
theorem lps_lintegral_mul_le_two {a b : Vec3 → ℝ}
    (ha : AEStronglyMeasurable a volume) (hb : AEStronglyMeasurable b volume) :
    ∫⁻ x, ‖a x‖ₑ * ‖b x‖ₑ ≤ eLpNorm a 2 volume * eLpNorm b 2 volume := by
  have : ENNReal.HolderTriple 2 2 1 := ⟨by simp [ENNReal.inv_two_add_inv_two]⟩
  have h := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) ha hb
  rw [eLpNorm_one_eq_lintegral_enorm (ha.smul hb)] at h
  simpa [Pi.smul_apply, smul_eq_mul, enorm_mul] using h

private theorem lps_enorm_le_of_abs_le {x c : ℝ} (h : |x| ≤ c) :
    ‖x‖ₑ ≤ ENNReal.ofReal c := by
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal h

private theorem lps_mollify_aesm {g : Vec3 → ℝ} (hg : LocallyIntegrable g volume) (n : ℕ) :
    AEStronglyMeasurable
      (CKN.mollify g (serrinRadius n) (serrinRadius_pos n)) volume :=
  (CKN.mollify_continuous (serrinRadius_pos n) hg).aestronglyMeasurable

/-- Fixed-time pairing limit for an essentially bounded factor and an
integrable factor: the cutoff-weighted product of mollifications converges in
`L¹`, with the error bounded by `4 B ‖g‖₁`. -/
theorem lps_endpoint_slice_pairing_linf_l1
    {f g : Vec3 → ℝ} {B : ℝ} (hf : AEStronglyMeasurable f volume)
    (hB : ∀ᵐ x ∂(volume : Measure Vec3), |f x| ≤ B)
    (hg : Integrable g volume) :
    (∀ n : ℕ, ∫⁻ x : Vec3,
      ‖serrinCutoff n x * CKN.mollify f (serrinRadius n) (serrinRadius_pos n) x *
        CKN.mollify g (serrinRadius n) (serrinRadius_pos n) x - f x * g x‖ₑ ≤
        4 * ENNReal.ofReal B * ∫⁻ x, ‖g x‖ₑ) ∧
    Tendsto (fun n : ℕ => ∫⁻ x : Vec3,
      ‖serrinCutoff n x * CKN.mollify f (serrinRadius n) (serrinRadius_pos n) x *
        CKN.mollify g (serrinRadius n) (serrinRadius_pos n) x - f x * g x‖ₑ)
      atTop (𝓝 0) := by
  set Mf : ℕ → Vec3 → ℝ := fun n => CKN.mollify f (serrinRadius n) (serrinRadius_pos n)
    with hMf
  set Mg : ℕ → Vec3 → ℝ := fun n => CKN.mollify g (serrinRadius n) (serrinRadius_pos n)
    with hMg
  have hB0 : 0 ≤ B := by
    obtain ⟨x, hx⟩ := hB.exists
    exact (abs_nonneg _).trans hx
  have hfTop : MemLp f ⊤ volume := memLp_top_of_bound hf B hB
  have hfLoc : LocallyIntegrable f volume := hfTop.locallyIntegrable le_top
  have hg1 : MemLp g 1 volume := memLp_one_iff_integrable.mpr hg
  have hMfB (n : ℕ) (x : Vec3) : |Mf n x| ≤ B :=
    lps_endpoint_mollify_linf_bound (serrinRadius_pos n) hf hB x
  have hMfMeas (n : ℕ) : AEStronglyMeasurable (Mf n) volume := lps_mollify_aesm hfLoc n
  have hMgMeas (n : ℕ) : AEStronglyMeasurable (Mg n) volume :=
    lps_mollify_aesm (hg.locallyIntegrable) n
  have hηMeas (n : ℕ) : AEStronglyMeasurable (serrinCutoff n) volume :=
    (serrinCutoff_contDiff n).continuous.aestronglyMeasurable
  have hηMfMeas (n : ℕ) : AEStronglyMeasurable (fun x => serrinCutoff n x * Mf n x) volume :=
    (hηMeas n).mul (hMfMeas n)
  have hηMfB (n : ℕ) (x : Vec3) : |serrinCutoff n x * Mf n x| ≤ B := by
    rw [abs_mul]
    calc |serrinCutoff n x| * |Mf n x| ≤ 1 * B :=
          mul_le_mul (serrinCutoff_abs_le_one n x) (hMfB n x) (abs_nonneg _) zero_le_one
      _ = B := one_mul B
  have hg1norm : eLpNorm g 1 volume = ∫⁻ x, ‖g x‖ₑ :=
    eLpNorm_one_eq_lintegral_enorm hg.aestronglyMeasurable
  have hgfin : (∫⁻ x, ‖g x‖ₑ) ≠ ⊤ := hg.hasFiniteIntegral.ne
  -- the two pieces
  let P : ℕ → ℝ≥0∞ := fun n => ∫⁻ x, ‖serrinCutoff n x * Mf n x - f x‖ₑ * ‖g x‖ₑ
  let Q : ℕ → ℝ≥0∞ := fun n => ∫⁻ x, ‖serrinCutoff n x * Mf n x‖ₑ * ‖Mg n x - g x‖ₑ
  have hPmeas (n : ℕ) : AEMeasurable
      (fun x => ‖serrinCutoff n x * Mf n x - f x‖ₑ * ‖g x‖ₑ) volume :=
    (((hηMfMeas n).sub hf).enorm).mul hg.aestronglyMeasurable.enorm
  have hQmeas (n : ℕ) : AEMeasurable
      (fun x => ‖serrinCutoff n x * Mf n x‖ₑ * ‖Mg n x - g x‖ₑ) volume :=
    ((hηMfMeas n).enorm).mul ((hMgMeas n).sub hg.aestronglyMeasurable).enorm
  have hSplit (n : ℕ) : ∫⁻ x : Vec3,
      ‖serrinCutoff n x * Mf n x * Mg n x - f x * g x‖ₑ ≤ P n + Q n := by
    calc
      _ ≤ ∫⁻ x, (‖serrinCutoff n x * Mf n x - f x‖ₑ * ‖g x‖ₑ +
          ‖serrinCutoff n x * Mf n x‖ₑ * ‖Mg n x - g x‖ₑ) := by
        refine lintegral_mono fun x => ?_
        have hid : serrinCutoff n x * Mf n x * Mg n x - f x * g x =
            (serrinCutoff n x * Mf n x - f x) * g x +
              (serrinCutoff n x * Mf n x) * (Mg n x - g x) := by ring
        rw [hid]
        calc _ ≤ ‖(serrinCutoff n x * Mf n x - f x) * g x‖ₑ +
              ‖(serrinCutoff n x * Mf n x) * (Mg n x - g x)‖ₑ := enorm_add_le _ _
          _ = _ := by rw [enorm_mul, enorm_mul]
      _ = P n + Q n := lintegral_add_left' (hPmeas n) _
  have hPbound (n : ℕ) : P n ≤ 2 * ENNReal.ofReal B * ∫⁻ x, ‖g x‖ₑ := by
    calc P n ≤ ∫⁻ x, (2 * ENNReal.ofReal B) * ‖g x‖ₑ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hB] with x hx
          gcongr
          have h2 : |serrinCutoff n x * Mf n x - f x| ≤ 2 * B := by
            calc _ ≤ |serrinCutoff n x * Mf n x| + |f x| := abs_sub _ _
              _ ≤ B + B := add_le_add (hηMfB n x) hx
              _ = 2 * B := by ring
          calc ‖serrinCutoff n x * Mf n x - f x‖ₑ ≤ ENNReal.ofReal (2 * B) :=
                lps_enorm_le_of_abs_le h2
            _ = 2 * ENNReal.ofReal B := by
                rw [ENNReal.ofReal_mul (by norm_num)]; simp
      _ = _ := lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)
  have hQbound (n : ℕ) : Q n ≤ ENNReal.ofReal B * eLpNorm (fun x => Mg n x - g x) 1 volume := by
    have hnorm : eLpNorm (fun x => Mg n x - g x) 1 volume =
        ∫⁻ x, ‖Mg n x - g x‖ₑ :=
      eLpNorm_one_eq_lintegral_enorm ((hMgMeas n).sub hg.aestronglyMeasurable)
    rw [hnorm]
    calc Q n ≤ ∫⁻ x, ENNReal.ofReal B * ‖Mg n x - g x‖ₑ := by
          refine lintegral_mono fun x => ?_
          gcongr
          exact lps_enorm_le_of_abs_le (hηMfB n x)
      _ = _ := lintegral_const_mul'' _ ((hMgMeas n).sub hg.aestronglyMeasurable).enorm
  have hMgNorm (n : ℕ) : eLpNorm (fun x => Mg n x - g x) 1 volume ≤ 2 * ∫⁻ x, ‖g x‖ₑ := by
    calc _ ≤ eLpNorm (Mg n) 1 volume + eLpNorm g 1 volume :=
          eLpNorm_sub_le le_rfl
      _ ≤ eLpNorm g 1 volume + eLpNorm g 1 volume :=
          add_le_add (lps_eLpNorm_mollify_le le_rfl (by simp) hg.aestronglyMeasurable n) le_rfl
      _ = 2 * ∫⁻ x, ‖g x‖ₑ := by rw [← two_mul, hg1norm]
  refine ⟨fun n => ?_, ?_⟩
  · calc _ ≤ P n + Q n := hSplit n
      _ ≤ 2 * ENNReal.ofReal B * (∫⁻ x, ‖g x‖ₑ) +
          ENNReal.ofReal B * (2 * ∫⁻ x, ‖g x‖ₑ) :=
        add_le_add (hPbound n) ((hQbound n).trans (mul_le_mul' le_rfl (hMgNorm n)))
      _ = 4 * ENNReal.ofReal B * ∫⁻ x, ‖g x‖ₑ := by ring
  · -- convergence
    have hQlim : Tendsto Q atTop (𝓝 0) := by
      have hconv := lps_mollify_tendsto_norm (p := 1) le_rfl (by simp) hg1
      have hmul : Tendsto (fun n => ENNReal.ofReal B *
          eLpNorm (fun x => Mg n x - g x) 1 volume) atTop (𝓝 (ENNReal.ofReal B * 0)) :=
        ENNReal.Tendsto.const_mul hconv (Or.inr ENNReal.ofReal_ne_top)
      rw [mul_zero] at hmul
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul
        (fun _ => bot_le) hQbound
    have hPlim : Tendsto P atTop (𝓝 0) := by
      have hDCT : Tendsto P atTop (𝓝 (∫⁻ x : Vec3, (0 : ℝ≥0∞))) := by
        refine tendsto_lintegral_of_dominated_convergence'
          (fun x => (2 * ENNReal.ofReal B) * ‖g x‖ₑ) hPmeas ?_ ?_ ?_
        · intro n
          filter_upwards [hB] with x hx
          gcongr
          have h2 : |serrinCutoff n x * Mf n x - f x| ≤ 2 * B := by
            calc _ ≤ |serrinCutoff n x * Mf n x| + |f x| := abs_sub _ _
              _ ≤ B + B := add_le_add (hηMfB n x) hx
              _ = 2 * B := by ring
          calc ‖serrinCutoff n x * Mf n x - f x‖ₑ ≤ ENNReal.ofReal (2 * B) :=
                lps_enorm_le_of_abs_le h2
            _ = 2 * ENNReal.ofReal B := by
                rw [ENNReal.ofReal_mul (by norm_num)]; simp
        · rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)]
          exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hgfin
        · filter_upwards [lps_ae_tendsto_serrin_mollify hfLoc] with x hx
          have hη := serrinCutoff_tendsto_one x
          have hprod : Tendsto (fun n => serrinCutoff n x * Mf n x - f x) atTop (𝓝 0) := by
            have := (hη.mul hx).sub_const (f x)
            simpa using this
          have h0 := ENNReal.Tendsto.mul_const hprod.enorm (Or.inr (enorm_ne_top (x := g x)))
          simpa using h0
      simpa using hDCT
    have hsum := hPlim.add hQlim
    rw [add_zero] at hsum
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => bot_le) hSplit

/-- Fixed-time pairing limit for two square-integrable factors: the
cutoff-weighted product of mollifications converges in `L¹`, with the error
bounded by `6 ‖f‖₂ ‖g‖₂`. -/
theorem lps_endpoint_slice_pairing_l2_l2
    {f g : Vec3 → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    (∀ n : ℕ, ∫⁻ x : Vec3,
      ‖serrinCutoff n x * CKN.mollify f (serrinRadius n) (serrinRadius_pos n) x *
        CKN.mollify g (serrinRadius n) (serrinRadius_pos n) x - f x * g x‖ₑ ≤
        6 * (eLpNorm f 2 volume * eLpNorm g 2 volume)) ∧
    Tendsto (fun n : ℕ => ∫⁻ x : Vec3,
      ‖serrinCutoff n x * CKN.mollify f (serrinRadius n) (serrinRadius_pos n) x *
        CKN.mollify g (serrinRadius n) (serrinRadius_pos n) x - f x * g x‖ₑ)
      atTop (𝓝 0) := by
  set Mf : ℕ → Vec3 → ℝ := fun n => CKN.mollify f (serrinRadius n) (serrinRadius_pos n)
    with hMf
  set Mg : ℕ → Vec3 → ℝ := fun n => CKN.mollify g (serrinRadius n) (serrinRadius_pos n)
    with hMg
  have h2f : (2 : ℝ≥0∞) ≠ ⊤ := by simp
  have hfLoc : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  have hgLoc : LocallyIntegrable g volume := hg.locallyIntegrable (by norm_num)
  have hfm := hf.aestronglyMeasurable
  have hgm := hg.aestronglyMeasurable
  have hMfMeas (n : ℕ) : AEStronglyMeasurable (Mf n) volume := lps_mollify_aesm hfLoc n
  have hMgMeas (n : ℕ) : AEStronglyMeasurable (Mg n) volume := lps_mollify_aesm hgLoc n
  have hηMeas (n : ℕ) : AEStronglyMeasurable (serrinCutoff n) volume :=
    (serrinCutoff_contDiff n).continuous.aestronglyMeasurable
  let R : ℕ → ℝ≥0∞ := fun n => ∫⁻ x, ‖(serrinCutoff n x - 1) * (f x * g x)‖ₑ
  let A : ℕ → ℝ≥0∞ := fun n => eLpNorm (fun x => Mf n x - f x) 2 volume * eLpNorm g 2 volume
  let C : ℕ → ℝ≥0∞ := fun n => eLpNorm f 2 volume * eLpNorm (fun x => Mg n x - g x) 2 volume
  have hfg : ∫⁻ x, ‖f x * g x‖ₑ ≤ eLpNorm f 2 volume * eLpNorm g 2 volume := by
    simpa only [enorm_mul] using lps_lintegral_mul_le_two hfm hgm
  have hSplit (n : ℕ) : ∫⁻ x : Vec3,
      ‖serrinCutoff n x * Mf n x * Mg n x - f x * g x‖ₑ ≤ A n + C n + R n := by
    have hA : ∫⁻ x, ‖Mf n x - f x‖ₑ * ‖Mg n x‖ₑ ≤ A n := by
      refine (lps_lintegral_mul_le_two ((hMfMeas n).sub hfm) (hMgMeas n)).trans ?_
      exact mul_le_mul' le_rfl (lps_eLpNorm_mollify_le (by norm_num) h2f hgm n)
    have hC : ∫⁻ x, ‖f x‖ₑ * ‖Mg n x - g x‖ₑ ≤ C n :=
      lps_lintegral_mul_le_two hfm ((hMgMeas n).sub hgm)
    calc
      _ ≤ ∫⁻ x, ((‖Mf n x - f x‖ₑ * ‖Mg n x‖ₑ + ‖f x‖ₑ * ‖Mg n x - g x‖ₑ) +
          ‖(serrinCutoff n x - 1) * (f x * g x)‖ₑ) := by
        refine lintegral_mono fun x => ?_
        have hid : serrinCutoff n x * Mf n x * Mg n x - f x * g x =
            serrinCutoff n x * ((Mf n x - f x) * Mg n x + f x * (Mg n x - g x)) +
              (serrinCutoff n x - 1) * (f x * g x) := by ring
        rw [hid]
        have hη : ‖serrinCutoff n x‖ₑ ≤ 1 := by
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_one.mpr (serrinCutoff_abs_le_one n x)
        calc _ ≤ ‖serrinCutoff n x * ((Mf n x - f x) * Mg n x + f x * (Mg n x - g x))‖ₑ +
              ‖(serrinCutoff n x - 1) * (f x * g x)‖ₑ := enorm_add_le _ _
          _ ≤ (‖Mf n x - f x‖ₑ * ‖Mg n x‖ₑ + ‖f x‖ₑ * ‖Mg n x - g x‖ₑ) +
              ‖(serrinCutoff n x - 1) * (f x * g x)‖ₑ := by
            gcongr
            rw [enorm_mul]
            calc ‖serrinCutoff n x‖ₑ * ‖(Mf n x - f x) * Mg n x + f x * (Mg n x - g x)‖ₑ
                ≤ 1 * ‖(Mf n x - f x) * Mg n x + f x * (Mg n x - g x)‖ₑ := by gcongr
              _ ≤ _ := by
                rw [one_mul]
                calc _ ≤ ‖(Mf n x - f x) * Mg n x‖ₑ + ‖f x * (Mg n x - g x)‖ₑ :=
                      enorm_add_le _ _
                  _ = _ := by rw [enorm_mul, enorm_mul]
      _ = (∫⁻ x, ‖Mf n x - f x‖ₑ * ‖Mg n x‖ₑ) + (∫⁻ x, ‖f x‖ₑ * ‖Mg n x - g x‖ₑ) + R n := by
        have hX : AEMeasurable (fun x => ‖Mf n x - f x‖ₑ * ‖Mg n x‖ₑ) volume :=
          (((hMfMeas n).sub hfm).enorm).mul (hMgMeas n).enorm
        have hZ : AEMeasurable (fun x => ‖(serrinCutoff n x - 1) * (f x * g x)‖ₑ) volume :=
          (((hηMeas n).sub aestronglyMeasurable_const).mul (hfm.mul hgm)).enorm
        rw [lintegral_add_right' _ hZ, lintegral_add_left' hX]
      _ ≤ A n + C n + R n := by gcongr
  have hRlim : Tendsto R atTop (𝓝 0) := by
    have hDCT : Tendsto R atTop (𝓝 (∫⁻ x : Vec3, (0 : ℝ≥0∞))) := by
      refine tendsto_lintegral_of_dominated_convergence'
        (fun x => 2 * ‖f x * g x‖ₑ)
        (fun n => (((hηMeas n).sub aestronglyMeasurable_const).mul (hfm.mul hgm)).enorm)
        ?_ ?_ ?_
      · intro n
        filter_upwards [] with x
        rw [enorm_mul]
        gcongr
        have : |serrinCutoff n x - 1| ≤ 2 := by
          calc _ ≤ |serrinCutoff n x| + |(1 : ℝ)| := abs_sub _ _
            _ ≤ 1 + 1 := add_le_add (serrinCutoff_abs_le_one n x) (by norm_num)
            _ = 2 := by norm_num
        calc ‖serrinCutoff n x - 1‖ₑ ≤ ENNReal.ofReal 2 := lps_enorm_le_of_abs_le this
          _ = 2 := by simp
      · rw [lintegral_const_mul' _ _ (by simp)]
        exact ENNReal.mul_ne_top (by simp)
          ((hfg.trans_lt (ENNReal.mul_lt_top hf.eLpNorm_lt_top hg.eLpNorm_lt_top)).ne)
      · filter_upwards [] with x
        have hsub : Tendsto (fun n : ℕ => serrinCutoff n x - 1) atTop (𝓝 0) := by
          simpa using (serrinCutoff_tendsto_one x).sub_const 1
        simpa using (hsub.mul_const (f x * g x)).enorm
    simpa using hDCT
  refine ⟨fun n => ?_, ?_⟩
  · refine (hSplit n).trans ?_
    have hA : A n ≤ 2 * (eLpNorm f 2 volume * eLpNorm g 2 volume) := by
      have : eLpNorm (fun x => Mf n x - f x) 2 volume ≤ 2 * eLpNorm f 2 volume :=
        calc _ ≤ eLpNorm (Mf n) 2 volume + eLpNorm f 2 volume :=
              eLpNorm_sub_le (by norm_num)
          _ ≤ eLpNorm f 2 volume + eLpNorm f 2 volume :=
              add_le_add (lps_eLpNorm_mollify_le (by norm_num) h2f hfm n) le_rfl
          _ = 2 * eLpNorm f 2 volume := (two_mul _).symm
      calc A n ≤ (2 * eLpNorm f 2 volume) * eLpNorm g 2 volume := by
            unfold A; gcongr
        _ = _ := by ring
    have hC : C n ≤ 2 * (eLpNorm f 2 volume * eLpNorm g 2 volume) := by
      have : eLpNorm (fun x => Mg n x - g x) 2 volume ≤ 2 * eLpNorm g 2 volume :=
        calc _ ≤ eLpNorm (Mg n) 2 volume + eLpNorm g 2 volume :=
              eLpNorm_sub_le (by norm_num)
          _ ≤ eLpNorm g 2 volume + eLpNorm g 2 volume :=
              add_le_add (lps_eLpNorm_mollify_le (by norm_num) h2f hgm n) le_rfl
          _ = 2 * eLpNorm g 2 volume := (two_mul _).symm
      calc C n ≤ eLpNorm f 2 volume * (2 * eLpNorm g 2 volume) := by
            unfold C; gcongr
        _ = _ := by ring
    have hR : R n ≤ 2 * (eLpNorm f 2 volume * eLpNorm g 2 volume) := by
      calc R n ≤ ∫⁻ x, 2 * ‖f x * g x‖ₑ := by
            refine lintegral_mono fun x => ?_
            rw [enorm_mul]
            gcongr
            have : |serrinCutoff n x - 1| ≤ 2 := by
              calc _ ≤ |serrinCutoff n x| + |(1 : ℝ)| := abs_sub _ _
                _ ≤ 1 + 1 := add_le_add (serrinCutoff_abs_le_one n x) (by norm_num)
                _ = 2 := by norm_num
            calc ‖serrinCutoff n x - 1‖ₑ ≤ ENNReal.ofReal 2 := lps_enorm_le_of_abs_le this
              _ = 2 := by simp
        _ = 2 * ∫⁻ x, ‖f x * g x‖ₑ := lintegral_const_mul' _ _ (by simp)
        _ ≤ _ := by gcongr
    calc A n + C n + R n ≤ 2 * (eLpNorm f 2 volume * eLpNorm g 2 volume) +
          2 * (eLpNorm f 2 volume * eLpNorm g 2 volume) +
          2 * (eLpNorm f 2 volume * eLpNorm g 2 volume) := by gcongr
      _ = 6 * (eLpNorm f 2 volume * eLpNorm g 2 volume) := by ring
  · have hAlim : Tendsto A atTop (𝓝 0) := by
      have h' := ENNReal.Tendsto.mul_const (lps_mollify_tendsto_norm (p := 2) (by norm_num) h2f hf)
        (Or.inr hg.eLpNorm_lt_top.ne)
      simpa [A] using h'
    have hClim : Tendsto C atTop (𝓝 0) := by
      have h' := ENNReal.Tendsto.const_mul (lps_mollify_tendsto_norm (p := 2) (by norm_num) h2f hg)
        (Or.inr hf.eLpNorm_lt_top.ne)
      simpa [C] using h'
    have hsum := (hAlim.add hClim).add hRlim
    simp only [add_zero] at hsum
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => bot_le) hSplit

end ESS

end
