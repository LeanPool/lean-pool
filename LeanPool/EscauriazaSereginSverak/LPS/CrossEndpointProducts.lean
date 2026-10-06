/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.CrossEndpointPairing
public import LeanPool.EscauriazaSereginSverak.LPS.MixedNormProductMoment

/-!
# Endpoint mixed norms of convection products

Products of an `L∞_t L²_x` factor or an `L²_t L∞_x` factor with a space-time
`L²` gradient factor lie in `L²_t L¹_x` or `L¹_t L²_x` respectively
(`lem:lps-comparison`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A square-integrable function with bounded squared integral has bounded
`L²` seminorm. -/
theorem lps_eLpNorm_two_le_sqrt {f : Vec3 → ℝ} {C : ℝ} (hf : MemLp f 2 volume)
    (hC : ∫ x : Vec3, f x ^ 2 ≤ C) :
    eLpNorm f 2 volume ≤ ENNReal.ofReal (Real.sqrt C) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have hI : (∫ x : Vec3, ‖f x‖ ^ (2 : ℝ)) ≤ C := by
    refine le_trans (le_of_eq ?_) hC
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [sq_abs]
  rw [h2, Real.sqrt_eq_rpow]
  simp only [one_div]
  exact Real.rpow_le_rpow (integral_nonneg fun x : Vec3 =>
    Real.rpow_nonneg (norm_nonneg (f x)) _) hI (by norm_num)

/-- The slice `L²` norm of a slab-measurable function is measurable in time. -/
theorem lps_slice_eLpNorm_two_aemeasurable {T : ℝ} {B : ParabolicPoint → ℝ}
    (hB : AEStronglyMeasurable B
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    AEMeasurable (fun t : ℝ => eLpNorm (fun x : Vec3 => B (x,t)) 2 volume)
      (volume.restrict (Ioo 0 T)) := by
  have hpow : AEMeasurable (fun z : Vec3 × ℝ => ‖B z‖ₑ ^ (2 : ℝ))
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) :=
    (serrin_aesm_prod hB).enorm.pow_const _
  have hlin := hpow.lintegral_prod_left'
  have hroot := hlin.pow_const (1 / (2 : ℝ))
  refine hroot.congr ?_
  filter_upwards [lps_slice_aesm hB] with t ht
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) ht]
  norm_num

/-- An `L∞_t L²_x` factor times a space-time `L²` factor lies in `L²_t L¹_x`. -/
theorem lps_endpoint_product_l2_l1 {T : ℝ} {A B : ParabolicPoint → ℝ} {K : ℝ≥0∞}
    (hB : MemLp B 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hASlice : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => A (x,τ)) 2 volume)
    (hK : K ≠ ⊤)
    (hAK : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      eLpNorm (fun x : Vec3 => A (x,τ)) 2 volume ≤ K) :
    (∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => A (x,τ) * B (x,τ)) (ENNReal.ofReal 1) volume) ∧
    (∫⁻ τ in Ioo 0 T,
      eLpNorm (fun x : Vec3 => A (x,τ) * B (x,τ)) (ENNReal.ofReal 1) volume ^ (2 : ℝ)) < ⊤ := by
  obtain ⟨hBslice, hBmom⟩ := lps_mixed_two_moment_of_memLp_two hB
  have hkey : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => A (x,τ) * B (x,τ)) (ENNReal.ofReal 1) volume ∧
      eLpNorm (fun x : Vec3 => A (x,τ) * B (x,τ)) (ENNReal.ofReal 1) volume ≤
        K * eLpNorm (fun x : Vec3 => B (x,τ)) 2 volume := by
    filter_upwards [hASlice, hBslice, hAK] with τ hA hBτ hKτ
    have : ENNReal.HolderTriple 2 2 1 := ⟨by simp [ENNReal.inv_two_add_inv_two]⟩
    have hmem : MemLp (fun x : Vec3 => A (x,τ) * B (x,τ)) 1 volume :=
      hA.mul (r := 1) hBτ
    have hmem' : MemLp (fun x : Vec3 => A (x,τ) * B (x,τ)) (ENNReal.ofReal 1) volume := by
      simpa using hmem
    refine ⟨hmem', ?_⟩
    have hnorm : eLpNorm (fun x : Vec3 => A (x,τ) * B (x,τ)) (ENNReal.ofReal 1) volume =
        ∫⁻ x : Vec3, ‖A (x,τ)‖ₑ * ‖B (x,τ)‖ₑ := by
      rw [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm hmem.aestronglyMeasurable]
      simp [enorm_mul]
    rw [hnorm]
    calc _ ≤ eLpNorm (fun x : Vec3 => A (x,τ)) 2 volume *
          eLpNorm (fun x : Vec3 => B (x,τ)) 2 volume :=
          lps_lintegral_mul_le_two hA.aestronglyMeasurable hBτ.aestronglyMeasurable
      _ ≤ _ := by gcongr
  refine ⟨by filter_upwards [hkey] with τ h using h.1, ?_⟩
  have hKpow : K ^ (2 : ℝ) < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num) hK
  calc (∫⁻ τ in Ioo 0 T,
      eLpNorm (fun x : Vec3 => A (x,τ) * B (x,τ)) (ENNReal.ofReal 1) volume ^ (2 : ℝ))
      ≤ ∫⁻ τ in Ioo 0 T, K ^ (2 : ℝ) *
          eLpNorm (fun x : Vec3 => B (x,τ)) 2 volume ^ (2 : ℝ) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hkey] with τ h
        rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        exact ENNReal.rpow_le_rpow h.2 (by norm_num)
    _ = K ^ (2 : ℝ) * ∫⁻ τ in Ioo 0 T,
          eLpNorm (fun x : Vec3 => B (x,τ)) 2 volume ^ (2 : ℝ) :=
        lintegral_const_mul' _ _ hKpow.ne
    _ < ⊤ := ENNReal.mul_lt_top hKpow hBmom

/-- An `L²_t L∞_x` factor times a space-time `L²` factor lies in `L¹_t L²_x`. -/
theorem lps_endpoint_product_linf_l2 {T : ℝ} {A B : ParabolicPoint → ℝ} {β : ℝ → ℝ}
    (hA : AEStronglyMeasurable A
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hB : MemLp B 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hβmeas : AEMeasurable (fun τ => ENNReal.ofReal (β τ)) (volume.restrict (Ioo 0 T)))
    (hβ : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      ∀ᵐ x ∂(volume : Measure Vec3), |A (x, τ)| ≤ β τ)
    (hβint : (∫⁻ τ in Ioo 0 T, ENNReal.ofReal (β τ) ^ (2 : ℝ)) < ⊤) :
    (∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => A (x,τ) * B (x,τ)) (ENNReal.ofReal 2) volume) ∧
    (∫⁻ τ in Ioo 0 T,
      eLpNorm (fun x : Vec3 => A (x,τ) * B (x,τ)) (ENNReal.ofReal 2) volume ^ (1 : ℝ)) < ⊤ := by
  obtain ⟨hBslice, hBmom⟩ := lps_mixed_two_moment_of_memLp_two hB
  have hkey : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => A (x,τ) * B (x,τ)) (ENNReal.ofReal 2) volume ∧
      eLpNorm (fun x : Vec3 => A (x,τ) * B (x,τ)) (ENNReal.ofReal 2) volume ≤
        ENNReal.ofReal (β τ) * eLpNorm (fun x : Vec3 => B (x,τ)) 2 volume := by
    filter_upwards [hβ, hBslice, lps_slice_aesm hA] with τ hβτ hBτ hAτ
    have hβ0 : 0 ≤ β τ := by
      obtain ⟨x, hx⟩ := hβτ.exists
      exact (abs_nonneg _).trans hx
    have hbound : ∀ᵐ x ∂(volume : Measure Vec3),
        ‖A (x,τ) * B (x,τ)‖ ≤ ‖(β τ) • B (x,τ)‖ := by
      filter_upwards [hβτ] with x hx
      simp only [norm_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ0]
      exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    have hmem : MemLp (fun x : Vec3 => A (x,τ) * B (x,τ)) 2 volume :=
      (hBτ.const_smul (β τ)).mono (hAτ.mul hBτ.aestronglyMeasurable) hbound
    refine ⟨by simpa using hmem, ?_⟩
    have hle : eLpNorm (fun x : Vec3 => A (x,τ) * B (x,τ)) 2 volume ≤
        eLpNorm ((β τ) • (fun x : Vec3 => B (x,τ))) 2 volume :=
      eLpNorm_mono_ae (hAτ.mul hBτ.aestronglyMeasurable) hbound
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hβ0] at hle
    simpa using hle
  refine ⟨by filter_upwards [hkey] with τ h using h.1, ?_⟩
  simp only [ENNReal.rpow_one]
  have hprod := lps_lintegral_mul_ne_top_of_sq hβmeas
    (lps_slice_eLpNorm_two_aemeasurable hB.aestronglyMeasurable) hβint hBmom
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) hprod.lt_top
  filter_upwards [hkey] with τ h
  exact h.2

end ESS

end
