/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

public section

open MeasureTheory Set Filter
open scoped Interval


namespace ESS

/-- Integral Gronwall with an integrable, time dependent coefficient. -/
theorem serrin_integral_gronwall_zero
    {T C : ℝ} {b q : ℝ → ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hb : IntegrableOn b (Icc 0 T) volume)
    (hbNonneg : ∀ᵐ t ∂volume.restrict (Icc 0 T), 0 ≤ b t)
    (hqNonneg : ∀ᵐ t ∂volume.restrict (Icc 0 T), 0 ≤ q t)
    (hprod : Integrable (fun t => b t * q t)
      (volume.restrict (Icc 0 T)))
    (hprodNonneg : ∀ᵐ t ∂volume.restrict (Icc 0 T), 0 ≤ b t * q t)
    (hineq : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      q t ≤ C * ∫ s in (0)..t, b s * q s) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T), q t = 0 := by
  let f : ℝ → ℝ := (Icc 0 T).indicator (fun t => b t * q t)
  let g : ℝ → ℝ := (Icc 0 T).indicator b
  let F : ℝ → ℝ := fun t => ∫ s in (0)..t, f s
  let B : ℝ → ℝ := fun t => ∫ s in (0)..t, g s
  let E : ℝ → ℝ := fun t => Real.exp (-C * B t)
  let H : ℝ → ℝ := F * E
  have hf : Integrable f volume := by
    exact (integrable_indicator_iff measurableSet_Icc).2 hprod
  have hg : Integrable g volume := by
    exact (integrable_indicator_iff measurableSet_Icc).2 hb
  have hfint : IntervalIntegrable f volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
    exact hf.mono_measure Measure.restrict_le_self
  have hgint : IntervalIntegrable g volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
    exact hg.mono_measure Measure.restrict_le_self
  have hFac : AbsolutelyContinuousOnInterval F 0 T := by
    simpa [F] using hfint.absolutelyContinuousOnInterval_intervalIntegral
      (c := 0) (by simp)
  have hBac : AbsolutelyContinuousOnInterval B 0 T := by
    simpa [B] using hgint.absolutelyContinuousOnInterval_intervalIntegral
      (c := 0) (by simp)
  have hFcont : ContinuousOn F (Icc 0 T) := by
    rw [← uIcc_of_le hT]
    exact hFac.uniformContinuousOn.continuousOn
  have hBcont : ContinuousOn B (Icc 0 T) := by
    rw [← uIcc_of_le hT]
    exact hBac.uniformContinuousOn.continuousOn
  have hfderiv : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      HasDerivAt F (f t) t := by
    filter_upwards [hfint.ae_hasDerivAt_integral.filter_mono ae_restrict_le,
      ae_restrict_mem measurableSet_Icc] with t ht htm
    have htm' : t ∈ uIcc 0 T := by
      rw [uIcc_of_le hT]
      exact htm
    have h0 : (0 : ℝ) ∈ uIcc 0 T := by
      rw [uIcc_of_le hT]
      exact ⟨le_rfl, hT⟩
    exact ht htm' 0 h0
  have hBderiv : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      HasDerivAt B (g t) t := by
    filter_upwards [hgint.ae_hasDerivAt_integral.filter_mono ae_restrict_le,
      ae_restrict_mem measurableSet_Icc] with t ht htm
    have htm' : t ∈ uIcc 0 T := by
      rw [uIcc_of_le hT]
      exact htm
    have h0 : (0 : ℝ) ∈ uIcc 0 T := by
      rw [uIcc_of_le hT]
      exact ⟨le_rfl, hT⟩
    exact ht htm' 0 h0
  have hFnonneg : ∀ t ∈ Icc 0 T, 0 ≤ F t := by
    intro t ht
    have hsubset : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
    apply intervalIntegral.integral_nonneg_of_ae_restrict ht.1
    filter_upwards [(ae_mono (Measure.restrict_mono_set volume hsubset)) hprodNonneg,
      ae_restrict_mem measurableSet_Icc] with s hs hsmem
    have hst : s ∈ Icc 0 T := ⟨hsmem.1, le_trans hsmem.2 ht.2⟩
    simpa [f, hst] using hs
  have hBnonneg : ∀ t ∈ Icc 0 T, 0 ≤ B t := by
    intro t ht
    have hsubset : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
    apply intervalIntegral.integral_nonneg_of_ae_restrict ht.1
    filter_upwards [(ae_mono (Measure.restrict_mono_set volume hsubset)) hbNonneg,
      ae_restrict_mem measurableSet_Icc] with s hs hsmem
    have hst : s ∈ Icc 0 T := ⟨hsmem.1, le_trans hsmem.2 ht.2⟩
    simpa [g, hst] using hs
  have hBbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T, B t ≤ M := by
    have himage : IsCompact (B '' Icc 0 T) := isCompact_Icc.image_of_continuousOn hBcont
    obtain ⟨M, hM⟩ := himage.bddAbove
    refine ⟨M, ?_, ?_⟩
    · have hzero : B 0 ∈ B '' Icc 0 T := ⟨0, by simp [hT], rfl⟩
      have hMzero := hM hzero
      simpa [B] using hMzero
    · intro t ht
      exact hM ⟨t, ht, rfl⟩
  rcases hBbound with ⟨M, hMnonneg, hMbound⟩
  have hyac : AbsolutelyContinuousOnInterval (fun t => -C * B t) 0 T := by
    simpa [B] using hBac.const_mul (-C)
  have hymaps : MapsTo (fun t => -C * B t) (uIcc 0 T) (Icc (-C * M) 0) := by
    rw [uIcc_of_le hT]
    intro t ht
    constructor
    · have hmul : C * B t ≤ C * M := mul_le_mul_of_nonneg_left (hMbound t ht) hC
      nlinarith only [hmul]
    · have hmul : 0 ≤ C * B t := mul_nonneg hC (hBnonneg t ht)
      nlinarith only [hmul]
  have hexpOn : ContDiffOn ℝ 1 Real.exp (Icc (-C * M) 0) := by
    exact (Real.contDiff_exp (n := 1)).contDiffOn
  obtain ⟨K, hexpLip⟩ := hexpOn.exists_lipschitzOnWith
    (by norm_num) (convex_Icc _ _) isCompact_Icc
  have hEac : AbsolutelyContinuousOnInterval E 0 T := by
    change AbsolutelyContinuousOnInterval
      (Real.exp ∘ fun t => -C * B t) 0 T
    exact hexpLip.comp_absolutelyContinuousOnInterval hymaps hyac
  have hHac : AbsolutelyContinuousOnInterval H 0 T := by
    simpa [H] using hFac.mul hEac
  have hHderivNonpos : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      deriv H t ≤ 0 := by
    filter_upwards [hfderiv, hBderiv, hbNonneg, hqNonneg, hineq,
      ae_restrict_mem measurableSet_Icc] with t hFt hBt hbt hqt hineqt htm
    · have hft : f t = b t * q t := by simp [f, htm]
      have hgt : g t = b t := by simp [g, htm]
      have hFvalue : F t = ∫ s in (0)..t, b s * q s := by
        dsimp [F]
        apply intervalIntegral.integral_congr_ae_restrict
        filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
        · have hs' : s ∈ Icc 0 T := by
            have hs0 : s ∈ Ioc 0 t := by simpa [uIoc_of_le htm.1] using hs
            exact ⟨le_of_lt hs0.1, le_trans hs0.2 htm.2⟩
          simp [f, hs']
      have hqF : q t ≤ C * F t := by simpa [hFvalue] using hineqt
      have hyderiv : HasDerivAt (fun s => -C * B s) (-C * g t) t := by
        convert (hasDerivAt_const t (-C)).mul hBt using 1
        ring
      have hEderiv : HasDerivAt E (E t * (-C * g t)) t := by
        have h := (Real.hasDerivAt_exp (-C * B t)).comp t hyderiv
        simpa [Function.comp_def, E, neg_mul] using h
      have hEpos : 0 < E t := by
        change 0 < Real.exp (-C * B t)
        exact Real.exp_pos _
      have hbf : b t * q t * E t ≤ (C * F t) * b t * E t := by
        calc
          b t * q t * E t ≤ (b t * (C * F t)) * E t :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hqF hbt) hEpos.le
          _ = (C * F t) * b t * E t := by ring
      have hderivValue : deriv H t =
          b t * q t * E t - (C * F t) * b t * E t := by
        change deriv (F * E) t = _
        calc
          deriv (F * E) t = f t * E t + F t * (E t * (-C * g t)) :=
            (hFt.mul hEderiv).deriv
          _ = b t * q t * E t - (C * F t) * b t * E t := by
            rw [hft, hgt]
            ring
      rw [hderivValue]
      exact sub_nonpos.mpr (by simpa [mul_assoc, mul_left_comm, mul_comm] using hbf)
  have hHzero : ∀ t ∈ Icc 0 T, H t = 0 := by
    intro t ht
    have hsub : uIcc 0 t ⊆ uIcc 0 T := by
      rw [uIcc_of_le ht.1, uIcc_of_le hT]
      exact Icc_subset_Icc le_rfl ht.2
    have hHac' : AbsolutelyContinuousOnInterval H 0 t := hHac.mono hsub
    have hpart : ∫ s in (0)..t, deriv H s ≤ 0 := by
      have hsmall : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
      have hneg : 0 ≤ ∫ s in (0)..t, -deriv H s := by
        apply intervalIntegral.integral_nonneg_of_ae_restrict ht.1
        filter_upwards [(ae_mono (Measure.restrict_mono_set volume hsmall)) hHderivNonpos]
          with s hs
        exact neg_nonneg.mpr hs
      have hneg' : 0 ≤ -(∫ s in (0)..t, deriv H s) := by
        simpa only [intervalIntegral.integral_neg] using hneg
      linarith only [hneg']
    have hFTC' : (∫ s in (0)..t, deriv H s) = H t - H 0 := by
      exact hHac'.integral_deriv_eq_sub
    have hH0 : H 0 = 0 := by simp [H, F, E]
    have hHle : H t ≤ 0 := by
      have hsuble : H t - H 0 ≤ 0 := by
        calc
          H t - H 0 = ∫ s in (0)..t, deriv H s := hFTC'.symm
          _ ≤ 0 := hpart
      simpa [hH0] using hsuble
    have hHnonneg : 0 ≤ H t := by
      simp only [H, Pi.mul_apply]
      have hEpos : 0 < E t := by
        change 0 < Real.exp (-C * B t)
        exact Real.exp_pos _
      exact mul_nonneg (hFnonneg t ht) hEpos.le
    exact le_antisymm hHle hHnonneg
  have hFzero : ∀ t ∈ Icc 0 T, F t = 0 := by
    intro t ht
    have hEpos : 0 < E t := by
      change 0 < Real.exp (-C * B t)
      exact Real.exp_pos _
    have h := hHzero t ht
    simpa [H] using (mul_eq_zero.mp h).resolve_right hEpos.ne'
  filter_upwards [hineq, hqNonneg, ae_restrict_mem measurableSet_Icc]
    with t hineqt hqt ht
  · have hFvalue : F t = ∫ s in (0)..t, b s * q s := by
      dsimp [F]
      apply intervalIntegral.integral_congr_ae_restrict
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
      · have hs' : s ∈ Ioc 0 t := by simpa [uIoc_of_le ht.1] using hs
        have hsT : s ∈ Icc 0 T := ⟨le_of_lt hs'.1, le_trans hs'.2 ht.2⟩
        simp [f, hsT]
    have hqle : q t ≤ 0 := by
      rw [← hFvalue, hFzero t ht] at hineqt
      simpa using hineqt
    exact le_antisymm hqle hqt

end ESS
