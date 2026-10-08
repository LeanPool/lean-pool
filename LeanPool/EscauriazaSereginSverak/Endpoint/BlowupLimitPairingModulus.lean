/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessMain

/-!
# Time moduli from a space-time flux bound

A uniform local `L^(3/2)` bound for the scalar flux in a smooth-test pairing
gives the endpoint-compatible power modulus used in `lem:compactness` of the CKN manuscript.
-/

public section

open CKN


open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- A spacetime `L^(3/2)` flux bound controls its time-integrated pairing on
every subrectangle, with the interval length appearing in the modulus. -/
theorem blowup_limit_interval_pairing_modulus_of_spacetime_flux
    {C : Set Vec3} (hC : IsCompact C)
    (a b M : ℝ) (hM : 0 ≤ M)
    (F : ℕ → ParabolicPoint → ℝ) (G : ℕ → ℝ → ℝ)
    (hF : ∀ n,
      MemLp (F n) (3 / 2 : ℝ≥0∞)
        (volume.restrict (C ×ˢ Icc a b)) ∧
      eLpNorm (F n) (3 / 2 : ℝ≥0∞)
        (volume.restrict (C ×ˢ Icc a b)) ≤ ENNReal.ofReal M)
    (hformula : ∀ n s t, s ∈ Icc a b → t ∈ Icc a b → s ≤ t →
      G n t - G n s = ∫ z in C ×ˢ Ioc s t, F n z) :
    ∀ n s t, s ∈ Icc a b → t ∈ Icc a b →
      |G n t - G n s| ≤ M *
        ((volume C).toReal * dist t s) ^ (1 / 3 : ℝ) := by
  intro n s t hs ht
  by_cases hst : s ≤ t
  · rw [hformula n s t hs ht hst]
    let μ : Measure ParabolicPoint := volume.restrict (C ×ˢ Ioc s t)
    have hsub : C ×ˢ Ioc s t ⊆ C ×ˢ Icc a b := by
      intro z hz
      exact ⟨hz.1, le_trans hs.1 (le_of_lt hz.2.1), le_trans hz.2.2 ht.2⟩
    have hf : MemLp (F n) (3 / 2 : ℝ≥0∞) μ :=
      (hF n).1.mono_measure (Measure.restrict_mono_set volume hsub)
    have hbound : eLpNorm (F n) (3 / 2 : ℝ≥0∞) μ ≤ ENNReal.ofReal M :=
      (eLpNorm_mono_measure (F n)
        (Measure.restrict_mono_set volume hsub)).trans (hF n).2
    have hlow : (1 : ℝ≥0∞) ≤ (3 / 2 : ℝ≥0∞) := by
      rw [← CKN.ofReal_threeHalves]
      exact ENNReal.one_le_ofReal.mpr (by norm_num)
    have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos
      (μ := μ) (f := F n) (p := (1 : ℝ≥0∞))
      (q := (3 / 2 : ℝ≥0∞)) hlow (by norm_num)
    have hmass : μ Set.univ = volume C * ENNReal.ofReal (t - s) := by
      change (volume.restrict (C ×ˢ Ioc s t)) Set.univ = _
      rw [Measure.restrict_apply_univ, Measure.volume_eq_prod Vec3 ℝ,
        Measure.prod_prod]
      rw [Real.volume_Ioc]
    let : IsFiniteMeasure μ := by
      refine ⟨?_⟩
      rw [hmass]
      exact ENNReal.mul_lt_top hC.measure_lt_top ENNReal.ofReal_lt_top
    have hL1 : MemLp (F n) (1 : ℝ≥0∞) μ := hf.mono_exponent hlow
    have hcompare' : eLpNorm (F n) 1 μ ≤
        ENNReal.ofReal M *
          (volume C * ENNReal.ofReal (t - s)) ^ (1 / 3 : ℝ) := by
      calc
        eLpNorm (F n) 1 μ ≤
            eLpNorm (F n) (3 / 2 : ℝ≥0∞) μ * μ Set.univ ^ (1 / 3 : ℝ) := by
          convert hcompare using 1
          norm_num
        _ ≤ ENNReal.ofReal M *
            (volume C * ENNReal.ofReal (t - s)) ^ (1 / 3 : ℝ) := by
          rw [hmass]
          gcongr
    have hnorm : ‖∫ z, F n z ∂μ‖ ≤ ∫ z, ‖F n z‖ ∂μ :=
      norm_integral_le_integral_norm (F n)
    have hnorm' : ENNReal.ofReal (|∫ z, F n z ∂μ|) ≤ eLpNorm (F n) 1 μ := by
      rw [hL1.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top]
      simpa only [ENNReal.toReal_one, one_div, inv_one, Real.rpow_one,
        Real.norm_eq_abs] using ENNReal.ofReal_le_ofReal hnorm
    have hVtop : volume C < ⊤ := hC.measure_lt_top
    let V : ℝ := (volume C).toReal
    have hV : volume C = ENNReal.ofReal V := by
      dsimp [V]
      exact (ENNReal.ofReal_toReal hVtop.ne).symm
    have hts : 0 ≤ t - s := sub_nonneg.mpr hst
    have hVnonneg : 0 ≤ V := ENNReal.toReal_nonneg
    have hdist : dist t s = t - s := by
      rw [Real.dist_eq, abs_of_nonneg hts]
    have hpow : (ENNReal.ofReal (V * (t - s))) ^ (1 / 3 : ℝ) =
        ENNReal.ofReal ((V * (t - s)) ^ (1 / 3 : ℝ)) :=
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hVnonneg hts) (by norm_num)
    have hproduct : ENNReal.ofReal M *
        (volume C * ENNReal.ofReal (t - s)) ^ (1 / 3 : ℝ) =
        ENNReal.ofReal (M * (V * (t - s)) ^ (1 / 3 : ℝ)) := by
      calc
        _ = ENNReal.ofReal M *
            (ENNReal.ofReal (V * (t - s))) ^ (1 / 3 : ℝ) := by
          rw [hV, ← ENNReal.ofReal_mul hVnonneg]
        _ = ENNReal.ofReal M *
            ENNReal.ofReal ((V * (t - s)) ^ (1 / 3 : ℝ)) := by rw [hpow]
        _ = _ := (ENNReal.ofReal_mul hM).symm
    have hreal : |∫ z, F n z ∂μ| ≤
        M * (V * (t - s)) ^ (1 / 3 : ℝ) := by
      have hle := hnorm'.trans hcompare'
      rw [hproduct] at hle
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
    have hformula' : ∫ z in C ×ˢ Ioc s t, F n z = ∫ z, F n z ∂μ := rfl
    rw [hformula', hdist]
    exact hreal
  · have hts : t ≤ s := le_of_not_ge hst
    have hrev := hformula n t s ht hs hts
    have hsub : C ×ˢ Ioc t s ⊆ C ×ˢ Icc a b := by
      intro z hz
      exact ⟨hz.1, le_trans ht.1 (le_of_lt hz.2.1), le_trans hz.2.2 hs.2⟩
    let μ : Measure ParabolicPoint := volume.restrict (C ×ˢ Ioc t s)
    have hf : MemLp (F n) (3 / 2 : ℝ≥0∞) μ :=
      (hF n).1.mono_measure (Measure.restrict_mono_set volume hsub)
    have hbound : eLpNorm (F n) (3 / 2 : ℝ≥0∞) μ ≤ ENNReal.ofReal M :=
      (eLpNorm_mono_measure (F n)
        (Measure.restrict_mono_set volume hsub)).trans (hF n).2
    have hlow : (1 : ℝ≥0∞) ≤ (3 / 2 : ℝ≥0∞) := by
      rw [← CKN.ofReal_threeHalves]
      exact ENNReal.one_le_ofReal.mpr (by norm_num)
    have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos
      (μ := μ) (f := F n) (p := (1 : ℝ≥0∞))
      (q := (3 / 2 : ℝ≥0∞)) hlow (by norm_num)
    have hmass : μ Set.univ = volume C * ENNReal.ofReal (s - t) := by
      change (volume.restrict (C ×ˢ Ioc t s)) Set.univ = _
      rw [Measure.restrict_apply_univ, Measure.volume_eq_prod Vec3 ℝ,
        Measure.prod_prod]
      rw [Real.volume_Ioc]
    let : IsFiniteMeasure μ := by
      refine ⟨?_⟩
      rw [hmass]
      exact ENNReal.mul_lt_top hC.measure_lt_top ENNReal.ofReal_lt_top
    have hL1 : MemLp (F n) (1 : ℝ≥0∞) μ := hf.mono_exponent hlow
    have hcompare' : eLpNorm (F n) 1 μ ≤
        ENNReal.ofReal M *
          (volume C * ENNReal.ofReal (s - t)) ^ (1 / 3 : ℝ) := by
      calc
        eLpNorm (F n) 1 μ ≤
            eLpNorm (F n) (3 / 2 : ℝ≥0∞) μ * μ Set.univ ^ (1 / 3 : ℝ) := by
          convert hcompare using 1
          norm_num
        _ ≤ ENNReal.ofReal M *
            (volume C * ENNReal.ofReal (s - t)) ^ (1 / 3 : ℝ) := by
          rw [hmass]
          gcongr
    have hnorm : ‖∫ z, F n z ∂μ‖ ≤ ∫ z, ‖F n z‖ ∂μ :=
      norm_integral_le_integral_norm (F n)
    have hnorm' : ENNReal.ofReal (|∫ z, F n z ∂μ|) ≤ eLpNorm (F n) 1 μ := by
      rw [hL1.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top]
      simpa only [ENNReal.toReal_one, one_div, inv_one, Real.rpow_one,
        Real.norm_eq_abs] using ENNReal.ofReal_le_ofReal hnorm
    have hVtop : volume C < ⊤ := hC.measure_lt_top
    let V : ℝ := (volume C).toReal
    have hV : volume C = ENNReal.ofReal V := by
      dsimp [V]
      exact (ENNReal.ofReal_toReal hVtop.ne).symm
    have hst' : 0 ≤ s - t := sub_nonneg.mpr hts
    have hVnonneg : 0 ≤ V := ENNReal.toReal_nonneg
    have hdist : dist t s = s - t := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hts)]
      ring
    have hpow : (ENNReal.ofReal (V * (s - t))) ^ (1 / 3 : ℝ) =
        ENNReal.ofReal ((V * (s - t)) ^ (1 / 3 : ℝ)) :=
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hVnonneg hst') (by norm_num)
    have hproduct : ENNReal.ofReal M *
        (volume C * ENNReal.ofReal (s - t)) ^ (1 / 3 : ℝ) =
        ENNReal.ofReal (M * (V * (s - t)) ^ (1 / 3 : ℝ)) := by
      calc
        _ = ENNReal.ofReal M *
            (ENNReal.ofReal (V * (s - t))) ^ (1 / 3 : ℝ) := by
          rw [hV, ← ENNReal.ofReal_mul hVnonneg]
        _ = ENNReal.ofReal M *
            ENNReal.ofReal ((V * (s - t)) ^ (1 / 3 : ℝ)) := by rw [hpow]
        _ = _ := (ENNReal.ofReal_mul hM).symm
    have hreal : |∫ z, F n z ∂μ| ≤
        M * (V * (s - t)) ^ (1 / 3 : ℝ) := by
      have hle := hnorm'.trans hcompare'
      rw [hproduct] at hle
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
    have hneg : G n t - G n s = -(G n s - G n t) := by ring
    rw [hneg, abs_neg, hrev]
    have hformula' : ∫ z in C ×ˢ Ioc t s, F n z = ∫ z, F n z ∂μ := rfl
    rw [hformula', hdist]
    exact hreal

end ESS

end
