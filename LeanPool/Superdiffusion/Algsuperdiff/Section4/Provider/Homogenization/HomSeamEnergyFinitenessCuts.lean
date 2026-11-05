/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamEnergySlotAssembly

/-!
# HomSeamEnergyFinitenessCuts

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The three finiteness cuts of the enlarged-`Y` top-scale item

## What this file supplies

`HomSeamEnergySlotAssembly.htop_seamEnlargedY` carries three a.e. cuts — the
`𝓔`-suprema at the honest Step-2 indices `t/2 = 1/8`, `t = 1/4` and at the
printed `1/4` are not `⊤`.  They are DISCHARGED here off branches 2, 4 and 5 of
`HomStepOneSeamAnchor.exists_ethmB_seam_factor_moments`, read at the boosted
exponent `q = 64 d |log γ|`, under the same `γ`-gate the seam display
uses.

Nothing analytic is added: a finite `q`-moment of a `[0,∞]`-valued observable
makes the observable finite almost surely.
-/

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

/-! ## 1. A finite moment kills the value `⊤` -/

/-- A finite `q`-moment at a positive exponent makes a `[0,∞]`-valued observable
almost surely finite. -/
theorem ae_ne_top_of_rpow_moment {d : ℕ} (M : ABKModel d)
    {F : Cutoff.CutoffSample d → ℝ≥0∞} (hF : Measurable F) {q c : ℝ} (hq : 0 < q)
    (hmom : (∫⁻ omega, F omega ^ q ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal c ^ q) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure, F omega ≠ ⊤ := by
  have hne : (∫⁻ omega, F omega ^ q ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top) hmom
  have hmeas : AEMeasurable (fun omega => F omega ^ q)
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    ((ENNReal.continuous_rpow_const (y := q)).measurable.comp hF).aemeasurable
  refine (ae_lt_top' hmeas hne).mono fun omega homega htop => ?_
  rw [htop, ENNReal.top_rpow_of_pos hq] at homega
  exact absurd homega (lt_irrefl _)

/-! ## 2. THE THREE CUTS -/

/-- **THE THREE `𝓔`-FINITENESS CUTS OF THE ENLARGED `Y`, DISCHARGED.**

At every model below one explicit threshold and at every scale, the two honest
Step-2 error indices `1/8`, `1/4` and the printed index `1/4` have almost surely
finite `sup_{L ≥ m}` observables.  These are exactly the three `≠ ⊤` hypotheses
of `HomSeamEnergySlotAssembly.htop_seamEnlargedY`. -/
theorem ae_seam_quarter_errors_ne_top (d : ℕ) [NeZero d] (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        0 < homS M → ∀ m : ℤ,
          ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            fluxCorrectedTwoScaleErrorObservableSup M m m
                ⟨1 / 4 / 2, half_pos seamQuarterPos⟩ omega ≠ ⊤ ∧
              fluxCorrectedTwoScaleErrorObservableSup M m m ⟨1 / 4, seamQuarterPos⟩
                  omega ≠ ⊤ ∧
              fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega ≠ ⊤ := by
  obtain ⟨g0, A, hg0, hA1, hanchor⟩ := exists_ethmB_seam_factor_moments d cstar hcstar
  have hApos : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA1
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hd1R : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hprod : (0 : ℝ) ≤ 1024 * (d : ℝ) * A :=
    mul_nonneg (mul_nonneg (by norm_num) hd0) hApos.le
  have hxpos : (0 : ℝ) < 1 + 1024 * (d : ℝ) * A := by linarith only [hprod]
  have hbmin : (0 : ℝ) < min ((1 + 1024 * (d : ℝ) * A)⁻¹) (1 / 16) :=
    lt_min (inv_pos.mpr hxpos) (by norm_num)
  refine ⟨min g0 (min ((1 + 1024 * (d : ℝ) * A)⁻¹) (1 / 16) ^ (4 : ℕ)),
    lt_min hg0 (pow_pos hbmin 4), ?_⟩
  intro M hcs hgamma hs m
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hg_g0 : M.gamma ≤ g0 := le_trans hgamma (min_le_left _ _)
  have hg_b : M.gamma ≤ min ((1 + 1024 * (d : ℝ) * A)⁻¹) (1 / 16) ^ (4 : ℕ) :=
    le_trans hgamma (min_le_right _ _)
  have ht : Real.sqrt (Real.sqrt M.gamma) ≤ min ((1 + 1024 * (d : ℝ) * A)⁻¹) (1 / 16) :=
    quarticRoot_le hgpos.le hbmin.le hg_b
  have htpos : 0 < Real.sqrt (Real.sqrt M.gamma) := quarticRoot_pos hgpos
  have ht4 : Real.sqrt (Real.sqrt M.gamma) ^ (4 : ℕ) = M.gamma :=
    quarticRoot_pow_four hgpos.le
  have ht16 : Real.sqrt (Real.sqrt M.gamma) ≤ 1 / 16 := le_trans ht (min_le_right _ _)
  have htA : Real.sqrt (Real.sqrt M.gamma) ≤ (1 + 1024 * (d : ℝ) * A)⁻¹ :=
    le_trans ht (min_le_left _ _)
  have hgsmall : M.gamma ≤ 1 / 65536 := by
    rw [← ht4]
    calc Real.sqrt (Real.sqrt M.gamma) ^ (4 : ℕ) ≤ (1 / 16 : ℝ) ^ (4 : ℕ) :=
          pow_le_pow_left₀ htpos.le ht16 4
      _ = 1 / 65536 := by norm_num
  have hg1 : M.gamma < 1 := by linarith only [hgsmall]
  have hL4 : 4 ≤ |Real.log M.gamma| := four_le_absLog hgpos (by linarith only [hgsmall])
  have hLpos : (0 : ℝ) < |Real.log M.gamma| := by linarith only [hL4]
  have hs4 : homS M ≤ 1 / 4 := homS_le_quarter hL4
  have hLu : |Real.log M.gamma| ≤ 4 * (Real.sqrt (Real.sqrt M.gamma))⁻¹ :=
    absLog_le_four_div_quarticRoot hgpos hg1
  have hAL : (0 : ℝ) < A * |Real.log M.gamma| := mul_pos hApos hLpos
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hgne : M.gamma ≠ 0 := ne_of_gt hgpos
  have hLne : |Real.log M.gamma| ≠ 0 := ne_of_gt hLpos
  have heqdiv : A⁻¹ * M.gamma⁻¹ * homS M = M.gamma⁻¹ / (A * |Real.log M.gamma|) := by
    rw [homS]; field_simp
  /- the boosted exponent sits inside the anchor's own admissible ran -/
  have hup2 : 64 * (d : ℝ) * |Real.log M.gamma| ≤ A⁻¹ * M.gamma⁻¹ * homS M := by
    rw [heqdiv, le_div_iff₀ hAL]
    set u : ℝ := (Real.sqrt (Real.sqrt M.gamma))⁻¹ with hudef
    have hupos : (0 : ℝ) < u := inv_pos.mpr htpos
    have hu1 : 1 + 1024 * (d : ℝ) * A ≤ u := by
      have hmul : (1 + 1024 * (d : ℝ) * A) * Real.sqrt (Real.sqrt M.gamma) ≤ 1 := by
        have h := mul_le_mul_of_nonneg_left htA hxpos.le
        rwa [mul_inv_cancel₀ (ne_of_gt hxpos)] at h
      have hdiv : (1 + 1024 * (d : ℝ) * A) ≤ 1 / Real.sqrt (Real.sqrt M.gamma) :=
        (le_div_iff₀ htpos).mpr hmul
      rwa [one_div] at hdiv
    have hu4 : M.gamma⁻¹ = u ^ (4 : ℕ) := by rw [hudef, inv_pow, ht4]
    have hstep1 : 64 * (d : ℝ) * |Real.log M.gamma| * (A * |Real.log M.gamma|) ≤
        1024 * (d : ℝ) * A * (u * u) := by
      have hu40 : (0 : ℝ) ≤ 4 * u := by linarith only [hupos]
      have hLL : |Real.log M.gamma| * |Real.log M.gamma| ≤ (4 * u) * (4 * u) :=
        mul_le_mul hLu hLu hLpos.le hu40
      have hfacnn : (0 : ℝ) ≤ 64 * (d : ℝ) * A :=
        mul_nonneg (mul_nonneg (by norm_num) hd0) hApos.le
      have hmul := mul_le_mul_of_nonneg_left hLL hfacnn
      calc 64 * (d : ℝ) * |Real.log M.gamma| * (A * |Real.log M.gamma|)
          = 64 * (d : ℝ) * A * (|Real.log M.gamma| * |Real.log M.gamma|) := by ring
        _ ≤ 64 * (d : ℝ) * A * ((4 * u) * (4 * u)) := hmul
        _ = 1024 * (d : ℝ) * A * (u * u) := by ring
    have hu1' : (1 : ℝ) ≤ u := by linarith only [hu1, hprod]
    have hsq : 1024 * (d : ℝ) * A ≤ u * u := by
      have h1 : u ≤ u * u := le_mul_of_one_le_left hupos.le hu1'
      linarith only [hu1, h1]
    have hstep2 : 1024 * (d : ℝ) * A * (u * u) ≤ u ^ (4 : ℕ) := by
      have hnn : (0 : ℝ) ≤ u * u := mul_nonneg hupos.le hupos.le
      have h := mul_le_mul_of_nonneg_right hsq hnn
      calc 1024 * (d : ℝ) * A * (u * u) ≤ (u * u) * (u * u) := h
        _ = u ^ (4 : ℕ) := by ring
    rw [hu4]
    linarith only [hstep1, hstep2]
  have hq0 : (0 : ℝ) < 64 * (d : ℝ) * |Real.log M.gamma| := by
    have h64 : (0 : ℝ) < 64 * (d : ℝ) := by linarith only [hd1R]
    exact mul_pos h64 hLpos
  have htlo : homS M / 8 ≤ 1 / 4 := by linarith only [hs4, hs]
  obtain ⟨_hf1, hf2, _hf3, hf4, hf5⟩ :=
    hanchor M hcs hg_g0 hs m (1 / 4) seamQuarterPos htlo le_rfl
      (64 * (d : ℝ) * |Real.log M.gamma|) le_rfl hup2
  have h1 := ae_ne_top_of_rpow_moment M
    (measurable_fluxCorrectedTwoScaleErrorObservableSup M (le_refl m) _) hq0 hf4
  have h2 := ae_ne_top_of_rpow_moment M
    (measurable_fluxCorrectedTwoScaleErrorObservableSup M (le_refl m) _) hq0 hf5
  have h3 := ae_ne_top_of_rpow_moment M
    (measurable_fluxCorrectedTwoScaleErrorObservableSup M (le_refl m) _) hq0 hf2
  filter_upwards [h1, h2, h3] with omega ha hb hc
  exact ⟨ha, hb, hc⟩

end

end Algsuperdiff.Section4.Provider.Homogenization
