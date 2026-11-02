/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration.Descent
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Bootstrap

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Deterministic recurrence integration: squared bootstrap

This file assembles Steps 3--4 of ABK26 `l.integrate.approx.recurrence` into
the squared-deviation estimate.  The all-scale envelope uses `cstarPlus`; the
comparator and recurrence remain directional in `cstar`.  The additional
`cstar⁻² * cstarPlus` term pays for that exact two-constant interface.

## References

* ABK26.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration

open scoped BigOperators
open Real

noncomputable section

namespace Internal

open scoped BigOperators
open Real

/-- The fixed universal descent constant: any value `≥ 6400·18/log 3 ≈ 1.05·10⁵`
works; `120000` gives margin.  It is public because the explicit integration
constant is built from it. -/
def recurrenceDescentConstant : ℝ := 120000

/-- `1 < log 3` (since `e < 3`). Standalone to keep it out of large contexts. -/
private lemma log_three_gt_one : 1 < Real.log 3 := by
  have h1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) h1

/-! ### Pure-real algebra cores

The three lemmas below are the `Chunk.lean` (`chunk_algebra`) device: every
genuinely *nonlinear* step of this file is discharged here, over abstract reals in
a minimal context, so that no numeric tactic is ever run inside the
`Real.sqrt` / `Real.log` / `geometricTerm` / `recurrenceComparator`-laden contexts of `base_bound`,
`smallness_B` and `sq_deviation_core_explicit`.  At the call sites only
`linarith only [...]` (or a direct application) remains. -/

/-- Squares reflect order between nonnegative reals (no numeric tactic: the two
square roots cancel by `Real.sqrt_sq`). -/
private lemma le_of_sq_le_sq_of_nonneg {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c)
    (h : x ^ 2 ≤ c ^ 2) : x ≤ c :=
  calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx).symm
    _ ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt h
    _ = c := Real.sqrt_sq hc

/-- `1 ≤ x → 1 ≤ x²`. -/
private lemma one_le_sq_of_one_le {x : ℝ} (hx : 1 ≤ x) : 1 ≤ x ^ 2 := by nlinarith [hx]

/-- Size facts for the comparator constant `cf = 1 + c⋆⁻²F + (c⋆c)⁻¹c⁺` and the
threshold `Θ = E·cf`: `1 + c⋆⁻²F ≤ cf`, `0 < cf`, `1 ≤ cf`, `1 ≤ Θ`.

Every leg is pure nonnegativity of the two added summands, so **no** upper bound
on `c⋆` is used (the manuscript's `2 ≤ cf`, which would need `c⋆ ≤ 1`, is never
required downstream: only `0 < Θ` and `1 ≤ Θ` are). -/
private lemma cf_size_facts {E cf Θ cstar cbar cplus F : ℝ}
    (hE : 1 ≤ E) (hF : 1 ≤ F) (hcstar : 0 < cstar) (hcbar : 0 < cbar)
    (hcc : cstar ≤ cplus)
    (hcf_def : cf = 1 + (cstar ^ 2)⁻¹ * F + (cstar * cbar)⁻¹ * cplus) (hΘ_def : Θ = E * cf) :
    1 + (cstar ^ 2)⁻¹ * F ≤ cf ∧ 0 < cf ∧ 1 ≤ cf ∧ 1 ≤ Θ := by
  have hcstar2pos : (0:ℝ) < cstar ^ 2 := pow_pos hcstar 2
  have hcbpos : (0:ℝ) < cstar * cbar := mul_pos hcstar hcbar
  have hcplus_pos : 0 < cplus := lt_of_lt_of_le hcstar hcc
  have hcplus_term : (0:ℝ) ≤ (cstar * cbar)⁻¹ * cplus :=
    mul_nonneg (inv_nonneg.mpr hcbpos.le) hcplus_pos.le
  have hFterm : (0:ℝ) ≤ (cstar ^ 2)⁻¹ * F :=
    mul_nonneg (inv_nonneg.mpr hcstar2pos.le) (by linarith only [hF])
  have hcf_lb0 : 1 + (cstar ^ 2)⁻¹ * F ≤ cf := by rw [hcf_def]; linarith only [hcplus_term]
  have hcf1 : (1:ℝ) ≤ cf := by rw [hcf_def]; linarith only [hFterm, hcplus_term]
  have hΘ1 : (1:ℝ) ≤ Θ := by
    have hprod := mul_le_mul hE hcf1 (by norm_num : (0:ℝ) ≤ 1) (by linarith only [hE] :
      (0:ℝ) ≤ E)
    rw [hΘ_def]; linarith only [hprod]
  exact ⟨hcf_lb0, by linarith only [hcf1], hcf1, hΘ1⟩

/-- Common cheap `cf/Θ/C₀` facts used by both smallness halves. -/
private lemma smallness_common
    {E γ cf Θ cstar cbar cplus F C₀ : ℝ}
    (hE : 1 ≤ E) (hF : 1 ≤ F) (hγ : 0 < γ) (hcstar : 0 < cstar) (hcbar : 0 < cbar)
    (hcc : cstar ≤ cplus)
    (hcf_def : cf = 1 + (cstar ^ 2)⁻¹ * F + (cstar * cbar)⁻¹ * cplus) (hΘ_def : Θ = E * cf)
    (hC0pos : 0 < C₀) (hthresh : γ * (C₀ * Θ) ≤ 1) :
    0 < cf ∧ (1 : ℝ) ≤ cf ∧ F ≤ cstar ^ 2 * cf ∧
      E ≤ Θ ∧ γ ≤ Θ * γ ∧ Θ * γ ≤ 1 / C₀ := by
  obtain ⟨-, hcfpos, hcf1, hΘ1⟩ := cf_size_facts hE hF hcstar hcbar hcc hcf_def hΘ_def
  have hcstar2pos : (0:ℝ) < cstar ^ 2 := pow_pos hcstar 2
  have hcbpos : (0:ℝ) < cstar * cbar := mul_pos hcstar hcbar
  have hcplus_pos : 0 < cplus := lt_of_lt_of_le hcstar hcc
  have hFle : F ≤ cstar ^ 2 * cf := by
    have hkey : cstar ^ 2 * ((cstar ^ 2)⁻¹ * F) = F := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcstar2pos), one_mul]
    have hexp : cstar ^ 2 * cf = cstar ^ 2 + cstar ^ 2 * ((cstar ^ 2)⁻¹ * F)
        + cstar ^ 2 * ((cstar * cbar)⁻¹ * cplus) := by rw [hcf_def]; ring
    rw [hkey] at hexp
    have hlast : (0:ℝ) ≤ cstar ^ 2 * ((cstar * cbar)⁻¹ * cplus) :=
      mul_nonneg hcstar2pos.le (mul_nonneg (inv_nonneg.mpr hcbpos.le) hcplus_pos.le)
    linarith only [hexp.le, hexp.ge, hlast, sq_nonneg cstar]
  have hEcf : E * 1 ≤ E * cf := mul_le_mul_of_nonneg_left hcf1 (by linarith [hE])
  have hEleΘ : E ≤ Θ := by rw [hΘ_def]; linarith [hEcf]
  have hΘgeγ : γ ≤ Θ * γ := by
    have := mul_le_mul_of_nonneg_right hΘ1 hγ.le
    linarith [this]
  have hΘγ : Θ * γ ≤ 1 / C₀ := by
    rw [le_div_iff₀ hC0pos]
    have heq : Θ * γ * C₀ = γ * (C₀ * Θ) := by ring
    linarith [hthresh, heq.le, heq.ge]
  exact ⟨hcfpos, hcf1, hFle, hEleΘ, hΘgeγ, hΘγ⟩

/-- **Smallness A.** The five "size" facts: `Eγ<1`, `4γ≤1`, `δ≤c⋆`,
`δ log3 ≤ 1`, `δ ≤ 1/2`.

The last leg is what lets the descent use the cap `c = min{c⋆,1}` without any
upper bound on `c⋆`: `δ ≤ c⋆` and `δ ≤ 1/2` together give `δ ≤ c`. -/
private lemma smallness_A
    {E γ cf Θ δ cstar cbar cplus F C₀ : ℝ}
    (hE : 1 ≤ E) (hF : 1 ≤ F) (hγ : 0 < γ) (hcstar : 0 < cstar) (hcbar : 0 < cbar)
    (hcc : cstar ≤ cplus)
    (hcf_def : cf = 1 + (cstar ^ 2)⁻¹ * F + (cstar * cbar)⁻¹ * cplus) (hΘ_def : Θ = E * cf)
    (hC0pos : 0 < C₀) (hC0big : (16 : ℝ) ≤ C₀)
    (hδ2cf : δ ^ 2 * cf = E * γ) (hδpos : 0 < δ) (hthresh : γ * (C₀ * Θ) ≤ 1) :
    E * γ < 1 ∧ 4 * γ ≤ 1 ∧ δ ≤ cstar ∧ δ * Real.log 3 ≤ 1 ∧ δ ≤ 1 / 2 := by
  obtain ⟨hcfpos, hcf1, hFle, hEleΘ, hΘgeγ, hΘγ⟩ :=
    smallness_common hE hF hγ hcstar hcbar hcc hcf_def hΘ_def hC0pos hthresh
  have hEγΘ : E * γ ≤ Θ * γ := mul_le_mul_of_nonneg_right hEleΘ hγ.le
  have h1lt : (1 : ℝ) / C₀ < 1 := by rw [div_lt_one hC0pos]; linarith [hC0big]
  have hEγ1 : E * γ ≤ 1 := le_trans hEγΘ (le_trans hΘγ h1lt.le)
  have hδ2E : δ ^ 2 ≤ E * γ := by
    have hp : δ ^ 2 * 1 ≤ δ ^ 2 * cf := mul_le_mul_of_nonneg_left hcf1 (sq_nonneg δ)
    rw [mul_one] at hp; linarith [hp, hδ2cf.le]
  have h4 : (1 : ℝ) / C₀ ≤ 1 / 4 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith [hC0big])
  have hδ2q : δ ^ 2 ≤ 1 / 4 := by linarith [hδ2E, hEγΘ, hΘγ, h4]
  have hδhalf : δ ≤ 1 / 2 := by
    have := Real.sqrt_le_sqrt hδ2q
    rw [Real.sqrt_sq hδpos.le] at this
    rwa [show Real.sqrt (1 / 4) = 1 / 2 by
      rw [show (1:ℝ)/4 = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
  refine ⟨?_, ?_, ?_, ?_, hδhalf⟩
  · linarith [hEγΘ, hΘγ, h1lt]
  · have hγC0 : γ ≤ 1 / C₀ := le_trans hΘgeγ hΘγ
    have : 4 * (1 / C₀) ≤ 1 := by rw [mul_one_div, div_le_one hC0pos]; linarith [hC0big]
    linarith [hγC0]
  · -- δ ≤ cstar, from `Eγ ≤ 1 ≤ F ≤ c⋆²cf`
    have hδ2cf_le : δ ^ 2 * cf ≤ cstar ^ 2 * cf := by
      rw [hδ2cf]; linarith [hEγ1, hF, hFle]
    have hδ2cstar : δ ^ 2 ≤ cstar ^ 2 := le_of_mul_le_mul_right hδ2cf_le hcfpos
    have := Real.sqrt_le_sqrt hδ2cstar
    rwa [Real.sqrt_sq hδpos.le, Real.sqrt_sq hcstar.le] at this
  · -- δ log 3 ≤ 1
    have hp : δ * Real.log 3 ≤ δ * 2 := mul_le_mul_of_nonneg_left log_three_le_two hδpos.le
    linarith [hp, hδhalf]

/-- **Smallness B.** The four "ratio" facts:
`2 ≤ δγ⁻¹`, `C·R ≤ 1/2`, `5δc⁺(c⋆c)⁻¹ ≤ C·R`, `δ·c⁺ ≤ c⋆c`.

The last two are the two-constant replacements for the single-constant
`5δc⋆⁻¹ ≤ C·R` and `δ ≤ c⋆`: both are bought by the `(c⋆c)⁻¹c⁺` summand of
`cf`, which forces `R = δ·cf ≥ δ·(c⋆c)⁻¹c⁺`, together with the
already-available `Cdesc'·R ≤ 1/2` (i.e. `δ·cf ≤ 1/240000`). -/
private lemma smallness_B
    {E γ cf Θ δ R cstar cbar cplus F Cdesc' C₀ : ℝ}
    (hE : 1 ≤ E) (hF : 1 ≤ F) (hγ : 0 < γ) (hcstar : 0 < cstar) (hcbar : 0 < cbar)
    (hcc : cstar ≤ cplus)
    (hcf_def : cf = 1 + (cstar ^ 2)⁻¹ * F + (cstar * cbar)⁻¹ * cplus) (hΘ_def : Θ = E * cf)
    (hCdesc_val : Cdesc' = 120000) (hC0_def : C₀ = 4 * Cdesc' ^ 2)
    (hR2 : R ^ 2 = Θ * γ) (hRnn : 0 ≤ R) (hδ2cf : δ ^ 2 * cf = E * γ) (hδpos : 0 < δ)
    (hRcf : R = δ * cf) (hthresh : γ * (C₀ * Θ) ≤ 1) :
    2 ≤ δ * γ⁻¹ ∧ Cdesc' * R ≤ 1 / 2 ∧
      5 * δ * cplus * (cstar * cbar)⁻¹ ≤ Cdesc' * R ∧ δ * cplus ≤ cstar * cbar := by
  have hCdescpos : 0 < Cdesc' := by rw [hCdesc_val]; norm_num
  have hC0pos : 0 < C₀ := by rw [hC0_def, hCdesc_val]; norm_num
  have hC0big : (16 : ℝ) ≤ C₀ := by rw [hC0_def, hCdesc_val]; norm_num
  obtain ⟨hcfpos, hcf1, -, hEleΘ, hΘgeγ, hΘγ⟩ :=
    smallness_common hE hF hγ hcstar hcbar hcc hcf_def hΘ_def hC0pos hthresh
  have hcstar2pos : (0:ℝ) < cstar ^ 2 := pow_pos hcstar 2
  have hcbpos : (0:ℝ) < cstar * cbar := mul_pos hcstar hcbar
  have hcplus_pos : 0 < cplus := lt_of_lt_of_le hcstar hcc
  -- the `c⁺`-summand lower bound on `cf`
  have hcf_lb2 : (cstar * cbar)⁻¹ * cplus ≤ cf := by
    rw [hcf_def]
    have h1 : (0:ℝ) ≤ (cstar ^ 2)⁻¹ * F :=
      mul_nonneg (inv_nonneg.mpr hcstar2pos.le) (by linarith [hF])
    linarith
  have hXnn : (0:ℝ) ≤ δ * ((cstar * cbar)⁻¹ * cplus) :=
    mul_nonneg hδpos.le (mul_nonneg (inv_nonneg.mpr hcbpos.le) hcplus_pos.le)
  have hRlb2 : δ * ((cstar * cbar)⁻¹ * cplus) ≤ R := by
    rw [hRcf]; exact mul_le_mul_of_nonneg_left hcf_lb2 hδpos.le
  -- `Cdesc' R ≤ 1/2`, proved once and reused by the last two legs
  have hCdescR : Cdesc' * R ≤ 1 / 2 := by
    have hsq : (Cdesc' * R) ^ 2 ≤ 1 / 4 := by
      rw [mul_pow, hR2]
      have hle : Cdesc' ^ 2 * (Θ * γ) ≤ Cdesc' ^ 2 * (1 / C₀) :=
        mul_le_mul_of_nonneg_left hΘγ (sq_nonneg _)
      have heq : Cdesc' ^ 2 * (1 / C₀) = 1 / 4 := by rw [hC0_def, hCdesc_val]; norm_num
      linarith [hle, heq.le, heq.ge]
    refine le_of_sq_le_sq_of_nonneg (mul_nonneg hCdescpos.le hRnn) (by norm_num) ?_
    rw [show ((1 : ℝ) / 2) ^ 2 = 1 / 4 by norm_num]; exact hsq
  refine ⟨?_, hCdescR, ?_, ?_⟩
  · -- 2 ≤ δ γ⁻¹
    have hδ2Θ : δ ^ 2 * Θ = E ^ 2 * γ := by
      rw [hΘ_def, show δ ^ 2 * (E * cf) = E * (δ ^ 2 * cf) by ring, hδ2cf]; ring
    have hxnn : 0 ≤ (δ * γ⁻¹) ^ 2 := sq_nonneg _
    have hxp : (δ * γ⁻¹) ^ 2 * (Θ * γ) = E ^ 2 := by
      rw [show (δ * γ⁻¹) ^ 2 * (Θ * γ) = (δ ^ 2 * Θ) * (γ⁻¹ * γ⁻¹ * γ) by
        ring, hδ2Θ,
        show γ⁻¹ * γ⁻¹ * γ = γ⁻¹ * (γ⁻¹ * γ) by ring, inv_mul_cancel₀
          (ne_of_gt hγ), mul_one,
        show E ^ 2 * γ * γ⁻¹ = E ^ 2 * (γ * γ⁻¹) by ring, mul_inv_cancel₀ (ne_of_gt
          hγ), mul_one]
    have h1 : (δ * γ⁻¹) ^ 2 * (Θ * γ) ≤ (δ * γ⁻¹) ^ 2 * (1 / C₀) :=
      mul_le_mul_of_nonneg_left hΘγ hxnn
    rw [hxp, mul_one_div, le_div_iff₀ hC0pos] at h1
    have hE2 : (1 : ℝ) ≤ E ^ 2 := one_le_sq_of_one_le hE
    have hlb : (16 : ℝ) ≤ E ^ 2 * C₀ := by
      have := mul_le_mul hE2 hC0big (by norm_num : (0:ℝ) ≤ 16) (sq_nonneg E)
      linarith [this]
    have hxge : 4 ≤ (δ * γ⁻¹) ^ 2 := by linarith [h1, hlb]
    have hx0 : 0 ≤ δ * γ⁻¹ := mul_nonneg hδpos.le (inv_nonneg.mpr hγ.le)
    refine le_of_sq_le_sq_of_nonneg (by norm_num) hx0 ?_
    rw [show (2 : ℝ) ^ 2 = 4 by norm_num]; exact hxge
  · -- 5 δ c⁺ (c⋆c)⁻¹ ≤ Cdesc R
    have h1 : Cdesc' * (δ * ((cstar * cbar)⁻¹ * cplus)) ≤ Cdesc' * R :=
      mul_le_mul_of_nonneg_left hRlb2 hCdescpos.le
    have h2 : 5 * (δ * ((cstar * cbar)⁻¹ * cplus)) ≤ Cdesc' * (δ * ((cstar * cbar)⁻¹ *
      cplus)) := by
      rw [hCdesc_val]; linarith [hXnn]
    have h3 : 5 * δ * cplus * (cstar * cbar)⁻¹ = 5 * (δ * ((cstar * cbar)⁻¹ * cplus)) := by
      ring
    linarith [h1, h2, h3.le, h3.ge]
  · -- δ c⁺ ≤ c⋆c
    have hδcf : δ * cf ≤ 1 / 240000 := by
      have h : Cdesc' * (δ * cf) ≤ 1 / 2 := by rw [← hRcf]; exact hCdescR
      rw [hCdesc_val] at h; linarith
    have hcplus_le : cplus ≤ (cstar * cbar) * cf := by
      have h := mul_le_mul_of_nonneg_left hcf_lb2 hcbpos.le
      rwa [show (cstar * cbar) * ((cstar * cbar)⁻¹ * cplus) = cplus by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcbpos), one_mul]] at h
    have hstep : δ * cplus ≤ δ * ((cstar * cbar) * cf) :=
      mul_le_mul_of_nonneg_left hcplus_le hδpos.le
    have hmul2 : (cstar * cbar) * (δ * cf) ≤ (cstar * cbar) * (1 / 240000) :=
      mul_le_mul_of_nonneg_left hδcf hcbpos.le
    have hid : δ * ((cstar * cbar) * cf) = (cstar * cbar) * (δ * cf) := by ring
    linarith [hstep, hmul2, hcbpos, hid.le, hid.ge]

/-- **Base case** (`e.small.m.is.done`), two-constant form: below `mc` (where
`3^{2γm} ≤ Bb`), the small-scale envelope at `c⁺` already gives
`|s_m² − T_m| ≤ C·R·T_m` for the comparator `T_m` built from `c⋆ ≤ c⁺`. -/
private lemma base_bound
    {ν cstar cbar cplus γ δ R Cdesc' : ℝ} {s : ℤ → ℝ}
    (hν : 0 < ν) (hcstar : 0 < cstar) (hcbar : 0 < cbar) (hcc : cstar ≤ cplus) (hγ : 0 < γ)
    (hsmall : ∀ m : ℤ, ν ≤ s m ∧
      s m ≤ (1 + (ν ^ 2)⁻¹ * cplus * γ⁻¹ * geometricTerm γ m) * ν)
    (_hδpos : 0 < δ) (hδcplus : δ * cplus ≤ cstar * cbar) (hγ1 : 4 * γ ≤ 1)
    (h5δR : 5 * δ * cplus * (cstar * cbar)⁻¹ ≤ Cdesc' * R) (hCdescpos : 0 < Cdesc') (hRnn :
      0 ≤ R)
    {m : ℤ} (hgm_ub : geometricTerm γ m ≤ δ * ν ^ 2 * γ * (cstar * cbar)⁻¹) :
    |(s m) ^ 2 - recurrenceComparator ν cstar γ m| ≤ Cdesc' * R * recurrenceComparator ν
      cstar γ m := by
  have hgm : 0 < geometricTerm γ m := geometricTerm_pos γ m
  have hν2pos : 0 < ν ^ 2 := pow_pos hν 2
  have hcplus_pos : 0 < cplus := lt_of_lt_of_le hcstar hcc
  have hcstar2pos : (0:ℝ) < cstar * cbar := mul_pos hcstar hcbar
  obtain ⟨hlo_s, hup_s⟩ := hsmall m
  have hsmpos : 0 < s m := lt_of_lt_of_le hν hlo_s
  have hβnn : 0 ≤ (ν ^ 2)⁻¹ * cplus * γ⁻¹ * geometricTerm γ m := by positivity
  have hsm_lo : ν ^ 2 ≤ (s m) ^ 2 := pow_le_pow_left₀ hν.le hlo_s 2
  have hsm_hi : (s m) ^ 2 ≤ (1 + (ν ^ 2)⁻¹ * cplus * γ⁻¹ * geometricTerm γ m) ^ 2 *
    ν ^ 2 := by
    have h := pow_le_pow_left₀ hsmpos.le hup_s 2
    rwa [mul_pow] at h
  -- β ≤ 1
  have hβ1 : (ν ^ 2)⁻¹ * cplus * γ⁻¹ * geometricTerm γ m ≤ 1 := by
    have hmono : (ν ^ 2)⁻¹ * cplus * γ⁻¹ * geometricTerm γ m
        ≤ (ν ^ 2)⁻¹ * cplus * γ⁻¹ * (δ * ν ^ 2 * γ * (cstar * cbar)⁻¹) :=
      mul_le_mul_of_nonneg_left hgm_ub (by positivity)
    have hval : (ν ^ 2)⁻¹ * cplus * γ⁻¹ * (δ * ν ^ 2 * γ * (cstar * cbar)⁻¹)
        = δ * cplus * (cstar * cbar)⁻¹ := by
      rw [show (ν ^ 2)⁻¹ * cplus * γ⁻¹ * (δ * ν ^ 2 * γ * (cstar * cbar)⁻¹)
          = δ * cplus * (cstar * cbar)⁻¹ * ((ν ^ 2)⁻¹ * ν ^ 2) * (γ⁻¹ * γ) by ring,
        inv_mul_cancel₀ (ne_of_gt hν2pos), inv_mul_cancel₀ (ne_of_gt hγ), mul_one, mul_one]
    have hδc1 : δ * cplus * (cstar * cbar)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hcstar2pos]; exact hδcplus
    linarith [hmono, hval.le, hval.ge, hδc1]
  have hKlo := Stream.le_Kgamma hγ
  have hKhi := Stream.Kgamma_le hγ
  have hss := small_scale_algebra hν2pos hcstar hcc hγ hgm.le hsm_lo hsm_hi rfl hβ1 hγ1 hKlo
    hKhi
  have hTmeq : ν ^ 2 + cstar * Stream.Kgamma γ * geometricTerm γ m = recurrenceComparator ν
    cstar γ m := by rw [recurrenceComparator]
  rw [hTmeq] at hss
  -- 5 c⁺γ⁻¹g_m ≤ Cdesc
  have h1 : cplus * γ⁻¹ * geometricTerm γ m ≤ cplus * γ⁻¹ * (δ * ν ^ 2 * γ *
    (cstar * cbar)⁻¹) :=
    mul_le_mul_of_nonneg_left hgm_ub (by positivity)
  have hBbval : cplus * γ⁻¹ * (δ * ν ^ 2 * γ * (cstar * cbar)⁻¹)
      = δ * ν ^ 2 * cplus * (cstar * cbar)⁻¹ := by
    rw [show cplus * γ⁻¹ * (δ * ν ^ 2 * γ * (cstar * cbar)⁻¹)
        = δ * ν ^ 2 * cplus * (cstar * cbar)⁻¹ * (γ⁻¹ * γ) by ring,
      inv_mul_cancel₀ (ne_of_gt hγ), mul_one]
  have h5 : 5 * (δ * ν ^ 2 * cplus * (cstar * cbar)⁻¹) ≤ Cdesc' * R * ν ^ 2 := by
    have hscale := mul_le_mul_of_nonneg_right h5δR hν2pos.le
    have hid : 5 * (δ * ν ^ 2 * cplus * (cstar * cbar)⁻¹)
        = 5 * δ * cplus * (cstar * cbar)⁻¹ * ν ^ 2 := by ring
    linarith only [hscale, hid.le, hid.ge]
  have hTmge : ν ^ 2 ≤ recurrenceComparator ν cstar γ m := nu_sq_le_recurrenceComparator
    hcstar.le hγ m
  have hCRnn : 0 ≤ Cdesc' * R := mul_nonneg hCdescpos.le hRnn
  have hfin : 5 * (cplus * γ⁻¹ * geometricTerm γ m) ≤ Cdesc' * R * recurrenceComparator
    ν cstar γ m := by
    have hb1 : 5 * (cplus * γ⁻¹ * geometricTerm γ m) ≤ 5 * (δ * ν ^ 2 * cplus * (cstar
      * cbar)⁻¹) := by
      linarith only [h1, hBbval.le, hBbval.ge]
    have hb2 : Cdesc' * R * ν ^ 2 ≤ Cdesc' * R * recurrenceComparator ν cstar γ m :=
      mul_le_mul_of_nonneg_left hTmge hCRnn
    linarith [hb1, h5, hb2]
  linarith [hss, hfin]

/-- **One-step increment** (Step 2 chunk + drop). Given the a-priori deviation
bound at the lower scale `n = m − ⌊adaptStep⌋`, the increment `|d_m − d_n|` is
controlled by the target drop `C·R·(T_m − T_n)`. -/
private lemma step_bound
    {ν cstar cbar γ E F δ R Cdesc' cf : ℝ} {m₀ : ℤ} {s : ℤ → ℝ}
    (hν : 0 < ν) (hcstar : 0 < cstar) (hcbar : 0 < cbar) (hcbarle : cbar ≤ cstar)
    (hcbar1 : cbar ≤ 1) (hγ : 0 < γ)
    (hE : 1 ≤ E) (hF : 1 ≤ F) (hpos : ∀ m, 0 < s m) (hEγ1 : E * γ < 1)
    (hupper : ∀ n m : ℤ, m ≤ m₀ → n ≤ m → (m : ℝ) ≤ (n : ℝ) + cstar *
      γ⁻¹ →
      s m ≤ (1 + E * γ) * s n + recurrenceIncrement cstar γ n m * (s n)⁻¹)
    (hlower : ∀ n m : ℤ, m ≤ m₀ → n ≤ m → (m : ℝ) ≤ (n : ℝ) + cstar *
      γ⁻¹ →
      (1 - E * γ) * s n + recurrenceIncrement cstar γ n m * ((s n)⁻¹) ^ 2 * s m
          - F * ((m : ℝ) - (n : ℝ)) ^ 2 * ((s n)⁻¹) ^ 4 * s m * geometricTerm (2 * γ) m
            ≤ s m)
    (hcf_lb0 : 1 + (cstar ^ 2)⁻¹ * F ≤ cf) (hcfpos : 0 < cf)
    (hδpos : 0 < δ) (hδlog : δ * Real.log 3 ≤ 1) (hδcbar : δ ≤ cbar) (hδγ2 : 2 ≤
      δ * γ⁻¹)
    (hδR : δ * R = E * γ) (hδ2cf : δ ^ 2 * cf = E * γ) (hCdescR : Cdesc' * R ≤ 1 / 2)
    (hCdesc_val : Cdesc' = 120000) (hRnn : 0 ≤ R)
    {m : ℤ} (hmle : m ≤ m₀)
    (hgm_lb : δ * ν ^ 2 * γ * (cstar * cbar)⁻¹ ≤ geometricTerm γ m)
    (hIH : |(s (m - ⌊adaptStep δ ν cstar γ m⌋)) ^ 2 - recurrenceComparator ν cstar γ (m
      - ⌊adaptStep δ ν cstar γ m⌋)|
        ≤ Cdesc' * R * recurrenceComparator ν cstar γ (m - ⌊adaptStep δ ν cstar γ m⌋)) :
    |(s m) ^ 2 - (s (m - ⌊adaptStep δ ν cstar γ m⌋)) ^ 2
        - 2 * recurrenceIncrement cstar γ (m - ⌊adaptStep δ ν cstar γ m⌋) m|
      ≤ Cdesc' * R * (recurrenceComparator ν cstar γ m - recurrenceComparator ν cstar γ (m
        - ⌊adaptStep δ ν cstar γ m⌋)) := by
  set h : ℤ := ⌊adaptStep δ ν cstar γ m⌋ with hh
  set n : ℤ := m - h with hn
  have ha_eq : (m : ℝ) - (n : ℝ) = (h : ℝ) := by
    have hint : (m : ℤ) - n = h := by omega
    exact_mod_cast hint
  have hastep2 : 2 ≤ adaptStep δ ν cstar γ m := two_le_adaptStep hδγ2 m
  have hastep_le : adaptStep δ ν cstar γ m ≤ cbar * γ⁻¹ :=
    adaptStep_le_cap hν hcstar hγ hδpos hcbar hδcbar hgm_lb
  have hfloor_le : (h : ℝ) ≤ adaptStep δ ν cstar γ m := by rw [hh]; exact Int.floor_le _
  have hfloor_ge : adaptStep δ ν cstar γ m / 2 ≤ (h : ℝ) := by
    rw [hh]
    exact floor_ge_half hastep2
  have hh1 : 1 ≤ h := by rw [hh]; exact one_le_floor hastep2
  have hnm : n ≤ m := by rw [hn]; omega
  have hh_nn : 0 ≤ (h : ℝ) := by
    have h0 : (0 : ℤ) ≤ h := by omega
    exact_mod_cast h0
  have hmax1 : δ * ν ^ 2 * cstar⁻¹ * (geometricTerm γ m)⁻¹ ≤ adaptStep δ ν cstar γ
    m := le_max_left _ _
  have hmax2 : δ * γ⁻¹ ≤ adaptStep δ ν cstar γ m := le_max_right _ _
  have hF1 : (1 / 2) * (δ * ν ^ 2 * cstar⁻¹ * (geometricTerm γ m)⁻¹) ≤ (m : ℝ) - (n
    : ℝ) := by
    rw [ha_eq]; linarith [hmax1, hfloor_ge]
  have hF2 : δ ≤ 2 * γ * ((m : ℝ) - (n : ℝ)) := by
    rw [ha_eq]
    have hstep_ge : δ * γ⁻¹ ≤ 2 * (h : ℝ) := by linarith [hmax2, hfloor_ge]
    calc δ = γ * (δ * γ⁻¹) := by
            rw [show γ * (δ * γ⁻¹) = δ * (γ * γ⁻¹) by ring, mul_inv_cancel₀
              (ne_of_gt hγ), mul_one]
      _ ≤ γ * (2 * (h : ℝ)) := mul_le_mul_of_nonneg_left hstep_ge hγ.le
      _ = 2 * γ * (h : ℝ) := by ring
  have hh_le : (h : ℝ) ≤ cbar * γ⁻¹ := le_trans hfloor_le hastep_le
  have hF3 : 2 * γ * ((m : ℝ) - (n : ℝ)) ≤ 2 := by
    rw [ha_eq]
    calc 2 * γ * (h : ℝ) ≤ 2 * γ * (cbar * γ⁻¹) := by
          apply mul_le_mul_of_nonneg_left hh_le; positivity
      _ = 2 * cbar * (γ * γ⁻¹) := by ring
      _ = 2 * cbar := by rw [mul_inv_cancel₀ (ne_of_gt hγ), mul_one]
      _ ≤ 2 := by linarith [hcbar1]
  have hrange : (m : ℝ) ≤ (n : ℝ) + cstar * γ⁻¹ := by
    have hx : (h : ℝ) ≤ cstar * γ⁻¹ :=
      le_trans hh_le (mul_le_mul_of_nonneg_right hcbarle (inv_nonneg.mpr hγ.le))
    rw [← ha_eq] at hx; linarith [hx]
  have hh_le_unit : (h : ℝ) ≤ γ⁻¹ := by
    calc
      (h : ℝ) ≤ cbar * γ⁻¹ := hh_le
      _ ≤ 1 * γ⁻¹ := mul_le_mul_of_nonneg_right hcbar1 (inv_nonneg.mpr hγ.le)
      _ = γ⁻¹ := one_mul _
  have hunitRange : (m : ℝ) ≤ (n : ℝ) + γ⁻¹ := by
    have hx := hh_le_unit
    rw [← ha_eq] at hx
    linarith only [hx]
  -- sandwich at n from the induction hypothesis
  have hTn0 : 0 ≤ recurrenceComparator ν cstar γ n := le_trans (sq_nonneg ν)
    (nu_sq_le_recurrenceComparator hcstar.le hγ n)
  rw [abs_le] at hIH
  have hprod : Cdesc' * R * recurrenceComparator ν cstar γ n ≤ (1 / 2) *
    recurrenceComparator ν cstar γ n :=
    mul_le_mul_of_nonneg_right hCdescR hTn0
  have hsass_hi : (s n) ^ 2 ≤ 2 * recurrenceComparator ν cstar γ n := by linarith [hIH.2,
    hprod, hTn0]
  have hsass_lo : (1 / 2) * recurrenceComparator ν cstar γ n ≤ (s n) ^ 2 := by linarith
    [hIH.1, hprod]
  -- chunk estimate
  have hchunk := chunk_increment_under_sass hν hcstar hγ hE hF hpos hEγ1
    hupper hlower hmle hnm hrange hunitRange hsass_lo hsass_hi
  -- quadratic term ≤ E
  have hμmono : min ((ν ^ 2)⁻¹ * cstar * γ⁻¹ * geometricTerm γ n) 1
      ≤ min ((ν ^ 2)⁻¹ * cstar * γ⁻¹ * geometricTerm γ m) 1 :=
    min_le_min (mul_le_mul_of_nonneg_left (geometricTerm_mono hγ hnm) (by positivity)) (le_refl 1)
  have hμnn : 0 ≤ min ((ν ^ 2)⁻¹ * cstar * γ⁻¹ * geometricTerm γ n) 1 :=
    le_min (mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr (sq_nonneg ν)) hcstar.le)
      (inv_nonneg.mpr hγ.le)) (geometricTerm_pos γ n).le) (by norm_num)
  have hμmnn : 0 ≤ min ((ν ^ 2)⁻¹ * cstar * γ⁻¹ * geometricTerm γ m) 1 :=
    le_min (mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr (sq_nonneg ν)) hcstar.le)
      (inv_nonneg.mpr hγ.le)) (geometricTerm_pos γ m).le) (by norm_num)
  have ha_nn : 0 ≤ (m : ℝ) - (n : ℝ) := by rw [ha_eq]; exact hh_nn
  have hμa : min ((ν ^ 2)⁻¹ * cstar * γ⁻¹ * geometricTerm γ n) 1 * ((m : ℝ) - (n :
    ℝ)) ≤ δ * γ⁻¹ := by
    have hmm := mu_mul_adaptStep_le hν hcstar hγ hδpos m
    rw [ha_eq]
    calc min ((ν ^ 2)⁻¹ * cstar * γ⁻¹ * geometricTerm γ n) 1 * (h : ℝ)
        ≤ min ((ν ^ 2)⁻¹ * cstar * γ⁻¹ * geometricTerm γ m) 1 * (h : ℝ) :=
          mul_le_mul_of_nonneg_right hμmono hh_nn
      _ ≤ min ((ν ^ 2)⁻¹ * cstar * γ⁻¹ * geometricTerm γ m) 1 * adaptStep δ ν cstar
        γ m :=
          mul_le_mul_of_nonneg_left hfloor_le hμmnn
      _ ≤ δ * γ⁻¹ := hmm
  have hquad : cf * (min ((ν ^ 2)⁻¹ * cstar * γ⁻¹ * geometricTerm γ n) 1) ^ 2 * γ *
    ((m : ℝ) - (n : ℝ)) ^ 2 ≤ E :=
    quad_bound hμa hμnn ha_nn hδpos.le hcfpos hγ hδ2cf
  have hTm_nn : 0 ≤ recurrenceComparator ν cstar γ m := le_trans (sq_nonneg ν)
    (nu_sq_le_recurrenceComparator hcstar.le hγ m)
  have hchunk6400 : |(s m) ^ 2 - (s n) ^ 2 - 2 * recurrenceIncrement cstar γ n m| ≤ 6400 * E
    * γ * recurrenceComparator ν cstar γ m := by
    -- the chunk's constant is `1 + c⋆⁻²F ≤ cf`; monotonicity in that coefficient
    have hQnn : (0:ℝ) ≤ (min ((ν ^ 2)⁻¹ * cstar * γ⁻¹ * geometricTerm γ n) 1) ^ 2
        * (γ * ((m : ℝ) - (n : ℝ)) ^ 2) := by positivity
    have hmono0 := mul_le_mul_of_nonneg_right hcf_lb0 hQnn
    have hbr : E + (1 + (cstar ^ 2)⁻¹ * F)
        * (min ((ν ^ 2)⁻¹ * cstar * γ⁻¹ * geometricTerm γ n) 1) ^ 2 * γ * ((m : ℝ) - (n : ℝ)) ^ 2
        ≤ 2 * E := by
      linarith [hquad, hmono0]
    have hmul : 3200 * γ * (E + (1 + (cstar ^ 2)⁻¹ * F) * (min ((ν ^ 2)⁻¹ * cstar *
      γ⁻¹ * geometricTerm γ n) 1) ^ 2 * γ * ((m : ℝ) - (n : ℝ)) ^ 2) *
      recurrenceComparator ν cstar γ m
        ≤ 3200 * γ * (2 * E) * recurrenceComparator ν cstar γ m := by
      apply mul_le_mul_of_nonneg_right _ hTm_nn
      apply mul_le_mul_of_nonneg_left hbr (by positivity)
    calc |(s m) ^ 2 - (s n) ^ 2 - 2 * recurrenceIncrement cstar γ n m|
        ≤ 3200 * γ * (E + (1 + (cstar ^ 2)⁻¹ * F) * (min ((ν ^ 2)⁻¹ * cstar * γ⁻¹
          * geometricTerm γ n) 1) ^ 2 * γ * ((m : ℝ) - (n : ℝ)) ^ 2) *
          recurrenceComparator ν cstar γ m := hchunk
      _ ≤ 3200 * γ * (2 * E) * recurrenceComparator ν cstar γ m := hmul
      _ = 6400 * E * γ * recurrenceComparator ν cstar γ m := by ring
  -- geometric drop
  have hdrop := drop_bound hcstar hγ hδpos hδlog hnm hF1 hF2 hF3
  have hκpos : 0 < Real.log 3 / 18 := by positivity
  have hC0κ : 6400 ≤ Cdesc' * (Real.log 3 / 18) := by
    rw [hCdesc_val]; linarith [log_three_gt_one]
  exact per_step_algebra hchunk6400 hδR.symm hdrop hRnn hδpos.le hTm_nn hκpos hC0κ

/-- **Squared-deviation core (ABK26 Steps 3–4), two-constant capped form.**
Produces the constant `C₀` and, under the quadratic smallness
`γ·C₀·(E(1+c⋆⁻²F+(c⋆·min{c⋆,1})⁻¹c⁺)) ≤ 1`, the bootstrap sandwich
`T_m ≤ 2s_m²` and the squared-deviation bound
`|s_m² − T_m| ≤ C₀√(E(1+c⋆⁻²F+(c⋆·min{c⋆,1})⁻¹c⁺)γ)·T_m` for every `m ≤ m₀`.

The a-priori envelope `hsmall` (`e.small.scale.bound`) is read at the constant
`c⁺ ≥ c⋆`, while the comparator `T_m` and the recurrence hypotheses keep the
directional `c⋆`; the gap is paid for by the extra `(c⋆·min{c⋆,1})⁻¹c⁺` summand
in the `γ`-threshold.

Both are recovered here from the cap `c = min{c⋆,1}` (`adaptStep_le_cap`),
whose only price is that the `c⁺`-summand of the composite constant is
denominated in `c⋆c` rather than `c⋆²`. -/
theorem sq_deviation_core_explicit
    {ν cstar cplus γ E F : ℝ} {m₀ : ℤ} {s : ℤ → ℝ}
    (hν : 0 < ν) (hcstar : 0 < cstar) (hcc : cstar ≤ cplus) (hγ : 0 < γ)
    (hE : 1 ≤ E) (hF : 1 ≤ F) (hpos : ∀ m, 0 < s m)
    (hsmall : ∀ m : ℤ, ν ≤ s m ∧
      s m ≤ (1 + (ν ^ 2)⁻¹ * cplus * γ⁻¹ * geometricTerm γ m) * ν)
    (hupper : ∀ n m : ℤ, m ≤ m₀ → n ≤ m → (m : ℝ) ≤ (n : ℝ) + cstar *
      γ⁻¹ →
      s m ≤ (1 + E * γ) * s n + recurrenceIncrement cstar γ n m * (s n)⁻¹)
    (hlower : ∀ n m : ℤ, m ≤ m₀ → n ≤ m → (m : ℝ) ≤ (n : ℝ) + cstar *
      γ⁻¹ →
      (1 - E * γ) * s n + recurrenceIncrement cstar γ n m * ((s n)⁻¹) ^ 2 * s m
          - F * ((m : ℝ) - (n : ℝ)) ^ 2 * ((s n)⁻¹) ^ 4 * s m * geometricTerm (2 * γ) m
        ≤ s m) :
    γ * ((4 * recurrenceDescentConstant ^ 2)
      * (E * (1 + (cstar ^ 2)⁻¹ * F + (cstar * min cstar 1)⁻¹ * cplus))) ≤ 1 →
      ∀ m : ℤ, m ≤ m₀ →
        recurrenceComparator ν cstar γ m ≤ 2 * (s m) ^ 2 ∧
        |(s m) ^ 2 - recurrenceComparator ν cstar γ m|
          ≤ (4 * recurrenceDescentConstant ^ 2)
              * Real.sqrt (E * (1 + (cstar ^ 2)⁻¹ * F + (cstar * min cstar 1)⁻¹ * cplus) * γ)
                * recurrenceComparator ν cstar γ m := by
  classical
  set cbar : ℝ := min cstar 1 with hcbar_def
  have hcbar : 0 < cbar := by rw [hcbar_def]; exact lt_min hcstar one_pos
  have hcbarle : cbar ≤ cstar := by rw [hcbar_def]; exact min_le_left _ _
  have hcbar1 : cbar ≤ 1 := by rw [hcbar_def]; exact min_le_right _ _
  set cf : ℝ := 1 + (cstar ^ 2)⁻¹ * F + (cstar * cbar)⁻¹ * cplus with hcf_def
  set Θ : ℝ := E * cf with hΘ_def
  -- cf ≥ 1 + c⋆⁻²F, cf ≥ 1 and Θ ≥ 1, from the pure-real algebra core
  obtain ⟨hcf_lb0, hcfpos, -, hΘ1⟩ := cf_size_facts hE hF hcstar hcbar hcc hcf_def hΘ_def
  have hΘpos : 0 < Θ := by linarith only [hΘ1]
  set C₀ : ℝ := 4 * recurrenceDescentConstant ^ 2 with hC0_def
  have hCdesc_val : recurrenceDescentConstant = 120000 := rfl
  have hCdescpos : 0 < recurrenceDescentConstant := by rw [hCdesc_val]; norm_num
  have hC0pos : 0 < C₀ := by rw [hC0_def]; positivity
  intro hthresh
  change γ * (C₀ * (E * (1 + (cstar ^ 2)⁻¹ * F + (cstar * cbar)⁻¹ * cplus))) ≤ 1 at hthresh
  set R : ℝ := Real.sqrt (Θ * γ) with hR_def
  set δ : ℝ := Real.sqrt (E * γ / cf) with hδ_def
  -- square-root identities feeding the abstract smallness lemma
  have hν2pos : 0 < ν ^ 2 := pow_pos hν 2
  have hEγpos : 0 < E * γ := by positivity
  have hΘγpos : 0 < Θ * γ := by positivity
  have hRnn : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = Θ * γ := by rw [hR_def]; exact Real.sq_sqrt hΘγpos.le
  have hδpos : 0 < δ := by rw [hδ_def]; exact Real.sqrt_pos.mpr (by positivity)
  have hδ2 : δ ^ 2 = E * γ / cf := by rw [hδ_def]; exact Real.sq_sqrt (by positivity)
  have hδ2cf : δ ^ 2 * cf = E * γ := by rw [hδ2]; field_simp
  have hδR : δ * R = E * γ := by
    rw [hδ_def, hR_def, ← Real.sqrt_mul (by positivity)]
    rw [show E * γ / cf * (Θ * γ) = (E * γ) ^ 2 by rw [hΘ_def]; field_simp]
    exact Real.sqrt_sq (by positivity)
  have hRcf : R = δ * cf := by
    rw [hR_def, hδ_def, show Θ * γ = cf ^ 2 * (E * γ / cf) by rw [hΘ_def]; field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hcfpos.le]
    ring
  have hC0big : (16 : ℝ) ≤ C₀ := by rw [hC0_def, hCdesc_val]; norm_num
  obtain ⟨hEγ1, hγ1, hδcstar, hδlog, hδhalf⟩ :=
    smallness_A hE hF hγ hcstar hcbar hcc hcf_def hΘ_def hC0pos hC0big hδ2cf hδpos hthresh
  have hδcbar : δ ≤ cbar := by
    rw [hcbar_def]; exact le_min hδcstar (by linarith only [hδhalf])
  obtain ⟨hδγ2, hCdescR, h5δR, hδcplus⟩ :=
    smallness_B hE hF hγ hcstar hcbar hcc hcf_def hΘ_def hCdesc_val hC0_def
      hR2 hRnn hδ2cf hδpos hRcf hthresh
  -- base scale mc via floor
  set Bb : ℝ := δ * ν ^ 2 * γ * (cstar * cbar)⁻¹ with hBb_def
  have hBbpos : 0 < Bb := by rw [hBb_def]; positivity
  have hden : 0 < 2 * γ * Real.log 3 := by positivity
  set mc : ℤ := ⌊Real.log Bb / (2 * γ * Real.log 3)⌋ with hmc_def
  have hmc_le : geometricTerm γ mc ≤ Bb := by
    apply geometricTerm_le_of_log_le hBbpos
    have hfloor : (mc : ℝ) ≤ Real.log Bb / (2 * γ * Real.log 3) := by
      rw [hmc_def]; exact Int.floor_le _
    calc 2 * γ * (mc : ℝ) * Real.log 3 = (mc : ℝ) * (2 * γ * Real.log 3) := by ring
      _ ≤ Real.log Bb := (le_div_iff₀ hden).mp hfloor
  have hmc_gt : Bb < geometricTerm γ (mc + 1) := by
    apply lt_geometricTerm_of_log_lt hBbpos
    have hlt : Real.log Bb / (2 * γ * Real.log 3) < (mc : ℝ) + 1 := by
      rw [hmc_def]; exact Int.lt_floor_add_one _
    have h := (div_lt_iff₀ hden).mp hlt
    push_cast
    calc Real.log Bb < ((mc : ℝ) + 1) * (2 * γ * Real.log 3) := h
      _ = 2 * γ * ((mc : ℝ) + 1) * Real.log 3 := by ring
  -- run the single-step-back descent
  have hdev : ∀ m : ℤ, m ≤ m₀ →
      |(s m) ^ 2 - recurrenceComparator ν cstar γ m| ≤ recurrenceDescentConstant * R *
        recurrenceComparator ν cstar γ m := by
    apply bound_by_descent_le (mc := mc) (m₀ := m₀)
      (Φ := fun k => recurrenceDescentConstant * R * recurrenceComparator ν cstar γ k)
      (dd := fun k => (s k) ^ 2 - recurrenceComparator ν cstar γ k)
      (nn := fun k => k - ⌊adaptStep δ ν cstar γ k⌋)
    · -- base case
      intro k hk
      have hgk : geometricTerm γ k ≤ Bb := le_trans (geometricTerm_mono hγ hk) hmc_le
      exact base_bound hν hcstar hcbar hcc hγ hsmall hδpos hδcplus hγ1 h5δR hCdescpos hRnn hgk
    · -- strict descent
      intro k _ _
      have h1 : 1 ≤ ⌊adaptStep δ ν cstar γ k⌋ := one_le_floor (two_le_adaptStep hδγ2 k)
      omega
    · -- one-step increment
      intro k hkmc hkm₀ hlow
      have hfk : 1 ≤ ⌊adaptStep δ ν cstar γ k⌋ := one_le_floor (two_le_adaptStep hδγ2 k)
      have hgk_lb : δ * ν ^ 2 * γ * (cstar * cbar)⁻¹ ≤ geometricTerm γ k := by
        rw [← hBb_def]; exact le_trans hmc_gt.le (geometricTerm_mono hγ (by omega))
      have hsb := step_bound hν hcstar hcbar hcbarle hcbar1 hγ hE hF hpos hEγ1 hupper hlower
        hcf_lb0 hcfpos hδpos hδlog hδcbar hδγ2 hδR hδ2cf hCdescR hCdesc_val hRnn hkm₀ hgk_lb
        hlow
      have hTsub : recurrenceComparator ν cstar γ k - recurrenceComparator ν cstar γ (k -
        ⌊adaptStep δ ν cstar γ k⌋)
          = 2 * recurrenceIncrement cstar γ (k - ⌊adaptStep δ ν cstar γ k⌋) k :=
        recurrenceComparator_sub_eq_two_increment hγ (by omega)
      change |((s k) ^ 2 - recurrenceComparator ν cstar γ k)
            - ((s (k - ⌊adaptStep δ ν cstar γ k⌋)) ^ 2
              - recurrenceComparator ν cstar γ (k - ⌊adaptStep δ ν cstar γ k⌋))|
          ≤ recurrenceDescentConstant * R * recurrenceComparator ν cstar γ k
            - recurrenceDescentConstant * R * recurrenceComparator ν cstar γ (k - ⌊adaptStep
              δ ν cstar γ k⌋)
      rw [show ((s k) ^ 2 - recurrenceComparator ν cstar γ k)
            - ((s (k - ⌊adaptStep δ ν cstar γ k⌋)) ^ 2
              - recurrenceComparator ν cstar γ (k - ⌊adaptStep δ ν cstar γ k⌋))
          = (s k) ^ 2 - (s (k - ⌊adaptStep δ ν cstar γ k⌋)) ^ 2
            - (recurrenceComparator ν cstar γ k - recurrenceComparator ν cstar γ (k -
              ⌊adaptStep δ ν cstar γ k⌋)) by ring, hTsub,
        show recurrenceDescentConstant * R * recurrenceComparator ν cstar γ k
            - recurrenceDescentConstant * R * recurrenceComparator ν cstar γ (k - ⌊adaptStep
              δ ν cstar γ k⌋)
          = recurrenceDescentConstant * R * (recurrenceComparator ν cstar γ k -
            recurrenceComparator ν cstar γ (k - ⌊adaptStep δ ν cstar γ k⌋)) by ring]
      exact hsb
  -- conclusion for each m ≤ m₀
  intro m hm
  have hdm : |(s m) ^ 2 - recurrenceComparator ν cstar γ m| ≤ recurrenceDescentConstant * R
    * recurrenceComparator ν cstar γ m := hdev m hm
  have hTm_nn : 0 ≤ recurrenceComparator ν cstar γ m := le_trans (sq_nonneg ν)
    (nu_sq_le_recurrenceComparator hcstar.le hγ m)
  have hprod : recurrenceDescentConstant * R * recurrenceComparator ν cstar γ m ≤ (1 / 2) *
    recurrenceComparator ν cstar γ m :=
    mul_le_mul_of_nonneg_right hCdescR hTm_nn
  refine ⟨?_, ?_⟩
  · -- bootstrap sandwich  T_m ≤ 2 s_m²
    rw [abs_le] at hdm
    linarith [hdm.1, hprod]
  · -- deviation bound with the reported constant C₀
    have hCdesc_le_C0 : recurrenceDescentConstant ≤ C₀ := by rw [hC0_def, hCdesc_val]; norm_num
    have hCR_le : recurrenceDescentConstant * R * recurrenceComparator ν cstar γ m ≤ C₀ *
      R * recurrenceComparator ν cstar γ m :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCdesc_le_C0 hRnn) hTm_nn
    linarith [hdm, hCR_le]

end Internal

end

end Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration
