/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.RowSumFinite
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.RatioTailArith
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.TranslatedLocality

/-!
# RatioTailClosed

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `𝒢₀` lane: the anchor `s`-window of the per-atom tail

ABK26, §4.1, `e.no.bad.scales.applied.for.lambdas` for the `𝒢₀` lane.

* `exp_le_budget` and `atomTail_of_budget` — the abstract-real budget steps at
  `E = C c⋆^{−1}`.
* `exists_cgExcess_atomTail_of_floor` — **the anchor `s`-window** (`hwin` of
  `AtomTail.exists_cgExcess_atomTail`): `exp(−(C_cg^{−1}E^{−2}γ^{−1})) ≤ γ/2` at
  the budget `E = C c⋆^{−1}`, from the printed regime `γ ≤ C^{−10}c⋆^{10}` for
  `C(d)` large; the per-atom `Γ_{1/3}` tail becomes unconditional.

## Scope

Provider material: proved local helpers.

## References

* ABK26, `l.good.scales.ratio.lambda`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability
open Algsuperdiff.Section4.Probability.ScalesConcentration
open Algsuperdiff.Section4.Probability.IndicatorDensity

noncomputable section

/-! ## 4. The two `AtomTail` bridges -/

variable {d : ℕ}

private theorem exp_le_budget (M : ABKModel d) {C : ℝ} {E : {E : ℝ // 1 ≤ E}}
    (hEval : (E : ℝ) = C * (Disorder.cstar M)⁻¹)
    (hCfloor : 3 / 2 * Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)) ≤ C) :
    Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)) ≤ (E : ℝ) := by
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcs : Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  have hcsinv : (2 : ℝ) / 3 ≤ (Disorder.cstar M)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hcs0]
    calc Disorder.cstar M ≤ 3 / 2 := hcs
      _ = ((2 : ℝ) / 3)⁻¹ := by norm_num
  have hstep : 3 / 2 * Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)) *
      (Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
    GoodEvents.mul_cstarInv_le_of_budget M hEval hCfloor
  have hlow : Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ))
      ≤ 3 / 2 * Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)) *
        (Disorder.cstar M)⁻¹ := by
    have h := mul_le_mul_of_nonneg_left hcsinv
      (by positivity :
        (0 : ℝ) ≤ 3 / 2 * Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)))
    calc Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ))
        = 3 / 2 * Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)) * (2 / 3) := by
          ring
      _ ≤ 3 / 2 * Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)) *
            (Disorder.cstar M)⁻¹ := h
  exact le_trans hlow hstep

private theorem atomTail_of_budget (M : ABKModel d) {C : ℝ} {E : {E : ℝ // 1 ≤ E}}
    (hC1 : 1 ≤ C) (hEval : (E : ℝ) = C * (Disorder.cstar M)⁻¹)
    (hEreg : M.gamma ≤ (((E : ℝ))⁻¹) ^ 10)
    (hall : ∀ m : ℤ, Algsuperdiff.Frozen.Section3.inductionState M m E)
    (hexpE : Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)) ≤ (E : ℝ))
    (hwin : cgTailScale M (E : ℝ) ≤ M.gamma / 2) (k : ℤ) (z : Vec d) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma (1 / 3 : ℝ))
      (fun omega =>
        Localize.cgExcess M (Support.cgEllipLowerConstant d) (k - 2) z omega)
      (cgTailScale M (E : ℝ)) := by
  have hEwindow := GoodEvents.coarseEllipticityBudget M hEval hC1 hEreg hall hexpE (k - 2)
  refine isBigOWith_cgExcess_of_state M k z ?_ hEwindow.2.1 hEwindow.2.2 hwin
  have hidx : k - 2 - 1 = k - 3 := by ring
  rw [hidx] at hEwindow
  exact hEwindow.1

/-! ## 5b. SLOT: the anchor's `s`-window at `s = γ`, discharged -/

/-- **The `𝒢₀` atom tail, unconditionally, at any floor the caller needs.**

`AtomTail.exists_cgExcess_atomTail` delivers the per-atom `Γ_{1/3}` tail only
under the anchor's own `s`-window premise `hwin: exp(−(C_cg^{−1}E^{−2}γ^{−1}))
≤ γ/2`, which it passes through as a caller obligation.  That premise is the
manuscript's own step and it is discharged here from the printed regime `γ ≤
C^{−10}c⋆^{10}` alone:

* at the budget `E = C c⋆^{−1}` the exponent is `u = c⋆²/(C_cg C² γ)`, and the
  regime with the proved `c⋆ ≤ 3/2` gives `C⁶ ≤ 12 C_cg² γu²` (`regime_core`);
* the floor `C ≥ 6912 C_cg²` therefore gives `γu² ≥ 576`, and
  `exp(−u) ≤ 2/u² ≤ γ/2` (`exp_neg_le_two_div_sq`).

The extra floor is free for the caller (the `p`-choice needs its own). -/
theorem exists_cgExcess_atomTail_of_floor (d : ℕ) (C0 : ℝ) :
    ∃ C : ℝ, 6 ≤ C ∧ C0 ≤ C ∧
      ∀ M : ABKModel d, M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∃ E : {E : ℝ // 1 ≤ E}, (E : ℝ) = C * (Disorder.cstar M)⁻¹ ∧
          cgTailScale M (E : ℝ) ≤ M.gamma / 2 ∧
            ∀ (k : ℤ) (z : Vec d),
              IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma (1 / 3 : ℝ))
                (fun omega =>
                  Localize.cgExcess M (Support.cgEllipLowerConstant d) (k - 2) z omega)
                (cgTailScale M (E : ℝ)) := by
  classical
  have hCcg0 : (0 : ℝ) < Support.cgEllipLowerConstant d := Support.cgEllipLowerConstant_pos d
  obtain ⟨fl, hfldef⟩ : ∃ x : ℝ, x = max C0
      (max (3 / 2 * Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)))
        (6912 * (Support.cgEllipLowerConstant d) ^ (2 : ℕ))) := ⟨_, rfl⟩
  obtain ⟨C, hC6, hCfl, hall⟩ := GoodEvents.exists_allScalesInductionState_ge d fl
  have hC1 : (1 : ℝ) ≤ C := by linarith only [hC6]
  have hC0' : (0 : ℝ) < C := by linarith only [hC6]
  have hCpow : C ≤ C ^ (6 : ℕ) := by
    calc C = C ^ (1 : ℕ) := (pow_one C).symm
      _ ≤ C ^ (6 : ℕ) := pow_le_pow_right₀ hC1 (by norm_num)
  have hflC0 : C0 ≤ C := by
    refine le_trans ?_ hCfl
    rw [hfldef]
    exact le_max_left _ _
  have hfl1 : 3 / 2 * Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)) ≤ C := by
    refine le_trans ?_ hCfl
    rw [hfldef]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hfl2 : 6912 * (Support.cgEllipLowerConstant d) ^ (2 : ℕ) ≤ C ^ (6 : ℕ) := by
    refine le_trans ?_ (le_trans hCfl hCpow)
    rw [hfldef]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C, hC6, hflC0, ?_⟩
  intro M hreg
  obtain ⟨E, hEval, hEreg, hstate⟩ := hall M hreg
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcs32 : Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  have hg0 : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hE0 : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le zero_lt_one E.2
  obtain ⟨u, hudef⟩ : ∃ x : ℝ, x = (Support.cgEllipLowerConstant d)⁻¹ *
      (((E : ℝ))⁻¹) ^ (2 : ℕ) * M.gamma⁻¹ := ⟨_, rfl⟩
  have hu0 : 0 < u := by
    rw [hudef]
    exact mul_pos (mul_pos (inv_pos.2 hCcg0) (pow_pos (inv_pos.2 hE0) 2)) (inv_pos.2 hg0)
  have hAu : cgTailScale M (E : ℝ) = Real.exp (-u) := by rw [hudef, cgTailScale]
  obtain ⟨hcore1, -, -⟩ :=
    regime_core (u := u) hg0 hcs0 hcs32 hCcg0 hC0' hreg (by rw [hudef, hEval])
  have hpos : (0 : ℝ) < 12 * (Support.cgEllipLowerConstant d) ^ (2 : ℕ) :=
    mul_pos (by norm_num) (pow_pos hCcg0 2)
  have hgu : (576 : ℝ) ≤ M.gamma * u ^ (2 : ℕ) := by
    have hchain : 12 * (Support.cgEllipLowerConstant d) ^ (2 : ℕ) * (576 : ℝ)
        ≤ 12 * (Support.cgEllipLowerConstant d) ^ (2 : ℕ) * (M.gamma * u ^ (2 : ℕ)) := by
      calc 12 * (Support.cgEllipLowerConstant d) ^ (2 : ℕ) * (576 : ℝ)
          = 6912 * (Support.cgEllipLowerConstant d) ^ (2 : ℕ) := by ring
        _ ≤ C ^ (6 : ℕ) := hfl2
        _ ≤ 12 * (Support.cgEllipLowerConstant d) ^ (2 : ℕ) * (M.gamma * u ^ (2 : ℕ)) := hcore1
    calc (576 : ℝ)
        = (12 * (Support.cgEllipLowerConstant d) ^ (2 : ℕ))⁻¹ *
            (12 * (Support.cgEllipLowerConstant d) ^ (2 : ℕ) * (576 : ℝ)) :=
          (inv_mul_cancel_left₀ (ne_of_gt hpos) _).symm
      _ ≤ (12 * (Support.cgEllipLowerConstant d) ^ (2 : ℕ))⁻¹ *
            (12 * (Support.cgEllipLowerConstant d) ^ (2 : ℕ) * (M.gamma * u ^ (2 : ℕ))) :=
          mul_le_mul_of_nonneg_left hchain (inv_nonneg.2 hpos.le)
      _ = M.gamma * u ^ (2 : ℕ) := inv_mul_cancel_left₀ (ne_of_gt hpos) _
  have hwin : cgTailScale M (E : ℝ) ≤ M.gamma / 2 := by
    rw [hAu]
    calc Real.exp (-u) ≤ 2 / u ^ (2 : ℕ) := exp_neg_le_two_div_sq hu0
      _ ≤ M.gamma / 2 := by
          rw [div_le_div_iff₀ (pow_pos hu0 2) (by norm_num : (0 : ℝ) < 2)]
          linarith only [hgu]
  exact ⟨E, hEval, hwin,
    atomTail_of_budget M hC1 hEval hEreg hstate (exp_le_budget M hEval hfl1) hwin⟩

end

end Algsuperdiff.Section4.Provider.Proportion
