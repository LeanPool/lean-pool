/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.LargeCubeW1Inf

/-!
# TranslatedLargeCubeW1Inf

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The summed derivative-stream bound on a translated cube

`LargeCubeW1Inf.lean` proves local versions of ABK26's
`e.W1inf.jL.bound.smaller` and `e.W.1.inf.bound` on the *centered* cube
`cu_l`.  The proof of `l.bad.event.lemma` on the branch `n < m` needs both
displays on the *translated* cube `z + cu_m`, since the good local sensitivity
event `e.good.local.events` is stated at `z + cu_m`.

This module re-runs the covering half of the source proof at an arbitrary base
point.  Nothing else changes: the covering family `subcubeShifts` and the
maximum lemma `l.maximums.Gamma.s` are the proved ones, and each translated
member of the cover is priced by the proved translated single-shell display
`isBigOWith_gammaSigma_shellDerivGauge_cube_translate` (ABK26's `e.nabla.jk.O`
at a base point, which is available at the *same* amplitude as at the origin by
the one-shell stationarity of `TranslatedTransport.lean`).  The base points
compose: covering the translated cube `z + cu_l` by translates of `cu_k` is
covering `cu_l` by translates of `cu_k` and then translating the shell, which
is `translate_translate` below.

The amplitudes are therefore **identical** to the centered ones; the base point
`z` is a silent parameter throughout.

## Main results

* `Algsuperdiff.Section3.Provider.Stream.translate_translate`
* `Algsuperdiff.Section3.Provider.Stream.isBigOWith_gammaSigma_shellDerivGaugeCover_translate`
* `Algsuperdiff.Section3.Provider.Stream.isBigOWith_gammaSigma_largeCubeDerivGauge_lt_translate`
* `Algsuperdiff.Section3.Provider.Stream.isBigOWith_gammaSigma_largeCubeDerivGauge_translate`

## References

* ABK26, `e.W.1.inf.bound`.
* ABK26, `e.W1inf.jL.bound.smaller`.
* ABK26, `e.nabla.jk.O`; `l.maximums.Gamma.s`.
* ABK26, `l.bad.event.lemma`.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open HCPolySupport
open HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Elementary rewrites -/

private theorem three_zpow_pos'' (k : ℤ) : (0 : ℝ) < (3 : ℝ) ^ k :=
  zpow_pos (by norm_num) k

private theorem three_zpow_mul_rpow_gamma_sub_one'' (gamma : ℝ) (k : ℤ) :
    (3 : ℝ) ^ k * Real.rpow 3 ((gamma - 1) * (k : ℝ)) =
      (3 : ℝ) ^ (gamma * (k : ℝ)) := by
  change (3 : ℝ) ^ k * (3 : ℝ) ^ ((gamma - 1) * (k : ℝ)) =
    (3 : ℝ) ^ (gamma * (k : ℝ))
  rw [← Real.rpow_intCast (3 : ℝ) k, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

private theorem rpow_inv_two'' (x : ℝ) : x ^ ((2 : ℝ)⁻¹) = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, one_div]

private theorem one_le_sqrt_max_one'' (a : ℝ) : (1 : ℝ) ≤ Real.sqrt (max 1 a) := by
  have h := Real.sqrt_le_sqrt (le_max_left (1 : ℝ) a)
  rwa [Real.sqrt_one] at h

/-! ## Composition of the translation action -/

/-- The frozen translation action composes: `j((· + b) + a) = j(· + (a + b))`. -/
theorem translate_translate (a b : Vec d) (j : ShellField d) :
    ShellField.translate a (ShellField.translate b j) =
      ShellField.translate (a + b) j :=
  ShellField.ext fun x => by
    simp only [ShellField.translate_apply, add_assoc]

/-! ## The translated covering maximum -/

/-- The probabilistic half of `e.W1inf.jL.bound.smaller` at an arbitrary base
point: the covering maximum of the translated own-scale derivative gauges obeys
the single-shell `Γ₂` estimate `e.nabla.jk.O` with the *same* amplitude as at the
origin, since each member of the cover is itself a translate. -/
theorem isBigOWith_gammaSigma_shellDerivGaugeCover_translate (M : ABKModel d)
    (l k : ℤ) (z : Vec d) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d =>
        shellDerivGaugeCover l k (ShellField.translate z (omega k)))
      ((3 * max 1 (Real.log (((subcubeShifts d k l).card : ℕ) : ℝ))) ^ (2 : ℝ)⁻¹ *
        Real.rpow 3 ((M.gamma - 1) * (k : ℝ))) := by
  simp only [shellDerivGaugeCover, translate_translate]
  refine Orlicz.isBigOWith_gammaSigma_finset_sup'_of_nonempty
    (subcubeShifts d k l) (subcubeShifts_nonempty d k l) (by norm_num)
    (Real.rpow_nonneg (by norm_num) _) ?_
  intro p _
  exact isBigOWith_gammaSigma_shellDerivGauge_cube_translate M (le_refl k)
    (subcubeCenter k p + z)

/-! ## `e.W1inf.jL.bound.smaller` at a base point -/

/-- **ABK26's `e.W1inf.jL.bound.smaller`** on the translated cube `z + cu_l`:
for `k < l`,

`3^k ‖∇j_k‖_{L∞(z+cu_l)} + 3^{2k} ‖∇²j_k‖_{L∞(z+cu_l)}
   ≤ O_{Γ₂}(C (l-k)^{1/2} 3^{γk})`,

with the same dimensional constant as the centered display. -/
theorem isBigOWith_gammaSigma_largeCubeDerivGauge_lt_translate (M : ABKModel d)
    {l k : ℤ} (hkl : k < l) (z : Vec d) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d =>
        largeCubeDerivGauge l k (ShellField.translate z (omega k)))
      (shellW1InfSmallerConst d * Real.sqrt ((l : ℝ) - (k : ℝ)) *
        (3 : ℝ) ^ (M.gamma * (k : ℝ))) := by
  have hd : (1 : ℕ) ≤ d := le_trans (by norm_num) M.shellPrefix.dimension
  have hpos : (0 : ℝ) < (3 : ℝ) ^ k := three_zpow_pos'' k
  have hc : (0 : ℝ) ≤ 2 * (3 : ℝ) ^ k := by positivity
  have hcov :=
    (isBigOWith_gammaSigma_shellDerivGaugeCover_translate M l k z).const_mul hc
  refine (hcov.of_le
    (fun omega => largeCubeDerivGauge_le_two_mul_shellDerivGaugeCover l k
      (ShellField.translate z (omega k)))).mono_scale ?_
  have hlogpos : (0 : ℝ) ≤
      3 * max 1 (Real.log (((subcubeShifts d k l).card : ℕ) : ℝ)) := by
    have h1 : (1 : ℝ) ≤ max 1 (Real.log (((subcubeShifts d k l).card : ℕ) : ℝ)) :=
      le_max_left _ _
    linarith
  have hlogbound := three_mul_max_one_log_card_subcubeShifts_le d
    (n := k) (l := l) hd hkl
  have hLnonneg : (0 : ℝ) ≤ largeCubeLogConst * (d : ℝ) := by
    have h1 : (0 : ℝ) ≤ largeCubeLogConst := largeCubeLogConst_pos.le
    have h2 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    exact mul_nonneg h1 h2
  have hsqrt : (3 * max 1 (Real.log (((subcubeShifts d k l).card : ℕ) : ℝ)))
      ^ (2 : ℝ)⁻¹ ≤
      Real.sqrt (largeCubeLogConst * (d : ℝ)) * Real.sqrt ((l : ℝ) - (k : ℝ)) := by
    rw [rpow_inv_two'', ← Real.sqrt_mul hLnonneg]
    exact Real.sqrt_le_sqrt hlogbound
  have hrpow : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (k : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  calc 2 * (3 : ℝ) ^ k *
        ((3 * max 1 (Real.log (((subcubeShifts d k l).card : ℕ) : ℝ)))
            ^ (2 : ℝ)⁻¹ * Real.rpow 3 ((M.gamma - 1) * (k : ℝ)))
      = 2 * (3 * max 1 (Real.log (((subcubeShifts d k l).card : ℕ) : ℝ)))
            ^ (2 : ℝ)⁻¹ *
          ((3 : ℝ) ^ k * Real.rpow 3 ((M.gamma - 1) * (k : ℝ))) := by ring
    _ = 2 * (3 * max 1 (Real.log (((subcubeShifts d k l).card : ℕ) : ℝ)))
            ^ (2 : ℝ)⁻¹ * (3 : ℝ) ^ (M.gamma * (k : ℝ)) := by
          rw [three_zpow_mul_rpow_gamma_sub_one'']
    _ ≤ 2 * (Real.sqrt (largeCubeLogConst * (d : ℝ)) *
            Real.sqrt ((l : ℝ) - (k : ℝ))) * (3 : ℝ) ^ (M.gamma * (k : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ hrpow.le
          exact mul_le_mul_of_nonneg_left hsqrt (by norm_num)
    _ = shellW1InfSmallerConst d * Real.sqrt ((l : ℝ) - (k : ℝ)) *
          (3 : ℝ) ^ (M.gamma * (k : ℝ)) := by
          rw [shellW1InfSmallerConst]
          ring

/-! ## The uniform per-shell estimate at a base point -/

/-- The per-shell estimate on `z + cu_l`, uniform in the two regimes of the
source proof: for `n < k`,

`3^k ‖∇j_k‖_{L∞(z+cu_l)} + 3^{2k} ‖∇²j_k‖_{L∞(z+cu_l)}
   ≤ O_{Γ₂}(C (1 ∨ (l-n))^{1/2} 3^{γk})`. -/
theorem isBigOWith_gammaSigma_largeCubeDerivGauge_translate (M : ABKModel d)
    {l n k : ℤ} (hnk : n < k) (z : Vec d) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d =>
        largeCubeDerivGauge l k (ShellField.translate z (omega k)))
      (shellW1InfConst d * Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) *
        (3 : ℝ) ^ (M.gamma * (k : ℝ))) := by
  have hnkR : (n : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hnk
  have hsq1 : (1 : ℝ) ≤ Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) :=
    one_le_sqrt_max_one'' _
  have hrpow : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (k : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hCsm := shellW1InfSmallerConst_nonneg d
  rcases lt_or_ge k l with hkl | hlk
  · refine (isBigOWith_gammaSigma_largeCubeDerivGauge_lt_translate M hkl z).mono_scale ?_
    have hle : Real.sqrt ((l : ℝ) - (k : ℝ)) ≤
        Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) := by
      refine Real.sqrt_le_sqrt (le_trans ?_ (le_max_right (1 : ℝ) _))
      linarith
    have hsq0 : (0 : ℝ) ≤ Real.sqrt ((l : ℝ) - (k : ℝ)) := Real.sqrt_nonneg _
    have hstep : shellW1InfSmallerConst d * Real.sqrt ((l : ℝ) - (k : ℝ)) ≤
        shellW1InfConst d * Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) := by
      rw [shellW1InfConst]
      nlinarith [hsq1, hle, hsq0, hCsm]
    exact mul_le_mul_of_nonneg_right hstep hrpow.le
  · have hpos : (0 : ℝ) < (3 : ℝ) ^ k := three_zpow_pos'' k
    have hdom : ∀ omega : ShellSeq d,
        largeCubeDerivGauge l k (ShellField.translate z (omega k)) ≤
          (3 : ℝ) ^ k *
            (localCubeDerivNorm k (ShellField.translate z (omega k)) +
              (3 : ℝ) ^ k *
                localCubeSecondDerivNorm k (ShellField.translate z (omega k))) := by
      intro omega
      rw [largeCubeDerivGauge_eq]
      refine mul_le_mul_of_nonneg_left ?_ hpos.le
      exact add_le_add
        (localCubeDerivNorm_mono hlk (ShellField.translate z (omega k)))
        (mul_le_mul_of_nonneg_left
          (localCubeSecondDerivNorm_mono hlk (ShellField.translate z (omega k)))
          hpos.le)
    refine ((((isBigOWith_gammaSigma_shellDerivGauge_cube_translate M
      (le_refl k) z).const_mul hpos.le)).of_le hdom).mono_scale ?_
    rw [three_zpow_mul_rpow_gamma_sub_one'']
    have hC1 : (1 : ℝ) ≤ shellW1InfConst d := by
      rw [shellW1InfConst]; linarith
    have hone : (1 : ℝ) ≤
        shellW1InfConst d * Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) := by
      nlinarith [hsq1, hC1]
    calc (3 : ℝ) ^ (M.gamma * (k : ℝ))
        = 1 * (3 : ℝ) ^ (M.gamma * (k : ℝ)) := (one_mul _).symm
      _ ≤ shellW1InfConst d * Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) *
            (3 : ℝ) ^ (M.gamma * (k : ℝ)) :=
          mul_le_mul_of_nonneg_right hone hrpow.le

end

end Algsuperdiff.Section3.Provider.Stream
