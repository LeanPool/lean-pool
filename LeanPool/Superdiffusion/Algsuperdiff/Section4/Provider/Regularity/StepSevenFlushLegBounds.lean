/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourSeminormComparisons
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.FractionalPoincare
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBCloseArith
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SealDatumStep

/-!
# StepSevenFlushLegBounds

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The pinned `s`-weights and the scalar helpers -/

/-- `s^{-2} = 16` at the pin `s = 1/4`. -/
theorem stepOneS_rpow_neg_two : Real.rpow stepOneS (-(2 : ℝ)) = 16 := by
  show (1 / 4 : ℝ) ^ (-(2 : ℝ)) = 16
  rw [Real.rpow_neg (by norm_num),
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- `s^{-3} = 64` at the pin. -/
theorem stepOneS_rpow_neg_three : Real.rpow stepOneS (-(3 : ℝ)) = 64 := by
  show (1 / 4 : ℝ) ^ (-(3 : ℝ)) = 64
  rw [Real.rpow_neg (by norm_num),
    show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- `s^{-6} = 4096` at the pin. -/
theorem stepOneS_rpow_neg_six : Real.rpow stepOneS (-(6 : ℝ)) = 4096 := by
  show (1 / 4 : ℝ) ^ (-(6 : ℝ)) = 4096
  rw [Real.rpow_neg (by norm_num),
    show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- `s^{-7} = 16384` at the pin. -/
theorem stepOneS_rpow_neg_seven : Real.rpow stepOneS (-(7 : ℝ)) = 16384 := by
  show (1 / 4 : ℝ) ^ (-(7 : ℝ)) = 16384
  rw [Real.rpow_neg (by norm_num),
    show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- `√σ · σ⁻¹ = √(σ⁻¹)` for `σ > 0`. -/
theorem sqrt_mul_inv_eq_sqrt_inv {sigma : ℝ} (hsigma : 0 < sigma) :
    Real.sqrt sigma * sigma⁻¹ = Real.sqrt sigma⁻¹ := by
  rw [Real.sqrt_inv]
  have hs : 0 < Real.sqrt sigma := Real.sqrt_pos.mpr hsigma
  have hsq : Real.sqrt sigma * Real.sqrt sigma = sigma := Real.mul_self_sqrt hsigma.le
  field_simp
  linarith only [hsq]

/-- **The `σ`-bridge budget absorption.**  At the regime `2γ ≤ 1-α`, the fine
`σ`-comparison factor is inside the quarter budget: `√(rootClauseBTopKs γ m j)
≤ 2·3^{(1/4)(1-α)(m-n)}` for `n ≤ j ≤ m`. -/
theorem sqrt_rootClauseBTopKs_le_budget {gamma alpha : ℝ} {n j m : ℤ}
    (hgamma0 : 0 ≤ gamma) (h2gamma : 2 * gamma ≤ 1 - alpha) (hnj : n ≤ j)
    (hjm : j ≤ m) :
    Real.sqrt (rootClauseBTopKs gamma m j) ≤
      2 * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) := by
  have hjr : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hjm
  have hnr : (n : ℝ) ≤ (j : ℝ) := by exact_mod_cast hnj
  have hexp : gamma * ((m : ℝ) - (j : ℝ)) / 2 ≤
      1 / 4 * stepSixExponent alpha n m := by
    rw [stepSixExponent]
    have h1 : gamma * ((m : ℝ) - (j : ℝ)) ≤ gamma * ((m : ℝ) - (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hnr]) hgamma0
    have h2 : gamma * ((m : ℝ) - (n : ℝ)) * 2 ≤ (1 - alpha) * ((m : ℝ) - (n : ℝ)) := by
      have hmn : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by linarith only [hnr, hjr]
      have := mul_le_mul_of_nonneg_right h2gamma hmn
      linarith only [this]
    linarith only [h1, h2]
  have hks : rootClauseBTopKs gamma m j =
      4 * Real.rpow (3 : ℝ) (gamma * ((m : ℝ) - (j : ℝ))) := rfl
  have hrp : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (gamma * ((m : ℝ) - (j : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  rw [hks, show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_mul (by positivity) _, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [show Real.rpow (3 : ℝ) (gamma * ((m : ℝ) - (j : ℝ))) =
      (3 : ℝ) ^ (gamma * ((m : ℝ) - (j : ℝ))) from rfl,
    Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (by rw [mul_comm _ (1 / 2 : ℝ)]; linarith only [hexp])

/-! ## 2. The `∇h` flat and coordinate legs, by the printed sup binder -/

theorem eLpNorm_grad_window_le_sup {m j : ℤ} {z : Vec d} {Kh : ℝ} (hKh : 0 ≤ Kh)
    (hz : z ∈ openCubeSet (originCube d m))
    (hdat : H1Function (openCubeSet (originCube d m)))
    (hsup : ∀ y ∈ openCubeSet (originCube d m),
      ‖hdat.grad y‖ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) :
    (eLpNorm hdat.grad 2
        (Support.normalizedVolumeMeasureOn (truncatedWindow z m j))).toReal ≤
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh := by
  have hC0 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hKh
  have := isProbabilityMeasure_normalizedVolumeMeasureOn
    (volume_truncatedWindow_pos j hz) (volume_truncatedWindow_lt_top z m j).ne
  have hae : ∀ᵐ y ∂(Support.normalizedVolumeMeasureOn (truncatedWindow z m j)),
      ‖hdat.grad y‖ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh := by
    rw [Support.normalizedVolumeMeasureOn_def]
    refine Measure.ae_smul_measure ?_ _
    refine ((ae_restrict_iff' (measurableSet_stepThreeWindow z m j)).mpr
      (Filter.Eventually.of_forall fun y hy => ?_))
    exact hsup y (truncatedWindow_subset_domain z m j hy)
  by_cases hmeas : AEStronglyMeasurable hdat.grad
      (Support.normalizedVolumeMeasureOn (truncatedWindow z m j))
  · have h := eLpNorm_le_of_ae_bound (p := 2) hmeas hae
    rw [measure_univ, ENNReal.one_rpow, one_mul] at h
    exact ENNReal.toReal_le_of_le_ofReal hC0 h
  · rw [eLpNorm_of_not_aestronglyMeasurable hmeas, ENNReal.toReal_top]
    exact hC0

theorem eLpNorm_grad_coord_window_le_sup {m j : ℤ} {z : Vec d} {Kh : ℝ}
    (hKh : 0 ≤ Kh) (hz : z ∈ openCubeSet (originCube d m))
    (hdat : H1Function (openCubeSet (originCube d m)))
    (hsup : ∀ y ∈ openCubeSet (originCube d m),
      ‖hdat.grad y‖ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) (i : Fin d) :
    (eLpNorm (fun y => hdat.grad y i) 2
        (Support.normalizedVolumeMeasureOn (truncatedWindow z m j))).toReal ≤
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh := by
  have hC0 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hKh
  have := isProbabilityMeasure_normalizedVolumeMeasureOn
    (volume_truncatedWindow_pos j hz) (volume_truncatedWindow_lt_top z m j).ne
  have hae : ∀ᵐ y ∂(Support.normalizedVolumeMeasureOn (truncatedWindow z m j)),
      ‖hdat.grad y i‖ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh := by
    rw [Support.normalizedVolumeMeasureOn_def]
    refine Measure.ae_smul_measure ?_ _
    refine ((ae_restrict_iff' (measurableSet_stepThreeWindow z m j)).mpr
      (Filter.Eventually.of_forall fun y hy => ?_))
    exact le_trans (norm_le_pi_norm (hdat.grad y) i)
      (hsup y (truncatedWindow_subset_domain z m j hy))
  by_cases hmeas : AEStronglyMeasurable (fun y => hdat.grad y i)
      (Support.normalizedVolumeMeasureOn (truncatedWindow z m j))
  · have h := eLpNorm_le_of_ae_bound (p := 2) hmeas hae
    rw [measure_univ, ENNReal.one_rpow, one_mul] at h
    exact ENNReal.toReal_le_of_le_ofReal hC0 h
  · rw [eLpNorm_of_not_aestronglyMeasurable hmeas, ENNReal.toReal_top]
    exact hC0

theorem sum_eLpNorm_grad_coord_window_le_sup {m j : ℤ} {z : Vec d} {Kh : ℝ}
    (hKh : 0 ≤ Kh) (hz : z ∈ openCubeSet (originCube d m))
    (hdat : H1Function (openCubeSet (originCube d m)))
    (hsup : ∀ y ∈ openCubeSet (originCube d m),
      ‖hdat.grad y‖ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) :
    ∑ i : Fin d, (eLpNorm (fun y => hdat.grad y i) 2
        (Support.normalizedVolumeMeasureOn (truncatedWindow z m j))).toReal ≤
      (d : ℝ) * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) := by
  have h := Finset.sum_le_card_nsmul Finset.univ
    (fun i : Fin d => (eLpNorm (fun y => hdat.grad y i) 2
      (Support.normalizedVolumeMeasureOn (truncatedWindow z m j))).toReal)
    (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)
    (fun i _ => eLpNorm_grad_coord_window_le_sup hKh hz hdat hsup i)
  rwa [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h

/-! ## 3. The two Gagliardo legs, by the `C^{0,1/2}` data -/

/-- **A Gagliardo window leg at the pin, `toReal` form.**  The Step-4 comparison at
`s = stepOneS = 1/4` on the truncated window. -/
theorem gagliardo_window_toReal_le {m j : ℤ} {z : Vec d} {Kf : ℝ}
    {f : Vec d → Vec d} (hd : 1 ≤ d) (hz : z ∈ openCubeSet (originCube d m))
    (hKf : 0 ≤ Kf)
    (hf : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kf f) :
    (Support.normalizedGagliardoESeminormOn (truncatedWindow z m j) stepOneS
        f).toReal ≤
      Kf * stepFourGagliardoConst d stepOneS * (3 : ℝ) ^ ((j : ℝ) / 4) := by
  rw [show stepOneS = (1 / 4 : ℝ) from rfl]
  have hC0 : (0 : ℝ) ≤ Kf * stepFourGagliardoConst d (1 / 4) * (3 : ℝ) ^ ((j : ℝ) / 4) :=
    mul_nonneg (mul_nonneg hKf (stepFourGagliardoConst_nonneg d _))
      (Real.rpow_nonneg (by norm_num) _)
  have h := normalizedGagliardoESeminormOn_stepThreeWindow_quarter_le
    (z := z) (m := m) (j := j) (g := f) (K := Kf) hd hz hKf hf
  exact ENNReal.toReal_le_of_le_ofReal hC0 h

/-! ## 4. The oscillation bridge -/

/-- **The window oscillation's carrier bridge**: the anchor-side `eLpNorm` reading
IS the boundary lane's `‖·‖_{L²}` reading. -/
theorem oscE_toReal_eq_normalizedL2On {m j : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m))
    (uglob : H1Function (openCubeSet (originCube d m))) (c : ℝ) :
    (eLpNorm (fun y => uglob.toFun y - c) 2
        (Support.normalizedVolumeMeasureOn (truncatedWindow z m j))).toReal =
      normalizedL2On (truncatedWindow z m j) (fun y => uglob.toFun y - c) := by
  have hmem : MemLp (fun y => uglob.toFun y - c) 2
      (volume.restrict (truncatedWindow z m j)) := by
    have : Fact (volume (truncatedWindow z m j) < ⊤) :=
      ⟨volume_truncatedWindow_lt_top z m j⟩
    have h := (memLp_toFun_of_subset uglob
      (truncatedWindow_subset_domain z m j)).sub (memLp_const (μ := volume.restrict
        (truncatedWindow z m j)) (p := 2) c)
    exact h
  exact (normalizedL2On_eq_toReal_eLpNorm_normalizedVolumeMeasureOn
    (volume_truncatedWindow_pos j hz)
    (volume_truncatedWindow_lt_top z m j).ne hmem).symm

end

end Algsuperdiff.Section4.Provider.Regularity
