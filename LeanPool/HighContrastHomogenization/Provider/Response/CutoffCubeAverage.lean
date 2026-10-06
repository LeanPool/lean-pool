/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCellDomain
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoli.EnergyBridge.QuantitativeCutoff.Basic
public import Mathlib.Algebra.Order.Ring.Pow

/-!
# High-contrast homogenization: Provider.Response.CutoffCubeAverage

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Reference-cube normalization for the adapted cutoff

The canonical product cutoff is one on its inner cube.  This file records the
corresponding lower bound on its cube average for arbitrary radii, and chooses
dimension-dependent radii whose inner cube occupies at least half the volume.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

noncomputable section

open Set MeasureTheory

/-- A scaled open cube is open. -/
private theorem isOpen_scaledOpenCubeSet {d : ℕ} (Q : TriadicCube d) (ρ : ℝ) :
    IsOpen (scaledOpenCubeSet Q ρ) := by
  rw [show scaledOpenCubeSet Q ρ =
      ⋂ i : Fin d, {x : Vec d | |x i - cubeCenter Q i| < ρ * cubeRadius Q} by
    ext x
    simp [scaledOpenCubeSet]]
  refine isOpen_iInter_of_finite ?_
  intro i
  exact isOpen_lt
    (continuous_abs.comp ((continuous_apply i).sub continuous_const))
    continuous_const

/-- The volume of the concentric open subcube is its relative side length to
the power of the dimension, times the volume scale of the parent cube. -/
theorem volume_scaledOpenCubeSet_toReal {d : ℕ} (Q : TriadicCube d)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (volume (scaledOpenCubeSet Q ρ)).toReal =
      (ρ * cubeScaleFactor Q) ^ d := by
  let a : Fin d → ℝ := fun i => cubeCenter Q i - ρ * cubeRadius Q
  let b : Fin d → ℝ := fun i => cubeCenter Q i + ρ * cubeRadius Q
  have hab : a ≤ b := by
    intro i
    dsimp [a, b]
    linarith only [hρ, cubeRadius_nonneg Q,
      mul_nonneg hρ (cubeRadius_nonneg Q)]
  rw [show scaledOpenCubeSet Q ρ =
      Set.pi Set.univ (fun i : Fin d => Set.Ioo (a i) (b i)) by
    ext x
    constructor
    · intro hx i _hi
      have hi := hx i
      rw [abs_lt] at hi
      constructor <;> dsimp [a, b] <;> linarith only [hi.1, hi.2]
    · intro hx i
      have hi := hx i (by simp)
      rw [abs_lt]
      constructor
      · dsimp [a, b] at hi
        linarith only [hi.1]
      · dsimp [a, b] at hi
        linarith only [hi.2]]
  have hside : ∀ i : Fin d, b i - a i = ρ * cubeScaleFactor Q := by
    intro i
    dsimp [a, b]
    rw [cubeScaleFactor_eq_two_mul_cubeRadius Q]
    ring
  calc
    (volume (Set.pi Set.univ (fun i : Fin d => Set.Ioo (a i) (b i)))).toReal =
        ∏ i : Fin d, (b i - a i) := by
          simpa [a, b] using Real.volume_pi_Ioo_toReal (ι := Fin d) hab
    _ = ∏ _i : Fin d, ρ * cubeScaleFactor Q := by
      apply Finset.prod_congr rfl
      intro i _hi
      exact hside i
    _ = (ρ * cubeScaleFactor Q) ^ d := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The canonical product cutoff has average at least the relative volume of
the inner cube. -/
theorem innerRatio_pow_le_cubeAverage_canonicalFun {d : ℕ}
    (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁)
    (hρ₁₂ : ρ₁ < ρ₂) (hρ₁_lt_one : ρ₁ < 1) :
    ρ₁ ^ d ≤ cubeAverage Q
      (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) := by
  let η : Vec d → ℝ := QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂
  let S : Set (Vec d) := scaledOpenCubeSet Q ρ₁
  have hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η := by
    simpa [η] using QuantitativeCubeCutoff.canonicalFun_smooth Q hρ₁ hρ₁₂
  have hη_compact : HasCompactSupport η := by
    simpa [η] using
      QuantitativeCubeCutoff.canonicalFun_hasCompactSupport Q hρ₁ hρ₁₂
  have hη_int : IntegrableOn η (cubeSet Q) volume :=
    (hη_smooth.continuous.integrable_of_hasCompactSupport hη_compact).integrableOn
  have hS_meas : MeasurableSet S := (isOpen_scaledOpenCubeSet Q ρ₁).measurableSet
  have hS_sub : S ⊆ cubeSet Q := by
    intro x hx
    have hxclosed : x ∈ scaledClosedCubeSet Q ρ₁ := fun i => le_of_lt (hx i)
    have hxopen : x ∈ openCubeSet Q :=
      scaledClosedCubeSet_subset_openCubeSet_of_lt_one Q hρ₁.le hρ₁_lt_one hxclosed
    exact openCubeSet_subset_cubeSet Q hxopen
  have hS_int : IntegrableOn (S.indicator (fun _ : Vec d => (1 : ℝ)))
      (cubeSet Q) volume := by
    have hconst : IntegrableOn (fun _ : Vec d => (1 : ℝ)) (cubeSet Q) volume :=
      integrableOn_const (μ := volume) (s := cubeSet Q) (C := (1 : ℝ))
        (volume_cubeSet_lt_top Q).ne
    exact hconst.indicator hS_meas
  have hpoint : ∀ x ∈ cubeSet Q,
      S.indicator (fun _ : Vec d => (1 : ℝ)) x ≤ η x := by
    intro x _hxQ
    by_cases hxS : x ∈ S
    · have hxclosed : x ∈ scaledClosedCubeSet Q ρ₁ := fun i => le_of_lt (hxS i)
      have hone : η x = 1 := by
        simpa [η] using QuantitativeCubeCutoff.canonicalFun_eq_one_on_inner
          (Q := Q) (ρ₁ := ρ₁) (ρ₂ := ρ₂) hρ₁ hρ₁₂ hxclosed
      simp [Set.indicator_of_mem hxS, hone]
    · have hnonneg : 0 ≤ η x := by
        simpa [η] using QuantitativeCubeCutoff.canonicalFun_nonneg Q ρ₁ ρ₂ x
      simpa [Set.indicator_of_notMem hxS] using hnonneg
  have hmono :
      ∫ x in cubeSet Q, S.indicator (fun _ : Vec d => (1 : ℝ)) x ∂volume ≤
        ∫ x in cubeSet Q, η x ∂volume :=
    setIntegral_mono_on hS_int hη_int (measurableSet_cubeSet Q) hpoint
  have hleft_eq :
      ∫ x in cubeSet Q, S.indicator (fun _ : Vec d => (1 : ℝ)) x ∂volume =
        (volume S).toReal := by
    rw [setIntegral_indicator hS_meas]
    rw [Set.inter_eq_right.mpr hS_sub]
    simp [measureReal_def]
  have hS_vol : (volume S).toReal = (ρ₁ * cubeScaleFactor Q) ^ d := by
    simpa [S] using volume_scaledOpenCubeSet_toReal Q hρ₁.le
  have hscale_pos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hratio :
      (cubeVolume Q)⁻¹ * (ρ₁ * cubeScaleFactor Q) ^ d = ρ₁ ^ d := by
    have hpow_ne : cubeScaleFactor Q ^ d ≠ 0 := pow_ne_zero d hscale_pos.ne'
    simp [cubeVolume, mul_pow]
    field_simp [hpow_ne]
  unfold cubeAverage
  calc
    ρ₁ ^ d = (cubeVolume Q)⁻¹ * (ρ₁ * cubeScaleFactor Q) ^ d := hratio.symm
    _ = (cubeVolume Q)⁻¹ * (volume S).toReal := by rw [hS_vol]
    _ = (cubeVolume Q)⁻¹ *
        ∫ x in cubeSet Q, S.indicator (fun _ : Vec d => (1 : ℝ)) x ∂volume := by
      rw [hleft_eq]
    _ ≤ (cubeVolume Q)⁻¹ * ∫ x in cubeSet Q, η x ∂volume :=
      mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr (cubeVolume_pos Q).le)

/-- Bernoulli's inequality shows that the chosen inner side ratio occupies at
least half the volume in every positive dimension. -/
theorem half_le_innerRatio_pow (d : ℕ) [NeZero d] :
    (1 / 2 : ℝ) ≤ (1 - 1 / (2 * (d : ℝ))) ^ d := by
  have hd_nat : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast hd_nat
  have hden : (0 : ℝ) < 2 * (d : ℝ) := mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hd)
  have ha : (-2 : ℝ) ≤ -(1 / (2 * (d : ℝ))) := by
    have hfrac : 1 / (2 * (d : ℝ)) ≤ 1 := by
      rw [div_le_one hden]
      linarith only [hd]
    linarith only [hfrac]
  have hbern := one_add_mul_le_pow ha d
  have hleft :
      1 + (d : ℝ) * (-(1 / (2 * (d : ℝ)))) = (1 / 2 : ℝ) := by
    field_simp [show (d : ℝ) ≠ 0 by positivity]
    ring
  have hright :
      1 + -(1 / (2 * (d : ℝ))) = 1 - 1 / (2 * (d : ℝ)) := by ring
  rw [hleft, hright] at hbern
  exact hbern

/-- The selected inner and outer relative radii are strictly ordered inside
the parent cube. -/
theorem cutoffRadii_spec (d : ℕ) [NeZero d] :
    0 < (1 - 1 / (2 * (d : ℝ))) ∧
      (1 - 1 / (2 * (d : ℝ))) < (1 - 1 / (4 * (d : ℝ))) ∧
      (1 - 1 / (4 * (d : ℝ))) < 1 := by
  have hd_nat : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast hd_nat
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le zero_lt_one hd
  constructor
  · rw [sub_pos, div_lt_one (mul_pos (by norm_num) hdpos)]
    linarith only [hd]
  constructor
  · have h2 : (0 : ℝ) < 2 * (d : ℝ) := mul_pos (by norm_num) hdpos
    have h4 : (0 : ℝ) < 4 * (d : ℝ) := mul_pos (by norm_num) hdpos
    have hdiv : 1 / (4 * (d : ℝ)) < 1 / (2 * (d : ℝ)) := by
      exact one_div_lt_one_div_of_lt h2 (by linarith only [hdpos])
    linarith only [hdiv]
  · have : (0 : ℝ) < 1 / (4 * (d : ℝ)) := by positivity
    linarith only [this]

end

end Response
end HighContrast
end HCPolySupport
