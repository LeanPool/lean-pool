/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorNormalizedL2Bridge
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorRealRadiusGrowth

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Continuous-radius sublinear growth of anchored correctors

This module turns the discrete centered-cube `O(3^q)` estimate into the exact
continuous-radius vanishing limit used by `MemLiouvilleClass`.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

/-- If a positive real side length dominates the `q`th triadic scale, its
canonical enclosing generation is at least `q`. -/
theorem natCast_le_outerTriadicGeneration_of_pow_le
    {R : ℝ} (hR : 0 < R) {q : ℕ} (hq : (3 : ℝ) ^ q ≤ R) :
    (q : ℤ) ≤ outerTriadicGeneration R hR := by
  have hlog : (q : ℝ) ≤ Real.logb 3 R := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 3) hR).2
    simpa only [Real.rpow_natCast] using hq
  rw [outerTriadicGeneration, Int.le_ceil_iff]
  have hpred : (q : ℝ) - 1 < (q : ℝ) := sub_one_lt _
  exact hpred.trans_le hlog

/-- In particular, a side length at least one has a nonnegative canonical
generation. -/
theorem outerTriadicGeneration_nonneg_of_one_le
    {R : ℝ} (hR : 0 < R) (hRone : 1 ≤ R) :
    0 ≤ outerTriadicGeneration R hR := by
  simpa only [Nat.cast_zero] using
    natCast_le_outerTriadicGeneration_of_pow_le hR
      (q := 0) (by simpa only [pow_zero] using hRone)

/-- A discrete `O(3^q)` bound with local square-integrability becomes an
eventual `O(r)` bound for the frozen normalized `L²` norm on Euclidean balls. -/
theorem exists_eventually_normalizedBallL2_le_linear_cubeGrowth
    {d : ℕ} [NeZero d] (f : Vec d → ℝ)
    (q₀ : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hmem : ∀ q : ℕ, MemLp f 2
      (normalizedCubeMeasure (originCube d (q : ℤ))))
    (hcube : ∀ q : ℕ, q₀ ≤ q →
      cubeLpNorm (originCube d (q : ℤ)) 2 f ≤
        C * (3 : ℝ) ^ q) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧ ∀ᶠ r : ℝ in atTop,
      normalizedL2Norm (euclideanBall d r) f ≤
        D * ENNReal.ofReal r := by
  let F : ℝ≥0∞ :=
    (ENNReal.ofReal ((3 * Real.sqrt d) ^ d)) ^ (1 / 2 : ℝ)
  let D : ℝ≥0∞ := F * ENNReal.ofReal (6 * C)
  have hFtop : F ≠ ⊤ := by
    dsimp only [F]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hDtop : D ≠ ⊤ := by
    dsimp only [D]
    exact ENNReal.mul_ne_top hFtop ENNReal.ofReal_ne_top
  refine ⟨D, hDtop, ?_⟩
  filter_upwards [eventually_ge_atTop
      (max 1 (((3 : ℝ) ^ q₀) / 2))] with r hrlarge
  have hrone : 1 ≤ r := (le_max_left _ _).trans hrlarge
  have hr : 0 < r := zero_lt_one.trans_le hrone
  have hpow : (3 : ℝ) ^ q₀ ≤ 2 * r := by
    have hhalf : ((3 : ℝ) ^ q₀) / 2 ≤ r :=
      (le_max_right _ _).trans hrlarge
    linarith only [hhalf]
  let m : ℤ := outerTriadicGeneration (2 * r) (by positivity)
  let q : ℕ := m.toNat
  have hmq₀Int : (q₀ : ℤ) ≤ m := by
    simpa only [m] using natCast_le_outerTriadicGeneration_of_pow_le
      (by positivity : 0 < 2 * r) hpow
  have hmnonneg : 0 ≤ m := by
    exact outerTriadicGeneration_nonneg_of_one_le (R := 2 * r)
      (by positivity) (by linarith only [hrone])
  have hq₀q : q₀ ≤ q := by
    dsimp only [q]
    omega
  have hmq : (q : ℤ) = m := by
    dsimp only [q]
    exact Int.toNat_of_nonneg hmnonneg
  have hscale : (3 : ℝ) ^ q < 6 * r := by
    have h := outerTriadicGeneration_scale_lt_three_mul
      (by positivity : 0 < 2 * r)
    have h' : (3 : ℝ) ^ m < 3 * (2 * r) := by
      simpa only [m] using h
    rw [← hmq, zpow_natCast] at h'
    linarith only [h']
  have hcubeq := hcube q hq₀q
  have hf : MemLp f 2
      (normalizedCubeMeasure
        (originCube d (outerTriadicGeneration (2 * r) (by positivity)))) := by
    simpa only [m, ← hmq] using hmem q
  have hball := normalizedL2Norm_euclideanBall_le_outerCube
    (d := d) hr f hf
  have hcubeq' :
      cubeLpNorm
          (originCube d (outerTriadicGeneration (2 * r) (by positivity))) 2
          f ≤ C * (3 : ℝ) ^ q := by
    simpa only [m, ← hmq] using hcubeq
  have hscaleC : C * (3 : ℝ) ^ q ≤ C * (6 * r) :=
    mul_le_mul_of_nonneg_left hscale.le hC
  calc
    normalizedL2Norm (euclideanBall d r) f ≤
        F * ENNReal.ofReal
          (cubeLpNorm
            (originCube d (outerTriadicGeneration (2 * r) (by positivity)))
            2 f) := by
      simpa only [F] using hball
    _ ≤ F * ENNReal.ofReal (C * (3 : ℝ) ^ q) := by
      simpa only [mul_comm] using
        mul_le_mul_left (ENNReal.ofReal_le_ofReal hcubeq') F
    _ ≤ F * ENNReal.ofReal (C * (6 * r)) := by
      simpa only [mul_comm] using
        mul_le_mul_left (ENNReal.ofReal_le_ofReal hscaleC) F
    _ = D * ENNReal.ofReal r := by
      rw [show C * (6 * r) = (6 * C) * r by ring,
        ENNReal.ofReal_mul (by positivity : 0 ≤ 6 * C)]
      dsimp only [D]
      ac_rfl

/-- Carrier-specialized form of the preceding real-radius bridge. -/
theorem
  NormalizedLocalH1Carrier.exists_eventually_normalizedBallL2_le_linear_cubeGrowth
    {d : ℕ} [NeZero d] (z : NormalizedLocalH1Carrier d)
    (q₀ : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hcube : ∀ q : ℕ, q₀ ≤ q →
      cubeLpNorm (originCube d (q : ℤ)) 2 z.globalValueRepresentative ≤
        C * (3 : ℝ) ^ q) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧ ∀ᶠ r : ℝ in atTop,
      normalizedL2Norm (euclideanBall d r) z.globalValueRepresentative ≤
        D * ENNReal.ofReal r :=
  _root_.HCPolySupport.HighContrast.exists_eventually_normalizedBallL2_le_linear_cubeGrowth
    z.globalValueRepresentative q₀ C hC
    z.memLp_globalValueRepresentative_normalizedCubeMeasure hcube

/-- Any eventual linear normalized-ball bound is sublinear of every strictly
larger power, in the exact frozen `ENNReal` formulation. -/
theorem tendsto_normalizedL2Norm_sublinear_of_eventually_linear
    {d : ℕ} {v : Vec d → ℝ} {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hlinear : ∃ D : ℝ≥0∞, D ≠ ⊤ ∧ ∀ᶠ r : ℝ in atTop,
      normalizedL2Norm (euclideanBall d r) v ≤ D * ENNReal.ofReal r) :
    Tendsto
      (fun r : ℝ => ENNReal.ofReal (r ^ (-(1 + ϑ))) *
        normalizedL2Norm (euclideanBall d r) v)
      atTop (nhds 0) := by
  obtain ⟨D, hDtop, hlinear⟩ := hlinear
  have hdecayReal : Tendsto (fun r : ℝ => r ^ (-ϑ)) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop hϑ
  have hdecay : Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ (-ϑ)))
      atTop (nhds 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hdecayReal
  have hright : Tendsto
      (fun r : ℝ => D * ENNReal.ofReal (r ^ (-ϑ))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (ENNReal.Tendsto.const_mul hdecay (Or.inr hDtop))
  have hbound : ∀ᶠ r : ℝ in atTop,
      ENNReal.ofReal (r ^ (-(1 + ϑ))) *
          normalizedL2Norm (euclideanBall d r) v ≤
        D * ENNReal.ofReal (r ^ (-ϑ)) := by
    filter_upwards [hlinear, eventually_gt_atTop (0 : ℝ)] with r hrnorm hr
    calc
      ENNReal.ofReal (r ^ (-(1 + ϑ))) *
          normalizedL2Norm (euclideanBall d r) v ≤
        ENNReal.ofReal (r ^ (-(1 + ϑ))) *
          (D * ENNReal.ofReal r) :=
        by simpa only [mul_comm] using
          mul_le_mul_left hrnorm (ENNReal.ofReal (r ^ (-(1 + ϑ))))
      _ = D * ENNReal.ofReal (r ^ (-ϑ)) := by
        have hreal : r ^ (-(1 + ϑ)) * r = r ^ (-ϑ) := by
          rw [← Real.rpow_add_one hr.ne']
          congr 1
          ring
        rw [show ENNReal.ofReal (r ^ (-(1 + ϑ))) *
              (D * ENNReal.ofReal r) =
            D * (ENNReal.ofReal (r ^ (-(1 + ϑ))) * ENNReal.ofReal r) by
              ac_rfl,
          ← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _), hreal]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hright (Eventually.of_forall fun _ => bot_le) hbound

/-- A discrete cube-growth estimate for a normalized local carrier therefore
implies the exact frozen sublinear-growth limit. -/
theorem NormalizedLocalH1Carrier.tendsto_normalizedL2Norm_sublinear_of_cubeGrowth
    {d : ℕ} [NeZero d] (z : NormalizedLocalH1Carrier d)
    (q₀ : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hcube : ∀ q : ℕ, q₀ ≤ q →
      cubeLpNorm (originCube d (q : ℤ)) 2 z.globalValueRepresentative ≤
        C * (3 : ℝ) ^ q)
    {ϑ : ℝ} (hϑ : 0 < ϑ) :
    Tendsto
      (fun r : ℝ => ENNReal.ofReal (r ^ (-(1 + ϑ))) *
        normalizedL2Norm (euclideanBall d r) z.globalValueRepresentative)
      atTop (nhds 0) :=
  tendsto_normalizedL2Norm_sublinear_of_eventually_linear hϑ
    (z.exists_eventually_normalizedBallL2_le_linear_cubeGrowth
      q₀ C hC hcube)

/-- Generic discrete-to-continuous frozen growth bridge. -/
theorem tendsto_normalizedL2Norm_sublinear_of_cubeGrowth
    {d : ℕ} [NeZero d] (f : Vec d → ℝ)
    (q₀ : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hmem : ∀ q : ℕ, MemLp f 2
      (normalizedCubeMeasure (originCube d (q : ℤ))))
    (hcube : ∀ q : ℕ, q₀ ≤ q →
      cubeLpNorm (originCube d (q : ℤ)) 2 f ≤ C * (3 : ℝ) ^ q)
    {ϑ : ℝ} (hϑ : 0 < ϑ) :
    Tendsto
      (fun r : ℝ => ENNReal.ofReal (r ^ (-(1 + ϑ))) *
        normalizedL2Norm (euclideanBall d r) f)
      atTop (nhds 0) :=
  tendsto_normalizedL2Norm_sublinear_of_eventually_linear hϑ
    (exists_eventually_normalizedBallL2_le_linear_cubeGrowth
      f q₀ C hC hmem hcube)

end

end HighContrast
end HCPolySupport
