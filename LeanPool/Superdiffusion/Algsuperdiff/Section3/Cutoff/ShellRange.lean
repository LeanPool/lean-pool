/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.LocalScaling
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Model
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.IndependenceMap
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.VecGauge

/-!
# ShellRange

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Range dependence of one scaled shell

This is the J1-to-one-shell step for the exact integral-local sigma-fields.
It is kept separate from the countable lower-tail aggregation.
-/

namespace Algsuperdiff.Section3.Cutoff

open HCPolySupport MeasureTheory ProbabilityTheory
open Algsuperdiff.Frozen.Assumptions
open scoped Pointwise

noncomputable section

variable {d : ℕ}

private theorem scaled_sets_measurable (r : ℝ) (hr : r ≠ 0)
    {U : Set (Vec d)} (hU : MeasurableSet U) : MeasurableSet (r • U) :=
  hU.const_smul_of_ne_zero hr

private theorem scaled_separation_of_le (m n : ℤ) (hnm : n ≤ m)
    {U V : Set (Vec d)}
    (hsep : ∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V →
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ m ≤ HCPolySupport.Book.Ch02.vecNorm (x - y)) :
    ∀ ⦃x y : Vec d⦄, x ∈ ((3 : ℝ) ^ n)⁻¹ • U → y ∈ ((3 : ℝ) ^ n)⁻¹ • V →
      Real.sqrt (d : ℝ) ≤ HCPolySupport.Book.Ch02.vecNorm (x - y) := by
  rintro x y ⟨x0, hx0, rfl⟩ ⟨y0, hy0, rfl⟩
  have hthree : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) _
  have hfactor : 1 ≤ (3 : ℝ) ^ (m - n) := by
    calc
      (1 : ℝ) = (3 : ℝ) ^ 0 := by simp
      _ ≤ (3 : ℝ) ^ (m - n) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hsource := hsep hx0 hy0
  have hscaled : Real.sqrt (d : ℝ) * (3 : ℝ) ^ (m - n) ≤
      ((3 : ℝ) ^ n)⁻¹ * HCPolySupport.Book.Ch02.vecNorm (x0 - y0) := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), div_eq_mul_inv]
    nlinarith [mul_le_mul_of_nonneg_left hsource (inv_nonneg.mpr hthree.le)]
  calc
    Real.sqrt (d : ℝ) ≤ Real.sqrt (d : ℝ) * (3 : ℝ) ^ (m - n) := by
      nlinarith [Real.sqrt_nonneg (d : ℝ)]
    _ ≤ ((3 : ℝ) ^ n)⁻¹ * HCPolySupport.Book.Ch02.vecNorm (x0 - y0) := hscaled
    _ = HCPolySupport.Book.Ch02.vecNorm (((3 : ℝ) ^ n)⁻¹ • x0 -
        ((3 : ℝ) ^ n)⁻¹ • y0) := by
      rw [← smul_sub, Algsuperdiff.Section5.Support.vecNorm_smul,
        abs_of_pos (inv_pos.mpr hthree)]

/-- A shell at index `n ≤ m` has integral-local range at most the cutoff's
natural range `sqrt(d) * 3^m`, solely from J1 and marginal scaling. -/
theorem indep_shellLocal_of_cutoff_separation (M : ABKModel d) (m n : ℤ)
    (hnm : n ≤ m) (U V : Set (Vec d)) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hsep : ∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V →
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ m ≤ HCPolySupport.Book.Ch02.vecNorm (x - y)) :
    Indep ((ShellField.lihLocalSigma U).comap
      (fun omega : ℤ → ShellField d => omega n))
      ((ShellField.lihLocalSigma V).comap
      (fun omega : ℤ → ShellField d => omega n)) M.P.toMeasure := by
  let r : ℝ := ((3 : ℝ) ^ n)⁻¹
  have hr : r ≠ 0 := by
    dsimp [r]
    exact inv_ne_zero (zpow_ne_zero _ (by norm_num))
  have hUscaled : MeasurableSet (r • U) := scaled_sets_measurable r hr hU
  have hVscaled : MeasurableSet (r • V) := scaled_sets_measurable r hr hV
  have hzero : Indep (ShellField.lihLocalSigma (r • U))
      (ShellField.lihLocalSigma (r • V)) (ShellField.zeroShellLaw M.P).toMeasure :=
    M.J1.range_dependence (r • U) (r • V) hUscaled hVscaled
      (by simpa [r] using scaled_separation_of_le m n hnm hsep)
  have htransportU := measurable_triadicScale_local M.gamma n U
  have htransportV := measurable_triadicScale_local M.gamma n V
  have hcomap : Indep ((ShellField.lihLocalSigma U).comap
      (ShellField.triadicScale M.gamma n))
      ((ShellField.lihLocalSigma V).comap (ShellField.triadicScale M.gamma n))
      (ShellField.zeroShellLaw M.P).toMeasure :=
    ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left hzero htransportU.comap_le)
      htransportV.comap_le
  have hscaled : Indep (ShellField.lihLocalSigma U) (ShellField.lihLocalSigma V)
      (Measure.map (ShellField.triadicScale M.gamma n)
        (ShellField.zeroShellLaw M.P).toMeasure) :=
    (Algsuperdiff.Probability.indep_comap_iff_indep_map
      (ShellField.measurable_triadicScale M.gamma n).aemeasurable
      (ShellField.lihLocalSigma_le_borel U)
      (ShellField.lihLocalSigma_le_borel V)).mp hcomap
  have hmarginal : Indep (ShellField.lihLocalSigma U) (ShellField.lihLocalSigma V)
      (ShellField.shellMarginalLaw M.P n).toMeasure := by
    have hscale := congrArg ProbabilityMeasure.toMeasure (M.shellPrefix.marginal_scaling n)
    change (ShellField.shellMarginalLaw M.P n).toMeasure =
      Measure.map (ShellField.triadicScale M.gamma n)
        (ShellField.zeroShellLaw M.P).toMeasure at hscale
    rwa [hscale]
  exact (Algsuperdiff.Probability.indep_comap_iff_indep_map
    (ShellField.measurable_shellCoordinate n).aemeasurable
    (ShellField.lihLocalSigma_le_borel U)
    (ShellField.lihLocalSigma_le_borel V)).mpr (by
      simpa [ShellField.shellMarginalLaw] using hmarginal)

end

end Algsuperdiff.Section3.Cutoff
