/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Leray Limit Interpolation

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace CKN.Leray

/-- A strong global `L²` limit and a uniform global `L^(10/3)` bound give
strong convergence in each intermediate exponent on an arbitrary measure
space. -/
theorem lerayLimit_strongLp_of_strongL2_and_uniform_high
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {F : ℕ → α → E} {G : α → E}
    (hFlow : ∀ n, MemLp (F n) (ENNReal.ofReal 2) μ)
    (hbound : ∃ B : ℝ≥0∞, B < ⊤ ∧
      ∀ n, eLpNorm (F n) (ENNReal.ofReal (10 / 3 : ℝ)) μ ≤ B)
    (h2 : Tendsto (fun n => eLpNorm (F n - G) (ENNReal.ofReal 2) μ)
      atTop (𝓝 0)) :
    ∀ q : ℝ, 2 ≤ q → q < 10 / 3 →
      Tendsto (fun n => eLpNorm (F n - G) (ENNReal.ofReal q) μ)
        atTop (𝓝 0) := by
  have h2half : ∀ᶠ n : ℕ in atTop,
      eLpNorm (F n - G) (ENNReal.ofReal 2) μ ≤ (1 / 2 : ℝ≥0∞) :=
    (ENNReal.tendsto_nhds_zero.mp h2) (1 / 2 : ℝ≥0∞) (by norm_num)
  have h2lt : ∀ᶠ n : ℕ in atTop,
      eLpNorm (F n - G) (ENNReal.ofReal 2) μ < 1 :=
    h2half.mono fun _ hn => lt_of_le_of_lt hn (by norm_num)
  obtain ⟨n₀, hn₀⟩ := h2lt.exists
  have hDiffMem₀ : MemLp (F n₀ - G) (ENNReal.ofReal 2) μ := by
    rw [memLp_iff]
    exact lt_trans hn₀ (by norm_num)
  have hGeq : G = F n₀ - (F n₀ - G) := by
    funext x
    change G x = F n₀ x - (F n₀ x - G x)
    abel
  have hGlow : MemLp G (ENNReal.ofReal 2) μ := by
    rw [hGeq]
    exact (hFlow n₀).sub hDiffMem₀
  intro q hqLower hqUpper
  have hqPos : 0 < q := lt_of_lt_of_le (by norm_num) hqLower
  have hqTop : ENNReal.ofReal q < ⊤ := ENNReal.ofReal_lt_top
  obtain ⟨B, hBTop, hB⟩ := hbound
  have hFhigh (n : ℕ) :
      MemLp (F n) (ENNReal.ofReal (10 / 3 : ℝ)) μ := by
    rw [memLp_iff]
    exact lt_of_le_of_lt (hB n) hBTop
  have hmeasure : TendstoInMeasure μ F atTop G :=
    tendstoInMeasure_of_tendsto_eLpNorm
      (μ := μ) (p := ENNReal.ofReal 2) (f := F) (g := G) (l := atTop)
      (by norm_num) h2
  obtain ⟨ns, _, hae⟩ := hmeasure.exists_seq_tendsto_ae
  have hGmeas : AEStronglyMeasurable G μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun i => (hFhigh (ns i)).aestronglyMeasurable) hae
  have hFatou := Lp.eLpNorm_lim_le_liminf_eLpNorm
      (p := ENNReal.ofReal (10 / 3 : ℝ))
      (fun i => (hFhigh (ns i)).aestronglyMeasurable) G hGmeas hae
  have hliminf : atTop.liminf
      (fun i => eLpNorm (F (ns i)) (ENNReal.ofReal (10 / 3 : ℝ)) μ) ≤ B :=
    liminf_le_of_frequently_le' <|
      (Eventually.of_forall fun i => hB (ns i)).frequently
  have hGhigh : MemLp G (ENNReal.ofReal (10 / 3 : ℝ)) μ := by
    rw [memLp_iff]
    exact lt_of_le_of_lt (hFatou.trans hliminf) hBTop
  have hDiffHigh (n : ℕ) :
      MemLp (F n - G) (ENNReal.ofReal (10 / 3 : ℝ)) μ :=
    (hFhigh n).sub hGhigh
  let Bdiff : ℝ≥0∞ := B + eLpNorm G (ENNReal.ofReal (10 / 3 : ℝ)) μ
  have hBdiffTop : Bdiff < ⊤ := by
    exact ENNReal.add_lt_top.mpr ⟨hBTop, hGhigh.eLpNorm_lt_top⟩
  have hDiffBound (n : ℕ) :
      eLpNorm (F n - G) (ENNReal.ofReal (10 / 3 : ℝ)) μ ≤ Bdiff := by
    calc
      eLpNorm (F n - G) (ENNReal.ofReal (10 / 3 : ℝ)) μ ≤
          eLpNorm (F n) (ENNReal.ofReal (10 / 3 : ℝ)) μ +
            eLpNorm G (ENNReal.ofReal (10 / 3 : ℝ)) μ :=
        eLpNorm_sub_le (p := ENNReal.ofReal (10 / 3 : ℝ))
          (μ := μ) (f := F n) (g := G) (by norm_num)
      _ ≤ Bdiff := add_le_add (hB n) le_rfl
  have hDiffLow (n : ℕ) : MemLp (F n - G) (ENNReal.ofReal 2) μ :=
    (hFlow n).sub hGlow
  by_cases hq2 : q = 2
  · subst q
    simpa using h2
  have hqStrict : 2 < q := lt_of_le_of_ne hqLower (Ne.symm hq2)
  let theta : ℝ := 5 / q - 3 / 2
  let beta : ℝ := 1 - theta
  have hαPos : 0 < theta := by
    dsimp [theta]
    have hmul : (3 / 2 : ℝ) * q < 5 := by
      have := mul_lt_mul_of_pos_left hqUpper (by norm_num : (0 : ℝ) < 3 / 2)
      nlinarith only [this]
    rw [sub_pos]
    exact (lt_div_iff₀ hqPos).2 hmul
  have hβPos : 0 < beta := by
    dsimp [beta, theta]
    have hmul : 5 < (5 / 2 : ℝ) * q := by
      have := mul_lt_mul_of_pos_left hqStrict (by norm_num : (0 : ℝ) < 5 / 2)
      nlinarith only [this]
    have hdiv : 5 / q < (5 / 2 : ℝ) := (div_lt_iff₀ hqPos).2 hmul
    linarith only [hdiv]
  have hαβ : theta + beta = 1 := by dsimp [beta]; ring
  have hrecip : 1 / q = theta / 2 + beta / (10 / 3 : ℝ) := by
    dsimp [theta, beta]
    field_simp
    ring
  let p1 : ℝ := 2 / theta
  let p2 : ℝ := (10 / 3 : ℝ) / beta
  have hp1Pos : 0 < p1 := by dsimp [p1]; positivity
  have hp2Pos : 0 < p2 := by dsimp [p2]; positivity
  have hHolder : Real.HolderTriple p1 p2 q := by
    refine ⟨?_, hp1Pos, hp2Pos⟩
    have h1 : p1⁻¹ = theta / 2 := by
      dsimp [p1]
      field_simp [ne_of_gt hαPos]
    have h2' : p2⁻¹ = beta / (10 / 3 : ℝ) := by
      dsimp [p2]
      field_simp [ne_of_gt hβPos]
    rw [h1, h2']
    simpa [one_div] using hrecip.symm
  have hqLtP1 : q < p1 := by
    have hrecip' : p1⁻¹ < q⁻¹ := by
      calc
        p1⁻¹ < p1⁻¹ + p2⁻¹ := lt_add_of_pos_right _ (inv_pos.mpr hp2Pos)
        _ = q⁻¹ := hHolder.inv_add_inv_eq_inv
    by_contra hnot
    have hp1le : p1 ≤ q := le_of_not_gt hnot
    have hmono : q⁻¹ ≤ p1⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hp1Pos hp1le
    exact (not_lt_of_ge hmono) hrecip'
  have hCoeffTop : Bdiff ^ beta < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg hβPos.le hBdiffTop.ne
  have hInterp (n : ℕ) :
      eLpNorm' (F n - G) q μ ≤
        Bdiff ^ beta * eLpNorm' (F n - G) 2 μ ^ theta := by
    let d : α → E := F n - G
    let f₁ : α → ℝ := fun x => ‖d x‖ ^ theta
    let f₂ : α → ℝ := fun x => ‖d x‖ ^ beta
    have hp1coe : ENNReal.ofReal p1 =
        ENNReal.ofReal 2 / ENNReal.ofReal theta := by
      dsimp [p1]
      exact ENNReal.ofReal_div_of_pos hαPos
    have hp2coe : ENNReal.ofReal p2 =
        ENNReal.ofReal (10 / 3 : ℝ) / ENNReal.ofReal beta := by
      dsimp [p2]
      exact ENNReal.ofReal_div_of_pos hβPos
    have hf₁ : MemLp f₁ (ENNReal.ofReal p1) μ := by
      rw [hp1coe]
      have h := (hDiffLow n).norm_rpow_div (ENNReal.ofReal theta)
      simpa [f₁, d, ENNReal.toReal_ofReal hαPos.le] using h
    have hf₂ : MemLp f₂ (ENNReal.ofReal p2) μ := by
      rw [hp2coe]
      have h := (hDiffHigh n).norm_rpow_div (ENNReal.ofReal beta)
      simpa [f₂, d, ENNReal.toReal_ofReal hβPos.le] using h
    have hnorm₁ : eLpNorm' f₁ p1 μ = eLpNorm' d 2 μ ^ theta := by
      have hpow := eLpNorm'_norm_rpow (μ := μ) d p1 theta hαPos
      have hp1mul : p1 * theta = 2 := by
        dsimp [p1]
        field_simp [ne_of_gt hαPos]
      simpa [f₁, hp1mul] using hpow
    have hnorm₂ : eLpNorm' f₂ p2 μ =
        eLpNorm' d (10 / 3 : ℝ) μ ^ beta := by
      have hpow := eLpNorm'_norm_rpow (μ := μ) d p2 beta hβPos
      have hp2mul : p2 * beta = (10 / 3 : ℝ) := by
        dsimp [p2]
        field_simp [ne_of_gt hβPos]
      simpa [f₂, hp2mul] using hpow
    have hprod (x : α) : f₁ x * f₂ x = ‖d x‖ := by
      dsimp [f₁, f₂]
      rw [← Real.rpow_add' (norm_nonneg _) (by rw [hαβ]; norm_num),
        hαβ, Real.rpow_one]
    have hHolderNorm :
        eLpNorm' (fun x => f₁ x * f₂ x) q μ ≤
          eLpNorm' f₁ p1 μ * eLpNorm' f₂ p2 μ := by
      simpa [mul_assoc] using (eLpNorm'_le_eLpNorm'_mul_eLpNorm'
        hf₁.aestronglyMeasurable hf₂.aestronglyMeasurable
        (fun x y : ℝ => x * y) 1
        (by
          filter_upwards [] with x
          simp)
        hqPos hqLtP1 (by
          simpa [one_div] using hHolder.inv_add_inv_eq_inv.symm))
    calc
      eLpNorm' d q μ = eLpNorm' (fun x => ‖d x‖) q μ := by
        symm
        exact eLpNorm'_norm (f := d) (q := q) (μ := μ)
      _ = eLpNorm' (fun x => f₁ x * f₂ x) q μ := by
        congr 1
        funext x
        exact (hprod x).symm
      _ ≤ eLpNorm' f₁ p1 μ * eLpNorm' f₂ p2 μ := hHolderNorm
      _ = eLpNorm' d 2 μ ^ theta * eLpNorm' d (10 / 3 : ℝ) μ ^ beta := by
        rw [hnorm₁, hnorm₂]
      _ ≤ eLpNorm' d 2 μ ^ theta * Bdiff ^ beta := by
        gcongr
        have hhighEq : eLpNorm' d (10 / 3 : ℝ) μ =
            eLpNorm d (ENNReal.ofReal (10 / 3 : ℝ)) μ := by
          dsimp [d]
          simpa only [ENNReal.toReal_ofReal
            (by norm_num : (0 : ℝ) ≤ 10 / 3)] using
            (eLpNorm_eq_eLpNorm'
              (p := ENNReal.ofReal (10 / 3 : ℝ))
              (f := F n - G) (μ := μ)
              (by norm_num) (by norm_num)
              (hDiffHigh n).aestronglyMeasurable).symm
        rw [hhighEq]
        exact hDiffBound n
      _ = Bdiff ^ beta * eLpNorm' d 2 μ ^ theta := by rw [mul_comm]
  have hlow : Tendsto
      (fun n => eLpNorm' (F n - G) 2 μ) atTop (𝓝 0) := by
    have heq : (fun n => eLpNorm' (F n - G) 2 μ) =
        fun n => eLpNorm (F n - G) (ENNReal.ofReal 2) μ := by
      funext n
      simpa [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)] using
        (eLpNorm_eq_eLpNorm' (p := ENNReal.ofReal 2)
          (f := F n - G) (μ := μ)
          (by norm_num) (by norm_num)
          (hDiffLow n).aestronglyMeasurable).symm
    rw [heq]
    exact h2
  have hupper : Tendsto
      (fun n => Bdiff ^ beta * eLpNorm' (F n - G) 2 μ ^ theta)
      atTop (𝓝 0) := by
    exact (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos
      (c := Bdiff ^ beta) hCoeffTop.ne hαPos).comp hlow
  have hinterp : Tendsto (fun n => eLpNorm' (F n - G) q μ)
      atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    have hev := (ENNReal.tendsto_nhds_zero.mp hupper) ε hε
    filter_upwards [hev] with n hn
    exact (hInterp n).trans hn
  have heq : (fun n => eLpNorm' (F n - G) q μ) =
      fun n => eLpNorm (F n - G) (ENNReal.ofReal q) μ := by
    funext n
    simpa [ENNReal.toReal_ofReal hqPos.le] using
      (eLpNorm_eq_eLpNorm' (p := ENNReal.ofReal q) (f := F n - G)
        (μ := μ) (ENNReal.ofReal_pos.mpr hqPos).ne' hqTop.ne
        (hDiffLow n).aestronglyMeasurable).symm
  rw [← heq]
  exact hinterp

end CKN.Leray

end
