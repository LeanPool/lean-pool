/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityPressureIntegralConvergence
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Stability Quadratic Product

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal
noncomputable section

namespace CKN

local instance stabilityHolderThreeThreeThreeHalves :
    ENNReal.HolderTriple (3 : ℝ≥0∞) 3 (3 / 2 : ℝ≥0∞) := by
  have hreal : Real.HolderTriple 3 3 (3 / 2) := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  simpa only [CKN.ofReal_threeHalves, ENNReal.ofReal_ofNat] using
    hreal.ennrealOfReal

/-- Products of two strongly `L³`-convergent scalar fields converge strongly
in `L^{3/2}`. -/
theorem stability_tendsto_eLpNorm_product_three
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F G : ℕ → α → ℝ) (f g : α → ℝ)
    (hF : ∀ n, MemLp (F n) 3 μ) (hG : ∀ n, MemLp (G n) 3 μ)
    (hf : MemLp f 3 μ) (hg : MemLp g 3 μ)
    (hFconv : Tendsto (fun n => eLpNorm (F n - f) 3 μ) atTop (nhds 0))
    (hGconv : Tendsto (fun n => eLpNorm (G n - g) 3 μ) atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm
      (fun x => F n x * G n x - f x * g x) (3 / 2 : ℝ≥0∞) μ)
      atTop (nhds 0) := by
  have hmul (a b : α → ℝ) (ha : AEStronglyMeasurable a μ)
      (hb : AEStronglyMeasurable b μ) :
      eLpNorm (fun x => a x * b x) (3 / 2 : ℝ≥0∞) μ ≤
        eLpNorm a 3 μ * eLpNorm b 3 μ := by
    simpa using (eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm
      (b := fun x y : ℝ => x * y) (c := (1 : ℝ≥0∞))
      (by fun_prop) ha hb (by filter_upwards with x; simp [enorm_mul]))
  have hsum (n : ℕ) :
      eLpNorm (fun x => F n x * G n x - f x * g x)
        (3 / 2 : ℝ≥0∞) μ ≤
        eLpNorm (F n - f) 3 μ * eLpNorm (G n) 3 μ +
          eLpNorm f 3 μ * eLpNorm (G n - g) 3 μ := by
    have hdiff : (fun x => F n x * G n x - f x * g x) =
        (fun x => (F n x - f x) * G n x + f x * (G n x - g x)) := by
      funext x
      ring
    rw [hdiff]
    calc
      _ ≤ eLpNorm (fun x => (F n x - f x) * G n x)
            (3 / 2 : ℝ≥0∞) μ +
          eLpNorm (fun x => f x * (G n x - g x))
            (3 / 2 : ℝ≥0∞) μ :=
          eLpNorm_add_le (by
            rw [← CKN.ofReal_threeHalves]
            simpa using ENNReal.ofReal_le_ofReal (by norm_num : (1 : ℝ) ≤ 3 / 2))
      _ ≤ _ := add_le_add
        (hmul _ _ ((hF n).sub hf).aestronglyMeasurable
          (hG n).aestronglyMeasurable)
        (hmul _ _ hf.aestronglyMeasurable
          ((hG n).sub hg).aestronglyMeasurable)
  let C := eLpNorm g 3 μ
  have hC : C < ⊤ := hg
  have hC1 : C + 1 ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hC.ne, ENNReal.one_ne_top⟩
  have hGbound : ∀ᶠ n : ℕ in atTop, eLpNorm (G n) 3 μ ≤ C + 1 := by
    filter_upwards [hGconv.eventually (Iio_mem_nhds
      (by norm_num : (0 : ℝ≥0∞) < 1))] with n hn
    have htriangle := eLpNorm_add_le (μ := μ) (p := (3 : ℝ≥0∞))
      (by norm_num) (f := G n - g) (g := g)
    have hidentity : G n = (fun x => G n x - g x + g x) := by
      funext x
      ring
    calc
      eLpNorm (G n) 3 μ = eLpNorm (fun x => G n x - g x + g x) 3 μ := by
        exact congrArg (fun k => eLpNorm k 3 μ) hidentity
      _ ≤ eLpNorm (G n - g) 3 μ + eLpNorm g 3 μ := htriangle
      _ ≤ 1 + C := add_le_add hn.le le_rfl
      _ = C + 1 := add_comm _ _
  have hfirst : Tendsto (fun n => eLpNorm (F n - f) 3 μ * (C + 1))
      atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.mul_const hFconv (Or.inr hC1)
  have hsecond : Tendsto
      (fun n => eLpNorm f 3 μ * eLpNorm (G n - g) 3 μ)
      atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hGconv (Or.inr hf.ne)
  have hmajor : Tendsto
      (fun n => eLpNorm (F n - f) 3 μ * (C + 1) +
        eLpNorm f 3 μ * eLpNorm (G n - g) 3 μ)
      atTop (nhds 0) := by
    simpa using hfirst.add hsecond
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor
  · filter_upwards with n
    exact bot_le
  · filter_upwards [hGbound] with n hn
    exact (hsum n).trans (add_le_add (mul_le_mul_right hn _) le_rfl)

end CKN
