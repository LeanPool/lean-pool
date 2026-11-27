/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified for Lean Pool: adapt module imports and source presentation. -/

module
public import LeanPool.VenNullClockRoundRates.SphereModel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-! Physical cap separation for the two quadrupole clock kernels. -/
@[expose] public section
noncomputable section
namespace VenRate
open MeasureTheory VenMask

instance : OpensMeasurableSpace UnitSphere := inferInstanceAs
  (OpensMeasurableSpace {q : ℝ × ℝ × ℝ // q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 = 1})

theorem first_cont : Continuous firstEnergy := by
  change Continuous (fun y : {q : ℝ × ℝ × ℝ // _} ↦ (1 - y.val.1 ^ 2) ^ 2)
  fun_prop

theorem second_cont (θ : ℝ) : Continuous (secondEnergy θ) := by
  change Continuous (fun y : {q : ℝ × ℝ × ℝ // _} ↦
    (1 - (Real.cos θ * y.val.1 + Real.sin θ * y.val.2.1) ^ 2) ^ 2)
  fun_prop

private theorem eb {u : ℝ} (hu : u ^ 2 ≤ 1) : energy u ∈ Set.Icc (0 : ℝ) 1 := by
  unfold energy
  constructor
  · positivity
  · nlinarith only [sq_nonneg u, mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu)]

theorem en_bounds (θ : ℝ) (y : UnitSphere) :
    firstEnergy y ∈ Set.Icc (0 : ℝ) 1 ∧ secondEnergy θ y ∈ Set.Icc (0 : ℝ) 1 := by
  have len := y.property
  have alg : (Real.cos θ * y.val.1 + Real.sin θ * y.val.2.1) ^ 2 +
      (Real.sin θ * y.val.1 - Real.cos θ * y.val.2.1) ^ 2 =
      (Real.sin θ ^2 + Real.cos θ ^2) * (y.val.1 ^ 2 + y.val.2.1 ^ 2) := by ring
  rw [Real.sin_sq_add_cos_sq, one_mul] at alg
  exact ⟨eb (by nlinarith only [len, sq_nonneg y.val.2.1, sq_nonneg y.val.2.2]),
    eb (by nlinarith only [len, alg, sq_nonneg (Real.sin θ * y.val.1 - Real.cos θ * y.val.2.1),
      sq_nonneg y.val.2.2])⟩

/-- A uniform pole separation: the first energy is at most e⁴ while the second
is at least e² on the same cap. The aperture is independent of the alternative. -/
theorem cap_separation {d θ : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (hs : d ≤ 1 - Real.cos θ ^ 2) (y : UnitSphere)
    (hp : firstEnergy y ≤ (d / 8) ^ 4) : (d / 8) ^ 2 ≤ secondEnergy θ y := by
  set e := d / 8 with he
  have he0 : 0 < e := by dsimp [e]; positivity
  have he1 : e < 1 := by dsimp [e]; linarith
  have len := y.property
  have hxs : y.val.1 ^ 2 ≤ 1 := by nlinarith only [len, sq_nonneg y.val.2.1, sq_nonneg y.val.2.2]
  have hx : |y.val.1| ≤ 1 := by nlinarith only [sq_abs y.val.1, hxs, abs_nonneg y.val.1]
  have hy1 : y.val.2.1 ^ 2 ≤ 1 - y.val.1 ^ 2 := by nlinarith only [len, sq_nonneg y.val.2.2]
  change (1 - y.val.1 ^ 2) ^ 2 ≤ e ^ 4 at hp
  have hf : 1 - y.val.1 ^ 2 ≤ e ^ 2 := by
    by_contra! no
    nlinarith only [hp, mul_pos (sub_pos.mpr no) (by linarith [sq_nonneg e] : 0 < 1 - y.val.1 ^ 2 +
      e ^ 2)]
  have hy : |y.val.2.1| ≤ e := by
    by_contra! no
    nlinarith only [hy1, hf, sq_abs y.val.2.1,
      mul_pos (sub_pos.mpr no) (by linarith [abs_nonneg y.val.2.1] : 0 < |y.val.2.1|+e)]
  have hc : |Real.cos θ| ≤ 1 - 2 * e := by
    by_contra! no
    have : 0 < |Real.cos θ|+(1 - 2 * e) := by rw [he]; linarith [abs_nonneg (Real.cos θ)]
    have h := mul_pos (sub_pos.mpr no) this
    rw [he] at h
    nlinarith only [h, sq_abs (Real.cos θ), hs, hd.le, sq_nonneg d]
  have hsin : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have hproj : |Real.cos θ * y.val.1 + Real.sin θ * y.val.2.1| ≤ 1 - e := by
    calc
      _ ≤ |Real.cos θ| * |y.val.1| + |Real.sin θ| * |y.val.2.1| := by
        simpa only [abs_mul] using abs_add_le (Real.cos θ * y.val.1) (Real.sin θ * y.val.2.1)
      _ ≤ (1 - 2 * e) * 1 + 1 * e := add_le_add
        (mul_le_mul hc hx (abs_nonneg _) ((abs_nonneg _).trans hc))
        (mul_le_mul hsin hy (abs_nonneg _) zero_le_one)
      _ = _ := by ring
  set v := Real.cos θ * y.val.1 + Real.sin θ * y.val.2.1
  have hb := mul_self_le_mul_self (abs_nonneg v) hproj
  have hb' : e ≤ 1 - v ^ 2 := by
    nlinarith only [hb, sq_abs v, mul_nonneg he0.le (sub_nonneg.mpr he1.le)]
  change e ^ 2 ≤ (1 - v ^ 2) ^ 2
  simpa only [sq] using mul_self_le_mul_self he0.le hb'

theorem cap_pos (μ : Measure UnitSphere) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    {r : ℝ} (hr : 0 < r) : 0 < μ.real {y | firstEnergy y < r} := by
  have ho := isOpen_lt first_cont (continuous_const (y := r))
  let pole : UnitSphere := ⟨(1, 0, 0), by norm_num⟩
  have hm := ho.measure_pos μ ⟨pole, by change (1 - (1 : ℝ) ^ 2) ^ 2 < r; simpa using hr⟩
  exact ENNReal.toReal_pos hm.ne' (measure_ne_top _ _)
end VenRate
end
